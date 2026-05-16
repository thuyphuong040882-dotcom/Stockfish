/*
 * Chess vs AI  —  single-file Win32/GDI+
 * Compile:
 *   g++ finalcode.cpp -o chess.exe -lgdi32 -luser32 -lgdiplus -lcomdlg32 -mwindows -std=c++14
 *
 * PNG pieces (optional): create a "pieces\" folder next to the .exe and add:
 *   wK wQ wR wB wN wP bK bQ bR bB bN bP  (all .png, e.g. Lichess "cburnett" set)
 * If files are absent the program falls back to Unicode glyphs automatically.
 *
 * Keyboard shortcuts:
 *   Ctrl+Z  Undo last two half-moves (player + AI)
 *   Ctrl+F  Load FEN from clipboard
 *   Ctrl+S  Save PGN to file
 *   Escape  Deselect / cancel drag
 */

#define UNICODE
#include <windows.h>
#include <windowsx.h>
#include <gdiplus.h>
#include <commdlg.h>
#include <string>
#include <vector>
#include <cstring>
#include <cctype>
#include <climits>
#include <algorithm>

#pragma comment(lib,"gdi32.lib")
#pragma comment(lib,"user32.lib")
#pragma comment(lib,"gdiplus.lib")
#pragma comment(lib,"comdlg32.lib")

// ─────────────────────── CONSTANTS ────────────────────────────
static const int SQ    = 80;
static const int OX    = 20;
static const int OY    = 20;
static const int SP    = 195;                          // side panel width
static const int WIN_W = OX + 8*SQ + SP + 8;
static const int WIN_H = OY + 8*SQ + 50;
static const int INF   = 30000;

#define WM_AI_DONE   (WM_APP+1)
#define TIMER_ANIM   1
#define TIMER_CLOCK  2
#define ANIM_MS      16
#define ANIM_DUR     240
#define TT_SIZE      (1<<17)                           // 128K entries

// Chess.com palette
static const COLORREF C_LIGHT = RGB(238,238,210);
static const COLORREF C_DARK  = RGB(118,150, 86);
static const COLORREF C_SEL   = RGB(246,246,105);
static const COLORREF C_LAST  = RGB(207,210,107);
static const COLORREF C_CHK   = RGB(235, 97, 80);
static const COLORREF C_BG    = RGB( 32, 36, 44);
static const COLORREF C_PANEL = RGB( 38, 43, 52);
static const COLORREF C_TEXT  = RGB(200,200,200);

// ─────────────────────── TYPES ────────────────────────────────
struct Move {
    signed char fr,fc,tr,tc;
    char promo;          // 0 or 'q','r','b','n'
    bool ep, castle;
};
static const Move NULL_MV = {-1,-1,-1,-1,0,false,false};
inline bool mvNull(const Move& m){ return m.fr<0; }
inline bool mvEq(const Move& a,const Move& b){ return a.fr==b.fr&&a.fc==b.fc&&a.tr==b.tr&&a.tc==b.tc; }

struct BS {                                            // board state (for search)
    char board[8][8];
    bool wKM,bKM,wARM,wHRM,bARM,bHRM;
    int  epR,epC;
};

struct TTEntry {
    unsigned long long hash;
    short score;
    signed char depth;
    signed char flag;  // 0=exact 1=upper 2=lower
    Move bestMv;
};

struct Anim { bool active; char piece; float cx,cy,tx,ty; int elapsed; Move mv; };

struct UndoInfo {
    char board[8][8];
    bool wKM,bKM,wARM,wHRM,bARM,bHRM;
    int  epR,epC;
    bool playerTurn, inCheck;
    int  lastFR,lastFC,lastTR,lastTC;
};

struct Drag { bool active; int srcR,srcC,cx,cy; char piece; };

// ─────────────────────── GLOBALS ──────────────────────────────
static struct {
    char  board[8][8];
    bool  playerWhite, playerTurn;
    bool  wKM,bKM,wARM,wHRM,bARM,bHRM;
    int   epR,epC;
    int   selR,selC;
    std::vector<Move> legal;
    int   lastFR,lastFC,lastTR,lastTC;
    bool  inCheck,gameOver,aiBusy;
    std::string status;
    int   aiDepth;
    int   playerClockMs, aiClockMs;
    Anim  anim;
    Drag  drag;
    std::vector<UndoInfo> undoStack;
    std::vector<std::string> hist;
    std::vector<unsigned long long> posHist; // for repetition detection
    int histScroll;   // move history scroll offset (lines from bottom)
} G;

static TTEntry ttable[TT_SIZE];
static unsigned long long ZKEYS[12][64], ZTURN, ZEP[8], ZCASTLE[4];
static Move killers[64][2]; // 2 killer moves per depth

static HWND  hWnd;
static HFONT hPF, hSF, hBF;
static ULONG_PTR gdipToken;
static Gdiplus::Bitmap* pieceImgs[12];
static bool hasPNG = false;

static DWORD aiStartTick;
static int   aiTimeLimitMs;

// ─────────────────────── HELPERS ──────────────────────────────
inline bool isW(char p)          { return p>='A'&&p<='Z'; }
inline bool isB(char p)          { return p>='a'&&p<='z'; }
inline bool inBnd(int r,int c)   { return r>=0&&r<8&&c>=0&&c<8; }
inline bool isEnemy(char p,bool w){ return w?isB(p):isW(p); }
inline bool isFriend(char p,bool w){ return w?isW(p):isB(p); }
inline bool timeUp(){ return (int)(GetTickCount()-aiStartTick)>=aiTimeLimitMs; }

// ─────────────────────── CHESS LOGIC ─────────────────────────
static bool attacked(const char b[8][8], int r, int c, bool byW) {
    char K=byW?'K':'k', Q=byW?'Q':'q', R=byW?'R':'r',
         B2=byW?'B':'b', N=byW?'N':'n', P=byW?'P':'p';
    static const int kd[8][2]={{-2,-1},{-2,1},{-1,-2},{-1,2},{1,-2},{1,2},{2,-1},{2,1}};
    for(auto&d:kd){int nr=r+d[0],nc=c+d[1];if(inBnd(nr,nc)&&b[nr][nc]==N)return true;}
    if(byW){if(inBnd(r+1,c-1)&&b[r+1][c-1]==P)return true;if(inBnd(r+1,c+1)&&b[r+1][c+1]==P)return true;}
    else   {if(inBnd(r-1,c-1)&&b[r-1][c-1]==P)return true;if(inBnd(r-1,c+1)&&b[r-1][c+1]==P)return true;}
    static const int sd[4][2]={{0,1},{0,-1},{1,0},{-1,0}};
    for(auto&d:sd)for(int i=1;i<8;i++){int nr=r+d[0]*i,nc=c+d[1]*i;if(!inBnd(nr,nc))break;if(b[nr][nc]!='.'){if(b[nr][nc]==R||b[nr][nc]==Q)return true;break;}}
    static const int dd[4][2]={{1,1},{1,-1},{-1,1},{-1,-1}};
    for(auto&d:dd)for(int i=1;i<8;i++){int nr=r+d[0]*i,nc=c+d[1]*i;if(!inBnd(nr,nc))break;if(b[nr][nc]!='.'){if(b[nr][nc]==B2||b[nr][nc]==Q)return true;break;}}
    for(int dr=-1;dr<=1;dr++)for(int dc=-1;dc<=1;dc++)if((dr||dc)&&inBnd(r+dr,c+dc)&&b[r+dr][c+dc]==K)return true;
    return false;
}

static void findKing(const char b[8][8], bool w, int& kr, int& kc) {
    char K=w?'K':'k';
    for(int r=0;r<8;r++)for(int c=0;c<8;c++)if(b[r][c]==K){kr=r;kc=c;return;}
    kr=kc=-1;
}

static void doMove(char b[8][8], const Move& m, int& epR, int& epC) {
    epR=epC=-1;
    char p=b[m.fr][m.fc];
    b[m.fr][m.fc]='.';
    b[m.tr][m.tc]=m.promo?(isW(p)?(char)toupper(m.promo):m.promo):p;
    if(m.ep)  b[isW(p)?m.tr+1:m.tr-1][m.tc]='.';
    if(m.castle){if(m.tc==6){b[m.tr][5]=b[m.tr][7];b[m.tr][7]='.';}else{b[m.tr][3]=b[m.tr][0];b[m.tr][0]='.';}}
    if((char)toupper(p)=='P'&&abs(m.tr-m.fr)==2){epR=(m.fr+m.tr)/2;epC=m.fc;}
}

static std::vector<Move> pseudoFor(const char b[8][8], int fr, int fc, int epR, int epC) {
    std::vector<Move> mv;
    char p=b[fr][fc]; if(p=='.') return mv;
    bool w=isW(p); char u=(char)toupper(p);
    auto add=[&](int tr,int tc,char pr=0,bool ep=false,bool cas=false){
        if(!inBnd(tr,tc))return;
        if(!ep&&!cas&&isFriend(b[tr][tc],w))return;
        mv.push_back({(signed char)fr,(signed char)fc,(signed char)tr,(signed char)tc,pr,ep,cas});
    };
    if(u=='P'){
        int dir=w?-1:1,sR=w?6:1,pR=w?0:7;
        if(inBnd(fr+dir,fc)&&b[fr+dir][fc]=='.'){
            if(fr+dir==pR){for(char pp:{'q','r','b','n'})add(fr+dir,fc,pp);}
            else{add(fr+dir,fc);if(fr==sR&&b[fr+2*dir][fc]=='.')add(fr+2*dir,fc);}
        }
        for(int dc:{-1,1}){
            int tr2=fr+dir,tc2=fc+dc; if(!inBnd(tr2,tc2))continue;
            if(isEnemy(b[tr2][tc2],w)){if(tr2==pR){for(char pp:{'q','r','b','n'})add(tr2,tc2,pp);}else add(tr2,tc2);}
            else if(tr2==epR&&tc2==epC)add(tr2,tc2,0,true);
        }
    }
    if(u=='N'){static const int kd[8][2]={{-2,-1},{-2,1},{-1,-2},{-1,2},{1,-2},{1,2},{2,-1},{2,1}};for(auto&d:kd)add(fr+d[0],fc+d[1]);}
    auto slide=[&](int dr,int dc){for(int i=1;i<8;i++){int r=fr+dr*i,c=fc+dc*i;if(!inBnd(r,c))break;add(r,c);if(b[r][c]!='.')break;}};
    if(u=='B'||u=='Q'){slide(1,1);slide(1,-1);slide(-1,1);slide(-1,-1);}
    if(u=='R'||u=='Q'){slide(0,1);slide(0,-1);slide(1,0);slide(-1,0);}
    if(u=='K'){for(int dr=-1;dr<=1;dr++)for(int dc=-1;dc<=1;dc++)if(dr||dc)add(fr+dr,fc+dc);}
    return mv;
}

static std::vector<Move> legalForBS(const BS& bs, int fr, int fc) {
    std::vector<Move> legal;
    char p=bs.board[fr][fc]; if(p=='.') return legal;
    bool w=isW(p);
    for(auto& m:pseudoFor(bs.board,fr,fc,bs.epR,bs.epC)){
        BS nx=bs; int er,ec; doMove(nx.board,m,er,ec);
        int kr,kc; findKing(nx.board,w,kr,kc);
        if(kr>=0&&!attacked(nx.board,kr,kc,!w)) legal.push_back(m);
    }
    if((char)toupper(p)=='K'){
        int kRow=w?7:0; bool km=w?bs.wKM:bs.bKM;
        if(!km&&fr==kRow&&fc==4&&!attacked(bs.board,kRow,4,!w)){
            // Kingside
            if(!(w?bs.wHRM:bs.bHRM)){
                if(bs.board[kRow][5]=='.'&&bs.board[kRow][6]=='.'&&
                   !attacked(bs.board,kRow,5,!w)&&!attacked(bs.board,kRow,6,!w))
                    legal.push_back({(signed char)fr,(signed char)fc,(signed char)kRow,6,0,false,true});
            }
            // Queenside
            if(!(w?bs.wARM:bs.bARM)){
                if(bs.board[kRow][3]=='.'&&bs.board[kRow][2]=='.'&&bs.board[kRow][1]=='.'&&
                   !attacked(bs.board,kRow,3,!w)&&!attacked(bs.board,kRow,2,!w))
                    legal.push_back({(signed char)fr,(signed char)fc,(signed char)kRow,2,0,false,true});
            }
        }
    }
    return legal;
}

static BS toBS() {
    BS bs; memcpy(bs.board,G.board,64);
    bs.wKM=G.wKM;bs.bKM=G.bKM;bs.wARM=G.wARM;bs.wHRM=G.wHRM;bs.bARM=G.bARM;bs.bHRM=G.bHRM;
    bs.epR=G.epR;bs.epC=G.epC;
    return bs;
}

static std::vector<Move> getLegal(int fr,int fc){ return legalForBS(toBS(),fr,fc); }

static bool anyLegal(const BS& bs, bool w){
    for(int r=0;r<8;r++)for(int c=0;c<8;c++)
        if(w?isW(bs.board[r][c]):isB(bs.board[r][c]))
            if(!legalForBS(bs,r,c).empty()) return true;
    return false;
}

static std::string toUCI(const Move& m){
    std::string s;
    s+=(char)('a'+m.fc);s+=(char)('0'+(8-m.fr));
    s+=(char)('a'+m.tc);s+=(char)('0'+(8-m.tr));
    if(m.promo)s+=m.promo; return s;
}

static BS applyToBS(const BS& bs, const Move& m){
    BS nx=bs; char p=nx.board[m.fr][m.fc];
    if(p=='K')nx.wKM=true; if(p=='k')nx.bKM=true;
    if(m.fr==7&&m.fc==0)nx.wARM=true; if(m.fr==7&&m.fc==7)nx.wHRM=true;
    if(m.fr==0&&m.fc==0)nx.bARM=true; if(m.fr==0&&m.fc==7)nx.bHRM=true;
    int er,ec; doMove(nx.board,m,er,ec); nx.epR=er; nx.epC=ec;
    return nx;
}

static void applyGlobal(const Move& m){
    char p=G.board[m.fr][m.fc];
    if(p=='K')G.wKM=true; if(p=='k')G.bKM=true;
    if(m.fr==7&&m.fc==0)G.wARM=true; if(m.fr==7&&m.fc==7)G.wHRM=true;
    if(m.fr==0&&m.fc==0)G.bARM=true; if(m.fr==0&&m.fc==7)G.bHRM=true;
    G.hist.push_back(toUCI(m));
    doMove(G.board,m,G.epR,G.epC);
    G.lastFR=m.fr;G.lastFC=m.fc;G.lastTR=m.tr;G.lastTC=m.tc;
    // Record position for repetition detection (reset on capture/pawn move)
    if(G.board[m.tr][m.tc]!='.'||(char)toupper(p)=='P') G.posHist.clear();
    G.posHist.push_back(zhash(toBS(),G.playerTurn));
}

// ─────────────────────── ZOBRIST ──────────────────────────────
static unsigned long long zrand(){
    static unsigned long long s=0xDEADBEEFCAFEBABEULL;
    s^=s>>12;s^=s<<25;s^=s>>27;return s*0x2545F4914F6CDD1DULL;
}
static int pieceIdx(char p){
    switch(p){case 'K':return 0;case 'Q':return 1;case 'R':return 2;case 'B':return 3;case 'N':return 4;case 'P':return 5;
               case 'k':return 6;case 'q':return 7;case 'r':return 8;case 'b':return 9;case 'n':return 10;case 'p':return 11;}
    return -1;
}
static void initZobrist(){
    for(auto&row:ZKEYS)for(auto&v:row)v=zrand();
    ZTURN=zrand();
    for(auto&v:ZEP)v=zrand();
    for(auto&v:ZCASTLE)v=zrand();
}
static unsigned long long zhash(const BS& bs, bool white){
    unsigned long long h=0;
    for(int r=0;r<8;r++)for(int c=0;c<8;c++){int i=pieceIdx(bs.board[r][c]);if(i>=0)h^=ZKEYS[i][r*8+c];}
    if(!white)h^=ZTURN;
    if(bs.epC>=0&&bs.epC<8)h^=ZEP[bs.epC];
    if(!bs.wKM&&!bs.wHRM)h^=ZCASTLE[0];
    if(!bs.wKM&&!bs.wARM)h^=ZCASTLE[1];
    if(!bs.bKM&&!bs.bHRM)h^=ZCASTLE[2];
    if(!bs.bKM&&!bs.bARM)h^=ZCASTLE[3];
    return h;
}

// ─────────────────────── EVALUATION ──────────────────────────
static const int PST_P[8][8]={ {0,0,0,0,0,0,0,0},{50,50,50,50,50,50,50,50},{10,10,20,30,30,20,10,10},{5,5,10,25,25,10,5,5},{0,0,0,20,20,0,0,0},{5,-5,-10,0,0,-10,-5,5},{5,10,10,-20,-20,10,10,5},{0,0,0,0,0,0,0,0} };
static const int PST_N[8][8]={ {-50,-40,-30,-30,-30,-30,-40,-50},{-40,-20,0,0,0,0,-20,-40},{-30,0,10,15,15,10,0,-30},{-30,5,15,20,20,15,5,-30},{-30,0,15,20,20,15,0,-30},{-30,5,10,15,15,10,5,-30},{-40,-20,0,5,5,0,-20,-40},{-50,-40,-30,-30,-30,-30,-40,-50} };
static const int PST_B[8][8]={ {-20,-10,-10,-10,-10,-10,-10,-20},{-10,0,0,0,0,0,0,-10},{-10,0,5,10,10,5,0,-10},{-10,5,5,10,10,5,5,-10},{-10,0,10,10,10,10,0,-10},{-10,10,10,10,10,10,10,-10},{-10,5,0,0,0,0,5,-10},{-20,-10,-10,-10,-10,-10,-10,-20} };
static const int PST_R[8][8]={ {0,0,0,0,0,0,0,0},{5,10,10,10,10,10,10,5},{-5,0,0,0,0,0,0,-5},{-5,0,0,0,0,0,0,-5},{-5,0,0,0,0,0,0,-5},{-5,0,0,0,0,0,0,-5},{-5,0,0,0,0,0,0,-5},{0,0,0,5,5,0,0,0} };
static const int PST_Q[8][8]={ {-20,-10,-10,-5,-5,-10,-10,-20},{-10,0,0,0,0,0,0,-10},{-10,0,5,5,5,5,0,-10},{-5,0,5,5,5,5,0,-5},{0,0,5,5,5,5,0,-5},{-10,5,5,5,5,5,0,-10},{-10,0,5,0,0,0,0,-10},{-20,-10,-10,-5,-5,-10,-10,-20} };
static const int PST_K[8][8]={ {-30,-40,-40,-50,-50,-40,-40,-30},{-30,-40,-40,-50,-50,-40,-40,-30},{-30,-40,-40,-50,-50,-40,-40,-30},{-30,-40,-40,-50,-50,-40,-40,-30},{-20,-30,-30,-40,-40,-30,-30,-20},{-10,-20,-20,-20,-20,-20,-20,-10},{20,20,0,0,0,0,20,20},{20,30,10,0,0,10,30,20} };

static int pval(char p){switch((char)toupper(p)){case 'P':return 100;case 'N':return 320;case 'B':return 330;case 'R':return 500;case 'Q':return 900;case 'K':return 20000;}return 0;}
static int pst(char p,int r,int c){int tr=isW(p)?r:7-r;switch((char)toupper(p)){case 'P':return PST_P[tr][c];case 'N':return PST_N[tr][c];case 'B':return PST_B[tr][c];case 'R':return PST_R[tr][c];case 'Q':return PST_Q[tr][c];case 'K':return PST_K[tr][c];}return 0;}

static int evalAbs(const BS& bs){
    int s=0;
    for(int r=0;r<8;r++)for(int c=0;c<8;c++){char p=bs.board[r][c];if(p=='.')continue;int v=pval(p)+pst(p,r,c);s+=isW(p)?v:-v;}
    return s;
}

// ─────────────── MOVE ORDERING ────────────────────────────────
static int mvScore(const Move& m, const char b[8][8], const Move& tt, int depth){
    if(mvEq(m,tt)) return 25000;
    char v=b[m.tr][m.tc];
    if(v!='.'||m.ep){ char a=b[m.fr][m.fc]; return 10000+pval(v)*10-pval(a); }
    if(m.promo) return 9000;
    if(depth>=0&&depth<64){
        if(mvEq(m,killers[depth][0])) return 8000;
        if(mvEq(m,killers[depth][1])) return 7000;
    }
    return 0;
}
static void sortMoves(std::vector<Move>& mv, const char b[8][8], const Move& tt, int depth=-1){
    std::stable_sort(mv.begin(),mv.end(),[&](const Move&a,const Move&b2){return mvScore(a,b,tt,depth)>mvScore(b2,b,tt,depth);});
}
static void storeKiller(int depth, const Move& m){
    if(depth<0||depth>=64) return;
    if(!mvEq(m,killers[depth][0])){killers[depth][1]=killers[depth][0];killers[depth][0]=m;}
}

// ─────────────────── QUIESCENCE SEARCH ───────────────────────
static int qsearch(const BS& bs, int alpha, int beta, bool white){
    int sp=evalAbs(bs); if(!white)sp=-sp;
    if(sp>=beta) return beta;
    alpha=std::max(alpha,sp);
    for(int r=0;r<8;r++)for(int c=0;c<8;c++){
        if(white?!isW(bs.board[r][c]):!isB(bs.board[r][c]))continue;
        std::vector<Move> caps;
        for(auto&m:legalForBS(bs,r,c))if(bs.board[m.tr][m.tc]!='.'||m.ep)caps.push_back(m);
        sortMoves(caps,bs.board,NULL_MV);
        for(auto&m:caps){
            int s=-qsearch(applyToBS(bs,m),-beta,-alpha,!white);
            if(s>=beta) return beta;
            alpha=std::max(alpha,s);
        }
    }
    return alpha;
}

// ─────────────────── NEGAMAX + TT ────────────────────────────
static int negamax(const BS& bs, int depth, int alpha, int beta, bool white){
    unsigned long long h=zhash(bs,white);
    TTEntry& tte=ttable[h&(TT_SIZE-1)];
    Move ttMv=NULL_MV;
    if(tte.hash==h && tte.depth>=depth){
        int s=tte.score;
        if(tte.flag==0) return s;
        if(tte.flag==2) alpha=std::max(alpha,s);
        if(tte.flag==1) beta =std::min(beta, s);
        if(alpha>=beta) return s;
        ttMv=tte.bestMv;
    }
    if(depth==0) return qsearch(bs,alpha,beta,white);

    // 3-fold repetition → draw
    int rCount=0;
    for(auto ph:G.posHist) if(ph==h) if(++rCount>=2) return 0;

    std::vector<Move> all;
    for(int r=0;r<8;r++)for(int c=0;c<8;c++)
        if(white?isW(bs.board[r][c]):isB(bs.board[r][c])){auto v=legalForBS(bs,r,c);all.insert(all.end(),v.begin(),v.end());}

    if(all.empty()){int kr,kc;findKing(bs.board,white,kr,kc);return attacked(bs.board,kr,kc,!white)?-INF+depth:0;}

    sortMoves(all,bs.board,ttMv,depth);

    int origAlpha=alpha, best=-INF; Move bestMv=all[0];
    for(auto&m:all){
        if(timeUp()) break;
        int s=-negamax(applyToBS(bs,m),depth-1,-beta,-alpha,!white);
        if(s>best){best=s;bestMv=m;}
        alpha=std::max(alpha,s);
        if(alpha>=beta){
            // Quiet move caused cutoff: store as killer
            if(bs.board[m.tr][m.tc]=='.'&&!m.ep&&!m.promo) storeKiller(depth,m);
            break;
        }
    }
    if(!timeUp()){
        tte.hash=h; tte.score=(short)best; tte.depth=(signed char)depth;
        tte.flag=(signed char)(best<=origAlpha?1:(best>=beta?2:0)); tte.bestMv=bestMv;
    }
    return best;
}

// ─────────────── ITERATIVE DEEPENING ROOT ────────────────────
struct AIParam{ BS bs; bool aiWhite; int maxDepth; int timeLimitMs; };

static DWORD WINAPI aiWorker(LPVOID p){
    AIParam* ap=(AIParam*)p;
    aiStartTick=GetTickCount(); aiTimeLimitMs=ap->timeLimitMs;
    memset(killers,0xff,sizeof(killers));
    Move best=NULL_MV;
    for(int d=1;d<=ap->maxDepth&&!timeUp();d++){
        std::vector<Move> all;
        for(int r=0;r<8;r++)for(int c=0;c<8;c++)
            if(ap->aiWhite?isW(ap->bs.board[r][c]):isB(ap->bs.board[r][c])){auto v=legalForBS(ap->bs,r,c);all.insert(all.end(),v.begin(),v.end());}
        if(all.empty())break;
        // Use TT best from previous iteration for ordering
        Move ttMv=NULL_MV;
        unsigned long long h=zhash(ap->bs,ap->aiWhite);
        TTEntry& tte=ttable[h&(TT_SIZE-1)];
        if(tte.hash==h)ttMv=tte.bestMv;
        sortMoves(all,ap->bs.board,ttMv,d-1);
        Move depthBest=NULL_MV; int bestVal=-INF;
        for(auto&m:all){
            if(timeUp())break;
            int s=-negamax(applyToBS(ap->bs,m),d-1,-INF,INF,!ap->aiWhite);
            if(s>bestVal){bestVal=s;depthBest=m;}
        }
        if(!mvNull(depthBest)&&!timeUp())best=depthBest;
    }
    Move* m=new Move(best);
    PostMessage(hWnd,WM_AI_DONE,0,(LPARAM)m);
    delete ap; return 0;
}

static void startAI(){
    if(G.aiBusy||G.gameOver)return;
    G.aiBusy=true;
    AIParam* p=new AIParam;
    p->bs=toBS(); p->aiWhite=!G.playerWhite;
    p->maxDepth=G.aiDepth;
    // Use 1/20 of remaining clock, clamped 300ms–8000ms
    int clk=G.aiClockMs; p->timeLimitMs=std::max(300,std::min(8000,clk/20));
    HANDLE h=CreateThread(NULL,0,aiWorker,p,0,NULL); CloseHandle(h);
}

// ─────────────────────── UNDO ─────────────────────────────────
static void pushUndo(){
    UndoInfo ui; memcpy(ui.board,G.board,64);
    ui.wKM=G.wKM;ui.bKM=G.bKM;ui.wARM=G.wARM;ui.wHRM=G.wHRM;ui.bARM=G.bARM;ui.bHRM=G.bHRM;
    ui.epR=G.epR;ui.epC=G.epC;ui.playerTurn=G.playerTurn;ui.inCheck=G.inCheck;
    ui.lastFR=G.lastFR;ui.lastFC=G.lastFC;ui.lastTR=G.lastTR;ui.lastTC=G.lastTC;
    G.undoStack.push_back(ui);
}
static void popUndo(){
    if(G.undoStack.empty())return;
    UndoInfo& ui=G.undoStack.back();
    memcpy(G.board,ui.board,64);
    G.wKM=ui.wKM;G.bKM=ui.bKM;G.wARM=ui.wARM;G.wHRM=ui.wHRM;G.bARM=ui.bARM;G.bHRM=ui.bHRM;
    G.epR=ui.epR;G.epC=ui.epC;G.playerTurn=ui.playerTurn;G.inCheck=ui.inCheck;
    G.lastFR=ui.lastFR;G.lastFC=ui.lastFC;G.lastTR=ui.lastTR;G.lastTC=ui.lastTC;
    G.undoStack.pop_back();
    if(!G.hist.empty())G.hist.pop_back();
    G.selR=G.selC=-1;G.legal.clear();
    G.gameOver=false;
}
static void doUndo(){
    // Undo 2 half-moves (AI response + player move) to restore player's turn
    int n=(int)G.undoStack.size();
    if(n==0)return;
    popUndo(); if(n>=2)popUndo();
    G.status="Hoan tac. Den luot cua ban.";
    InvalidateRect(hWnd,NULL,FALSE);
}

// ─────────────────────── FEN / PGN ───────────────────────────
static bool loadFEN(const char* fen){
    // Clear board
    for(int r=0;r<8;r++)for(int c=0;c<8;c++)G.board[r][c]='.';
    const char* p=fen; int r=0,c=0;
    while(*p&&*p!=' '){
        if(*p=='/'){r++;c=0;}
        else if(*p>='1'&&*p<='8')c+=*p-'0';
        else if(c<8&&r<8)G.board[r][c++]=*p;
        p++;
    }
    if(*p==' ')p++;
    bool fenWhite=(*p=='w');
    G.playerTurn=(fenWhite==G.playerWhite);
    while(*p&&*p!=' ')p++;if(*p==' ')p++;
    G.wKM=G.bKM=G.wHRM=G.wARM=G.bHRM=G.bARM=true;
    while(*p&&*p!=' '){
        if(*p=='K')G.wHRM=false; if(*p=='Q')G.wARM=false;
        if(*p=='k')G.bHRM=false; if(*p=='q')G.bARM=false;
        p++;
    }
    if(*p==' ')p++;
    G.epR=G.epC=-1;
    if(*p!='-'&&*(p+1)){G.epC=p[0]-'a';G.epR=8-(p[1]-'0');}
    G.selR=G.selC=-1;G.legal.clear();G.lastFR=G.lastFC=G.lastTR=G.lastTC=-1;
    G.inCheck=G.gameOver=G.aiBusy=false;G.undoStack.clear();G.hist.clear();
    return true;
}
static std::string toFEN(){
    std::string fen;
    for(int r=0;r<8;r++){int e=0;for(int c=0;c<8;c++){if(G.board[r][c]=='.')e++;else{if(e){fen+=(char)('0'+e);e=0;}fen+=G.board[r][c];}}if(e)fen+=(char)('0'+e);if(r<7)fen+='/';}
    bool wt=(G.playerTurn==G.playerWhite);
    fen+=wt?" w ":" b ";
    std::string ca;
    if(!G.wKM&&!G.wHRM)ca+='K';if(!G.wKM&&!G.wARM)ca+='Q';
    if(!G.bKM&&!G.bHRM)ca+='k';if(!G.bKM&&!G.bARM)ca+='q';
    fen+=ca.empty()?"-":ca; fen+=" ";
    if(G.epC>=0){fen+=(char)('a'+G.epC);fen+=(char)('0'+(8-G.epR));}else fen+="-";
    fen+=" 0 1"; return fen;
}
static void loadFENFromClipboard(){
    if(!OpenClipboard(hWnd))return;
    HANDLE h=GetClipboardData(CF_TEXT);
    if(h){const char* t=(const char*)GlobalLock(h);if(t){char buf[256];strncpy(buf,t,255);buf[255]=0;loadFEN(buf);}GlobalUnlock(h);}
    CloseClipboard();
    G.status="FEN da tai tu clipboard.";
    InvalidateRect(hWnd,NULL,FALSE);
}
static void savePGN(){
    wchar_t fn[MAX_PATH]=L"game.pgn";
    OPENFILENAMEW ofn={};ofn.lStructSize=sizeof(ofn);ofn.hwndOwner=hWnd;
    ofn.lpstrFilter=L"PGN Files\0*.pgn\0All Files\0*.*\0";
    ofn.lpstrFile=fn;ofn.nMaxFile=MAX_PATH;
    ofn.Flags=OFN_OVERWRITEPROMPT;ofn.lpstrDefExt=L"pgn";
    if(!GetSaveFileNameW(&ofn))return;
    FILE* f=_wfopen(fn,L"w");if(!f)return;
    const char* wp=G.playerWhite?"Player":"AI";
    const char* bp=G.playerWhite?"AI":"Player";
    fprintf(f,"[Event \"Chess Game\"]\n[White \"%s\"]\n[Black \"%s\"]\n[FEN \"%s\"]\n\n",wp,bp,toFEN().c_str());
    for(int i=0;i<(int)G.hist.size();i++){if(i%2==0)fprintf(f,"%d. ",i/2+1);fprintf(f,"%s ",G.hist[i].c_str());}
    fprintf(f,"*\n");fclose(f);
    G.status="PGN da luu!";InvalidateRect(hWnd,NULL,FALSE);
}

// ─────────────────────── SOUND ────────────────────────────────
struct BP{int f,d;};
static DWORD WINAPI bfn(LPVOID p){BP*b=(BP*)p;Beep(b->f,b->d);delete b;return 0;}
static void bplay(int f,int d){BP*b=new BP{f,d};HANDLE h=CreateThread(NULL,0,bfn,b,0,NULL);CloseHandle(h);}
static void sndMove()   {bplay(440,35);}
static void sndCapture(){bplay(300,70);}
static void sndCheck()  {bplay(880,70);}
static void sndEnd()    {bplay(440,160);}

// ─────────────────────── ANIMATION ───────────────────────────
static void startAnim(const Move& m, char piece){
    G.anim.active=true;G.anim.piece=piece;
    G.anim.cx=(float)(OX+m.fc*SQ+SQ/2);G.anim.cy=(float)(OY+m.fr*SQ+SQ/2);
    G.anim.tx=(float)(OX+m.tc*SQ+SQ/2);G.anim.ty=(float)(OY+m.tr*SQ+SQ/2);
    G.anim.elapsed=0;G.anim.mv=m;
    SetTimer(hWnd,TIMER_ANIM,ANIM_MS,NULL);
}

// ─────────────────────── RENDERING ───────────────────────────
static const wchar_t* glyph(char p){
    switch(p){case 'K':return L"♔";case 'Q':return L"♕";case 'R':return L"♖";case 'B':return L"♗";case 'N':return L"♘";case 'P':return L"♙";
               case 'k':return L"♚";case 'q':return L"♛";case 'r':return L"♜";case 'b':return L"♝";case 'n':return L"♞";case 'p':return L"♟";}
    return L"";
}
static int pngIdx(char p){
    switch(p){case 'K':return 0;case 'Q':return 1;case 'R':return 2;case 'B':return 3;case 'N':return 4;case 'P':return 5;
               case 'k':return 6;case 'q':return 7;case 'r':return 8;case 'b':return 9;case 'n':return 10;case 'p':return 11;}
    return -1;
}
static void drawPiece(HDC hdc, char p, int px, int py, int sz=SQ){
    int idx=pngIdx(p);
    if(hasPNG&&idx>=0&&pieceImgs[idx]){
        Gdiplus::Graphics gfx(hdc);
        gfx.SetInterpolationMode(Gdiplus::InterpolationModeHighQualityBicubic);
        gfx.SetSmoothingMode(Gdiplus::SmoothingModeAntiAlias);
        int x=px-sz/2+3,y=py-sz/2+3,s2=sz-6;
        gfx.DrawImage(pieceImgs[idx],x,y,s2,s2);
        return;
    }
    // Unicode fallback
    HFONT old=SelectFont(hdc,hPF); SetBkMode(hdc,TRANSPARENT);
    RECT sq={px-sz/2,py-sz/2,px+sz/2,py+sz/2};
    if(isW(p)){
        SetTextColor(hdc,RGB(60,60,60));RECT sh=sq;sh.left+=3;sh.top+=3;
        DrawTextW(hdc,glyph(p),-1,&sh,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
        SetTextColor(hdc,RGB(255,255,255));
    }else{
        SetTextColor(hdc,RGB(180,180,180));RECT sh=sq;sh.left+=2;sh.top+=2;
        DrawTextW(hdc,glyph(p),-1,&sh,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
        SetTextColor(hdc,RGB(20,20,20));
    }
    DrawTextW(hdc,glyph(p),-1,&sq,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
    SelectFont(hdc,old);
}

static std::wstring fmtClock(int ms){
    if(ms<0)ms=0;
    int m=ms/60000,s=(ms%60000)/1000;
    wchar_t buf[16]; wsprintfW(buf,L"%d:%02d",m,s); return buf;
}

static void render(HDC hdc){
    int ckR=-1,ckC=-1;
    if(G.inCheck){bool cw=G.playerTurn?G.playerWhite:!G.playerWhite;findKing(G.board,cw,ckR,ckC);}

    for(int r=0;r<8;r++)for(int c=0;c<8;c++){
        bool lt=(r+c)%2==0;
        COLORREF col=lt?C_LIGHT:C_DARK;
        if((r==G.lastFR&&c==G.lastFC)||(r==G.lastTR&&c==G.lastTC))col=C_LAST;
        if(r==G.selR&&c==G.selC)col=C_SEL;
        if(G.drag.active&&r==G.drag.srcR&&c==G.drag.srcC)col=C_SEL;
        if(r==ckR&&c==ckC)col=C_CHK;
        RECT sq={OX+c*SQ,OY+r*SQ,OX+c*SQ+SQ,OY+r*SQ+SQ};
        HBRUSH br=CreateSolidBrush(col);FillRect(hdc,&sq,br);DeleteObject(br);
        // Legal move dots
        for(auto&m:G.legal){
            if(m.tr!=r||m.tc!=c)continue;
            int cx=OX+c*SQ+SQ/2,cy=OY+r*SQ+SQ/2;
            if(G.board[r][c]!='.'){
                HPEN pen=CreatePen(PS_SOLID,6,lt?RGB(90,110,55):RGB(80,100,45));
                HGDIOBJ op=SelectObject(hdc,pen);SelectObject(hdc,GetStockObject(NULL_BRUSH));
                Ellipse(hdc,OX+c*SQ+5,OY+r*SQ+5,OX+c*SQ+SQ-5,OY+r*SQ+SQ-5);
                SelectObject(hdc,op);DeleteObject(pen);
            }else{
                COLORREF dc=lt?RGB(140,155,95):RGB(95,120,60);
                HPEN pen=CreatePen(PS_SOLID,1,dc);HBRUSH db=CreateSolidBrush(dc);
                HGDIOBJ op=SelectObject(hdc,pen),ob=SelectObject(hdc,db);
                Ellipse(hdc,cx-13,cy-13,cx+13,cy+13);
                SelectObject(hdc,op);SelectObject(hdc,ob);DeleteObject(pen);DeleteObject(db);
            }
        }
    }
    // Labels inside squares (Chess.com style)
    HFONT olds=SelectFont(hdc,hSF); SetBkMode(hdc,TRANSPARENT);
    for(int i=0;i<8;i++){
        SetTextColor(hdc,(i%2==0)?C_DARK:C_LIGHT);
        RECT rr={OX+3,OY+i*SQ+3,OX+18,OY+i*SQ+19};
        wchar_t buf[4];wsprintfW(buf,L"%d",8-i);DrawTextW(hdc,buf,-1,&rr,DT_LEFT|DT_TOP);
        SetTextColor(hdc,((7-i)%2==0)?C_DARK:C_LIGHT);
        RECT fr2={OX+i*SQ+SQ-17,OY+8*SQ-18,OX+i*SQ+SQ-2,OY+8*SQ-3};
        wchar_t fc[4]={(wchar_t)('a'+i),0};DrawTextW(hdc,fc,-1,&fr2,DT_RIGHT|DT_BOTTOM);
    }
    SelectFont(hdc,olds);
    // Pieces (skip anim dest + drag src)
    for(int r=0;r<8;r++)for(int c=0;c<8;c++){
        char p=G.board[r][c];if(p=='.')continue;
        if(G.anim.active&&r==G.anim.mv.tr&&c==G.anim.mv.tc)continue;
        if(G.drag.active&&r==G.drag.srcR&&c==G.drag.srcC)continue;
        drawPiece(hdc,p,OX+c*SQ+SQ/2,OY+r*SQ+SQ/2);
    }
    if(G.anim.active)drawPiece(hdc,G.anim.piece,(int)G.anim.cx,(int)G.anim.cy);
    if(G.drag.active)drawPiece(hdc,G.drag.piece,G.drag.cx,G.drag.cy,SQ+10);

    // ── SIDE PANEL ──
    int px=OX+8*SQ+8;
    RECT panel={px-2,0,WIN_W,WIN_H};
    HBRUSH pb=CreateSolidBrush(C_PANEL);FillRect(hdc,&panel,pb);DeleteObject(pb);
    HPEN dp=CreatePen(PS_SOLID,1,RGB(55,60,70));HGDIOBJ dop=SelectObject(hdc,dp);
    MoveToEx(hdc,px-2,0,NULL);LineTo(hdc,px-2,WIN_H);
    SelectObject(hdc,dop);DeleteObject(dp);
    SetBkMode(hdc,TRANSPARENT);
    // AI player label + clock
    HFONT oldbf=SelectFont(hdc,hBF);
    SetTextColor(hdc,C_TEXT);
    std::string aiStr=G.playerWhite?"Black (AI)":"White (AI)";
    std::wstring aiW(aiStr.begin(),aiStr.end());
    RECT aiLbl={px+6,6,WIN_W-6,26};DrawTextW(hdc,aiW.c_str(),-1,&aiLbl,DT_LEFT|DT_VCENTER|DT_SINGLELINE);
    std::wstring aiClk=fmtClock(G.aiClockMs);
    RECT aiClkR={px+6,6,WIN_W-6,26};SetTextColor(hdc,G.aiBusy?RGB(250,200,80):C_TEXT);
    DrawTextW(hdc,aiClk.c_str(),-1,&aiClkR,DT_RIGHT|DT_VCENTER|DT_SINGLELINE);
    // Player label + clock
    SetTextColor(hdc,C_TEXT);
    std::string plStr=G.playerWhite?"White (You)":"Black (You)";
    std::wstring plW(plStr.begin(),plStr.end());
    RECT plLbl={px+6,WIN_H-30,WIN_W-6,WIN_H-8};DrawTextW(hdc,plW.c_str(),-1,&plLbl,DT_LEFT|DT_VCENTER|DT_SINGLELINE);
    std::wstring plClk=fmtClock(G.playerClockMs);
    SetTextColor(hdc,G.playerTurn?RGB(250,200,80):C_TEXT);
    DrawTextW(hdc,plClk.c_str(),-1,&plLbl,DT_RIGHT|DT_VCENTER|DT_SINGLELINE);
    SelectFont(hdc,oldbf);
    // Dividers
    HPEN lp=CreatePen(PS_SOLID,1,RGB(55,60,70));HGDIOBJ lop=SelectObject(hdc,lp);
    MoveToEx(hdc,px,32,NULL);LineTo(hdc,WIN_W,32);
    MoveToEx(hdc,px,WIN_H-34,NULL);LineTo(hdc,WIN_W,WIN_H-34);
    SelectObject(hdc,lop);DeleteObject(lp);
    // Move history (scrollable with mouse wheel)
    HFONT oldmf=SelectFont(hdc,hSF);
    int visLines=(WIN_H-74)/18; // lines that fit between dividers
    int totalPairs=(int)G.hist.size()/2+((G.hist.size()%2)?1:0);
    int scrollOff=std::max(0,std::min(G.histScroll,std::max(0,totalPairs-visLines)));
    int hy=38;
    for(int pair=scrollOff;pair<totalPairs&&hy<WIN_H-38;pair++){
        int i=pair*2;
        std::string w2=G.hist[i],b2=(i+1<(int)G.hist.size())?G.hist[i+1]:"";
        wchar_t line[48];wsprintfW(line,L"%2d. %-7hs%hs",pair+1,w2.c_str(),b2.c_str());
        bool isLast=(pair==totalPairs-1);
        SetTextColor(hdc,isLast?RGB(230,230,180):RGB(150,155,160));
        RECT lr={px+6,hy,WIN_W-4,hy+18};DrawTextW(hdc,line,-1,&lr,DT_LEFT|DT_VCENTER|DT_SINGLELINE);
        hy+=18;
    }
    // Scroll indicator
    if(totalPairs>visLines){
        SetTextColor(hdc,RGB(70,75,85));
        RECT sr2={px+6,WIN_H-36,WIN_W-4,WIN_H-20};
        DrawTextW(hdc,L"↑↓ cuon lich su",-1,&sr2,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
    }
    SelectFont(hdc,oldmf);
    // Status bar (below board)
    RECT sr={0,OY+8*SQ+2,OX+8*SQ,WIN_H};
    HBRUSH sb=CreateSolidBrush(C_BG);FillRect(hdc,&sr,sb);DeleteObject(sb);
    HFONT oldsf2=SelectFont(hdc,hBF);
    SetBkMode(hdc,TRANSPARENT);SetTextColor(hdc,RGB(220,220,100));
    std::wstring ws(G.status.begin(),G.status.end());
    DrawTextW(hdc,ws.c_str(),-1,&sr,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
    SelectFont(hdc,oldsf2);
    // Keyboard hint bar
    RECT hr={OX+8*SQ+2,OY+8*SQ+2,WIN_W,WIN_H};
    HFONT oldh=SelectFont(hdc,hSF);SetTextColor(hdc,RGB(90,95,105));SetBkMode(hdc,TRANSPARENT);
    DrawTextW(hdc,L"^Z Undo  ^N New  ^F FEN  ^S PGN",-1,&hr,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
    SelectFont(hdc,oldh);
}

// ─────────────────────── PROMOTION PICKER ────────────────────
static char askPromo(){
    int r=MessageBoxW(hWnd,
        L"Phong cap:\n\nYes = Hau (Q)  |  No = Xe (R)\n(Nhan Cancel = Tuong (B) / Phong (N))",
        L"Phong cap",MB_YESNOCANCEL|MB_ICONQUESTION);
    if(r==IDYES)   return 'q';
    if(r==IDNO)    return 'r';
    // Cancel => second dialog for minor pieces
    int r2=MessageBoxW(hWnd,L"Yes = Tuong (B)\nNo  = Phong (N)",L"Phong cap",MB_YESNO|MB_ICONQUESTION);
    return (r2==IDYES)?'b':'n';
}

// ─────────────────────── WNDPROC ──────────────────────────────
// Pick promotion piece for player moves, then play it
static void handlePlayerMove(Move m){
    if(m.promo){
        char chosen=askPromo();
        // Find the matching legal move with the chosen promo piece
        for(auto& lm:G.legal){
            if(lm.fr==m.fr&&lm.fc==m.fc&&lm.tr==m.tr&&lm.tc==m.tc&&lm.promo==chosen){
                m=lm; break;
            }
        }
    }
    handleMove(m);
}

static void handleMove(const Move& m){
    // Called when a legal move is confirmed (click or drop)
    pushUndo();
    bool cap=G.board[m.tr][m.tc]!='.'||m.ep;
    applyGlobal(m);
    char animPiece=G.board[m.tr][m.tc];
    startAnim(m,animPiece);
    G.selR=G.selC=-1;G.legal.clear();
    if(cap)sndCapture();else sndMove();
    BS bs=toBS();
    bool oppW=!G.playerWhite;
    int kr,kc;findKing(G.board,oppW,kr,kc);
    G.inCheck=(kr>=0&&attacked(G.board,kr,kc,G.playerWhite));
    if(!anyLegal(bs,oppW)){
        G.gameOver=true;G.status=G.inCheck?"CHIEU TUONG! Ban da thang!":"HOA CO (Pat)!";sndEnd();
    }else{
        G.playerTurn=false;
        G.status=G.inCheck?"AI bi chieu! Dang suy nghi...":"AI dang suy nghi...";
        if(G.inCheck)sndCheck();
        // AI starts in TIMER_ANIM after animation
    }
    InvalidateRect(hWnd,NULL,FALSE);
}

static LRESULT CALLBACK WndProc(HWND hw, UINT msg, WPARAM wp, LPARAM lp){
    switch(msg){
    case WM_PAINT:{
        PAINTSTRUCT ps;HDC hdc=BeginPaint(hw,&ps);
        RECT rc;GetClientRect(hw,&rc);
        HDC mem=CreateCompatibleDC(hdc);
        HBITMAP bmp=CreateCompatibleBitmap(hdc,rc.right,rc.bottom);
        HGDIOBJ old=SelectObject(mem,bmp);
        HBRUSH bg=CreateSolidBrush(C_BG);FillRect(mem,&rc,bg);DeleteObject(bg);
        render(mem);
        BitBlt(hdc,0,0,rc.right,rc.bottom,mem,0,0,SRCCOPY);
        SelectObject(mem,old);DeleteObject(bmp);DeleteDC(mem);
        EndPaint(hw,&ps);return 0;
    }
    case WM_TIMER:
        if(wp==TIMER_ANIM&&G.anim.active){
            G.anim.elapsed+=ANIM_MS;
            float t=(float)G.anim.elapsed/ANIM_DUR;if(t>1.f)t=1.f;
            float e=1.f-(1.f-t)*(1.f-t)*(1.f-t); // ease-out cubic
            float sx=(float)(OX+G.anim.mv.fc*SQ+SQ/2),sy=(float)(OY+G.anim.mv.fr*SQ+SQ/2);
            G.anim.cx=sx+(G.anim.tx-sx)*e;G.anim.cy=sy+(G.anim.ty-sy)*e;
            if(t>=1.f){KillTimer(hw,TIMER_ANIM);G.anim.active=false;if(!G.playerTurn&&!G.gameOver&&!G.aiBusy)startAI();}
            InvalidateRect(hw,NULL,FALSE);
        }
        if(wp==TIMER_CLOCK&&!G.gameOver&&!G.anim.active){
            if(G.playerTurn&&!G.aiBusy){G.playerClockMs-=100;if(G.playerClockMs<=0){G.playerClockMs=0;G.gameOver=true;G.status="HET GIO! Ban thua!";sndEnd();}}
            else if(!G.playerTurn&&G.aiBusy){G.aiClockMs-=100;if(G.aiClockMs<=0){G.aiClockMs=0;G.gameOver=true;G.status="HET GIO! AI thua!";sndEnd();}}
            InvalidateRect(hw,NULL,FALSE);
        }
        break;
    case WM_LBUTTONDOWN:{
        if(G.gameOver||G.anim.active)break;
        int mx=GET_X_LPARAM(lp),my=GET_Y_LPARAM(lp);
        int col=(mx-OX)/SQ,row=(my-OY)/SQ;
        bool onBoard=(col>=0&&col<8&&row>=0&&row<8);
        if(!G.playerTurn){break;}
        if(!onBoard){G.selR=G.selC=-1;G.legal.clear();InvalidateRect(hw,NULL,FALSE);break;}
        // Try apply legal move
        if(G.selR>=0){
            for(auto&m:G.legal){
                if(m.tr==row&&m.tc==col){handlePlayerMove(m);return 0;}
            }
        }
        // Start drag or select
        char p=G.board[row][col];
        bool own=G.playerWhite?isW(p):isB(p);
        if(own){
            G.selR=row;G.selC=col;G.legal=getLegal(row,col);
            G.drag.active=true;G.drag.srcR=row;G.drag.srcC=col;G.drag.cx=mx;G.drag.cy=my;G.drag.piece=p;
            SetCapture(hw);
        }else{G.selR=G.selC=-1;G.legal.clear();}
        InvalidateRect(hw,NULL,FALSE);break;
    }
    case WM_MOUSEMOVE:
        if(G.drag.active){G.drag.cx=GET_X_LPARAM(lp);G.drag.cy=GET_Y_LPARAM(lp);InvalidateRect(hw,NULL,FALSE);}
        break;
    case WM_LBUTTONUP:{
        if(!G.drag.active)break;
        ReleaseCapture();
        int mx=GET_X_LPARAM(lp),my=GET_Y_LPARAM(lp);
        int col=(mx-OX)/SQ,row=(my-OY)/SQ;
        G.drag.active=false;
        if(inBnd(row,col)&&G.playerTurn&&!G.gameOver){
            for(auto&m:G.legal){if(m.tr==row&&m.tc==col){handlePlayerMove(m);return 0;}}
        }
        InvalidateRect(hw,NULL,FALSE);break;
    }
    case WM_AI_DONE:{
        Move* m=(Move*)lp;G.aiBusy=false;
        if(!m||mvNull(*m)){G.gameOver=true;G.status="AI het nuoc. Ban da thang!";sndEnd();}
        else{
            pushUndo();
            bool cap=G.board[m->tr][m->tc]!='.'||m->ep;
            applyGlobal(*m);char animPiece=G.board[m->tr][m->tc];
            startAnim(*m,animPiece);
            if(cap)sndCapture();else sndMove();
            BS bs=toBS();int kr,kc;findKing(G.board,G.playerWhite,kr,kc);
            G.inCheck=(kr>=0&&attacked(G.board,kr,kc,!G.playerWhite));
            if(!anyLegal(bs,G.playerWhite)){G.gameOver=true;G.status=G.inCheck?"CHIEU TUONG! AI da thang!":"HOA CO (Pat)!";sndEnd();}
            else{G.playerTurn=true;G.status=G.inCheck?"Ban bi chieu! Den luot cua ban.":"Den luot cua ban.";if(G.inCheck)sndCheck();}
        }
        delete m;InvalidateRect(hw,NULL,FALSE);break;
    }
    case WM_KEYDOWN:{
        bool ctrl=(GetKeyState(VK_CONTROL)&0x8000)!=0;
        if(ctrl&&wp=='Z'){if(!G.aiBusy&&!G.anim.active)doUndo();}
        if(ctrl&&wp=='F'){if(!G.aiBusy&&!G.anim.active)loadFENFromClipboard();}
        if(ctrl&&wp=='S')savePGN();
        if(ctrl&&wp=='N')startNewGame();
        if(wp==VK_ESCAPE){G.selR=G.selC=-1;G.legal.clear();G.drag.active=false;ReleaseCapture();InvalidateRect(hw,NULL,FALSE);}
        break;
    }
    case WM_MOUSEWHEEL:{
        int delta=GET_WHEEL_DELTA_WPARAM(wp)/WHEEL_DELTA;
        int maxScroll=std::max(0,(int)G.hist.size()/2-13);
        G.histScroll=std::max(0,std::min(maxScroll,G.histScroll-delta));
        InvalidateRect(hw,NULL,FALSE);break;
    }
    case WM_DESTROY:
        KillTimer(hw,TIMER_ANIM);KillTimer(hw,TIMER_CLOCK);
        DeleteObject(hPF);DeleteObject(hSF);DeleteObject(hBF);
        for(int i=0;i<12;i++)if(pieceImgs[i])delete pieceImgs[i];
        Gdiplus::GdiplusShutdown(gdipToken);
        PostQuitMessage(0);return 0;
    }
    return DefWindowProc(hw,msg,wp,lp);
}

// ─────────────────────── INIT ─────────────────────────────────
static void loadPieceImages(){
    const wchar_t* names[]={L"pieces\\wK.png",L"pieces\\wQ.png",L"pieces\\wR.png",L"pieces\\wB.png",L"pieces\\wN.png",L"pieces\\wP.png",
                             L"pieces\\bK.png",L"pieces\\bQ.png",L"pieces\\bR.png",L"pieces\\bB.png",L"pieces\\bN.png",L"pieces\\bP.png"};
    hasPNG=true;
    for(int i=0;i<12;i++){
        pieceImgs[i]=new Gdiplus::Bitmap(names[i]);
        if(pieceImgs[i]->GetLastStatus()!=Gdiplus::Ok){hasPNG=false;delete pieceImgs[i];pieceImgs[i]=nullptr;}
    }
}
static void initGame(){
    const char* back="rnbqkbnr";
    for(int c=0;c<8;c++){G.board[0][c]=back[c];G.board[1][c]='p';for(int r=2;r<6;r++)G.board[r][c]='.';G.board[6][c]='P';G.board[7][c]=(char)toupper(back[c]);}
    G.wKM=G.bKM=G.wARM=G.wHRM=G.bARM=G.bHRM=false;G.epR=G.epC=-1;
    G.selR=G.selC=-1;G.legal.clear();G.lastFR=G.lastFC=G.lastTR=G.lastTC=-1;
    G.inCheck=G.gameOver=G.aiBusy=G.anim.active=G.drag.active=false;
    G.undoStack.clear();G.hist.clear();G.posHist.clear();G.histScroll=0;
    memset(killers,0xff,sizeof(killers)); // -1 = null
    memset(ttable,0,sizeof(ttable));
}

static void startNewGame(){
    if(G.aiBusy){G.status="AI dang tinh, vui long doi...";InvalidateRect(hWnd,NULL,FALSE);return;}
    // Re-ask settings
    int r1=MessageBoxW(hWnd,L"Do kho:\nYes=De/TB  No=Kho/CG",L"Do kho",MB_YESNO);
    if(r1==IDYES){int r2=MessageBoxW(hWnd,L"Yes=De(2)  No=TB(3)",L"Do kho",MB_YESNO);G.aiDepth=(r2==IDYES)?2:3;}
    else         {int r2=MessageBoxW(hWnd,L"Yes=Kho(4)  No=CG(5)",L"Do kho",MB_YESNO);G.aiDepth=(r2==IDYES)?4:5;}
    int rt=MessageBoxW(hWnd,L"Thoi gian:\nYes=5ph  No=10ph",L"Thoi gian",MB_YESNO);
    G.playerClockMs=G.aiClockMs=(rt==IDYES)?5*60000:10*60000;
    int rc=MessageBoxW(hWnd,L"Chon quan:\nYes=Trang  No=Den",L"Chon quan",MB_YESNO);
    G.playerWhite=(rc==IDYES);
    initGame();
    if(!G.playerWhite){G.playerTurn=false;G.status="AI dang di nuoc dau...";startAI();}
    else{G.playerTurn=true;G.status="Den luot cua ban. Click hoac keo quan.";}
    InvalidateRect(hWnd,NULL,FALSE);
}

// ─────────────────────── WINMAIN ──────────────────────────────
int WINAPI WinMain(HINSTANCE hInst,HINSTANCE,LPSTR,int nShow){
    Gdiplus::GdiplusStartupInput gsi;
    Gdiplus::GdiplusStartup(&gdipToken,&gsi,NULL);
    initZobrist();
    memset(ttable,0,sizeof(ttable));

    // Difficulty
    int r1=MessageBoxW(NULL,L"Do kho:\n\nYes = De / Trung binh\nNo  = Kho / Chuyen gia",L"Thiet lap",MB_YESNO|MB_ICONQUESTION);
    if(r1==IDYES){int r2=MessageBoxW(NULL,L"Yes = De (depth 2)\nNo  = Trung binh (depth 3)",L"Do kho",MB_YESNO);G.aiDepth=(r2==IDYES)?2:3;}
    else         {int r2=MessageBoxW(NULL,L"Yes = Kho (depth 4)\nNo  = Chuyen gia (depth 5)",L"Do kho",MB_YESNO);G.aiDepth=(r2==IDYES)?4:5;}
    // Time control
    int rt=MessageBoxW(NULL,L"Thoi gian moi ben:\n\nYes = 5 phut\nNo  = 10 phut",L"Thoi gian",MB_YESNO|MB_ICONQUESTION);
    G.playerClockMs=G.aiClockMs=(rt==IDYES)?5*60000:10*60000;
    // Color
    int rc=MessageBoxW(NULL,L"Chon quan:\n\nYes = Trang (di truoc)\nNo  = Den (di sau)",L"Chon quan",MB_YESNO|MB_ICONQUESTION);
    G.playerWhite=(rc==IDYES);

    initGame();
    loadPieceImages();

    WNDCLASSW wc={};
    wc.lpfnWndProc=WndProc;wc.hInstance=hInst;wc.hbrBackground=(HBRUSH)(COLOR_WINDOW+1);
    wc.lpszClassName=L"ChessApp";wc.hCursor=LoadCursor(NULL,IDC_ARROW);
    RegisterClassW(&wc);

    hWnd=CreateWindowW(L"ChessApp",L"Co Vua  •  Ctrl+Z Undo  Ctrl+N New  Ctrl+F FEN  Ctrl+S PGN",
        WS_OVERLAPPED|WS_CAPTION|WS_SYSMENU|WS_MINIMIZEBOX,
        CW_USEDEFAULT,CW_USEDEFAULT,WIN_W+16,WIN_H+39,NULL,NULL,hInst,NULL);

    hPF=CreateFontW(56,0,0,0,FW_NORMAL,0,0,0,DEFAULT_CHARSET,OUT_DEFAULT_PRECIS,CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,DEFAULT_PITCH,L"Segoe UI Symbol");
    hSF=CreateFontW(14,0,0,0,FW_NORMAL,0,0,0,DEFAULT_CHARSET,OUT_DEFAULT_PRECIS,CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,DEFAULT_PITCH,L"Consolas");
    hBF=CreateFontW(15,0,0,0,FW_BOLD, 0,0,0,DEFAULT_CHARSET,OUT_DEFAULT_PRECIS,CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,DEFAULT_PITCH,L"Segoe UI");

    SetTimer(hWnd,TIMER_CLOCK,100,NULL);

    if(!G.playerWhite){G.playerTurn=false;G.status="AI dang di nuoc dau...";startAI();}
    else              {G.playerTurn=true; G.status="Den luot cua ban. Click hoac keo quan.";}

    ShowWindow(hWnd,nShow);UpdateWindow(hWnd);
    MSG msg;while(GetMessage(&msg,NULL,0,0)){TranslateMessage(&msg);DispatchMessage(&msg);}
    return (int)msg.wParam;
}
