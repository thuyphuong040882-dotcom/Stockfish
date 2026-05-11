#include <windows.h>
#include <windowsx.h>
#include <string>
#include <vector>
#include <sstream>
#include <cstring>
#include <cctype>
#include <climits>
#include <algorithm>

#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "user32.lib")

// ===================== CONSTANTS =====================
static const int SQ    = 80;
static const int OX    = 20;
static const int OY    = 20;
static const int SP    = 190;
static const int WIN_W = OX + 8*SQ + SP + 10;
static const int WIN_H = OY + 8*SQ + 50;

#define WM_AI_DONE  (WM_APP+1)
#define ANIM_TIMER  1
#define ANIM_MS     16
#define ANIM_DUR    260

// Chess.com palette
static const COLORREF C_LIGHT  = RGB(238,238,210);
static const COLORREF C_DARK   = RGB(118,150, 86);
static const COLORREF C_SEL    = RGB(246,246,105);
static const COLORREF C_LASTM  = RGB(207,210,107);
static const COLORREF C_CHECK  = RGB(235, 97, 80);
static const COLORREF C_BG     = RGB( 32, 36, 44);
static const COLORREF C_PANEL  = RGB( 38, 43, 52);
static const COLORREF C_TEXT   = RGB(200,200,200);

// ===================== TYPES =====================
struct Move { int fr,fc,tr,tc; char promo; bool ep,castle; };

struct BS {
    char board[8][8];
    bool wKM,bKM,wARM,wHRM,bARM,bHRM;
    int  epR,epC;
};

struct Anim {
    bool  active;
    char  piece;
    float cx,cy,tx,ty;
    int   elapsed;
    Move  mv;
};

// ===================== GLOBALS =====================
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
    Anim  anim;
    std::vector<std::string> hist;
} G;

static HWND  hWnd;
static HFONT hPF, hSF, hBF;

// ===================== HELPERS =====================
inline bool isW(char p)        { return p>='A'&&p<='Z'; }
inline bool isB(char p)        { return p>='a'&&p<='z'; }
inline bool inBnd(int r,int c) { return r>=0&&r<8&&c>=0&&c<8; }
inline bool isEnemy(char p,bool w){ return w?isB(p):isW(p); }
inline bool isFriend(char p,bool w){ return w?isW(p):isB(p); }

// ===================== CHESS LOGIC =====================
static bool attacked(const char b[8][8], int r, int c, bool byW) {
    char K=byW?'K':'k', Q=byW?'Q':'q', R=byW?'R':'r',
         B2=byW?'B':'b', N=byW?'N':'n', P=byW?'P':'p';
    static const int kd[8][2]={{-2,-1},{-2,1},{-1,-2},{-1,2},{1,-2},{1,2},{2,-1},{2,1}};
    for (auto& d:kd){int nr=r+d[0],nc=c+d[1];if(inBnd(nr,nc)&&b[nr][nc]==N)return true;}
    if (byW){if(inBnd(r+1,c-1)&&b[r+1][c-1]==P)return true;if(inBnd(r+1,c+1)&&b[r+1][c+1]==P)return true;}
    else    {if(inBnd(r-1,c-1)&&b[r-1][c-1]==P)return true;if(inBnd(r-1,c+1)&&b[r-1][c+1]==P)return true;}
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
    if(m.ep)b[isW(p)?m.tr+1:m.tr-1][m.tc]='.';
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
        mv.push_back({fr,fc,tr,tc,pr,ep,cas});
    };
    if(u=='P'){
        int dir=w?-1:1,sR=w?6:1,pR=w?0:7;
        if(inBnd(fr+dir,fc)&&b[fr+dir][fc]=='.'){
            if(fr+dir==pR)add(fr+dir,fc,'q');
            else{add(fr+dir,fc);if(fr==sR&&b[fr+2*dir][fc]=='.')add(fr+2*dir,fc);}
        }
        for(int dc:{-1,1}){
            int t2=fr+dir,t3=fc+dc; if(!inBnd(t2,t3))continue;
            if(isEnemy(b[t2][t3],w)){if(t2==pR)add(t2,t3,'q');else add(t2,t3);}
            else if(t2==epR&&t3==epC)add(t2,t3,0,true);
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
            bool hrm=w?bs.wHRM:bs.bHRM;
            if(!hrm&&bs.board[kRow][5]=='.'&&bs.board[kRow][6]=='.'&&!attacked(bs.board,kRow,5,!w)&&!attacked(bs.board,kRow,6,!w))
                legal.push_back({fr,fc,kRow,6,0,false,true});
            bool arm=w?bs.wARM:bs.bARM;
            if(!arm&&bs.board[kRow][3]=='.'&&bs.board[kRow][2]=='.'&&bs.board[kRow][1]=='.'&&!attacked(bs.board,kRow,3,!w)&&!attacked(bs.board,kRow,2,!w))
                legal.push_back({fr,fc,kRow,2,0,false,true});
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

static std::vector<Move> getLegal(int fr, int fc) { return legalForBS(toBS(),fr,fc); }

static bool anyLegal(const BS& bs, bool w) {
    for(int r=0;r<8;r++)for(int c=0;c<8;c++)
        if(w?isW(bs.board[r][c]):isB(bs.board[r][c]))
            if(!legalForBS(bs,r,c).empty()) return true;
    return false;
}

static std::string toUCI(const Move& m) {
    std::string s;
    s+=(char)('a'+m.fc);s+=(char)('0'+(8-m.fr));
    s+=(char)('a'+m.tc);s+=(char)('0'+(8-m.tr));
    if(m.promo)s+=m.promo; return s;
}

static BS applyToBS(const BS& bs, const Move& m) {
    BS nx=bs;
    char p=nx.board[m.fr][m.fc];
    if(p=='K')nx.wKM=true; if(p=='k')nx.bKM=true;
    if(m.fr==7&&m.fc==0)nx.wARM=true; if(m.fr==7&&m.fc==7)nx.wHRM=true;
    if(m.fr==0&&m.fc==0)nx.bARM=true; if(m.fr==0&&m.fc==7)nx.bHRM=true;
    int er,ec; doMove(nx.board,m,er,ec); nx.epR=er; nx.epC=ec;
    return nx;
}

static void applyGlobal(const Move& m) {
    char p=G.board[m.fr][m.fc];
    if(p=='K')G.wKM=true; if(p=='k')G.bKM=true;
    if(m.fr==7&&m.fc==0)G.wARM=true; if(m.fr==7&&m.fc==7)G.wHRM=true;
    if(m.fr==0&&m.fc==0)G.bARM=true; if(m.fr==0&&m.fc==7)G.bHRM=true;
    G.hist.push_back(toUCI(m));
    doMove(G.board,m,G.epR,G.epC);
    G.lastFR=m.fr;G.lastFC=m.fc;G.lastTR=m.tr;G.lastTC=m.tc;
}

// ===================== AI — MINIMAX + ALPHA-BETA =====================
static const int PST_P[8][8]={ {0,0,0,0,0,0,0,0},{50,50,50,50,50,50,50,50},{10,10,20,30,30,20,10,10},{5,5,10,25,25,10,5,5},{0,0,0,20,20,0,0,0},{5,-5,-10,0,0,-10,-5,5},{5,10,10,-20,-20,10,10,5},{0,0,0,0,0,0,0,0} };
static const int PST_N[8][8]={ {-50,-40,-30,-30,-30,-30,-40,-50},{-40,-20,0,0,0,0,-20,-40},{-30,0,10,15,15,10,0,-30},{-30,5,15,20,20,15,5,-30},{-30,0,15,20,20,15,0,-30},{-30,5,10,15,15,10,5,-30},{-40,-20,0,5,5,0,-20,-40},{-50,-40,-30,-30,-30,-30,-40,-50} };
static const int PST_B[8][8]={ {-20,-10,-10,-10,-10,-10,-10,-20},{-10,0,0,0,0,0,0,-10},{-10,0,5,10,10,5,0,-10},{-10,5,5,10,10,5,5,-10},{-10,0,10,10,10,10,0,-10},{-10,10,10,10,10,10,10,-10},{-10,5,0,0,0,0,5,-10},{-20,-10,-10,-10,-10,-10,-10,-20} };
static const int PST_R[8][8]={ {0,0,0,0,0,0,0,0},{5,10,10,10,10,10,10,5},{-5,0,0,0,0,0,0,-5},{-5,0,0,0,0,0,0,-5},{-5,0,0,0,0,0,0,-5},{-5,0,0,0,0,0,0,-5},{-5,0,0,0,0,0,0,-5},{0,0,0,5,5,0,0,0} };
static const int PST_K[8][8]={ {-30,-40,-40,-50,-50,-40,-40,-30},{-30,-40,-40,-50,-50,-40,-40,-30},{-30,-40,-40,-50,-50,-40,-40,-30},{-30,-40,-40,-50,-50,-40,-40,-30},{-20,-30,-30,-40,-40,-30,-30,-20},{-10,-20,-20,-20,-20,-20,-20,-10},{20,20,0,0,0,0,20,20},{20,30,10,0,0,10,30,20} };

static int pval(char p){switch((char)toupper(p)){case 'P':return 100;case 'N':return 320;case 'B':return 330;case 'R':return 500;case 'Q':return 900;case 'K':return 20000;}return 0;}
static int pst(char p,int r,int c){int tr=isW(p)?r:(7-r);switch((char)toupper(p)){case 'P':return PST_P[tr][c];case 'N':return PST_N[tr][c];case 'B':return PST_B[tr][c];case 'R':return PST_R[tr][c];case 'K':return PST_K[tr][c];}return 0;}

static int eval(const BS& bs){
    int s=0;
    for(int r=0;r<8;r++)for(int c=0;c<8;c++){char p=bs.board[r][c];if(p=='.')continue;int v=pval(p)+pst(p,r,c);if(isW(p))s+=v;else s-=v;}
    return s;
}

static int minimax(const BS& bs, int depth, int alpha, int beta, bool white) {
    if(depth==0) return eval(bs);
    std::vector<Move> all;
    for(int r=0;r<8;r++)for(int c=0;c<8;c++)
        if(white?isW(bs.board[r][c]):isB(bs.board[r][c])){auto v=legalForBS(bs,r,c);all.insert(all.end(),v.begin(),v.end());}
    if(all.empty()){int kr,kc;findKing(bs.board,white,kr,kc);if(attacked(bs.board,kr,kc,!white))return white?-19000+depth:19000-depth;return 0;}
    if(white){int best=INT_MIN;for(auto&m:all){int s=minimax(applyToBS(bs,m),depth-1,alpha,beta,false);best=std::max(best,s);alpha=std::max(alpha,s);if(beta<=alpha)break;}return best;}
    else     {int best=INT_MAX;for(auto&m:all){int s=minimax(applyToBS(bs,m),depth-1,alpha,beta,true);best=std::min(best,s);beta=std::min(beta,s);if(beta<=alpha)break;}return best;}
}

static Move findBest(const BS& bs, bool aiWhite, int depth) {
    std::vector<Move> all;
    for(int r=0;r<8;r++)for(int c=0;c<8;c++)
        if(aiWhite?isW(bs.board[r][c]):isB(bs.board[r][c])){auto v=legalForBS(bs,r,c);all.insert(all.end(),v.begin(),v.end());}
    if(all.empty()) return {-1,-1,-1,-1,0,false,false};
    Move best=all[0]; int bestVal=aiWhite?INT_MIN:INT_MAX;
    for(auto&m:all){
        int s=minimax(applyToBS(bs,m),depth-1,INT_MIN,INT_MAX,!aiWhite);
        if(aiWhite&&s>bestVal){bestVal=s;best=m;}
        if(!aiWhite&&s<bestVal){bestVal=s;best=m;}
    }
    return best;
}

struct AIParam { BS bs; bool aiWhite; int depth; };

static DWORD WINAPI aiWorker(LPVOID p) {
    AIParam* ap=(AIParam*)p;
    Move best=findBest(ap->bs,ap->aiWhite,ap->depth);
    Move* m=new Move(best);
    PostMessage(hWnd,WM_AI_DONE,0,(LPARAM)m);
    delete ap; return 0;
}

static void startAI() {
    if(G.aiBusy||G.gameOver) return;
    G.aiBusy=true; G.status="AI dang suy nghi...";
    InvalidateRect(hWnd,NULL,FALSE);
    AIParam* p=new AIParam{toBS(),!G.playerWhite,G.aiDepth};
    HANDLE h=CreateThread(NULL,0,aiWorker,p,0,NULL); CloseHandle(h);
}

// ===================== SOUND (async) =====================
struct BP{int f,d;};
static DWORD WINAPI bfn(LPVOID p){BP*b=(BP*)p;Beep(b->f,b->d);delete b;return 0;}
static void bplay(int f,int d){BP*b=new BP{f,d};HANDLE h=CreateThread(NULL,0,bfn,b,0,NULL);CloseHandle(h);}
static void sndMove()    {bplay(440,40);}
static void sndCapture() {bplay(300,80);}
static void sndCheck()   {bplay(880,80);}
static void sndEnd()     {bplay(440,180);}

// ===================== ANIMATION =====================
static void startAnim(const Move& m, char piece) {
    G.anim.active=true; G.anim.piece=piece;
    G.anim.cx=(float)(OX+m.fc*SQ+SQ/2); G.anim.cy=(float)(OY+m.fr*SQ+SQ/2);
    G.anim.tx=(float)(OX+m.tc*SQ+SQ/2); G.anim.ty=(float)(OY+m.tr*SQ+SQ/2);
    G.anim.elapsed=0; G.anim.mv=m;
    SetTimer(hWnd,ANIM_TIMER,ANIM_MS,NULL);
}

// ===================== RENDERING =====================
static const wchar_t* glyph(char p){
    switch(p){case 'K':return L"♔";case 'Q':return L"♕";case 'R':return L"♖";case 'B':return L"♗";case 'N':return L"♘";case 'P':return L"♙";
               case 'k':return L"♚";case 'q':return L"♛";case 'r':return L"♜";case 'b':return L"♝";case 'n':return L"♞";case 'p':return L"♟";}
    return L"";
}

static void drawPiece(HDC hdc, char p, int px, int py) {
    const wchar_t* g=glyph(p); if(!g[0]) return;
    RECT sq={px-SQ/2,py-SQ/2,px+SQ/2,py+SQ/2};
    HFONT old=SelectFont(hdc,hPF);
    SetBkMode(hdc,TRANSPARENT);
    if(isW(p)){
        SetTextColor(hdc,RGB(60,60,60));
        RECT sh=sq;sh.left+=3;sh.top+=3;
        DrawTextW(hdc,g,-1,&sh,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
        SetTextColor(hdc,RGB(255,255,255));
    } else {
        SetTextColor(hdc,RGB(180,180,180));
        RECT sh=sq;sh.left+=2;sh.top+=2;
        DrawTextW(hdc,g,-1,&sh,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
        SetTextColor(hdc,RGB(20,20,20));
    }
    DrawTextW(hdc,g,-1,&sq,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
    SelectFont(hdc,old);
}

static void render(HDC hdc) {
    int ckR=-1,ckC=-1;
    if(G.inCheck){bool cw=G.playerTurn?G.playerWhite:!G.playerWhite;findKing(G.board,cw,ckR,ckC);}

    // Squares
    for(int r=0;r<8;r++) for(int c=0;c<8;c++) {
        bool lt=(r+c)%2==0;
        COLORREF col=lt?C_LIGHT:C_DARK;
        if((r==G.lastFR&&c==G.lastFC)||(r==G.lastTR&&c==G.lastTC)) col=C_LASTM;
        if(r==G.selR&&c==G.selC) col=C_SEL;
        if(r==ckR&&c==ckC) col=C_CHECK;
        RECT sq={OX+c*SQ,OY+r*SQ,OX+c*SQ+SQ,OY+r*SQ+SQ};
        HBRUSH br=CreateSolidBrush(col);FillRect(hdc,&sq,br);DeleteObject(br);
        // Legal move dots
        for(auto& m:G.legal){
            if(m.tr!=r||m.tc!=c) continue;
            int cx=OX+c*SQ+SQ/2,cy=OY+r*SQ+SQ/2;
            if(G.board[r][c]!='.'){
                HPEN pen=CreatePen(PS_SOLID,6,lt?RGB(90,110,55):RGB(80,100,45));
                HGDIOBJ op=SelectObject(hdc,pen);SelectObject(hdc,GetStockObject(NULL_BRUSH));
                Ellipse(hdc,OX+c*SQ+5,OY+r*SQ+5,OX+c*SQ+SQ-5,OY+r*SQ+SQ-5);
                SelectObject(hdc,op);DeleteObject(pen);
            } else {
                COLORREF dc=lt?RGB(140,155,95):RGB(95,120,60);
                HPEN pen=CreatePen(PS_SOLID,1,dc);HBRUSH db=CreateSolidBrush(dc);
                HGDIOBJ op=SelectObject(hdc,pen),ob=SelectObject(hdc,db);
                Ellipse(hdc,cx-13,cy-13,cx+13,cy+13);
                SelectObject(hdc,op);SelectObject(hdc,ob);DeleteObject(pen);DeleteObject(db);
            }
        }
    }

    // Rank/file labels inside squares (Chess.com style)
    HFONT olds=SelectFont(hdc,hSF);
    SetBkMode(hdc,TRANSPARENT);
    for(int i=0;i<8;i++){
        bool evenRank=(i%2==0), evenFile=((7-i)%2==0);
        SetTextColor(hdc,evenRank?C_DARK:C_LIGHT);
        RECT rr={OX+3,OY+i*SQ+3,OX+18,OY+i*SQ+19};
        wchar_t buf[4]; wsprintf(buf,L"%d",8-i);
        DrawTextW(hdc,buf,-1,&rr,DT_LEFT|DT_TOP);
        SetTextColor(hdc,evenFile?C_DARK:C_LIGHT);
        RECT fr2={OX+i*SQ+SQ-17,OY+8*SQ-18,OX+i*SQ+SQ-2,OY+8*SQ-3};
        wchar_t fc[4]={(wchar_t)('a'+i),0};
        DrawTextW(hdc,fc,-1,&fr2,DT_RIGHT|DT_BOTTOM);
    }
    SelectFont(hdc,olds);

    // Pieces (skip anim destination — drawn separately)
    for(int r=0;r<8;r++) for(int c=0;c<8;c++){
        char p=G.board[r][c]; if(p=='.') continue;
        if(G.anim.active&&r==G.anim.mv.tr&&c==G.anim.mv.tc) continue;
        drawPiece(hdc,p,OX+c*SQ+SQ/2,OY+r*SQ+SQ/2);
    }
    if(G.anim.active) drawPiece(hdc,G.anim.piece,(int)G.anim.cx,(int)G.anim.cy);

    // ---- SIDE PANEL ----
    int px=OX+8*SQ+8;
    RECT panel={px-2,0,WIN_W,WIN_H};
    HBRUSH pb=CreateSolidBrush(C_PANEL);FillRect(hdc,&panel,pb);DeleteObject(pb);

    // Divider line
    HPEN dp=CreatePen(PS_SOLID,1,RGB(60,65,75));
    HGDIOBJ op=SelectObject(hdc,dp);
    MoveToEx(hdc,px-2,0,NULL);LineTo(hdc,px-2,WIN_H);
    SelectObject(hdc,op);DeleteObject(dp);

    // Player labels
    HFONT oldbf=SelectFont(hdc,hBF);
    SetBkMode(hdc,TRANSPARENT);
    SetTextColor(hdc,C_TEXT);
    RECT topLbl={px+6,8,WIN_W-4,30};
    std::string aiStr=G.playerWhite?"♟ Black (AI)":"♙ White (AI)";
    std::wstring aiW(aiStr.begin(),aiStr.end());
    DrawTextW(hdc,aiW.c_str(),-1,&topLbl,DT_LEFT|DT_VCENTER|DT_SINGLELINE);
    RECT botLbl={px+6,WIN_H-30,WIN_W-4,WIN_H-8};
    std::string plStr=G.playerWhite?"♙ White (You)":"♟ Black (You)";
    std::wstring plW(plStr.begin(),plStr.end());
    DrawTextW(hdc,plW.c_str(),-1,&botLbl,DT_LEFT|DT_VCENTER|DT_SINGLELINE);
    SelectFont(hdc,oldbf);

    // Divider lines
    HPEN lp=CreatePen(PS_SOLID,1,RGB(55,60,70));
    HGDIOBJ lop=SelectObject(hdc,lp);
    MoveToEx(hdc,px,33,NULL);LineTo(hdc,WIN_W,33);
    MoveToEx(hdc,px,WIN_H-33,NULL);LineTo(hdc,WIN_W,WIN_H-33);
    SelectObject(hdc,lop);DeleteObject(lp);

    // Move history
    HFONT oldmf=SelectFont(hdc,hSF);
    int hy=40;
    int start=(int)G.hist.size()>28?(int)G.hist.size()-28:0;
    for(int i=start;i<(int)G.hist.size();i+=2){
        int num=i/2+1;
        std::string w2=G.hist[i], b2=(i+1<(int)G.hist.size())?G.hist[i+1]:"";
        wchar_t line[48]; wsprintfW(line,L"%2d.  %-7hs%hs",num,w2.c_str(),b2.c_str());
        bool isLast=(i+1>=(int)G.hist.size()-1);
        SetTextColor(hdc,isLast?RGB(230,230,180):RGB(160,165,170));
        SetBkMode(hdc,TRANSPARENT);
        RECT lr={px+6,hy,WIN_W-4,hy+18};
        DrawTextW(hdc,line,-1,&lr,DT_LEFT|DT_VCENTER|DT_SINGLELINE);
        hy+=18; if(hy>WIN_H-38) break;
    }
    SelectFont(hdc,oldmf);

    // Status bar
    RECT sr={0,OY+8*SQ+2,OX+8*SQ,WIN_H};
    HBRUSH sb=CreateSolidBrush(C_BG);FillRect(hdc,&sr,sb);DeleteObject(sb);
    HFONT oldsf2=SelectFont(hdc,hBF);
    SetBkMode(hdc,TRANSPARENT);SetTextColor(hdc,RGB(220,220,100));
    std::wstring ws(G.status.begin(),G.status.end());
    DrawTextW(hdc,ws.c_str(),-1,&sr,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
    SelectFont(hdc,oldsf2);
}

// ===================== WINDOW PROC =====================
static LRESULT CALLBACK WndProc(HWND hw, UINT msg, WPARAM wp, LPARAM lp) {
    switch(msg) {
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC hdc=BeginPaint(hw,&ps);
        RECT rc; GetClientRect(hw,&rc);
        HDC mem=CreateCompatibleDC(hdc);
        HBITMAP bmp=CreateCompatibleBitmap(hdc,rc.right,rc.bottom);
        HGDIOBJ old=SelectObject(mem,bmp);
        HBRUSH bg=CreateSolidBrush(C_BG);FillRect(mem,&rc,bg);DeleteObject(bg);
        render(mem);
        BitBlt(hdc,0,0,rc.right,rc.bottom,mem,0,0,SRCCOPY);
        SelectObject(mem,old);DeleteObject(bmp);DeleteDC(mem);
        EndPaint(hw,&ps); return 0;
    }
    case WM_TIMER: {
        if(wp!=ANIM_TIMER||!G.anim.active) break;
        G.anim.elapsed+=ANIM_MS;
        float t=(float)G.anim.elapsed/ANIM_DUR;
        if(t>1.0f)t=1.0f;
        // Ease-out cubic
        float e=1.0f-(1.0f-t)*(1.0f-t)*(1.0f-t);
        float sx=(float)(OX+G.anim.mv.fc*SQ+SQ/2), sy=(float)(OY+G.anim.mv.fr*SQ+SQ/2);
        G.anim.cx=sx+(G.anim.tx-sx)*e;
        G.anim.cy=sy+(G.anim.ty-sy)*e;
        if(t>=1.0f){
            KillTimer(hw,ANIM_TIMER);
            G.anim.active=false;
            // After player's animation, start AI
            if(!G.playerTurn&&!G.gameOver&&!G.aiBusy) startAI();
        }
        InvalidateRect(hw,NULL,FALSE); break;
    }
    case WM_LBUTTONDOWN: {
        if(G.gameOver||G.aiBusy||G.anim.active||!G.playerTurn) break;
        int mx=GET_X_LPARAM(lp), my=GET_Y_LPARAM(lp);
        int col=(mx-OX)/SQ, row=(my-OY)/SQ;
        if(col<0||col>7||row<0||row>7){G.selR=G.selC=-1;G.legal.clear();InvalidateRect(hw,NULL,FALSE);break;}

        // Try to apply a legal move
        if(G.selR>=0) {
            for(auto& m:G.legal) {
                if(m.tr!=row||m.tc!=col) continue;
                bool cap=G.board[m.tr][m.tc]!='.';
                applyGlobal(m);
                char animPiece=G.board[m.tr][m.tc];
                startAnim(m,animPiece);
                G.selR=G.selC=-1; G.legal.clear();
                if(cap)sndCapture();else sndMove();
                BS bs=toBS();
                bool oppW=!G.playerWhite;
                int kr,kc; findKing(G.board,oppW,kr,kc);
                G.inCheck=(kr>=0&&attacked(G.board,kr,kc,G.playerWhite));
                if(!anyLegal(bs,oppW)){
                    G.gameOver=true;
                    G.status=G.inCheck?"CHIEU TUONG! Ban da thang!":"HOA CO (Pat)!";
                    sndEnd();
                } else {
                    G.playerTurn=false;
                    G.status=G.inCheck?"AI bi chieu! Dang suy nghi...":"AI dang suy nghi...";
                    if(G.inCheck)sndCheck();
                    // AI starts in WM_TIMER after animation
                }
                InvalidateRect(hw,NULL,FALSE); return 0;
            }
        }
        // Select piece
        G.selR=G.selC=-1; G.legal.clear();
        char p=G.board[row][col];
        if(G.playerWhite?isW(p):isB(p)){G.selR=row;G.selC=col;G.legal=getLegal(row,col);}
        InvalidateRect(hw,NULL,FALSE); break;
    }
    case WM_AI_DONE: {
        Move* m=(Move*)lp; G.aiBusy=false;
        if(!m||m->fr<0){
            G.gameOver=true; G.status="AI het nuoc. Ban da thang!"; sndEnd();
        } else {
            bool cap=G.board[m->tr][m->tc]!='.';
            applyGlobal(*m);
            char animPiece=G.board[m->tr][m->tc];
            startAnim(*m,animPiece);
            if(cap)sndCapture();else sndMove();
            BS bs=toBS();
            int kr,kc; findKing(G.board,G.playerWhite,kr,kc);
            G.inCheck=(kr>=0&&attacked(G.board,kr,kc,!G.playerWhite));
            if(!anyLegal(bs,G.playerWhite)){
                G.gameOver=true;
                G.status=G.inCheck?"CHIEU TUONG! AI da thang!":"HOA CO (Pat)!";
                sndEnd();
            } else {
                G.playerTurn=true;
                G.status=G.inCheck?"Ban bi chieu! Den luot cua ban.":"Den luot cua ban.";
                if(G.inCheck)sndCheck();
            }
        }
        delete m; InvalidateRect(hw,NULL,FALSE); break;
    }
    case WM_DESTROY:
        KillTimer(hw,ANIM_TIMER);
        DeleteObject(hPF);DeleteObject(hSF);DeleteObject(hBF);
        PostQuitMessage(0); return 0;
    }
    return DefWindowProc(hw,msg,wp,lp);
}

// ===================== INIT =====================
static void initGame() {
    const char* back="rnbqkbnr";
    for(int c=0;c<8;c++){
        G.board[0][c]=back[c];G.board[1][c]='p';
        for(int r=2;r<6;r++)G.board[r][c]='.';
        G.board[6][c]='P';G.board[7][c]=(char)toupper(back[c]);
    }
    G.wKM=G.bKM=G.wARM=G.wHRM=G.bARM=G.bHRM=false;
    G.epR=G.epC=-1; G.selR=G.selC=-1; G.legal.clear();
    G.lastFR=G.lastFC=G.lastTR=G.lastTC=-1;
    G.inCheck=G.gameOver=G.aiBusy=G.anim.active=false;
    G.hist.clear();
}

// ===================== WINMAIN =====================
int WINAPI WinMain(HINSTANCE hInst, HINSTANCE, LPSTR, int nShow) {
    // Difficulty selection
    int r1=MessageBoxA(NULL,"Do kho:\n\nYes = De / Trung binh\nNo  = Kho / Chuyen gia","Thiet lap",MB_YESNO|MB_ICONQUESTION);
    if(r1==IDYES){
        int r2=MessageBoxA(NULL,"Yes = De (depth 2)\nNo  = Trung binh (depth 3)","Do kho",MB_YESNO);
        G.aiDepth=(r2==IDYES)?2:3;
    } else {
        int r2=MessageBoxA(NULL,"Yes = Kho (depth 4)\nNo  = Chuyen gia (depth 5)","Do kho",MB_YESNO);
        G.aiDepth=(r2==IDYES)?4:5;
    }
    int rc=MessageBoxA(NULL,"Chon quan:\n\nYes = Trang (di truoc)\nNo  = Den (di sau)","Chon quan",MB_YESNO|MB_ICONQUESTION);
    G.playerWhite=(rc==IDYES);

    initGame();

    WNDCLASSA wc{}; wc.lpfnWndProc=WndProc; wc.hInstance=hInst;
    wc.hbrBackground=(HBRUSH)(COLOR_WINDOW+1); wc.lpszClassName="ChessApp";
    wc.hCursor=LoadCursor(NULL,IDC_ARROW); wc.hIcon=LoadIcon(NULL,IDI_APPLICATION);
    RegisterClassA(&wc);

    hWnd=CreateWindowA("ChessApp","Co Vua (Chess.com Style)",
        WS_OVERLAPPED|WS_CAPTION|WS_SYSMENU|WS_MINIMIZEBOX,
        CW_USEDEFAULT,CW_USEDEFAULT,WIN_W+16,WIN_H+39,NULL,NULL,hInst,NULL);

    hPF=CreateFontW(56,0,0,0,FW_NORMAL,0,0,0,DEFAULT_CHARSET,OUT_DEFAULT_PRECIS,
        CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,DEFAULT_PITCH,L"Segoe UI Symbol");
    hSF=CreateFontW(14,0,0,0,FW_NORMAL,0,0,0,DEFAULT_CHARSET,OUT_DEFAULT_PRECIS,
        CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,DEFAULT_PITCH,L"Consolas");
    hBF=CreateFontW(16,0,0,0,FW_BOLD,0,0,0,DEFAULT_CHARSET,OUT_DEFAULT_PRECIS,
        CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,DEFAULT_PITCH,L"Segoe UI");

    if(!G.playerWhite){
        G.playerTurn=false; G.status="AI dang di nuoc dau...";
        startAI();
    } else {
        G.playerTurn=true; G.status="Den luot cua ban. Click vao quan de chon.";
    }

    ShowWindow(hWnd,nShow); UpdateWindow(hWnd);
    MSG msg;
    while(GetMessage(&msg,NULL,0,0)){TranslateMessage(&msg);DispatchMessage(&msg);}
    return (int)msg.wParam;
}
