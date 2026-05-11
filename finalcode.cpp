#include <windows.h>
#include <windowsx.h>
#include <string>
#include <vector>
#include <sstream>
#include <cstring>
#include <cctype>

#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "user32.lib")

// ===================== CONSTANTS =====================
static const int SQ    = 80;
static const int OX    = 50;
static const int OY    = 30;
static const int WIN_W = SQ*8 + OX + 20;
static const int WIN_H = SQ*8 + OY + 30 + 60;
#define WM_SF_DONE (WM_APP+1)

static const char* SF_PATH = "C:\\Users\\Huyen\\Downloads\\stockfish\\stockfish\\stockfish.exe";

static const COLORREF C_LIGHT = RGB(240,217,181);
static const COLORREF C_DARK  = RGB(181,136, 99);
static const COLORREF C_SEL   = RGB(247,247,105);
static const COLORREF C_LEGAL = RGB( 80,150, 80);
static const COLORREF C_LAST  = RGB(205,210, 98);
static const COLORREF C_CHECK = RGB(220, 50, 50);
static const COLORREF C_BG    = RGB( 40, 40, 40);

// ===================== TYPES =====================
struct Move { int fr,fc,tr,tc; char promo; bool ep,castle; };

// ===================== STATE =====================
static struct {
    char  board[8][8];
    bool  playerWhite, playerTurn;
    bool  wKM,bKM,wARM,wHRM,bARM,bHRM;
    int   epR,epC;
    std::vector<std::string> uciMoves;
    int   selR,selC;
    std::vector<Move> legal;
    int   lastFR,lastFC,lastTR,lastTC;
    bool  inCheck,gameOver,sfBusy;
    std::string status;
    HANDLE sfIn,sfOut,sfProc,sfThr;
    int   skillLv,movetime;
} G;

static HWND  hWnd;
static HFONT hPF, hSF;

// ===================== HELPERS =====================
inline bool isW(char p)  { return p>='A'&&p<='Z'; }
inline bool isB(char p)  { return p>='a'&&p<='z'; }
inline bool inBnd(int r,int c) { return r>=0&&r<8&&c>=0&&c<8; }
inline bool isEnemy(char p,bool w) { return w?isB(p):isW(p); }
inline bool isFriend(char p,bool w){ return w?isW(p):isB(p); }

// ===================== CHESS LOGIC =====================
static bool attacked(char b[8][8], int r, int c, bool byW) {
    char K=byW?'K':'k', Q=byW?'Q':'q', R=byW?'R':'r',
         B2=byW?'B':'b', N=byW?'N':'n', P=byW?'P':'p';

    static const int kd[8][2]={{-2,-1},{-2,1},{-1,-2},{-1,2},{1,-2},{1,2},{2,-1},{2,1}};
    for (auto& d:kd) { int nr=r+d[0],nc=c+d[1]; if(inBnd(nr,nc)&&b[nr][nc]==N) return true; }

    if (byW) { if(inBnd(r+1,c-1)&&b[r+1][c-1]==P) return true; if(inBnd(r+1,c+1)&&b[r+1][c+1]==P) return true; }
    else     { if(inBnd(r-1,c-1)&&b[r-1][c-1]==P) return true; if(inBnd(r-1,c+1)&&b[r-1][c+1]==P) return true; }

    static const int sd[4][2]={{0,1},{0,-1},{1,0},{-1,0}};
    for (auto& d:sd) for (int i=1;i<8;i++) { int nr=r+d[0]*i,nc=c+d[1]*i; if(!inBnd(nr,nc)) break; if(b[nr][nc]!='.'){if(b[nr][nc]==R||b[nr][nc]==Q)return true;break;} }

    static const int dd[4][2]={{1,1},{1,-1},{-1,1},{-1,-1}};
    for (auto& d:dd) for (int i=1;i<8;i++) { int nr=r+d[0]*i,nc=c+d[1]*i; if(!inBnd(nr,nc)) break; if(b[nr][nc]!='.'){if(b[nr][nc]==B2||b[nr][nc]==Q)return true;break;} }

    for (int dr=-1;dr<=1;dr++) for (int dc=-1;dc<=1;dc++)
        if ((dr||dc)&&inBnd(r+dr,c+dc)&&b[r+dr][c+dc]==K) return true;
    return false;
}

static void findKing(char b[8][8], bool w, int& kr, int& kc) {
    char K=w?'K':'k';
    for (int r=0;r<8;r++) for (int c=0;c<8;c++) if (b[r][c]==K) { kr=r; kc=c; return; }
    kr=kc=-1;
}

static void doMove(char b[8][8], const Move& m, int& epR, int& epC) {
    epR=epC=-1;
    char p=b[m.fr][m.fc];
    b[m.fr][m.fc]='.';
    b[m.tr][m.tc]=m.promo?(isW(p)?(char)toupper(m.promo):m.promo):p;
    if (m.ep) b[isW(p)?m.tr+1:m.tr-1][m.tc]='.';
    if (m.castle) {
        if (m.tc==6) { b[m.tr][5]=b[m.tr][7]; b[m.tr][7]='.'; }
        else         { b[m.tr][3]=b[m.tr][0]; b[m.tr][0]='.'; }
    }
    if ((char)toupper(p)=='P'&&abs(m.tr-m.fr)==2) { epR=(m.fr+m.tr)/2; epC=m.fc; }
}

static std::vector<Move> pseudo(char b[8][8], int fr, int fc, int epR, int epC) {
    std::vector<Move> mv;
    char p=b[fr][fc]; if (p=='.') return mv;
    bool w=isW(p); char u=(char)toupper(p);

    auto add=[&](int tr,int tc,char pr=0,bool ep=false,bool cas=false){
        if (!inBnd(tr,tc)) return;
        if (!ep&&!cas&&isFriend(b[tr][tc],w)) return;
        mv.push_back({fr,fc,tr,tc,pr,ep,cas});
    };

    if (u=='P') {
        int dir=w?-1:1, sR=w?6:1, pR=w?0:7;
        if (inBnd(fr+dir,fc)&&b[fr+dir][fc]=='.') {
            if (fr+dir==pR) add(fr+dir,fc,'q');
            else { add(fr+dir,fc); if (fr==sR&&b[fr+2*dir][fc]=='.') add(fr+2*dir,fc); }
        }
        for (int dc:{-1,1}) {
            int tr2=fr+dir, tc2=fc+dc; if (!inBnd(tr2,tc2)) continue;
            if (isEnemy(b[tr2][tc2],w)) { if(tr2==pR) add(tr2,tc2,'q'); else add(tr2,tc2); }
            else if (tr2==epR&&tc2==epC) add(tr2,tc2,0,true);
        }
    }
    if (u=='N') { static const int kd[8][2]={{-2,-1},{-2,1},{-1,-2},{-1,2},{1,-2},{1,2},{2,-1},{2,1}}; for (auto& d:kd) add(fr+d[0],fc+d[1]); }
    auto slide=[&](int dr,int dc){ for(int i=1;i<8;i++){int r=fr+dr*i,c=fc+dc*i;if(!inBnd(r,c))break;add(r,c);if(b[r][c]!='.')break;} };
    if (u=='B'||u=='Q') { slide(1,1);slide(1,-1);slide(-1,1);slide(-1,-1); }
    if (u=='R'||u=='Q') { slide(0,1);slide(0,-1);slide(1,0);slide(-1,0); }
    if (u=='K') { for(int dr=-1;dr<=1;dr++) for(int dc=-1;dc<=1;dc++) if(dr||dc) add(fr+dr,fc+dc); }
    return mv;
}

static std::vector<Move> getLegal(int fr, int fc) {
    std::vector<Move> legal;
    char p=G.board[fr][fc]; if (p=='.') return legal;
    bool w=isW(p);
    for (auto& m:pseudo(G.board,fr,fc,G.epR,G.epC)) {
        char b2[8][8]; memcpy(b2,G.board,64);
        int er,ec; doMove(b2,m,er,ec);
        int kr,kc; findKing(b2,w,kr,kc);
        if (kr>=0&&!attacked(b2,kr,kc,!w)) legal.push_back(m);
    }
    // Castling
    if ((char)toupper(p)=='K') {
        int kRow=w?7:0;
        bool km=w?G.wKM:G.bKM;
        if (!km&&fr==kRow&&fc==4&&!attacked(G.board,kRow,4,!w)) {
            bool hrm=w?G.wHRM:G.bHRM;
            if (!hrm&&G.board[kRow][5]=='.'&&G.board[kRow][6]=='.'
                &&!attacked(G.board,kRow,5,!w)&&!attacked(G.board,kRow,6,!w))
                legal.push_back({fr,fc,kRow,6,0,false,true});
            bool arm=w?G.wARM:G.bARM;
            if (!arm&&G.board[kRow][3]=='.'&&G.board[kRow][2]=='.'&&G.board[kRow][1]=='.'
                &&!attacked(G.board,kRow,3,!w)&&!attacked(G.board,kRow,2,!w))
                legal.push_back({fr,fc,kRow,2,0,false,true});
        }
    }
    return legal;
}

static bool anyLegal(bool w) {
    for (int r=0;r<8;r++) for (int c=0;c<8;c++)
        if (w?isW(G.board[r][c]):isB(G.board[r][c]))
            if (!getLegal(r,c).empty()) return true;
    return false;
}

static std::string toUCI(const Move& m) {
    std::string s;
    s+=(char)('a'+m.fc); s+=(char)('0'+(8-m.fr));
    s+=(char)('a'+m.tc); s+=(char)('0'+(8-m.tr));
    if (m.promo) s+=m.promo;
    return s;
}

static void applyMove(const Move& m) {
    char p=G.board[m.fr][m.fc];
    if (p=='K') G.wKM=true; if (p=='k') G.bKM=true;
    if (m.fr==7&&m.fc==0) G.wARM=true; if (m.fr==7&&m.fc==7) G.wHRM=true;
    if (m.fr==0&&m.fc==0) G.bARM=true; if (m.fr==0&&m.fc==7) G.bHRM=true;
    doMove(G.board,m,G.epR,G.epC);
    G.lastFR=m.fr; G.lastFC=m.fc; G.lastTR=m.tr; G.lastTC=m.tc;
    G.uciMoves.push_back(toUCI(m));
}

static void applyUCI(const std::string& mv) {
    if (mv.size()<4) return;
    int fc=mv[0]-'a', fr=8-(mv[1]-'0'), tc=mv[2]-'a', tr=8-(mv[3]-'0');
    char pr=mv.size()==5?mv[4]:0;
    char p=G.board[fr][fc];
    bool ep=((char)toupper(p)=='P'&&fc!=tc&&G.board[tr][tc]=='.');
    bool cas=((char)toupper(p)=='K'&&abs(tc-fc)==2);
    applyMove({fr,fc,tr,tc,pr,ep,cas});
}

// ===================== STOCKFISH =====================
static void sfRead(const char* kw) {
    char buf[512]; DWORD r; std::string out;
    while (ReadFile(G.sfOut,buf,sizeof(buf)-1,&r,NULL)) { buf[r]='\0'; out+=buf; if (out.find(kw)!=std::string::npos) break; }
}

static DWORD WINAPI sfWorker(LPVOID) {
    DWORD w;
    std::string cmd="position startpos moves";
    for (auto& m:G.uciMoves) cmd+=" "+m;
    cmd+="\n";
    WriteFile(G.sfIn,cmd.c_str(),(DWORD)cmd.size(),&w,NULL);
    std::string go="go movetime "+std::to_string(G.movetime)+"\n";
    WriteFile(G.sfIn,go.c_str(),(DWORD)go.size(),&w,NULL);
    char buf[512]; DWORD r; std::string out;
    while (ReadFile(G.sfOut,buf,sizeof(buf)-1,&r,NULL)) {
        buf[r]='\0'; out+=buf;
        size_t p=out.find("bestmove ");
        if (p!=std::string::npos) {
            std::istringstream iss(out.substr(p));
            std::string tmp,best; iss>>tmp>>best;
            char* s=new char[best.size()+1]; strcpy(s,best.c_str());
            PostMessage(hWnd,WM_SF_DONE,0,(LPARAM)s);
            break;
        }
    }
    return 0;
}

static void sfThink() {
    if (G.sfBusy||G.gameOver) return;
    G.sfBusy=true;
    HANDLE h=CreateThread(NULL,0,sfWorker,NULL,0,NULL);
    CloseHandle(h);
}

// ===================== RENDERING =====================
static const wchar_t* glyph(char p) {
    switch(p) {
        case 'K':return L"♔"; case 'Q':return L"♕"; case 'R':return L"♖";
        case 'B':return L"♗"; case 'N':return L"♘"; case 'P':return L"♙";
        case 'k':return L"♚"; case 'q':return L"♛"; case 'r':return L"♜";
        case 'b':return L"♝"; case 'n':return L"♞"; case 'p':return L"♟";
        default: return L"";
    }
}

static void render(HDC hdc) {
    int ckR=-1, ckC=-1;
    if (G.inCheck) {
        bool cw=G.playerTurn?G.playerWhite:!G.playerWhite;
        findKing(G.board,cw,ckR,ckC);
    }

    for (int r=0;r<8;r++) for (int c=0;c<8;c++) {
        bool lt=(r+c)%2==0;
        COLORREF col=lt?C_LIGHT:C_DARK;
        if ((r==G.lastFR&&c==G.lastFC)||(r==G.lastTR&&c==G.lastTC)) col=C_LAST;
        if (r==G.selR&&c==G.selC) col=C_SEL;
        if (r==ckR&&c==ckC) col=C_CHECK;
        RECT sq={OX+c*SQ, OY+r*SQ, OX+c*SQ+SQ, OY+r*SQ+SQ};
        HBRUSH br=CreateSolidBrush(col); FillRect(hdc,&sq,br); DeleteObject(br);

        for (auto& m:G.legal) {
            if (m.tr!=r||m.tc!=c) continue;
            if (G.board[r][c]!='.') {
                HPEN pen=CreatePen(PS_SOLID,5,C_LEGAL); HGDIOBJ op=SelectObject(hdc,pen);
                SelectObject(hdc,GetStockObject(NULL_BRUSH));
                Ellipse(hdc,OX+c*SQ+4,OY+r*SQ+4,OX+c*SQ+SQ-4,OY+r*SQ+SQ-4);
                SelectObject(hdc,op); DeleteObject(pen);
            } else {
                int cx=OX+c*SQ+SQ/2, cy=OY+r*SQ+SQ/2;
                HBRUSH db=CreateSolidBrush(C_LEGAL); HGDIOBJ op=SelectObject(hdc,db);
                HPEN pen=CreatePen(PS_SOLID,1,C_LEGAL); HGDIOBJ op2=SelectObject(hdc,pen);
                Ellipse(hdc,cx-12,cy-12,cx+12,cy+12);
                SelectObject(hdc,op); SelectObject(hdc,op2);
                DeleteObject(db); DeleteObject(pen);
            }
        }
    }

    // Pieces
    HFONT old=SelectFont(hdc,hPF);
    SetBkMode(hdc,TRANSPARENT);
    for (int r=0;r<8;r++) for (int c=0;c<8;c++) {
        char p=G.board[r][c]; if (p=='.') continue;
        RECT sq={OX+c*SQ, OY+r*SQ, OX+c*SQ+SQ, OY+r*SQ+SQ};
        if (isW(p)) {
            SetTextColor(hdc,RGB(0,0,0));
            RECT sh=sq; sh.left+=2; sh.top+=2;
            DrawTextW(hdc,glyph(p),-1,&sh,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
            SetTextColor(hdc,RGB(255,255,255));
        } else {
            SetTextColor(hdc,RGB(20,20,20));
        }
        DrawTextW(hdc,glyph(p),-1,&sq,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
    }
    SelectFont(hdc,old);

    // Labels
    HFONT olds=SelectFont(hdc,hSF);
    SetBkMode(hdc,TRANSPARENT); SetTextColor(hdc,RGB(180,180,180));
    for (int i=0;i<8;i++) {
        wchar_t buf[4];
        RECT rr={5, OY+i*SQ+SQ/2-12, OX-5, OY+i*SQ+SQ/2+12};
        wsprintf(buf,L"%d",8-i); DrawTextW(hdc,buf,-1,&rr,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
        RECT fr2={OX+i*SQ, OY+8*SQ+5, OX+i*SQ+SQ, OY+8*SQ+25};
        wchar_t fc2[4]={(wchar_t)('a'+i),0}; DrawTextW(hdc,fc2,-1,&fr2,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
    }

    // Status bar
    RECT sr={0, OY+8*SQ+28, WIN_W, WIN_H};
    SetBkMode(hdc,OPAQUE); SetBkColor(hdc,C_BG); SetTextColor(hdc,RGB(220,220,100));
    std::wstring ws(G.status.begin(),G.status.end());
    DrawTextW(hdc,ws.c_str(),-1,&sr,DT_CENTER|DT_VCENTER|DT_SINGLELINE);
    SelectFont(hdc,olds);
}

// ===================== WINDOW PROC =====================
static LRESULT CALLBACK WndProc(HWND hw, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC hdc=BeginPaint(hw,&ps);
        RECT rc; GetClientRect(hw,&rc);
        HDC mem=CreateCompatibleDC(hdc);
        HBITMAP bmp=CreateCompatibleBitmap(hdc,rc.right,rc.bottom);
        HGDIOBJ old=SelectObject(mem,bmp);
        HBRUSH bg=CreateSolidBrush(C_BG); FillRect(mem,&rc,bg); DeleteObject(bg);
        render(mem);
        BitBlt(hdc,0,0,rc.right,rc.bottom,mem,0,0,SRCCOPY);
        SelectObject(mem,old); DeleteObject(bmp); DeleteDC(mem);
        EndPaint(hw,&ps); return 0;
    }
    case WM_LBUTTONDOWN: {
        if (G.gameOver||G.sfBusy||!G.playerTurn) break;
        int mx=GET_X_LPARAM(lp), my=GET_Y_LPARAM(lp);
        int col=(mx-OX)/SQ, row=(my-OY)/SQ;
        if (col<0||col>7||row<0||row>7) { G.selR=G.selC=-1; G.legal.clear(); InvalidateRect(hw,NULL,FALSE); break; }

        if (G.selR>=0) {
            for (auto& m:G.legal) {
                if (m.tr==row&&m.tc==col) {
                    applyMove(m);
                    G.selR=G.selC=-1; G.legal.clear();
                    bool oppW=!G.playerWhite;
                    int kr,kc; findKing(G.board,oppW,kr,kc);
                    G.inCheck=(kr>=0&&attacked(G.board,kr,kc,G.playerWhite));
                    if (!anyLegal(oppW)) {
                        G.gameOver=true;
                        G.status=G.inCheck?"CHIEU TUONG! Ban da thang!":"HOA CO (Pat)!";
                    } else {
                        G.playerTurn=false;
                        G.status=G.inCheck?"Stockfish bi chieu! Dang suy nghi...":"Stockfish dang suy nghi...";
                        sfThink();
                    }
                    InvalidateRect(hw,NULL,FALSE); return 0;
                }
            }
        }

        G.selR=G.selC=-1; G.legal.clear();
        char p=G.board[row][col];
        if (G.playerWhite?isW(p):isB(p)) { G.selR=row; G.selC=col; G.legal=getLegal(row,col); }
        InvalidateRect(hw,NULL,FALSE); break;
    }
    case WM_SF_DONE: {
        char* best=(char*)lp;
        G.sfBusy=false;
        std::string mv=best?best:""; delete[] best;
        if (mv.empty()||mv=="(none)") {
            G.gameOver=true; G.status="Stockfish het nuoc di. Ban da thang!";
        } else {
            applyUCI(mv);
            int kr,kc; findKing(G.board,G.playerWhite,kr,kc);
            G.inCheck=(kr>=0&&attacked(G.board,kr,kc,!G.playerWhite));
            if (!anyLegal(G.playerWhite)) {
                G.gameOver=true;
                G.status=G.inCheck?"CHIEU TUONG! Stockfish da thang!":"HOA CO (Pat)!";
            } else {
                G.playerTurn=true;
                G.status=G.inCheck?"Ban bi chieu! Den luot cua ban.":"Den luot cua ban.";
            }
        }
        InvalidateRect(hw,NULL,FALSE); break;
    }
    case WM_DESTROY:
        if (G.sfProc) { DWORD w; WriteFile(G.sfIn,"quit\n",5,&w,NULL); CloseHandle(G.sfIn); CloseHandle(G.sfOut); CloseHandle(G.sfProc); CloseHandle(G.sfThr); }
        DeleteObject(hPF); DeleteObject(hSF);
        PostQuitMessage(0); return 0;
    }
    return DefWindowProc(hw,msg,wp,lp);
}

// ===================== INIT =====================
static bool initSF() {
    SECURITY_ATTRIBUTES sa{sizeof(sa),NULL,TRUE};
    HANDLE ir,iw,or2,ow;
    CreatePipe(&or2,&ow,&sa,0); SetHandleInformation(or2,HANDLE_FLAG_INHERIT,0);
    CreatePipe(&ir,&iw,&sa,0);  SetHandleInformation(iw,HANDLE_FLAG_INHERIT,0);
    STARTUPINFOA si{}; PROCESS_INFORMATION pi{};
    si.cb=sizeof(si); si.dwFlags=STARTF_USESTDHANDLES;
    si.hStdInput=ir; si.hStdOutput=ow; si.hStdError=ow;
    char cmd[256]; strcpy(cmd,SF_PATH);
    if (!CreateProcessA(NULL,cmd,NULL,NULL,TRUE,CREATE_NO_WINDOW,NULL,NULL,&si,&pi)) return false;
    CloseHandle(ir); CloseHandle(ow);
    G.sfIn=iw; G.sfOut=or2; G.sfProc=pi.hProcess; G.sfThr=pi.hThread;
    DWORD w;
    WriteFile(G.sfIn,"uci\n",4,&w,NULL); sfRead("uciok");
    WriteFile(G.sfIn,"ucinewgame\n",11,&w,NULL);
    WriteFile(G.sfIn,"isready\n",8,&w,NULL); sfRead("readyok");
    std::string sc="setoption name Skill Level value "+std::to_string(G.skillLv)+"\n";
    WriteFile(G.sfIn,sc.c_str(),(DWORD)sc.size(),&w,NULL);
    return true;
}

static void initGame() {
    const char* back="rnbqkbnr";
    for (int c=0;c<8;c++) {
        G.board[0][c]=back[c]; G.board[1][c]='p';
        for (int r=2;r<6;r++) G.board[r][c]='.';
        G.board[6][c]='P'; G.board[7][c]=(char)toupper(back[c]);
    }
    G.wKM=G.bKM=G.wARM=G.wHRM=G.bARM=G.bHRM=false;
    G.epR=G.epC=-1; G.selR=G.selC=-1; G.legal.clear();
    G.lastFR=G.lastFC=G.lastTR=G.lastTC=-1;
    G.inCheck=G.gameOver=G.sfBusy=false;
    G.uciMoves.clear();
}

// ===================== WINMAIN =====================
int WINAPI WinMain(HINSTANCE hInst, HINSTANCE, LPSTR, int nShow) {
    int r1=MessageBoxA(NULL,"Chon nhom do kho:\n\nYes = De / Trung binh\nNo  = Kho / Chuyen gia","Do kho (1/2)",MB_YESNO|MB_ICONQUESTION);
    if (r1==IDYES) {
        int r2=MessageBoxA(NULL,"Yes = De (Skill 3, 200ms)\nNo  = Trung binh (Skill 10, 500ms)","Do kho (2/2)",MB_YESNO);
        if (r2==IDYES){G.skillLv=3;G.movetime=200;}else{G.skillLv=10;G.movetime=500;}
    } else {
        int r2=MessageBoxA(NULL,"Yes = Kho (Skill 18, 1s)\nNo  = Chuyen gia (Skill 20, 2s)","Do kho (2/2)",MB_YESNO);
        if (r2==IDYES){G.skillLv=18;G.movetime=1000;}else{G.skillLv=20;G.movetime=2000;}
    }
    int rc=MessageBoxA(NULL,"Chon quan:\n\nYes = Trang (di truoc)\nNo  = Den (di sau)","Chon quan",MB_YESNO|MB_ICONQUESTION);
    G.playerWhite=(rc==IDYES);

    initGame();
    if (!initSF()) { MessageBoxA(NULL,"Khong mo duoc Stockfish!\nKiem tra lai duong dan.","Loi",MB_OK|MB_ICONERROR); return 1; }

    WNDCLASSA wc{};
    wc.lpfnWndProc=WndProc; wc.hInstance=hInst;
    wc.hbrBackground=(HBRUSH)(COLOR_WINDOW+1);
    wc.lpszClassName="ChessApp";
    wc.hCursor=LoadCursor(NULL,IDC_ARROW);
    RegisterClassA(&wc);

    hWnd=CreateWindowA("ChessApp","Co Vua vs Stockfish",
        WS_OVERLAPPED|WS_CAPTION|WS_SYSMENU|WS_MINIMIZEBOX,
        CW_USEDEFAULT,CW_USEDEFAULT,WIN_W+16,WIN_H+39,NULL,NULL,hInst,NULL);

    hPF=CreateFontW(58,0,0,0,FW_NORMAL,0,0,0,DEFAULT_CHARSET,OUT_DEFAULT_PRECIS,
        CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,DEFAULT_PITCH,L"Segoe UI Symbol");
    hSF=CreateFontW(16,0,0,0,FW_NORMAL,0,0,0,DEFAULT_CHARSET,OUT_DEFAULT_PRECIS,
        CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,DEFAULT_PITCH,L"Arial");

    if (!G.playerWhite) {
        G.playerTurn=false; G.status="Stockfish dang di nuoc dau...";
        sfThink();
    } else {
        G.playerTurn=true; G.status="Den luot cua ban (Trang). Click vao quan de chon.";
    }

    ShowWindow(hWnd,nShow); UpdateWindow(hWnd);
    MSG msg;
    while (GetMessage(&msg,NULL,0,0)) { TranslateMessage(&msg); DispatchMessage(&msg); }
    return (int)msg.wParam;
}
