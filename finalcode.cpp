#include <windows.h>
#include <iostream>
#include <string>
#include <vector>
#include <sstream>
#include <cstring>
#include <cctype>
#include <io.h>
#include <fcntl.h>

const char* STOCKFISH_PATH = "C:\\Users\\Huyen\\Downloads\\stockfish\\stockfish\\stockfish.exe";

// ===================== BOARD STATE =====================
char board[8][8];

void initBoard() {
    const char* back = "rnbqkbnr";
    for (int c = 0; c < 8; c++) {
        board[0][c] = back[c];
        board[1][c] = 'p';
        for (int r = 2; r < 6; r++) board[r][c] = '.';
        board[6][c] = 'P';
        board[7][c] = (char)toupper(back[c]);
    }
}

void applyMove(const std::string& mv) {
    if (mv.size() < 4) return;
    int fc = mv[0]-'a', fr = 8-(mv[1]-'0');
    int tc = mv[2]-'a', tr = 8-(mv[3]-'0');
    char piece = board[fr][fc];
    board[fr][fc] = '.';
    board[tr][tc] = piece;
    if (mv.size() == 5) {
        char p = mv[4];
        board[tr][tc] = isupper(piece) ? (char)toupper(p) : p;
    }
    // Nhập thành
    if ((piece=='K'||piece=='k') && abs(tc-fc)==2) {
        if (tc==6) { board[tr][5]=board[tr][7]; board[tr][7]='.'; }
        else       { board[tr][3]=board[tr][0]; board[tr][0]='.'; }
    }
}

// ===================== CONSOLE DISPLAY =====================
const wchar_t* pieceChar(char p) {
    switch(p) {
        case 'K': return L"♔"; case 'Q': return L"♕"; case 'R': return L"♖";
        case 'B': return L"♗"; case 'N': return L"♘"; case 'P': return L"♙";
        case 'k': return L"♚"; case 'q': return L"♛"; case 'r': return L"♜";
        case 'b': return L"♝"; case 'n': return L"♞"; case 'p': return L"♟";
        default:  return L" ";
    }
}

void gotoXY(HANDLE h, int x, int y) {
    COORD pos = {(SHORT)x, (SHORT)y};
    SetConsoleCursorPosition(h, pos);
}

// fromR/fromC = -1 nghĩa là không highlight
void drawBoard(HANDLE h, int sx, int sy, int fromR=-1, int fromC=-1, int toR=-1, int toC=-1) {
    const WORD LIGHT   = BACKGROUND_RED|BACKGROUND_GREEN|BACKGROUND_BLUE|BACKGROUND_INTENSITY;
    const WORD DARK    = BACKGROUND_BLUE|BACKGROUND_GREEN;
    const WORD HL_FROM = BACKGROUND_RED|BACKGROUND_GREEN|BACKGROUND_INTENSITY; // vàng
    const WORD HL_TO   = BACKGROUND_GREEN|BACKGROUND_INTENSITY;                // xanh lá
    const WORD RESET   = FOREGROUND_RED|FOREGROUND_GREEN|FOREGROUND_BLUE|FOREGROUND_INTENSITY;

    for (int r = 0; r < 8; r++) {
        gotoXY(h, sx, sy+r);
        SetConsoleTextAttribute(h, RESET);
        wprintf(L"%d ", 8-r);

        for (int c = 0; c < 8; c++) {
            bool light = (r+c)%2==0;
            WORD bg = (r==fromR && c==fromC) ? HL_FROM :
                      (r==toR   && c==toC  ) ? HL_TO   :
                      light ? LIGHT : DARK;

            char piece = board[r][c];
            WORD fg = (isupper(piece) && piece!='.') ?
                       FOREGROUND_INTENSITY :
                      (FOREGROUND_RED|FOREGROUND_BLUE|FOREGROUND_INTENSITY);

            SetConsoleTextAttribute(h, bg|fg);
            wprintf(L" %s ", pieceChar(piece));
        }
        SetConsoleTextAttribute(h, RESET);
        wprintf(L" \n");
    }
    gotoXY(h, sx+2, sy+8);
    SetConsoleTextAttribute(h, RESET);
    wprintf(L"  a  b  c  d  e  f  g  h\n");
    SetConsoleTextAttribute(h, FOREGROUND_RED|FOREGROUND_GREEN|FOREGROUND_BLUE);
}

// Animation 3 frame: highlight nguồn → highlight nguồn+đích → áp dụng và vẽ lại
void animateMove(HANDLE h, int sx, int sy, const std::string& mv) {
    if (mv.size() < 4) return;
    int fr = 8-(mv[1]-'0'), fc = mv[0]-'a';
    int tr = 8-(mv[3]-'0'), tc = mv[2]-'a';

    drawBoard(h, sx, sy, fr, fc, -1, -1);  // ô nguồn sáng vàng
    Sleep(350);
    drawBoard(h, sx, sy, fr, fc, tr, tc);  // cả nguồn + đích
    Sleep(350);
    applyMove(mv);
    drawBoard(h, sx, sy, -1, -1, tr, tc);  // quân đã di chuyển, đích sáng xanh
    Sleep(300);
    drawBoard(h, sx, sy);                   // bàn cờ bình thường
}

// ===================== STOCKFISH =====================
void readUntil(HANDLE hRead, const char* kw) {
    char buf[256]; DWORD r;
    std::string out;
    while (ReadFile(hRead, buf, sizeof(buf)-1, &r, NULL)) {
        buf[r]='\0'; out+=buf;
        if (out.find(kw)!=std::string::npos) break;
    }
}

std::string getBestMove(HANDLE hIn, HANDLE hOut,
                        const std::vector<std::string>& moves, int movetime) {
    DWORD w;
    std::string cmd = "position startpos moves";
    for (auto& m : moves) cmd += " "+m;
    cmd += "\n";
    WriteFile(hIn, cmd.c_str(), (DWORD)cmd.size(), &w, NULL);

    std::string go = "go movetime "+std::to_string(movetime)+"\n";
    WriteFile(hIn, go.c_str(), (DWORD)go.size(), &w, NULL);

    char buf[256]; DWORD r;
    std::string out;
    while (ReadFile(hOut, buf, sizeof(buf)-1, &r, NULL)) {
        buf[r]='\0'; out+=buf;
        size_t p = out.find("bestmove ");
        if (p!=std::string::npos) {
            std::istringstream iss(out.substr(p));
            std::string tmp, best;
            iss>>tmp>>best;
            return best;
        }
    }
    return "";
}

bool isValidMove(const std::string& mv) {
    if (mv.size()<4||mv.size()>5) return false;
    if (mv[0]<'a'||mv[0]>'h') return false;
    if (mv[1]<'1'||mv[1]>'8') return false;
    if (mv[2]<'a'||mv[2]>'h') return false;
    if (mv[3]<'1'||mv[3]>'8') return false;
    if (mv.size()==5) {
        char p=mv[4];
        if (p!='q'&&p!='r'&&p!='b'&&p!='n') return false;
    }
    return true;
}

// ===================== MAIN =====================
int main() {
    _setmode(_fileno(stdout), _O_U16TEXT); // bật Unicode output

    HANDLE hCon = GetStdHandle(STD_OUTPUT_HANDLE);

    // Ẩn con trỏ khi animation
    CONSOLE_CURSOR_INFO ci{1, FALSE};
    SetConsoleCursorInfo(hCon, &ci);

    // Khởi động Stockfish
    SECURITY_ATTRIBUTES sa{sizeof(sa), NULL, TRUE};
    HANDLE inRead, inWrite, outRead, outWrite;
    CreatePipe(&outRead, &outWrite, &sa, 0);
    SetHandleInformation(outRead, HANDLE_FLAG_INHERIT, 0);
    CreatePipe(&inRead, &inWrite, &sa, 0);
    SetHandleInformation(inWrite, HANDLE_FLAG_INHERIT, 0);

    STARTUPINFO si{}; PROCESS_INFORMATION pi{};
    si.cb=sizeof(si); si.dwFlags=STARTF_USESTDHANDLES;
    si.hStdInput=inRead; si.hStdOutput=outWrite; si.hStdError=outWrite;

    char cmd[256]; strcpy(cmd, STOCKFISH_PATH);
    if (!CreateProcess(NULL,cmd,NULL,NULL,TRUE,0,NULL,NULL,&si,&pi)) {
        wprintf(L"Khong mo duoc Stockfish! Kiem tra lai duong dan.\n");
        return 1;
    }
    CloseHandle(inRead); CloseHandle(outWrite);

    DWORD written;
    WriteFile(inWrite,"uci\n",4,&written,NULL);
    readUntil(outRead,"uciok");
    WriteFile(inWrite,"ucinewgame\n",11,&written,NULL);
    WriteFile(inWrite,"isready\n",8,&written,NULL);
    readUntil(outRead,"readyok");

    // ---- Màn hình thiết lập ----
    system("cls");
    wprintf(L"===== CO VUA VS STOCKFISH =====\n");
    wprintf(L"Dinh dang nuoc di: e2e4 | phong cap: e7e8q | 'thoat' de ket thuc\n\n");

    // Chọn độ khó
    wprintf(L"Chon do kho:\n");
    wprintf(L"  1. De          (Skill  3,  200ms)\n");
    wprintf(L"  2. Trung binh  (Skill 10,  500ms)\n");
    wprintf(L"  3. Kho         (Skill 18, 1000ms)\n");
    wprintf(L"  4. Chuyen gia  (Skill 20, 2000ms)\n");

    int diff=0, skillLevel=20, movetime=1000;
    while (diff<1||diff>4) {
        wprintf(L"Lua chon (1-4): ");
        std::cin>>diff;
        if (diff<1||diff>4) wprintf(L"Vui long nhap so tu 1 den 4!\n");
    }
    switch(diff) {
        case 1: skillLevel=3;  movetime=200;  break;
        case 2: skillLevel=10; movetime=500;  break;
        case 3: skillLevel=18; movetime=1000; break;
        case 4: skillLevel=20; movetime=2000; break;
    }
    {
        std::string sc="setoption name Skill Level value "+std::to_string(skillLevel)+"\n";
        WriteFile(inWrite,sc.c_str(),(DWORD)sc.size(),&written,NULL);
    }
    const wchar_t* diffNames[]={L"",L"De",L"Trung binh",L"Kho",L"Chuyen gia"};
    wprintf(L"Do kho: %s\n\n", diffNames[diff]);

    // Chọn màu quân
    char col=0;
    while (col!='T'&&col!='D') {
        wprintf(L"Chon quan ([T]rang / [D]en): ");
        std::string inp; std::cin>>inp;
        col=(char)toupper(inp[0]);
        if (col!='T'&&col!='D') wprintf(L"Vui long nhap T hoac D!\n");
    }
    bool isWhite=(col=='T');
    wprintf(L"Ban choi quan %s\n", isWhite?L"TRANG (di truoc)":L"DEN (di sau)");
    Sleep(800);

    // ---- Game ----
    system("cls");
    initBoard();
    const int BX=0, BY=1;   // vị trí bàn cờ
    const int INFO_Y=BY+10; // vùng thông tin bên dưới

    drawBoard(hCon, BX, BY);

    std::vector<std::string> moves;
    int turn=1;

    // Stockfish đi trước nếu người chơi là quân đen
    if (!isWhite) {
        gotoXY(hCon, 0, INFO_Y);
        wprintf(L"Stockfish dang suy nghi...                        ");
        std::string best=getBestMove(inWrite,outRead,moves,movetime);
        if (!best.empty()&&best!="(none)") {
            animateMove(hCon, BX, BY, best);
            moves.push_back(best);
            gotoXY(hCon, 0, INFO_Y);
            wprintf(L"Stockfish (Trang): %hs                           \n", best.c_str());
        }
    }

    // Vòng lặp game
    while (true) {
        gotoXY(hCon, 0, INFO_Y+1);
        wprintf(L"Luot %d | Nuoc cua ban (%s): ", turn, isWhite?L"Trang":L"Den");

        std::string userMove;
        std::cin>>userMove;

        if (userMove=="thoat") break;

        if (!isValidMove(userMove)) {
            gotoXY(hCon, 0, INFO_Y+2);
            wprintf(L"Sai dinh dang! Vi du hop le: e2e4 hoac e7e8q    ");
            continue;
        }

        // Animate nước người chơi
        animateMove(hCon, BX, BY, userMove);
        moves.push_back(userMove);

        gotoXY(hCon, 0, INFO_Y+2);
        wprintf(L"Stockfish dang suy nghi...                           ");

        std::string best=getBestMove(inWrite,outRead,moves,movetime);
        if (best.empty()||best=="(none)") {
            gotoXY(hCon, 0, INFO_Y+2);
            wprintf(L"Stockfish khong tim duoc nuoc di. Ban da thang!  \n");
            break;
        }

        // Animate nước Stockfish
        animateMove(hCon, BX, BY, best);
        moves.push_back(best);

        gotoXY(hCon, 0, INFO_Y);
        wprintf(L"Stockfish (%s): %hs                                  \n",
                isWhite?L"Den":L"Trang", best.c_str());

        turn++;
    }

    WriteFile(inWrite,"quit\n",5,&written,NULL);
    CloseHandle(inWrite); CloseHandle(outRead);
    CloseHandle(pi.hProcess); CloseHandle(pi.hThread);

    ci.bVisible=TRUE;
    SetConsoleCursorInfo(hCon, &ci);

    gotoXY(hCon, 0, INFO_Y+3);
    wprintf(L"Ket thuc game. Tam biet!\n");
    return 0;
}
