#include <windows.h>
#include <iostream>
#include <string>
#include <vector>
#include <sstream>
#include <cstring>

// Sửa lỗi: bỏ .exe thừa ở cuối đường dẫn
const char* STOCKFISH_PATH = "C:\\Users\\Huyen\\Downloads\\stockfish\\stockfish\\stockfish.exe";

// ================== ĐỌC ĐẾN KHI GẶP TỪ KHÓA ==================
void readUntil(HANDLE hRead, const char* keyword) {
    char buffer[256];
    DWORD read;
    std::string out;

    while (ReadFile(hRead, buffer, sizeof(buffer) - 1, &read, NULL)) {
        buffer[read] = '\0';
        out += buffer;
        if (out.find(keyword) != std::string::npos) break;
    }
}

// ================== LẤY BESTMOVE TỪ STOCKFISH ==================
std::string getBestMove(
    HANDLE hIn,
    HANDLE hOut,
    const std::vector<std::string>& moves,
    int movetime
) {
    DWORD written;
    char buffer[256];
    DWORD read;

    std::string cmd = "position startpos moves";
    for (auto& m : moves) cmd += " " + m;
    cmd += "\n";
    WriteFile(hIn, cmd.c_str(), (DWORD)cmd.size(), &written, NULL);

    std::string goCmd = "go movetime " + std::to_string(movetime) + "\n";
    WriteFile(hIn, goCmd.c_str(), (DWORD)goCmd.size(), &written, NULL);

    std::string output;
    while (ReadFile(hOut, buffer, sizeof(buffer) - 1, &read, NULL)) {
        buffer[read] = '\0';
        output += buffer;

        size_t p = output.find("bestmove ");
        if (p != std::string::npos) {
            std::istringstream iss(output.substr(p));
            std::string tmp, best;
            iss >> tmp >> best;
            return best;
        }
    }
    return "";
}

// ================== KIỂM TRA ĐỊNH DẠNG NƯỚC ĐI ==================
bool isValidMoveFormat(const std::string& move) {
    // Nước đi hợp lệ: 4 ký tự (vd: e2e4) hoặc 5 ký tự khi phong cấp (vd: e7e8q)
    if (move.size() < 4 || move.size() > 5) return false;

    if (move[0] < 'a' || move[0] > 'h') return false;
    if (move[1] < '1' || move[1] > '8') return false;
    if (move[2] < 'a' || move[2] > 'h') return false;
    if (move[3] < '1' || move[3] > '8') return false;

    // Ký tự phong cấp (nếu có): q, r, b, n
    if (move.size() == 5) {
        char promo = move[4];
        if (promo != 'q' && promo != 'r' && promo != 'b' && promo != 'n')
            return false;
    }

    return true;
}

// ================== MAIN ==================
int main() {
    SECURITY_ATTRIBUTES sa{ sizeof(sa), NULL, TRUE };
    HANDLE inRead, inWrite, outRead, outWrite;

    CreatePipe(&outRead, &outWrite, &sa, 0);
    SetHandleInformation(outRead, HANDLE_FLAG_INHERIT, 0);

    CreatePipe(&inRead, &inWrite, &sa, 0);
    SetHandleInformation(inWrite, HANDLE_FLAG_INHERIT, 0);

    STARTUPINFO si{};
    PROCESS_INFORMATION pi{};
    si.cb = sizeof(si);
    si.dwFlags = STARTF_USESTDHANDLES;
    si.hStdInput  = inRead;
    si.hStdOutput = outWrite;
    si.hStdError  = outWrite;

    char cmd[256];
    strcpy(cmd, STOCKFISH_PATH);

    if (!CreateProcess(NULL, cmd, NULL, NULL, TRUE, 0, NULL, NULL, &si, &pi)) {
        std::cout << "Khong mo duoc Stockfish. Kiem tra lai duong dan!\n";
        return 1;
    }

    CloseHandle(inRead);
    CloseHandle(outWrite);

    DWORD written;

    // Khởi tạo UCI
    WriteFile(inWrite, "uci\n", 4, &written, NULL);
    readUntil(outRead, "uciok");

    WriteFile(inWrite, "ucinewgame\n", 11, &written, NULL);
    WriteFile(inWrite, "isready\n", 8, &written, NULL);
    readUntil(outRead, "readyok");

    std::vector<std::string> moves;
    int turnNumber = 1;

    std::cout << "===== CO VUA VS STOCKFISH =====\n";
    std::cout << "Dinh dang nuoc di: e2e4 (hoac e7e8q khi phong cap)\n";
    std::cout << "Nhap 'thoat' de ket thuc\n\n";

    // Chọn độ khó
    int skillLevel = 20;
    int movetime   = 1000;

    std::cout << "Chon do kho:\n";
    std::cout << "  1. De    (Skill 3,  suy nghi 200ms)\n";
    std::cout << "  2. TB    (Skill 10, suy nghi 500ms)\n";
    std::cout << "  3. Kho   (Skill 18, suy nghi 1000ms)\n";
    std::cout << "  4. Chuyen gia (Skill 20, suy nghi 2000ms)\n";

    int diffChoice = 0;
    while (diffChoice < 1 || diffChoice > 4) {
        std::cout << "Lua chon (1-4): ";
        std::cin >> diffChoice;
        if (diffChoice < 1 || diffChoice > 4)
            std::cout << "Vui long nhap so tu 1 den 4!\n";
    }

    switch (diffChoice) {
        case 1: skillLevel = 3;  movetime = 200;  break;
        case 2: skillLevel = 10; movetime = 500;  break;
        case 3: skillLevel = 18; movetime = 1000; break;
        case 4: skillLevel = 20; movetime = 2000; break;
    }

    // Gửi skill level cho Stockfish
    {
        DWORD w;
        std::string skillCmd = "setoption name Skill Level value " + std::to_string(skillLevel) + "\n";
        WriteFile(inWrite, skillCmd.c_str(), (DWORD)skillCmd.size(), &w, NULL);
    }

    const char* diffNames[] = { "", "De", "Trung binh", "Kho", "Chuyen gia" };
    std::cout << "Do kho: " << diffNames[diffChoice] << "\n";

    // Chọn màu quân
    char colorChoice = 0;
    while (colorChoice != 'T' && colorChoice != 'D') {
        std::cout << "Chon quan cua ban ([T]rang / [D]en): ";
        std::string input;
        std::cin >> input;
        colorChoice = (char)toupper(input[0]);
        if (colorChoice != 'T' && colorChoice != 'D')
            std::cout << "Vui long nhap T (trang) hoac D (den)!\n";
    }

    bool playerIsWhite = (colorChoice == 'T');
    std::cout << "Ban choi quan " << (playerIsWhite ? "TRANG (di truoc)" : "DEN (di sau)") << "\n";

    // Nếu người chơi là quân đen, Stockfish đi trước
    if (!playerIsWhite) {
        std::cout << "\nStockfish dang suy nghi...\n";
        std::string best = getBestMove(inWrite, outRead, moves, movetime);
        if (best.empty() || best == "(none)") {
            std::cout << "Loi: Stockfish khong tra ve nuoc di.\n";
        } else {
            std::cout << "Stockfish (Trang): " << best << "\n";
            moves.push_back(best);
        }
    }

    // Vòng lặp game
    while (true) {
        std::cout << "\n--- Luot " << turnNumber << " ---\n";

        // Hiển thị lịch sử nước đi
        if (!moves.empty()) {
            std::cout << "Lich su: ";
            for (size_t i = 0; i < moves.size(); i++) {
                if (i % 2 == 0) std::cout << (i / 2 + 1) << ". ";
                std::cout << moves[i] << " ";
            }
            std::cout << "\n";
        }

        std::string userMove;
        std::cout << "Nguoi choi (" << (playerIsWhite ? "Trang" : "Den") << "): ";
        std::cin >> userMove;

        if (userMove == "thoat") break;

        if (!isValidMoveFormat(userMove)) {
            std::cout << "Sai dinh dang! Vi du hop le: e2e4 hoac e7e8q\n";
            continue;
        }

        moves.push_back(userMove);

        std::cout << "Stockfish dang suy nghi...\n";
        std::string best = getBestMove(inWrite, outRead, moves, movetime);
        if (best.empty() || best == "(none)") {
            std::cout << "Stockfish khong tim duoc nuoc di. Ban da thang!\n";
            break;
        }

        std::cout << "Stockfish (" << (playerIsWhite ? "Den" : "Trang") << "): " << best << "\n";
        moves.push_back(best);
        turnNumber++;
    }

    WriteFile(inWrite, "quit\n", 5, &written, NULL);

    CloseHandle(inWrite);
    CloseHandle(outRead);
    CloseHandle(pi.hProcess);
    CloseHandle(pi.hThread);

    std::cout << "\nKet thuc game. Tam biet!\n";
    return 0;
}
