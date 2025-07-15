#include <iostream>
#include <vector>
#include <queue>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <fstream>
#include <sstream>
#include <tuple>
#include <set>
#include <algorithm>
#include <regex>
#include <map>
#include <filesystem>
namespace fs = std::filesystem;
using namespace std;
vector<tuple<int, int, int>> fixedCells; //For sat solver

bool depthExperiment = true;

bool showIntermediateProcess = false;
int Height = 10;
int Width = 10;
const int DIRECTIONS[4][2] = {{-1, 0}, {1, 0}, {0, -1}, {0, 1}}; // Up, Down, Left, Right
int maxNumOnBoard = 9;

bool showDepth = false;
int maxDepth = 0;
std::map<int, int> depthGapHistogram;

// make a board with 0's
std::vector<std::vector<int>> board(Height, std::vector<int>(Width, 0));

struct Group {
    int number;
    vector<pair<int, int>> cells;
};

vector<Group> globalGroups;


class FillominoSMTSolver {
public:
    int rows, cols;

    FillominoSMTSolver() {}

    vector<pair<int, int>> adj(int row, int col) {
        vector<pair<int, int>> neighbors;
        if (row - 1 >= 0) neighbors.emplace_back(row - 1, col);
        if (row + 1 < rows) neighbors.emplace_back(row + 1, col);
        if (col - 1 >= 0) neighbors.emplace_back(row, col - 1);
        if (col + 1 < cols) neighbors.emplace_back(row, col + 1);
        return neighbors;
    }

    string solve(int r, int c, const vector<tuple<int, int, int>>& nums) {
        ostringstream oss;

        oss << "(set-option :print-success false)" << "\n";
        oss << "(set-logic QF_UFLIA)" << "\n";

        rows = r;
        cols = c;

		//we define edges e_{x}_{y} between cells. 1 if there exists one between two cells, else 0
        for (int row1 = 0; row1 < rows; row1++) {
            for (int col1 = 0; col1 < cols; col1++) {
                int x = row1 * cols + col1;
                for (auto [row2, col2] : adj(row1, col1)) {
                    int y = row2 * cols + col2;
                    oss << "(declare-fun e_" << x << "_" << y << " () Int)" << "\n";
                    oss << "(assert (or (= e_" << x << "_" << y << " 0) (= e_" << x << "_" << y << " 1)))" << "\n";
                }
            }
        }

		//We cant have an edge between cells in both directions, only one direction.
        for (int row1 = 0; row1 < rows; row1++) {
            for (int col1 = 0; col1 < cols; col1++) {
                int x = row1 * cols + col1;
                for (auto [row2, col2] : adj(row1, col1)) {
                    int y = row2 * cols + col2;
                    oss << "(assert (<= (+ e_" << x << "_" << y << " e_" << y << "_" << x << ") 1))" << "\n";
                }
            }
        }

		//each cell is allowed to have at most one incoming edge (tree structure)
        for (int row1 = 0; row1 < rows; row1++) {
            for (int col1 = 0; col1 < cols; col1++) {
                int x = row1 * cols + col1;
                oss << "(assert (<= (+" << "\n";
                for (auto [row2, col2] : adj(row1, col1)) {
                    int y = row2 * cols + col2;
                    oss << "               e_" << y << "_" << x << "\n";
                }
                oss << ") 1))" << "\n";
            }
        }

		//number variable for each cell
        for (int row = 0; row < rows; row++) {
            for (int col = 0; col < cols; col++) {
                int x = row * cols + col;
                oss << "(declare-fun n_" << x << " () Int)" << "\n";
            }
        }

		//If we already know if certain cells contain a certain number, we assign them.
        for (auto [i, j, k] : nums) {
            int x = i * cols + j;
            oss << "(assert (= n_" << x << " " << k << "))" << "\n";
        }

		//size constraint for regions
        for (int row = 0; row < rows; row++) {
            for (int col = 0; col < cols; col++) {
                int x = row * cols + col;
                oss << "(declare-fun s_" << x << " () Int)" << "\n";
            }
        }

		//s_x =  (sum of the sizes of the neighbours connected from this cell) + 1.
        for (int row1 = 0; row1 < rows; row1++) {
            for (int col1 = 0; col1 < cols; col1++) {
                int x = row1 * cols + col1;
                oss << "(assert (= s_" << x << " (+ 1" << "\n";
                for (auto [row2, col2] : adj(row1, col1)) {
                    int y = row2 * cols + col2;
                    oss << "                   (ite (= e_" << x << "_" << y << " 1) s_" << y << " 0)" << "\n";
                }
                oss << ")))" << "\n";
            }
        }

		//if there are no incoming edges, s_x has to equal n_x
        for (int row1 = 0; row1 < rows; row1++) {
            for (int col1 = 0; col1 < cols; col1++) {
                int x = row1 * cols + col1;
                oss << "(assert (=> (= (+" << "\n";
                for (auto [row2, col2] : adj(row1, col1)) {
                    int y = row2 * cols + col2;
                    oss << "                  e_" << y << "_" << x << "\n";
                }
                oss << ") 0) (= s_" << x << " n_" << x << ")))" << "\n";
            }
        }

		//all cells in the same region must have the same number
        for (int row1 = 0; row1 < rows; row1++) {
            for (int col1 = 0; col1 < cols; col1++) {
                int x = row1 * cols + col1;
                for (auto [row2, col2] : adj(row1, col1)) {
                    int y = row2 * cols + col2;
                    oss << "(assert (=> (= e_" << x << "_" << y << " 1) (= n_" << x << " n_" << y << ")))" << "\n";
                }
            }
        }

		//declare root variable for each cell
        for (int row = 0; row < rows; row++) {
            for (int col = 0; col < cols; col++) {
                int x = row * cols + col;
                oss << "(declare-fun r_" << x << " () Int)" << "\n";
            }
        }

		//cells with no incoming edges are roots.
        for (int row1 = 0; row1 < rows; row1++) {
            for (int col1 = 0; col1 < cols; col1++) {
                int x = row1 * cols + col1;
                oss << "(assert (=> (= (+" << "\n";
                for (auto [row2, col2] : adj(row1, col1)) {
                    int y = row2 * cols + col2;
                    oss << "                  e_" << y << "_" << x << "\n";
                }
                oss << ") 0) (= r_" << x << " " << x << ")))" << "\n";
            }
        }

		//connected cells in the same region, must have the same root.
        for (int row1 = 0; row1 < rows; row1++) {
            for (int col1 = 0; col1 < cols; col1++) {
                int x = row1 * cols + col1;
                for (auto [row2, col2] : adj(row1, col1)) {
                    int y = row2 * cols + col2;
                    oss << "(assert (=> (= n_" << x << " n_" << y << ") (= r_" << x << " r_" << y << ")))" << "\n";
                }
            }
        }

        oss << "(check-sat)" << "\n";

        for (int row = 0; row < rows; row++) {
            for (int col = 0; col < cols; col++) {
                int x = row * cols + col;
                oss << "(get-value (n_" << x << "))" << "\n";
            }
        }

        return oss.str();
    }
};


bool loadSMTsolvedBoard(const std::string& filename) {
    std::ifstream file(filename);
    if (!file) {
        std::cout << "cannot open the file:" << filename << std::endl;
        return false;
    }

    std::string ln;
    if (!std::getline(file, ln)) {
        std::cout << "error reading the file" << std::endl;
        return false;
    }
    if (ln.substr(0, 3) != "sat") {
        std::cout << "No solution"<< std::endl;
        return false;
    }

    std::string line;
    std::regex pattern(R"(\(\(n_(\d+) (\d+)\)\))");

    while (std::getline(file, line)) {
        std::smatch matches;
        if (std::regex_match(line, matches, pattern)) {
            int cellIndex = std::stoi(matches[1].str());
            int number = std::stoi(matches[2].str());

            int row = cellIndex / Width;
            int col = cellIndex % Width;

            if (row >= 0 && row < Height && col >= 0 && col < Width) {
                board[row][col] = number;
            }
        }
    }

    file.close();
    return true;
}

bool allGroupsAreExactlyFilled() {
    for (const auto& group : globalGroups) {
        if (group.cells.size() != group.number) {
            return false;
        }
    }
    return true;
}

// Check if a cell is within the board
bool isValid(int i, int j) {
    return (i >= 0 && i < Height && j >= 0 && j < Width);
}

bool existsOverfilledGroup() {
    for (const auto& group : globalGroups) {
        if (group.cells.size() > group.number) {
            return true;
        }
    }
    return false;
}

void displayBoard() {
    cout << "Board Layout:" << endl;
    for (int i = 0; i < Height; i++) {
        for (int j = 0; j < Width; j++) {
            cout << board[i][j] << " ";
        }
        cout << endl;
    }
    cout << endl;
}

// Find the size of a group of a given number
int getGroupSize(int startRow, int startCol, int number) {
    std::vector<std::vector<bool>> visited(Height, std::vector<bool>(Width, false));
    queue<pair<int, int>> q;
    int groupSize = 0;

    q.push({startRow, startCol});
    visited[startRow][startCol] = true;

    while (!q.empty()) {
        auto [row, col] = q.front();
        q.pop();
        groupSize++;

        for (const auto& dir : DIRECTIONS) {
            int newRow = row + dir[0];
            int newCol = col + dir[1];

            if (isValid(newRow, newCol) && !visited[newRow][newCol] && board[newRow][newCol] == number) {
                visited[newRow][newCol] = true;
                q.push({newRow, newCol});
            }
        }
    }

    return groupSize;
}

// Check if we can reach the target cell from any number considering group size
bool canReach(int startRow, int startCol, int targetRow, int targetCol, int number) {
    if (board[startRow][startCol] == 0){
        return false;
    }

    int groupSize = getGroupSize(startRow, startCol, number);
    int allowedMoves = number - groupSize;

    if (allowedMoves < 0){
        return false;
    }

    std::vector<std::vector<bool>> visited(Height, std::vector<bool>(Width, false));

    queue<pair<pair<int, int>, int>> q;

    q.push({{startRow, startCol}, 0});
    visited[startRow][startCol] = true;

    while (!q.empty()) {
        auto front = q.front();
        q.pop();

        int row = front.first.first;
        int col = front.first.second;
        int moves = front.second;

        if (row == targetRow && col == targetCol) return true;

        if (moves >= allowedMoves) continue;

        for (const auto& dir : DIRECTIONS) {
            int newRow = row + dir[0];
            int newCol = col + dir[1];

            if (isValid(newRow, newCol) && !visited[newRow][newCol] && board[newRow][newCol] == 0) {
                visited[newRow][newCol] = true;
                q.push({{newRow, newCol}, moves + 1});
            }
        }
    }

    return false;
}

//find groups in the board and store them
void findAndStoreGroups() {
    globalGroups.clear();
    std::vector<std::vector<bool>> visited(Height, std::vector<bool>(Width, false));


    for (int i = 0; i < Height; i++) {
        for (int j = 0; j < Width; j++) {
            if (board[i][j] != 0 && !visited[i][j]) {
                //BFS to find group
                queue<pair<int, int>> q;
                vector<pair<int, int>> groupCells;
                int number = board[i][j];

                q.push({i, j});
                visited[i][j] = true;

                while (!q.empty()) {
                    auto [row, col] = q.front();
                    q.pop();
                    groupCells.push_back({row, col});

                    for (const auto& dir : DIRECTIONS) {
                        int newRow = row + dir[0];
                        int newCol = col + dir[1];

                        if (isValid(newRow, newCol) && !visited[newRow][newCol] && board[newRow][newCol] == number) {
                            visited[newRow][newCol] = true;
                            q.push({newRow, newCol});
                        }
                    }
                }

                //store into global var
                Group newGroup = {number, groupCells};
                globalGroups.push_back(newGroup);
            }
        }
    }
}

//Checks if this cell can be reached by exactly 1 number
int checkReachability(int targetRow, int targetCol) {

    bool found = false;
    int howManyNumsCanReachThis = 0;
    int lastNumberThatReached = -1;

    for (int number = 2; number <= maxNumOnBoard; number++) {
        bool reachable = false;

        for (int i = 0; i < Height; i++) {
            for (int j = 0; j < Width; j++) {
                if (board[i][j] == number) {
                    if (canReach(i, j, targetRow, targetCol, number)) {
                        reachable = true;
                        break;
                    }
                }
            }
            if (reachable) break;
        }

        if (reachable) {
            lastNumberThatReached = number;
            howManyNumsCanReachThis++;

            if(howManyNumsCanReachThis > 1){
                //More than 1 number can reach this cell
                return -1;
            }
        }
    }

    if (howManyNumsCanReachThis == 0) {
        //No number can reach the empty cell
        return 0;
    }
    else{
        //The only number that could reach the cell
        return lastNumberThatReached;
    }
}

int checkIfEmptyCellCanBeReachedByOneNum(pair<int, int> &whichCell){
    //Checks if there is an empty cell on the board that can be reached by only one number
    whichCell = {-1, -1};
    for (int i = 0; i < Height; i++){
        for(int j = 0; j < Width; j++){
            if (isValid(i, j) && board[i][j] == 0){
                int ReachableCode = checkReachability(i,j);
                if(ReachableCode > 0){
                    //Empty cell as parameter, and which number it only can be reached by, will be returned
                    whichCell = {i, j};
                    return ReachableCode;
                }

            }
        }
    }

    //No empty cell on the board can be reached by exactly 1 number.
    return -1;
}

//If we found a group that isnt full with one exit, we store the exit cell in the parameter and return the number.
int checkSingleExitGroups(pair<int, int> &exitCell) {
    findAndStoreGroups();
    for (const auto& group : globalGroups) {
        int exitCount = 0;
        pair<int, int> tempExit = {-1, -1};

        // Loop through each cell in the group to count exits
        for (const auto& cell : group.cells) {
            int row = cell.first;
            int col = cell.second;

            //check the 4 directions
            for (const auto& dir : DIRECTIONS) {
                int newRow = row + dir[0];
                int newCol = col + dir[1];

                //check if cell is valid
                if (isValid(newRow, newCol) && board[newRow][newCol] == 0 && exitCell == make_pair(-1, -1)) {
                    exitCount++;
                    tempExit = {newRow, newCol};
                    if(exitCount > 1){
                        break;
                    }
                }
            }
            if(exitCount > 1){
                    break;
            }
        }

        //exactly one exit found
        if (exitCount == 1 && group.cells.size() < group.number) {
            exitCell = tempExit;
            return group.number;
        }
    }

    //no group found with exactly one exit
    return -1;
}

bool fillCell(int i, int j, int num) {
    if (!isValid(i, j) || board[i][j] != 0 || num < 2 || num > maxNumOnBoard) {
        return false; 
    }

    board[i][j] = num;
    findAndStoreGroups();
    return true;  
}

bool removeCell(int i, int j) {
    if (isValid(i, j)) {
        board[i][j] = 0;
        findAndStoreGroups();
        return true; 
    }
    
    return false;  
}


//fill board with nums 2-maxNumOnBoard
void fillBoardRandom() {
    srand(time(0));
    const int chanceToFill = 60;

    for (int i = 0; i < Height; i++) {
        for (int j = 0; j < Width; j++) {
            if (rand() % 100 < chanceToFill) { 
                board[i][j] = rand() % 8 + 2;  //random num
            }
        }
    }
    findAndStoreGroups();
}

bool readBoardFromFile(const string& filename) {
    ifstream file(filename);
    if (!file) {
        cout << "cant open file" << endl;
        return false;
    }
    int height, width;
    file >> height >> width;
    Height = height;
    Width = width;
    board.clear();
    board.resize(Height);
    for (int i = 0; i < Height; i++) {
        board[i].resize(Width, 0);
    }
    globalGroups.clear();

    fixedCells.clear();
    for (int i = 0; i < Height; i++) {
        for (int j = 0; j < Width; j++) {
            file >> board[i][j];

            if (board[i][j] != 0) {
                fixedCells.emplace_back(i, j, board[i][j]);
                if (board[i][j] > maxNumOnBoard) {
                    maxNumOnBoard = board[i][j];
                }
            }
        }
    }

    file.close();
    findAndStoreGroups();
    return true;
}

bool KeepCheckingSingleExits(){
    bool changed = false;
    pair<int, int> exitCell = {-1,-1};
    int groupNumber = -1;

    while(true){
        exitCell = {-1,-1};
        groupNumber = checkSingleExitGroups(exitCell);
        if (groupNumber > 0){
            if (!fillCell(exitCell.first, exitCell.second, groupNumber)){
                cout << "error with filling the cell";
            }
            changed = true;
            if(showIntermediateProcess){
                cout << "Filled cell: " << "(" << exitCell.first << "," << exitCell.second << ")" << " with " << groupNumber <<endl;
                displayBoard();
            }
        }
        else{
            break;
        }
    }
    return changed;
}

bool KeepCheckingEmptyReachableCells(){
    bool changed = false;
    pair<int, int> whichCell = {-1,-1};
    int groupNumber = -1;
    while(true){
        whichCell = {-1,-1};
        groupNumber = checkIfEmptyCellCanBeReachedByOneNum(whichCell);
        if (groupNumber > 0){
            if (!fillCell(whichCell.first, whichCell.second, groupNumber)){
                cout << "error with filling the cell";
            }
            changed = true;
            if(showIntermediateProcess){
                cout << "Filled cell: " << "(" << whichCell.first << "," << whichCell.second << ")" << " with " << groupNumber <<endl;
                displayBoard();
            }
        }
        else{
            break;
        }
    }
    return changed;
}

bool canGroupBeCompleted(Group& group) {
    int currentGroupSize = group.cells.size();
    int targetSize = group.number;
    int requiredEmptyCells = targetSize - currentGroupSize;

    if (requiredEmptyCells <= 0) {
        return false;  // Group is already complete
    }

    // To store visited empty cells during BFS
    std::vector<std::vector<bool>> visited(Height, std::vector<bool>(Width, false));


    // BFS to check adjacent empty cells
    queue<pair<int, int>> q;

    for (const auto& cell : group.cells){
        //put the cells from our group to true
        visited[cell.first][cell.second] = true;
    }

    // Enqueue all the boundary cells of the group to start BFS from
    for (const auto& cell : group.cells) {
        int row = cell.first;
        int col = cell.second;

        for (const auto& dir : DIRECTIONS) {
            int newRow = row + dir[0];
            int newCol = col + dir[1];

            if (isValid(newRow, newCol) && !visited[newRow][newCol] && board[newRow][newCol] == 0) {
                visited[newRow][newCol] = true;
                q.push({newRow, newCol});
            }
        }
    }

    int emptyCellsFound = 0;

    while (!q.empty()) {
        auto [row, col] = q.front();
        q.pop();

        // If we've found enough empty cells, return true
        if (++emptyCellsFound >= requiredEmptyCells) {
            return true;
        }

        for (const auto& dir : DIRECTIONS) {
            int newRow = row + dir[0];
            int newCol = col + dir[1];

            //Instead of just checking empty cells, also check if we come across a same number, we could potentially merge with
            //making it so we do have enough cells to complete to group
            if (isValid(newRow, newCol) && !visited[newRow][newCol] && (board[newRow][newCol] == 0 || board[newRow][newCol] == group.number)) {
                visited[newRow][newCol] = true;
                q.push({newRow, newCol});
            }
        }
    }

    // Not enough adjacent empty cells to complete the group
    return false;
}

void checkIncompleteGroups() {
    findAndStoreGroups();

    for (auto& group : globalGroups) {
        if (group.cells.size() < group.number) {
            // The group is incomplete, check if it can be completed
            bool canBeCompleted = canGroupBeCompleted(group);

            cout << "Checking Group " << group.number << " with cells: ";
            for (const auto& cell : group.cells) {
                cout << "(" << cell.first << "," << cell.second << ") ";
            }
            cout << endl;

            if (canBeCompleted) {
                cout << "Group " << group.number << " can be completed." << endl;
            } else {
                cout << "Group " << group.number << " cannot be completed." << endl;
            }
        }
    }
}

bool canAllGroupsBeCompleted(){
    findAndStoreGroups();
    for (auto& group : globalGroups) {
        if (group.cells.size() < group.number){
            //there is at least one group that cannot be completed
            if(!canGroupBeCompleted(group)){
                return false;
            }
        }
    }

    //all groups can be completed
    return true;
}

int findDefinitiveNumber(pair<int, int> &defCell) {
    for (int i = 0; i < Height; i++) {
        for (int j = 0; j < Width; j++) {
            if (board[i][j] == 0) { // Empty cell found
                set<int> possibleNumbers;
                
                // Find numbers that can reach this cell
                for (int number = 2; number <= maxNumOnBoard; number++) {
                    for (int x = 0; x < Height; x++) {
                        for (int y = 0; y < Width; y++) {
                            if (board[x][y] == number && canReach(x, y, i, j, number)) {
                                possibleNumbers.insert(number);
                                break; // No need to check further for this number
                            }
                        }
                    }
                }
                
                int validCount = 0;
                int lastValidNumber = -1;
                // Test filling the cell with each possible number
                for (int num : possibleNumbers) {
                    board[i][j] = num; // Temporarily place the number
                    if (canAllGroupsBeCompleted() && !existsOverfilledGroup()) {
                        validCount++;
                        lastValidNumber = num;
                    }
                    board[i][j] = 0; // Revert change
                    
                    if (validCount > 1){
                        break; // If more than 1 number is valid, move to next cell
                    }
                        
                }
                
                // If exactly one valid number was found, fill it in permanently
                if (validCount == 1) {
                    defCell.first = i;
                    defCell.second = j;
                    return lastValidNumber;
                }
            }
        }
    }

    //No cell found where we can figure out a possible definitive number.
    return -1;
}

bool keepFillingDefinitiveNumbers(){
    bool changed = false;
    pair<int, int> defCell;
    int defNumber;
    while (true)
    {
        defCell = {-1, -1};
        defNumber = findDefinitiveNumber(defCell);
        if (defNumber == -1) {
            //no more definitive numbers can be found
            break;
        }
        if (!fillCell(defCell.first, defCell.second, defNumber)) {
            cout << "Error filling cell (" << defCell.first << ", " << defCell.second << ") with " << defNumber << endl;
        }
        changed = true;
        
        if (showIntermediateProcess) {
            //cout << "Filled cell: (" << defCell.first << ", " << defCell.second << ") with " << defNumber << endl;
            //displayBoard();
        }
    }
    return changed;
}

void applyAllDeterministicFilling() {
    bool overallChanged;

    do {
        overallChanged = false;
        bool easyStratsChanged;
        do {
            easyStratsChanged = false;
            if (KeepCheckingSingleExits()){
                easyStratsChanged = true;
            }
            if (KeepCheckingEmptyReachableCells()){
                easyStratsChanged = true;
            }
            if (easyStratsChanged){
                overallChanged = true;
            }
        } while (easyStratsChanged);

        if (keepFillingDefinitiveNumbers()) {
            overallChanged = true;
        }

    } while (overallChanged);
}

bool solveWithBacktracking(int currentDepth = 0) {
    if ((showDepth || depthExperiment) && currentDepth > maxDepth) {
        maxDepth = currentDepth;
    }

    applyAllDeterministicFilling();

    if (existsOverfilledGroup() || !canAllGroupsBeCompleted()) {
        return false;
    }

    if (allGroupsAreExactlyFilled()) {
        return true;
    }

    auto boardBackup = board;
    vector<Group> groupsBackup = globalGroups;

    for (int i = 0; i < Height; i++) {
        for (int j = 0; j < Width; j++) {
            if (board[i][j] != 0) continue;

            bool triedSomething = false;

            for (int num = 2; num <= maxNumOnBoard; num++) {
                bool reachable = false;

                for (int x = 0; x < Height && !reachable; x++) {
                    for (int y = 0; y < Width && !reachable; y++) {
                        if (board[x][y] == num && canReach(x, y, i, j, num)) {
                            reachable = true;
                        }
                    }
                }

                if (!reachable) continue;

                triedSomething = true;
                board[i][j] = num;
                findAndStoreGroups();

                if (solveWithBacktracking(currentDepth + 1)) {
                    return true;
                }

                // Backtrack
                board = boardBackup;
                globalGroups = groupsBackup;
            }

            if (showDepth && triedSomething) {
                int depthGap = maxDepth - currentDepth;
                depthGapHistogram[depthGap]++;
            }

            return false;
        }
    }

    return false;
}

//finds moves for the challenging version of the game, where you can create new groups
void fillSingleExitCellsAndSafeMoves() {
    bool somethingFilled = true; //track if any cell is filled
    pair<int, int> exitcell = {-1, -1};
    while (somethingFilled) {
        somethingFilled = false;
        int groupNumber = checkSingleExitGroups(exitcell);  //check if there exists a group with a single exit
        if (groupNumber != -1) {  //check if such group was found
            int row = exitcell.first;
            int col = exitcell.second;

            //fill the group
            if (fillCell(row, col, groupNumber)) {
                if (showIntermediateProcess) {
                    cout << "Filled single exit cell (" << row << "," << col << ") with " << groupNumber << endl;
                    displayBoard();
                }
                somethingFilled = true;
            }
        }
        if (!somethingFilled) {
            for (int i = 0; i < Height; i++) {
                for (int j = 0; j < Width; j++) {
                    if (board[i][j] != 0){
                        continue;
                    }

                    int validCount = 0;
                    int lastValidNumber = -1;
                    for (int num = 1; num <= maxNumOnBoard; num++) {
                        board[i][j] = num;
                        if (canAllGroupsBeCompleted() && !existsOverfilledGroup()) {
                            validCount++;
                            lastValidNumber = num;
                        }
                        board[i][j] = 0;

                        //more than 1 numbers doesnt cause issues for the board
                        if (validCount > 1) {
                            break;
                        }
                    }

                    //only one valid num
                    if (validCount == 1) {
                        if (fillCell(i, j, lastValidNumber)) {
                            if (showIntermediateProcess) {
                                cout << "Filled cell (" << i << "," << j << ") with " << lastValidNumber << endl;
                                displayBoard();
                            }
            
                            somethingFilled = true;
                        }
                    }
                }
            }
        }
    }
}

void txtFilesToSMT() {

    string inputDir = "C:\\Users\\Ryan\\Desktop\\baronPuzzles\\";
    string outputDir = "C:\\Users\\Ryan\\Desktop\\baronSMTs\\";

    for (const auto& entry : fs::directory_iterator(inputDir)) {
        if (entry.path().extension() == ".txt") {
            string filename = entry.path().filename().string();
            size_t xPos = filename.find('x');
            size_t pbPos = filename.find("PB");
            size_t dotPos = filename.find('.');

            if (xPos == string::npos || pbPos == string::npos || dotPos == string::npos) {
                cerr << "Bad file format: " << filename << endl;
                continue;
            }

            int height = stoi(filename.substr(0, xPos));
            int width = stoi(filename.substr(xPos + 1, pbPos - xPos - 1));
            string numberPart = filename.substr(pbPos + 2, dotPos - (pbPos + 2));  

            Height = height;
            Width = width;

            string fullPath = entry.path().string();

            if (!readBoardFromFile(fullPath)) {
                cerr << "Cant read: " << fullPath << endl;
                continue;
            }

            FillominoSMTSolver solver;
            string smtOutput = solver.solve(Height, Width, fixedCells);

            //{Height}x{Width}_{number}.txt
            string outPath = outputDir + to_string(Height) + "x" + to_string(Width) + "_" + numberPart + ".txt";

            ofstream outfile(outPath);
            if (!outfile) {
                cerr << "error with: " << outPath << endl;
                continue;
            }

            outfile << smtOutput;
            outfile.close();
            cout << "SMT constraints written to: " << outPath << endl;
        }
    }
}

void experiment() {
    string basePath = "C:\\Users\\Ryan\\Desktop\\baronPuzzles\\";
    string outputCSV = basePath + "results.csv";

    ofstream csvFile(outputCSV);
    if (!csvFile.is_open()) {
        cerr << "Could not open results file for writing.\n";
        return;
    }

    csvFile << "height,width,boardnum,maxdepth,time_ms\n";

    regex filePattern(R"((\d+)x(\d+)PB(\d+)\.txt)");

    for (const auto& entry : fs::directory_iterator(basePath)) {
        if (!entry.is_regular_file()) continue;

        string filename = entry.path().filename().string();
        smatch match;

        if (!regex_match(filename, match, filePattern)) continue;

        int height = stoi(match[1]);
        int width = stoi(match[2]);
        int boardnum = stoi(match[3]);

        string fullPath = entry.path().string();
        cout << "Processing " << filename << endl;

        if (!readBoardFromFile(fullPath)) {
            cout << "Failed to read " << filename << endl;
            continue;
        }

        maxDepth = 0;
        auto start = chrono::high_resolution_clock::now();
        bool solved = solveWithBacktracking();
        auto end = chrono::high_resolution_clock::now();
        auto duration = chrono::duration_cast<chrono::milliseconds>(end - start).count();

        if (solved) {
            cout << "Solved " << filename << ", maxDepth: " << maxDepth << endl;
        } else {
            cout << "Could not solve " << filename << endl;
            exit(1);
        }

        csvFile << height << "," << width << "," << boardnum << ","
                << maxDepth << "," << duration << "\n";
    }

    csvFile.close();
}


int main() {
    char choice;
    while (true) {
        cout << "Choose an option:" << endl
         << "a. Load board from file" << endl
         << "b. Make a move" << endl
         << "c. Remove a number" << endl
         << "d. Check reachability" << endl
         << "e. Check single exit groups" << endl
         << "f. Check if each group can be completed" << endl
         << "g. Check if a cell can only have one number that results in a valid board" << endl
         << "h. Check if there exists an overfilled group in the board" << endl
         << "i. Check if all groups filled with correct amount"  << endl 
         << "j. Export to SMT format (to use with z3, yices etc.)"  << endl
         << "k. Load SMT-solved file as board"  << endl  << endl 
         << "1. Keep checking and filling valid single exits" << endl
         << "2. Keep checking and filling empty cells that can be reached by exactly one number" << endl
         << "3. Keep checking and filling empty cells that can be reached by two or more numbers, but only 1 results in a legal board" << endl
         << "4. Keep backtracking with FindDefinitiveNumber" << endl
         << "5. Keep checking single exits and safe moves (Works with all versions)" << endl
         << "6. Experiment" << endl
         << "7. Exit" << endl
         << "Enter choice: ";

        cin >> choice;
        if (choice == 'a') {
            string filename;
            cout << "Enter filename to load board: ";
            cin >> filename;

            if (readBoardFromFile(filename)) {
                cout << "Board loaded successfully" << endl;
            } else {
                cout << "Failed to load board from file" << endl;
            }
        }
        else if (choice == 'd') {
            pair<int, int> whichCell;
            cout << " " << checkIfEmptyCellCanBeReachedByOneNum(whichCell) << " " << whichCell.first << "," << whichCell.second;
        } else if (choice == 'e') {
            pair<int, int> exitcell;
            cout << " " << checkSingleExitGroups(exitcell) << "" << exitcell.first << "," << exitcell.second;
        } else if (choice == 'b') { 
            int row, col, num;
            cout << "Enter row (0-based index): ";
            cin >> row;
            cout << "Enter column (0-based index): ";
            cin >> col;
            cout << "Enter number to place: ";
            cin >> num;
    
            if (fillCell(row, col,num)) {
                cout << "Cell (" << row << "," << col << ") was successfully filled." << endl;
            } else {
                cout << "Failed to fill cell (" << row << "," << col << ")" << endl;
            }
        } else if (choice == 'c') { 
            int row, col;
            cout << "Enter row (0-based index): ";
            cin >> row;
            cout << "Enter column (0-based index): ";
            cin >> col;
    
            if (removeCell(row, col)) {
                cout << "Cell (" << row << "," << col << ") was successfully removed." << endl;
            } else {
                cout << "This cell is out of bounds" << endl;
            }
        }
        else if(choice == 'f'){
            checkIncompleteGroups();
        }
        else if(choice == 'g'){
            pair<int, int> defCell;
            int defNumber = findDefinitiveNumber(defCell);
            if(defNumber != -1){
                cout << "Number for cell (" << defCell.first << "," << defCell.second << ") has to be " << defNumber << endl;
            }
            else{
                cout << "No cell could be found with a definitive number" << endl;
            }
            
        }
        else if(choice == 'h'){
            if(!existsOverfilledGroup()){
                cout << "There are no overfilled groups" << endl;
            }
            else{
                cout << "There exists an overfilled group" << endl;
            }
            
        }
        else if(choice == 'i'){
            if(allGroupsAreExactlyFilled()){
                cout << "All groups have the correct number of cells" << endl;
            }
            else{
                cout << "There is a group that does not have the correct number of cells" << endl;
            }
        }
        else if (choice == 'j') {
            FillominoSMTSolver solver;
            string smtOutput = solver.solve(Height, Width, fixedCells);

            int suffix = 0;
            string baseName = "satoutputformat";
            string extension = ".txt";
            string filename = baseName + extension;

            // Check for existing files and find an unused filename
            while (ifstream(filename)) {
                suffix++;
                filename = baseName + to_string(suffix) + extension;
            }

            ofstream outfile(filename);
            if (!outfile) {
                cout << "Can't open output file: " << filename << endl;
            } else {
                outfile << smtOutput;
                outfile.close();
                cout << "Constraints written to " << filename << endl;
            }
        }
        else if (choice == 'k') {
            std::string filename;
            std::cout << "enter filename of SMT solver output: ";
            std::cin >> filename;

            if (loadSMTsolvedBoard(filename)) {
                std::cout << "Solution has been set" << std::endl;
            }

            findAndStoreGroups();
        }
        else if(choice ==  '1'){
            KeepCheckingSingleExits();
        }
        else if(choice == '2'){
            KeepCheckingEmptyReachableCells();
        }
        else if(choice == '3'){
            keepFillingDefinitiveNumbers();
        }
        else if (choice == '4') {
            if(showDepth){
                depthGapHistogram.clear();
            }
            
            solveWithBacktracking();
            if(showDepth){
                std::cout << endl << "Backtrack depth gap histogram (gap -> count):" << endl;
                for (const auto& entry : depthGapHistogram) {
                    std::cout << "Gap " << entry.first << " -> " << entry.second << " times" << endl;
                }
            }
            
        }
        else if(choice == '5'){
            fillSingleExitCellsAndSafeMoves();
        }
        else if (choice == '6') {
            experiment();
        }
        else if (choice == '7') {
            break;
        }
        else {
            cout << "Invalid choice" << endl;
        }

        // display board after every action
        displayBoard();
    }

    return 0;
}