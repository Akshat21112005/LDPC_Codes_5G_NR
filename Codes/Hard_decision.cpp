#include <iostream>
#include <vector>
#include <random>
#include <cmath>
#include <algorithm>
#include <fstream>
#include <iomanip>
#include <sstream>
#include <string>

using namespace std;

class NRLDPCSimulator {
private:
    vector<vector<int>> baseMatrix;
    int z = 52;
    int mb, nb, kb;
    vector<vector<int>> H;
    vector<double> EbNodB;
    vector<double> codeRates;
    random_device rd;
    mt19937 gen;

public:
    NRLDPCSimulator() : gen(rd()) {
        for (double ebno = 0.0; ebno <= 10.0; ebno += 0.5) {
            EbNodB.push_back(ebno);
        }
        codeRates = {0.25, 1.0/3.0, 0.5, 0.6};
    }

    bool loadBaseMatrix(const string& filename) {
        ifstream file(filename);
        if (!file.is_open()) {
            cerr << "Error: Could not open file " << filename << endl;
            return false;
        }

        string line;
        baseMatrix.clear();

        while (getline(file, line)) {
            if (line.empty()) continue;

            vector<int> row;
            stringstream ss(line);
            string token;

            while (ss >> token) {
                token.erase(remove(token.begin(), token.end(), ','), token.end());
                token.erase(remove(token.begin(), token.end(), ';'), token.end());
                if (!token.empty()) {
                    try {
                        row.push_back(stoi(token));
                    } catch (const exception& e) {
                        cerr << "Error parsing value: " << token << endl;
                        return false;
                    }
                }
            }
            if (!row.empty()) baseMatrix.push_back(row);
        }
        file.close();

        if (baseMatrix.empty()) {
            cerr << "Error: No data loaded from file" << endl;
            return false;
        }

        mb = baseMatrix.size();
        nb = baseMatrix[0].size();
        kb = nb - mb;

        for (size_t i = 0; i < baseMatrix.size(); i++) {
            if (baseMatrix[i].size() != nb) {
                cerr << "Error: Row " << i << " has " << baseMatrix[i].size() 
                     << " columns, expected " << nb << endl;
                return false;
            }
        }
        return true;
    }

    void printBaseMatrix(int maxRows = 5, int maxCols = 10) {
        for (int i = 0; i < min(maxRows, (int)baseMatrix.size()); i++) {
            for (int j = 0; j < min(maxCols, (int)baseMatrix[i].size()); j++) {
                cout << setw(4) << baseMatrix[i][j];
            }
            if (baseMatrix[i].size() > maxCols) cout << " ...";
            cout << endl;
        }
        if (baseMatrix.size() > maxRows) cout << "  ..." << endl;
    }

    vector<int> circshift(const vector<int>& vec, int shift) {
        vector<int> result(vec.size());
        int n = vec.size();
        shift = ((shift % n) + n) % n;

        for (int i = 0; i < n; i++) {
            result[i] = vec[(i + shift) % n];
        }
        return result;
    }

    vector<int> mulSh(const vector<int>& msg, int shift) {
        if (shift == -1) return vector<int>(z, 0);

        vector<int> identity(z, 0);
        for (int i = 0; i < z; i++) identity[i] = (i == 0) ? 1 : 0;

        vector<int> shifted = circshift(identity, -shift);
        vector<int> result(z, 0);

        for (int i = 0; i < z; i++) {
            for (int j = 0; j < z; j++) {
                if (shifted[i] && msg[j]) {
                    result[(i + j) % z] ^= 1;
                }
            }
        }
        return result;
    }

    void generateHMatrix() {
        H.clear();
        H.resize(mb * z, vector<int>(nb * z, 0));

        for (int i = 0; i < mb; i++) {
            for (int j = 0; j < nb; j++) {
                int startRow = i * z;
                int startCol = j * z;

                if (baseMatrix[i][j] != -1) {
                    for (int k = 0; k < z; k++) {
                        int shiftedPos = (k + baseMatrix[i][j]) % z;
                        H[startRow + k][startCol + shiftedPos] = 1;
                    }
                }
            }
        }
    }

    vector<int> encode(const vector<int>& msg) {
        vector<int> cword(nb * z, 0);

        for (int i = 0; i < (nb - mb) * z; i++) {
            cword[i] = msg[i];
        }

        vector<int> temp(z, 0);

        for (int i = 0; i < min(4, mb); i++) {
            fill(temp.begin(), temp.end(), 0);
            for (int j = 0; j < nb - mb; j++) {
                if (baseMatrix[i][j] != -1) {
                    vector<int> msgPart(msg.begin() + j*z, msg.begin() + (j+1)*z);
                    vector<int> mulResult = mulSh(msgPart, baseMatrix[i][j]);
                    for (int k = 0; k < z; k++) temp[k] ^= mulResult[k];
                }
            }
            int parityStart = (nb - mb + i) * z;
            for (int k = 0; k < z; k++) cword[parityStart + k] = temp[k];
        }

        for (int i = 4; i < mb; i++) {
            fill(temp.begin(), temp.end(), 0);
            for (int j = 0; j < nb - mb + min(i, 4); j++) {
                if (baseMatrix[i][j] != -1) {
                    vector<int> cwPart(cword.begin() + j*z, cword.begin() + (j+1)*z);
                    vector<int> mulResult = mulSh(cwPart, baseMatrix[i][j]);
                    for (int k = 0; k < z; k++) temp[k] ^= mulResult[k];
                }
            }
            int parityStart = (nb - mb + i) * z;
            for (int k = 0; k < z; k++) cword[parityStart + k] = temp[k];
        }
        return cword;
    }

    vector<int> decode(const vector<double>& receivedLLR, int maxIter, int nBlockLength) {
        int nRows = mb * z;
        int nCols = nBlockLength;
        vector<vector<int>> Hshort(nRows, vector<int>(nCols));
        for (int i = 0; i < nRows && i < H.size(); i++) {
            for (int j = 0; j < nCols && j < H[i].size(); j++) {
                Hshort[i][j] = H[i][j];
            }
        }

        vector<vector<double>> M(nRows, vector<double>(nCols, 0.0));
        vector<vector<double>> L(nRows, vector<double>(nCols, 0.0));
        vector<int> decodedMsg(nCols, 0);

        for (int col = 0; col < nCols; col++) {
            for (int row = 0; row < nRows; row++) {
                if (row < Hshort.size() && col < Hshort[row].size() && Hshort[row][col] == 1) {
                    M[row][col] = receivedLLR[col];
                }
            }
        }

        for (int iter = 0; iter < maxIter; iter++) {
            for (int row = 0; row < nRows; row++) {
                if (row >= Hshort.size()) continue;
                vector<int> connectedVNs;
                for (int col = 0; col < nCols; col++) {
                    if (col < Hshort[row].size() && Hshort[row][col] == 1) {
                        connectedVNs.push_back(col);
                    }
                }
                for (int vn : connectedVNs) {
                    double product = 1.0;
                    for (int otherVN : connectedVNs) {
                        if (otherVN != vn) product *= tanh(M[row][otherVN] / 2.0);
                    }
                    L[row][vn] = 2.0 * atanh(max(min(product, 0.999), -0.999));
                }
            }

            for (int col = 0; col < nCols; col++) {
                vector<int> connectedCNs;
                for (int row = 0; row < nRows; row++) {
                    if (row < Hshort.size() && col < Hshort[row].size() && Hshort[row][col] == 1) {
                        connectedCNs.push_back(row);
                    }
                }
                double totalLLR = receivedLLR[col];
                for (int cn : connectedCNs) totalLLR += L[cn][col];
                decodedMsg[col] = (totalLLR < 0) ? 1 : 0;

                for (int cn : connectedCNs) {
                    double msgLLR = receivedLLR[col];
                    for (int otherCN : connectedCNs) {
                        if (otherCN != cn) msgLLR += L[otherCN][col];
                    }
                    M[cn][col] = msgLLR;
                }
            }
        }
        return decodedMsg;
    }

    vector<double> awgnChannel(const vector<int>& codeword, double sigma) {
        normal_distribution<double> noise(0.0, sigma);
        vector<double> received(codeword.size());

        for (size_t i = 0; i < codeword.size(); i++) {
            double symbol = 1.0 - 2.0 * codeword[i];
            double noisySample = symbol + noise(gen);
            received[i] = 2.0 * noisySample / (sigma * sigma);
        }
        return received;
    }

    void runSimulation(const string& baseMatrixFile) {
        const int Nsim = 500;
        const int maxIter = 20;

        if (!loadBaseMatrix(baseMatrixFile)) return;
        generateHMatrix();

        vector<vector<double>> BER(codeRates.size(), vector<double>(EbNodB.size(), 0.0));
        vector<vector<double>> FER(codeRates.size(), vector<double>(EbNodB.size(), 0.0));

        for (size_t rateIdx = 0; rateIdx < codeRates.size(); rateIdx++) {
            double codeRate = codeRates[rateIdx];
            int k_pc = kb - 2;
            int nbRM = ceil(k_pc / codeRate) + 2;
            int nBlockLength = nbRM * z;
            int kNumInfoBits = kb * z;

            for (size_t ebnoIdx = 0; ebnoIdx < EbNodB.size(); ebnoIdx++) {
                double EbNo_dB = EbNodB[ebnoIdx];
                double EbNo = pow(10.0, EbNo_dB / 10.0);
                double sigma = sqrt(1.0 / (2.0 * codeRate * EbNo));

                int totalBitErrors = 0;
                int totalFrameErrors = 0;

                for (int sim = 0; sim < Nsim; sim++) {
                    vector<int> message(kNumInfoBits);
                    uniform_int_distribution<int> bitDist(0, 1);
                    for (int& bit : message) bit = bitDist(gen);

                    vector<int> codeword = encode(message);
                    codeword.resize(nBlockLength);
                    vector<double> receivedLLR = awgnChannel(codeword, sigma);
                    vector<int> decodedMsg = decode(receivedLLR, maxIter, nBlockLength);

                    int bitErrors = 0;
                    for (int i = 0; i < kNumInfoBits && i < decodedMsg.size(); i++) {
                        if (decodedMsg[i] != message[i]) bitErrors++;
                    }
                    totalBitErrors += bitErrors;
                    if (bitErrors > 0) totalFrameErrors++;
                }

                BER[rateIdx][ebnoIdx] = (double)totalBitErrors / (kNumInfoBits * Nsim);
                FER[rateIdx][ebnoIdx] = (double)totalFrameErrors / Nsim;
            }
        }
        saveResults(BER, FER);
    }

    void saveResults(const vector<vector<double>>& BER, const vector<vector<double>>& FER) {
        ofstream berFile("ber_results.txt");
        berFile << "EbN0_dB";
        for (size_t i = 0; i < codeRates.size(); i++) {
            berFile << "\tRate_" << codeRates[i];
        }
        berFile << "\tUncoded" << endl;

        for (size_t i = 0; i < EbNodB.size(); i++) {
            berFile << EbNodB[i];
            for (size_t j = 0; j < codeRates.size(); j++) {
                berFile << "\t" << scientific << BER[j][i];
            }
            double EbNo_linear = pow(10.0, EbNodB[i] / 10.0);
            double uncoded_ber = 0.5 * erfc(sqrt(EbNo_linear / 2.0));
            berFile << "\t" << uncoded_ber << endl;
        }
        berFile.close();

        ofstream ferFile("fer_results.txt");
        ferFile << "EbN0_dB";
        for (size_t i = 0; i < codeRates.size(); i++) {
            ferFile << "\tRate_" << codeRates[i];
        }
        ferFile << endl;

        for (size_t i = 0; i < EbNodB.size(); i++) {
            ferFile << EbNodB[i];
            for (size_t j = 0; j < codeRates.size(); j++) {
                ferFile << "\t" << scientific << FER[j][i];
            }
            ferFile << endl;
        }
        ferFile.close();
    }
};

int main(int argc, char* argv[]) {
    NRLDPCSimulator simulator;
    string baseMatrixFile = "NR_2_6_52.txt";
    if (argc > 1) baseMatrixFile = argv[1];
    simulator.runSimulation(baseMatrixFile);
    return 0;
}