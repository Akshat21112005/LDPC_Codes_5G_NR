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
    vector<double> codeRates = {0.25, 1.0/3.0, 0.5, 0.6};
    random_device rd;
    mt19937 gen;

public:
    NRLDPCSimulator() : gen(rd()) {
        for (double ebno = 0.0; ebno <= 1.0; ebno += 0.01) {
            EbNodB.push_back(ebno);
        }
    }

    bool loadBaseMatrix(const string& filename) {
        ifstream file(filename);
        if (!file.is_open()) {
            return false;
        }

        string line;
        baseMatrix.clear();

        while (getline(file, line)) {
            if (line.empty()) {
                continue;
            }

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
                        return false;
                    }
                }
            }
            
            if (!row.empty()) {
                baseMatrix.push_back(row);
            }
        }
        file.close();

        if (baseMatrix.empty()) {
            return false;
        }

        mb = baseMatrix.size();
        nb = baseMatrix[0].size();
        kb = nb - mb;

        for (size_t i = 0; i < baseMatrix.size(); i++) {
            if (baseMatrix[i].size() != nb) {
                return false;
            }
        }
        
        return true;
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

    vector<int> mulSh(const vector<int>& x, int k) {
        if (k == -1) {
            return vector<int>(x.size(), 0);
        }
        return circshift(x, k);
    }

    void generateHMatrix() {
        H.clear();
        H.resize(mb * z, vector<int>(nb * z, 0));
        
        vector<vector<int>> Iz(z, vector<int>(z, 0));
        for (int i = 0; i < z; i++) {
            Iz[i][i] = 1;
        }

        for (int kk = 0; kk < mb; kk++) {
            for (int kk1 = 0; kk1 < nb; kk1++) {
                int tmpvecR_start = kk * z;
                int tmpvecC_start = kk1 * z;
                
                if (baseMatrix[kk][kk1] == -1) {
                    for (int i = 0; i < z; i++) {
                        for (int j = 0; j < z; j++) {
                            H[tmpvecR_start + i][tmpvecC_start + j] = 0;
                        }
                    }
                } else {
                    for (int i = 0; i < z; i++) {
                        for (int j = 0; j < z; j++) {
                            H[tmpvecR_start + i][tmpvecC_start + ((j + baseMatrix[kk][kk1]) % z)] = Iz[i][j];
                        }
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
                    
                    for (int k = 0; k < z; k++) {
                        temp[k] ^= mulResult[k];
                    }
                }
            }
            
            int p1_sh = (baseMatrix[2][nb - mb + 1] == -1) ? 
                       baseMatrix[3][nb - mb + 1] : 
                       baseMatrix[2][nb - mb + 1];
            
            cword[(nb - mb) * z] = mulSh(temp, z - p1_sh)[0];
            
            for (int k = 0; k < z; k++) {
                cword[(nb - mb) * z + k] = temp[k];
            }
        }

        for (int i = 1; i < min(4, mb); i++) {
            fill(temp.begin(), temp.end(), 0);
            
            for (int j = 0; j < nb - mb + i; j++) {
                if (baseMatrix[i][j] != -1) {
                    vector<int> cwPart(cword.begin() + j*z, cword.begin() + (j+1)*z);
                    vector<int> mulResult = mulSh(cwPart, baseMatrix[i][j]);
                    
                    for (int k = 0; k < z; k++) {
                        temp[k] ^= mulResult[k];
                    }
                }
            }
            
            for (int k = 0; k < z; k++) {
                cword[(nb - mb + i) * z + k] = temp[k];
            }
        }

        for (int i = 4; i < mb; i++) {
            fill(temp.begin(), temp.end(), 0);
            
            for (int j = 0; j < nb - mb + 4; j++) {
                if (baseMatrix[i][j] != -1) {
                    vector<int> cwPart(cword.begin() + j*z, cword.begin() + (j+1)*z);
                    vector<int> mulResult = mulSh(cwPart, baseMatrix[i][j]);
                    
                    for (int k = 0; k < z; k++) {
                        temp[k] ^= mulResult[k];
                    }
                }
            }
            
            for (int k = 0; k < z; k++) {
                cword[(nb - mb + i - 1) * z + k] = temp[k];
            }
        }
        
        return cword;
    }

    vector<int> minSumDecode(const vector<double>& llr, int max_iter) {
        int m = H.size();
        int n = H[0].size();
        
        vector<vector<double>> msg_c2v(m, vector<double>(n, 0.0));
        vector<vector<double>> msg_v2c(m, vector<double>(n, 0.0));
        vector<double> llrVal = llr;
        vector<double> prev_msg_v2c(m * n);

        for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) {
                if (H[i][j]) {
                    msg_v2c[i][j] = llrVal[j];
                }
            }
        }

        for (int iter = 0; iter < max_iter; iter++) {
            for (int idx = 0; idx < m * n; idx++) {
                prev_msg_v2c[idx] = msg_v2c[idx / n][idx % n];
            }

            for (int i = 0; i < m; i++) {
                vector<int> cols;
                for (int j = 0; j < n; j++) {
                    if (H[i][j]) {
                        cols.push_back(j);
                    }
                }
                
                vector<double> signs(cols.size());
                vector<double> abs_msg(cols.size());
                
                for (size_t j = 0; j < cols.size(); j++) {
                    signs[j] = signbit(msg_v2c[i][cols[j]]) ? -1.0 : 1.0;
                    abs_msg[j] = abs(msg_v2c[i][cols[j]]);
                }
                
                for (size_t j = 0; j < cols.size(); j++) {
                    double min1 = numeric_limits<double>::infinity();
                    double min2 = min1;
                    
                    for (size_t k = 0; k < cols.size(); k++) {
                        if (k != j) {
                            if (abs_msg[k] < min1) {
                                min2 = min1;
                                min1 = abs_msg[k];
                            } else if (abs_msg[k] < min2) {
                                min2 = abs_msg[k];
                            }
                        }
                    }
                    
                    double alpha = 0.0;
                    double sign_product = 1.0;
                    
                    for (size_t k = 0; k < cols.size(); k++) {
                        if (k != j) {
                            sign_product *= signs[k];
                        }
                    }
                    
                    msg_c2v[i][cols[j]] = sign_product * min1 * alpha;
                }
            }

            for (int j = 0; j < n; j++) {
                vector<int> rows;
                for (int i = 0; i < m; i++) {
                    if (H[i][j]) {
                        rows.push_back(i);
                    }
                }
                
                double sum_llr = llrVal[j];
                for (int i : rows) {
                    sum_llr += msg_c2v[i][j];
                }
                
                for (int i : rows) {
                    msg_v2c[i][j] = sum_llr - msg_c2v[i][j];
                }
            }

            for (int i = 0; i < m; i++) {
                for (int j = 0; j < n; j++) {
                    if (H[i][j] && 
                        signbit(msg_v2c[i][j]) != signbit(prev_msg_v2c[i * n + j]) && 
                        iter > 0) {
                        msg_v2c[i][j] = 0;
                    }
                }
            }

            vector<double> posterior_llr(n, 0.0);
            for (int j = 0; j < n; j++) {
                posterior_llr[j] = llrVal[j];
                for (int i = 0; i < m; i++) {
                    if (H[i][j]) {
                        posterior_llr[j] += msg_c2v[i][j];
                    }
                }
            }
            
            vector<int> decodedBits(n);
            for (int j = 0; j < n; j++) {
                decodedBits[j] = posterior_llr[j] < 0 ? 1 : 0;
            }

            vector<int> check = matrixMultiply(H, decodedBits);
            bool allZero = all_of(check.begin(), check.end(), [](int x) { 
                return x % 2 == 0; 
            });
            
            if (allZero) {
                break;
            }
        }

        vector<int> decodedBits(n);
        for (int j = 0; j < n; j++) {
            double posterior_llr = llrVal[j];
            for (int i = 0; i < m; i++) {
                if (H[i][j]) {
                    posterior_llr += msg_c2v[i][j];
                }
            }
            decodedBits[j] = posterior_llr < 0 ? 1 : 0;
        }
        
        return decodedBits;
    }

    vector<int> matrixMultiply(const vector<vector<int>>& A, const vector<int>& x) {
        vector<int> result(A.size(), 0);
        
        for (size_t i = 0; i < A.size(); i++) {
            for (size_t j = 0; j < x.size(); j++) {
                result[i] = (result[i] + A[i][j] * x[j]) % 2;
            }
        }
        
        return result;
    }

    vector<double> awgnChannel(const vector<int>& codeword, double sigma) {
        normal_distribution<double> noise(0.0, sigma);
        vector<double> received(codeword.size());
        
        for (size_t i = 0; i < codeword.size(); i++) {
            double txSig = 1.0 - 2.0 * codeword[i];
            received[i] = 2.0 * (txSig + noise(gen)) / (sigma * sigma);
        }
        
        return received;
    }

    void runSimulation(const string& baseMatrixFile) {
        const int Nsim = 100;
        const int maxIter = 10;

        if (!loadBaseMatrix(baseMatrixFile)) {
            return;
        }
        
        generateHMatrix();

        vector<vector<double>> BER(codeRates.size(), vector<double>(EbNodB.size(), 0.0));
        vector<vector<double>> p_error(codeRates.size(), vector<double>(EbNodB.size(), 0.0));

        for (size_t crIdx = 0; crIdx < codeRates.size(); crIdx++) {
            double codeRate = codeRates[crIdx];
            int numShortened = 2 * z;
            int totalBitsAfterShortening = nb * z - numShortened;
            int actualInfoBits = kb * z - numShortened;
            
            double desiredCodewordLength = actualInfoBits / codeRate;
            desiredCodewordLength = max(desiredCodewordLength, static_cast<double>(actualInfoBits));
            
            int numPunctured = totalBitsAfterShortening - desiredCodewordLength;
            numPunctured = max(0, static_cast<int>(round(numPunctured)));
            
            int availableParity = mb * z - (numShortened - (nb - mb) * z);
            availableParity = max(0, availableParity);
            
            numPunctured = min(numPunctured, availableParity);
            numPunctured = (numPunctured / z) * z;
            
            double actualCodeRate = static_cast<double>(actualInfoBits) / 
                                   (totalBitsAfterShortening - numPunctured);

            for (size_t ebNoIdx = 0; ebNoIdx < EbNodB.size(); ebNoIdx++) {
                double EbNo_linear = pow(10.0, EbNodB[ebNoIdx] / 10.0);
                double sigma = sqrt(1.0 / (2.0 * actualCodeRate * EbNo_linear));
                int errorCount = 0;
                int bitError = 0;

                for (int sim = 0; sim < Nsim; sim++) {
                    vector<int> infoBits(actualInfoBits);
                    uniform_int_distribution<int> bitDist(0, 1);
                    
                    for (int& bit : infoBits) {
                        bit = bitDist(gen);
                    }

                    vector<int> paddedInfo(numShortened + actualInfoBits, 0);
                    for (int i = numShortened; i < paddedInfo.size(); i++) {
                        paddedInfo[i] = infoBits[i - numShortened];
                    }

                    vector<int> codeword = encode(paddedInfo);
                    vector<int> tx_codeword(codeword.begin() + numShortened, 
                                           codeword.end() - numPunctured);

                    vector<double> received = awgnChannel(tx_codeword, sigma);

                    vector<double> llr(numShortened + tx_codeword.size() + numPunctured);
                    fill(llr.begin(), llr.begin() + numShortened, 1e20);
                    
                    for (size_t i = 0; i < received.size(); i++) {
                        llr[numShortened + i] = received[i];
                    }
                    
                    fill(llr.begin() + numShortened + received.size(), llr.end(), 0.0);

                    vector<int> decodedBits = minSumDecode(llr, maxIter);
                    vector<int> receivedInfo(decodedBits.begin() + numShortened, 
                                           decodedBits.begin() + numShortened + actualInfoBits);

                    for (size_t i = 0; i < receivedInfo.size(); i++) {
                        if (receivedInfo[i] != infoBits[i]) {
                            bitError++;
                        }
                    }
                    
                    if (!equal(receivedInfo.begin(), receivedInfo.end(), infoBits.begin())) {
                        errorCount++;
                    }
                }

                BER[crIdx][ebNoIdx] = static_cast<double>(bitError) / (Nsim * actualInfoBits);
                p_error[crIdx][ebNoIdx] = static_cast<double>(errorCount) / Nsim;
            }
        }

        saveResults(BER, p_error);
    }

    void saveResults(const vector<vector<double>>& BER, const vector<vector<double>>& p_error) {
        ofstream berFile("ber_results.txt");
        berFile << "EbN0_dB";
        for (size_t i = 0; i < codeRates.size(); i++) {
            berFile << "\tRate_" << codeRates[i];
        }
        berFile << endl;
        
        for (size_t i = 0; i < EbNodB.size(); i++) {
            berFile << EbNodB[i];
            for (size_t j = 0; j < codeRates.size(); j++) {
                berFile << "\t" << scientific << BER[j][i];
            }
            berFile << endl;
        }
        berFile.close();

        ofstream ferFile("bler_results.txt");
        ferFile << "EbN0_dB";
        for (size_t i = 0; i < codeRates.size(); i++) {
            ferFile << "\tRate_" << codeRates[i];
        }
        ferFile << endl;
        
        for (size_t i = 0; i < EbNodB.size(); i++) {
            ferFile << EbNodB[i];
            for (size_t j = 0; j < codeRates.size(); j++) {
                ferFile << "\t" << scientific << p_error[j][i];
            }
            ferFile << endl;
        }
        ferFile.close();
    }
};

int main(int argc, char* argv[]) {
    NRLDPCSimulator simulator;
    string baseMatrixFile = "NR_2_6_52.txt";
    
    if (argc > 1) {
        baseMatrixFile = argv[1];
    }
    
    simulator.runSimulation(baseMatrixFile);
    return 0;
}