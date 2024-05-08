#include <algorithm>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <set>
#include <vector>

using namespace std;

int main() {
    const int numNodes = 1000;
    const int numEdges = 1500;
    const int numStations = 200;

    // 使用随机数生成器生成图的数据
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<> dis(1, numNodes);   // 结点编号从1开始
    uniform_int_distribution<> disWeight(1, 200);  // 边的权重范围为1到100

    // 生成边的数据
    vector<pair<int, int>> edges;
    set<pair<int, int>> edgeSet;  // 使用set来避免重复的边

    // 创建一个生成树
    vector<int> nodes(numNodes);
    iota(nodes.begin(), nodes.end(), 1);       // 填充1到numNodes
    shuffle(nodes.begin(), nodes.end(), gen);  // 随机打乱

    for (int i = 0; i < numNodes - 1; ++i) {
        edges.push_back({nodes[i], nodes[i + 1]});
        edgeSet.insert({min(nodes[i], nodes[i + 1]), max(nodes[i], nodes[i + 1])});
    }

    // 随机添加额外的边
    while (edges.size() < numEdges) {
        int u = dis(gen);
        int v = dis(gen);
        if (u != v && edgeSet.find({min(u, v), max(u, v)}) == edgeSet.end()) {
            edgeSet.insert({min(u, v), max(u, v)});
            edges.push_back({u, v});
        }
    }

    // 生成充电站节点编号
    set<int> stations;
    while (stations.size() < numStations) {
        stations.insert(dis(gen));
    }

    // 写入文件
    ofstream outFile_original("graph_data.txt");
    ofstream outFile_CH("graph_data_for_CH.txt");

    if (!outFile_original) {
        cerr << "Unable to open output file!" << endl;
        return 1;
    }
    if (!outFile_CH) {
        cerr << "Unable to open output file!" << endl;
        return 1;
    }

    outFile_original << numNodes << endl;
    outFile_CH << numNodes << " " << edges.size() << endl;
    for (const auto& edge : edges) {
        int weight = disWeight(gen);
        outFile_original << edge.first << " " << edge.second << " " << weight << endl;
        outFile_CH << edge.first << " " << edge.second << " " << weight << endl;
        // outFile_CH << edge.second << " " << edge.first << " " << weight << endl;
    }

    outFile_original << "#" << endl;
    for (const auto& station : stations) {
        outFile_original << station << endl;
    }

    outFile_original.close();
    outFile_CH.close();
    cout << "Graph data has been generated and saved to graph_data.txt!" << endl;
    return 0;
}