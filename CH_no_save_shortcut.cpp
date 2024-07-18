#include <algorithm>
#include <ctime>
#include <fstream>
#include <iostream>
#include <queue>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#define pb push_back
#define mp make_pair
#define fs first
#define sc second

using namespace std;

typedef long long ll;                                                     // 长整型
typedef pair<int, int> Node;                                                // 结点: (结点编号, 距离)
typedef vector<vector<Node>> Graph;                                       // 图: 邻接表
typedef priority_queue<Node, vector<Node>, greater<Node>> DijkstraQueue;  // 最小堆

typedef struct cars {        //存储汽车的相关信息（起始电量、心理阈值、最大续航里程...）
    double remaining_power;   //剩余百分比电量%
    double min_power;       //心理百分比电量阈值%
    double max_distance;    //汽车最大续航里程km
    double battery_capacity;//汽车电池最大容量kW·h

    //返回汽车从x到y的耗能,x与y在原图相邻
    double power_consume(int distance) {
        return distance / max_distance * 100.0;
    }

    double distanceCanRun() {
        return (remaining_power - min_power) / 100 * max_distance;
    }
}bev;

const int INF = 1e9 + 10;  // 无穷大

// ifstream graph("NY_graph.txt");  // 读取图
// ifstream queries("Queries.txt"); // 读取查询

ifstream queries("query2.txt");

// 创建一个ofstream对象，并打开一个名为"output.txt"的文件
std::ofstream outFile("output.txt");

class CH {
private:

    int n, m, s, t, order;                       // n: 结点数, m: 边数, s: 起点, t: 终点, order: 结点顺序
    vector<Graph> G, G_CH;                       // G[0] 表示正向边(u 为边的起点), G[1] 表示反向边(u 为边的终点); G_CH 是包含捷径的叠加图
    vector<vector<int>> dist;                     // 用于存储从每个结点到所有其他结点的最短距离
    vector<DijkstraQueue> pq;                    // 用于存储待处理的结点; 有两个优先队列分别对应正向边pq[0]和反向边pq[1]
    DijkstraQueue imp_pq;                        // 重要性优先队列
    vector<bool> contracted;                     // 判断结点是否已经收缩
    vector<int> imp;                             // 存储结点重要性, 用于确定结点收缩顺序
    vector<int> level;                           // 记录每个结点的层级
    vector<int> contr_neighbours;                // 记录每个结点的收缩邻居数
    unordered_map<string, vector<int>> shortcut;  // 记录捷径的原路径
    unordered_map<string, int> shortcut_weight;    // 记录捷径的权重
    vector<vector<int>> fa;                       // 记录节点的父节点, fa[0]:正向边父节点, fa[1]:反向边父节点
    vector<int> stations;                         // 记录充电站的节点
    bev car;                                      // 记录汽车的信息
    friend class CH_ChargeStation;                // 设置友元类

    // 读取图(读入有向图; 如果要处理无向图则需要将每条边读入两次)
    void read(string input) {
        ifstream graph(input);
        graph >> n >> m;
        G.assign(2, Graph(n + 1, vector<Node>()));  // 初始化图
        int u, v, w;                                // u: 边的起点, v: 边的终点, w: 边的权重
        for (int i = 0; i < m; ++i) {
            graph >> u >> v >> w;
            //u++, v++;    // 结点编号从 1 开始
            if (u == v)  // 排除自环
                continue;
            Connect(G[0][u], v, w);  // 正向边, 表示从结点 u 出发的正向边
            Connect(G[1][v], u, w);  // 反向边, 表示指向结点 v 的反向边
            Connect(G[0][v], u, w);  // 无向图需要将每条边读入两次
            Connect(G[1][u], v, w);  // 无向图需要将每条边读入两次
        }
        int size;
        graph >> size;
        stations.assign(size, false);
        for (int i = 0; i < size; i++) {
            int x;
            graph >> x;
            stations[i] = x;
        }
    }

    // 预处理
    void preprocess() {
        SetOrder();   // 设置结点顺序
        BuildG_CH();  // 构建 CH 图
    }

    // 连接节点
    void Connect(vector<Node>& E, int v, int w) {
        // 检查是否有重边
        for (auto& p : E) {
            if (p.fs == v) {
                p.sc = min(p.sc, w);  // 如果有重边, 取最小值
                return;               // 返回, 不添加新边
            }
        }
        E.pb(mp(v, w));  // 如果没有重边, 添加新边
    }

    // 添加捷径原路径
    void addShortcut(int v, int mid, int u, int distance) {
        // 生成键
        string str_v = to_string(v);
        string str_mid = to_string(mid);
        string str_u = to_string(u);
        string v_mid = str_v + "?" + str_mid;
        string mid_u = str_mid + "?" + str_u;
        string v_u = str_v + "?" + str_u;
        //判断捷径是否已存在/最优
        if (shortcut_weight.find(v_u) != shortcut_weight.end()) {
            if (shortcut_weight[v_u] <= distance) return;
            else shortcut[v_u].clear();
        }
        else {
            shortcut_weight[v_u] = distance;
        }
        // 判断v-mid-u是否包含捷径
        vector<int> vec;
        if (shortcut.find(v_mid) != shortcut.end()) {
            vec.insert(vec.end(), shortcut[v_mid].begin(), shortcut[v_mid].end());
        }
        else {
            vec.insert(vec.end(), { v, mid });
        }
        if (shortcut.find(mid_u) != shortcut.end()) {
            vec.insert(vec.end(), shortcut[mid_u].begin() + 1, shortcut[mid_u].end());
        }
        else {
            vec.insert(vec.end(), { u });
        }
        shortcut[v_u] = vec;
        return;
    }

    // 设置节点顺序
    void SetOrder() {
        contracted.assign(n + 1, 0);        // 初始化节点收缩状态(均未收缩)
        imp.assign(n + 1, 0);               // 初始化节点重要性
        level.assign(n + 1, 0);             // 初始每个结点的层级
        contr_neighbours.assign(n + 1, 0);  // 初始化每个结点的收缩邻居数

        for (int i = 1; i <= n; ++i)
            imp_pq.push(mp(-n, i));  // 初始化重要性优先队列(设置为 -n 保证最优先处理)
        int curr_node, new_imp;
        order = 1;
        while (!imp_pq.empty()) {
            curr_node = imp_pq.top().sc;
            imp_pq.pop();
            new_imp = GetImportance(curr_node);  // 获取节点重要性
            // 如果当前节点的重要性与当前最小重要性之差小于等于10, 则收缩当前节点
            // 即使当前节点被收缩后，下一个节点的收缩操作也不会受到太大影响; 可以有效控制节点收缩的频率
            if (imp_pq.empty() || new_imp - imp_pq.top().fs <= 10) {
                imp[curr_node] = order++;  // 设置节点顺序
                contracted[curr_node] = 1;
                ContractNode(curr_node);
            }
            else {
                imp_pq.push(mp(new_imp, curr_node));  // 否则, 将当前节点重新加入优先队列
            }
        }
    }

    // 获取节点重要性
    int GetImportance(int x) {
        int u, v, shortcuts = 0, in_out = 0;  // shortcuts: 有效快捷路径数, in_out: 原始边数
        for (int i = 0; i < 2; ++i) {
            for (auto& p : G[i][x]) {
                if (!contracted[p.fs])  // 如果邻接结点未被收缩, 则增加原始边数
                    ++in_out;           // 计算原始边数
            }
        }
        for (auto& p1 : G[1][x]) {
            for (auto& p2 : G[0][x]) {
                u = p1.fs;
                v = p2.fs;  // u, v 分别表示 x 的入边和出边的邻接结点(捷径u-x-v)
                // 如果 u 和 v 都未被收缩, 则增加有效快捷路径数
                if (!contracted[u] && !contracted[v])
                    ++shortcuts;
            }
        }
        int edge_diff = shortcuts - in_out;  // 边缘差异 = 添加的快捷方式边数 - 移除的原始边数

        // 返回节点重要性; 重要性 = 边缘差异 + 2 * 收缩邻居数 + 层级
        // *2 放大收缩邻居数量对节点重要性
        return edge_diff + 2 * contr_neighbours[x] + level[x];
    }

    // 收缩节点
    void ContractNode(int x) {
        int u;
        int w, mx = GetMaxEdge(x);
        set<pair<int, int>> out_edges;
        for (auto& p : G[0][x]) {
            if (!contracted[p.fs])
                out_edges.insert(mp(p.fs, p.sc));
        }
        for (auto& p : G[1][x]) {
            u = p.fs;
            if (contracted[u])
                continue;
            w = p.sc;
            Check_Witness(u, x, w, mx, out_edges, 0);  // 检查见证+压缩
        }
        for (int i = 0; i < 2; ++i) {
            for (auto& p : G[i][x]) {
                ++contr_neighbours[p.fs];
                level[p.fs] = max(level[p.fs], level[x] + 1);  // 更新邻居的层级
            }
        }
    }

    // 获取最大边权 (边权大的结点需要保留)
    int GetMaxEdge(int x) {
        int ret = 0;
        for (auto& p1 : G[1][x]) {
            for (auto& p2 : G[0][x]) {
                if (p1.fs != p2.fs && !contracted[p1.fs] && !contracted[p2.fs])
                    ret = max(ret, p1.sc + p2.sc);
            }
        }
        return ret;
    }

    // 检查见证 --        u-x-out_edges
    int Check_Witness(int u, int x, int w, int mx, set<pair<int, int>>& out_edges, bool type) {
        int a, b;                // a: 当前结点, b: 邻接结点
        int curr_dist, new_dist;  // curr_dist: 当前距离, new_dist: 新距离
        DijkstraQueue D_pq;
        unordered_map<int, int> D_dist;
        D_pq.push(mp(0, u));
        D_dist[u] = 0;
        int iter = 250 * (n - order) / n;  // 人为设定一个迭代次数，因为在后期进行收缩成本很高
        // 从u点出发，不断向周边辐射，求从u
        //  开始的路径和，并存于D_dist[b]，b表示终点。
        while (!D_pq.empty() && iter--) {
            curr_dist = D_pq.top().fs;
            a = D_pq.top().sc;
            D_pq.pop();
            if (curr_dist > D_dist[a])
                continue;
            for (auto& p : G[0][a]) {
                new_dist = p.sc + curr_dist;
                b = p.fs;
                if (b != x && !contracted[b]) {
                    if (D_dist.find(b) == D_dist.end() || D_dist[b] > new_dist) {
                        // D_dist[b] < mx避免了无效数据，当D_dist[b] >= mx, a-x-b一定可以压缩
                        if (D_dist[b] < mx)
                            D_dist[b] = new_dist, D_pq.push(mp(new_dist, b));
                    }
                }
            }
        }
        // 压缩，
        int v, ret = 0;
        int new_w;
        for (auto& p : out_edges) {
            v = p.fs, new_w = w + p.sc;
            // 没有见证路径/见证路径比要生成的捷径要大
            if (D_dist.find(v) == D_dist.end() || D_dist.find(v)->sc > new_w) {
                ++ret;
                if (!type && u != v) {
                    Connect(G[0][u], v, new_w);
                    addShortcut(u, x, v, new_w);
                    Connect(G[1][v], u, new_w);
                }
            }
        }
        return ret;
    }

    //返回两个相邻节点x、y在原图的距离
    double getDis(int x, int y, int g) {
        if (x == y) return 0.0;
        for (auto& p : G[g][x]) {
            if (p.first == y)
                return p.second;
        }
        return INF;
    }


    // 构建 CH 图
    void BuildG_CH() {
        G_CH.assign(2, Graph(n + 1, vector<Node>()));
        int v;
        int w;
        for (int u = 1; u <= n; ++u) {
            for (auto& p : G[0][u]) {
                v = p.fs;
                w = p.sc;
                if (imp[v] > imp[u])
                    G_CH[0][u].pb(mp(v, w));
                else
                    G_CH[1][v].pb(mp(u, w));
            }
        }
    }

    // 获得最短路径的途径的节点 path:途径的节点 mid:最短路径的中间节点
    void getNodeInPath(vector<int>& path, int mid) {
        for (int i = 0; i < 2; i++) {
            int x = mid;
            while (fa[i][x] != x) {
                x = fa[i][x];
                if (!i) {
                    path.insert(path.begin(), x);
                }
                else {
                    path.push_back(x);
                }
            }
            if (!i)
                path.push_back(mid);
        }
        for (int i = 1; i < path.size(); i++) {
            string u = to_string(path[i - 1]);
            string v = to_string(path[i]);
            string u_v = u + "?" + v;
            if (shortcut.find(u_v) != shortcut.end()) {
                path.insert(path.begin() + i, shortcut[u_v].begin() + 1, shortcut[u_v].end() - 1);
                // 更新i,指向原i
                i += (shortcut[u_v].end() - 1) - (shortcut[u_v].begin() + 1);
            }
        }
    }

    // 获取最短路径
    int GetDistance(vector<int>& path) {
        dist[0][s] = dist[1][t] = 0;  // s 为起点, t 为终点
        int SP = INF;                  // 最短路径 shortest path
        pq[0].push(mp(0, s));
        pq[1].push(mp(0, t));
        Node front;
        int curr_node;
        int curr_dist;
        int min_node;  // 最短路径的交汇点
        // 从起点和终点分别进行 Dijkstra 操作 (双向 Dijkstra 搜索)
        while (!pq[0].empty() || !pq[1].empty()) {
            if (!pq[0].empty()) {
                front = pq[0].top();
                pq[0].pop();
                curr_node = front.sc;  // 当前结点 (中间结点)
                curr_dist = front.fs;
                if (SP >= curr_dist)
                    RelaxNodeEdges(curr_node, 0);
                // 由于结点只会被访问一次 故双向搜索不会出现重复
                if (SP > dist[0][curr_node] + dist[1][curr_node]) {
                    SP = dist[0][curr_node] + dist[1][curr_node];
                    min_node = curr_node;
                }
            }
            if (!pq[1].empty()) {
                front = pq[1].top();
                pq[1].pop();
                curr_node = front.sc;
                curr_dist = front.fs;
                if (SP >= curr_dist)
                    RelaxNodeEdges(curr_node, 1);
                if (SP > dist[0][curr_node] + dist[1][curr_node]) {
                    SP = dist[0][curr_node] + dist[1][curr_node];
                    min_node = curr_node;
                }
            }
        }
        if (SP == INF)
            return -1;  // 如果不存在最短路径, 返回 -1
        getNodeInPath(path, min_node);
        return SP;
    }

    int GetDistanceWithoutPath() {
        dist[0][s] = dist[1][t] = 0;  // s 为起点, t 为终点
        int SP = INF;                  // 最短路径 shortest path
        pq[0].push(mp(0, s));
        pq[1].push(mp(0, t));
        Node front;
        int curr_node;
        int curr_dist;
        int min_node;  // 最短路径的交汇点
        // 从起点和终点分别进行 Dijkstra 操作 (双向 Dijkstra 搜索)
        while (!pq[0].empty() || !pq[1].empty()) {
            if (!pq[0].empty()) {
                front = pq[0].top();
                pq[0].pop();
                curr_node = front.sc;  // 当前结点 (中间结点)
                curr_dist = front.fs;
                if (SP >= curr_dist)
                    RelaxNodeEdgesWithoutPath(curr_node, 0);
                // 由于结点只会被访问一次 故双向搜索不会出现重复
                if (SP > dist[0][curr_node] + dist[1][curr_node]) {
                    SP = dist[0][curr_node] + dist[1][curr_node];
                    min_node = curr_node;
                }
            }
            if (!pq[1].empty()) {
                front = pq[1].top();
                pq[1].pop();
                curr_node = front.sc;
                curr_dist = front.fs;
                if (SP >= curr_dist)
                    RelaxNodeEdgesWithoutPath(curr_node, 1);
                if (SP > dist[0][curr_node] + dist[1][curr_node]) {
                    SP = dist[0][curr_node] + dist[1][curr_node];
                    min_node = curr_node;
                }
            }
        }
        if (SP == INF)
            return -1;  // 如果不存在最短路径, 返回 -1
        return SP;
    }

    // 松弛操作
    void RelaxNodeEdges(int u, int g) {  // u: 当前结点, g: 当前图 (0表示正向边 1表示反向边)
        int v;
        int w;
        for (auto& p : G_CH[g][u]) {
            v = p.fs, w = p.sc;
            if (dist[g][v] > dist[g][u] + w) {
                dist[g][v] = dist[g][u] + w;
                pq[g].push(mp(dist[g][v], v));
                fa[g][v] = u;
            }
        }
    }

    // 松弛操作不存储父节点
    void RelaxNodeEdgesWithoutPath(int u, int g) {  // u: 当前结点, g: 当前图 (0表示正向边 1表示反向边)
        int v;
        int w;
        for (auto& p : G_CH[g][u]) {
            v = p.fs, w = p.sc;
            if (dist[g][v] > dist[g][u] + w) {
                dist[g][v] = dist[g][u] + w;
                pq[g].push(mp(dist[g][v], v));
            }
        }
    }

public:
    // CH 构造函数
    CH(string input) {
        cout << "Preprocessing...\n\n";
        read(input);
        preprocess();
        cout << "\nPreprocessing done!\n\n";
        car.remaining_power = 80.0;   //起始电量
        car.min_power = 30.0;       //心理阈值
        car.max_distance = 400.0;    //汽车最大续航里程
    }

    CH() {

    }

    // 查询最短路径，并且保存路径
    int Query(int _s, int _t, vector<int>& path) {  // path:最短路径
        s = _s, t = _t;                           // 设置起点和终点
        dist.assign(2, vector<int>(n + 1, INF));   // 初始化距离为无穷大
        // 初始化父节点为它本身
        fa.assign(2, vector<int>(n + 1, 0));
        for (int i = 0; i < n + 1; i++) {
            fa[0][i] = i;
            fa[1][i] = i;
        }
        pq.assign(2, DijkstraQueue());  // 初始化优先队列
        return GetDistance(path);       // 获取最短路径
    }

    // 查询最短路径，并且不保存路径
    int QueryWithoutPath(int _s, int _t) {  // path:最短路径
        s = _s, t = _t;                           // 设置起点和终点
        dist.assign(2, vector<int>(n + 1, INF));   // 初始化距离为无穷大
        // 初始化父节点为它本身
        pq.assign(2, DijkstraQueue());  // 初始化优先队列
        return GetDistanceWithoutPath();       // 获取最短路径
    }

    // 显示捷径
    void showcaseShortcut(ofstream& outFile) {
        long long shortcuts_cnt = shortcut.size();  // 记录增加的捷径数
        for (auto& x : shortcut) {
            cout << "Added shortcut: " << *(x.second.begin()) << " -> " << *(x.second.end() - 1) << " (weight: " << shortcut_weight[x.first] << ")" << endl;
            outFile << *(x.second.begin()) << " " << *(x.second.end() - 1) << " " << shortcut_weight[x.first] << endl;
        }
        cout << "Added " << shortcuts_cnt << " shortcuts:\n";
        outFile << "Added " << shortcuts_cnt << " shortcuts:\n";
        for (auto& x : shortcut) {
            cout << "	";
            outFile << "	";
            for (int i = 0; i < x.second.size(); i++) {
                if (i)
                    cout << " -> ";
                cout << x.second[i];
                if (i)
                    outFile << " -> ";
                outFile << x.second[i];
            }
            cout << endl;
            outFile << endl;
        }
        cout << endl;
        outFile << endl;
    }

    // 预处理阶段还是不要使用当前剩余电量，判断当前电量是否可以行驶某路程
    bool isCanDriveThisWay(int distance) {
        int max_distance = car.max_distance * (100 - car.min_power) / 100;
        if (max_distance >= distance) {
            return true;
        }
        return false;
    }
};

//可达充电站连接图
class CH_ChargeStation {

public:
    CH_ChargeStation() {
        // 生成CH
        m = 0;
        G = CH("2000.txt");
        // 预处理chargeStations
        completeChargeStations();
        // 预处理isCanNocharge
        completeIs_can_no_charge();
        // 预处理nodeToStation，stationToStaion，nodeAroundStation，stationAroundNode
        completeNodeToStation();
        // 预处理stationToNode_shortcuts, stationToNode_shortcut_weight,stationToNode
        completeStationToNode();
        // 预处理stationToStation, stationToStation_shortcuts, stationToStation_shortcut_weight
        completeStationToStaion();
        // 生成输入文件
        generateInputFile();
        // 生成CH_ChargeStation
        G_ChargeStation = CH("G_ChargeStation_input.txt");
        // 预处理nodeToNode_in_G_ChargeStation, nodeToNode_in_G_ChargeStation_shortcuts, nodeToNode_in_G_ChargeStation_shortcut_weight
        completeNodeToNode_in_G_ChargeStation();

    }

    CH G; // 原图的CH
    CH G_ChargeStation; // 构建起终点，中途节点皆为充电站的压缩图
    int m; // 边数
    unordered_set<int> charge_stations; // 充电站集
    vector<vector<int>> is_can_no_charge; // 路程中是否不需要充电 -1 : 断路 -2 :可达但要充电  路程: 可达且不用充电

    //unordered_map<string, vector<int>> nodeToStation_shortcuts; // 保存预处理中普通节点到充电站的可达路径(未压缩)
    unordered_map<string, int> nodeToStation_shortcut_weight; // 保存预处理中普通节点到充电站的可达路径的权重
    unordered_map<int, vector<int>> nodeToStation; // 保存普通节点周围的可达充电站 -- 正向(node --> station), key -- node

    //unordered_map<string, vector<int>> stationToNode_shortcuts; // 保存预处理中充电站到普通节点的可达路径(未压缩)
    unordered_map<string, int> stationToNode_shortcut_weight; // 保存预处理中充电站到普通节点的可达路径的权重
    unordered_map<int, vector<int>> stationToNode; // 保存普通节点周围的可达充电站 -- 反向(node <-- station), key -- node

    unordered_map<string, vector<int>> stationToStation_shortcuts; // 保存预处理中充电站到充电站的可达路径(未压缩)
    unordered_map<string, int> stationToStation_shortcut_weight; // 保存预处理中充电站到充电站的可达路径的权重
    unordered_map<int, vector<int>> stationToStation; // 保存充电站周围的可达充电站

    //unordered_map<string, vector<int>> nodeToNode_in_G_ChargeStation_shortcuts; // 保存G_ChargeStation图中节点到节点的路径(未压缩)
    unordered_map<string, int> nodeToNode_in_G_ChargeStation_shortcut_weight; // 保存G_ChargeStation图中节点到节点路径权重
    unordered_map<int, vector<int>> nodeToNode_in_G_ChargeStation; // 保存G_ChargeStation图中节点到节点

    // 预处理chargeStations
    void completeChargeStations() {
        cout << "completeChargeStations begin" << endl;
        for (int i = 0, I = G.stations.size(); i < I; i++) {
            charge_stations.insert(G.stations[i]);
        }
        cout << "completeChargeStations end" << endl;
        return;
    }

    // 预处理isCanNocharge
    void completeIs_can_no_charge() {
        cout << "completeIs_can_no_charge begin" << endl;
        is_can_no_charge.assign(G.n + 1, vector<int>(G.n + 1, -1));
        for (int i = 1; i <= G.n; i++) {
            for (int j = 1; j <= G.n; j++) {
                if (i == j)continue;
                int weight = G.QueryWithoutPath(i, j);
                if (weight == -1) {
                    is_can_no_charge[i][j] = -1;
                }
                else if (G.isCanDriveThisWay(weight)) {
                    is_can_no_charge[i][j] = weight;
                }
                else {
                    is_can_no_charge[i][j] = -2;
                }
            }
        }
        cout << "completeIs_can_no_charge end" << endl;
        return;
    }

    // 预处理nodeToStation,nodeToStation_shortcuts,nodeToStation_shortcut_weight
    void completeNodeToStation() {
        cout << "completeNodeToStation begin" << endl;
        for (int i = 1; i <= G.n; i++) {
            // 判断是不是充电站
            if (charge_stations.find(i) != charge_stations.end()) continue;
            for (int j = 0, J = G.stations.size(); j < J; j++) {
                int weight = G.QueryWithoutPath(i, G.stations[j]);
                if (weight == -1) continue;
                // 判断在最大行驶里程（考虑心理阈值）可达
                if (G.isCanDriveThisWay(weight)) {
                    nodeToStation[i].push_back(G.stations[j]);
                    string str_node = to_string(i);
                    string str_station = to_string(G.stations[j]);
                    string node_station = str_node + "?" + str_station;
                    nodeToStation_shortcut_weight[node_station] = weight;
                }
            }
        }
        cout << "completeNodeToStation end" << endl;
        return;
    }

    // 预处理stationToNode_shortcuts, stationToNode_shortcut_weight,stationToNode
    void completeStationToNode() {
        cout << "completeStationToNode beign" << endl;
        for (int i = 0, I = G.stations.size(); i < I; i++) {
            for (int j = 1; j <= G.n; j++) {
                // 判断是不是充电站
                if (charge_stations.find(j) != charge_stations.end()) continue;
                int weight = G.QueryWithoutPath(G.stations[i], j);
                if (weight == -1) continue;
                if (G.isCanDriveThisWay(weight)) {
                    stationToNode[j].push_back(G.stations[i]);
                    string str_station = to_string(G.stations[i]);
                    string str_node = to_string(j);
                    string station_node = str_station + "?" + str_node;
                    stationToNode_shortcut_weight[station_node] = weight;
                }
            }
        }
        cout << "completeStationToNode end" << endl;
        return;
    }

    // 预处理stationToStaion, stationToStation_shortcuts, stationToStation_shortcut_weight
    void completeStationToStaion() {
        cout << "completeStationToStaion begin" << endl;
        for (int i = 0, I = G.stations.size(); i < I; i++) {
            for (int j = 0, J = G.stations.size(); j < J; j++) {
                // 判断是不是相同充电站
                if (i == j) continue;
                vector<int> path;
                int weight = G.Query(G.stations[i], G.stations[j], path);
                if (weight == -1) continue;
                if (G.isCanDriveThisWay(weight)) {
                    stationToStation[G.stations[i]].push_back(G.stations[j]);
                    m++;
                    string str_station1 = to_string(G.stations[i]);
                    string str_station2 = to_string(G.stations[j]);
                    string station1_stations2 = str_station1 + "?" + str_station2;
                    stationToStation_shortcuts[station1_stations2] = path;
                    stationToStation_shortcut_weight[station1_stations2] = weight;
                }
            }
        }
        cout << "completeStationToStaion end" << endl;
        return;
    }

    // 生成输入文件(关于G_ChargeStation)
    void generateInputFile() {
        cout << "generateInputFile begin" << endl;
        ofstream outFile("G_ChargeStation_input.txt");
        if (!outFile) {
            cerr << "无法打开文件 G_ChargeStation_input.txt" << endl;
            return;
        }
        // 输入节点数，边数
        outFile << G.n << ' ' << m << endl;
        // 输入边和权值
        for (auto& x : stationToStation_shortcut_weight) {
            int index = x.first.find('?');
            outFile << x.first.substr(0, index) << ' ' << x.first.substr(index + 1) << ' ' << x.second << endl;
        }
        // 输入充电站数量和编号
        outFile << G.stations.size() << endl;
        for (int i = 0, I = G.stations.size(); i < I; i++) {
            outFile << G.stations[i] << endl;
        }
        cout << "generateInputFile endl" << endl;
        return;
    }

    // 预处理nodeToNode_in_G_ChargeStation, nodeToNode_in_G_ChargeStation_shortcuts, nodeToNode_in_G_ChargeStation_shortcut_weight
    void completeNodeToNode_in_G_ChargeStation() {
        cout << "completeNodeToNode_in_G_ChargeStation begin" << endl;
        for (int i = 0, I = G_ChargeStation.stations.size(); i < I; i++) {
            for (int j = 0, J = G_ChargeStation.stations.size(); j < J; j++) {
                if (i == j) continue;
                int weight = G_ChargeStation.QueryWithoutPath(G_ChargeStation.stations[i], G_ChargeStation.stations[j]);
                if (weight == -1)continue;
                nodeToNode_in_G_ChargeStation[G.stations[i]].push_back(G.stations[j]);
                string str_station1 = to_string(G.stations[i]);
                string str_station2 = to_string(G.stations[j]);
                string station1_stations2 = str_station1 + "?" + str_station2;
                nodeToNode_in_G_ChargeStation_shortcut_weight[station1_stations2] = weight;
            }
        }
        // 处理路程只经过一个充电站
        nodeToNode_in_G_ChargeStation_shortcut_weight[""] = 0;
        cout << "completeNodeToNode_in_G_ChargeStation end" << endl;
    }

    // 将充电站到充电站的捷径还原
    void decompressPath(vector<int>& path) {
        for (int i = 1; i < path.size(); i++) {
            string u = to_string(path[i - 1]);
            string v = to_string(path[i]);
            string u_v = u + "?" + v;
            if (stationToStation_shortcuts.find(u_v) != stationToStation_shortcuts.end()) {
                path.insert(path.begin() + i, stationToStation_shortcuts[u_v].begin() + 1, stationToStation_shortcuts[u_v].end() - 1);
                // 更新i,指向原i
                i += (stationToStation_shortcuts[u_v].end() - 1) - (stationToStation_shortcuts[u_v].begin() + 1);
            }
        }
        return;
    }

    // 考虑电量的路径搜索
    int Query(int s, int t, vector<int>& path) {
        if (is_can_no_charge[s][t] == -1) {
            return -1;
        }
        else if (is_can_no_charge[s][t] != -2 && G.car.distanceCanRun() >= is_can_no_charge[s][t]) {
            return G.Query(s, t, path);
        }
        else {
            // 如果s和t都是充电站
            if (charge_stations.find(s) != charge_stations.end() && charge_stations.find(t) != charge_stations.end()) {
                string s_t = to_string(s) + "?" + to_string(t);
                if (nodeToNode_in_G_ChargeStation_shortcut_weight.find(s_t) != nodeToNode_in_G_ChargeStation_shortcut_weight.end()) {
                    G_ChargeStation.Query(s, t, path);
                    decompressPath(path);
                    return nodeToNode_in_G_ChargeStation_shortcut_weight[s_t];
                }
                return -1;
            }
            // 如果t是充电站,s不是
            else if (charge_stations.find(s) == charge_stations.end() && charge_stations.find(t) != charge_stations.end()) {
                // 筛选s能到达的充电站
                int sum_weight = INF;
                int x_node = -1;
                string s_x_ = "", x_t_ = "";
                for (auto& x : nodeToStation[s]) {
                    string s_x = to_string(s) + "?" + to_string(x);
                    int weight_s_x = nodeToStation_shortcut_weight[s_x];
                    // 要考虑起始电量
                    if (weight_s_x > G.car.distanceCanRun())continue;
                    string x_t;
                    // 让所有只经过一个充电站的情况对应为""
                    if (x == t) x_t = "";
                    else x_t = to_string(x) + "?" + to_string(t);
                    int weight_x_t = 0;
                    if (nodeToNode_in_G_ChargeStation_shortcut_weight.find(x_t) != nodeToNode_in_G_ChargeStation_shortcut_weight.end()) {
                        weight_x_t = nodeToNode_in_G_ChargeStation_shortcut_weight[x_t];
                    }
                    else continue;
                    if (sum_weight > weight_s_x + weight_x_t) {
                        sum_weight = weight_s_x + weight_x_t;
                        s_x_ = s_x;
                        x_t_ = x_t;
                        x_node = x;
                    }
                }
                if (sum_weight != INF) {
                    // 将两段路径拼接
                    if (x_t_ == "") {
                        G.Query(s, t, path);
                    }
                    else {
                        G.Query(s, x_node, path);
                        vector<int> path1;
                        G_ChargeStation.Query(x_node, t, path1);
                        decompressPath(path1);
                        path.insert(path.end(), path1.begin() + 1, path1.end());
                    }
                    return sum_weight;
                }
                return -1;
            }
            // 如果s是充电站,t不是
            else if (charge_stations.find(s) != charge_stations.end() && charge_stations.find(t) == charge_stations.end()) {
                // 筛选t能到达的充电站
                int sum_weight = INF;
                int x_node = -1;
                string s_x_ = "", x_t_ = "";
                for (auto& x : stationToNode[t]) {
                    string x_t = to_string(x) + "?" + to_string(t);
                    int weight_x_t = stationToNode_shortcut_weight[x_t];
                    string s_x;
                    if (s == x) s_x = "";
                    else s_x = to_string(s) + "?" + to_string(x);
                    int weight_s_x = 0;
                    if (nodeToNode_in_G_ChargeStation_shortcut_weight.find(s_x) != nodeToNode_in_G_ChargeStation_shortcut_weight.end()) {
                        weight_s_x = nodeToNode_in_G_ChargeStation_shortcut_weight[s_x];
                    }
                    else continue;
                    if (sum_weight > weight_s_x + weight_x_t) {
                        sum_weight = weight_s_x + weight_x_t;
                        s_x_ = s_x;
                        x_t_ = x_t;
                        x_node = x;
                    }
                }
                if (sum_weight != INF) {
                    // 将两段路径拼接
                    if (s_x_ == "") {
                        G.Query(s, t, path);
                    }
                    else {
                        G_ChargeStation.Query(s, x_node, path);
                        decompressPath(path);
                        vector<int> path1;
                        G.Query(x_node, t, path1);
                        path.insert(path.end(), path1.begin() + 1, path1.end());
                    }
                    return sum_weight;
                }
                return -1;
            }
            // 如果s和t都不是充电站
            else {
                int sum_weight = INF;
                string s_x_ = "", x_y_ = "", y_t_ = "";
                int x_node = -1, y_node = -1;
                for (auto& x : nodeToStation[s]) {
                    // 确定充电站x
                    string s_x = to_string(s) + "?" + to_string(x);
                    int weight_s_x = nodeToStation_shortcut_weight[s_x];
                    if (weight_s_x > G.car.distanceCanRun()) continue;
                    for (auto& y : stationToNode[t]) {
                        // 确定充电站y
                        string y_t = to_string(y) + "?" + to_string(t);
                        int weight_y_t = stationToNode_shortcut_weight[y_t];
                        string x_y;
                        if (x == y) x_y = "";
                        else x_y = to_string(x) + "?" + to_string(y);
                        int weight_x_y = 0;
                        if (nodeToNode_in_G_ChargeStation_shortcut_weight.find(x_y) != nodeToNode_in_G_ChargeStation_shortcut_weight.end()) {
                            weight_x_y = nodeToNode_in_G_ChargeStation_shortcut_weight[x_y];
                        }
                        else continue;
                        if (sum_weight > weight_s_x + weight_x_y + weight_y_t) {
                            sum_weight = weight_s_x + weight_x_y + weight_y_t;
                            s_x_ = s_x;
                            x_y_ = x_y;
                            y_t_ = y_t;
                            x_node = x;
                            y_node = y;
                        }
                    }
                }
                if (sum_weight != INF) {
                    // 将三段路径拼接
                    if (x_y_ == "") {
                        G.Query(s, x_node, path);
                        vector<int> path1;
                        G.Query(x_node, t, path1);
                        path.insert(path.end(), path1.begin() + 1, path1.end());
                    }
                    else {
                        G.Query(s, x_node, path);
                        vector<int> path1;
                        G_ChargeStation.Query(x_node, y_node, path1);
                        decompressPath(path1);
                        path.insert(path.end(), path1.begin() + 1, path1.end());
                        path1.clear();
                        G.Query(y_node, t, path1);
                        path.insert(path.end(), path1.begin() + 1, path1.end());
                    }
                    return sum_weight;
                }
                return -1;
            }
        }
    }
};



int main() {
    ios::sync_with_stdio(0);  // 加速输入输出流
    int T = clock();
    CH_ChargeStation CC;
    // // 创建一个ofstream对象，并打开一个名为"output.txt"的文件
    // std::ofstream outFile("output.txt");
    // 检查文件是否成功打开
    if (!outFile) {
        std::cerr << "无法打开文件 output.txt" << std::endl;
        return 1;
    }

    // 显示捷径
    CC.G.showcaseShortcut(outFile);
    CC.G_ChargeStation.showcaseShortcut(outFile);

    cout << "Preprocessing time: " << 1.0 * (clock() - T) / CLOCKS_PER_SEC << "s\n"
        << endl;
    outFile << "Preprocessing time: " << 1.0 * (clock() - T) / CLOCKS_PER_SEC << "s\n"
        << endl;

    int q, s, t;
    double tot_time = 0, query_time;
    queries >> q;
    for (int i = 0; i < q; ++i) {
        queries >> s >> t;
        T = clock();

        vector<int> path;
        int dis = CC.Query(s, t, path);
        cout << "Shortest path distance from " << s << " to " << t << " : " << dis << endl;
        cout << "	";
        for (int i = 0; i < path.size(); i++) {
            if (i)
                cout << " -> ";
            cout << path[i];
        }
        cout << endl;

        outFile << "Shortest path distance from " << s << " to " << t << " : " << dis << endl;
        outFile << "	";
        for (int i = 0; i < path.size(); i++) {
            if (i)
                outFile << " -> ";
            outFile << path[i];
        }
        outFile << endl;
        query_time = 1.0 * (clock() - T) / CLOCKS_PER_SEC;
        outFile << "Time: " << query_time << "s\n\n";
        cout << "Time: " << query_time << "s\n\n";
        tot_time += query_time;
    }
    outFile << "\nAverage query time: " << tot_time / q << "s\n";
    outFile.close();
    cout << "\nAverage query time: " << tot_time / q << "s\n";
    cout << "Press Enter to terminate...";
    cin.ignore();  // 暂停程序
    string term;
    getline(cin, term);
    return 0;
}


