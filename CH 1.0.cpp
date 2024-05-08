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
typedef pair<ll, ll> Node;                                                // 结点: (结点编号, 距离)
typedef vector<vector<Node>> Graph;                                       // 图: 邻接表
typedef priority_queue<Node, vector<Node>, greater<Node>> DijkstraQueue;  // 最小堆

const ll INF = 1e15 + 10;  // 无穷大

// ifstream graph("NY_graph.txt");  // 读取图
// ifstream queries("Queries.txt"); // 读取查询
ifstream graph("test1.txt");
ifstream queries("query2.txt");

// 创建一个ofstream对象，并打开一个名为"output.txt"的文件
std::ofstream outFile("output.txt");

class CH {
   private:
    int n, m, s, t, order;                       // n: 结点数, m: 边数, s: 起点, t: 终点, order: 结点顺序
    vector<Graph> G, G_CH;                       // G[0] 表示正向边(u 为边的起点), G[1] 表示反向边(u 为边的终点); G_CH 是包含捷径的叠加图
    vector<vector<ll>> dist;                     // 用于存储从每个结点到所有其他结点的最短距离
    vector<DijkstraQueue> pq;                    // 用于存储待处理的结点; 有两个优先队列分别对应正向边pq[0]和反向边pq[1]
    DijkstraQueue imp_pq;                        // 重要性优先队列
    vector<bool> contracted;                     // 判断结点是否已经收缩
    vector<int> imp;                             // 存储结点重要性, 用于确定结点收缩顺序
    vector<int> level;                           // 记录每个结点的层级
    vector<int> contr_neighbours;                // 记录每个结点的收缩邻居数
    unordered_map<string, vector<ll>> shortcut;  // 记录捷径的原路径
    vector<vector<ll>> fa;                       // 记录节点的父节点, fa[0]:正向边父节点, fa[1]:反向边父节点

    // 读取图(读入有向图; 如果要处理无向图则需要将每条边读入两次)
    void read() {
        graph >> n >> m;
        G.assign(2, Graph(n + 1, vector<Node>()));  // 初始化图
        int u, v, w;                                // u: 边的起点, v: 边的终点, w: 边的权重
        for (int i = 0; i < m; ++i) {
            graph >> u >> v >> w;
            // u++, v++;    // 结点编号从 1 开始
            if (u == v)  // 排除自环
                continue;
            Connect(G[0][u], v, w);  // 正向边, 表示从结点 u 出发的正向边
            Connect(G[1][v], u, w);  // 反向边, 表示指向结点 v 的反向边
            Connect(G[0][v], u, w);  // 无向图需要将每条边读入两次
            Connect(G[1][u], v, w);  // 无向图需要将每条边读入两次
        }
    }

    // 预处理
    void preprocess() {
        SetOrder();   // 设置结点顺序
        BuildG_CH();  // 构建 CH 图
    }

    // 连接节点
    void Connect(vector<Node>& E, int v, ll w) {
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
    void addShortcut(int v, int mid, int u) {
        // 生成键
        string str_v = to_string(v);
        string str_mid = to_string(mid);
        string str_u = to_string(u);
        string v_mid = str_v + str_mid;
        string mid_u = str_mid + str_u;
        string v_u = str_v + str_u;
        // 判断v-mid-u是否包含捷径
        vector<ll> vec;
        if (shortcut.find(v_mid) != shortcut.end()) {
            vec.insert(vec.end(), shortcut[v_mid].begin(), shortcut[v_mid].end());
        } else {
            vec.insert(vec.end(), {v, mid});
        }
        if (shortcut.find(mid_u) != shortcut.end()) {
            vec.insert(vec.end(), shortcut[mid_u].begin() + 1, shortcut[mid_u].end());
        } else {
            vec.insert(vec.end(), {u});
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
            } else {
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
        ll w, mx = GetMaxEdge(x);
        set<pair<int, ll>> out_edges;
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
    ll GetMaxEdge(int x) {
        ll ret = 0;
        for (auto& p1 : G[1][x]) {
            for (auto& p2 : G[0][x]) {
                if (p1.fs != p2.fs && !contracted[p1.fs] && !contracted[p2.fs])
                    ret = max(ret, p1.sc + p2.sc);
            }
        }
        return ret;
    }

    // 检查见证 --        u-x-out_edges
    int Check_Witness(int u, int x, ll w, ll mx, set<pair<int, ll>>& out_edges, bool type) {
        int a, b;                // a: 当前结点, b: 邻接结点
        ll curr_dist, new_dist;  // curr_dist: 当前距离, new_dist: 新距离
        DijkstraQueue D_pq;
        unordered_map<int, ll> D_dist;
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
        ll new_w;
        for (auto& p : out_edges) {
            v = p.fs, new_w = w + p.sc;
            // 没有见证路径/见证路径比要生成的捷径要大
            if (D_dist.find(v) == D_dist.end() || D_dist.find(v)->sc > new_w) {
                ++ret;
                if (!type && u != v) {
                    Connect(G[0][u], v, new_w);
                    addShortcut(u, x, v);
                    Connect(G[1][v], u, new_w);
                    cout << "Added shortcut: " << u << " -> " << v << " (weight: " << new_w << ")" << endl;
                    outFile << u << " " << v << " " << new_w << endl;
                }
            }
        }
        return ret;
    }

    // 构建 CH 图
    void BuildG_CH() {
        G_CH.assign(2, Graph(n + 1, vector<Node>()));
        int v;
        ll w;
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
    void getNodeInPath(vector<ll>& path, int mid) {
        for (int i = 0; i < 2; i++) {
            int x = mid;
            while (fa[i][x] != x) {
                x = fa[i][x];
                if (!i) {
                    path.insert(path.begin(), x);
                } else {
                    path.push_back(x);
                }
            }
            if (!i)
                path.push_back(mid);
        }
        for (int i = 1; i < path.size(); i++) {
            string u = to_string(path[i - 1]);
            string v = to_string(path[i]);
            string u_v = u + v;
            if (shortcut.find(u_v) != shortcut.end()) {
                path.insert(path.begin() + i, shortcut[u_v].begin() + 1, shortcut[u_v].end() - 1);
                // 更新i,指向原i
                i += (shortcut[u_v].end() - 1) - (shortcut[u_v].begin() + 1);
            }
        }
    }

    // 获取最短路径
    ll GetDistance(vector<ll>& path) {
        dist[0][s] = dist[1][t] = 0;  // s 为起点, t 为终点
        ll SP = INF;                  // 最短路径 shortest path
        pq[0].push(mp(0, s));
        pq[1].push(mp(0, t));
        Node front;
        int curr_node;
        ll curr_dist;
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

    // 松弛操作
    void RelaxNodeEdges(int u, int g) {  // u: 当前结点, g: 当前图 (0表示正向边 1表示反向边)
        int v;
        ll w;
        for (auto& p : G_CH[g][u]) {
            v = p.fs, w = p.sc;
            if (dist[g][v] > dist[g][u] + w) {
                dist[g][v] = dist[g][u] + w;
                pq[g].push(mp(dist[g][v], v));
                fa[g][v] = u;
            }
        }
    }

   public:
    // CH 构造函数
    CH() {
        cout << "Preprocessing...\n\n";
        read();
        preprocess();
        cout << "\nPreprocessing done!\n\n";
    }

    // 查询最短路径
    ll Query(int _s, int _t, vector<ll>& path) {  // path:最短路径
        s = _s, t = _t;                           // 设置起点和终点
        dist.assign(2, vector<ll>(n + 1, INF));   // 初始化距离为无穷大
        // 初始化父节点为它本身
        fa.assign(2, vector<ll>(n + 1, 0));
        for (int i = 0; i < n + 1; i++) {
            fa[0][i] = i;
            fa[1][i] = i;
        }
        pq.assign(2, DijkstraQueue());  // 初始化优先队列
        return GetDistance(path);       // 获取最短路径
    }

    // 显示捷径
    void showcaseShortcut(ofstream& outFile) {
        long long shortcuts_cnt = shortcut.size();  // 记录增加的捷径数
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
};

int main() {
    ios::sync_with_stdio(0);  // 加速输入输出流
    int T = clock();
    CH G;
    // // 创建一个ofstream对象，并打开一个名为"output.txt"的文件
    // std::ofstream outFile("output.txt");
    // 检查文件是否成功打开
    if (!outFile) {
        std::cerr << "无法打开文件 output.txt" << std::endl;
        return 1;
    }

    // 显示捷径
    G.showcaseShortcut(outFile);

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
        vector<ll> path;
        cout << "Shortest path distance from " << s << " to " << t << " : " << G.Query(s, t, path) << endl;
        cout << "	";
        for (int i = 0; i < path.size(); i++) {
            if (i)
                cout << " -> ";
            cout << path[i];
        }
        cout << endl;
        path.clear();

        outFile << "Shortest path distance from " << s << " to " << t << " : " << G.Query(s, t, path) << endl;
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