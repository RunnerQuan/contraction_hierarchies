#include <bits/stdc++.h>

#define pb push_back
#define mp make_pair
#define fs first
#define sc second

using namespace std;

typedef long long ll;                                                     // 长整型
typedef pair<ll, ll> Node;                                                // 结点: (结点编号, 距离)
typedef vector<vector<Node>> Graph;                                       // 图: 邻接表
typedef priority_queue<Node, vector<Node>, greater<Node>> DijkstraQueue;  // 最小堆
typedef struct cars {                                                     // 存储汽车的相关信息（起始电量、心理阈值、最大续航里程...）
    double initial_power;                                                 // 起始百分比电量%
    double min_power;                                                     // 心理百分比电量阈值%
    double max_distance;                                                  // 汽车最大续航里程km
    double battery_capacity;                                              // 汽车电池最大容量kW·h
} bev;

const ll INF = 1e15 + 10;  // 无穷大

// ifstream graph("NY_graph.txt");  // 读取图
// ifstream queries("Queries.txt"); // 读取查询
ifstream graph("test3.txt");
ifstream queries("query3.txt");

// 创建一个ofstream对象，并打开一个名为"output.txt"的文件
std::ofstream outFile("output11.txt");

class CH {
   private:
    int n, m, s, t, order;                        // n: 结点数, m: 边数, s: 起点, t: 终点, order: 结点顺序
    vector<Graph> G, G_CH;                        // G[0] 表示正向边(u 为边的起点), G[1] 表示反向边(u 为边的终点); G_CH 是包含捷径的叠加图
    vector<vector<ll>> dist;                      // 用于存储从每个结点到所有其他结点的最短距离
    vector<DijkstraQueue> pq;                     // 用于存储待处理的结点; 有两个优先队列分别对应正向边pq[0]和反向边pq[1]
    DijkstraQueue imp_pq;                         // 重要性优先队列
    vector<bool> contracted;                      // 判断结点是否已经收缩
    vector<int> imp;                              // 存储结点重要性, 用于确定结点收缩顺序
    vector<int> level;                            // 记录每个结点的层级
    vector<int> contr_neighbours;                 // 记录每个结点的收缩邻居数
    unordered_map<string, vector<int>> shortcut;  // 记录捷径的原路径
    unordered_map<string, ll> shortcut_weight;    // 记录捷径的权重
    vector<vector<int>> fa;                       // 记录节点的父节点, fa[0]:正向边父节点, fa[1]:反向边父节点
    vector<vector<pair<double, double>>> power;   // 记录节点的到达时电量和离开时电量
    vector<int> stations;                         // 记录充电站的节点
    bev car;                                      // 记录汽车的信息

    // 读取图(读入有向图; 如果要处理无向图则需要将每条边读入两次)
    void read() {
        graph >> n >> m;
        G.assign(2, Graph(n + 1, vector<Node>()));  // 初始化图
        int u, v, w;                                // u: 边的起点, v: 边的终点, w: 边的权重
        for (int i = 0; i < m; ++i) {
            graph >> u >> v >> w;
            if (u == v)  // 排除自环
                continue;
            Connect(G[0][u], v, w);  // 正向边, 表示从结点 u 出发的正向边
            Connect(G[1][v], u, w);  // 反向边, 表示指向结点 v 的反向边
            Connect(G[0][v], u, w);  // 无向图需要将每条边读入两次
            Connect(G[1][u], v, w);  // 无向图需要将每条边读入两次
        }
        int size;
        graph >> size;
        stations.assign(n + 1, false);
        for (int i = 0; i < size; i++) {
            int x;
            graph >> x;
            stations[x] = true;
        }
        vector<pair<double, double>> tem;
        tem.assign(n + 1, mp(-1, -1));
        power.assign(2, tem);
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
    void addShortcut(int v, int mid, int u, ll distance) {
        // 生成键
        string str_v = to_string(v);
        string str_mid = to_string(mid);
        string str_u = to_string(u);
        string v_mid = str_v + str_mid;
        string mid_u = str_mid + str_u;
        string v_u = str_v + str_u;
        // 判断捷径是否已存在/最优
        if (shortcut_weight.find(v_u) != shortcut_weight.end()) {
            if (shortcut_weight[v_u] <= distance)
                return;
            else
                shortcut[v_u].clear();
        } else {
            shortcut_weight[v_u] = distance;
        }
        // 判断v-mid-u是否包含捷径
        vector<int> vec;
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
                    addShortcut(u, x, v, new_w);
                    Connect(G[1][v], u, new_w);
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
    void getNodeInPath(vector<int>& path, int mid) {
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

    // 在考虑电量的情况下判断途径节点x是否合理
    bool judge_node(int x) {
        if (x == s || x == t)
            return true;
        double tem = (100.0 - power[0][x].first) + (power[1][x].first - car.min_power);
        if (tem <= (100.0 - car.min_power))
            return true;
        else
            return false;
    }

    // 获取最短路径
    ll GetDistance(vector<int>& path) {
        dist[0][s] = dist[1][t] = 0;  // s 为起点, t 为终点
        ll SP = INF;                  // 最短路径 shortest path
        pq[0].push(mp(0, s));
        pq[1].push(mp(0, t));
        car.initial_power = 60.0;  // 起始电量
        car.min_power = 20.0;      // 心理阈值
        car.max_distance = 500.0;  // 汽车最大续航里程
        power[0][s].first = power[0][s].second = car.initial_power;
        power[1][t].first = power[1][t].second = car.min_power;
        if (stations[s])
            power[0][s].second = 100.0;  // 当前节点是充电站 则离开此位置电量为100%
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
                if (SP > dist[0][curr_node] + dist[1][curr_node] && judge_node(curr_node)) {
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
                if (SP > dist[0][curr_node] + dist[1][curr_node] && judge_node(curr_node)) {
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

    // 返回两个相邻节点x、y在原图的距离
    double getDis(int x, int y, int g) {
        if (x == y)
            return 0.0;
        for (auto& p : G[g][x]) {
            if (p.first == y)
                return p.second;
        }
        return INF;
    }

    // 返回汽车从x到y的耗能,x与y在原图相邻
    double power_consume(int x, int y, double distance) {
        return distance / car.max_distance * 100.0;
    }

    // 判断在考虑电量的情况下，捷径u->v是否可行
    bool judge_shortcut(int u, int v, int g) {  // 捷径起点、终点、正反向
        for (auto& p : shortcut) {
            double distance = 0;
            double pc = 0;
            if (*(p.second.end() - 1) == v && *(p.second.begin()) == u) {
                int last_node = *(p.second.begin());
                for (auto q = p.second.begin(), qq = q + 1; qq != p.second.end(); q++, qq++) {
                    double temdis = getDis(*q, *qq, g);
                    if (temdis == INF)
                        return false;
                    distance += temdis;
                    pc += power_consume(*q, *qq, temdis);
                    if (stations[*qq]) {
                        double temp = power[g][last_node].second - pc * pow(-1, g);
                        if (temp >= car.min_power && temp <= 100.0) {
                            power[g][*qq].first = temp;
                            power[g][*qq].second = car.min_power * g + (1 - g) * 100.0;
                        } else {
                            return false;
                        }
                        last_node = *qq;
                        distance = 0;
                        pc = 0;
                    }
                }
                if (!stations[v]) {
                    power[g][v].first = power[g][last_node].second - pc * pow(-1, g);
                    power[g][v].second = power[g][v].first;
                }
                return true;
            }
        }
        double tem = power[g][u].second - power_consume(u, v, getDis(u, v, g)) * pow(-1, g);
        if (tem >= car.min_power && tem <= 100.0) {
            power[g][v].first = tem;
            if (stations[v])
                power[g][v].second = car.min_power * g + (1 - g) * 100.0;
            else
                power[g][v].second = power[g][v].first;

            return true;
        } else {
            return false;
        }
    }

    // 松弛操作
    void RelaxNodeEdges(int u, int g) {  // u: 当前结点, g: 当前图 (0表示正向边 1表示反向边)
        int v;
        ll w;
        // cout<<u<<" A "<<g<<" "<<power[0][u].first<<" "<<power[0][u].second<<" "<<power[1][u].first<<" "<<power[1][u].second<<endl;
        if (power[g][u].first < 0 || power[g][u].second < 0)
            return;
        for (auto& p : G_CH[g][u]) {
            v = p.fs, w = p.sc;
            // cout<<v<<" B "<<endl;
            if (dist[g][v] > dist[g][u] + w) {
                if (judge_shortcut(u, v, g)) {
                    // cout<<v<<" C "<<power[g][v].first<<" "<<power[g][v].second<<endl;
                    dist[g][v] = dist[g][u] + w;
                    pq[g].push(mp(dist[g][v], v));
                    fa[g][v] = u;
                }
            }
        }
    }

   public:
    // CH 构造函数
    CH() {
        cout << "Preprocessing...\n\n";
        read();
        cout << "read";
        preprocess();
        cout << "\nPreprocessing done!\n\n";
        // for (int i = 1; i < n + 1; i++) {
        //     cout << i << endl;
        //     for (auto& p : G_CH[0][i]) {
        //         cout << p.first << " " << p.second << " R0 ";
        //     }
        //     cout << endl;
        //     for (auto& p : G_CH[1][i]) {
        //         cout << p.first << " " << p.second << " R1 ";
        //     }
        //     cout << endl;
        // }
    }

    // 查询最短路径
    ll Query(int _s, int _t, vector<int>& path) {  // path:最短路径
        s = _s, t = _t;                            // 设置起点和终点
        dist.assign(2, vector<ll>(n + 1, INF));    // 初始化距离为无穷大
        // 初始化父节点为它本身
        fa.assign(2, vector<int>(n + 1, 0));
        vector<pair<double, double>> tem;
        tem.assign(n + 1, mp(-1, -1));
        power.assign(2, tem);
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
};

int main() {
    ios::sync_with_stdio(0);  // 加速输入输出流
    int T = clock();
    CH G;
    cout << "finish1";
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
        vector<int> path;
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
