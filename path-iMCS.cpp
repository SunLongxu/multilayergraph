#include <bits/stdc++.h>

#include <random>

using namespace std;

typedef long long ll;
typedef unsigned long long ull;
#pragma GCC optimize(3)
#define debug(x...)             \
    do {                      \
        cout << #x << " -> ";\
        err(x);               \
    } while (0)

void err() {
    cout << endl;
}

template<class T, class... Ts>
void err(const T &arg, const Ts &... args) {
    cout << arg << ' ';
    err(args...);
}

const ll LINF = 0x3f3f3f3f3f3f3f3f;
const int INF = 0x3f3f3f3f;//2147483647;
const ll MOD[2] = {1000000007, 998244353};
const ll BASE[2] = {131, 13331};
const double pi = acos(-1.0);

const int N = 2e6 + 5, M = 1000 + 5;
const ll mod = 31011;

int n, m, layers;

int nd_tot = 0;
map<pair<int, int>, int> mp;

int trans(pair<int, int> x, vector<pair<int, int>> &mpp) {
    auto [id, lay] = x;
    if (!mp.count({id, lay})) {
        mp[{id, lay}] = ++nd_tot;
        mpp[nd_tot] = {id, lay};
    }
    return mp[{id, lay}];
}

unordered_map<int, int> coreDecomposition(int id1, set<int> &layer1, int id2, set<int> &layer2, vector<set<int>> &G,
                                          vector<pair<int, int>> &mpp) {
    vector<int> sets;
    for (auto i: layer1)sets.emplace_back(i);
    if (id1 != id2)for (auto i: layer2)sets.emplace_back(i);
    unordered_map<int, int> deg;
    for (auto i: sets) {
        auto curL = mpp[i].second;
        deg[i] = 0;
        for (auto v: G[i]) {
            auto adjL = mpp[v].second;
            if (curL == id1 && adjL == id2) {
                deg[i]++;
            } else if (curL == id2 && adjL == id1) {
                deg[i]++;
            }
        }
    }
    unordered_map<int, int> res;
    int max_deg = 0;
    for (auto [cur, z]: deg)max_deg = max(max_deg, z);
    vector<vector<int>> vec_deg(max_deg + 1);
    for (auto [cur, z]: deg) {
        vec_deg[z].emplace_back(cur);
    }
    unordered_map<int, int> vis;
    for (int k = 0; k <= max_deg; k++) {
        for (int i = 0; i < (int) vec_deg[k].size(); i++) {
            int cur = vec_deg[k][i];
            if (vis.count(cur))continue;
            res[cur] = k;
            vis[cur] = true;
            int curL = mpp[cur].second;
            for (auto v: G[cur]) {
                int adjL = mpp[v].second;
                if (curL == id1 && adjL == id2 && !vis.count(v)) {
                    deg[v]--;
                    vec_deg[deg[v]].emplace_back(v);
                } else if (curL == id2 && adjL == id1 && !vis.count(v)) {
                    deg[v]--;
                    vec_deg[deg[v]].emplace_back(v);
                }
            }
        }
    }
    return res;
}

unordered_map<int, bool> split_vis;
int component_tot = 0;

vector<pair<int, set<int>>> split_layer(set<int> &layer_sets, vector<set<int>> &G) {
    vector<pair<int, set<int>>> components;
    for (auto i: layer_sets) {
        if (split_vis[i])continue;
        split_vis[i] = true;
        set<int> tmp;
        tmp.insert(i);
        queue<int> q;
        q.push(i);
        while (!q.empty()) {
            int cur = q.front();
            q.pop();
            for (auto v: G[cur]) {
                if (layer_sets.find(v) != layer_sets.end()) {
                    if (split_vis[v])continue;
                    split_vis[v] = true;
                    tmp.insert(v);
                    q.push(v);
                }
            }
        }
        components.emplace_back(++component_tot, tmp);
    }
    return components;
}


void DFS(int cur, set<int> &sets, vector<set<int>> &G, set<int> &alive, unordered_map<int, int> &vis) {
    for (auto v: alive) {
        if (G[cur].find(v) == G[cur].end())continue;
        if (vis[v])continue;
        vis[v] = 1;
        sets.insert(v);
        DFS(v, sets, G, alive, vis);
    }
}

pair<set<int>, set<int>>
cores(int k, int d, set<int> &components1, set<int> &components2, vector<set<int>> &G) {
    map<int, pair<int, int>> D1;// first -> local layer , second -> adjacent layer
    map<int, pair<int, int>> D2;
    set<pair<int, int>> setk;// k-core , both layer 1&2
    set<pair<int, int>> setd;// d-core , between layer 1&2
    for (auto u: components1) {
        int d1 = 0, d2 = 0;
        if (components1.size() + components2.size() < G[u].size()) {
            for (auto v: components1) {
                if (G[u].find(v) != G[u].end())d1++;
            }
            for (auto v: components2) {
                if (G[u].find(v) != G[u].end())d2++;
            }
        } else {
            for (auto id: G[u]) {
                if (components1.find(id) != components1.end()) {
                    d1++;
                } else if (components2.find(id) != components2.end()) {
                    d2++;
                }
            }
        }
        D1[u] = {d1, d2};
        setk.insert({d1, u});
        setd.insert({d2, u});
    }
    for (auto u: components2) {
        int d1 = 0, d2 = 0;
        if (components1.size() + components2.size() < G[u].size()) {
            for (auto v: components2) {
                if (G[u].find(v) != G[u].end())d1++;
            }
            for (auto v: components1) {
                if (G[u].find(v) != G[u].end())d2++;
            }
        } else {
            for (auto id: G[u]) {
                if (components2.find(id) != components2.end()) {
                    d1++;
                } else if (components1.find(id) != components1.end()) {
                    d2++;
                }
            }
        }
        D2[u] = {d1, d2};
        setk.insert({d1, u});
        setd.insert({d2, u});
    }

    while (!setk.empty() && !setd.empty()) {
        if (((*setk.rbegin()).first < k) || ((*setd.rbegin()).first < d))
            return {{},
                    {}};
        auto [dk, cur1] = *setk.begin();
//        auto [u, layu] = mpp[cur1];
        if (dk < k) {
            if (components1.find(cur1) != components1.end()) {
                auto [d1, d2] = D1[cur1];
                setk.erase({d1, cur1});
                setd.erase({d2, cur1});
                D1.erase(cur1);
            } else if (components2.find(cur1) != components2.end()) {
                auto [d1, d2] = D2[cur1];
                setk.erase({d1, cur1});
                setd.erase({d2, cur1});
                D2.erase(cur1);
            }
            if (components1.size() + components2.size() < G[cur1].size()) {
                for (auto id: components1) {
                    if (G[cur1].find(id) == G[cur1].end()) continue;
                    if (D1.count(id)) {
                        if (components1.find(cur1) != components1.end()) {
                            setk.erase({D1[id].first, id});
                            D1[id].first--;
                            setk.insert({D1[id].first, id});
                        } else {
                            setd.erase({D1[id].second, id});
                            D1[id].second--;
                            setd.insert({D1[id].second, id});
                        }
                    }
                }
                for (auto id: components2) {
                    if (G[cur1].find(id) == G[cur1].end())continue;
                    if (D2.count(id)) {
                        if (components2.find(cur1) != components2.end()) {
                            setk.erase({D2[id].first, id});
                            D2[id].first--;
                            setk.insert({D2[id].first, id});
                        } else {
                            setd.erase({D2[id].second, id});
                            D2[id].second--;
                            setd.insert({D2[id].second, id});
                        }
                    }
                }
            } else {
                for (auto id: G[cur1]) {
                    if (D1.count(id)) {
                        if (components1.find(cur1) != components1.end()) {
                            setk.erase({D1[id].first, id});
                            D1[id].first--;
                            setk.insert({D1[id].first, id});
                        } else {
                            setd.erase({D1[id].second, id});
                            D1[id].second--;
                            setd.insert({D1[id].second, id});
                        }
                    }
                    if (D2.count(id)) {
                        if (components2.find(cur1) != components2.end()) {
                            setk.erase({D2[id].first, id});
                            D2[id].first--;
                            setk.insert({D2[id].first, id});
                        } else {
                            setd.erase({D2[id].second, id});
                            D2[id].second--;
                            setd.insert({D2[id].second, id});
                        }
                    }
                }
            }

            continue;
        }
        auto [dd, cur2] = *setd.begin();
        if (dd < d) {
            if (components1.find(cur2) != components1.end()) {
                auto [d1, d2] = D1[cur2];
                setk.erase({d1, cur2});
                setd.erase({d2, cur2});
                D1.erase(cur2);
            } else if (components2.find(cur2) != components2.end()) {
                auto [d1, d2] = D2[cur2];
                setk.erase({d1, cur2});
                setd.erase({d2, cur2});
                D2.erase(cur2);
            }
            if (components1.size() + components2.size() < G[cur2].size()) {
                for (auto id: components1) {
                    if (G[cur2].find(id) == G[cur2].end()) continue;
                    if (D1.count(id)) {
                        if (components1.find(cur2) != components1.end()) {
                            setk.erase({D1[id].first, id});
                            D1[id].first--;
                            setk.insert({D1[id].first, id});
                        } else {
                            setd.erase({D1[id].second, id});
                            D1[id].second--;
                            setd.insert({D1[id].second, id});
                        }
                    }
                }
                for (auto id: components2) {
                    if (G[cur2].find(id) == G[cur2].end())continue;
                    if (D2.count(id)) {
                        if (components2.find(cur2) != components2.end()) {
                            setk.erase({D2[id].first, id});
                            D2[id].first--;
                            setk.insert({D2[id].first, id});
                        } else {
                            setd.erase({D2[id].second, id});
                            D2[id].second--;
                            setd.insert({D2[id].second, id});
                        }
                    }
                }
            } else {
                for (auto id: G[cur2]) {
                    if (D1.count(id)) {
                        if (components1.find(cur2) != components1.end()) {
                            setk.erase({D1[id].first, id});
                            D1[id].first--;
                            setk.insert({D1[id].first, id});
                        } else {
                            setd.erase({D1[id].second, id});
                            D1[id].second--;
                            setd.insert({D1[id].second, id});
                        }
                    }
                    if (D2.count(id)) {
                        if (components2.find(cur2) != components2.end()) {
                            setk.erase({D2[id].first, id});
                            D2[id].first--;
                            setk.insert({D2[id].first, id});
                        } else {
                            setd.erase({D2[id].second, id});
                            D2[id].second--;
                            setd.insert({D2[id].second, id});
                        }
                    }
                }
            }
            continue;
        }
        break;
    }
    set<int> res1, res2;
    if (setk.empty() || setd.empty()) {
        return {res1, res2};
    }
    unordered_map<int, int> s_vis;
    for (auto [dd, cur]: setk) {
        if (components1.find(cur) != components1.end()) {
            res1.insert(cur);
        }
        if (components2.find(cur) != components2.end()) {
            res2.insert(cur);
        }
    }
    vector<set<int>> comp1;
    vector<set<int>> comp2;
    for (auto i: res1) {
        if (s_vis[i])continue;
        set<int> temp;
        temp.insert(i);
        s_vis[i] = true;
        DFS(i, temp, G, res1, s_vis);
        comp1.push_back(temp);
    }
    for (auto i: res2) {
        if (s_vis[i])continue;
        set<int> temp;
        temp.insert(i);
        s_vis[i] = true;
        DFS(i, temp, G, res2, s_vis);
        comp2.push_back(temp);
    }
    if (comp1.size() == 1 && comp2.size() == 1) {
        return {res1, res2};
    }
    for (int i = 0; i < (int) comp1.size(); i++) {
        for (int j = 0; j < (int) comp2.size(); j++) {
            auto [re1, re2] = cores(k, d, comp1[i], comp2[j], G);
            if (re1.empty() || re2.empty())continue;
            return {re1, re2};
        }
    }
    return {{},
            {}};
}

pair<pair<unordered_map<int, int>, unordered_map<int, int>>, int>
find_max_layer(vector<int> &query_comp, vector<int> &belong_layer, map<pair<int, int>, bool> &exist_comp) {
    vector<set<int>> comp_G(component_tot + 1);
    for (auto [a, b]: exist_comp) {
        if (b) {
            auto [comp1, comp2] = a;
            comp_G[comp1].insert(comp2);
            comp_G[comp2].insert(comp1);
        }
    }
    unordered_map<int, int> comp_vis;
    unordered_map<int, int> layer_vis;
    int st_comp = query_comp[0];

    // bfs
    queue<int> q;
    q.push(st_comp), comp_vis[st_comp] = 1, layer_vis[belong_layer[st_comp]] = 1;
    while (!q.empty()) {
        int cur = q.front();
        q.pop();
        for (auto v: comp_G[cur]) {
            if (comp_vis.count(v))continue;
            comp_vis[v] = 1;
            if (!layer_vis.count(belong_layer[v])) {
                layer_vis[belong_layer[v]] = 1;
            }
            q.push(v);
        }
    }
    return {{comp_vis, layer_vis}, layer_vis.size()};
}

#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/hash_policy.hpp>

using namespace __gnu_pbds;
string tmp;

void solve() {
    string ss = tmp + ".txt";
    freopen(ss.c_str(), "r", stdin);

    cin >> n >> m >> layers;
    mp.clear();
    vector<set<int>> G(n * layers + 1);
    nd_tot = 0;
    vector<set<int>> layer_sets(layers + 1);
    vector<pair<int, int>> mpp(n * layers + 1);
    for (int i = 1; i <= m; i++) {
        int u, v, lu, lv;
        cin >> u >> lu >> v >> lv;
        int id1 = trans({u, lu}, mpp), id2 = trans({v, lv}, mpp);
        layer_sets[lu].insert(id1), layer_sets[lv].insert(id2);
        G[id1].insert(id2), G[id2].insert(id1);
    }
    string index_ss = tmp + "_index.txt";
    freopen(index_ss.c_str(), "r", stdin);

    //K-D index init (read)
    vector<vector<tree<pair<int, int>, null_type, less<>, rb_tree_tag, tree_order_statistics_node_update>>> kd_index(
            nd_tot + 1, vector<tree<pair<int, int>, null_type, less<>, rb_tree_tag, tree_order_statistics_node_update>>(
                    layers + 1));

    string ssss = tmp + "_index.txt";
    freopen(ssss.c_str(), "r", stdin);
    int nd_tot_index, layers_index;
    cin >> nd_tot_index >> layers_index;
    for (int i = 1; i <= nd_tot_index; i++) {
        int u, lu;
        cin >> u >> lu;
        auto cur_id = mp[{u, lu}];
        if (cur_id != i) {
            cout << "Bug in index";
            exit(0);
        }
        for (int j = 1; j <= layers; j++) {
            int num;
            cin >> num;
            for (int _ = 1; _ <= num; _++) {
                int k, d;
                cin >> k >> d;
                kd_index[i][j].insert({k, d});
            }
        }
    }

    string query_ss = tmp + "_query.txt";
    freopen(query_ss.c_str(), "r", stdin);

    string query_log = tmp + "_query_log_Alg5_2.txt";
    freopen(query_log.c_str(), "w", stdout);

    int query_time;
    cin >> query_time;
    double sum_query_time = 0;
    double sum_inter_density = 0;
    double sum_intra_density = 0;
    double sum_L = 0;
    for (int _ = 1; _ <= query_time; _++) {
        split_vis.clear();
        component_tot = 0;
        int q;
        cin >> q;
        vector<int> query_sets;
        for (int i = 1; i <= q; i++) {
            int q_node, q_layer;
            cin >> q_node >> q_layer;
            query_sets.push_back(mp[{q_node, q_layer}]);
        }
        int K, D;
        cin >> K >> D;
        // �ҳ����е� k-core components O(m)
        for (int i = 1; i <= nd_tot; i++) {
            auto [cur, cur_layer] = mpp[i];
            //�����i ��ͬ�㲻����k-core, ɾ��
            int kmax = kd_index[i][cur_layer].rbegin()->first;
            if(kmax<K){
            	split_vis[i] = true;
			}
        }
        component_tot = 0;
        vector<vector<pair<int, set<int>>>> layer_component(layers + 1);
        for (int i = 1; i <= layers; i++) {
            layer_component[i] = split_layer(layer_sets[i], G);
        }
        if (component_tot == 0)break;
        vector<set<int>> components(component_tot + 1);
        vector<int> belong_component(nd_tot + 1);
        vector<int> belong_layer(component_tot + 1);
        for (int i = 1; i <= layers; i++) {
            for (auto [id, sets]: layer_component[i]) {
                components[id] = sets;
                belong_layer[id] = i;
                for (auto node: sets) {
                    belong_component[node] = id;
                }
            }
        }
		double qu_st = 1.0 * clock() / CLOCKS_PER_SEC;
        unordered_map<int, int> layer_vis, node_vis, comp_vis;
        queue<int> queue3;
        queue3.push(*query_sets.begin());
		node_vis[*query_sets.begin()] = 1;
        while (!queue3.empty()) {
            int u = queue3.front();
            queue3.pop();
            layer_vis[mpp[u].second] = 1;
            comp_vis[belong_component[u]] = 1;
            for (auto v: G[u]) {
                if (node_vis.count(v))continue;
                if (mpp[v].second == mpp[u].second) { 
                    int kmax = kd_index[v][mpp[v].second].rbegin()->first;
                    if (K <= kmax) {
                        queue3.push(v);
                        node_vis[v] =1;  
                    }
                } else {
                    if (kd_index[v][mpp[u].second].lower_bound({K, D}) == kd_index[v][mpp[u].second].end()) {
                        continue;
                    }
                    auto [k, d] = *kd_index[v][mpp[u].second].lower_bound({K, D});
                    if (K <= k && D <= d) {
                        queue3.push(v);
                        node_vis[v] =1 ;
                    }
                }
            }
        }
        int max_L = (int) layer_vis.size();
        double qu_ed = 1.0 * clock() / CLOCKS_PER_SEC;
        double qu_cost = qu_ed - qu_st;
        sum_query_time += qu_cost;
        cout << "query #" << _ << ":" << endl;
        cout << "cur_cost: " << fixed << setprecision(8) << qu_cost << endl;
        cout << "avg_cost: " << fixed << setprecision(8) << sum_query_time / _ << endl;
        cout << "max_L: " << max_L << endl;
        sum_L += max_L;
        cout << "avg_L: " << fixed << setprecision(8) << sum_L / _ << endl;
        map<int, int> bfs_V;
        map<pair<int, int>, int> bfs_E;
        queue<int> queue2;
        queue2.push(query_sets[0]);
        bfs_V[query_sets[0]] = 1;
        ll inter_E = 0, intra_E = 0;
        while (!queue2.empty()) {
            int cur = queue2.front();
            queue2.pop();
            for (auto v: G[cur]) {
                if (comp_vis.count(belong_component[v])) {
                    if (!bfs_E.count({cur, v})) {
                        bfs_E[{cur, v}] = bfs_E[{v, cur}] = 1;
                        if (mpp[cur].second == mpp[v].second) {
                            inter_E++;
                        } else intra_E++;
                    }
                    if (!bfs_V.count(v)) {
                        bfs_V[v] = 1;
                        queue2.push(v);
                    }
                }
            }
        }
        ll cnt_V = bfs_V.size();
        double inter_density = 2.0 * inter_E / cnt_V / (cnt_V - 1);
        double intra_density = 2.0 * intra_E / cnt_V / (cnt_V - 1);
        cout << "cur_inter_density: " << fixed << setprecision(8) << inter_density << endl;
        cout << "cur_intra_density: " << fixed << setprecision(8) << intra_density << endl;
        sum_inter_density += inter_density;
        sum_intra_density += intra_density;
        cout << "avg_inter_density: " << fixed << setprecision(8) << sum_inter_density / _ << endl;
        cout << "avg_intra_density: " << fixed << setprecision(8) << sum_intra_density / _ << endl;
    }
}

signed main(int argc, char *argv[]) {
    tmp = argv[1];
    solve();
    return 0;
}
