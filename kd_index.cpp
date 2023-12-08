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
        queue<int>q;
        q.push(i);
        while(!q.empty()){
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
string tmp ;
void solve() {
	string ss = tmp+".txt";
	freopen(ss.c_str(),"r",stdin);
	mp.clear(); 
    cin >> n >> m >> layers;
//    debug(n, m, layers);
    vector<set<int>> G(n * layers + 1);
    nd_tot = 0;
    vector<set<int>> layer_sets(layers + 1);
    vector<pair<int, int>> mpp(n * layers + 1);
    for (int i = 1; i <= m; i++) {
        int u, v, lu, lv;
        cin >> u >> lu >> v >> lv;
//        double val;
//        cin >> val;
        int id1 = trans({u, lu}, mpp), id2 = trans({v, lv}, mpp);
        layer_sets[lu].insert(id1), layer_sets[lv].insert(id2);
        G[id1].insert(id2), G[id2].insert(id1);
    }
    
    
    //K-D index init
    int KK = 1;
    vector<vector<map<int, int>>> kd_index(nd_tot + 1, vector<map<int, int>>(layers + 1));
    double st =  1.0 * clock() / CLOCKS_PER_SEC;
    while (true) {
//        debug(KK);
        split_vis.clear();
        for (int i = 1; i <= layers; i++) {
            unordered_map<int, int> res = coreDecomposition(i, layer_sets[i], i, layer_sets[i], G, mpp);
            for (auto [cur, k]: res) {
                if (k < KK) {
                    split_vis[cur] = true;
                }
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
        if (KK == 1) {
            for (int i = 1; i <= component_tot; i++) {
                for (int j = 1; j <= layers; j++) {
                    int D = 1;
                    while (true) {
                        int flag = 0;
                        for (auto [id, sets]: layer_component[j]) {
                        	if(id == i) continue;
                            auto [res1, res2] = cores(KK, D, components[i], components[id], G);
                            if (res1.empty() || res2.empty()) {
                                continue;
                            } else {
                                flag = 1;
                                break;
                            }
                        }
                        if (flag) D++;
                        else {
                        	D--;
                        	break;
						}
                    }  
					for (auto u: components[i]) {
	                    kd_index[u][j][KK] = D;
	                } 	
                }
            }
        } else {
            for (int i = 1; i <= component_tot; i++) {
                int sign = *components[i].begin();
                for (int j = 1; j <= layers; j++) {
                    int D = kd_index[sign][j][KK - 1];
                    while (true) {
                        if (D == 0)break;
                        int flag = 0;
                        for (auto [id, sets]: layer_component[j]) {
                        	if(id == i) continue;
                            auto [res1, res2] = cores(KK, D, components[i], components[id], G);
                            if (res1.empty() || res2.empty()) {
                                continue;
                            } else {
                                flag = 1;
                                break;
                            }
                        }
                        if (flag)break;
                        D--;
                    }
                    for (auto u: components[i]) {
                        kd_index[u][j][KK] = D;
                    }
                }
            }
        }
        KK++;
    }
    
    double ed =  1.0 * clock() / CLOCKS_PER_SEC;
    string sss = tmp + "_index_time.txt";
    freopen(sss.c_str(),"w",stdout);
    cout<<fixed<<setprecision(8)<<ed-st<<endl;
    
    string ssss =  tmp + "_index.txt";
    freopen(ssss.c_str(),"w",stdout);
	cout<<nd_tot<<" "<<layers<<endl;
    for (int i = 1; i <= nd_tot; i++) {
        cout << mpp[i].first << " " << mpp[i].second << "\n";
        for (int j = 1; j <= layers; j++) {
            cout<<kd_index[i][j].size()<<"\n";
            for (auto [k, d]: kd_index[i][j]) {
                cout << k << " " << d << "\n";
            }
        }
        cout << "\n";
    }
}

signed main(int argc, char *argv[]) {
	// vector<string>vec_tmp;
	// vec_tmp.push_back("Venetie_db");
	// vec_tmp.push_back("6ng");
	// vec_tmp.push_back("9ng");
	// vec_tmp.push_back("citeseer");
	// vec_tmp.push_back("1dblp");
	// vec_tmp.push_back("twitter");
	// vec_tmp.push_back("yeast_db");
	// vec_tmp.push_back("fao_db");
	// vec_tmp.push_back("dblp");
	// vec_tmp.push_back("ff_db");
    int _ = 1;
    for (int i = 1; i <= _; i++) {
	// for(auto i:vec_tmp){
		// tmp = i ;
        tmp = argv[1];
		solve();
	}
    return 0;
}
/*

 17 28 3

 1 1 2 1
 1 1 3 1
 2 1 3 1
 4 1 5 1
 4 1 6 1
 5 1 6 1
 3 1 16 1
 16 1 5 1

 7 2 8 2
 7 2 9 2
 8 2 9 2
 10 2 11 2
 10 2 12 2
 11 2 12 2
 9 2 17 2
 17 2 11 2

 13 3 14 3
 13 3 15 3
 14 3 15 3

 1 1 7 2
 1 1 13 3
 2 1 8 2
 2 1 14 3
 3 1 9 2
 3 1 15 3
 7 2 13 3
 8 2 14 3
 9 2 15 3

 1
 1 1

 2 1
*/

