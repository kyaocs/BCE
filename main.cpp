//
//  main.cpp
//  MSBC_GAP
//
//  Created by kai on 2022/1/21.
//

#include "Timer.h"
#include "Utility.h"
#include "LinearHeap.h"

ui n; //number of vertices
ui m; //number of edges
ui pm; //number of positive edges
ui nm; //number of negative edges
ui d_MAX; //max degree
ui max_core; //degeneracy number
int tau; //threshold
int alpha; //gap
int Mtau; //polarization factor
pair<vector<ui>, vector<ui>> cur_MC; //currently the largest MSBC
int LB; //Lower Bound
int UB; //UB of MSBC
ui * mapping;
ui * ori_id;
ui * inLR;
unordered_map<ui, string> id2str;
vector<pair<vector<ui>, vector<ui>>> results;
int result_num = 0;
ui CntEgoNet;
ui num_of_ori_edges;
ui num_of_now_edges;
ui num_of_after_reduction_now_edges;

//original graph
ui * p_pstart;
ui * p_pend;
ui * p_edges;
ui * n_pstart;
ui * n_pend;
ui * n_edges;

//intermediate graph
ui * inter_p_pstart;
//ui * inter_p_pend;
ui * inter_p_edges;
ui * inter_n_pstart;
//ui * inter_n_pend;
ui * inter_n_edges;
ui * inter_degree;
ui * inter_p_degree;
ui * inter_n_degree;
ui inter_n;
ui * inter_core;

//oriented graph
ui * p_pstart_o;
ui * p_pend_o;
ui * p_edges_o;
ui * n_pstart_o;
ui * n_pend_o;
ui * n_edges_o;

//degree
ui * degree;
ui * p_degree;
ui * n_degree;

//peeling information
ui * core;
ui * peel_s;
ui * bit_del;
ui * PNdeg;
ui max_PorNdeg;
int ** Matrix;
ui * trans;
//ui * trs;
ui * inPN;
ui * vs_core;
ui * vs_color;
vector<ui> maxC;

void load_graph(string input_graph)
{
    string buffer;
    ifstream input_file(input_graph, ios::in);
    
    if (!input_file.is_open()){
        cout << "cannot open file : "<<input_graph<<endl;exit(1);
    }
    else{
        input_file >> n >> m;
        map<ui, int> * s_G = new map<ui, int>[n];
        ui tu, tv;
        int flag;
        while (input_file >> tu >> tv >> flag){
            if(tu == tv) continue;
            assert(tu >= 0 && tu < n);
            assert(tv >= 0 && tv < n);
            assert(flag == 1 || flag == -1);
            s_G[tu].insert(make_pair(tv, flag));
            s_G[tv].insert(make_pair(tu, flag));
        }
        m = 0; pm = 0; nm = 0;
        for(ui i = 0; i < n; i++){
            const map<ui, int> & nei = s_G[i];
            for(auto e : nei){
                if(e.second == 1)
                    ++ pm;
                else
                    ++ nm;
            }
            m += nei.size();
        }
        assert(m%2 == 0);assert(pm%2 == 0);assert(nm%2 == 0);
        m /= 2; pm /= 2; nm /= 2;

        input_file.close();
        
        p_pstart = new ui[n+1];
        p_edges = new ui[2*pm];
        p_pend = new ui[n];
        n_pstart = new ui[n+1];
        n_edges = new ui[2*nm];
        n_pend = new ui[n];
        
        degree = new ui[n];
        p_degree = new ui[n];
        n_degree = new ui[n];
        
        //construct positive edges
        p_pstart[0] = 0;
        for(ui i = 0; i < n; i++){
            const map<ui, int> & nei = s_G[i];
            ui start_idx = p_pstart[i];
            int t_d = 0;
            for(auto e : nei){
                if(e.second == 1){
                    p_edges[start_idx ++] = e.first;
                    ++ t_d;
                }
            }
            p_pstart[i+1] = start_idx;
            p_degree[i] = t_d;
        }
        assert(p_pstart[n] == 2*pm);
        
        //construct negative edges
        n_pstart[0] = 0;
        for(ui i = 0; i < n; i++){
            const map<ui, int> & nei = s_G[i];
            ui start_idx = n_pstart[i];
            int t_d = 0;
            for(auto e : nei){
                if(e.second == -1){
                    n_edges[start_idx ++] = e.first;
                    ++ t_d;
                }
            }
            n_pstart[i+1] = start_idx;
            n_degree[i] = t_d;
        }
        assert(n_pstart[n] == 2*nm);
        
        for(ui i = 0; i < n; i++){
            p_pend[i] = p_pstart[i+1];
            n_pend[i] = n_pstart[i+1];
        }
        long max_pndeg = 0;
        d_MAX = 0;
        for(ui i = 0; i < n; i++){
            degree[i] = p_degree[i] + n_degree[i];
            if(p_degree[i] * n_degree[i] > max_pndeg) max_pndeg = p_degree[i] * n_degree[i];
            if(degree[i] > d_MAX)
                d_MAX = degree[i];
        }
        delete [] s_G;
        
        //allocate memory for intermediate subgraph, for MBCEG problem
        inter_p_pstart = new ui[n+1];
        inter_p_edges = new ui[2*pm];
//        inter_p_pend = new ui[n];
        inter_n_pstart = new ui[n+1];
        inter_n_edges = new ui[2*nm];
//        inter_n_pend = new ui[n];
        
        inter_degree = new ui[n];
        inter_p_degree = new ui[n];
        inter_n_degree = new ui[n];
        
    }
//    cout<<"\t G : n = "<<n<<", pm = "<<pm<<", nm = "<<nm<<endl;
#ifdef _CaseStudy_
    input_graph.erase(input_graph.end() - 4, input_graph.end());
    input_graph.append("_map.txt"); //the mapping file should be named in this way.
    input_file.open(input_graph);
    if(!input_file.is_open()){ cout<<"cannot open map file !"<<endl; exit(1); }
    ori_id = new ui[n];
    ui vid;
    string content;
    while (input_file >> content >> vid) id2str[vid] = content;
    input_file.close();
#endif
}

//greedy search until find one solution, at most 'rounds' tries.
void heu_MSBC_max_deg_inturn_find_one_stop(int rounds)
{
    if(rounds < 1) return;
    assert(psz(cur_MC) == 0);
    priority_queue<pair<ui, ui>, vector<pair<ui, ui>>, greater<pair<ui, ui>>> kset;
    for (ui i = 0; i < rounds; i++) kset.push(make_pair(miv(p_degree[i], n_degree[i]), i));
    
    for(ui i = rounds; i < n; i++){
        ui itsdeg = miv(p_degree[i], n_degree[i]);
        if(itsdeg > kset.top().first){
            kset.pop();
            kset.push(make_pair(itsdeg, i));
        }
    }
    vector<pair<ui, ui>> ordV(rounds);
    for(ui i = 0; i < rounds; i++){
        ordV[i] = kset.top();
        kset.pop();
    }
    assert(kset.empty());
    
    sort(ordV.begin(), ordV.end(), greater<>());
    
    ui * label = new ui[n];
    ui * vs_deg = new ui[n];
    
    for(ui round = 0; round < rounds && round < n; round++){
        ui u = ordV[round].second;
        memset(label, 0, sizeof(ui)*n);
        pair<vector<ui>, vector<ui>> res;
        res.first.push_back(u);
        vector<ui> vsP, vsN;
        for(ui i = p_pstart[u]; i < p_pend[u]; i++){
            ui v = p_edges[i];
            vsP.push_back(v);
            label[v] = 1;
        }
        for(ui i = n_pstart[u]; i < n_pend[u]; i++){
            ui v = n_edges[i];
            vsN.push_back(v);
            label[v] = 2;
        }
        for(auto e : vsP) vs_deg[e] = 0;
        for(auto e : vsN) vs_deg[e] = 0;
        for(auto e : vsP){
            for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                ui v = p_edges[i];
                if(label[v] == 1) ++ vs_deg[e];
            }
            for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                ui v = n_edges[i];
                if(label[v] == 2) ++ vs_deg[e];
            }
        }
        for(auto e : vsN){
            for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                ui v = p_edges[i];
                if(label[v] == 2) ++ vs_deg[e];
            }
            for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                ui v = n_edges[i];
                if(label[v] == 1) ++ vs_deg[e];
            }
        }
        
        while (!vsP.empty() || !vsN.empty()) {
            if(!vsP.empty() && !vsN.empty()){
                if(res.first.size() >= res.second.size()){ // next vertex will select from vsN
                    ui tmp_deg = 0;
                    ui next_v;
                    for(ui i = 0; i < vsN.size(); i++){
                        if(vs_deg[vsN[i]] >= tmp_deg){
                            tmp_deg = vs_deg[vsN[i]];
                            next_v = vsN[i];
                        }
                    }
                    res.second.push_back(next_v);
                    vector<ui> new_vsP, new_vsN;
                    assert(label[next_v] == 2);
                    for(ui i = p_pstart[next_v]; i < p_pend[next_v]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 2) new_vsN.push_back(v);
                    }
                    for(ui i = n_pstart[next_v]; i < n_pend[next_v]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 1) new_vsP.push_back(v);
                    }
                    for(auto e : vsP) label[e] = 0;
                    for(auto e : vsN) label[e] = 0;
                    vsP = new_vsP;
                    vsN = new_vsN;
                    for(auto e : vsP) label[e] = 1;
                    for(auto e : vsN) label[e] = 2;
                    for(auto e : vsP) vs_deg[e] = 0;
                    for(auto e : vsN) vs_deg[e] = 0;
                    for(auto e : vsP){
                        for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                            ui v = p_edges[i];
                            if(label[v] == 1) ++ vs_deg[e];
                        }
                        for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                            ui v = n_edges[i];
                            if(label[v] == 2) ++ vs_deg[e];
                        }
                    }
                    for(auto e : vsN){
                        for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                            ui v = p_edges[i];
                            if(label[v] == 2) ++ vs_deg[e];
                        }
                        for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                            ui v = n_edges[i];
                            if(label[v] == 1) ++ vs_deg[e];
                        }
                    }
                }
                else{ // next vertex will select from vsP
                    ui tmp_deg = 0;
                    ui next_v;
                    for(ui i = 0; i < vsP.size(); i++){
                        if(vs_deg[vsP[i]] >= tmp_deg){
                            tmp_deg = vs_deg[vsP[i]];
                            next_v = vsP[i];
                        }
                    }
                    res.first.push_back(next_v);
                    vector<ui> new_vsP, new_vsN;
                    assert(label[next_v] == 1);
                    for(ui i = p_pstart[next_v]; i < p_pend[next_v]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 1) new_vsP.push_back(v);
                    }
                    for(ui i = n_pstart[next_v]; i < n_pend[next_v]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 2) new_vsN.push_back(v);
                    }
                    for(auto e : vsP) label[e] = 0;
                    for(auto e : vsN) label[e] = 0;
                    vsP = new_vsP;
                    vsN = new_vsN;
                    for(auto e : vsP) label[e] = 1;
                    for(auto e : vsN) label[e] = 2;
                    for(auto e : vsP) vs_deg[e] = 0;
                    for(auto e : vsN) vs_deg[e] = 0;
                    for(auto e : vsP){
                        for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                            ui v = p_edges[i];
                            if(label[v] == 1) ++ vs_deg[e];
                        }
                        for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                            ui v = n_edges[i];
                            if(label[v] == 2) ++ vs_deg[e];
                        }
                    }
                    for(auto e : vsN){
                        for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                            ui v = p_edges[i];
                            if(label[v] == 2) ++ vs_deg[e];
                        }
                        for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                            ui v = n_edges[i];
                            if(label[v] == 1) ++ vs_deg[e];
                        }
                    }
                }
            }
            else if(vsP.empty() && !vsN.empty()){ // next vertex will select from vsN
                ui tmp_deg = 0;
                ui next_v;
                for(ui i = 0; i < vsN.size(); i++){
                    if(vs_deg[vsN[i]] >= tmp_deg){
                        tmp_deg = vs_deg[vsN[i]];
                        next_v = vsN[i];
                    }
                }
                res.second.push_back(next_v);
                vector<ui> new_vsP, new_vsN;
                assert(label[next_v] == 2);
                for(ui i = p_pstart[next_v]; i < p_pend[next_v]; i++){
                    ui v = p_edges[i];
                    if(label[v] == 2) new_vsN.push_back(v);
                }
                for(ui i = n_pstart[next_v]; i < n_pend[next_v]; i++){
                    ui v = n_edges[i];
                    if(label[v] == 1) new_vsP.push_back(v);
                }
                for(auto e : vsP) label[e] = 0;
                for(auto e : vsN) label[e] = 0;
                vsP = new_vsP;
                vsN = new_vsN;
                for(auto e : vsP) label[e] = 1;
                for(auto e : vsN) label[e] = 2;
                for(auto e : vsP) vs_deg[e] = 0;
                for(auto e : vsN) vs_deg[e] = 0;
                for(auto e : vsP){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                }
                for(auto e : vsN){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                }
            }
            else if (!vsP.empty() && vsN.empty()){ // next vertex will select from vsP
                ui tmp_deg = 0;
                ui next_v;
                for(ui i = 0; i < vsP.size(); i++){
                    if(vs_deg[vsP[i]] >= tmp_deg){
                        tmp_deg = vs_deg[vsP[i]];
                        next_v = vsP[i];
                    }
                }
                res.first.push_back(next_v);
                vector<ui> new_vsP, new_vsN;
                assert(label[next_v] == 1);
                for(ui i = p_pstart[next_v]; i < p_pend[next_v]; i++){
                    ui v = p_edges[i];
                    if(label[v] == 1) new_vsP.push_back(v);
                }
                for(ui i = n_pstart[next_v]; i < n_pend[next_v]; i++){
                    ui v = n_edges[i];
                    if(label[v] == 2) new_vsN.push_back(v);
                }
                for(auto e : vsP) label[e] = 0;
                for(auto e : vsN) label[e] = 0;
                vsP = new_vsP;
                vsN = new_vsN;
                for(auto e : vsP) label[e] = 1;
                for(auto e : vsN) label[e] = 2;
                for(auto e : vsP) vs_deg[e] = 0;
                for(auto e : vsN) vs_deg[e] = 0;
                for(auto e : vsP){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                }
                for(auto e : vsN){
                    for(ui i = p_pstart[e]; i < p_pend[e]; i++){
                        ui v = p_edges[i];
                        if(label[v] == 2) ++ vs_deg[e];
                    }
                    for(ui i = n_pstart[e]; i < n_pend[e]; i++){
                        ui v = n_edges[i];
                        if(label[v] == 1) ++ vs_deg[e];
                    }
                }
            }
            else{
                cout<<"wrong!"<<endl;
                exit(1);
            }
        }
        if(psz(res) > psz(cur_MC) && res.first.size() >= tau && res.second.size() >= tau){
            cur_MC = res;
            break;
        }
    }
}

void vertex_reduction(ui & del_count, ui * bit_del)
{
    if(tau <= 1) {cout<<"\ttau should be at least 2"<<endl; exit(1); }
    int pt = tau - 1;
    int nt = tau;
    queue<ui> Q;
    for(ui i = 0; i < n; i++) if(p_degree[i] < pt || n_degree[i] < nt) Q.push(i);
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        ++ del_count;
        bit_del[u] = 1;
        for(ui i = p_pstart[u]; i < p_pstart[u+1]; i++){
            if((p_degree[p_edges[i]]--) == pt && n_degree[p_edges[i]] >= nt){
                Q.push(p_edges[i]);
            }
        }
        for(ui i = n_pstart[u]; i < n_pstart[u+1]; i++){
            if((n_degree[n_edges[i]]--) == nt && p_degree[n_edges[i]] >= pt){
                Q.push(n_edges[i]);
            }
        }
    }
}

void shrink_on_reduced_v(ui * bit_del)
{
    mapping = new ui[n];
    ori_id = new ui[n];
    ui idx = 0;
    for(ui i = 0; i < n; i++) {
        if(!bit_del[i]) {
            mapping[i] = idx;
            ori_id[idx] = i;
            ++ idx;
        }
    }
#ifdef _DEBUG_
    cout<<"after shrink_on_reduced_v(), mapping content : "<<endl;
    for(ui i = 0; i < n; i++){
        if(!bit_del[i]){
            cout<<" "<<i<<" ---> "<<mapping[i]<<endl;
        }
    }
#endif
    ui * t_p_pstart = new ui[n+1];
    ui * t_p_edges = new ui[2*pm];
    ui * t_n_pstart = new ui[n+1];
    ui * t_n_edges = new ui[2*nm];
    ui new_i = 0;
    t_p_pstart[0] = 0;
    for(ui i = 0; i < n; i++) if(!bit_del[i]){
        ui pos = t_p_pstart[new_i];
        for(ui j = p_pstart[i]; j < p_pstart[i+1]; j++) if(!bit_del[p_edges[j]]){
            t_p_edges[pos++] = mapping[p_edges[j]];
        }
        t_p_pstart[++new_i] = pos;
    }
    assert(new_i == idx);
    new_i = 0;
    t_n_pstart[0] = 0;
    for(ui i = 0; i < n; i++) if(!bit_del[i]){
        ui pos = t_n_pstart[new_i];
        for(ui j = n_pstart[i]; j < n_pstart[i+1]; j++) if(!bit_del[n_edges[j]]){
            t_n_edges[pos++] = mapping[n_edges[j]];
        }
        t_n_pstart[++new_i] = pos;
    }
    assert(new_i == idx);
    n = idx;
    delete [] p_pstart;
    delete [] p_edges;
    delete [] n_pstart;
    delete [] n_edges;
    p_pstart = t_p_pstart;
    p_edges = t_p_edges;
    n_pstart = t_n_pstart;
    n_edges = t_n_edges;
    //update pend
    for(ui i = 0; i < n; i++){
        p_pend[i] = p_pstart[i+1];
        n_pend[i] = n_pstart[i+1];
    }
    d_MAX = 0;
    //update degree
    for(ui i = 0; i < n; i++){
        p_degree[i] = p_pstart[i+1] - p_pstart[i];
        n_degree[i] = n_pstart[i+1] - n_pstart[i];
        degree[i] = p_degree[i] + n_degree[i];
        if(degree[i] > d_MAX) d_MAX = degree[i];
    }
    PNdeg = new ui[n];
    max_PorNdeg = 0;
    for(ui i = 0; i < n; i++){
        if(p_degree[i] < n_degree[i]) PNdeg[i] = p_degree[i] + 1;
        else PNdeg[i] = n_degree[i];
        if(p_degree[i] > max_PorNdeg) max_PorNdeg = p_degree[i];
        if(n_degree[i] > max_PorNdeg) max_PorNdeg = n_degree[i];
    }
    //reserve intermediate subgraph for MBCEG problem
    inter_n = n;
    for(ui i = 0; i < n+1; i++) {
        inter_p_pstart[i] = p_pstart[i];
        inter_n_pstart[i] = n_pstart[i];
    }
    for(ui i = 0; i < 2*pm; i++) inter_p_edges[i] = p_edges[i];
    for(ui i = 0; i < 2*nm; i++) inter_n_edges[i] = n_edges[i];
    for(ui i = 0; i < n; i++){
        inter_degree[i] = degree[i];
        inter_p_degree[i] = p_degree[i];
        inter_n_degree[i] = n_degree[i];
    }
}

inline void reord_deg(ui & v1, ui & v2)
{
    if(degree[v1]>degree[v2]){
        ui t = v2;
        v2 = v1;
        v1 = t;
    }
}

ui color_based_UB()
{
    ui max_color = 0;
    ui * color = new ui[n];
    for(ui i = 0; i < n; i++) color[i] = n;
    ui * vis = new ui[n];
    memset(vis, 0, sizeof(ui)*n);
    for(ui i = n; i > 0; i--){
        ui u = peel_s[i-1];
        for(ui j = p_pstart[u]; j < p_pend[u]; j++){
            ui c = color[p_edges[j]];
            if(c != n) {vis[c] = 1;}
        }
        for(ui j = n_pstart[u]; j < n_pend[u]; j++){
            ui c = color[n_edges[j]];
            if(c != n) {vis[c] = 1;}
        }
        for(ui j = 0; ;j++) if(!vis[j]) {
            color[u] = j;
            if(j > max_color) {max_color = j;}
            break;
        }
        for(ui j = p_pstart[u]; j < p_pend[u]; j++){
            ui c = color[p_edges[j]];
            if(c != n) vis[c] = 0;
        }
        for(ui j = n_pstart[u]; j < n_pend[u]; j++){
            ui c = color[n_edges[j]];
            if(c != n) vis[c] = 0;
        }
    }
    delete [] color;
    delete [] vis;
    return max_color + 1;
}

void PN_order()
{
    assert(n > 0);
    max_core = 0;
    ListLinearHeap *linear_heap = new ListLinearHeap(n, max_PorNdeg);
    linear_heap->init(n, max_PorNdeg, peel_s, PNdeg);
    core = new ui[n];
    memset(core, 0, sizeof(ui)*n);
    for(ui i = 0; i < n; i ++) {
        ui u, key;
        linear_heap->pop_min(u, key);
        if(key > max_core) max_core = key;
        peel_s[i] = u;
        core[u] = max_core;
        for(ui j = p_pstart[u];j < p_pend[u];j ++){
            ui v = p_edges[j];
            if(core[v] == 0){
                if((p_degree[v]--) < n_degree[v]){
                    linear_heap->decrement(v, 1);
                }
            }
        }
        for(ui j = n_pstart[u];j < n_pend[u];j ++){
            ui v = n_edges[j];
            if(core[v] == 0){
                if((n_degree[v]--) <= p_degree[v] + 1){
                    linear_heap->decrement(v, 1);
                }
            }
        }
    }
    delete linear_heap;
    
#ifdef _DEBUG_
    cout<<"core information : ";
    for(ui i = 0; i< n; i++) cout<<i<<": "<<core[i]<<",  ";cout<<endl;

    cout<<"peel sequence : ";
    for(ui i = 0; i< n; i++) cout<<peel_s[i]<<", "; cout<<endl;
#endif
}
   
void degeneracy_order()
{
    assert(n > 0);
    peel_s = new ui[n]; //from left to right, record the peeling sequence
    for(ui i = 0; i < n; i++) peel_s[i] = i;
    max_core = 0;
    ListLinearHeap *linear_heap = new ListLinearHeap(n, n-1);
    linear_heap->init(n, n-1, peel_s, degree);
    core = new ui[n]; inter_core = new ui[n];
    memset(core, 0, sizeof(ui)*n);
    for(ui i = 0; i < n; i ++) {
        ui u, key;
        linear_heap->pop_min(u, key);
        if(key > max_core) max_core = key;
        peel_s[i] = u;
        core[u] = max_core;
        inter_core[u] = max_core;
        for(ui j = p_pstart[u];j < p_pend[u];j ++) if(core[p_edges[j]] == 0)
            linear_heap->decrement(p_edges[j], 1);
        for(ui j = n_pstart[u];j < n_pend[u];j ++) if(core[n_edges[j]] == 0)
            linear_heap->decrement(n_edges[j], 1);
    }
    delete linear_heap;
    
#ifdef _DEBUG_
    cout<<"core information : ";
    for(ui i = 0; i< n; i++) cout<<i<<": "<<core[i]<<",  ";cout<<endl;
    cout<<"peel sequence : ";
    for(ui i = 0; i< n; i++) cout<<peel_s[i]<<", "; cout<<endl;
#endif
}

void shrink_and_orient_graph_Mtau_PNorder()
{
    ui threshold = Mtau + 1;
    ui * rid = new ui[n];
    for(ui i = 0; i < n; i ++) rid[peel_s[i]] = i;
    ui * mapping = new ui[n];
    ui * oldVid = new ui[n];
    ui idx = 0;
    for(ui i = 0; i < n; i++) if(core[peel_s[i]] >= threshold) {
        mapping[peel_s[i]] = idx;
        oldVid[idx] = peel_s[i];
        idx++;
    }
#ifdef _DEBUG_
    cout<<"in orient_graph(), mapping content : "<<endl;
    for(ui i = 0; i < n; i++){
        if(core[peel_s[i]] >= threshold){
            cout<<" "<<peel_s[i]<<" ---> "<<mapping[peel_s[i]]<<endl;
        }
    }
#endif
    p_pstart_o = new ui[n+1];
    p_edges_o = new ui[pm*2];
    p_pstart_o[0] = 0;
    ui cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = p_pstart_o[cnt];
            for(ui j = p_pstart[u]; j < p_pend[u]; j++){
                ui v = p_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    p_edges_o[pos++] = mapping[v];
                }
            }
            p_pstart_o[++cnt] = pos;
        }
    }
    assert(cnt == idx);
    
    n_pstart_o = new ui[n+1];
    n_edges_o = new ui[nm*2];
    n_pstart_o[0] = 0;
    cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = n_pstart_o[cnt];
            for(ui j = n_pstart[u]; j < n_pend[u]; j++){
                ui v = n_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    n_edges_o[pos++] = mapping[v];
                }
            }
            n_pstart_o[++cnt] = pos;
        }
    }
    assert(cnt == idx);
#ifdef _DEBUG_
    cout<<"after orient, n = "<<cnt<<endl;
    cout<<"p_pstart_o and p_pend_o info : "<<endl;
    for(ui i = 0; i < cnt; i++){
        cout<<"for vertex "<<i<<" : "<<endl;
        cout<<"  + neis : ";
        for(ui j = p_pstart_o[i]; j < p_pstart_o[i+1]; j++){
            cout<<p_edges_o[j]<<", ";
        }cout<<endl;
        cout<<"  - neis : ";
        for(ui j = n_pstart_o[i]; j < n_pstart_o[i+1]; j++){
            cout<<n_edges_o[j]<<", ";
        }cout<<endl;
    }
#endif
    n = idx;
    for(ui i = 0; i < n; i++) rid[i] = core[oldVid[i]];
    delete [] core;
    core = rid;
    delete [] mapping;
    delete [] oldVid;
}

void shrink_and_orient_graph_Mtau_dorder()
{
    ui threshold = Mtau + 1;
    ui * rid = new ui[n];
    memset(rid, 0, sizeof(ui)*n);
    for(ui i = 0; i < n; i ++) rid[peel_s[i]] = i;
    ui * mapping = new ui[n]; memset(mapping, 0, sizeof(ui)*n);
    ui * oldVid = new ui[n]; memset(oldVid, 0, sizeof(ui)*n);
    ui idx = 0;
    for(ui i = 0; i < n; i++) if(core[peel_s[i]] >= threshold) {
        mapping[peel_s[i]] = idx;
        oldVid[idx] = peel_s[i];
        idx++;
    }
#ifdef _DEBUG_
    cout<<"in orient_graph(), mapping content : "<<endl;
    for(ui i = 0; i < n; i++){
        if(core[peel_s[i]] >= threshold){
            cout<<" "<<peel_s[i]<<" ---> "<<mapping[peel_s[i]]<<endl;
        }
    }
#endif
    p_pstart_o = new ui[n+1];
    p_edges_o = new ui[pm*2];
    p_pstart_o[0] = 0;
    ui cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = p_pstart_o[cnt];
            for(ui j = p_pstart[u]; j < p_pend[u]; j++){
                ui v = p_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    p_edges_o[pos++] = mapping[v];
                }
            }
            p_pstart_o[++cnt] = pos;
        }
    }
    assert(cnt == idx);

    n_pstart_o = new ui[n+1];
    n_edges_o = new ui[nm*2];
    n_pstart_o[0] = 0;
    cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = n_pstart_o[cnt];
            for(ui j = n_pstart[u]; j < n_pend[u]; j++){
                ui v = n_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    n_edges_o[pos++] = mapping[v];
                }
            }
            n_pstart_o[++cnt] = pos;
        }
    }
    n = idx;
    for(ui i = 0; i < n; i++) rid[i] = core[oldVid[i]];
    delete [] core;
    core = rid;
    assert(cnt == idx);
    for(ui i = 1; i < n; i++) if(core[i] < core[i-1]) exit(1);
#ifdef _DEBUG_
    cout<<"after orient, n = "<<cnt<<endl;
    cout<<"p_pstart_o and p_pend_o info : "<<endl;
    for(ui i = 0; i < cnt; i++){
        cout<<"for vertex "<<i<<" : "<<endl;
        cout<<"  + neis : ";
        for(ui j = p_pstart_o[i]; j < p_pstart_o[i+1]; j++){
            cout<<p_edges_o[j]<<", ";
        }cout<<endl;
        cout<<"  - neis : ";
        for(ui j = n_pstart_o[i]; j < n_pstart_o[i+1]; j++){
            cout<<n_edges_o[j]<<", ";
        }cout<<endl;
    }
#endif
    delete [] mapping;
    delete [] oldVid;
}

void shrink_and_orient_graph()
{
    ui threshold = psz(cur_MC);
    ui * rid = new ui[n]; //record vertex ranking, i.e., rid[vertexid] = ranking in peel_s
    for(ui i = 0; i < n; i ++) rid[peel_s[i]] = i;
    ui * mapping = new ui[n];
    ui * oldVid = new ui[n];
    
    ui idx = 0;
    for(ui i = 0; i < n; i++) if(core[peel_s[i]] >= threshold) {
        mapping[peel_s[i]] = idx;
        oldVid[idx] = peel_s[i];
        idx++;
    }
    
#ifdef _DEBUG_
    cout<<"in orient_graph(), mapping content : "<<endl;
    for(ui i = 0; i < n; i++){
        if(core[peel_s[i]] >= threshold){
            cout<<" "<<peel_s[i]<<" ---> "<<mapping[peel_s[i]]<<endl;
        }
    }
#endif
    p_pstart_o = new ui[n+1];
    p_edges_o = new ui[pm*2];
    p_pstart_o[0] = 0;
    ui cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = p_pstart_o[cnt];
            for(ui j = p_pstart[u]; j < p_pend[u]; j++){
                ui v = p_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    p_edges_o[pos++] = mapping[v];
                }
            }
            p_pstart_o[++cnt] = pos;
        }
    }
    assert(cnt == idx);

    n_pstart_o = new ui[n+1];
    n_edges_o = new ui[nm*2];
    n_pstart_o[0] = 0;
    cnt = 0;
    for(ui i = 0; i < n; i++){
        ui u = peel_s[i];
        if(core[u] >= threshold){
            ui pos = n_pstart_o[cnt];
            for(ui j = n_pstart[u]; j < n_pend[u]; j++){
                ui v = n_edges[j];
                if(rid[v] > rid[u]){
                    assert(core[v]>=threshold);
                    n_edges_o[pos++] = mapping[v];
                }
            }
            n_pstart_o[++cnt] = pos;
        }
    }
    assert(cnt == idx);
#ifdef _DEBUG_
    cout<<"after orient, n = "<<cnt<<endl;
    cout<<"p_pstart_o and p_pend_o info : "<<endl;
    for(ui i = 0; i < cnt; i++){
        cout<<"for vertex "<<i<<" : "<<endl;
        cout<<"  + neis : ";
        for(ui j = p_pstart_o[i]; j < p_pstart_o[i+1]; j++){
            cout<<p_edges_o[j]<<", ";
        }cout<<endl;
        cout<<"  - neis : ";
        for(ui j = n_pstart_o[i]; j < n_pstart_o[i+1]; j++){
            cout<<n_edges_o[j]<<", ";
        }cout<<endl;
    }
#endif
    n = idx;
    for(ui i = 0; i < n; i++) rid[i] = core[oldVid[i]];
    delete [] core;
    core = rid;
    delete [] mapping;
    delete [] oldVid;
}

void construct_induced_subgraph(ui * vsP, ui vsP_size, ui * vsN, ui vsN_size, ui & tmp_ori_edges, ui& tmp_now_edges)
{
    tmp_ori_edges = vsP_size + vsN_size;
    tmp_now_edges = 0;
    for(ui i = 0; i < vsP_size; i++) {
        ui u = vsP[i];
        degree[u] = 0;
        p_degree[u] = 0;
        n_degree[u] = 0;
    }
    for(ui i = 0; i < vsN_size; i++) {
        ui u = vsN[i];
        degree[u] = 0;
        p_degree[u] = 0;
        n_degree[u] = 0;
    }
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 1){
                ++ degree[u];
                ++ degree[v];
                ++ p_degree[u];
                ++ p_degree[v];
                ++ tmp_now_edges;
            }
            if(inPN[v] != 0) ++ tmp_ori_edges;
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 2){
                ++ degree[u];
                ++ degree[v];
                ++ n_degree[u];
                ++ n_degree[v];
                ++ tmp_now_edges;
            }
            if(inPN[v] != 0) ++ tmp_ori_edges;
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 2){
                ++ degree[u];
                ++ degree[v];
                ++ p_degree[u];
                ++ p_degree[v];
                ++tmp_now_edges;
            }
            if(inPN[v] != 0) ++ tmp_ori_edges;
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 1){
                ++ degree[u];
                ++ degree[v];
                ++ n_degree[u];
                ++ n_degree[v];
                ++tmp_now_edges;
            }
            if(inPN[v] != 0) ++ tmp_ori_edges;
        }
    }
    
#ifdef _DEBUG_
    cout<<"in this induced subgraph, each vertex degree : "<<endl;
    for(ui i = 0; i < vsP_size; i++)
        cout<<vsP[i]<<": deg = "<<degree[vsP[i]]<<",  p_deg = "<<p_degree[vsP[i]]<<",  n_deg = "<<n_degree[vsP[i]]<<endl;
    for(ui i = 0; i < vsN_size; i++)
        cout<<vsN[i]<<": deg = "<<degree[vsN[i]]<<",  p_deg = "<<p_degree[vsN[i]]<<",  n_deg = "<<n_degree[vsN[i]]<<endl;
#endif
    
    assert(vsP_size > 0);
    assert(vsN_size > 0);
    
    p_pstart[vsP[0]] = 0;
    for(ui i = 1; i < vsP_size; i++) p_pstart[vsP[i]] = p_pstart[vsP[i-1]] + p_degree[vsP[i-1]];
    if(vsP_size > 0) p_pstart[vsN[0]] = p_pstart[vsP[vsP_size-1]] + p_degree[vsP[vsP_size-1]];
    else p_pstart[vsN[0]] = 0;
    for(ui i = 1; i < vsN_size; i++) p_pstart[vsN[i]] = p_pstart[vsN[i-1]] + p_degree[vsN[i-1]];
    
    n_pstart[vsP[0]] = 0;
    for(ui i = 1; i < vsP_size; i++) n_pstart[vsP[i]] = n_pstart[vsP[i-1]] + n_degree[vsP[i-1]];
    if(vsP_size > 0) n_pstart[vsN[0]] = n_pstart[vsP[vsP_size-1]] + n_degree[vsP[vsP_size-1]];
    else n_pstart[vsN[0]] = 0;
    for(ui i = 1; i < vsN_size; i++) n_pstart[vsN[i]] = n_pstart[vsN[i-1]] + n_degree[vsN[i-1]];
    
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        p_pend[u] = p_pstart[u];
        n_pend[u] = n_pstart[u];
    }
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        p_pend[u] = p_pstart[u];
        n_pend[u] = n_pstart[u];
    }
    
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 1){
                p_edges[p_pend[u]++] = v;
                p_edges[p_pend[v]++] = u;
            }
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 2){
                n_edges[n_pend[u]++] = v;
                n_edges[n_pend[v]++] = u;
            }
        }
    }
    
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 2){
                p_edges[p_pend[u]++] = v;
                p_edges[p_pend[v]++] = u;
            }
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 1){
                n_edges[n_pend[u]++] = v;
                n_edges[n_pend[v]++] = u;
            }
        }
    }
}

void construct_induced_subgraph(vector<ui> XL, vector<ui> PL, vector<ui> XR, vector<ui> PR)
{
    for(auto u : XL) { degree[u] = 0; p_degree[u] = 0; n_degree[u] = 0; }
    for(auto u : PL) { degree[u] = 0; p_degree[u] = 0; n_degree[u] = 0; }
    for(auto u : XR) { degree[u] = 0; p_degree[u] = 0; n_degree[u] = 0; }
    for(auto u : PR) { degree[u] = 0; p_degree[u] = 0; n_degree[u] = 0; }
    
    for(auto u : XL) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++)
            if(inLR[inter_p_edges[i]] == 1) { ++ degree[u]; ++ p_degree[u]; }
        for(ui i = inter_n_pstart[u]; i < inter_n_pstart[u+1]; i++)
            if(inLR[inter_n_edges[i]] == 2) { ++ degree[u]; ++ n_degree[u]; }
    }
    for(auto u : PL) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++)
            if(inLR[inter_p_edges[i]] == 1) { ++ degree[u]; ++ p_degree[u]; }
        for(ui i = inter_n_pstart[u]; i < inter_n_pstart[u+1]; i++)
            if(inLR[inter_n_edges[i]] == 2) { ++ degree[u]; ++ n_degree[u]; }
    }
    for(auto u : XR) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++)
            if(inLR[inter_p_edges[i]] == 2) { ++ degree[u]; ++ p_degree[u]; }
        for(ui i = inter_n_pstart[u]; i < inter_n_pstart[u+1]; i++)
            if(inLR[inter_n_edges[i]] == 1) { ++ degree[u]; ++ n_degree[u]; }
    }
    for(auto u : PR) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++)
            if(inLR[inter_p_edges[i]] == 2) { ++ degree[u]; ++ p_degree[u]; }
        for(ui i = inter_n_pstart[u]; i < inter_n_pstart[u+1]; i++)
            if(inLR[inter_n_edges[i]] == 1) { ++ degree[u]; ++ n_degree[u]; }
    }
    
    vector<ui> allV;
    allV.insert(allV.end(), XL.begin(), XL.end());
    allV.insert(allV.end(), PL.begin(), PL.end());
    allV.insert(allV.end(), XR.begin(), XR.end());
    allV.insert(allV.end(), PR.begin(), PR.end());
    
    assert(allV.size() > 0);
    
    p_pstart[allV[0]] = 0;
    for(ui i = 1; i < allV.size(); i++) p_pstart[allV[i]] = p_pstart[allV[i-1]] + p_degree[allV[i-1]];
    n_pstart[allV[0]] = 0;
    for(ui i = 1; i < allV.size(); i++) n_pstart[allV[i]] = n_pstart[allV[i-1]] + n_degree[allV[i-1]];
    
    for(auto u : allV) {
        p_pend[u] = p_pstart[u];
        n_pend[u] = n_pstart[u];
    }
    
    for(auto u : XL) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++) {
            ui v = inter_p_edges[i];
            if(inLR[v] == 1) { p_edges[p_pend[u]++] = v; }
        }
        for(ui i = inter_n_pstart[u]; i < inter_n_pstart[u+1]; i++) {
            ui v = inter_n_edges[i];
            if(inLR[v] == 2) { n_edges[n_pend[u]++] = v; }
        }
    }
    for(auto u : PL) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++) {
            ui v = inter_p_edges[i];
            if(inLR[v] == 1) { p_edges[p_pend[u]++] = v; }
        }
        for(ui i = inter_n_pstart[u]; i < inter_n_pstart[u+1]; i++) {
            ui v = inter_n_edges[i];
            if(inLR[v] == 2) { n_edges[n_pend[u]++] = v; }
        }
    }
    for(auto u : XR) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++) {
            ui v = inter_p_edges[i];
            if(inLR[v] == 2) { p_edges[p_pend[u]++] = v; }
        }
        for(ui i = inter_n_pstart[u]; i < inter_n_pstart[u+1]; i++) {
            ui v = inter_n_edges[i];
            if(inLR[v] == 1) { n_edges[n_pend[u]++] = v; }
        }
    }
    for(auto u : PR) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++) {
            ui v = inter_p_edges[i];
            if(inLR[v] == 2) { p_edges[p_pend[u]++] = v; }
        }
        for(ui i = inter_n_pstart[u]; i < inter_n_pstart[u+1]; i++) {
            ui v = inter_n_edges[i];
            if(inLR[v] == 1) { n_edges[n_pend[u]++] = v; }
        }
    }
}

void vs_vertex_reduce_Mtau(ui * vsP, ui & vsP_size, ui * vsN, ui & vsN_size)
{
    int vsP_pt = Mtau - 1;
    int vsP_nt = Mtau + 1;
    
    int vsN_pt = Mtau;
    int vsN_nt = Mtau;
    
    queue<ui> Q;
    
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        if(p_degree[u] < vsP_pt || n_degree[u] < vsP_nt){
            Q.push(u);
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        if(p_degree[u] < vsN_pt || n_degree[u] < vsN_nt){
            Q.push(u);
        }
    }
    
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        assert(inPN[u]==1 || inPN[u]==2);
        degree[u] = 0;
        p_degree[u] = 0;
        n_degree[u] = 0;

        for(ui i = p_pstart[u]; i < p_pend[u]; i++){
            ui v = p_edges[i];
            if(p_degree[v] > 0){
                assert(inPN[u] == inPN[v]);
                if(inPN[v] == 1){
                    if((p_degree[v]--) == vsP_pt && n_degree[v] >= vsP_nt){
                        Q.push(v);
                    }
                }
                else{
                    if((p_degree[v]--) == vsN_pt && n_degree[v] >= vsN_nt){
                        Q.push(v);
                    }
                }
            }
        }
        for(ui i = n_pstart[u]; i < n_pend[u]; i++){
            ui v = n_edges[i];
            if(n_degree[v] > 0){
                assert(inPN[u] != inPN[v]);
                if(inPN[v] == 1){
                    if((n_degree[v]--) == vsP_nt && p_degree[v] >= vsP_pt){
                        Q.push(v);
                    }
                }
                else{
                    if((n_degree[v]--) == vsN_nt && p_degree[v] >= vsN_pt){
                        Q.push(v);
                    }
                }
            }
        }
        inPN[u] = 0;
    }
    ui vsP_new_size = 0, vsN_new_size = 0;
    for(ui i = 0; i < vsP_size; i++){
        if(inPN[vsP[i]] != 0){
            vsP[vsP_new_size++] = vsP[i];
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        if(inPN[vsN[i]] != 0){
            vsN[vsN_new_size++] = vsN[i];
        }
    }
    vsP_size = vsP_new_size;
    vsN_size = vsN_new_size;
    //update degree
    for(ui i = 0; i < vsP_size; i++)
        degree[vsP[i]] = p_degree[vsP[i]] + n_degree[vsP[i]];
    for(ui i = 0; i < vsN_size; i++)
        degree[vsN[i]] = p_degree[vsN[i]] + n_degree[vsN[i]];
    
#ifdef _DEBUG_
    cout<<"now, vsP_new_size = "<<vsP_new_size<<endl;
    cout<<"now, vsN_new_size = "<<vsN_new_size<<endl;
    
    cout<<"vsP : "; for(ui i = 0; i < vsP_size; i++) cout<<vsP[i]<<", ";cout<<endl;
    cout<<"vsN : "; for(ui i = 0; i < vsN_size; i++) cout<<vsN[i]<<", ";cout<<endl;
#endif
    
}

void vs_vertex_reduce(ui * vsP, ui & vsP_size, ui * vsN, ui & vsN_size)
{
    int vsP_pt = tau - 2;
    int vsP_nt = tau;
    
    int vsN_pt = tau - 1;
    int vsN_nt = tau - 1;
    
    queue<ui> Q;
    
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        if(p_degree[u] < vsP_pt || n_degree[u] < vsP_nt){
            Q.push(u);
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        if(p_degree[u] < vsN_pt || n_degree[u] < vsN_nt){
            Q.push(u);
        }
    }
    
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        assert(inPN[u]==1 || inPN[u]==2);
        degree[u] = 0;
        p_degree[u] = 0;
        n_degree[u] = 0;

        for(ui i = p_pstart[u]; i < p_pend[u]; i++){
            ui v = p_edges[i];
            if(p_degree[v] > 0){
                assert(inPN[u] == inPN[v]);
                if(inPN[v] == 1){
                    if((p_degree[v]--) == vsP_pt && n_degree[v] >= vsP_nt){
                        Q.push(v);
                    }
                }
                else{
                    if((p_degree[v]--) == vsN_pt && n_degree[v] >= vsN_nt){
                        Q.push(v);
                    }
                }
            }
        }
        for(ui i = n_pstart[u]; i < n_pend[u]; i++){
            ui v = n_edges[i];
            if(n_degree[v] > 0){
                assert(inPN[u] != inPN[v]);
                if(inPN[v] == 1){
                    if((n_degree[v]--) == vsP_nt && p_degree[v] >= vsP_pt){
                        Q.push(v);
                    }
                }
                else{
                    if((n_degree[v]--) == vsN_nt && p_degree[v] >= vsN_pt){
                        Q.push(v);
                    }
                }
            }
        }
        inPN[u] = 0;
    }
    ui vsP_new_size = 0, vsN_new_size = 0;
    for(ui i = 0; i < vsP_size; i++){
        if(inPN[vsP[i]] != 0){
            vsP[vsP_new_size++] = vsP[i];
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        if(inPN[vsN[i]] != 0){
            vsN[vsN_new_size++] = vsN[i];
        }
    }
    vsP_size = vsP_new_size;
    vsN_size = vsN_new_size;
    //update degree
    for(ui i = 0; i < vsP_size; i++)
        degree[vsP[i]] = p_degree[vsP[i]] + n_degree[vsP[i]];
    for(ui i = 0; i < vsN_size; i++)
        degree[vsN[i]] = p_degree[vsN[i]] + n_degree[vsN[i]];
    
#ifdef _DEBUG_
    cout<<"after ve_vertex_reduction."<<endl;
    cout<<"now, vsP_new_size = "<<vsP_new_size<<"  :  "; for(ui i = 0; i < vsP_size; i++) cout<<vsP[i]<<", ";cout<<endl;
    cout<<"now, vsN_new_size = "<<vsN_new_size<<"  :  "; for(ui i = 0; i < vsN_size; i++) cout<<vsN[i]<<", ";cout<<endl;
#endif
    
}

void reduce_to_kcore(ui * vsP, ui & vsP_size, ui * vsN, ui & vsN_size, int k)
{
    queue<ui> Q;
    for(ui i = 0; i < vsP_size; i++){
        if(degree[vsP[i]] < k){
            Q.push(vsP[i]);
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        if(degree[vsN[i]] < k){
            Q.push(vsN[i]);
        }
    }
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        inPN[u] = 0;
        degree[u] = 0;
        for(ui i = p_pstart[u]; i < p_pend[u]; i++){
            ui v = p_edges[i];
            if(degree[v] > 0){
                if((degree[v]--) == k){
                    Q.push(v);
                }
            }
        }
        for(ui i = n_pstart[u]; i < n_pend[u]; i++){
            ui v = n_edges[i];
            if(degree[v] > 0){
                if((degree[v]--) == k){
                    Q.push(v);
                }
            }
        }
    }
    ui vsP_new_size = 0, vsN_new_size = 0;
    for(ui i = 0; i < vsP_size; i++){
        if(inPN[vsP[i]] != 0){
            vsP[vsP_new_size++] = vsP[i];
        }
    }
    for(ui i = 0; i < vsN_size; i++){
        if(inPN[vsN[i]] != 0){
            vsN[vsN_new_size++] = vsN[i];
        }
    }
    
    vsP_size = vsP_new_size;
    vsN_size = vsN_new_size;
    
#ifdef _DEBUG_
    cout<<"after reduce_to_kcore."<<endl;
    cout<<"now, vsP_new_size = "<<vsP_new_size<<"  :  "; for(ui i = 0; i < vsP_size; i++) cout<<vsP[i]<<", ";cout<<endl;
    cout<<"now, vsN_new_size = "<<vsN_new_size<<"  :  "; for(ui i = 0; i < vsN_size; i++) cout<<vsN[i]<<", ";cout<<endl;
#endif

}

void get_degeneracy_order(ui * vs, ui vs_size)
{
    ui cur_max_coreunm = 0;
    for(ui i = 0; i < vs_size; i++) {
        ui idx = i;
        for(ui j = i+1; j < vs_size; j++){
            if(degree[vs[j]] < degree[vs[idx]]){
                idx = j;
            }
        }
        if(idx != i){
            swap(vs[idx], vs[i]);
        }
        ui u = vs[i];
        if(degree[u] > cur_max_coreunm)
            cur_max_coreunm = degree[u];
        vs_core[u] = cur_max_coreunm;
        for(ui j = i+1; j < vs_size; j++){
            ui v = vs[j];
            if(Matrix[trans[u]][trans[v]] != 0){
                assert(degree[u] > 0);
                assert(degree[v] > 0);
                -- degree[u];
                -- degree[v];
            }
        }
    }
#ifdef _DEBUG_
    cout<<"after comp_corenum(), peel sequence and core number for each vertex : "<<endl;
    for(ui i = 0; i < vs_size; i++)
        cout<<vs[i]<<":"<<vs_core[vs[i]]<<", ";
    cout<<endl;
#endif
}

void comp_corenum_and_reduce_to_kcore_by_Matrix(ui * vs, ui & vs_size, int k)
{
    assert(k >= 0);
    ui cur_max_coreunm = 0;
    for(ui i = 0; i < vs_size; i++) {
        ui idx = i;
        for(ui j = i+1; j < vs_size; j++){
            if(degree[vs[j]] < degree[vs[idx]]){
                idx = j;
            }
        }
        if(idx != i){
            swap(vs[idx], vs[i]);
        }
        ui u = vs[i];
        if(degree[u] > cur_max_coreunm)
            cur_max_coreunm = degree[u];
        vs_core[u] = cur_max_coreunm;
        for(ui j = i+1; j < vs_size; j++){
            ui v = vs[j];
            if(Matrix[trans[u]][trans[v]] != 0){
                assert(degree[u] > 0);
                assert(degree[v] > 0);
                -- degree[u];
                -- degree[v];
            }
        }
    }
#ifdef _DEBUG_
    cout<<"after comp_corenum(), peel sequence and core number for each vertex : "<<endl;
    for(ui i = 0; i < vs_size; i++)
        cout<<vs[i]<<":"<<vs_core[vs[i]]<<", ";
    cout<<endl;
#endif
    
    ui new_vs_size = 0;
    for(ui i = 0; i < vs_size; i++){
        if(vs_core[vs[i]] >= k){
            vs[new_vs_size++] = vs[i];
        }
    }
    vs_size = new_vs_size;
#ifdef _DEBUG_
    cout<<"after reduce_to_kcore(), peel sequence and core number for each vertex : "<<endl;
    for(ui i = 0; i < vs_size; i++)
        cout<<vs[i]<<":"<<vs_core[vs[i]]<<", ";
    cout<<endl;
#endif
}

//vs_core
void comp_corenum_and_reduce_to_kcore_by_Matrix(ui * vs, ui & vs_size, int k, ui & suffix_len)
{
    suffix_len = 0;
    ui cur_max_coreunm = 0;
    for(ui i = 0; i < vs_size; i++) {
        ui idx = i;
        for(ui j = i+1; j < vs_size; j++){
            if(degree[vs[j]] < degree[vs[idx]]){
                idx = j;
            }
        }
        if(idx != i){
            swap(vs[idx], vs[i]);
        }
        ui u = vs[i];
        if(degree[u] > cur_max_coreunm)
            cur_max_coreunm = degree[u];
        vs_core[u] = cur_max_coreunm;
        
        if(degree[u] + i + 1 == vs_size){
            suffix_len = 1;
            for(ui j = i+1; j < vs_size; j++){
                vs_core[vs[j]] = cur_max_coreunm;
                suffix_len ++;
            }
            break;
        }
        
        for(ui j = i+1; j < vs_size; j++){
            ui v = vs[j];
            if(Matrix[trans[u]][trans[v]] != 0){
                assert(degree[u] > 0);
                assert(degree[v] > 0);
                -- degree[u];
                -- degree[v];
            }
        }
    }
#ifdef _DEBUG_
    cout<<"after comp_corenum(), peel sequence and core number for each vertex : "<<endl;
    for(ui i = 0; i < vs_size; i++)
        cout<<vs[i]<<":"<<vs_core[vs[i]]<<", ";
    cout<<endl;
#endif
    
    ui new_vs_size = 0;
    for(ui i = 0; i < vs_size; i++){
        if(vs_core[vs[i]] >= k){
            vs[new_vs_size++] = vs[i];
        }
    }
    assert(new_vs_size <= vs_size);
    vs_size = new_vs_size;
#ifdef _DEBUG_
    cout<<"after reduce_to_kcore(), peel sequence and core number for each vertex : "<<endl;
    for(ui i = 0; i < vs_size; i++)
        cout<<vs[i]<<":"<<vs_core[vs[i]]<<", ";
    cout<<endl;
#endif
    //set suffix_idx
    if(vs_size < suffix_len)
        suffix_len = 0;
}

void get_higher_neighbors(ui u, ui * vsP, ui &vsP_size, ui * vsN, ui &vsN_size)
{
    memset(inPN, 0, sizeof(ui)*n);
    vsP_size = 0;
    for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
        vsP[vsP_size++] = p_edges_o[j];
        inPN[p_edges_o[j]] = 1;
    }
    vsN_size = 0;
    for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
        vsN[vsN_size++] = n_edges_o[j];
        inPN[n_edges_o[j]] = 2;
    }
}

void construct_Matrix(ui * vsP, ui vsP_size, ui * vsN, ui vsN_size)
{
    ui idx = 0;
    for(ui i = 0; i < vsP_size; i++){
        trans[vsP[i]] = idx ++;
    }
    for(ui i = 0; i < vsN_size; i++){
        trans[vsN[i]] = idx ++;
    }
    
    assert(idx == (vsP_size + vsN_size));
    
    for(ui i = 0; i < idx; i++)
        for(ui j = 0; j < idx; j++)
            Matrix[i][j] = 0;
    
    for(ui i = 0; i < vsP_size; i++){
        ui u = vsP[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 1){
                Matrix[trans[u]][trans[v]] = 1;
                Matrix[trans[v]][trans[u]] = 1;
            }
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[v] == 2){
                Matrix[trans[u]][trans[v]] = -1;
                Matrix[trans[v]][trans[u]] = -1;
            }
        }
    }
    
    for(ui i = 0; i < vsN_size; i++){
        ui u = vsN[i];
        for(ui j = p_pstart_o[u]; j < p_pstart_o[u+1]; j++){
            ui v = p_edges_o[j];
            if(inPN[v] == 2){
                Matrix[trans[u]][trans[v]] = 1;
                Matrix[trans[v]][trans[u]] = 1;
            }
        }
        for(ui j = n_pstart_o[u]; j < n_pstart_o[u+1]; j++){
            ui v = n_edges_o[j];
            if(inPN[n_edges_o[j]] == 1){
                Matrix[trans[u]][trans[v]] = -1;
                Matrix[trans[v]][trans[u]] = -1;
            }
        }
    }
}

void obtain_degree_Mtau(ui * vs, ui vs_size)
{
    for(ui i = 0; i < vs_size; i++){
        ui u = vs[i];
        degree[u] = 0;
        p_degree[u] = 0;
        n_degree[u] = 0;
    }
    for(ui i = 0; i < vs_size; i++){
        ui u = vs[i];
        for(ui j = i + 1; j < vs_size; j++){
            ui v = vs[j];
            if(Matrix[trans[u]][trans[v]] == 1){
                ++ degree[u]; ++ degree[v];
                ++ p_degree[u]; ++ p_degree[v];
            }
            else if(Matrix[trans[u]][trans[v]] == -1){
                ++ degree[u]; ++ degree[v];
                ++ n_degree[u]; ++ n_degree[v];
            }
        }
    }
    
#ifdef _DEBUG_
    cout<<"each vertex degree by obtain_degree(): "<<endl;
    for(ui i = 0; i < vs_size; i++){
        cout<<"vertex "<<vs[i]<<": degree = "<<degree[vs[i]]<<", p_degree = "<<p_degree[vs[i]]<<", n_degree = "<<n_degree[vs[i]]<<endl;
    }
    cout<<endl;
#endif
}

void obtain_degree(ui * vs, ui vs_size)
{
    for(ui i = 0; i < vs_size; i++) degree[vs[i]] = 0;
    for(ui i = 0; i < vs_size; i++){
        ui u = vs[i];
        for(ui j = i + 1; j < vs_size; j++){
            ui v = vs[j];
            if(Matrix[trans[u]][trans[v]] != 0){
                ++ degree[u];
                ++ degree[v];
            }
        }
    }
#ifdef _DEBUG_
    cout<<"each vertex degree by obtain_degree(): ";
    for(ui i = 0; i < vs_size; i++)
        cout<<degree[vs[i]]<<",";
    cout<<endl;
#endif
}

void obtain_degree_and_reduce(vector<ui> &PL, vector<ui> &PR, vector<ui> &CL, vector<ui> &CR)
{
    int dt = LB - (int)CL.size() - (int)CR.size() - 1;
    if(dt < 1) return;
        
    for(auto u : PL) {degree[u] = 0; }
    for(auto u : PR) {degree[u] = 0; }
    
    for(auto u : PL) {
        for(auto v : PL) if(Matrix[trans[u]][trans[v]] == 1) {++ degree[u];}
        for(auto v : PR) if(Matrix[trans[u]][trans[v]] == -1) {++ degree[u];}
    }
    for(auto u : PR) {
        for(auto v : PL) if(Matrix[trans[u]][trans[v]] == -1) {++ degree[u];}
        for(auto v : PR) if(Matrix[trans[u]][trans[v]] == 1) {++ degree[u];}
    }
    
    for(auto e : PL) bit_del[e] = 1;
    for(auto e : PR) bit_del[e] = 2;
    
    vector<ui> vs;
    vs.insert(vs.end(), PL.begin(), PL.end());
    vs.insert(vs.end(), PR.begin(), PR.end());
    ui vs_size = vs.size();
    
    ui cur_max_coreunm = 0;
    for(ui i = 0; i < vs_size; i++) {
        ui idx = i;
        for(ui j = i+1; j < vs_size; j++){
            if(degree[vs[j]] < degree[vs[idx]]){
                idx = j;
            }
        }
        if(idx != i){
            swap(vs[idx], vs[i]);
        }
        ui u = vs[i];
        if(degree[u] > cur_max_coreunm)
            cur_max_coreunm = degree[u];
        vs_core[u] = cur_max_coreunm;
        
        for(ui j = i+1; j < vs_size; j++){
            ui v = vs[j];
            if(Matrix[trans[u]][trans[v]] != 0){
                assert(degree[u] > 0);
                assert(degree[v] > 0);
                -- degree[u];
                -- degree[v];
            }
        }
    }
    PL.clear(); PR.clear();
    for(ui i = 0; i < vs.size(); i++) {
        ui u = vs[i];
        if(vs_core[u] >= dt) {
            if(bit_del[u] == 1) PL.push_back(u);
            else {
                assert(bit_del[u] == 2);
                PR.push_back(u);
            }
        }
    }
}

ui degeneracy_order_on_Matrix(vector<ui> & vs)
{
    ui cur_core_num = 0;
    for(ui i = 0; i < vs.size(); i++){
        ui idx = i;
        for(ui j = i+1; j < vs.size(); j++){
            if(degree[vs[j]] < degree[vs[i]])
                idx = j;
        }
        if(idx != i) swap(vs[idx], vs[i]);
        ui u = vs[i]; // u has min degree
        if(degree[u] > cur_core_num) cur_core_num = degree[u];
        vs_core[u] = cur_core_num;
        for(ui j = i+1; j < vs.size(); j++){
            if(Matrix[trans[u]][trans[vs[j]]] == 1 || Matrix[trans[u]][trans[vs[j]]] == -1){
                -- degree[u];
                -- degree[vs[j]];
            }
        }
    }
    return cur_core_num;
}

void shrink_vs(vector<ui> & vs, ui & vs_size, int threshold)
{
    for(ui i = 0; i < vs.size(); i++){
        if(vs_core[vs[i]] >= threshold){
            vs[vs_size++] = vs[i];
        }
    }
}

ui color_based_UB_Matrix(ui * vs, ui vs_size)
{
    ui max_color = 0;
    for(ui i = 0; i < vs_size; i++){
        vs_color[vs[i]] = vs_size;
    }
    ui * vis = new ui[vs_size];
    memset(vis, 0, sizeof(ui)*vs_size);
    for(ui i = vs_size; i > 0; i--){
        ui u = vs[i-1];
        for(ui j = vs_size; j > 0; j--){
            ui v = vs[j-1];
            if(u == v) continue;
            if(Matrix[trans[u]][trans[v]] == 1 || Matrix[trans[u]][trans[v]] == -1){
                ui c = vs_color[v];
                if(c != vs_size) {vis[c] = 1;}
            }
        }
        for(ui j = 0;; j++){
            if(!vis[j]){
                vs_color[u] = j;
                if(j > max_color) max_color = j;
                break;
            }
        }
        for(ui j = vs_size; j > 0; j--){
            ui v = vs[j-1];
            if(u == v) continue;
            if(Matrix[trans[u]][trans[v]] == 1 || Matrix[trans[u]][trans[v]] == -1){
                ui c = vs_color[v];
                if(c != vs_size) {vis[c] = 0;}
            }
        }
    }
    assert(max_color < vs_size);
    delete [] vis;
    return max_color+1;
}

void mDC(pair<vector<ui>, vector<ui>> cur_C, ui * vs, ui vs_size, int tp, int tn)
{
    if(vs_size == 0 && tp == 0 && tn == 0){
        if(psz(cur_C) > psz(cur_MC)) cur_MC = cur_C; return;
    }
    
    if(psz(cur_C) + vs_size <= psz(cur_MC)) return;
    
    obtain_degree(vs, vs_size);

    ui suffix_len;
    comp_corenum_and_reduce_to_kcore_by_Matrix(vs, vs_size, mav(psz(cur_MC) + 1 - psz(cur_C) - 1, 0), suffix_len);
    assert(suffix_len >= 0 && suffix_len <= vs_size);
    if(vs_size == 0) return;
    
    pair<vector<ui>, vector<ui>> sfx_C(cur_C);
    for(ui i = vs_size - suffix_len; i < vs_size; i++){
        ui u = vs[i];
        assert(inPN[u] == 1 || inPN[u] == 2);
        if(inPN[u] == 1) sfx_C.first.push_back(u);
        else sfx_C.second.push_back(u);
    }
    if(sfx_C.first.size() >= tau && sfx_C.second.size() >= tau && psz(sfx_C) > psz(cur_MC)) cur_MC = sfx_C;
    
#ifdef _COLORUB_
    int coUB = color_based_UB_Matrix(vs, vs_size);
    if(coUB < mav(psz(cur_MC) + 1 - psz(cur_C), 0)) return;
#endif
    
    int p_cand = 0, n_cand = 0;
    for(ui i = 0; i < vs_size; i++){
        assert(inPN[vs[i]] == 1 || inPN[vs[i]] == 2);
        if(inPN[vs[i]] == 1) ++ p_cand;
        else ++ n_cand;
    }
    if(p_cand < tp || n_cand < tn) return;
    
    if(tp > 0  && tn > 0){
        assert(p_cand > 0); assert(n_cand > 0);
        if(p_cand <= n_cand){ // first select from P
            vector<ui> tmpvec(vs_size);
            for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
            ui n_idx = 0;
            ui p_idx = n_cand;
            for(ui i = 0; i < vs_size; i++){
                ui u = tmpvec[i];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) vs[p_idx++] = u;
                else vs[n_idx++] = u;
            }
            assert(p_idx == vs_size); assert(n_idx == n_cand);

            vector<int> pivot_indicator(vs_size, 1);
            vector<int> exp_indicator(vs_size, 1);
            
            bool pivot_f = true;
            for(ui i = vs_size; i > 0; i--){
                ui u = vs[i-1];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 2) continue;
                if(pivot_indicator[i-1] == 0) continue;
                if(pivot_f){
                    for(ui j = 0; j < vs_size; j++){
                        ui v = vs[j];
                        if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                    }
                    pivot_f = false;
                }
                vector<ui> next_g;
                for(ui j = vs_size; j > 0; j--){
                    ui v = vs[j-1];
                    if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
                }
                pair<vector<ui>, vector<ui>> next_C(cur_C);
                int new_tp, new_tn;
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1){
                    new_tp = mav(tp-1, 0);
                    new_tn = tn;
                    next_C.first.push_back(u);
                }
                else{
                    new_tp = tp;
                    new_tn = mav(tn-1, 0);
                    next_C.second.push_back(u);
                }
                mDC(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
                exp_indicator[i-1] = 0;
            }
        }
        else{ // first select from N
            vector<ui> tmpvec(vs_size);
            for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
            ui n_idx = p_cand;
            ui p_idx = 0;
            for(ui i = 0; i < vs_size; i++){
                ui u = tmpvec[i];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) vs[p_idx++] = u;
                else vs[n_idx++] = u;
            }
            assert(p_idx == p_cand); assert(n_idx == vs_size);

            vector<int> pivot_indicator(vs_size, 1);
            vector<int> exp_indicator(vs_size, 1);
            
            bool pivot_f = true;
            for(ui i = vs_size; i > 0; i--){
                ui u = vs[i-1];
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1) continue;
                if(pivot_indicator[i-1] == 0) continue;
                
                if(pivot_f){
                    for(ui j = 0; j < vs_size; j++){
                        ui v = vs[j];
                        if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                    }
                    pivot_f = false;
                }
                
                vector<ui> next_g;
                for(ui j = vs_size; j > 0; j--){
                    ui v = vs[j-1];
                    if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
                }
                
                pair<vector<ui>, vector<ui>> next_C(cur_C);
                int new_tp, new_tn;
                assert(inPN[u] == 1 || inPN[u] == 2);
                if(inPN[u] == 1){
                    new_tp = mav(tp-1, 0);
                    new_tn = tn;
                    next_C.first.push_back(u);
                }
                else{
                    new_tp = tp;
                    new_tn = mav(tn-1, 0);
                    next_C.second.push_back(u);
                }
                mDC(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
                exp_indicator[i-1] = 0;
            }
        }
    }
    else if (tp > 0 && tn == 0){
        vector<ui> tmpvec(vs_size);
        for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
        ui n_idx = 0;
        ui p_idx = n_cand;
        for(ui i = 0; i < vs_size; i++){
            ui u = tmpvec[i];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) vs[p_idx++] = u;
            else vs[n_idx++] = u;
        }
        assert(p_idx == vs_size); assert(n_idx == n_cand);
        
        vector<int> pivot_indicator(vs_size, 1);
        vector<int> exp_indicator(vs_size, 1);
        
        bool pivot_f = true;
        for(ui i = vs_size; i > 0; i--){
            ui u = vs[i-1];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 2) continue;
            if(pivot_indicator[i-1] == 0) continue;
            if(pivot_f){
                for(ui j = 0; j < vs_size; j++){
                    ui v = vs[j];
                    if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                }
                pivot_f = false;
            }
            
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
            }
            
            pair<vector<ui>, vector<ui>> next_C(cur_C);
            int new_tp, new_tn;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                new_tp = mav(tp-1, 0);
                new_tn = tn;
                next_C.first.push_back(u);
            }
            else{
                new_tp = tp;
                new_tn = mav(tn-1, 0);
                next_C.second.push_back(u);
            }
            mDC(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
        }
    }
    else if (tp == 0 && tn > 0){
        vector<ui> tmpvec(vs_size);
        for(ui i = 0; i < vs_size; i++) tmpvec[i] = vs[i];
        ui n_idx = p_cand;
        ui p_idx = 0;
        for(ui i = 0; i < vs_size; i++){
            ui u = tmpvec[i];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) vs[p_idx++] = u;
            else vs[n_idx++] = u;
        }
        assert(p_idx == p_cand); assert(n_idx == vs_size);

        vector<int> pivot_indicator(vs_size, 1);
        vector<int> exp_indicator(vs_size, 1);
        
        bool pivot_f = true;
        for(ui i = vs_size; i > 0; i--){
            ui u = vs[i-1];
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1) continue;
            if(pivot_indicator[i-1] == 0) continue;
            if(pivot_f){
                for(ui j = 0; j < vs_size; j++){
                    ui v = vs[j];
                    if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
                }
                pivot_f = false;
            }
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
            }

            pair<vector<ui>, vector<ui>> next_C(cur_C);
            int new_tp, new_tn;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                new_tp = mav(tp-1, 0);
                new_tn = tn;
                next_C.first.push_back(u);
            }
            else{
                new_tp = tp;
                new_tn = mav(tn-1, 0);
                next_C.second.push_back(u);
            }
            mDC(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
        }
    }
    else{
        assert(tp == 0 && tn == 0);
        vector<int> pivot_indicator(vs_size, 1);
        vector<int> exp_indicator(vs_size, 1);
        
        for(ui i = vs_size; i > 0; i--){
            ui u = vs[i-1];
            if(pivot_indicator[i-1] == 0) continue;
            for(ui j = 0; j < vs_size; j++){
                ui v = vs[j];
                if(Matrix[trans[u]][trans[v]] != 0) pivot_indicator[j] = 0;
            }
            vector<ui> next_g;
            for(ui j = vs_size; j > 0; j--){
                ui v = vs[j-1];
                if(Matrix[trans[u]][trans[v]] != 0 && exp_indicator[j-1] == 1) next_g.push_back(v);
            }
            pair<vector<ui>, vector<ui>> next_C(cur_C);
            int new_tp, new_tn;
            assert(inPN[u] == 1 || inPN[u] == 2);
            if(inPN[u] == 1){
                new_tp = mav(tp-1, 0);
                new_tn = tn;
                next_C.first.push_back(u);
            }
            else{
                new_tp = tp;
                new_tn = mav(tn-1, 0);
                next_C.second.push_back(u);
            }
            mDC(next_C, next_g.data(), next_g.size(), new_tp, new_tn);
            exp_indicator[i-1] = 0;
        }
    }
}

void find_MSBC()
{
    ui delv_count = 0;
    bit_del = new ui[n];
    memset(bit_del, 0, sizeof(ui)*n);
    vertex_reduction(delv_count, bit_del); //vertex reduction
    shrink_on_reduced_v(bit_del);
    if(n == 0) return;
    heu_MSBC_max_deg_inturn_find_one_stop(1); //find heuristic MSBC
    degeneracy_order();
    shrink_and_orient_graph(); //shrink and orient the remaining subgraph
    ui tmp_m = 0;
    for(ui i = 0; i < n; i++){
        tmp_m += p_pstart_o[i+1] - p_pstart_o[i];
        tmp_m += n_pstart_o[i+1] - n_pstart_o[i];
    }
    vector<ui> vsP(d_MAX);
    ui vsP_size;
    vector<ui> vsN(d_MAX);
    ui vsN_size;
    inPN = new ui[n];
    vs_core = new ui[n];
    vs_color = new ui[n];
    Matrix = new int*[max_core];
    for(int i = 0; i < max_core; i++) Matrix[i] = new int[max_core];
    trans = new ui[n];
    CntEgoNet = 0;
    num_of_ori_edges = 0;
    num_of_now_edges = 0;
    num_of_after_reduction_now_edges = 0;
    for(ui i = n; i > 0; i--){
        ui u = i - 1;
        if(n - i < psz(cur_MC)) continue;
        if(core[u] < psz(cur_MC)) break;
        get_higher_neighbors(u, vsP.data(), vsP_size, vsN.data(), vsN_size);
        if(vsP_size < tau - 1 || vsN_size < tau) continue;
        ui tmp_ori_edges, tmp_now_edges;
        //note: this subgraph is stored in p_pstart p_edges and n_pstart n_edges
        //must use p_pend and n_pend to get the index range of a vertex's neighbors
        construct_induced_subgraph(vsP.data(), vsP_size, vsN.data(), vsN_size, tmp_ori_edges, tmp_now_edges);
        vs_vertex_reduce(vsP.data(), vsP_size, vsN.data(), vsN_size);
        if(vsP_size == 0 && vsN_size == 0) continue;
        reduce_to_kcore(vsP.data(), vsP_size, vsN.data(), vsN_size, mav(psz(cur_MC) - 1, tau*2 - 2));
        if(vsP_size == 0 && vsN_size == 0) continue;
        construct_Matrix(vsP.data(), vsP_size, vsN.data(), vsN_size);
        vector<ui> vs;
        for(ui i = 0; i < vsP_size; i++) vs.push_back(vsP[i]);
        for(ui i = 0; i < vsN_size; i++) vs.push_back(vsN[i]);
        ui tm = 0;
        for(ui i = 0; i < vs.size(); i++) for(ui j = i+1; j< vs.size(); j++)
            if(Matrix[trans[vs[i]]][trans[vs[j]]] == 1 || Matrix[trans[vs[i]]][trans[vs[j]]] == -1) ++ tm;
        if(color_based_UB_Matrix(vs.data(), vs.size()) < psz(cur_MC) ) continue;
        pair<vector<ui>, vector<ui>> cur_C;
        cur_C.first.push_back(u);
        mDC(cur_C, vs.data(), vs.size(), tau - 1, tau);
        ++ CntEgoNet;
        num_of_ori_edges += tmp_ori_edges;
        num_of_now_edges += tmp_now_edges;
        num_of_after_reduction_now_edges += tm;
    }
}

void delete_memo()
{
    if(p_pstart != nullptr){
        delete [] p_pstart;
        p_pstart = nullptr;
    }
    if(p_edges != nullptr){
        delete [] p_edges;
        p_edges = nullptr;
    }
    if(p_pend != nullptr){
        delete [] p_pend;
        p_pend = nullptr;
    }
    if(n_pstart != nullptr)
    {
        delete [] n_pstart;
        n_pstart = nullptr;
    }
    if(n_edges != nullptr){
        delete [] n_edges;
        n_edges = nullptr;
    }
    if(n_pend != nullptr){
        delete [] n_pend;
        n_pend = nullptr;
    }
    
    if(p_pstart_o != nullptr){
        delete [] p_pstart_o;
        p_pstart_o = nullptr;
    }
    if(p_edges_o != nullptr){
        delete [] p_edges_o;
        p_edges_o = nullptr;
    }
    if(n_pstart_o != nullptr){
        delete [] n_pstart_o;
        n_pstart_o = nullptr;
    }
    if(n_edges_o != nullptr){
        delete [] n_edges_o;
        n_edges_o = nullptr;
    }
    
    if(p_pstart != nullptr){
        delete [] degree;
        degree = nullptr;
    }
    if(p_pstart != nullptr){
        delete [] p_degree;
        p_degree = nullptr;
    }
    if(p_pstart != nullptr){
        delete [] n_degree;
        n_degree = nullptr;
    }
    if(core != nullptr){
        delete [] core;
        core = nullptr;
    }
    if(peel_s != nullptr){
        delete [] peel_s;
        peel_s = nullptr;
    }
    if(inPN != nullptr){
        delete [] inPN;
        inPN = nullptr;
    }
    if(vs_core != nullptr){
        delete [] vs_core;
        vs_core = nullptr;
    }
    if(vs_color != nullptr){
        delete [] vs_color;
        vs_color = nullptr;
    }
    for(int i = 0; i < d_MAX; i++) if(Matrix[i] != nullptr){
        delete [] Matrix[i];
        Matrix[i] = nullptr;
    }
    if(trans != nullptr){
        delete [] trans;
        trans = nullptr;
    }
    if(bit_del != nullptr){
        delete [] bit_del;
        bit_del = nullptr;
    }
    if(PNdeg != nullptr){
        delete [] PNdeg;
        PNdeg = nullptr;
    }
    if(mapping != nullptr){
        delete [] mapping;
        mapping = nullptr;
    }
    if(ori_id != nullptr){
        delete [] ori_id;
        ori_id = nullptr;
    }
    
    //delete intermediate subgraph
    if(inter_p_pstart != nullptr){
        delete [] inter_p_pstart;
        inter_p_pstart = nullptr;
    }
    if(inter_p_edges != nullptr){
        delete [] inter_p_edges;
        inter_p_edges = nullptr;
    }
    if(inter_n_pstart != nullptr){
        delete [] inter_n_pstart;
        inter_n_pstart = nullptr;
    }
    if(inter_n_edges != nullptr){
        delete [] inter_n_edges;
        inter_n_edges = nullptr;
    }
    if(inter_degree != nullptr){
        delete [] inter_degree;
        inter_degree = nullptr;
    }
    if(inter_p_degree != nullptr){
        delete [] inter_p_degree;
        inter_p_degree = nullptr;
    }
    if(inter_n_degree != nullptr){
        delete [] inter_n_degree;
        inter_n_degree = nullptr;
    }
}

void vertex_reduction_mix(ui & del_count, ui * bit_del)
{
    if(tau <= 1) {cout<<"\t tau should be at least 2"<<endl; exit(1); }
    int pt = tau - 1;
    int nt = tau;
    int degt = LB - 1;
    queue<ui> Q;
    for(ui i = 0; i < n; i++) if(p_degree[i] < pt || n_degree[i] < nt ) Q.push(i);
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        ++ del_count;
        bit_del[u] = 1;
        for(ui i = p_pstart[u]; i < p_pstart[u+1]; i++){
            ui v = p_edges[i];
            if((p_degree[v]--) == pt && n_degree[v] >= nt){
                Q.push(v);
            }
        }
        for(ui i = n_pstart[u]; i < n_pstart[u+1]; i++){
            ui v = n_edges[i];
            if((n_degree[v]--) == nt && p_degree[v] >= pt){
                Q.push(v);
            }
        }
    }
}

void build_matrix_PL_PR_XL_XR(vector<ui> PL, vector<ui> PR, vector<ui> XL, vector<ui> XR, ui & matrix_idx)
{
    matrix_idx = 0;
    for(auto e : PL) trans[e] = matrix_idx ++; for(auto e : PR) trans[e] = matrix_idx ++;
    for(auto e : XL) trans[e] = matrix_idx ++; for(auto e : XR) trans[e] = matrix_idx ++;
    for(auto u : PL) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++) {
            ui v = inter_p_edges[i];
            if(inLR[v] == 1) {
                Matrix[trans[u]][trans[v]] = 1;
            }
        }
        for(ui i = inter_n_pstart[u]; i < inter_n_pstart[u+1]; i++) {
            ui v = inter_n_edges[i];
            if(inLR[v] == 2) {
                Matrix[trans[u]][trans[v]] = -1;
                Matrix[trans[v]][trans[u]] = -1;
            }
        }
    }
    for(auto u : XL) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++) {
            ui v = inter_p_edges[i];
            if(inLR[v] == 1) {
                Matrix[trans[u]][trans[v]] = 1;
            }
        }
        for(ui i = inter_n_pstart[u]; i < inter_n_pstart[u+1]; i++) {
            ui v = inter_n_edges[i];
            if(inLR[v] == 2) {
                Matrix[trans[u]][trans[v]] = -1;
                Matrix[trans[v]][trans[u]] = -1;
            }
        }
    }
    for(auto u : PR) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++) {
            ui v = inter_p_edges[i];
            if(inLR[v] == 2) {
                Matrix[trans[u]][trans[v]] = 1;
            }
        }
    }
    for(auto u : XR) {
        for(ui i = inter_p_pstart[u]; i < inter_p_pstart[u+1]; i++) {
            ui v = inter_p_edges[i];
            if(inLR[v] == 2) {
                Matrix[trans[u]][trans[v]] = 1;
            }
        }
    }
}

void obtain_deg_inP(vector<ui> &XL, vector<ui> &PL, vector<ui> &XR, vector<ui> &PR)
{
    for(auto u : XL) {p_degree[u] = 0;}
    for(auto u : PL) {p_degree[u] = 0;}
    for(auto u : XR) {p_degree[u] = 0;}
    for(auto u : PR) {p_degree[u] = 0;}
    
    for(auto u : XL) {
        for(auto v : PL) if(Matrix[trans[u]][trans[v]] == 1) {++ p_degree[u]; }
        for(auto v : PR) if(Matrix[trans[u]][trans[v]] == -1) {++ p_degree[u]; }
    }
    for(auto u : PL) {
        for(auto v : PL) if(Matrix[trans[u]][trans[v]] == 1) {++ p_degree[u]; }
        for(auto v : PR) if(Matrix[trans[u]][trans[v]] == -1) {++ p_degree[u]; }
    }
    for(auto u : XR) {
        for(auto v : PL) if(Matrix[trans[u]][trans[v]] == -1) {++ p_degree[u]; }
        for(auto v : PR) if(Matrix[trans[u]][trans[v]] == 1) {++ p_degree[u]; }
    }
    for(auto u : PR) {
        for(auto v : PL) if(Matrix[trans[u]][trans[v]] == -1) {++ p_degree[u]; }
        for(auto v : PR) if(Matrix[trans[u]][trans[v]] == 1) {++ p_degree[u]; }
    }
}

ui pivot_selection(vector<ui> &XL, vector<ui> &PL, vector<ui> &XR, vector<ui> &PR)
{
    int tmp_deg = -1;
    ui pivot;
    for(auto u : XL) {
        int d = p_degree[u];
        if( d > tmp_deg) {
            pivot = u;
            tmp_deg = d;
        }
    }
    for(auto u : PL) {
        int d = p_degree[u];
        if(d > tmp_deg) {
            pivot = u;
            tmp_deg = d;
        }
    }
    for(auto u : XR) {
        int d = p_degree[u];
        if(d > tmp_deg) {
            pivot = u;
            tmp_deg = d;
        }
    }
    for(auto u : PR) {
        int d = p_degree[u];
        if(d > tmp_deg) {
            pivot = u;
            tmp_deg = d;
        }
    }
    assert(tmp_deg > -1);
    return pivot;
}

void MBCEG_enum(vector<ui> CL, vector<ui> CR, vector<ui> PL, vector<ui> PR, vector<ui> XL, vector<ui> XR)
{
    if(PL.empty() && PR.empty() && XL.empty() && XR.empty()) {
        if(CL.size() >= tau && CR.size() >= tau && CL.size() + CR.size() >= LB) {
            results.push_back(make_pair(CL, CR));
            ++ result_num;
        }
    }
    if(PL.empty() && PR.empty()) return;
#ifdef _ET1_
    if(CL.size() + PL.size() < tau || CR.size() + PR.size() < tau) return;
#endif
#ifdef _ET2_
    //early termination by checking maximality
    bool find_one_links_all = false;
    for(auto u : XL) {
        bool link_all = true;
        for(auto v : PL) {
            if(Matrix[trans[u]][trans[v]] == 0) {
                link_all = false;
                break;
            }
        }
        if(link_all == false) continue;
        for(auto v : PR) {
            if(Matrix[trans[u]][trans[v]] == 0) {
                link_all = false;
                break;
            }
        }
        if(link_all == true) {
            find_one_links_all = true;
            break;
        }
    }
    if(find_one_links_all == true) return;
    assert(find_one_links_all == false);
    for(auto u : XR) {
        bool link_all = true;
        for(auto v : PL) {
            if(Matrix[trans[u]][trans[v]] == 0) {
                link_all = false;
                break;
            }
        }
        if(link_all == false) continue;
        for(auto v : PR) {
            if(Matrix[trans[u]][trans[v]] == 0) {
                link_all = false;
                break;
            }
        }
        if(link_all == true) {
            find_one_links_all = true;
            break;
        }
    }
    if(find_one_links_all == true) return;
    assert(find_one_links_all == false);
#endif
#ifdef _ET1_
    if(CL.size() + PL.size() < tau || CR.size() + PR.size() < tau) return;
#endif
    vector<ui> PL_pivot_indicator(PL.size(), 1);
    vector<ui> PR_pivot_indicator(PR.size(), 1);
    vector<ui> PL_exp_indicator(PL.size(), 1);
    vector<ui> PR_exp_indicator(PR.size(), 1);
#ifdef _Pivot_
    //obtain degree for vertices from XLXRPLPR in PLPR: reuse p_degree[] to store them
    obtain_deg_inP(XL, PL, XR, PR);
    ui ustar = pivot_selection(XL, PL, XR, PR);
    for(ui i = 0; i < PL.size(); i++) if(Matrix[trans[ustar]][trans[PL[i]]] != 0) PL_pivot_indicator[i] = 0;
    for(ui i = 0; i < PR.size(); i++) if(Matrix[trans[ustar]][trans[PR[i]]] != 0) PR_pivot_indicator[i] = 0;
#endif
    
    for(ui i = 0; i < PL.size(); i++) {
        if(PL_pivot_indicator[i] == 0) continue;
        ui u = PL[i];
        vector<ui> new_CL = CL;
        new_CL.push_back(u);
        vector<ui> new_CR = CR;
        vector<ui> new_PL;
        for(ui j = 0; j < PL.size(); j++) {
            ui v = PL[j];
            if(Matrix[trans[u]][trans[v]] == 1 && PL_exp_indicator[j] == 1) new_PL.push_back(v);
        }
        vector<ui> new_PR;
        for(auto v : PR) {
            if(Matrix[trans[u]][trans[v]] == -1) new_PR.push_back(v);
        }
        vector<ui> new_XL;
        for(auto v : XL) {
            if(Matrix[trans[u]][trans[v]] == 1) new_XL.push_back(v);
        }
        vector<ui> new_XR;
        for(auto v : XR) {
            if(Matrix[trans[u]][trans[v]] == -1) new_XR.push_back(v);
        }
        MBCEG_enum(new_CR, new_CL, new_PR, new_PL, new_XR, new_XL);
        XL.push_back(u);
        PL_exp_indicator[i] = 0;
    }
    
    for(ui i = 0; i < PR.size(); i++) {
        if(PR_pivot_indicator[i] == 0) continue;
        ui u = PR[i];
        vector<ui> new_CL = CL;
        vector<ui> new_CR = CR;
        new_CR.push_back(u);
        vector<ui> new_PL;
        for(ui j = 0; j < PL.size(); j++) {
            ui v = PL[j];
            if(Matrix[trans[u]][trans[v]] == -1 && PL_exp_indicator[j] == 1) new_PL.push_back(v);
        }
        vector<ui> new_PR;
        for(ui j = 0; j < PR.size(); j++) {
            ui v = PR[j];
            if(Matrix[trans[u]][trans[v]] == 1 && PR_exp_indicator[j] == 1) new_PR.push_back(v);
        }
        vector<ui> new_XL;
        for(auto v : XL) {
            if(Matrix[trans[u]][trans[v]] == -1) new_XL.push_back(v);
        }
        vector<ui> new_XR;
        for(auto v : XR) {
            if(Matrix[trans[u]][trans[v]] == 1) new_XR.push_back(v);
        }
        MBCEG_enum(new_CR, new_CL, new_PR, new_PL, new_XR, new_XL);
        XR.push_back(u);
        PR_exp_indicator[i] = 0;
    }
}

void degree_based_vertex_reduction_mix(vector<ui> &XL, vector<ui> &PL, vector<ui> &XR, vector<ui> &PR)
{
    int L_pt = tau - 2;
    int L_nt = tau;
    int R_pt = tau - 1;
    int R_nt = tau - 1;
    int degt = LB - 2;
    memset(bit_del, 0, sizeof(ui) * inter_n);
    queue<ui> Q;
    for(auto u : XL) if(degree[u] < degt || p_degree[u] < L_pt || n_degree[u] < L_nt) {
        Q.push(u);
        bit_del[u] = 1;
    }
    for(auto u : PL) if(degree[u] < degt || p_degree[u] < L_pt || n_degree[u] < L_nt) {
        Q.push(u);
        bit_del[u] = 1;
    }
    for(auto u : XR) if(degree[u] < degt || p_degree[u] < R_pt || n_degree[u] < R_nt) {
        Q.push(u);
        bit_del[u] = 1;
    }
    for(auto u : PR) if(degree[u] < degt || p_degree[u] < R_pt || n_degree[u] < R_nt) {
        Q.push(u);
        bit_del[u] = 1;
    }
    while (!Q.empty()) {
        ui u = Q.front();
        Q.pop();
        if(inLR[u] == 1){
            for(ui i = p_pstart[u]; i < p_pend[u]; i++) {
                ui v = p_edges[i];
                if(bit_del[v] == 1) continue;
                assert(degree[v] > 0); assert(p_degree[v] > 0);
                -- p_degree[v];
                -- degree[v];
                assert(inLR[v] == 1);
                if(p_degree[v] < L_pt || degree[v] < degt) {
                    Q.push(v);
                    bit_del[v] = 1;
                }
            }
            for(ui i = n_pstart[u]; i < n_pend[u]; i++) {
                ui v = n_edges[i];
                if(bit_del[v] == 1) continue;
                assert(degree[v] > 0); assert(n_degree[v] > 0);
                -- n_degree[v];
                -- degree[v];
                assert(inLR[v] == 2);
                if(n_degree[v] < R_nt || degree[v] < degt) {
                    Q.push(v);
                    bit_del[v] = 1;
                }
            }
        }
        else {
            assert(inLR[u] == 2);
            for(ui i = p_pstart[u]; i < p_pend[u]; i++) {
                ui v = p_edges[i];
                if(bit_del[v] == 1) continue;
                assert(degree[v] > 0); assert(p_degree[v] > 0);
                -- p_degree[v];
                -- degree[v];
                assert(inLR[v] == 2);
                if(p_degree[v] < R_pt || degree[v] < degt) {
                    Q.push(v);
                    bit_del[v] = 1;
                }
            }
            for(ui i = n_pstart[u]; i < n_pend[u]; i++) {
                ui v = n_edges[i];
                if(bit_del[v] == 1) continue;
                assert(degree[v] > 0); assert(n_degree[v] > 0);
                -- n_degree[v];
                -- degree[v];
                assert(inLR[v] == 1);
                if(n_degree[v] < L_nt || degree[v] < degt) {
                    Q.push(v);
                    bit_del[v] = 1;
                }
            }
        }
    }
    ui idx = 0; vector<ui>::iterator it = XL.begin();
    for(ui i = 0; i < XL.size(); i++) {
        if(bit_del[XL[i]] == 0) {
            XL[idx++] = XL[i]; ++ it;
        }
        else inLR[XL[i]] = 0;
    }
    XL.erase(it, XL.end());
    
    idx = 0; it = PL.begin();
    for(ui i = 0; i < PL.size(); i++) {
        if(bit_del[PL[i]] == 0) {
            PL[idx++] = PL[i]; ++ it;
        }
        else inLR[PL[i]] = 0;
    }
    PL.erase(it, PL.end());
    
    idx = 0; it = XR.begin();
    for(ui i = 0; i < XR.size(); i++) {
        if(bit_del[XR[i]] == 0) {
            XR[idx++] = XR[i]; ++ it;
        }
        else inLR[XR[i]] = 0;
    }
    XR.erase(it, XR.end());
    
    idx = 0; it = PR.begin();
    for(ui i = 0; i < PR.size(); i++) {
        if(bit_del[PR[i]] == 0) {
            PR[idx++] = PR[i]; ++ it;
        }
        else inLR[PR[i]] = 0;
    }
    PR.erase(it, PR.end());
}

void MBCEG()
{
    assert(psz(cur_MC) == 0);
    find_MSBC();
    LB = mav(psz(cur_MC) - alpha, 2*tau);
    ui now_m = 0;
    for(ui i = 0; i < inter_n; i++) now_m += inter_degree[i];
    assert(now_m%2 == 0); now_m /= 2;
    d_MAX = 0; for(ui i = 0; i < inter_n; i++) if(inter_degree[i] > d_MAX) d_MAX = inter_degree[i];
    cout<<"\tMSBC size = "<<psz(cur_MC)<<", LB = "<<LB<<", inter_n = "<<inter_n<<", m = "<<now_m<<", d_MAX = "<<d_MAX<<endl;
    for(int i = 0; i < max_core; i++) if(Matrix[i] != nullptr){ delete [] Matrix[i]; Matrix[i] = nullptr; }
    Matrix = new int*[d_MAX]; for(int i = 0; i < d_MAX; i++) Matrix[i] = new int[d_MAX];
    for(ui i = 0; i < d_MAX; i++) memset(Matrix[i], 0, sizeof(int)*d_MAX);
    if(trans != nullptr) { delete [] trans; trans = nullptr; }
    trans = new ui[inter_n];
    if(vs_core != nullptr) { delete [] vs_core; vs_core = nullptr; }
    vs_core = new ui[inter_n];
#ifndef _VRandOrder_
    vector<ui> x;
    for(ui i = 0; i < inter_n; i++) x.push_back(peel_s[i]);
    ui j = 0;
    for(int i = inter_n-1; i >= 0; i--) {peel_s[j++] = x[i];}
#endif
    ui * rid = core; //record vertex ranking, i.e., rid[vertexid] = ranking in peel_s
    for(ui i = 0; i < inter_n; i ++) rid[peel_s[i]] = i;
    inLR = new ui[inter_n]; memset(inLR, 0, sizeof(ui)*inter_n); //indicate v in L (1) or R (2)
    for(ui i = 0; i < inter_n; i++) {
        ui u = peel_s[i];
        if(inter_core[u] < LB-1) continue;
        vector<ui> CL, CR;
        CL.push_back(u);
        vector<ui> PL, XL;
        for(ui j = inter_p_pstart[u]; j < inter_p_pstart[u+1]; j++) {
            ui v = inter_p_edges[j];
            if (inter_core[v] < LB-1) continue;
            if(rid[v] < rid[u]) XL.push_back(v);
            else { assert(rid[v] > rid[u]); PL.push_back(v); }
            inLR[v] = 1; //v is a positive neighbor of u, in PL or XL
        }
        vector<ui> PR, XR;
        for(ui j = inter_n_pstart[u]; j < inter_n_pstart[u+1]; j++) {
            ui v = inter_n_edges[j];
            if (inter_core[v] < LB-1) continue;
            if(rid[v] < rid[u]) XR.push_back(v);
            else { assert(rid[v] > rid[u]); PR.push_back(v); }
            inLR[v] = 2; //v is a negative neighbor of u, in PR or XR
        }
        if(PL.size() < tau - 1 || PR.size() < tau || PL.size() + PR.size() < LB - 1) {
            for(auto e : PL) inLR[e] = 0; for(auto e : XL) inLR[e] = 0;
            for(auto e : PR) inLR[e] = 0; for(auto e : XR) inLR[e] = 0;
            continue;
        }
#ifdef _egoN_vr_
        //materialize the subgraph induced by u's neighbors
        construct_induced_subgraph(XL, PL, XR, PR);
        degree_based_vertex_reduction_mix(XL, PL, XR, PR);
        if(PL.size() < tau - 1 || PR.size() < tau || PL.size() + PR.size() < LB - 1) {
            for(auto e : PL) inLR[e] = 0; for(auto e : XL) inLR[e] = 0;
            for(auto e : PR) inLR[e] = 0; for(auto e : XR) inLR[e] = 0;
            continue;
        }
#endif
        ui matrix_idx = 0;
        //construct matrix, positive edge is 1, negative edge is -1.
        build_matrix_PL_PR_XL_XR(PL, PR, XL, XR, matrix_idx);
        MBCEG_enum(CL, CR, PL, PR, XL, XR);
        for(auto e : PL) inLR[e] = 0; for(auto e : XL) inLR[e] = 0;
        for(auto e : PR) inLR[e] = 0; for(auto e : XR) inLR[e] = 0;
        for(ui j = 0; j < matrix_idx; j++) for(ui k = 0; k < matrix_idx; k++) Matrix[j][k] = 0;
    }
    delete [] inLR;
}

void CheckCorrect(string input_graph_name)
{
    vector<pair<vector<ui>, vector<ui>>> Rlt;
    for(auto e : results) {
        vector<ui> c1;
        for(auto x : e.first) c1.push_back(ori_id[x]);
        sort(c1.begin(),c1.end());
        
        vector<ui> c2;
        for(auto x : e.second) c2.push_back(ori_id[x]);
        sort(c2.begin(),c2.end());
        
        if(c1[0] < c2[0]) Rlt.push_back(make_pair(c1, c2));
        else Rlt.push_back(make_pair(c2, c1));
    }
    sort(Rlt.begin(), Rlt.end());

    //check the correctness of the results
    //read the orginal graph
    cout<<"\tCheck results : ";
    ifstream input_file(input_graph_name, ios::in);
    unordered_map<ui, unordered_map<ui, int>> SG;
    input_file >> n >> m;
    ui tu, tv;
    int flag;
    while (input_file >> tu >> tv >> flag){
        if(tu == tv) continue;
        assert(tu >= 0 && tu < n);
        assert(tv >= 0 && tv < n);
        assert(flag == 1 || flag == -1);
        SG[tu][tv] = flag;
        SG[tv][tu] = flag;
    }
    input_file.close();
    cout<<"read orginal graph, ";
    
    bool right = true;
    
    for(auto C : Rlt) {
        
        vector<ui> CL = C.first;
        vector<ui> CR = C.second;
        
        for(ui i = 0; i < CL.size(); i++) {
            for(ui j = i + 1; j < CL.size(); j++) {
                ui tmp_u = CL[i];
                ui tmp_v = CL[j];
                assert(SG.find(tmp_u) != SG.end());
                if(SG[tmp_u].find(tmp_v) == SG[tmp_u].end()) {
                    right = false;
                }
                else {
                    assert(SG[tmp_u][tmp_v] == 1);
                }
            }
        }
        for(ui i = 0; i < CR.size(); i++) {
            for(ui j = i + 1; j < CR.size(); j++) {
                ui tmp_u = CR[i];
                ui tmp_v = CR[j];
                assert(SG.find(tmp_u) != SG.end());
                if(SG[tmp_u].find(tmp_v) == SG[tmp_u].end()) {
                    right = false;
                }
                else {
                    assert(SG[tmp_u][tmp_v] == 1);
                }
            }
        }
        for(auto tmp_u : CL) {
            for(auto tmp_v : CR) {
                assert(SG.find(tmp_u) != SG.end());
                if(SG[tmp_u].find(tmp_v) == SG[tmp_u].end()) {
                    right = false;
                }
                else {
                    assert(SG[tmp_u][tmp_v] == -1);
                }
            }
        }
    }
    
    if(right == true) cout<<"VVV all correct!"<<endl;
    else cout<<"XXX something wrong!"<<endl;
}

void PrintResults(string input_graph_name)
{
//    vector<pair<vector<ui>, vector<ui>>> Rlt1;
    vector<pair<int, pair<vector<ui>, vector<ui>>>> Rlt1;
    for(auto e : results) {
        vector<ui> c1;
        for(auto x : e.first) c1.push_back(ori_id[x]);
        sort(c1.begin(),c1.end());
        
        vector<ui> c2;
        for(auto x : e.second) c2.push_back(ori_id[x]);
        sort(c2.begin(),c2.end());
        
        if(c1[0] < c2[0]) Rlt1.push_back(make_pair(c1.size()+c2.size(), make_pair(c1, c2)));
        else Rlt1.push_back(  make_pair ( c1.size()+c2.size(),   make_pair(c2, c1)     )   );
    }
    sort(Rlt1.begin(), Rlt1.end());
    
    ofstream outfile;
    string outdir = input_graph_name + "_" + to_string(tau) + "_" + to_string(alpha) + ".result.txt";
    outfile.open(outdir);
    outfile<<"Total "<<results.size()<<" cliques."<<endl<<endl;
    for(auto C : Rlt1) {
        outfile<<C.first<<" : < ";
        for(auto e : C.second.first) outfile<<id2str[e]<<", ";
        outfile<<" | ";
        for(auto e : C.second.second) outfile<<id2str[e]<<", ";
        outfile<<">"<<endl<<endl;
        
    }
    outfile.close();
    cout<<"\tPrint results!"<<endl;
}

int main(int argc, const char * argv[]) {
    
    if(argc < 4) {
        cout<<"\tUsage: [0]exe [1]input_graph [2]tau [3]alpha \t"<<endl; exit(1);
    }
    
    load_graph(argv[1]);
    tau = atoi(argv[2]);
    alpha = atoi(argv[3]);
    
    cout<<"\tGraph: "<<argv[1]<<", n = "<<n<<", m = "<<m<<endl;
    cout<<"\ttau: "<<tau<<", alpha: "<<alpha<<endl;
    
    Timer t;
    
    MBCEG(); //Maximal Balanced Clique Enumeration with Gap
    
    cout<<"\t----------------------------------------------"<<endl;
    cout<<"\tResults size = "<<result_num<<endl;
    cout<<"\tTime cost  = "<<integer_to_string(t.elapsed())<<endl;
    cout<<"\t----------------------------------------------"<<endl;
    
//    CheckCorrect(string(argv[1]));
//    PrintResults(string(argv[1]));
    
    delete_memo();
    
    return 0;
}

