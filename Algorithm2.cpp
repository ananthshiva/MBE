#define _CRT_SECURE_NO_WARNINGS
#include <iostream>
#include <string>
#include <cstdlib>
#include <algorithm>
#include <cstring>
#include <time.h>
#include <cstdio>
#include <cassert>
#include <cstdio>
#include <stdio.h>
#include <numeric>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <sstream>
#include <chrono>
#include<vector>

using namespace std;

#define SZ(x) ((int)x.size())
#define ll long long
#define ull unsigned long long
#define ld long double
#define eps 1e-11
#define max(x,y) ((x)>(y)?(x):(y))
#define min(x,y) ((x)<(y)?(x):(y))

const int ITER_VER = 2200;
const ll shift = 1000 * 1000 * 1000LL;
const double TIME_LIMIT = 20;
const int N_WEDGE_ITERATIONS = 2 * 1000 * 1000 * 10;
const int ITERATIONS_SAMPLING = 5;
const int N_SPARSIFICATION_ITERATIONS = 5;
const int TIME_LIMIT_SPARSIFICATION = 10000; 
const int N_FAST_EDGE_BFC_ITERATIONS = 2100; 
const int N_FAST_WEDGE_ITERATIONS = 50; 
char output_address[2000];
char* input_address;


set <vector<int>> edges;
map<pair<int, int>, int> edge_sign;
vector < pair <int, int>> list_of_edges;
map < int, int > vertices[2];
vector <int> index_map;
vector <int> vertices_in_left;
vector <int> vertices_in_right;
vector < vector <int> > adj;
vector < vector <int> > adj_positive;
vector < vector <int> > adj_negative;
vector < vector < int > > sampled_adj_list;
vector <bool> visited;
vector <int> list_of_vertices;
vector <int> vertex_counter;


ll count_wedge;
ll n_vertices;
ll n_edges;
ld exact_n_bf;
ld exact_n_bf_signed;
ld exact_n_bf_unsigned;
ll n_wedge_in_partition[2];
ll largest_index_in_partition[2];
int tauU =3 , tauV=3;
set<pair<vector<int>,vector<int>>> beta;
ll betacount=0;
vector <int> clr;
vector <int> hashmap_C;
vector <ll> sum_wedges;
vector <ll> sum_deg_neighbors;
vector <int> aux_array_two_neighboorhood;

void clear_everything() {
	largest_index_in_partition[0] = largest_index_in_partition[1] = 0;
	n_vertices = 0;
	n_edges = 0;
	edges.clear();
	vertices[0].clear(); vertices[1].clear();
	index_map.clear();
	vertices_in_left.clear();
	vertices_in_right.clear();
	adj.clear();
	sampled_adj_list.clear();
	visited.clear();
	//list_of_edges.clear();
	vertex_counter.clear();
	clr.clear();
	hashmap_C.clear();
	sum_wedges.clear();
	sum_deg_neighbors.clear();
	aux_array_two_neighboorhood.clear();
}

void resize_all() {
	clr.resize(n_vertices);
	hashmap_C.resize(n_vertices);
	aux_array_two_neighboorhood.resize(n_vertices);
	sum_wedges.resize(n_vertices);
	visited.resize(n_vertices);
	index_map.resize(n_vertices);
	sum_deg_neighbors.resize(n_vertices);
}


// ------------- Read the graph ---------------------
void add_vertex(int A, int side) {
	if (vertices[side].find(A) == vertices[side].end()) {
		if (side == 0) vertices_in_left.push_back(A);
		else vertices_in_right.push_back(A);
		vertices[side][A] = 1;
	}
}

void add_edge(int &A, int &B, int &sign) {
	add_vertex(A, 0);
	add_vertex(B, 1);

	if (edges.find({ A,B,sign }) == edges.end()) {
		edges.insert({ A,B,sign });

		n_edges++;
	}
}

void get_index(int& A, int side) {
	if (vertices[side].find(A) == vertices[side].end()) {
		vertices[side][A] = largest_index_in_partition[side]++;		
	}
	A = vertices[side][A];
}

bool all_num(string& s) {
	for (int i = 0; i < SZ(s); i++) if ((s[i] >= '0' && s[i] <= '9') == false) return false;
	return true;
}

void get_graph() {
	freopen(input_address, "r", stdin); 
	printf("[%ld:] File Opened\n", __LINE__);
	string s;
	cin.clear(); 
	while (getline(cin, s)) { 
		stringstream ss;
		ss << s; 
		vector <string> vec_str;
		for (string z; ss >> z; vec_str.push_back(z));
		if (SZ(vec_str) >= 2) {
			bool is_all_num = true;
			for (int i = 0; i < min(2, SZ(vec_str)); i++) is_all_num &= all_num(vec_str[i]);
			if (is_all_num) {
				int A, B, sign;
				ss.clear(); ss << vec_str[0]; ss >> A;
				ss.clear(); ss << vec_str[1]; ss >> B;
				ss.clear(); ss << vec_str[2]; ss >> sign;
				add_edge(A, B, sign);

			}
		}
	}
	//printf("[%ld:] File Reading Done!\n", __LINE__);
	vertices[0].clear();
	vertices[1].clear();
	largest_index_in_partition[0] = 0;
	largest_index_in_partition[1] = SZ(vertices_in_left);
	n_vertices = SZ(vertices_in_left) + SZ(vertices_in_right);

	adj.resize(n_vertices, vector <int>());
	adj_positive.resize(n_vertices, vector <int>());
	adj_negative.resize(n_vertices, vector <int>());
	for (auto edge : edges) {
		int A = edge[0];
		int B = edge[1];
		int sign = edge[2];
		get_index(A, 0);
		get_index(B, 1);
		adj[A].push_back(B);
		adj[B].push_back(A);
		if(sign){
			adj_positive[A].push_back(B);
			adj_positive[B].push_back(A);
		}else{
			adj_negative[A].push_back(B);
			adj_negative[B].push_back(A);
		}
		//list_of_edges.push_back(make_pair(A, B)); 
		edge_sign[{A, B}] = sign;
		edge_sign[{B, A}] = sign;


	}
	resize_all();

	//cerr << " for test # edges :: " << SZ(list_of_edges) << " left :: " << SZ(vertices_in_left) << " right :: "  << SZ(vertices_in_right) << endl;
	//sort(list_of_edges.begin(), list_of_edges.end());
	edges.clear();
	fclose(stdin);
}



void read_the_graph(char* fin) {
	clear_everything();
	cerr << " Insert the input (bipartite network) file location" << endl;
	cerr << " >>> "; 
	input_address = fin;
	//cerr << " Insert the output file" << endl;
	//cerr << " >>> "; cin >> output_address;
	//freopen(output_address, "w", stdout);
	cerr << " ---------------------------------------------------------------------------------------------------------------------- \n";
	cerr << "| * Note that edges should be separated line by line.\n\
| In each line, the first integer number is considered as a vertex in the left partition of bipartite network, \n\
| and the second integer number is a vertex in the right partition. \n\
| In addition, multiple edges are removed from the given bipartite network.\n\
| Also, note that in this version of the source code, we did NOT remove vertices with degree zero.\n";
	cerr << " ---------------------------------------------------------------------------------------------------------------------- \n";

	cerr << " Processing the graph ... (please wait) \n";

	get_graph();   

	cout << " -------------------------------------------------------------------------- \n";
	cout << "Input graph: " << input_address << "\n";
	cout << " The graph is processed - there are " << n_vertices << " vertices and " << n_edges << " edges  \n";
	cout << " -------------------------------------------------------------------------- \n";
}




void SUB_BASEENUM(vector<int>& Ul, vector<int>& Ur, vector<int>& Vl, vector<int>& Vr, set<int>& C, set<int>& X);

void BASEENUM(vector<int>& Ul, vector<int>& Ur, vector<int>& Vl, vector<int>& Vr, set<int>& C, set<int>& X) {
	bool Flag = true;
	auto C_iterator = C.begin();
	const auto C_end_iterator = C.end();
	while (C_iterator != C_end_iterator){
		int v=*C_iterator;
		C_iterator = C.erase(C_iterator);
		Vl.push_back(v);
		vector<int> Ul_prime, Ur_prime;
		for (int neighbor : adj_positive[v]) {
			if (find(Ul.begin(), Ul.end(), neighbor) != Ul.end()) {
				Ul_prime.push_back(neighbor);	
			}
		}
		for (int neighbor : adj_negative[v]){
			if (find(Ur.begin(), Ur.end(), neighbor) != Ur.end()) {
				Ur_prime.push_back(neighbor);
			}
		}
		if (SZ(Ul_prime) == SZ(Ul) && SZ(Ur_prime) == SZ(Ur)) {
			Flag = false;
		}
		
		SUB_BASEENUM(Ul_prime, Ur_prime, Vl, Vr, C, X);
		Vl.pop_back();
		if (!Vl.empty() || !Vr.empty()) {
			Vr.push_back(v);
			Ul_prime.clear();
			Ur_prime.clear();
			for (int neighbor : adj_negative[v]) {
				if (find(Ul.begin(), Ul.end(), neighbor) != Ul.end()) {
					Ul_prime.push_back(neighbor);	
				}
			}
			for (int neighbor : adj_positive[v]){
				if (find(Ur.begin(), Ur.end(), neighbor) != Ur.end()) {
					Ur_prime.push_back(neighbor);
				}
			}

			if (SZ(Ul_prime) == SZ(Ul) && SZ(Ur_prime) == SZ(Ur)) {
				Flag = false;
			}

			SUB_BASEENUM(Ul_prime, Ur_prime, Vl, Vr, C, X);
			Vr.pop_back();
		}
		X.insert(v);
	}

	if (Flag && SZ(Ul) + SZ(Ur) >= tauU && SZ(Vl) + SZ(Vr) >= tauV) {
		if(SZ(Ul)+SZ(Ur)>0 && SZ(Vl)+SZ(Vr)>0)
			betacount++;
	}
}

void SUB_BASEENUM(vector<int>& Ul, vector<int>& Ur, vector<int>& Vl, vector<int>& Vr, set<int>& C, set<int>& X) {
	set<int> C_prime, X_prime;

	for (int w : C) {
		int count_1=0,count_2=0;
		for(auto u_l : Ul){
			if(find(adj_positive[w].begin(), adj_positive[w].end(),u_l) != adj_positive[w].end()){
				count_1++;
			}
		}for(auto u_r : Ur){
			if(find(adj_negative[w].begin(), adj_negative[w].end(),u_r) != adj_negative[w].end()){
				count_1++;
			}
		}
		for(auto u_r : Ur){
			if(find(adj_positive[w].begin(), adj_positive[w].end(),u_r) != adj_positive[w].end()){
				count_2++;
			}
		}for(auto u_l : Ul){
			if(find(adj_negative[w].begin(), adj_negative[w].end(),u_l) != adj_negative[w].end()){
				count_2++;
			}
		}

		if (max(count_1,count_2) >= tauU){
			C_prime.insert(w);
		}
	}
	for (int w : X) {
		int count_1=0,count_2=0;
		for(auto u_l : Ul){
			if(find(adj_positive[w].begin(), adj_positive[w].end(),u_l) != adj_positive[w].end()){
				count_1++;
			}
		}for(auto u_r : Ur){
			if(find(adj_negative[w].begin(), adj_negative[w].end(),u_r) != adj_negative[w].end()){
				count_1++;
			}
		}
		for(auto u_r : Ur){
			if(find(adj_positive[w].begin(), adj_positive[w].end(),u_r) != adj_positive[w].end()){
				count_2++;
			}
		}for(auto u_l : Ul){
			if(find(adj_negative[w].begin(), adj_negative[w].end(),u_l) != adj_negative[w].end()){
				count_2++;
			}
		}
		if (max(count_1,count_2) >= tauU){
			X_prime.insert(w);
		}
	}
	for (int v : X_prime) {
		if ((includes(adj_positive[v].begin(), adj_positive[v].end(), Ul.begin(), Ul.end()) &&
			includes(adj_negative[v].begin(), adj_negative[v].end(), Ur.begin(), Ur.end())) ||
			(includes(adj_negative[v].begin(), adj_negative[v].end(), Ul.begin(), Ul.end()) &&
				includes(adj_positive[v].begin(), adj_positive[v].end(), Ur.begin(), Ur.end()))) {
			return;
		}
	}

	BASEENUM(Ul, Ur, Vl, Vr, C_prime, X_prime);
}

void enumerate_bicliques() {
	vector<int> initial_Ul(vertices_in_left.begin(), vertices_in_left.end());
	vector<int> initial_Ur(vertices_in_right.begin(), vertices_in_right.end());
	vector<int> initial_Vl, initial_Vr;
	set<int> initial_C(vertices_in_right.begin(), vertices_in_right.end());
	set<int> initial_X;
	BASEENUM(initial_Ul, initial_Ur, initial_Vl, initial_Vr, initial_C, initial_X);
	std::cout<<"Number of Maximal Balanced Signed Bicliques: "<<betacount<<endl;
}




void exact_algorithm_time_tracker() {
	auto start_time = std::chrono::high_resolution_clock::now();
	enumerate_bicliques();
	auto end_time = std::chrono::high_resolution_clock::now();
	auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time);

	std::cout << "Algorithm execution time: " << duration.count() << " ms" << std::endl;
}

int main(int argc, char* argv[])
{
	std::ios::sync_with_stdio(false);
	read_the_graph(argv[1]);
	exact_algorithm_time_tracker();
}
