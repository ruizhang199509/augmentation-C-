// ConsoleApplication1.cpp : 定义控制台应用程序的入口点。
//

#include "stdafx.h"
#include <iostream>
#include<vector>
#include<fstream>
#include<set>
#include <queue>
#include<math.h>
#include <time.h>
#define N  2000
using namespace std;


vector<int> link_a;   //存放匹配边
vector<int>  link_b;
vector<int> link_a_temp;   //存放匹配边
vector<int>  link_b_temp;
vector<int> visited;
vector<int> node_if_visited;         //findpath2中标记
vector<int> matched_a;  //标记是否已匹配
vector<int> matched_b;
vector  <int>  Replace;   //节点i的替换节点集
vector <vector<int > > Replace_linka;          //保存新的 link 之间的关系
vector <vector<int > > Replace_linkb;
int match_link = 0;
vector <int> match;   //存放in集合中匹配的节点
vector <int> reduncdant_nodes;
vector <int> MDS;
int sub = -1;
int update_nodes;
double K;               //平均度
int Nc;
int removal_node;
int Min, Max, Add;
set <int> R_a;             //存放不能被放进核中的点
set <int> R_b;
int N_core;
vector<int> mark_a;           //标记是否是core节点
vector<int>mark_b;
int M;                                //网络中边的总数目
int degree_a[N];               //存放节点的度   
int degree_b[N];
double r;                                  //对于固定度网络的r值
vector <int> Linklist_a;     //存放边
vector<int>Linklist_b;
int temp_mark[N];
double c = 20;
double ALPHA = 0.6;              
double sum_of_weight;
vector<vector<int> > choose;   //存放度的范围数组
double weight[N];   //存放每个点的度
int N;


double Rand_number() {
	double r = rand() / (RAND_MAX + 1.0);
	r = ((double)rand() + r) / (RAND_MAX + 1.0);
	r = ((double)rand() + r) / (RAND_MAX + 1.0);
	r = ((double)rand() + r) / (RAND_MAX + 1.0);
	r = ((double)rand() + r) / (RAND_MAX + 1.0);
	r = ((double)rand() + r) / (RAND_MAX + 1.0);
	r = ((double)rand() + r) / (RAND_MAX + 1.0);
	return r;
}

int findpath(vector<vector<int> >  Link, int i) {
	vector<int>s;
	s.push_back(i);
	vector<int>::iterator it;
	for (it = s.begin();it != s.end();it++) {
		for (int t = 0;t < Link[*it].size();t++) {
			int cur_node = Link[*it][t];
			if (visited[cur_node] == 0) {     //vi未访问
				visited[cur_node] = 1;
				if (!matched_b[cur_node] || findpath(Link, link_b[cur_node])) {
					matched_b[cur_node] = 1;
					matched_a[i] = 1;
					link_a[i] = cur_node;
					link_b[cur_node] = i;
					return 1;
					break;
				}
			}

		}
	}

	return 0;
}

int maxmatch(vector<vector<int> >  Link) {

	match_link = 0;
	matched_a.clear();
	matched_b.clear();
	link_a.clear();
	link_b.clear();
	visited.resize(N);
	matched_a.resize(N);
	matched_b.resize(N);
	link_a.resize(N);
	link_b.resize(N);
	for (int i = 0;i < N;i++) {
		link_a[i] = -1;
		link_b[i] = -1;
		matched_a[i] = 0;
		matched_b[i] = 0;
	}
	for (int i = 0;i < Link.size();i++) {
		for (int j = 0;j < N;j++) {
			visited[j] = 0;
		}
		if (!matched_a[i] && findpath(Link, i)) {
			match_link++;
			//cout << i<<"h";

		}
	}
	return match_link;
}

int findpath2(vector<vector<int> >  Link, int x1) {     //找驱动节点的替换节点
														//sub = -1;
	for (int i = 0;i < Link.size();i++) {
		for (int j = 0;j < Link[i].size();j++) {
			if (Link[i][j] == x1) {      //如果和节点i连接，则在节点i的所有连接节点中找匹配节点来更新驱动节点
				int m = link_a[i];
				if (node_if_visited[m] == 0) {
					node_if_visited[m] = 1;
					node_if_visited[x1] = 1;
					sub = link_a[i];
					matched_b[x1] = 1;
					matched_b[sub] = 0;
					link_a[i] = x1;
					link_b[x1] = i;
					for (int k = 0;k < match.size();k++) {
						if (match[k] == sub) {
							match[k] = x1;
						}
					}
					return 1;
				}
			}
		}
	}
	return 0;
}

int Update(vector<vector<int> >  Link) {
	update_nodes = 0;
	MDS.clear();
	match.clear();
	for (int i = 0;i < Link.size();i++) {
		if (matched_b[i] == 0) {
			MDS.push_back(i);
		}
		else
			match.push_back(i);
	}

	node_if_visited.resize(N);
	for (int j = 0;j < Link.size();j++) {
		node_if_visited[j] = 0;
	}
	for (int p = 0;p < MDS.size();p++) {
		if (findpath2(Link, MDS[p]) == 1) {                       //找到替换节点
			MDS[p] = sub;
			update_nodes++;
		}
	}
	return update_nodes;
}

//判断是否连接
bool nodes_if_link(vector<vector<int> >  Link, int x1, int x2) {
	for (int i = 0;i < Link[x1].size();i++) {
		if (Link[x1][i] == x2) {
			return 1;
		}
	}
	return 0;
}


int findpath3(vector<vector<int> > & Link, int i) {
	vector<int>s;
	s.push_back(i);
	vector<int>::iterator it;
	for (it = s.begin();it != s.end();it++) {
		for (int t = 0;t < Link[*it].size();t++) {
			int cur_node = Link[*it][t];
			if (visited[cur_node] == 0) {     //vi未访问
				visited[cur_node] = 1;
				if (!matched_b[cur_node] || findpath3(Link, link_b[cur_node])) {
					return 1;
					//break;
				}
			}

		}
	}

	return 0;
}

void Redundant_nodes(vector<vector<int> > & Link, vector<vector<int> > Link_temp) {
	maxmatch(Link);
	for (int i = 0;i < Link.size();i++) {
		if (matched_b[i] == 1)
			match.push_back(i);
	}

	for (int i = 0;i < match.size();i++) {
		int j = link_b[match[i]];
		for (int m = 0;m < Link.size();m++) {
			for (int n = 0; n < Link[m].size();n++) {
				if (Link[m][n] == match[i]) {
					int k = Link[m].size();
					Link[m][n] = Link[m][k - 1];
					Link[m].pop_back();
				}
			}
		} //删除与节点 i 的连接
		for (int i = 0;i < N;i++) {
			visited[i] = 0;
		}
		if (findpath3(Link, j) == 0) {
			reduncdant_nodes.push_back(match[i]);
		}
		Link.clear();
		Link = Link_temp;
	}
}


//建立网络
void Create_network(vector<vector<int> > & Link, vector<vector<int> >& Link_reverse) {
	int q = 0;
	while (q < (N*K / 2)) {
		int out, in;
		out = Rand_number()*N;
		in = Rand_number()*N;
		if (nodes_if_link(Link, out, in) == 0) {
			Link[out].push_back(in);
			Link_reverse[in].push_back(out);
			q++;

		}
	}
}

//建立SF网络
//void Create_network(vector<vector<int> > & Link, vector<vector<int> >& Link_reverse) {
//	double sum = 0;
//	sum_of_weight = 0;
//	choose.resize(N);
//	for (int i = 1;i <=N;i++) {
//		weight[i-1] = c*pow(i, -ALPHA);
//		sum_of_weight += weight[i-1];     //给每个点分配度的值 
//		choose[i-1].push_back(sum);
//		choose[i-1].push_back(sum_of_weight);     //[sum,sum_of_weight]表示度的权重范围
//		sum = sum_of_weight;
//	}
//	//int p = sum_of_weight + 1;
//	cout << sum_of_weight << "aaaaaaaa";
//	int q = 0;
//	while (q < (N*K / 2)) {
//		int out, in;
//		double a, b;
//		int E = N*K ;     
//		a = rand() %E ;
//		b = rand() % E;
//		for (int i = 0;i < N;i++) {
//		//	for (int j = 0;j < choose[i].size();j++) {
//				if (a >= choose[i][0] && a < choose[i][1]) {
//					out = i;
//					break;
//				//}
//			}
//		}
//		for (int i = 0;i < N;i++) {
//		//	for (int j = 0;j < choose[i].size();j++) {
//				if (b >= choose[i][0] && b < choose[i][1]) {
//					in = i;
//					break;
//				//}
//			}
//		}
//		if (nodes_if_link(Link, out, in) == 0) {
//			Link[out].push_back(in);
//			Link_reverse[in].push_back(out);
//			q++;
//		}
//
//	}
//}



bool incoming_links(vector<vector<int> >  Link, int x1) {
	for (int m = 0;m < Link.size();m++) {
		for (int n = 0;n < Link[m].size();n++) {
			if (Link[m][n] == x1) {
				return 1;
			}
		}
	}
	return 0;
}

int Get_Nc(vector<vector<int> >  Link) {  //获取入度为0 的结点
	Nc = 0;
	for (int i = 0;i < N;i++) {
		if (incoming_links(Link, i) == 0) {
			Nc++;
		}
	}
	return Nc;
}

int find_path(vector<vector<int> >  Link, int i) {
	vector<int> s;
	s.push_back(i);
	vector<int>::iterator it;
	for (it = s.begin();it != s.end();it++) {
		for (int t = 0;t < Link[*it].size();t++) {
			int cur_node = Link[*it][t];
			if (temp_mark[cur_node] == 0) {
				if (visited[cur_node] == 0) {     //vi未访问
					visited[cur_node] = 1;
					if (matched_b[cur_node] == 0 || find_path(Link, link_b_temp[cur_node])) {
						link_a_temp[i] = cur_node;
						link_b_temp[cur_node] = i;
						if (matched_b[cur_node] == 0) {
							removal_node = cur_node;
						}
						return 1;
						break;
					}
				}
			}
		}
	}

	return 0;
}

//枚举一个IN set 中节点x1的所有替换节点
void Enmurate(vector<vector<int> >  Link, int x1) {
	int j = link_b_temp[x1];
	temp_mark[x1] = 1;
	//for (int m = 0;m < Link.size();m++) {
	//	for (int n = 0; n < Link[m].size();n++) {
	//		if (Link[m][n] == x1) {
	//			int k = Link[m].size();
	//			Link[m][n] = Link[m][k - 1];
	//			Link[m].pop_back();
	//		}
	//	}
	//}              //删除与节点 x1 的连接
	for (int i = 0;i < N;i++) {
		visited[i] = 0;
	}
	if (find_path(Link, j) == 1) {
		//matched_b[x1] = 0;
		//link_b[removal_node] = j;
		Replace.push_back(removal_node);
		Replace_linka.push_back(link_a_temp);
		Replace_linkb.push_back(link_b_temp);
		Enmurate(Link, removal_node);
	}

}

//随机取样得到上下界
void Bound(vector<vector<int> > & Link, vector<vector<int> >  Link_temp) {
	Add = 0;
	removal_node = -1;
	for (int i = 0;i < Link.size();i++) {
		if (matched_b[i] == 1) {
			match.push_back(i);                       //获得当前MMS
		}
	}

	Update(Link);
	Add = Max = Min = update_nodes;
	for (int times = 0;times < 100;times++) {
		for (int i = 0;i < 10;i++) {
			if (!match.empty()) {
				int r = Rand_number()*match.size();
				removal_node = match[r];
				int before = match[r];
				Replace.clear();
				Replace_linka.clear();
				Replace_linkb.clear();
				link_a_temp.clear();
				link_b_temp.clear();
				link_a_temp = link_a;
				link_b_temp = link_b;
				for (int i1 = 0;i1 < N;i1++) {
					temp_mark[i1] = 0;
				}
				Enmurate(Link, removal_node);

				if (!Replace.empty()) {
					int a = Rand_number()*Replace.size();
					int b = Replace[a];
					matched_b[b] = 1;
					matched_b[before] = 0;
					link_a.clear();
					link_b.clear();
					link_a = Replace_linka[a];
					link_b = Replace_linkb[a];
					match[r] = b;                                //随机选择一个节点替换 i 形成新的MMS
																 //cout << "b" << endl;
				}
			}
		}
		Update(Link);
		Add = Add + update_nodes;
		if (Min > update_nodes) {
			Min = update_nodes;                                   //更新上下界的值
		}
		if (Max < update_nodes) {
			Max = update_nodes;
		}
	}    //重复100次结束
}

//遍历度是否为1
int get_degree(vector<vector<int> > & Link, vector<vector<int> > &Link_reverse) {

	for (int i = 0;i < Link.size();i++) {
		if (mark_a[i] == 0) {
			if (Link[i].size() == 1 || Link[i].size() == 0) {                               //遍历 + set
				return 1;
			}
		}
	}
	for (int i = 0;i<Link_reverse.size();i++) {
		if (mark_b[i] == 0) {
			if (Link_reverse[i].size() == 1 || Link_reverse[i].size() == 0) {
				return 1;
			}
		}
	}
	return 0;
}


int Get_core(vector<vector<int> > & Link, vector<vector<int> > &Link_reverse) {
	N_core = 0;
	mark_a.resize(N);
	mark_b.resize(N);
	while (get_degree(Link, Link_reverse) == 1) {
		for (int j = 0;j < Link.size();j++) {
			if (mark_a[j] == 0) {

				if (Link[j].size() == 1 || Link[j].size() == 0) {
					//cout << j << "\t";
					R_a.insert(j);
					mark_a[j] = 1;
					if (Link[j].size() == 1) {
						int m = Link[j][0];                     //m为 节点度为1 的neighbor节点     
						mark_b[m] = 1;
						R_b.insert(Link[j][1]);
						for (int a = 0;a < Link.size();a++) {
							for (int b = 0;b < Link[a].size();b++) {
								if (Link[a][b] == m) {
									int l = Link[a].size();
									Link[a][b] = Link[a][l - 1];
									Link[a].pop_back();
								}
							}
						}

						Link_reverse[m].clear();

					}
					Link[j].clear();
				}
			}
		}
		for (int j = 0;j < Link.size();j++) {
			if (mark_b[j] == 0) {
				if (Link_reverse[j].size() == 1 || Link_reverse[j].size() == 0) {
					R_b.insert(j);
					mark_b[j] = 1;
					//cout << j << "h" << endl;
					if (Link_reverse[j].size() == 1) {
						int m = Link_reverse[j][0];                  //m为 节点度为1 的neighbor节点
						R_a.insert(m);
						mark_a[m] = 1;
						Link[m].clear();
						for (int p = 0;p < Link_reverse.size();p++) {                  //删除与neighbor 节点的连接
							for (int q = 0;q < Link_reverse[p].size();q++) {
								if (Link_reverse[p][q] == m) {
									int k = Link_reverse[p].size();
									Link_reverse[p][q] = Link_reverse[p][k - 1];
									Link_reverse[p].pop_back();
								}
							}
						}
					}
					Link_reverse[j].clear();

				}
			}//mark[j]==0
		}

	}//while
	 //N_core = Link.size() - R_a.size();
	for (int s = 0;s < mark_a.size();s++) {
		if (mark_a[s] == 0) {
			N_core++;
		}
	}
	return N_core;
}

void Swap_add(vector<vector<int> >& Link, vector<vector<int> >& Link_reverse) {

	int a = 0, b = 0;
	a = Rand_number()*M;         //随机选择两条边
	b = Rand_number()*M;
	int u = 0, v = 0, x = 0, y = 0;
	int num1 = -1, num2 = -1;
	u = Linklist_a[a];
	v = Linklist_b[a];
	x = Linklist_a[b];
	y = Linklist_b[b];
	while (u == x || v == y || (degree_a[u] * degree_b[v] + degree_a[x] * degree_b[y]) >= (degree_a[u] * degree_b[y] + degree_a[x] * degree_b[v]) || nodes_if_link(Link, u, y) || nodes_if_link(Link, x, v)) {                 //随机产生两条边
		a = Rand_number()*M;
		b = Rand_number()*M;
		u = Linklist_a[a];
		v = Linklist_b[a];
		x = Linklist_a[b];
		y = Linklist_b[b];
	}


	for (int m1 = 0;m1 < Link[u].size();m1++) {
		if (Link[u][m1] == v) {
			num1 = m1;
			break;
		}
	}


	for (int m2 = 0;m2 < Link[x].size();m2++) {                   //交换连接
		if (Link[x][m2] == y) {
			num2 = m2;
			break;
		}
	}
	Link[u][num1] = y;
	Link[x][num2] = v;
	for (int m3 = 0;m3 < Link_reverse[v].size();m3++) {
		if (Link_reverse[v][m3] == u) {
			num1 = m3;
			break;
		}
	}
	for (int m4 = 0;m4 < Link_reverse[y].size();m4++) {                   //交换连接
		if (Link_reverse[y][m4] == x) {
			num2 = m4;
			break;
		}
	}
	Link_reverse[v][num1] = x;
	Link_reverse[y][num2] = u;
	Linklist_b[a] = y;                              //更新Link_list中的连接
	Linklist_b[b] = v;
}

void Swap_dec(vector<vector<int> >& Link, vector<vector<int> >& Link_reverse) {
	int a = 0, b = 0;
	a = Rand_number()*M;         //随机选择两条边
	b = Rand_number()*M;
	int u = 0, v = 0, x = 0, y = 0;
	int num1 = -1;
	int 	num2 = -1;
	u = Linklist_a[a];
	v = Linklist_b[a];
	x = Linklist_a[b];
	y = Linklist_b[b];
	while (u == x || v == y || (degree_a[u] * degree_b[v] + degree_a[x] * degree_b[y]) <= (degree_a[u] * degree_b[y] + degree_a[x] * degree_b[v]) || nodes_if_link(Link, u, y) || nodes_if_link(Link, x, v)) {                 //随机产生两条边
		a = Rand_number()*M;
		b = Rand_number()*M;
		u = Linklist_a[a];
		v = Linklist_b[a];
		x = Linklist_a[b];
		y = Linklist_b[b];
	}


	for (int m1 = 0;m1 < Link[u].size();m1++) {
		if (Link[u][m1] == v) {
			num1 = m1;
			break;
		}
	}


	for (int m2 = 0;m2 < Link[x].size();m2++) {                   //交换连接
		if (Link[x][m2] == y) {
			num2 = m2;
			break;
		}
	}
	Link[u][num1] = y;
	Link[x][num2] = v;
	for (int m3 = 0;m3 < Link_reverse[v].size();m3++) {
		if (Link_reverse[v][m3] == u) {
			num1 = m3;
			break;
		}
	}
	for (int m4 = 0;m4 < Link_reverse[y].size();m4++) {                   //交换连接
		if (Link_reverse[y][m4] == x) {
			num2 = m4;
			break;
		}
	}
	Link_reverse[v][num1] = x;
	Link_reverse[y][num2] = u;
	Linklist_b[a] = y;                              //更新Link_list中的连接
	Linklist_b[b] = v;
}


void Get_r(vector<vector<int> > Link, vector<vector<int> > Link_reverse) {
	M = 0;
	Linklist_a.clear();
	Linklist_b.clear();
	for (int i = 0;i < N;i++) {
		degree_a[i] = Link[i].size();                           //存放点的度
		degree_b[i] = Link_reverse[i].size();
		M = M + Link[i].size();
	}
	for (int m = 0;m < Link.size();m++) {
		for (int n = 0;n < Link[m].size();n++) {              //存放边
			if (Link[m].size() != 0) {
				Linklist_a.push_back(m);
				Linklist_b.push_back(Link[m][n]);
			}
		}  //for
	}
	double A = 0, B = 0, C = 0;
	for (int i = 0;i < M;i++) {
		int k1 = Linklist_a[i];
		int k2 = Linklist_b[i];
		A += degree_a[k1] * degree_b[k2];
		B += (degree_a[k1] + degree_b[k2]);
		C += (degree_a[k1] * degree_a[k1] + degree_b[k2] * degree_b[k2]);
	}
	double R1 = 4 * M*A - B*B;
	double R2 = 2 * M*C - B*B;
	r = R1 / R2;
}

//读取真实数据
//int max_node_number_binary_data(string fname, int& number_link) {
//
//	string filename = "F:\\augmentation\\real-network\\";
//	//filename.append(fname);
//
//	ifstream bin(filename, ios_base::in | ios::binary);
//	if (!bin) { cout << "Cannot open " << filename << " for read."; exit(0); }
//	int* nm = new int[2];
//	bin.read(reinterpret_cast<char *>(nm), 2 * sizeof(int));
//	int n = nm[0];
//	int m = nm[1];
//	delete[] nm;
//	number_link = m;
//
//	return n;
//}

void readin_network_binary(string fname, link_type& link) {

	
	string filename = "F:\\augmentation\\real-network\\ECircuit-s208.elist.b";
//	filename.append(fname);

	ifstream bin(filename, ios_base::in | ios::binary);
	if (!bin) { cout << "Cannot open " << filename << " for read."; exit(0); }

	int* nm = new int[2];
	bin.read(reinterpret_cast<char *>(nm), 2 * sizeof(int));
	int n = nm[0];
	int m = nm[1];
	delete[] nm;

	int* endpoints = new int[2 * m];
	bin.read(reinterpret_cast<char *>(endpoints), 2 * m * sizeof(int));
	bin.close();

	int N = n;
	int i, j;

	for (int e = 0; e<m; e++) {
		i = endpoints[2 * e + 0]; // source
		j = endpoints[2 * e + 1]; // target

		if (i >= N || j >= N) {

			cout << "error in readin data" << endl;
		}
		if (node_if_link(Link, i, j) == 0) {
			Link[i].push_back(j);
			Link_reverse[j].push_back(i);
		}
	

	}
	
	delete[] endpoints;
}

//int main() {
//	srand((unsigned)time(NULL));
//	string filename = "F:\\augmentation\\real-network\\ECircuit-s208.elist.b";
//	//	filename.append(fname);
//	ifstream bin(filename, ios_base::in | ios::binary);
//	if (!bin) { cout << "Cannot open " << filename << " for read."; exit(0); }
//	int* nm = new int[2];
//	bin.read(reinterpret_cast<char *>(nm), 2 * sizeof(int));
//	int n = nm[0];
//	int m = nm[1];
//	delete[] nm;
//
//	int* endpoints = new int[2 * m];
//	bin.read(reinterpret_cast<char *>(endpoints), 2 * m * sizeof(int));
//	bin.close();
//
//	int N = n;
//	int i, j;
//	vector<vector<int> > Link;
//	vector<vector<int> > Link_temp;
//	vector<vector<int> > Link_reverse;
//	Link.resize(N);
//	Link_temp.resize(N);
//	Link_reverse.resize(N);
//	for (int e = 0; e<m; e++) {
//		i = endpoints[2 * e + 0]; // source
//		j = endpoints[2 * e + 1]; // target
//
//		if (i >= N || j >= N) {
//
//			cout << "error in readin data" << endl;
//		}
//		if (node_if_link(Link, i, j) == 0) {
//			Link[i].push_back(j);
//			Link_reverse[j].push_back(i);
//		}
//
//
//	}
//	delete[] endpoints;
//	
//		/*Replace_linka.resize(N);
//		Replace_linkb.resize(N);*/
//		/*for (int i = 0;i < N;i++) {
//		link_a[i] = -1;
//		link_b[i] = -1;
//		}*/
//	//	Create_network(Link, Link_reverse);
//	    
//		maxmatch(Link);
//		//Redundant_nodes(Link, Link_temp);
//		Update(Link);
//		//Bound(Link, Link_temp);
//		cout << n << "\t" << m;
//	system("pause");
//	return 0;
//}



int main()
{
	srand((unsigned)time(NULL));
	K = 4;
	M = 0;
	r = 0;
	int q;
	update_nodes = 0;
	ofstream infile;
	ofstream infile1;
	infile6.open("F:\\augmentation\\data3\\drivenode-initial.txt", ios::out);
	infile << "r\t\t" << "N" << endl;
	vector<vector<int> > Link;
	vector<vector<int> > Link_temp;
	vector<vector<int> > Link_reverse;
	Link.resize(N);
	Link_temp.resize(N);
	Link_reverse.resize(N);
	Create_network(Link, Link_reverse);
	for (int i = 0;i < Link.size();i++) {
		for (int j = 0;j < Link[i].size();j++) {
			if (Link[i].size() != 0) {
				infile5 << i << "\t" << Link[i][j] << "'" << endl;
			}
		}
	}

	Link_temp.clear();
	Link_temp = Link;
	Get_r(Link, Link_reverse);
	maxmatch(Link);
	Update(Link);
	for (int i = 0;i < MDS.size();i++) {
		infile6 << MDS[i] << endl;
	}
	//cout << "aaa";
	//Bound(Link, Link_temp);
	//cout << "bbb";
	/*q = Add / 11;
	cout << "r :   " << r << "\t" << "Min:   " << Min << "\t" << "Max :   " << Max << "\t" << "AVG :   " << q << endl;
	infile << r << "\t\t" << Min << "\t\t" << Max << "\t\t" << q << endl;*/
	cout << "r: " << r << "\t" << "N :" << "\t" << update_nodes << endl;
	infile << r << "\t\t" << update_nodes << endl;
	double r1 = r;

	for (int times = 0;times < 2500;times++) {

		Swap_dec(Link, Link_reverse);
		Get_r(Link, Link_reverse);
		if ((r1 - r) >= 0.01) {
			maxmatch(Link);
			Update(Link);
			//Bound(Link, Link_temp);
			/*q = Add / 11;
			cout << "r :   " << r << "\t" << "Min:   " << Min << "\t" << "Max :   " << Max << "\t" << "AVG :   " << q << endl;
			infile << r << "\t\t" << Min << "\t\t" << Max << "\t\t" << q << endl;*/
			cout << "r: " << r << "\t" << "N :" << "\t" << update_nodes << endl;
			infile << r << "\t\t" << update_nodes << endl;
			r1 = r;

		}
		if (r < -0.6) {
			maxmatch(Link);
			Update(Link);
			/*Bound(Link, Link_temp);
			q = Add / 11;
			cout << "r :   " << r << "\t" << "Min:   " << Min << "\t" << "Max :   " << Max << "\t" << "AVG :   " << q << endl;
			infile << r << "\t\t" << Min << "\t\t" << Max << "\t\t" << q << endl;*/
			cout << "r: " << r << "\t" << "N :" << "\t" << update_nodes << endl;
			infile << r << "\t\t" << update_nodes << endl;
			for (int i = 0;i < Link.size();i++) {
				for (int j = 0;j < Link[i].size();j++) {
					if (Link[i].size() != 0) {
						infile1 << i << "\t" << Link[i][j] << "'" << endl;
					}
				}
			}
			for (int i = 0;i < MDS.size();i++) {
				infile3 << MDS[i] << endl;
			}
			break;
		}
	}
	//Link.clear();
	//Link_reverse.clear();
	//Link_temp.clear();
	//Link.resize(N);
	//Link_temp.resize(N);
	//Link_reverse.resize(N);
	//Create_network(Link, Link_reverse);
	//Link_temp.clear();
	//Link_temp = Link;
	Get_r(Link, Link_reverse);
	r1 = r;
	for (int times = 0;times < 2500;times++) {
		Swap_add(Link, Link_reverse);
		Get_r(Link, Link_reverse);
		if ((r - r1) >= 0.01) {
			maxmatch(Link);
			Update(Link);
			/*Bound(Link, Link_temp);
			q = Add / 11;
			cout << "r :   " << r << "\t" << "Min:   " << Min << "\t" << "Max :
			" << Max << "\t" << "AVG :   " << q << endl;
			infile << r << "\t\t" << Min << "\t\t" << Max << "\t\t" << q << endl;*/
			cout << "r: " << r << "\t" << "N :" << "\t" << update_nodes << endl;
			infile << r << "\t\t" << update_nodes << endl;
			r1 = r;

		}
		if (r > 0.6) {
			maxmatch(Link);
			Update(Link);
			/*Bound(Link, Link_temp);
			q = Add / 11;
			cout << "r :   " << r << "\t" << "Min:   " << Min << "\t" << "Max :   " << Max << "\t" << "AVG :   " << q << endl;
			infile << r << "\t\t" << Min << "\t\t" << Max << "\t\t" << q << endl;*/
			cout << "r: " << r << "\t" << "N :" << "\t" << update_nodes << endl;
			infile << r << "\t\t" << update_nodes << endl;
			for (int i = 0;i < Link.size();i++) {
				for (int j = 0;j < Link[i].size();j++) {
					if (Link[i].size() != 0) {
						infile2 << i << "\t" << Link[i][j]  <<"'"<< endl;
					}
				}
			}
			for (int i = 0;i < MDS.size();i++) {
				infile4 << MDS[i] << endl;
			}
			break;
		}
	}
	Get_r(Link, Link_reverse);
	maxmatch(Link);
	Update(Link);
	/*Bound(Link, Link_temp);
	q = Add / 11;
	cout << "r :   " << r << "\t" << "Min:   " << Min << "\t" << "Max :   " << Max << "\t" << "AVG :   " << q << endl;
	infile << r << "\t\t" << Min << "\t\t" << Max << "\t\t" << q << endl;*/
	cout << "r: " << r << "\t" << "N :" << "\t" << update_nodes << endl;
	infile << r << "\t\t" << update_nodes << endl;
	system("pause");
	return 0;

}
