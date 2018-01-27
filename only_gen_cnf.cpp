#include <stdlib.h>
#include <math.h>
#include <iostream>
#include <fstream>
#include <vector>
#include <queue>
#include <string>

using namespace std;

struct pv{
	int r, c, v;
	pv(int rr, int cc, int vv):r(rr),c(cc),v(vv){};
};

struct pc{
	int r, c;
	vector<int> candi;
	pc(int rr, int cc):r(rr),c(cc){};
};

struct cv{
	int count;
	queue<int> vars;
	cv():count(0){};
};

class solver{
	public:
		solver();
		void read_board(char*);
		void cnf_encode();
		void go(char*);
		void write_result(char*);
	private:
		int _N;
		int _squN;
		string _sat_in;
		string _sat_out;
		vector<int> _board;
		vector<pc> _posi_candi;
		vector<vector<int> > _clauses;
		vector<pv> _var2pv;
		void _gen_candi();
		void _candi_constraint();
		void _rcs_constraint();
		void _group_handler(int, int);
		void _group_handler(queue<int>&);
		void _no_group_handler(int, int);
		void _no_group_handler(queue<int>&);
		void _add_clause(int, int=0, int=0, int=0);
		void _gen_go_input_file();
		bool _decode();
};

solver::solver():_sat_in("sat_in"),_sat_out("sat_out"){
	_var2pv.push_back(pv(-1, -1, -1)); //dummy [0]
}

void solver::read_board(char* filename){
	ifstream fin(filename);
	int n;
	while(!fin.eof()){
		fin >> n;
		_board.push_back(n);
	}
	fin.close();
	_N = sqrt(_board.size());
	_squN = sqrt(_N);
	_gen_candi();
}

void solver::_gen_candi(){
	bool row_has[_N][_N]={{false}}, col_has[_N][_N]={{false}}, squ_has[_N][_N]={{false}};
	for(int r=0; r<_N; r++){
		for(int c=0; c<_N; c++){
			int n = _board[r*_N+c];
			if(n!=0){
				row_has[r][n-1] = true;
				col_has[c][n-1] = true;
				squ_has[r/_squN*_squN + c/_squN][n-1] = true;
			}
			else{
				_posi_candi.push_back(pc(r,c));
			}
		}
	}
	for(int i=0; i<_posi_candi.size(); i++){
		int r = _posi_candi[i].r;
		int c = _posi_candi[i].c;
		int s = r/_squN*_squN + c/_squN;
		for(int n=0; n<_N; n++){
			if(!row_has[r][n] && !col_has[c][n] && !squ_has[s][n])
				_posi_candi[i].candi.push_back(n+1);
		}
	}
	//output _posi_candi
	ofstream fout("posi_candi");
	for(int i=0; i<_posi_candi.size(); i++){
		int r = _posi_candi[i].r;
		int c = _posi_candi[i].c;
		fout << "(" << r << " , " << c << "): ";
		for(int j=0; j<_posi_candi[i].candi.size(); j++){
			fout << _posi_candi[i].candi[j] << ' ';
		}
		fout << endl;
	}
}

void solver::cnf_encode(){
	_candi_constraint();
	_rcs_constraint();
	// output the _var2pv
	ofstream fout("var2pv");
	for(int i=1; i<_var2pv.size(); i++){
		int r = _var2pv[i].r;
		int c = _var2pv[i].c;
		int v = _var2pv[i].v;
		fout << i << ": " << r << ' ' << c << ' ' << v << endl;
	}
	fout.close();
	_gen_go_input_file();
}

void solver::_candi_constraint(){
	for(int i=0; i<_posi_candi.size(); i++){
		int r = _posi_candi[i].r;
		int c = _posi_candi[i].c;
		for(int j=0; j<_posi_candi[i].candi.size(); j++){
			int v = _posi_candi[i].candi[j];
			_var2pv.push_back(pv(r, c, v));
		}
		int n_candi = _posi_candi[i].candi.size();
		int var_idx_head = _var2pv.size() - n_candi;
		int var_idx_tail = var_idx_head + n_candi - 1;
		_group_handler(var_idx_head, var_idx_tail);
	}
}

void solver::_rcs_constraint(){
	struct cv count_r_v[_N][_N], count_c_v[_N][_N], count_s_v[_N][_N];
	for(int i=1; i<_var2pv.size(); i++){
		int v = _var2pv[i].v;
		if(v != -1){
			int r = _var2pv[i].r;
			int c = _var2pv[i].c;
			int s = r/_squN*_squN + c/_squN;
			count_r_v[r][v-1].count++;
			count_r_v[r][v-1].vars.push(i);
			count_c_v[c][v-1].count++;
			count_c_v[c][v-1].vars.push(i);
			count_s_v[s][v-1].count++;
			count_s_v[s][v-1].vars.push(i);
		}
	}
	for(int r=0; r<_N; r++)
		for(int v=0; v<_N; v++)
			if(count_r_v[r][v].count > 1)
				_group_handler(count_r_v[r][v].vars);
			else 
				while(!count_r_v[r][v].vars.empty())
					count_r_v[r][v].vars.pop();
	for(int c=0; c<_N; c++)
		for(int v=0; v<_N; v++)
			if(count_c_v[c][v].count > 1)
				_group_handler(count_c_v[c][v].vars);
			else 
				while(!count_c_v[c][v].vars.empty())
					count_c_v[c][v].vars.pop();
	for(int s=0; s<_N; s++)
		for(int v=0; v<_N; v++)
			if(count_s_v[s][v].count > 1)
				_group_handler(count_s_v[s][v].vars);
			else 
				while(!count_s_v[s][v].vars.empty())
					count_s_v[s][v].vars.pop();
}


void solver::_group_handler(int idx_head, int idx_tail){
	int rest = idx_tail - idx_head + 1;
	int vh = idx_head;
	int gh = idx_tail + 1;
	while(rest > 3){
		int n_group = rest / 3;
		for(int i=0; i<n_group; i++){
			_var2pv.push_back(pv(-1, -1, -1));
			_add_clause(vh, vh+1, vh+2, gh);
			vh += 3;
			gh++;
		}
		rest = gh - vh;
	}
	_no_group_handler(vh, gh-1);
}

void solver::_group_handler(queue<int> &vars){
	int rest = vars.size();
	while(rest > 3){
		int n_group = rest / 3;
		for(int i=0; i<n_group; i++){
			_var2pv.push_back(pv(-1, -1, -1));
			int g = _var2pv.size() - 1;
			vars.push(g);
			int v1 = vars.front();
			vars.pop();
			int v2 = vars.front();
			vars.pop();
			int v3 = vars.front();
			vars.pop();
			_add_clause(v1, v2, v3, g);
		}
		rest = vars.size();
	}
	_no_group_handler(vars);
}

void solver::_no_group_handler(int idx_head, int idx_tail){
	int n_candi = idx_tail - idx_head + 1;
	switch(n_candi){
		case 3:
			_add_clause(idx_head, idx_head+1, idx_tail);
			break;
		case 2:
			_add_clause(idx_head, idx_tail);
			break;
		case 1:
			_add_clause(idx_head);
			break;
		default:
			break;
	}
}

void solver::_no_group_handler(queue<int> &vars){
	int v1, v2, v3;
	switch(vars.size()){
		case 3:
			v1 = vars.front();
			vars.pop();
			v2 = vars.front();
			vars.pop();
			v3 = vars.front();
			vars.pop();
			_add_clause(v1, v2, v3);
			break;
		case 2:
			v1 = vars.front();
			vars.pop();
			v2 = vars.front();
			vars.pop();
			_add_clause(v1, v2);
			break;
		case 1:
			v1 = vars.front();
			vars.pop();
			_add_clause(v1);
			break;
		default:
			break;
	}
}

void solver::_add_clause(int v1, int v2, int v3, int g){
	if(g != 0){
		vector<int> c[7];
		c[0].push_back(-v1); c[0].push_back(-v2);
		c[1].push_back(-v1); c[1].push_back(-v3);
		c[2].push_back(-v2); c[2].push_back(-v3);
		c[3].push_back(v1); c[3].push_back(v2); c[3].push_back(v3); c[3].push_back(-g);
		c[4].push_back(-v1); c[4].push_back(g);
		c[5].push_back(-v2); c[5].push_back(g);
		c[6].push_back(-v3); c[6].push_back(g);
		for(int i=0; i<7; i++)
			_clauses.push_back(c[i]);
	}
	else if(v3 != 0){
		vector<int> c[4];
		c[0].push_back(v1); c[0].push_back(v2); c[0].push_back(v3);
		c[1].push_back(-v1); c[1].push_back(-v2);
		c[2].push_back(-v1); c[2].push_back(-v3);
		c[3].push_back(-v2); c[3].push_back(-v3);
		for(int i=0; i<4; i++)
			_clauses.push_back(c[i]);
	}
	else if(v2 != 0){
		vector<int> c[2];
		c[0].push_back(v1); c[0].push_back(v2);
		c[1].push_back(-v1); c[1].push_back(-v2);
		for(int i=0; i<2; i++)
			_clauses.push_back(c[i]);
	}
	else{
		vector<int> c;
		c.push_back(v1);
		_clauses.push_back(c);
	}
}

void solver::go(char* sat_name){
	_gen_go_input_file();
	string sat(sat_name);
	string cmd = "./" + sat + " " + _sat_in + " " + _sat_out;
	system(cmd.c_str());
}

void solver::_gen_go_input_file(){
	ofstream fout(_sat_in.c_str());
	fout << "p cnf " << _var2pv.size()-1 << ' ' << _clauses.size() << endl;
	for(int i=0; i<_clauses.size(); i++){
		for(int j=0; j<_clauses[i].size(); j++)
			fout << _clauses[i][j] << ' ';
		fout << '0' << endl;
	}
	fout.close();
}

void solver::write_result(char* result_name){
	bool solved = _decode();
	ofstream fout(result_name);
	if(solved){
		for(int r=0; r<_N; r++){
			for(int c=0; c<_N; c++){
				fout << _board[r*_N+c] << ' ';
			}
			fout << endl;
		}
	}
	else
		fout << "NO";
	fout.close();
}

bool solver::_decode(){
	ifstream fin(_sat_out.c_str());
	string status;
	fin >> status;
	if(status == "UNSAT"){
		fin.close();
		return false;
	}
	else{
		while(!fin.eof()){
			int n;
			fin >> n;
			if(n>0 && _var2pv[n].r != -1){
				int r = _var2pv[n].r;
				int c = _var2pv[n].c;
				int v = _var2pv[n].v;
				_board[r*_N+c] = v;
			}
		}
	}
	fin.close();
	return true;
}

int main(int argc, char* argv[]){
	solver sv;
	sv.read_board(argv[1]);
	sv.cnf_encode();
	//sv.go(argv[3]);
	//sv.write_result(argv[2]);
	return 0;
}
