#include "gurobi_c++.h"
#include <fstream>
#include <cmath>
#include <stdlib.h>
#include <stdio.h>
#include <iostream>
#include <fstream>
#include <locale>
#include <vector>
#include <ctime>
#include <random>
#include <algorithm>
#include <queue>
using namespace std;

bool DEBUG = true;
ofstream logger("log.txt");

struct Solution {
	vector<int> p;
	int q;
	int W;
	int Z;
};

struct Solution_uniform {
	int p;
	int q;
	int W;
	int Z;
};

struct Price {
	int N = 1;
	vector<int> l = vector<int>(1);
	vector<int> r = vector<int>(1);
};

vector<Price> creation(int Ml, vector<int> Pmax) {
	vector<Price> P;
	Price Helper = Price();

	for (int i = 0; i < Ml; i++) {
		Helper.r[0] = Pmax[i];
		P.push_back(Helper);
	}

	return P;
}

void note(vector<Price>& P, int N, vector<int> l, vector<int> r) {
	P[N].l.clear();
	P[N].r.clear();
	P[N].l = l;
	P[N].r = r;
	//for(int i = 0; i < l.size(); i++) {
	//	P[N].l.push_back(l[i]);
	//	P[N].r.push_back(r[i]);
	//}
}

void printIt(vector<vector<int>> &M, ofstream & output)
{
	for (int i = 0; i < M.size(); i++)
		for (int j = 0; j < M[0].size(); j++)
			output << M[i][j];
}

void printIt(vector<int> &vec, ostream& output)
{
	for (int i = 0; i < vec.size(); i++)
		output << vec[i] << ' ';

	output << endl;
}

void fragmentation(int K, vector<Price>& P) {
	for (int i = 0; i < P.size(); i++)
	{
		auto n = P[i].N;

		vector<int> l(K * n, 1);
		vector<int> r(K * n, 1);

		for (int j = 0; j < n; j++) {
			for (int k = 0; k < K; k++) {
				l[k	 + j * K] = k * (P[i].r[j] + 1 - P[i].l[j]) / K + P[i].l[j];
				r[k + j * K] = (k + 1) * (P[i].r[j] + 1 - P[i].l[j]) / K + P[i].l[j] - 1;
			}
			r[(j + 1) * K - 1] = P[i].r[j];
		}

		P[i].l = l;
		P[i].r = r;
		P[i].N *= K;
	}
	
	if (DEBUG){
		for (size_t i = 0; i < P.size(); i++)
		{
			logger << "i = " << i << endl;
			logger << "r : ";
			printIt(P[i].r, logger);
			//for (size_t j = 0; j < P[i].r.size(); j++)
			//	cout << P[i].r[j] << ' ';
			//cout << endl << "l : ";
			logger << "l : ";
			printIt(P[i].l, logger);
			//for (size_t j = 0; j < P[i].l.size(); j++)
			//	cout << P[i].l[j] << ' ';
			//cout << endl;
		}
	}
}

struct Segment {
	int l;
	int r;
	int cnt;
};

int Ml, Mf, N;
const int price = 100;

bool operator< (const Segment &a, const Segment &b) {
	return a.r * a.cnt < b.r * b.cnt;
}

void AddVariables(vector<int>& price_min,
	vector<int>& price_max, 
	GRBModel& model, 
	vector<vector<GRBVar>>& x,
	vector<vector<GRBVar>>& w,
	vector<vector<GRBVar>>& z,
	vector<GRBVar>& p) 
{
	for (int i = 0; i < Ml; i++)//границы цен, Обязательно! + тип
		p[i] = model.addVar(price_min[i], price_max[i], 0.0, GRB_INTEGER);//узнать как в гуроби заводить даблы //q is Z+ (4)

	for (int i = 0; i < Ml + Mf; i++) //то же самое для х
		for (int j = 0; j < N; j++)
			x[i][j] = model.addVar(0, 1, 0.0, GRB_BINARY);// x is B (9)

	for (int i = 0; i < Ml; i++) //то же самое для w
		for (int j = 0; j < N; j++)
			w[i][j] = model.addVar(0, price_max[i] * Ml, 0.0, GRB_INTEGER);

	for (int i = 0; i < Mf; i++) //то же самое для z
		for (int j = 0; j < N; j++)
			z[i][j] = model.addVar(0, price * Mf, 0.0, GRB_INTEGER);
	model.update();
}

void SetObjective(GRBModel& model, vector<vector<GRBVar>>& w) {
	model.set(GRB_IntAttr_ModelSense, GRB_MAXIMIZE);//модель максимизируется
	GRBLinExpr obj = 0;//считает текущее значение целевой функции
	for (int i = 0; i < w.size(); i++)
		for (int j = 0; j < N; j++)
			obj += w[i][j]; // (1)
	model.setObjective(obj);//объявили, что будем максимизировать
}

void AddRestriction5(GRBModel& model, vector<vector<GRBVar>>& x, vector<vector<GRBVar>>& w, vector<vector<GRBVar>>& z, vector<int>& cf, vector<vector<int>>& cl) {
	vector<GRBLinExpr> Restriction_5(N);
	for (int j = 0; j < N; j++) {
		Restriction_5[j] = 0;
		for (int i = 0; i < Ml; i++)
			Restriction_5[j] += x[i][j] * cl[i][j] - w[i][j];
		for (int i = 0; i < Mf; i++)
			Restriction_5[j] += x[i + Ml][j] * cf[j] - z[i][j]; // (5)
		model.addConstr(Restriction_5[j] >= 0.0);
	}
}

void AddRestriction6(GRBModel& model, vector<vector<GRBVar>>& x, vector<vector<GRBVar>>& w, vector<vector<GRBVar>>& z, vector<int>& cf, vector<vector<int>>& cl, vector<GRBVar>& p) {
	vector<vector<GRBLinExpr>> Restriction_6(Ml, vector<GRBLinExpr>(N));
	for (int k = 0; k < Ml; k++) {
		for (int j = 0; j < N; j++) {
			Restriction_6[k][j] = price - cl[k][j] + p[k];
			for (int i = 0; i < Ml; i++) {
				Restriction_6[k][j] -= x[i][j] * (price - cl[i][j]) + w[i][j];
			}
			for (int i = 0; i < Mf; i++) {
				Restriction_6[k][j] -= x[i + Ml][j] * (price - cf[j]) + z[i][j];
			}
			model.addConstr(Restriction_6[k][j] >= 0.0);
		}
	}
}

void AddRestriction7(GRBModel& model, vector<vector<GRBVar>>& x, vector<vector<GRBVar>>& w, vector<vector<GRBVar>>& z, vector<int>& cf, vector<vector<int>>& cl, int q) {
	vector<vector<GRBLinExpr>> Restriction_7(Mf, vector<GRBLinExpr>(N));
	for (int k = 0; k < Mf; k++) {
		for (int j = 0; j < N; j++) {
			Restriction_7[k][j] = price - cf[j] + q;
			for (int i = 0; i < Ml; i++) {
				Restriction_7[k][j] -= x[i][j] * (price - cl[i][j]) + w[i][j]; // <--- ограничение (7)
			}
			for (int i = 0; i < Mf; i++) {
				Restriction_7[k][j] -= x[i + Ml][j] * (price - cf[j]) + z[i][j]; // <--- ограничение (7)
			}
			model.addConstr(Restriction_7[k][j] >= 0.0);
		}
	}
}

void AddRestriction8(GRBModel& model, vector<vector<GRBVar>>& x) {
	vector<GRBLinExpr> Restriction_8(N);
	for (int j = 0; j < N; j++) {
		Restriction_8[j] = 0;
		for (int i = 0; i < Ml + Mf; i++)
			Restriction_8[j] += x[i][j];
		model.addConstr(Restriction_8[j] <= 1.0);
	}
}

void AddRestriction10(GRBModel& model, vector<vector<GRBVar>>& x, vector<vector<GRBVar>>& w, vector<int>& pmax, vector<GRBVar>& p) {
	vector<vector<GRBLinExpr>> Restriction_10(Ml, vector<GRBLinExpr>(N));
	for (int i = 0; i < Ml; i++) {
		for (int j = 0; j < N; j++) {
			Restriction_10[i][j] = (1 - x[i][j]) * pmax[i] - w[i][j] + p[i];
			model.addConstr(Restriction_10[i][j] >= 0.0);
		}
	}
}

void AddRestriction11(GRBModel& model, vector<vector<GRBVar>>& x, vector<vector<GRBVar>>& w, vector<int>& pmax, vector<GRBVar>& p) {
	vector<vector<GRBLinExpr>> Restriction_11(Ml, vector<GRBLinExpr>(N));
	for (int i = 0; i < Ml; i++) {
		for (int j = 0; j < N; j++) {
			Restriction_11[i][j] = (1 - x[i][j]) * pmax[i] + w[i][j] - p[i]; // (10)
			model.addConstr(Restriction_11[i][j] >= 0.0);
		}
	}
}

void AddRestriction12(GRBModel& model, vector<vector<GRBVar>>& x, vector<vector<GRBVar>>& w, vector<int>& pmax) {
	vector<vector<GRBLinExpr>> Restriction_12(Ml, vector<GRBLinExpr>(N));
	for (int i = 0; i < Ml; i++) {
		for (int j = 0; j < N; j++) {
			Restriction_12[i][j] = x[i][j] * pmax[i] - w[i][j];
			model.addConstr(Restriction_12[i][j] >= 0.0);
		}
	}
}

void AddRestriction13(GRBModel& model, vector<vector<GRBVar>>& x, vector<vector<GRBVar>>& z, int qmax, int q) {
	vector<vector<GRBLinExpr>> Restriction_13(Mf, vector<GRBLinExpr>(N));
	for (int i = 0; i < Mf; i++) {
		for (int j = 0; j < N; j++) {
			Restriction_13[i][j] = (1 - x[i + Ml][j])* qmax - z[i][j] + q;
			model.addConstr(Restriction_13[i][j] >= 0.0);
		}
	}
}

void AddRestriction14(GRBModel& model, vector<vector<GRBVar>>& x, vector<vector<GRBVar>>& z, int qmax, int q) {
	vector<vector<GRBLinExpr>> Restriction_14(Mf, vector<GRBLinExpr>(N));
	for (int i = 0; i < Mf; i++) {
		for (int j = 0; j < N; j++) {
			Restriction_14[i][j] = (1 - x[i + Ml][j]) * qmax + z[i][j] - q;
			model.addConstr(Restriction_14[i][j] >= 0.0);
		}
	}
}

void AddRestriction15(GRBModel& model, vector<vector<GRBVar>>& x, vector<vector<GRBVar>>& z, int qmax) {
	vector<vector<GRBLinExpr>> Restriction_15(Mf, vector<GRBLinExpr>(N));
	for (int i = 0; i < Mf; i++) {
		for (int j = 0; j < N; j++) {
			Restriction_15[i][j] = x[i + Ml][j] * qmax - z[i][j];
			model.addConstr(Restriction_15[i][j] >= 0.0);
		}
	}
}

/*Solution RMP_old(priority_queue<Segment>& q) {
	Solution SolRMP;
	Segment s = q.top();
	q.pop();
	SolRMP.W = s.r * s.cnt;
	SolRMP.p = s.r;
	SolRMP.Z = 0;
	if (s.l != s.r) {
	s.r--;
	q.push(s);
	}
	return SolRMP;
	}*/
/*
Solution FP_old(vector<int> cl, vector<vector<int>> cf, int pmax, vector<int> qmax, int p) {
cout << "FP SOLVING HERE" << endl;
GRBEnv env = GRBEnv(); //создание модели
GRBModel model_FP = GRBModel(env); //имя модели

vector<vector<GRBVar>> x(Mlmin + Mf, vector<GRBVar>(N));
vector<vector<GRBVar>> w(Mlmin, vector<GRBVar>(N));
vector<vector<GRBVar>> z(Mf, vector<GRBVar>(N));
vector<GRBVar> q(Mf);


AddVariables(model_FP, x, w, z, q);

SetObjective(model_FP, w, z, p);

AddRestriction5(model_FP, x, w, z, cl, cf);

AddRestriction6(model_FP, x, w, z, cl, cf, p);

AddRestriction7(model_FP, x, w, z, cl, cf, q);

AddRestriction8(model_FP, x);

AddRestriction10(model_FP, x, w, pmax, p);

AddRestriction11(model_FP, x, w, pmax, p);

AddRestriction12(model_FP, x, w, pmax);

AddRestriction13(model_FP, x, z, qmax, q);

AddRestriction14(model_FP, x, z, qmax, q);

AddRestriction15(model_FP, x, z, qmax);

model_FP.update();
model_FP.optimize();

//Запись полученного решения
Solution SolFP;
SolFP.p = p;
SolFP.Z = 0;
for (int i = 0; i < Mf; i++) {
for (int j = 0; j < N; j++) {
int b = z[i][j].get(GRB_DoubleAttr_X);
SolFP.Z += b;
}
}
SolFP.W = 0;
for (int i = 0; i < Ml; i++) {
for (int j = 0; j < N; j++) {
int b = w[i][j].get(GRB_DoubleAttr_X);
SolFP.W += b;
}
}
return SolFP;
};*/

Solution_uniform SB(priority_queue<Segment>& p) {
	Solution_uniform SolRMP;
	Segment s = p.top();
	p.pop();
	SolRMP.W = s.r * s.cnt;
	SolRMP.p = s.r;
	SolRMP.Z = 0;
	if (s.l != s.r) {
		s.r--;
		p.push(s);
	}
	return SolRMP;
}

Solution FP(vector<int> p, vector<int> cf, vector<vector<int>> cl, int qmax) {
	Solution cur;
	cur.p = p;
	cur.W = 0;
	cur.Z = 0;
	for (int q = 1; q <= qmax; q++) {
		int w = 0;
		int z = 0;
		for (int j = 0; j < N; j++) {
			bool flag_F = 1; //возможно 0
			bool flag_L = 0;
			if (q <= cf[j]) {
				for (int i = 0; i < Ml; i++) {
					if (cf[j] - q < cl[i][j] - p[i]) {
						flag_F = 0;
					}
				}
			}
			else {
				flag_F = 0;
			}
			int help = 0;
			int p_help = 0;
			if (!flag_F) {
				for (int i = 0; i < Ml; i++) {
					if (cl[i][j] - p[i] > help) {
						help = cl[i][j] - p[i];
						p_help = p[i];
						flag_L = 1;
					}
				}
			}
			if (flag_F) z += q;
			if (flag_L) w += p_help;
		}
		if ((cur.Z < z) || (cur.Z == z && cur.W < w)) {
			cur.Z = z;
			cur.W = w;
			cur.q = q;
		}
	}
	/*cout << "Optimum weigths : " << cur.W << endl;
	cout << "Optimum weigths Z : " << cur.Z << endl;
	cout << "Optimum weigths q : " << cur.q << endl;
	cout << "Optimum weigths p : " << cur.p[0] << endl;
	cout << "Optimum weigths p : " << cur.p[1] << endl;*/

	return cur;
}

Solution RMP(vector<int> cf, vector<vector<int>> cl, int qmax, vector<int> pmin, vector<int> pmax) {
	cout << "RMP SOLVING HERE" << endl;
	GRBEnv env = GRBEnv(); //создание модели
	GRBModel model_RMP = GRBModel(env); //имя модели

	vector<vector<GRBVar>> x(Ml + Mf, vector<GRBVar>(N));
	vector<vector<GRBVar>> w(Ml, vector<GRBVar>(N));
	vector<vector<GRBVar>> z(Mf, vector<GRBVar>(N));
	vector<GRBVar> p(Ml);
	//GRBVar q;


	AddVariables(pmin, pmax, model_RMP, x, w, z, p);
	SetObjective(model_RMP, w);

	int q = price + 1;
#pragma region AddRestrictions	
	AddRestriction5(model_RMP, x, w, z, cf, cl);
	AddRestriction6(model_RMP, x, w, z, cf, cl, p);
	AddRestriction7(model_RMP, x, w, z, cf, cl, q);
	AddRestriction8(model_RMP, x);
	AddRestriction10(model_RMP, x, w, pmax, p);
	AddRestriction11(model_RMP, x, w, pmax, p);
	AddRestriction12(model_RMP, x, w, pmax);
	AddRestriction13(model_RMP, x, z, qmax, q);
	//TODO: fix that restriction later
	//AddRestriction14(model_RMP, x, z, qmax, q);
	AddRestriction15(model_RMP, x, z, qmax);
#pragma endregion

	model_RMP.update();
	model_RMP.optimize();

	//Запись полученного решения
	Solution SolRMP;
	for (int i = 0; i < Ml; i++) {
		double help = p[i].get(GRB_DoubleAttr_X);
		SolRMP.p.push_back(help);
	}
	SolRMP.Z = 0;
	for (int i = 0; i < Mf; i++) {
		for (int j = 0; j < N; j++) {
			int b = z[i][j].get(GRB_DoubleAttr_X);
			SolRMP.Z += b;
		}
	}
	SolRMP.W = 0;
	for (int i = 0; i < Ml; i++) {
		for (int j = 0; j < N; j++) {
			int b = w[i][j].get(GRB_DoubleAttr_X);
			SolRMP.W += b;
		}
	}
	return SolRMP;
};

void cut(vector<Price>& P, vector<int> q, vector<vector<int>>cl, int qmax, vector<int> Pmax, Solution Sol_cur) {
	Solution SolRMP;
	for (int i = 0; i < Ml; i++) {
		vector<int> min(Ml, 1);
		vector<int> max = Pmax;

		for (int j = 0; j < P[i].N; j++) {
			min[i] = P[i].l[j];
			max[i] = P[i].r[j];
			SolRMP = RMP(q, cl, qmax, min, max);
			if (Sol_cur.W >= SolRMP.W) {
				for (int k = j; k < P[i].N; k--) {
					P[i].l[k] = P[i].l[k + 1];
					P[i].r[k] = P[i].r[k + 1];
				}
				P[i].N--;
			}
		}

	}
};

Solution Sol_opt;

void calc(int fixed_count, 
	vector<Price> P, 
	//Solution& Sol_cur, 
	vector<int> p, 
	vector<int> cf, 
	vector<vector<int>> cl, 
	int qmax) 
{
	for (int i = 0; i < P[fixed_count].N; i++) 
	{
		for (int j = P[fixed_count].l[i]; j <= P[fixed_count].r[i]; j++) 
		{
			p.push_back(j);
			
			if (p.size() == Ml)
			{
				Solution SOL_FP;
				SOL_FP = FP(p, cf, cl, qmax);
				
				if (SOL_FP.W > Sol_opt.W)
					Sol_opt = SOL_FP;
				
			} 
			else
			{
				calc(fixed_count + 1, P, p, cf, cl, qmax);
			}

			p.pop_back();
		}
	}

	return;
}



int main(void) {
	srand(10);
	ifstream input("input.txt");
	input >> Ml >> Mf >> N;

	vector<vector<int>> cl(Ml, vector<int>(N));
	vector<vector<int>> cf(Mf, vector<int>(N));
	//vector<int> b(N);

	ofstream output("output.txt");
	output << Ml << ' ' << Mf << ' ' << N << endl << endl;

	for (int i = 0; i < Ml; i++) {//для чтения данных из файла 
		for (int j = 0; j < N; j++) {
			input >> cl[i][j];
			output << cl[i][j] << ' ';
		}
		output << endl;
	}
	output << endl;

	for (int i = 0; i < Mf; i++) {
		for (int j = 0; j < N; j++) {
			input >> cf[i][j];
			output << cf[i][j] << ' ';
		}
		output << endl;
	}
	output << endl;


	Solution Sol_cur;
	Sol_cur.p.assign(Ml, 0);

	for (int i = 0; i < Ml; i++)
		input >> Sol_cur.p[i];

	input >> Sol_cur.q;
	input >> Sol_cur.W;
	input >> Sol_cur.Z;

	/*
	for (int i = 0; i < Ml; i++) {//для генерирования
	for (int j = 0; j < N; j++) {
	cl[i][j] = 100 - rand() %(100);
	output << cl[i][j] << "  ";
	}
	output << endl;
	}
	output << endl;
	for (int i = 0; i < Mf; i++) {
	for (int j = 0; j < N; j++) {
	cf[i][j] = 100 - rand()%(100);
	output << cf[i][j] << "  ";
	}
	output << endl;
	}
	output << endl;*/


	vector<int> p(N, 0);

	for (int i = 0; i < cl[0].size(); i++)
		for (int j = 0; j < cl.size(); j++)
			p[i] = max(p[i], cl[j][i]);


	int pmax = *max_element(p.begin(), p.end());

	for (int i = 0; i < N; i++)
		output << p[i] << ' ';

	output << endl;


	vector<int> Pmax(Ml, 0);

	for (int i = 0; i < Ml; i++)
		Pmax[i] = *max_element(cl[i].begin(), cl[i].end());

	vector<int> q(N, 0);

	for (int i = 0; i < cf[0].size(); i++)
		for (int j = 0; j < cf.size(); j++)
			q[i] = max(q[i], cf[j][i]);

	int qmax = *max_element(q.begin(), q.end());
	priority_queue<Segment> Queue;//возможно не нужно

	for (int j = 0; j < N; j++) {
		Segment s;
		if (j == 0) {
			s.l = 0;
		} else s.l = p[j - 1] + 1;
		s.r = p[j];
		if (s.l <= s.r) {
			s.cnt = N - j;
			Queue.push(s);
		}
	}

	Solution SolFP, SolSP;

	clock_t cutoff1 = clock(); //Содание блоков цены для лидера
	vector<Price> P;
	P = creation(Ml, Pmax);
	fragmentation(3, P);

	//cut(P, q, cl, qmax, Pmax, Sol_cur);
	//fragmentation(3, P);
	//cut(P, q, cl, qmax, Pmax, Sol_cur);
	clock_t cutoff2 = clock();


	clock_t search1 = clock();
	vector<int> r;
	calc(0, P, r, q, cl, qmax);
	cout << "Optimum weigths : " << Sol_opt.W << endl;
	cout << "Optimum weigths Z : " << Sol_opt.Z << endl;
	cout << "Optimum weigths q : " << Sol_opt.q << endl;
	cout << "Optimum weigths p : " << Sol_opt.p[0] << endl;
	cout << "Optimum weigths p : " << Sol_opt.p[1] << endl;

	clock_t search2 = clock();


	printIt(cl, output);
	printIt(cf, output);

	output << ' ' << Sol_cur.W << ' '
		<< Sol_cur.Z << ' '
		<< double(cutoff2 - cutoff1) / CLOCKS_PER_SEC << endl;


	system("pause");
	return 0;
}
