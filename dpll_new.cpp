#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <omp.h>
#include <string>
#include <vector>
#include <fstream>
using namespace std;

enum Cat
{
	satisfied,
	unsatisfied,
	normal,
	completed,
	terminated
};

class Formula
{
	public:

		vector<int> literals;
	vector<int> literal_frequency;

	vector<int> literal_polarity;

	vector<vector < int>> clauses;
	Formula() {}

	Formula(const Formula &f)
	{
		literals = f.literals;
		clauses = f.clauses;
		literal_frequency = f.literal_frequency;
		literal_polarity = f.literal_polarity;
	}
};

class SATSolverDPLL
{
	private:
		Formula formula;
	int literal_count;
	int clause_count;
	int unit_propagate(Formula &);
	int DPLL(Formula);
	int apply_transform(Formula &, 		int);
	void show_result(Formula &, int);
	int *completed;
	public:
		SATSolverDPLL(int & c)
		{
			completed = &c;
		}
	void initialize(string);
	int solve();
	void print_result(int);
};

void SATSolverDPLL::print_result(int result)
{
	if (result == Cat::normal)
	{
		show_result(formula, Cat::unsatisfied);
	}
}

void SATSolverDPLL::initialize(string filename)
{
	char c;
	string s;

	ifstream in (filename);
	streambuf *cinbuf = cin.rdbuf();
	cin.rdbuf(in .rdbuf());

	while (true)
	{
		cin >> c;
		if (c == 'c')
		{
			getline(cin, s);
		}
		else
		{
			cin >> s;
			break;
		}
	}
	cin >> literal_count;
	cin >> clause_count;

	formula.literals.clear();
	formula.literals.resize(literal_count, -1);
	formula.clauses.clear();
	formula.clauses.resize(clause_count);
	formula.literal_frequency.clear();
	formula.literal_frequency.resize(literal_count, 0);
	formula.literal_polarity.clear();
	formula.literal_polarity.resize(literal_count, 0);

	int literal;

	for (int i = 0; i < clause_count; i++)
	{
		while (true)
		{
			cin >> literal;
			if (literal > 0)
			{
				formula.clauses[i].push_back(2 *
					(literal - 1));

				formula.literal_frequency[literal - 1]++;
				formula.literal_polarity[literal - 1]++;
			}
			else if (literal < 0)
			{
				formula.clauses[i].push_back(2 *((-1) *literal - 1) +
					1);

				formula.literal_frequency[-1 - literal]++;
				formula.literal_polarity[-1 - literal]--;
			}
			else
			{
				break;
			}
		}
	}
}
int SATSolverDPLL::unit_propagate(Formula & f)
{
	bool unit_clause_found =
		false;
	if (f.clauses.size() == 0)
	{
		return Cat::satisfied;
	}
	do {
		unit_clause_found = false;

		for (int i = 0; i < f.clauses.size(); i++)
		{
			if (f.clauses[i].size() ==
				1)
			{
				unit_clause_found = true;
				f.literals[f.clauses[i][0] / 2] =
					f.clauses[i][0] % 2;
				f.literal_frequency[f.clauses[i][0] / 2] = -1;
				int result = apply_transform(f, f.clauses[i][0] /
					2);

				if (result == Cat::satisfied || result == Cat::unsatisfied)
				{
					return result;
				}
				break;
			}
			else if (f.clauses[i].size() == 0)
			{
				return Cat::unsatisfied;
			}
		}
	} while (unit_clause_found);

	return Cat::normal;
}
int SATSolverDPLL::apply_transform(Formula &f, int literal_to_apply)
{
	int value_to_apply = f.literals[literal_to_apply];

	for (int i = 0; i < f.clauses.size(); i++)
	{

		for (int j = 0; j < f.clauses[i].size(); j++)
		{

			if ((2 *literal_to_apply + value_to_apply) == f.clauses[i][j])
			{
				f.clauses.erase(f.clauses.begin() +
					i);
				i--;
				if (f.clauses.size() ==
					0)
				{
					return Cat::satisfied;
				}
				break;
			}
			else if (f.clauses[i][j] / 2 ==
				literal_to_apply)
			{
				f.clauses[i].erase(					f.clauses[i].begin() +
					j);
				j--;
				if (f.clauses[i].size() ==
					0)
				{
					return Cat::unsatisfied;
				}
				break;
			}
		}
	}

	return Cat::normal;
}
int SATSolverDPLL::DPLL(Formula f)
{
	if (*completed == 1)
	{
		return Cat::terminated;
	}
	int result = unit_propagate(f);
	if (result == Cat::satisfied)
	{
		show_result(f, result);
		return Cat::completed;
	}
	else if (result == Cat::unsatisfied)

	{
		return Cat::normal;
	}

	int i = distance(		f.literal_frequency.begin(),
		max_element(f.literal_frequency.begin(), f.literal_frequency.end()));

	for (int j = 0; j < 2; j++)
	{
		Formula new_f = f;
		if (new_f.literal_polarity[i] >
			0)
		{
			new_f.literals[i] = j;
		}
		else
		{
			new_f.literals[i] = (j + 1) % 2;
		}
		new_f.literal_frequency[i] = -1;
		int transform_result =
			apply_transform(new_f, i);
		if (transform_result ==
			Cat::satisfied)
		{
			show_result(new_f, transform_result);
			return Cat::completed;
		}
		else if (transform_result == Cat::unsatisfied)

		{

			continue;
		}
		int dpll_result = DPLL(new_f);
		if (dpll_result == Cat::completed)
		{
			return dpll_result;
		}
	}

	return Cat::normal;
}

void SATSolverDPLL::show_result(Formula &f, int result)
{

	int tid = omp_get_thread_num();
	printf("thread num = %d\n", tid);
	if (result == Cat::satisfied)
	{
		printf("SAT\n");
		for (int i = 0; i < f.literals.size(); i++)
		{
			if (i != 0)
			{
				cout << " ";
			}
			if (f.literals[i] != -1)
			{
				cout << pow(-1, f.literals[i]) *(i + 1);
			}
			else

			{

				cout << (i + 1);
			}
		}
		cout << " 0\n";
	}
	else
	{
		cout << "UNSAT";
	}
}

int SATSolverDPLL::solve()
{
	int result = DPLL(formula);

	return result;
}

int main()
{
	int completed = 0;
    #pragma omp parallel default (none) shared(completed)
	{
		SATSolverDPLL solver(completed);
        #pragma omp critical
		solver.initialize("problem1.cnf");
		int result = solver.solve();
        #pragma omp critical
		{
			if (completed == 0)
			{
				completed = 1;
				solver.print_result(result);
			}
		}
	}
	return 0;
}