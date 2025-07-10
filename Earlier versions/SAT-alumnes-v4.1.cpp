#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

uint numVars;
uint numClauses;
vector<vector<int> > clauses;
vector<int> model;
vector<int> modelStack;
uint indexOfNextLitToPropagate;
uint decisionLevel;

vector<vector<int>> posLit; // vector on s'indica les clausules en que la variable (index) surt en literal positiu
vector<vector<int>> negLit; // vector on s'indica les clausules en que la variable (index) surt en literal negatiu
vector<int> occurLit; // vector on s'indica el número de clausules en que la variable (index) surt
vector<int> ordOccurLit; // vector de variables ordenat per ordre descencent pel contingut de occurLit
vector<int> pureLit; // vector on s'indica si una variable surt sempre en literal positiu (1),
					 // literal negatiu (-1), o en ambdós tipus (2)
vector<int> vsidsLit; // vector on s'indica una puntuacio per a escollir la seguent variable a donar valor
vector<int> confLit; // vector on s'indica el numero de conflictes en els que ha aparegut cada variable
vector<int> signLit; // vector on s'indica el balanç de conflictes positius i negatius
					 // un balanç de conflictes positius tindra un numero positiu, un balanç
					 // de conflictes negatius tindra un numero negatiu i quan mes igualats
					 // mes proper el valor estara a 0
uint stepsCounter; // comptador de pasos

void readClauses( ){
	// Skip comments
	char c = cin.get();
	while (c == 'c') {
		while (c != '\n')
			c = cin.get();
		c = cin.get();
	}	
	// Read "cnf numVars numClauses"
	string aux;
	cin >> aux >> numVars >> numClauses;
	clauses.resize(numClauses);

	posLit.resize(numVars+1);
	negLit.resize(numVars+1);
	occurLit.resize(numVars+1);
	ordOccurLit.resize(numVars+1, -1);
	pureLit.resize(numVars+1);
	vsidsLit.resize(numVars+1);
	confLit.resize(numVars+1);
	signLit.resize(numVars+1);

	// Read clauses
	for (uint i = 0; i < numClauses; ++i) {
		int lit;
		while (cin >> lit and lit != 0) {
			clauses[i].push_back(lit);

			uint var = abs(lit); // 1 <= var <= numVars
			if (lit >= 0) posLit[var].push_back(i);
			else negLit[var].push_back(i);

			occurLit[var]++;

			if (lit >= 0) {
				if (pureLit[var] == 0) pureLit[var] = 1;
				else if (pureLit[var] == -1) pureLit[var] = 2;
			}
			else {
				if (pureLit[var] == 0) pureLit[var] = -1;
				else if (pureLit[var] == 1) pureLit[var] = 2;
			}
		}
	}
	
	// construir el ordOccurLit
	for (uint i=1; i<occurLit.size(); ++i) {
		int occurrences = occurLit[i];
		int j = 0;
		int var = ordOccurLit[j];
		bool greater = false;
		while (var != -1 and not greater) {
			if (occurrences > occurLit[var])
				greater = true;
			else {
				++j;
				var = ordOccurLit[j];
			}
		}
		if (greater) {
			for (int k=i; k>j; --k)
				ordOccurLit[k] = ordOccurLit[k-1];
		}
		ordOccurLit[j] = i;
	}
	ordOccurLit[ordOccurLit.size()-1] = 0;
	// // COMPROVACION OCCURLIT Y ORDOCCURLIT
	// for (int i=0; i<occurLit.size(); ++i)
	// 	cout << i << '=' << occurLit[i] << ' ';
	// cout << endl;
	// for (int i=0; i<ordOccurLit.size(); ++i)
	// 	cout << i << '=' << ordOccurLit[i] << '(' << occurLit[ordOccurLit[i]] << ") ";
	// cout << endl;

	for (uint var=0; var<occurLit.size(); ++var) {
		vsidsLit[var] = occurLit[var];
	}
}


int currentValueInModel(int lit){
	if (lit >= 0) return model[lit];
	else {
		if (model[-lit] == UNDEF) return UNDEF;
		else return 1 - model[-lit];
	}
}


void setLiteralToTrue(int lit){
	modelStack.push_back(lit);
	if (lit > 0) model[lit] = TRUE;
	else model[-lit] = FALSE;
}


bool propagateGivesConflict ( ) {
	while ( indexOfNextLitToPropagate < modelStack.size() ) {
		int litToPropagate = modelStack[indexOfNextLitToPropagate];
		uint varLit = abs(litToPropagate); // 1 <= var <= numVars
		vector<int> conflictClauses;
		if (litToPropagate >= 0) conflictClauses = negLit[varLit];
		else conflictClauses = posLit[varLit];
		for (uint i : conflictClauses) {
			bool someLitTrue = false;
			int numUndefs = 0;
			int lastLitUndef = 0;
			for (uint k=0; not someLitTrue and k<clauses[i].size(); ++k) {
				int val = currentValueInModel(clauses[i][k]);
				if (val == TRUE) someLitTrue = true;
				else if (val == UNDEF){
					++numUndefs;
					lastLitUndef = clauses[i][k];
				}
			}
			if (not someLitTrue and numUndefs == 0) {
				for (uint k=0; k<clauses[i].size(); ++k) {
					int lit = clauses[i][k];
					uint var = abs(lit);
					confLit[var]++;
					if (lit >= 0) signLit[var]++;
					else signLit[var]--;
					vsidsLit[var] = occurLit[var] + confLit[var] * decisionLevel;
				}
				return true; // conflict! all lits false
			}
			else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);
		}

		++indexOfNextLitToPropagate;
		++stepsCounter;
	}
	return false;
}


void backtrack(){
	uint i = modelStack.size() -1;
	int lit = 0;
	while (modelStack[i] != 0){ // 0 is the DL mark
		lit = modelStack[i];
		model[abs(lit)] = UNDEF;
		modelStack.pop_back();
		--i;
	}
	// at this point, lit is the last decision
	modelStack.pop_back(); // remove the DL mark
	--decisionLevel;
	indexOfNextLitToPropagate = modelStack.size();
	setLiteralToTrue(-lit);	// reverse last decision
}


// Heuristic for finding the next decision literal:
int getNextDecisionLiteral(){
	int nextDecLit = 0;
	uint i = 0;
	int found = 0;
	while (i<ordOccurLit.size() and found < 5) {
		int var = ordOccurLit[i];
		// cout << nextDecLit << ' ' << vsidsLit[nextDecLit] << endl;
		// cout << var << ' ' << vsidsLit[var] << endl;
		if (currentValueInModel(var) == UNDEF and vsidsLit[var] > vsidsLit[nextDecLit]) {
			++found;
			nextDecLit = var;
		}
		++i;
	}
	return nextDecLit;
/*
	int nextDecLit = 0;
	uint i = 0;
	bool found = false;
	while (i<ordOccurLit.size() and not found) {
		int var = ordOccurLit[i];
		if (currentValueInModel(var) == UNDEF) {
			found = true;
			nextDecLit = var;
		}
		++i;
	}
	return nextDecLit;*/
}


void checkmodel(){
	for (uint i = 0; i < numClauses; ++i){
		bool someTrue = false;
		for (uint j = 0; not someTrue and j < clauses[i].size(); ++j)
			someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
		if (not someTrue) {
			cout << "Error in model, clause is not satisfied:";
			for (uint j = 0; j < clauses[i].size(); ++j)
				cout << clauses[i][j] << " ";
			cout << endl;
			exit(1);
		}
	}	
}


int main(){ 
	readClauses(); // reads numVars, numClauses and clauses
	model.resize(numVars+1,UNDEF);

	// pure-literal variables value assignation
	for (uint var=1; var<=numVars; ++var) {
		if (pureLit[var] == 1) setLiteralToTrue(var);
		else if (pureLit[var] == -1) setLiteralToTrue(-var);
	}
	
	// Take care of initial unit clauses, if any
	for (uint i = 0; i < numClauses; ++i)
		if (clauses[i].size() == 1) {
			int lit = clauses[i][0];
			int var = currentValueInModel(lit);
			if (var == FALSE) {cout << "UNSATISFIABLE" << endl; return 10;}
			else if (var == UNDEF) setLiteralToTrue(lit);
		}
	
	indexOfNextLitToPropagate = 0;
	decisionLevel = 0;

	stepsCounter = 0;
	
	// DPLL algorithm
	while (true) {
		if (stepsCounter % 5000 == 0) {
			for (uint var=1; var<vsidsLit.size(); ++var) {
				confLit[var] /= 2;
			}
		}

		while ( propagateGivesConflict() ) {
			if ( decisionLevel == 0) { cout << "UNSATISFIABLE" << endl; return 10; }
			backtrack();
		}
		int decisionLit = getNextDecisionLiteral();
		if (decisionLit == 0) { checkmodel(); cout << "SATISFIABLE" << endl; return 20; }
		// start new decision level:
		modelStack.push_back(0);	// push mark indicating new DL
		++indexOfNextLitToPropagate;
		++decisionLevel;
		setLiteralToTrue(decisionLit);	// now push decisionLit on top of the mark
	}
}
