#include "basis.h"
#include "ProbCCAnr.h"
#include "cw.h"
#include "preprocessor.h"

#include <sys/times.h> //these two h files are for linux
#include <unistd.h>

//pick a var to be flip
int pick_var() {
	int         i,k,c,v,ci;
	int         bestVar=best_var;
	lit*		clause_c;
	double      randPosition_p,sumProb,randPosition,tempBest_var,tempV;
	int		    *truep,bbreakv,countBestV,bestV[goodvar_stack_fill_pointer];
	double      probs[max_clause_len];
	double      probCcd[goodvar_stack_fill_pointer],sumProbCcd;

	/**Greedy Mode**/
	/*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
	if(goodvar_stack_fill_pointer>0) {
		countBestV=0;
		best_var = goodvar_stack[0];

		for(i=1; i<goodvar_stack_fill_pointer; ++i) {//selecting a CCD variable in CCDvarsBest
			v=goodvar_stack[i];
			if(score[v]>score[best_var]) {
				best_var = v;
				countBestV=0;
			}
			else if(score[v]==score[best_var]) {
				bestV[countBestV]=v;
				countBestV++;
			}
		}
		if(countBestV>1) {//probabilistic selection-based exponential function for tie-breaking in CCD
			for(i=0; i<countBestV; i++) {
				v=bestV[i];
				probCcd[i] =probsBreak[breaks[v]];
				sumProbCcd += probCcd[i];
			}
			randPosition = (double) (rand()) / (RAND_MAX + 1.0) * sumProbCcd;
			for (i = i - 1; i != 0; i--) {
				sumProbCcd -= probCcd[i];
				if (sumProbCcd <= randPosition)
					break;
			}
			best_var = bestV[i];
		}
		return best_var;
	}

	/*SD (significant decreasing) mode, the level with aspiration*/
	best_var = 0;
	for(i=0; i<unsatvar_stack_fill_pointer; ++i) {//selecting a SD variable in SDvarsBest
		if(score[unsatvar_stack[i]]>sigscore) { 
			best_var = unsatvar_stack[i];
			break;
		}
	}
	for(++i; i<unsatvar_stack_fill_pointer; ++i) {
		v=unsatvar_stack[i];
		if(score[v]>score[best_var]) best_var = v;////1-level tie-breaking picking a variable in VarBest
		else if(score[v]==score[best_var]) {// //2-level tie-breaking strategy in VarBest  using the Lva function 
			tempBest_var=(double)vSelect[best_var]/(double)(step/num_vars+1)+gama*(double)(step+1-time_stamp[best_var])/(step+1);
			tempV=(double)vSelect[v]/(double)(step/num_vars+1)+gama*(double)(step+1-time_stamp[v])/(step+1);
			if(tempV>tempBest_var)	best_var = v;
		}
	}

	if(best_var!=0) return best_var;

	/**Diversification Mode**/

	update_clause_weights();

	/*focused random walk*/

	randPosition_p = (double) (rand()) / (RAND_MAX + 1.0);
	
	/* The diversification mode utilizing probabilistic selection */
	//probabilistic selection strategy in clause selection
	if(randPosition_p<p_first) {
		if(count_candidate_falseClause_first>0) {
			c =candidate_falseClause_first_stack[rand()%count_candidate_falseClause_first];
			count_SelectT_first++;
		} else {
			c=unsat_stack[rand()%unsat_stack_fill_pointer];
		}
	} else if((randPosition_p>p_first)&&(randPosition_p<(p_first+p_second))) {
		if(count_candidate_falseClause_second>0) {
			c =candidate_falseClause_second_stack[rand()%count_candidate_falseClause_second];
			count_SelectT_second++;
		} else {
			c=unsat_stack[rand()%unsat_stack_fill_pointer];
		}
	} else {
		c=unsat_stack[rand()%unsat_stack_fill_pointer];
	}


	count_selectCaluse[c]++;
	clause_c = clause_lit[c];
	//probabilistic selection strategy in clause selection using exponential function like in PrboSAT
	for(k=0; k<clause_lit_count[c]; ++k) { 
		v=clause_c[k].var_num;
		probs[k] =probsBreak[breaks[v]];
		sumProb += probs[k];
	}
	randPosition = (double) (rand()) / (RAND_MAX + 1.0) * sumProb;
	for (k = k - 1; k != 0; k--) {
		sumProb -= probs[k];
		if (sumProb <= randPosition)
			break;
	}
	best_var = clause_c[k].var_num;
	
	if((least_unsatClauses<30)&&(randPosition_p<0.08)) {
		if(	best_atom[best_var]==cur_soln[best_var]) 
			for(k=0; k<clause_lit_count[c]; ++k) {
				v=clause_c[k].var_num;
				if(score[v]>score[best_var]) best_var = v;
				else if(score[v]==score[best_var]) {//2-level tie-breaking strategy in variable selection using the Lva function
					tempBest_var=(double)vSelect[best_var]/(double)(step/num_vars+1)+gama*(double)(step+1-time_stamp[best_var])/(step+1);
					tempV=(double)vSelect[v]/(double)(step/num_vars+1)+gama*(double)(step+1-time_stamp[v])/(step+1);
					if(tempV>tempBest_var)	best_var = v;
				}
			}
	}

	if(bestVar!=best_var) 
		return best_var;
	else {
		count_breaktingTie++;
		for(k=0; k<clause_lit_count[c]; ++k) {
			v=clause_c[k].var_num;
			if(score[v]>score[best_var]) best_var = v;//1-level tie-breaking picking a variable in VarBest
			else if(score[v]==score[best_var]) {//2-level tie-breaking strategy in VarBest using the Lva function
				tempBest_var=(double)vSelect[best_var]/(double)(step/num_vars+1)+gama*(double)(step+1-time_stamp[best_var])/(step+1);
				tempV=(double)vSelect[v]/(double)(step/num_vars+1)+gama*(double)(step+1-time_stamp[v])/(step+1);
				if(tempV>tempBest_var)	best_var = v;

			}
		}
		return best_var;
	}


}


//set functions in the algorithm
void settings() {
	set_clause_weighting();
//	set_FRW();
}

void local_search(int max_flips) {
	int i,flipvar;

	for (step = 0; step<max_flips; step++) { 
		//find a solution
		if(unsat_stack_fill_pointer==0) return;
		flipvar = pick_var();
		vSelect[flipvar]++;//update vNTS
		flip(flipvar);

		time_stamp[flipvar] = step;
		if((least_unsatClauses>unsat_stack_fill_pointer)&&(unsat_stack_fill_pointer<30)) { 
			least_unsatClauses=unsat_stack_fill_pointer;
			for(i=1; i<=num_vars; i++)
				best_atom[i]=cur_soln[i];
		}
	}
}


int main(int argc, char* argv[]) {
//FILE *fp;
//fp=fopen("data.txt","w+");
//	if(fp==NULL)
//
//	{
//		printf("File cannot open! " );
//
//		exit(0);
//	}


	int     seed,i;
	int		satisfy_flag=0;
	struct 	tms start, stop;
	cout<<"c This is CCAnr [Version: 2013.4.18] [Author: Shaowei Cai]."<<endl;

	times(&start);

	if (build_instance(argv[1])==0) {
		cout<<"Invalid filename: "<< argv[1]<<endl;
		return -1;
	}
	set_FRW();
	initLookUpTable(); //Initialize the look up table
	sscanf(argv[2],"%d",&seed);
	p_first=atof(argv[3]);
	p_second=atof(argv[4]);
	Beta_first=atoi(argv[5]);
	Beta_second=atoi(argv[6]);
	gama=atoi(argv[7]);
	srand(seed);

	if(unitclause_queue_end_pointer>0) {
		preprocess();
	}

	build_neighbor_relation();

	cout<<"c Instance: Number of variables = "<<num_vars<<endl;
	cout<<"c Instance: Number of clauses = "<<num_clauses<<endl;
	cout<<"c Instance: Ratio = "<<ratio<<endl;
	cout<<"c Instance: Formula length = "<<formula_len<<endl;
	cout<<"c Instance: Avg (Min,Max) clause length = "<<avg_clause_len<<" ("<<min_clause_len<<","<<max_clause_len<<")"<<endl;
	cout<<"c Algorithmic: Random seed = "<<seed<<endl;
	cout<<"c Algorithmic: Beta_first = "<<Beta_first<<endl;
	cout<<"c Algorithmic: Beta_second = "<<Beta_second<<endl;
	cout<<"c Algorithmic: p_first = "<<p_first<<endl;
	cout<<"c Algorithmic: p_second = "<<p_second<<endl;
	for (tries = 0; tries <=max_tries; tries++) { 

		settings();

		init();
		local_search(max_flips);
		
		if (unsat_stack_fill_pointer==0) {
			if(verify_sol()==1) {
				satisfy_flag = 1;
				break;
			} else cout<<"c Sorry, something is wrong."<<endl; 
		}

	}

	times(&stop);
	double comp_time = double(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);

	if(satisfy_flag==1) {

		cout<<"s SATISFIABLE"<<endl;
		print_solution();
	} else  cout<<"s UNKNOWN"<<endl;

	cout<<"c solveSteps = "<<i<<" tries + "<<step<<" steps (each try has " << max_flips << " steps)."<<endl;
	cout<<"c solveTime = "<<comp_time<<endl;
    cout<<"c solveSteps = "<<tries<<" tries + "<<step<<" steps (each try has "<<max_flips<<" steps)."<<endl;
    cout<<"c solveTime = "<<comp_time<<endl;

	free_memory();

	return 0;
}
