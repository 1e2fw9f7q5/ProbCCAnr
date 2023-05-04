/************************************===  ProbCCAnr ===***************************************          
 **  ProbCCAnr is an algorithm developed based on CCAnr for the Boolean Satisfiability (SAT) problem,
 ** which is especially designed for non-random instances.
 **                                        
 *****************************************************************************************/



#ifndef _CCA_H_
#define _CCA_H_

#include "basis.h"

#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item



inline void unsat(int clause)
{
	index_in_unsat_stack[clause] = unsat_stack_fill_pointer;
	push(clause,unsat_stack);
	
	//update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v;
	for(lit* p=clause_lit[clause]; (v=p->var_num)!=0; p++)
	{	
		unsat_app_count[v]++;
		if(unsat_app_count[v]==1)
		{
			index_in_unsatvar_stack[v] = unsatvar_stack_fill_pointer;
			push(v,unsatvar_stack);	 
		}
	}
}


inline void sat(int clause)
{
	int index,last_unsat_clause;

	//since the clause is satisfied, its position can be reused to store the last_unsat_clause
	last_unsat_clause = pop(unsat_stack);
	index = index_in_unsat_stack[clause];
	unsat_stack[index] = last_unsat_clause;
	index_in_unsat_stack[last_unsat_clause] = index;
	
	//update appreance count of each var in unsat clause and update stack of vars in unsat clauses
	int v,last_unsat_var;
	for(lit* p=clause_lit[clause]; (v=p->var_num)!=0; p++)
	{	
		unsat_app_count[v]--;
		if(unsat_app_count[v]==0)
		{
			last_unsat_var = pop(unsatvar_stack);
			index = index_in_unsatvar_stack[v];
			unsatvar_stack[index] = last_unsat_var;
			index_in_unsatvar_stack[last_unsat_var] = index;
		}
	}
}

//initiation of the algorithm
void init()
{
	int 		v,c;
	int			i,j;
	int			clause;
	count_FRW=0;//new
	least_unsatClauses=num_clauses;
	//Initialize edge weights
	for (c = 0; c<num_clauses; c++)
		clause_weight[c] = 1;
// Initialize candidate clause
	count_candidate_falseClause_first=0;
	count_candidate_falseClause_second=0;
	for (c = 0; c<num_clauses; c++){
		whereCandidate_first[i]=0;
		whereCandidate_second[i]=0;
		candidate_falseClause_first_stack[i]=0;
		candidate_falseClause_second_stack[i]=0;
		count_selectCaluse[i]=0;
		isCandidate_first[i]=0;
		isCandidate_second[i]=0;
	}

	//init unsat_stack
	unsat_stack_fill_pointer = 0;
	unsatvar_stack_fill_pointer = 0;

	//init solution
	for (v = 1; v <= num_vars; v++) {
        vSelect[v]=0;//new
        if(fix[v]==0){
            if(rand()%2==1) cur_soln[v] = 1;
            else cur_soln[v] = 0;
			time_stamp[v] = 0;
			conf_change[v] = 1;
			unsat_app_count[v] = 0;
		
			//pscore[v] = 0;
		}
       best_atom[v]=cur_soln[v];
       breaks[v]=0;
	}

	/* figure out sat_count, and init unsat_stack */
	for (c=0; c<num_clauses; ++c) 
	{
		if(clause_delete[c]==1) continue;
		
		sat_count[c] = 0;
		
		for(j=0; j<clause_lit_count[c]; ++j)
		{
			if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				sat_count[c]++;
				sat_var[c] = clause_lit[c][j].var_num;	
			}
		}

		if (sat_count[c] == 0) 
			unsat(c);
		else if(sat_count[c] == 1){
			breaks[sat_var[c]]++;
		} 
	}

	/*figure out var score*/
	int lit_count;
	for (v=1; v<=num_vars; v++) 
	{
		if(fix[v]==1) 
		{
			score[v] = -100000;
			continue;
		}
		
		score[v] = 0;

		lit_count = var_lit_count[v];
		
		for(i=0; i<lit_count; ++i)
		{
			c = var_lit[v][i].clause_num;
			if (sat_count[c]==0) score[v]++;
			else if (sat_count[c]==1 && var_lit[v][i].sense==cur_soln[v]) score[v]--;
		}
	}
	
	/*
	int flag;
	//compute pscore and record sat_var and sat_var2 for 2sat clauses
	for (c=0; c<num_clauses; ++c) 
	{
		if(clause_delete[c]==1) continue;
		
		if (sat_count[c]==1)
		{
			for(j=0;j<clause_lit_count[c];++j)
			{
				v=clause_lit[c][j].var_num;
				if(v!=sat_var[c])pscore[v]++;
			}
		}
		else if(sat_count[c]==2)
		{
			flag=0;
			for(j=0;j<clause_lit_count[c];++j)
			{
				v=clause_lit[c][j].var_num;
				if(clause_lit[c][j].sense == cur_soln[v])
				{
					pscore[v]--;
					if(flag==0){sat_var[c] = v; flag=1;}
					else	{sat_var2[c] = v; break;}
				}
			}
		
		}
	}
	*/
	
		
	//init goodvars stack
	goodvar_stack_fill_pointer = 0;
	for (v=1; v<=num_vars; v++) 
	{
		if(fix[v]==1)  continue;
		if(score[v]>0)// && conf_change[v]==1)
		{
			already_in_goodvar_stack[v] = 1;
			push(v,goodvar_stack);
			
		}
		else already_in_goodvar_stack[v] = 0;
	}
	
	//setting for the virtual var 0
	time_stamp[0]=0;
	//pscore[0]=0;
}


void flip(int flipvar)
{
	cur_soln[flipvar] = 1 - cur_soln[flipvar];

	int i,j;
	int v,c;

	lit* clause_c;
	
	int org_flipvar_score = score[flipvar];
	
	//update related clauses and neighbor vars
	for(lit *q = var_lit[flipvar]; (c=q->clause_num)>=0; q++)
	{
		clause_c = clause_lit[c];
		if(cur_soln[flipvar] == q->sense)
		{
			++sat_count[c];
			
			if (sat_count[c] == 2) //sat_count from 1 to 2
				{
					score[sat_var[c]] += clause_weight[c];
					breaks[sat_var[c]]--;
				}
			else if (sat_count[c] == 1) // sat_count from 0 to 1
			{
				sat_var[c] = flipvar;//record the only true lit's var
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) score[v] -= clause_weight[c];
                
				sat(c);
				breaks[flipvar]++;
					//update cNTS
			   	    if(isCandidate_first[c]==1){
				       isCandidate_first[c]=0;
				       count_candidate_falseClause_first--;
				       candidate_falseClause_first_stack[whereCandidate_first[c]]=candidate_falseClause_first_stack[count_candidate_falseClause_first];
				       whereCandidate_first[candidate_falseClause_first_stack[count_candidate_falseClause_first]]=whereCandidate_first[c];
				
				   }
			      	else{
				        if(isCandidate_second[c]==1){
				        isCandidate_second[c]=0;
				        count_candidate_falseClause_second--;
				        candidate_falseClause_second_stack[whereCandidate_second[c]]=candidate_falseClause_second_stack[count_candidate_falseClause_second];
				        whereCandidate_second[candidate_falseClause_second_stack[count_candidate_falseClause_second]]=whereCandidate_second[c];	
				     }
			      }

			}
		}
		else // cur_soln[flipvar] != cur_lit.sense
		{
			--sat_count[c];
			if (sat_count[c] == 1) //sat_count from 2 to 1
			{
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) 
				{
					if(p->sense == cur_soln[v] )
					{
						score[v] -= clause_weight[c];
						sat_var[c] = v;
						breaks[v]++;
						break;
					}
				}
			}
			else if (sat_count[c] == 0) //sat_count from 1 to 0
			{
				for(lit* p=clause_c; (v=p->var_num)!=0; p++) score[v] += clause_weight[c];
				unsat(c);
				breaks[flipvar]--;
				//update cNTS
				if((count_selectCaluse[c]>Beta_first)&&(isCandidate_first[c]==0)){//new
				isCandidate_first[c]=1;
				candidate_falseClause_first_stack[count_candidate_falseClause_first]=c;
				whereCandidate_first[c]=count_candidate_falseClause_first;
				count_candidate_falseClause_first++;
			   }
			    else if((count_selectCaluse[c]>Beta_second)&&(count_selectCaluse[c]<Beta_first)&&(isCandidate_second[c]==0)){
				isCandidate_second[c]=1;
				candidate_falseClause_second_stack[count_candidate_falseClause_second]=c;
				whereCandidate_second[c]=count_candidate_falseClause_second;
				count_candidate_falseClause_second++;
		      	}
		   	}
			
		}
	}

	score[flipvar] = -org_flipvar_score;
	
	/*update CCD */
	int index;
	
	conf_change[flipvar] = 0;
	//remove the vars no longer goodvar in goodvar stack 
	for(index=goodvar_stack_fill_pointer-1; index>=0; index--)
	{
		v = goodvar_stack[index];
		if(score[v]<=0)
		{
			goodvar_stack[index] = pop(goodvar_stack);
			already_in_goodvar_stack[v] = 0;
		}	
	}

	//update all flipvar's neighbor's conf_change to be 1, add goodvar
	int* p;
	for(p=var_neighbor[flipvar]; (v=*p)!=0; p++) 
	{
		conf_change[v] = 1;
		
		if(score[v]>0 && already_in_goodvar_stack[v] ==0)
		{                                                 
			push(v,goodvar_stack);
			already_in_goodvar_stack[v] = 1;
		}
	}
}

#endif
