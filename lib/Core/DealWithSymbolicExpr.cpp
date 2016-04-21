/*
 * SymbolicListener.h
 *
 *  Created on: 2015年7月21日
 *      Author: zhy
 */

#ifndef LIB_CORE_DEALWITHSYMBOLIC_C_
#define LIB_CORE_DEALWITHSYMBOLIC_C_

#define DEBUG 0

#define OP1 0
//1为失效，0为生效

#include "DealWithSymbolicExpr.h"
#include "llvm/IR/Instruction.h"
#include <sstream>
#include <ostream>
#include <set>
#include <vector>
#include <map>

namespace klee {

std::string DealWithSymbolicExpr::getVarName(ref<klee::Expr> value) {
//	std::cerr << "getVarName : " << value << "\n";
	std::stringstream varName;
	varName.str("");
	ReadExpr *revalue;
	if (value->getKind() == Expr::Concat) {
		ConcatExpr *ccvalue = cast<ConcatExpr>(value);
		revalue = cast<ReadExpr>(ccvalue->getKid(0));
	} else if (value->getKind() == Expr::Read) {
		revalue = cast<ReadExpr>(value);
	} else {
		return varName.str();
	}
	std::string globalVarFullName = revalue->updates.root->name;
	unsigned int i = 0;
	while ((globalVarFullName.at(i) != 'S') && (globalVarFullName.at(i) != 'L')) {
		varName << globalVarFullName.at(i);
		i++;
	}
	return varName.str();
}

std::string DealWithSymbolicExpr::getFullName(ref<klee::Expr> value) {

	ReadExpr *revalue;
	if (value->getKind() == Expr::Concat) {
		ConcatExpr *ccvalue = cast<ConcatExpr>(value);
		revalue = cast<ReadExpr>(ccvalue->getKid(0));
	} else if (value->getKind() == Expr::Read) {
		revalue = cast<ReadExpr>(value);
	} else {
		assert( 0 && "getFullName");
	}
	std::string globalVarFullName = revalue->updates.root->name;
	return globalVarFullName;
}

void DealWithSymbolicExpr::resolveSymbolicExpr(ref<klee::Expr> value,
		std::set<std::string>* relatedSymbolicExpr) {
	if (value->getKind() == Expr::Read) {
		std::string varName = getVarName(value);
		if (relatedSymbolicExpr->find(varName) == relatedSymbolicExpr->end()) {
			relatedSymbolicExpr->insert(varName);
		}
		return;
	} else {
		unsigned kidsNum = value->getNumKids();
		if (kidsNum == 2 && value->getKid(0) == value->getKid(1)) {
			resolveSymbolicExpr(value->getKid(0), relatedSymbolicExpr);
		} else {
			for (unsigned int i = 0; i < kidsNum; i++) {
				resolveSymbolicExpr(value->getKid(i), relatedSymbolicExpr);
			}
		}
	}
}

void DealWithSymbolicExpr::addExprToSet(std::set<std::string>* Expr,
		std::set<std::string>* relatedSymbolicExpr) {

	for (std::set<std::string>::iterator it =
			Expr->begin(), ie = Expr->end(); it != ie; ++it) {
		std::string varName =*it;
		if (relatedSymbolicExpr->find(varName) == relatedSymbolicExpr->end()) {
			relatedSymbolicExpr->insert(varName);
		}
	}
}

bool DealWithSymbolicExpr::isRelated(std::string varName) {
	if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
		return true;
	} else {
		return false;
	}
}

void DealWithSymbolicExpr::fillterTrace(Trace* trace, std::set<std::string> RelatedSymbolicExpr) {
	std::string varName;

	//PathCondition
	std::vector<ref<klee::Expr> > &kQueryExpr = trace->kQueryExpr;
	std::vector<ref<klee::Expr> > &usefulkQueryExpr = trace->usefulkQueryExpr;
	usefulkQueryExpr.clear();
	for (std::vector<ref<Expr> >::iterator it = kQueryExpr.begin(), ie =
			kQueryExpr.end(); it != ie; ++it) {
		varName = getVarName(it->get()->getKid(1));
		if (RelatedSymbolicExpr.find(varName) != RelatedSymbolicExpr.end() || OP1) {
			usefulkQueryExpr.push_back(*it);
		}
	}

	//readSet
	std::map<std::string, std::vector<Event *> > &usefulReadSet = trace->usefulReadSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			readSet.begin(), nie = readSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (RelatedSymbolicExpr.find(varName) != RelatedSymbolicExpr.end() || OP1) {
			usefulReadSet.insert(*nit);
		}
	}

	//writeSet
	std::map<std::string, std::vector<Event *> > &usefulWriteSet = trace->usefulWriteSet;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			writeSet.begin(), nie = writeSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (RelatedSymbolicExpr.find(varName) != RelatedSymbolicExpr.end() || OP1) {
			usefulWriteSet.insert(*nit);
		}
	}

	//global_variable_initializer
	std::map<std::string, llvm::Constant*> &useful_global_variable_initializer = trace->useful_global_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	useful_global_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			global_variable_initializer.begin(), nie = global_variable_initializer.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (RelatedSymbolicExpr.find(varName) != RelatedSymbolicExpr.end() || OP1) {
			useful_global_variable_initializer.insert(*nit);
		}
	}

	//event
	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
			currentEvent != endEvent; currentEvent++) {
		if ((*currentEvent)->isGlobal == true) {
			if ((*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Load
					|| (*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Store) {
				if (RelatedSymbolicExpr.find((*currentEvent)->varName) == RelatedSymbolicExpr.end() && !OP1) {
					(*currentEvent)->usefulGlobal = false;
				} else {
					(*currentEvent)->usefulGlobal = true;
				}
			}
		}
	}
}

void DealWithSymbolicExpr::filterUseless(Trace* trace) {

	std::string varName;
	std::vector<std::string> remainingExprVarName;
	std::vector<ref<klee::Expr> > remainingExpr;
	allRelatedSymbolicExpr.clear();
	remainingExprVarName.clear();
	remainingExpr.clear();
	std::vector<ref<klee::Expr> > &storeSymbolicExpr = trace->storeSymbolicExpr;
	for (std::vector<ref<Expr> >::iterator it = storeSymbolicExpr.begin(), ie =
			storeSymbolicExpr.end(); it != ie; ++it) {
		varName = getVarName(it->get()->getKid(1));
		remainingExprVarName.push_back(varName);
		remainingExpr.push_back(it->get());
	}
#if DEBUG
		std::cerr << "\n storeSymbolicExpr " << std::endl;
		for (std::vector<ref<Expr> >::iterator it = storeSymbolicExpr.begin(),
				ie = storeSymbolicExpr.end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
#endif


	//br
	std::vector<ref<klee::Expr> > &brSymbolicExpr = trace->brSymbolicExpr;
	std::vector<std::set<std::string>*> &brRelatedSymbolicExpr = trace->brRelatedSymbolicExpr;
	for (std::vector<ref<Expr> >::iterator it = brSymbolicExpr.begin(), ie =
			brSymbolicExpr.end(); it != ie; ++it) {
		std::set<std::string>* tempSymbolicExpr = new std::set<std::string>();
		resolveSymbolicExpr(it->get(), tempSymbolicExpr);
		brRelatedSymbolicExpr.push_back(tempSymbolicExpr);
		addExprToSet(tempSymbolicExpr, &allRelatedSymbolicExpr);
#if DEBUG
		std::cerr << "\n" << *it << "\n brRelatedSymbolicExpr " << std::endl;
		for (std::set<std::string>::iterator it = tempSymbolicExpr->begin(),
				ie = tempSymbolicExpr->end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
#endif
	}

	//assert
	std::vector<ref<klee::Expr> > &assertSymbolicExpr = trace->assertSymbolicExpr;
	std::vector<std::set<std::string>*> &assertRelatedSymbolicExpr = trace->assertRelatedSymbolicExpr;
	for (std::vector<ref<Expr> >::iterator it = assertSymbolicExpr.begin(), ie =
			assertSymbolicExpr.end(); it != ie; ++it) {
		std::set<std::string>* tempSymbolicExpr = new std::set<std::string>();
		resolveSymbolicExpr(it->get(), tempSymbolicExpr);
		assertRelatedSymbolicExpr.push_back(tempSymbolicExpr);
		addExprToSet(tempSymbolicExpr, &allRelatedSymbolicExpr);
#if DEBUG
		std::cerr << "\n" << *it << "\n assertRelatedSymbolicExpr " << std::endl;
		for (std::set<std::string>::iterator it = tempSymbolicExpr->begin(),
				ie = tempSymbolicExpr->end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
#endif
	}

#if DEBUG
	std::cerr << "\n allRelatedSymbolicExpr " << std::endl;
	for (std::set<std::string>::iterator it = allRelatedSymbolicExpr.begin(),
			ie = allRelatedSymbolicExpr.end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif

	std::vector<ref<klee::Expr> > &kQueryExpr = trace->kQueryExpr;
	std::map<std::string, std::set<std::string>* > &varRelatedSymbolicExpr = trace->varRelatedSymbolicExpr;
	for (std::set<std::string>::iterator nit = allRelatedSymbolicExpr.begin();
			nit != allRelatedSymbolicExpr.end(); ++nit) {
		varName = *nit;
		std::vector<ref<Expr> >::iterator itt = remainingExpr.begin();
		for (std::vector<std::string>::iterator it =
				remainingExprVarName.begin(), ie = remainingExprVarName.end();
				it != ie;) {
			if (varName == *it) {
				remainingExprVarName.erase(it);
				--ie;
				kQueryExpr.push_back(*itt);

				std::set<std::string>* tempSymbolicExpr = new std::set<std::string>();
				resolveSymbolicExpr(itt->get(), tempSymbolicExpr);
				if (varRelatedSymbolicExpr.find(varName) != varRelatedSymbolicExpr.end()) {
					addExprToSet(tempSymbolicExpr, varRelatedSymbolicExpr[varName]);
				} else {
					varRelatedSymbolicExpr[varName] = tempSymbolicExpr;
				}
				addExprToSet(tempSymbolicExpr, &allRelatedSymbolicExpr);
#if DEBUG
				std::cerr << "\n" << varName << "\n varRelatedSymbolicExpr " << std::endl;
				std::cerr << *itt << "\n";
				for (std::set<std::string>::iterator it = tempSymbolicExpr->begin(),
						ie = tempSymbolicExpr->end(); it != ie; ++it) {
					std::cerr << *it << std::endl;
				}
#endif
				remainingExpr.erase(itt);
			} else {
				++it;
				++itt;
			}
		}
	}

#if DEBUG
	std::cerr << "\n" << varName << "\n varRelatedSymbolicExpr " << std::endl;
	for (std::map<std::string, std::set<std::string>* >::iterator nit = varRelatedSymbolicExpr.begin();
			nit != varRelatedSymbolicExpr.end(); ++nit) {
		std::cerr << "name : " << (*nit).first << "\n";
		for (std::set<std::string>::iterator it = (*nit).second->begin(),
				ie = (*nit).second->end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
	}
#endif

	std::map<std::string, long> &varThread = trace->varThread;

	std::map<std::string, std::vector<Event *> > usefulReadSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			readSet.begin(), nie = readSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end() || OP1) {
			usefulReadSet.insert(*nit);
			if (varThread.find(varName) == varThread.end()) {
				varThread[varName] = (*(nit->second.begin()))->threadId;
			}
			long id = varThread[varName];
			if (id != 0){
				for (std::vector<Event *>::iterator it =
						nit->second.begin(), ie = nit->second.end(); it != ie; ++it) {
					if( id != (*it)->threadId){
						varThread[varName] = 0;
						break;
					}
				}
			}

		}

	}
	readSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulReadSet.begin(), nie = usefulReadSet.end(); nit != nie;
			++nit) {
		readSet.insert(*nit);
	}

	std::map<std::string, std::vector<Event *> > usefulWriteSet;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			writeSet.begin(), nie = writeSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end() || OP1) {
			usefulWriteSet.insert(*nit);
			if (varThread.find(varName) == varThread.end()) {
				varThread[varName] = (*(nit->second.begin()))->threadId;
			}
			long id = varThread[varName];
			if (id != 0){
				for (std::vector<Event *>::iterator it =
						nit->second.begin(), ie = nit->second.end(); it != ie; ++it) {
					if( id != (*it)->threadId){
						varThread[varName] = 0;
						break;
					}
				}
			}
		}
	}
	writeSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulWriteSet.begin(), nie = usefulWriteSet.end(); nit != nie;
			++nit) {
		writeSet.insert(*nit);
	}

	for (std::map<std::string, long> ::iterator nit = varThread.begin(),
			nie = varThread.end(); nit != nie; ++nit) {
		if (usefulWriteSet.find((*nit).first) == usefulWriteSet.end()) {
			(*nit).second = -1;
		}
	}

#if DEBUG
	std::cerr << "varThread\n";
	for (std::map<std::string, long>::iterator nit =
			varThread.begin(), nie = varThread.end(); nit != nie; ++nit) {
		std::cerr << nit->first << " : " << nit->second << "\n";
	}
#endif

	std::map<std::string, llvm::Constant*> usefulGlobal_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	usefulGlobal_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			global_variable_initializer.begin(), nie = global_variable_initializer.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end() || OP1) {
			usefulGlobal_variable_initializer.insert(*nit);
		}
	}
	global_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			usefulGlobal_variable_initializer.begin(), nie = usefulGlobal_variable_initializer.end(); nit != nie;
			++nit) {
		global_variable_initializer.insert(*nit);
	}

//	std::vector<std::vector<Event*>*> eventList = trace->eventList;
	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
			currentEvent != endEvent; currentEvent++) {
		if ((*currentEvent)->isGlobal == true) {
			if ((*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Load
					|| (*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Store) {
				if (allRelatedSymbolicExpr.find((*currentEvent)->varName) == allRelatedSymbolicExpr.end() && !OP1) {
					(*currentEvent)->isGlobal = false;
					(*currentEvent)->usefulGlobal = false;
				} else {
					(*currentEvent)->usefulGlobal = true;
				}
			} else {
				(*currentEvent)->usefulGlobal = true;
			}
		}
	}

	std::vector<ref<klee::Expr> > usefulRwSymbolicExpr;
	std::vector<ref<klee::Expr> > &rwSymbolicExpr = trace->rwSymbolicExpr;
	usefulGlobal_variable_initializer.clear();
	for (std::vector<ref<klee::Expr> >::iterator nit =
			rwSymbolicExpr.begin(), nie = rwSymbolicExpr.end(); nit != nie; ++nit) {
		varName = getVarName((*nit)->getKid(1));
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end() || OP1) {
			usefulRwSymbolicExpr.push_back(*nit);
		}
	}
	rwSymbolicExpr.clear();
	for (std::vector<ref<klee::Expr> >::iterator nit =
			usefulRwSymbolicExpr.begin(), nie = usefulRwSymbolicExpr.end(); nit != nie;
			++nit) {
		rwSymbolicExpr.push_back(*nit);
	}

	fillterTrace(trace, allRelatedSymbolicExpr);

}

bool DealWithSymbolicExpr::filterUselessWithSet(Trace* trace, std::set<std::string>* relatedSymbolicExpr){
	bool branch = false;
	std::set<std::string> &RelatedSymbolicExpr = trace->RelatedSymbolicExpr;
	RelatedSymbolicExpr.clear();
#if DEBUG
	std::cerr << "\n relatedSymbolicExpr " << std::endl;
	for (std::set<std::string>::iterator it = relatedSymbolicExpr->begin(),
			ie = relatedSymbolicExpr->end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif
	addExprToSet(relatedSymbolicExpr, &RelatedSymbolicExpr);

	std::string varName;
	std::map<std::string, std::set<std::string>* > &varRelatedSymbolicExpr = trace->varRelatedSymbolicExpr;
	for (std::set<std::string>::iterator nit = RelatedSymbolicExpr.begin();
			nit != RelatedSymbolicExpr.end(); ++nit) {
		varName = *nit;
#if DEBUG
		std::cerr << "\n varName : " <<  varName << std::endl;
#endif
		if (varRelatedSymbolicExpr.find(varName) != varRelatedSymbolicExpr.end()) {
			addExprToSet(varRelatedSymbolicExpr[varName], &RelatedSymbolicExpr);
		}
#if DEBUG
		std::cerr << "\n addExprToSet(relatedSymbolicExpr, &RelatedSymbolicExpr); " << std::endl;
#endif
	}
#if DEBUG
	std::cerr << "\n RelatedSymbolicExpr " << std::endl;
	for (std::set<std::string>::iterator it = RelatedSymbolicExpr.begin(),
			ie = RelatedSymbolicExpr.end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif

	std::map<std::string, long> &varThread = trace->varThread;
	for (std::set<std::string>::iterator it = RelatedSymbolicExpr.begin(),
			ie = RelatedSymbolicExpr.end(); it != ie; ++it) {
		if(varThread[*it] == 0){
			branch = true;
			break;
		}
	}
	if (branch) {
//		fillterTrace(trace, RelatedSymbolicExpr);
		return true;
	} else {
		return false;
	}
}

}

#endif /* LIB_CORE_DEALWITHSYMBOLIC_C_ */
