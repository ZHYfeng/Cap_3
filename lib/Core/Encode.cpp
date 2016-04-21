/*
 * Encode.cpp
 *
 *  Created on: Jun 10, 2014
 *      Author: xdzhang
 */

#include "klee/Internal/Module/KInstruction.h"
#include "klee/Internal/Module/InstructionInfoTable.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/TypeBuilder.h"
#else
#include "llvm/Attributes.h"
#include "llvm/BasicBlock.h"
#include "llvm/Constants.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#if LLVM_VERSION_CODE <= LLVM_VERSION(3, 1)
#include "llvm/Target/TargetData.h"
#else
#include "llvm/DataLayout.h"
#include "llvm/TypeBuilder.h"
#endif
#endif
#include "llvm/Support/FileSystem.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <vector>
#include <sstream>
#include <assert.h>
#include <sys/time.h>
#include <fstream>
#include <pthread.h>
#include <z3.h>
#include <z3_api.h>
#include <iostream>
#include <iomanip>

#include "Prefix.h"
#include "Encode.h"
#include "Common.h"
#include "KQuery2Z3.h"

#define FORMULA_DEBUG 0
#define BRANCH_INFO 1
#define BUFFERSIZE 300
#define BIT_WIDTH 64
#define POINT_BIT_WIDTH 64
#define INT_ARITHMETIC 0


using namespace llvm;
using namespace std;
using namespace z3;
namespace klee {

struct Pair {
	int order; //the order of a event
	Event *event;
};

void Encode::buildAllFormula() {
	buildInitValueFormula(z3_solver);
	buildPathCondition(z3_solver);
	buildMemoryModelFormula();
	buildPartialOrderFormula();
	buildReadWriteFormula(z3_solver);
	buildSynchronizeFormula();
	//debug: test satisfy of the model
//	check_result result = z3_solver.check();
//	if (result != z3::sat) {
//		assert(0 && "failed");
//	}
//	else assert(0 && "success");
	//
}

//true :: assert can't be violated. false :: assert can be violated.
bool Encode::verify() {
#if !FORMULA_DEBUG
	showInitTrace();
#endif
	cerr << "\nVerifying this trace......\n";
#if FORMULA_DEBUG
	stringstream ss;
	ss << "./output_info/" << "Trace" << trace->Id << ".z3expr" ;
	std::ofstream out_file(ss.str().c_str(),std::ios_base::out);
	out_file <<"\n"<<z3_solver<<"\n";
	out_file <<"\nifFormula\n";
	for (unsigned i = 0; i < ifFormula.size(); i++) {
		out_file << "Trace" << trace->Id << "#"
				<< ifFormula[i].first->inst->info->file << "#"
				<< ifFormula[i].first->inst->info->line << "#"
				<< ifFormula[i].first->eventName << "#"
				<< ifFormula[i].first->condition << "-"
				<< !(ifFormula[i].first->condition) << "\n";
		out_file << ifFormula[i].second << "\n";
	}
	out_file <<"\nassertFormula\n";
	for (unsigned i = 0; i < assertFormula.size(); i++) {
		out_file << "Trace" << trace->Id << "#"
				<< assertFormula[i].first->inst->info->file << "#"
				<< assertFormula[i].first->inst->info->line << "#"
				<< assertFormula[i].first->eventName << "#"
				<< assertFormula[i].first->condition << "-"
				<< !(assertFormula[i].first->condition) << "\n";
		out_file << assertFormula[i].second << "\n";
	}
	out_file.close();
#endif
	z3_solver.push();	//backtrack 1
	cerr << "\nThe number of assert: " << assertFormula.size() << "\n";
	for (unsigned i = 0; i < assertFormula.size(); i++) {
#if BRANCH_INFO
		stringstream ss;
		ss << "Trace" << trace->Id << "#"
//				<< assertFormula[i].first->inst->info->file << "#"
				<< assertFormula[i].first->inst->info->line << "#"
				<< assertFormula[i].first->eventName << "#"
				<< assertFormula[i].first->condition << "-"
				<< !(assertFormula[i].first->condition) << "assert_bug";
		cerr << "Verifying assert " << i+1 << " @" << ss.str() << ": ";
#endif
		z3_solver.push();	//backtrack point 2
//		buildAllFormula();

			Event* curr = assertFormula[i].first;

		z3_solver.add(!assertFormula[i].second);
		for (unsigned j = 0; j < assertFormula.size(); j++) {
			if (j == i) {
				continue;
			}
			Event* temp = assertFormula[j].first;
			expr currIf = z3_ctx.int_const(curr->eventName.c_str());
			expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
			expr constraint = z3_ctx.bool_val(1);
			if (curr->threadId == temp->threadId) {
				if (curr->eventId > temp->eventId)
					constraint = assertFormula[j].second;
			} else
				constraint = implies(tempIf < currIf, assertFormula[j].second);
			z3_solver.add(constraint);
		}
		for (unsigned j = 0; j < ifFormula.size(); j++) {
			Event* temp = ifFormula[j].first;
			expr currIf = z3_ctx.int_const(curr->eventName.c_str());
			expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
			expr constraint = z3_ctx.bool_val(1);
			if (curr->threadId == temp->threadId) {
				if (curr->eventId > temp->eventId)
					constraint = ifFormula[j].second;
			} else
				constraint = implies(tempIf < currIf, ifFormula[j].second);
			z3_solver.add(constraint);
		}
		formulaNum = formulaNum + ifFormula.size() - 1;
		//statics
		cerr <<"\n"<<z3_solver<<"\n";
		check_result result = z3_solver.check();

		solvingTimes++;
		stringstream output;
		if (result == z3::sat) {
			//should compute the prefix violating assert
			cerr << "Yes!\n";
			runtimeData->clearAllPrefix();

			//former :: replay the bug trace and erminate klee. later:: terminate klee directly
			if (true) {
				vector<Event*> vecEvent;
				computePrefix(vecEvent, assertFormula[i].first);
				Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint,
						ss.str());
				output << "./output_info/" << prefix->getName() << ".z3expr";
				runtimeData->addScheduleSet(prefix);
//			} else {
				cerr << "Assert Failure at "
						<< assertFormula[i].first->inst->info->file << ": "
						<< assertFormula[i].first->inst->info->line << "\n";
#if FORMULA_DEBUG
				showPrefixInfo(prefix, assertFormula[i].first);
#endif

			}
#if FORMULA_DEBUG
		std::ofstream out_file(output.str().c_str(),std::ios_base::out|std::ios_base::app);
		out_file << "!assertFormula[i].second : " << !assertFormula[i].second << "\n";
		out_file <<"\n"<<z3_solver<<"\n";
		model m = z3_solver.get_model();
		out_file <<"\nz3_solver.get_model()\n";
		out_file <<"\n"<<m<<"\n";
		out_file.close();
#endif
//		logStatisticInfo();
			return false;
		} else if (result == z3::unknown) {
			cerr << "assert" << i << ": unknown!\n";
		} else if (result == z3::unsat) {
#if BRANCH_INFO
			cerr << "No!\n";
#endif
		}
		z3_solver.pop();	//backtrack point 2
	}
	z3_solver.pop();	//backtrack 1
	cerr << "\nVerifying is over!\n";
	return true;
}

void Encode::check_if() {
	unsigned sum = 0, num = 0;
	unsigned size = ifFormula.size();
	cerr << "Sum of branches: " << size << "\n";
	for (unsigned i = 0; i < ifFormula.size(); i++) {
		num++;
#if BRANCH_INFO
//		cerr << ifFormula[i].second << "\n";
		stringstream ss;
		ss << "Trace" << trace->Id << "#"
//				<< ifFormula[i].first->inst->info->file << "#"
				<< ifFormula[i].first->inst->info->line << "#"
				<< ifFormula[i].first->eventName << "#"
				<< ifFormula[i].first->condition << "-"
				<< !(ifFormula[i].first->condition);
		cerr << "Verifying branch " << num << " @" << ss.str() << ": ";
#endif

		//create a backstracking point
		z3_solver.push();

		struct timeval start, finish;
		gettimeofday(&start, NULL);

		bool branch = filter.filterUselessWithSet(trace, trace->brRelatedSymbolicExpr[i]);
//		bool branch = true;
//		branch = true;
		gettimeofday(&finish, NULL);
		double cost = (double) (finish.tv_sec * 1000000UL + finish.tv_usec
				- start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
		cerr << "CCost : " << cost << "\n";

		if (!branch) {
			cerr << "NNo!\n";
//		} else {
//			cerr << "YYes!\n";
//			struct timeval start, finish;
//			gettimeofday(&start, NULL);
//
//			solver temp_solver(z3_ctx);
//			KQuery2Z3 * kq = new KQuery2Z3(z3_ctx);
//			z3::expr res = kq->getZ3Expr(trace->brSymbolicExpr[i]);
//			temp_solver.add(!res);
//			buildInitValueFormula(temp_solver);
//			buildPathCondition(temp_solver);
//			buildReadWriteFormula(temp_solver);
//
////			cerr << "!ifFormula[i].second : " << !ifFormula[i].second << "\n";
////			cerr << "\n"<<temp_solver<<"\n";
////			cerr << "end\n";
//
//			check_result result;
//			try {
//				//statics
//				result = temp_solver.check();
//			} catch (z3::exception & ex) {
//				std::cerr << "\nUnexpected error: " << ex << "\n";
//				continue;
//			}
//			if (result == z3::unsat) {
//				branch = 0;
//				cerr << "NNNo!\n";
//			} else {
//				cerr << "YYYes!\n";
//			}
//
//			gettimeofday(&finish, NULL);
//			double cost = (double) (finish.tv_sec * 1000000UL + finish.tv_usec
//					- start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
//			cerr << "CCCost : " << cost << "\n";
		}

		if(branch){
//			buildAllFormula();

			Event* curr = ifFormula[i].first;

			//添加读写的解
			std::set<std::string> &RelatedSymbolicExpr = trace->RelatedSymbolicExpr;
			std::vector<ref<klee::Expr> > &rwSymbolicExpr = trace->rwSymbolicExpr;
			std::string varName;
			unsigned int totalRwExpr = rwFormula.size();
			for (unsigned int j = 0; j < totalRwExpr; j++){
				varName = filter.getVarName(rwSymbolicExpr[j]->getKid(1));
				if (RelatedSymbolicExpr.find(varName) == RelatedSymbolicExpr.end()){
					Event* temp = rwFormula[j].first;
					expr currIf = z3_ctx.int_const(curr->eventName.c_str());
					expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
					expr constraint = z3_ctx.bool_val(1);
					if (curr->threadId == temp->threadId) {
						if (curr->eventId > temp->eventId)
							constraint = rwFormula[j].second;
					} else {
						constraint = implies(tempIf < currIf, rwFormula[j].second);
					}
					z3_solver.add(constraint);
//					z3_solver.add(rwFormula[j].second);
				}
			}

			z3_solver.add(!ifFormula[i].second);
			for (unsigned j = 0; j < ifFormula.size(); j++) {
				if (j == i) {
					continue;
				}
				Event* temp = ifFormula[j].first;
				expr currIf = z3_ctx.int_const(curr->eventName.c_str());
				expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
				expr constraint = z3_ctx.bool_val(1);
				if (curr->threadId == temp->threadId) {
					if (curr->eventId > temp->eventId)
						constraint = ifFormula[j].second;
				} else
					constraint = implies(tempIf < currIf, ifFormula[j].second);
				z3_solver.add(constraint);
			}
			//statics
			formulaNum = formulaNum + ifFormula.size() - 1;
			//solving
			check_result result;
			struct timeval start, finish;

			gettimeofday(&start, NULL);
			try {
				//statics
				result = z3_solver.check();
			} catch (z3::exception & ex) {
				std::cerr << "\nUnexpected error: " << ex << "\n";
				continue;
			}
			gettimeofday(&finish, NULL);
			double cost = (double) (finish.tv_sec * 1000000UL + finish.tv_usec
					- start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
			cerr << "Cost : " << cost << "\n";
			solvingTimes++;
			stringstream output;
			if (result == z3::sat) {
				vector<Event*> vecEvent;
				computePrefix(vecEvent, ifFormula[i].first);
				Prefix* prefix = new Prefix(vecEvent, trace->createThreadPoint,
						ss.str());
				output << "./output_info/" << prefix->getName() << ".z3expr";
				//printf prefix to DIR output_info
				runtimeData->addScheduleSet(prefix);
				runtimeData->satBranch++;
				runtimeData->satCost += cost;
#if FORMULA_DEBUG
				showPrefixInfo(prefix, ifFormula[i].first);
#endif
			} else {
				runtimeData->unSatBranch++;
				runtimeData->unSatCost += cost;
			}

#if BRANCH_INFO
			if (result == z3::sat) {
				sum++;
				cerr << "Yes!\n";
#if FORMULA_DEBUG
				std::ofstream out_file(output.str().c_str(),std::ios_base::out|std::ios_base::app);
				out_file << "!ifFormula[i].second : " << !ifFormula[i].second << "\n";
				out_file <<"\n"<<z3_solver<<"\n";
				model m = z3_solver.get_model();
				out_file <<"\nz3_solver.get_model()\n";
				out_file <<"\n"<<m<<"\n";
				out_file.close();
#endif
			} else if (result == z3::unsat) {
				cerr << "No!\n";
			} else
				cerr << "Warning!\n";
#endif
		} else {
			runtimeData->uunSatBranch++;
		}
		//backstracking
		z3_solver.pop();

	}

//	//print log
//	logStatisticInfo();
//
//	if (sum == 0)
//		cerr << "\nAll the branches can't be negated!\n";
//	else
//		cerr << "\nIn total, there are " << sum << "/" << size
//				<< " branches can be negated!\n";
}

void Encode::showInitTrace() {
	string ErrorInfo;
	stringstream output;
	output << "./output_info/" << "Trace" << trace->Id << ".bitcode" ;
	raw_fd_ostream out_to_file(output.str().c_str(), ErrorInfo, 0x0200);
	unsigned size = trace->path.size();
//bitcode
	for (unsigned i = 0; i < size; i++) {
		Event* currEvent = trace->path[i];
		if (trace->path[i]->inst->info->line == 0
				|| trace->path[i]->eventType != Event::NORMAL)
			continue;
		out_to_file << i << "---" << trace->path[i]->threadId << "---"
				<< trace->path[i]->eventName << "---"
				<< trace->path[i]->inst->inst->getParent()->getParent()->getName().str()
				<< "---" << trace->path[i]->inst->info->line << "---"
				<< trace->path[i]->condition << "---";
		trace->path[i]->inst->inst->print(out_to_file);
		if (currEvent->isGlobal) {
			out_to_file << "--" << currEvent->globalVarFullName << "=";
			string str = currEvent->globalVarFullName;
			if (str == ""){
				out_to_file << "\n";
				continue;
			}
		}
		if (currEvent->isLocal) {
			out_to_file << "--" << currEvent->varName << "=";
			string str = currEvent->varName;
		}
		out_to_file << "\n";
	}
//source code
	printSourceLine("./output_info/source_trace", trace->path);
}


void Encode::computePrefix(vector<Event*>& vecEvent, Event* ifEvent) {
	vector<struct Pair *> eventOrderPair;
//get the order of event
	map<string, expr>::iterator it = eventNameInZ3.find(ifEvent->eventName);
	assert(it != eventNameInZ3.end());
	model m = z3_solver.get_model();
	stringstream ss;
	ss << m.eval(it->second);
	long ifEventOrder = atoi(ss.str().c_str());
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0, size = thread->size(); index < size; index++) {
			if (thread->at(index)->eventType == Event::VIRTUAL)
				continue;

			it = eventNameInZ3.find(thread->at(index)->eventName);
			assert(it != eventNameInZ3.end());
			stringstream ss;
			ss << m.eval(it->second);
			long order = atoi(ss.str().c_str());
			//cut off segment behind the negated branch
			if (order > ifEventOrder)
				continue;
			if (order == ifEventOrder
					&& thread->at(index)->threadId != ifEvent->threadId)
				continue;
			if (thread->at(index)->eventName == ifEvent->eventName
					&& thread->at(index)->eventId > ifEvent->eventId)
				continue;
			//put the event to its position
			//
			Pair * pair = new Pair;				//should be deleted
			pair->order = order;
			pair->event = thread->at(index);
			eventOrderPair.push_back(pair);
		}
	}

//sort all events according to order
	unsigned size = eventOrderPair.size();
	for (unsigned i = 0; i < size - 1; i++) {
		for (unsigned j = 0; j < size - i - 1; j++) {
			if (eventOrderPair[j]->order > eventOrderPair[j + 1]->order) {
				Pair *temp = eventOrderPair[j];
				eventOrderPair[j] = eventOrderPair[j + 1];
				eventOrderPair[j + 1] = temp;
			}
		}
	}

//put the ordered events to vecEvent.
	for (unsigned i = 0; i < eventOrderPair.size(); i++) {
		//TODO: use a simple struct to log prefix
		vecEvent.push_back(eventOrderPair[i]->event);
		delete eventOrderPair[i];
	}
}

void Encode::showPrefixInfo(Prefix* prefix, Event* ifEvent) {
	vector<Event*>* orderedEventList = prefix->getEventList();
	unsigned size = orderedEventList->size();
	model m = z3_solver.get_model();
//print counterexample at bitcode
	string ErrorInfo;
	stringstream output;
	output << "./output_info/" << prefix->getName() << ".bitcode";
	raw_fd_ostream out_to_file(output.str().c_str(), ErrorInfo,
//			0x0200);
			raw_fd_ostream::BLACK);
	cerr << ErrorInfo;
//out_to_file << "threadId:   "<< "lineNum:    " << "source:" <<"\n";
//raw_fd_ostream out_to_file("./output_info/counterexample.txt", ErrorInfo, 2 & 0x0200);
	for (unsigned i = 0; i < size; i++) {
		Event* currEvent = orderedEventList->at(i);
		out_to_file << currEvent->threadId << "---" << currEvent->eventName
				<< "---"
				<< currEvent->inst->inst->getParent()->getParent()->getName().str()
				<< "---" << currEvent->inst->info->line << "---"
				<< currEvent->condition << "---";
		currEvent->inst->inst->print(out_to_file);
		if (currEvent->isGlobal) {
			out_to_file << "--" << currEvent->globalVarFullName << "=";
			string str = currEvent->globalVarFullName;
			if (str == ""){
				out_to_file << "\n";
				continue;
			}
			stringstream ss;
#if INT_ARITHMETIC
			ss << m.eval(z3_ctx.int_const(str.c_str()));
#else
			ss << m.eval(z3_ctx.bv_const(str.c_str(), BIT_WIDTH));	//just for
#endif
			out_to_file << ss.str();
		}
		if (currEvent->isLocal) {
			out_to_file << "--" << currEvent->varName << "=";
			string str = currEvent->varName;
			stringstream ss;
#if INT_ARITHMETIC
			ss << m.eval(z3_ctx.int_const(str.c_str()));
#else
			ss << m.eval(z3_ctx.bv_const(str.c_str(), BIT_WIDTH));
#endif
			out_to_file << ss.str();
		}
		out_to_file << "\n";
	}
	out_to_file.close();
//print source code
//	printSourceLine(filename, eventOrderPair);
}

/*
 * called by showInitTrace to print initial trace
 */
void Encode::printSourceLine(string path, vector<Event *>& trace) {
	string output;
	string ErrorInfo;
	output = path + ".txt";
	raw_fd_ostream out_to_file(output.c_str(), ErrorInfo, 0x0200);
	out_to_file << "threadId  " << "lineNum   " << "function                 "
			<< "source" << "\n";
	unsigned preThreadId = 0, preCodeLine = 0;
	for (unsigned i = 0, size = trace.size(); i < size; i++) {
		if (trace[i]->eventType != Event::NORMAL)
			continue;
		if (trace[i]->inst->info->line == 0)
			continue;
		unsigned currCodeLine = trace[i]->inst->info->line;
		unsigned currThreadId = trace[i]->threadId;
		if (currThreadId == preThreadId && currCodeLine == preCodeLine)
			continue;
//		string fileName = trace[i]->codeDir + "/" + trace[i]->codeFile;
		string fileName = trace[i]->inst->info->file;
		string source = readLine(fileName, trace[i]->inst->info->line);
		if (source == "")
			assert(0 && "blank line");
		if (source == "{" || source == "}")
			continue;
		//write to file
		int len;
		stringstream ss;
		ss << currThreadId;
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 10 - len; k++)
			ss << " ";
		ss << currCodeLine;
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 20 - len; k++)
			ss << " ";
		ss << trace[i]->inst->inst->getParent()->getParent()->getName().str();
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 45 - len; k++)
			ss << " ";
		ss << source << "\n";
		out_to_file << ss.str();

		preThreadId = currThreadId;
		preCodeLine = currCodeLine;
	}
}

/*
 * called by showEventSequence to print counterexample
 */
void Encode::printSourceLine(string path,
		vector<struct Pair *>& eventIndexPair) {
	string output;
	string ErrorInfo;
	output = "./output_info/" + path + ".source";
	raw_fd_ostream out_to_file(output.c_str(), ErrorInfo, 0x0200);
	out_to_file << "threadId  " << "lineNum   " << "function                 "
			<< "source" << "\n";

	unsigned preThreadId = 0, preCodeLine = 0;
	for (unsigned i = 0, size = eventIndexPair.size(); i < size; i++) {

		if (eventIndexPair[i]->event->eventType != Event::NORMAL)
			continue;
		if (eventIndexPair[i]->event->inst->info->line == 0)
			continue;
		unsigned currCodeLine = eventIndexPair[i]->event->inst->info->line;
		unsigned currThreadId = eventIndexPair[i]->event->threadId;
		if (currThreadId == preThreadId && currCodeLine == preCodeLine)
			continue;
//		string fileName = eventIndexPair[i]->event->codeDir + "/"
//				+ eventIndexPair[i]->event->codeFile;
		string fileName = eventIndexPair[i]->event->inst->info->file;
		string source = readLine(fileName,
				eventIndexPair[i]->event->inst->info->line);
		if (source == "{" || source == "}")
			continue;
		//write to file
		int len;
		stringstream ss;
		ss << currThreadId;
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 10 - len; k++)
			ss << " ";
		ss << currCodeLine;
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 20 - len; k++)
			ss << " ";
		ss
				<< eventIndexPair[i]->event->inst->inst->getParent()->getParent()->getName().str();
		len = strlen(ss.str().c_str());
		for (int k = 0; k < 45 - len; k++)
			ss << " ";
		ss << source << "\n";
		out_to_file << ss.str();
		preThreadId = currThreadId;
		preCodeLine = currCodeLine;
	}
}

bool Encode::isAssert(string filename, unsigned line) {
	char source[BUFFERSIZE];
	ifstream ifile(filename.c_str());
	if (!ifile.is_open())
		assert(0 && "open file error");
	unsigned i = 0;
	while (i != line) {
		ifile.getline(source, BUFFERSIZE);
		i += 1;
	}
	ifile.close();
	string s(source);
	return s.find("assert", 0) != string::npos;
}

string Encode::readLine(string filename, unsigned line) {
	char source[BUFFERSIZE];
	ifstream ifile(filename.c_str());
	if (!ifile.is_open())
		assert(0 && "open file error");
	unsigned i = 0;
	while (i != line) {
		ifile.getline(source, BUFFERSIZE);
		i += 1;
	}
	ifile.close();
	return stringTrim(source);
}

string Encode::stringTrim(char * source) {
	string ret;
	char dest[BUFFERSIZE];
	int k = 0;
	int s = 0, e = 0;
	int len = strlen(source);
	for (int i = 0; i < len; i++) {
		if (!isspace(source[i])) {
			s = i;
			break;
		}
	}
	for (int i = (len - 1); i >= 0; i--) {
		if (!isspace(source[i])) {
			e = i;
			break;
		}
	}
	for (int i = s; i <= e; i++) {
		dest[k++] = source[i];
	}
	dest[k] = '\0';
	ret = dest;
	return ret;
}
void Encode::logStatisticInfo() {
	unsigned threadNumber = 0;
	unsigned instNumber = 0;
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		threadNumber++;
		instNumber += thread->size();
	}
	unsigned lockNumber = trace->all_lock_unlock.size();
	unsigned lockPairNumber = 0;
	std::map<std::string, std::vector<LockPair *> >::iterator it =
			trace->all_lock_unlock.begin();
	for (; it != trace->all_lock_unlock.end(); it++) {
		lockPairNumber += it->second.size();
	}
	unsigned signalNumber = trace->all_signal.size();
	unsigned waitNumber = trace->all_wait.size();
	unsigned sharedVarNumber = trace->global_variable_final.size();
	unsigned readNumber = trace->readSet.size();
	unsigned writeNumber = trace->writeSet.size();
	string ErrorInfo;
	raw_fd_ostream out("./output_info/statistic.info", ErrorInfo, 0x0200);
	out << "#Threads:" << threadNumber << "\n";
	out << "#Instructions: " << instNumber << "\n";
	out << "#Locks: " << lockNumber << "\n";
	out << "#Lock/Unlock Pairs: " << lockPairNumber << "\n";
	out << "#Signal/Wait: " << signalNumber << "/" << waitNumber << "\n";
	out << "#Shared Variables: " << sharedVarNumber << "\n";
	out << "#Read/Write of shared points: " << readNumber << "/" << writeNumber
			<< "\n";
//	out << "#Constaints: " << constaintNumber << "\n";
}

void Encode::buildInitValueFormula(solver z3_solver_init) {
//for global initializer
#if FORMULA_DEBUG
	cerr << "\nGlobal var initial value:\n";
	cerr << "\nGlobal var initial size: " << trace->global_variable_initializer.size() << "\n";
#endif
	std::map<std::string, llvm::Constant*>::iterator gvi =
			trace->useful_global_variable_initializer.begin();

	for (; gvi != trace->useful_global_variable_initializer.end(); gvi++) {
		//bitwidth may introduce bug!!!
		const Type *type = gvi->second->getType();
		const z3::sort varType(llvmTy_to_z3Ty(type));
		string str = gvi->first + "_Init";
		expr lhs = z3_ctx.constant(str.c_str(), varType);
		expr rhs = buildExprForConstantValue(gvi->second, false, "");
		z3_solver_init.add(lhs == rhs);

#if FORMULA_DEBUG
		cerr << (lhs == rhs) << "\n";
#endif
	}
	//statics
	formulaNum += trace->useful_global_variable_initializer.size();
}

void Encode::buildOutputFormula() {
//for global var at last
//need to choose manually
#if FORMULA_DEBUG
	cerr << "\nGlobal var final value:\n";
#endif
	std::map<std::string, llvm::Constant*>::iterator gvl =
			trace->global_variable_final.begin();
	for (; gvl != trace->global_variable_final.end(); gvl++) {
		const Type *type = gvl->second->getType();
		const z3::sort varType(llvmTy_to_z3Ty(type));
		string str = gvl->first + "_Final";
		expr lhs = z3_ctx.constant(str.c_str(), varType);
		expr rhs = buildExprForConstantValue(gvl->second, false, "");
		expr finalValue = (lhs == rhs);
		expr constrait = z3_ctx.bool_val(1);

		vector<Event*> maybeRead;
		map<int, map<string, Event*> >::iterator atlw =
				allThreadLastWrite.begin();
		for (; atlw != allThreadLastWrite.end(); atlw++) {
			map<string, Event*>::iterator it = atlw->second.find(gvl->first);
			if (it != atlw->second.end()) {
				maybeRead.push_back(it->second);
			}
		}
		if (maybeRead.size() == 0) {	//be equal with initial value!
			string str = gvl->first + "_Init";
			expr init = z3_ctx.constant(str.c_str(), varType);
			constrait = (lhs == init);
		} else {	//be equal with the last write in some threads
			vector<expr> allReads;
			for (unsigned i = 0; i < maybeRead.size(); i++) {
				//build the equation
				expr write = z3_ctx.constant(
						maybeRead[i]->globalVarFullName.c_str(), varType);//used write event
				expr eq = (lhs == write);
				//build the constrait of equation
				expr writeOrder = z3_ctx.int_const(
						maybeRead[i]->eventName.c_str());
				vector<expr> beforeRelation;
				for (unsigned j = 0; j < maybeRead.size(); j++) {
					if (j == i)
						continue;
					expr otherWriteOrder = z3_ctx.int_const(
							maybeRead[j]->eventName.c_str());
					expr temp = (otherWriteOrder < writeOrder);
					beforeRelation.push_back(temp);
				}
				expr tmp = makeExprsAnd(beforeRelation);
				allReads.push_back(eq && tmp);
			}
			constrait = makeExprsOr(allReads);
		}

		pair<expr, expr> temp = make_pair(finalValue, constrait);
#if FORMULA_DEBUG
		cerr << "\n" << finalValue << "-------" << constrait;
#endif
		globalOutputFormula.push_back(temp);
	}
}

void Encode::markLatestWriteForGlobalVar() {
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0; index < thread->size(); index++) {
			Event* event = thread->at(index);
			if (event->usefulGlobal) {
//			if (event->isGlobal) {
				Instruction *I = event->inst->inst;
				if (StoreInst::classof(I)) { //write
					latestWriteOneThread[event->varName] = event;
				} else if (!event->implicitGlobalVar.empty()
						&& CallInst::classof(I)) {
					for (unsigned i = 0; i < event->implicitGlobalVar.size();
							i++) {
						string curr = event->implicitGlobalVar[i];
						string varName = curr.substr(0, curr.find('S', 0));
						latestWriteOneThread[varName] = event;
					}
				} else { //read
					Event * writeEvent;
					map<string, Event *>::iterator it;
					it = latestWriteOneThread.find(event->varName);
					if (it != latestWriteOneThread.end()) {
						writeEvent = it->second;
					} else {
						writeEvent = NULL;
					}
					event->latestWrite = writeEvent;
				}
			}
		}
		//post operations
		allThreadLastWrite[tid] = latestWriteOneThread;
		latestWriteOneThread.clear();
	}
}

void Encode::buildPathCondition(solver z3_solver_pc) {
#if FORMULA_DEBUG
	cerr << "\nBasicFormula:\n";
#endif

	KQuery2Z3 *kq = new KQuery2Z3(z3_ctx);;
	unsigned int totalExpr = trace->usefulkQueryExpr.size();
	for (unsigned int i = 0; i < totalExpr; i++) {
		z3::expr temp = kq->getZ3Expr(trace->usefulkQueryExpr[i]);
		z3_solver_pc.add(temp);
#if FORMULA_DEBUG
	cerr << temp << "\n";
#endif
	}

}

void Encode::buildifAndassert() {
	Trace* trace = runtimeData->getCurrentTrace();
	filter.filterUseless(trace);
#if DEBUGSYMBOLIC
	cerr << "all constraint :" << std::endl;
	std::cerr << "storeSymbolicExpr = " << trace->storeSymbolicExpr.size()
	<< std::endl;
	for (std::vector<ref<Expr> >::iterator it = trace->storeSymbolicExpr.begin(),
			ie = trace->storeSymbolicExpr.end(); it != ie; ++it) {
		it->get()->dump();
	}
	std::cerr << "brSymbolicExpr = " << trace->brSymbolicExpr.size()
	<< std::endl;
	for (std::vector<ref<Expr> >::iterator it = trace->brSymbolicExpr.begin(),
			ie = trace->brSymbolicExpr.end(); it != ie; ++it) {
		it->get()->dump();
	}
	std::cerr << "assertSymbolicExpr = " << trace->assertSymbolicExpr.size()
	<< std::endl;

	for (std::vector<ref<Expr> >::iterator it = trace->assertSymbolicExpr.begin(),
			ie = trace->assertSymbolicExpr.end(); it != ie; ++it) {
		it->get()->dump();
	}
	std::cerr << "kQueryExpr = " << trace->kQueryExpr.size()
	<< std::endl;
	for (std::vector<ref<Expr> >::iterator it = trace->kQueryExpr.begin(),
			ie = trace->kQueryExpr.end(); it != ie; ++it) {
		it->get()->dump();
	}
#endif
	unsigned brGlobal = 0;
	runtimeData->getCurrentTrace()->traceType = Trace::UNIQUE;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			readSet.begin(), nie = readSet.end(); nit != nie; ++nit) {
		brGlobal += nit->second.size();
	}
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			writeSet.begin(), nie = writeSet.end(); nit != nie; ++nit) {
		std::string varName = nit->first;
		if (trace->readSet.find(varName) == trace->readSet.end()) {
			brGlobal += nit->second.size();
		}
	}
	runtimeData->brGlobal += brGlobal;

	KQuery2Z3 * kq = new KQuery2Z3(z3_ctx);

	unsigned int totalAssertEvent = trace->assertEvent.size();
	unsigned int totalAssertSymbolic = trace->assertSymbolicExpr.size();
	assert( totalAssertEvent == totalAssertSymbolic
					&& "the number of brEvent is not equal to brSymbolic");
	Event * event = NULL;
	z3::expr res = z3_ctx.bool_val(true);
	for (unsigned int i = 0; i < totalAssertEvent; i++) {
		event = trace->assertEvent[i];
//		cerr << "asert : " << trace->assertSymbolicExpr[i] <<"\n";
		res = kq->getZ3Expr(trace->assertSymbolicExpr[i]);
//		string fileName = event->inst->info->file;
		unsigned line = event->inst->info->line;
		if (line != 0)
			assertFormula.push_back(make_pair(event, res));
//		else
//			ifFormula.push_back(make_pair(event, res));

	}

	unsigned int totalBrEvent = trace->brEvent.size();
	for (unsigned int i = 0; i < totalBrEvent; i++) {
		event = trace->brEvent[i];
//		cerr << "br : " << trace->brSymbolicExpr[i] <<"\n";
		res = kq->getZ3Expr(trace->brSymbolicExpr[i]);
		if(event->isConditionIns == true){
//			event->inst->inst->dump();
//			string fileName = event->inst->info->file;
//			unsigned line = event->inst->info->line;
//			cerr << "fileName : " << fileName <<" line : " << line << "\n";
			ifFormula.push_back(make_pair(event, res));
//			cerr << "event name : " << ifFormula[i].first->eventName << "\n";
//			cerr << "constraint : " << ifFormula[i].second << "\n";
		}else if(event->isConditionIns == false){
			z3_solver.add(res);
		}
	}


	unsigned int totalRwExpr = trace->rwSymbolicExpr.size();
	for (unsigned int i = 0; i < totalRwExpr; i++) {
		event = trace->rwEvent[i];
		res = kq->getZ3Expr(trace->rwSymbolicExpr[i]);
		rwFormula.push_back(make_pair(event, res));
//		cerr << "rwSymbolicExpr : " << res << "\n";
	}
	buildAllFormula();
}

expr Encode::buildExprForConstantValue(Value *V, bool isLeft,
		string currInstPrefix) {
	assert(V && "V is null!");
	expr ret = z3_ctx.bool_val(1);
//llvm type to z3 type, except load and store inst which contain pointer
	const z3::sort varType(llvmTy_to_z3Ty(V->getType()));
//
	if (ConstantInt *ci = dyn_cast<ConstantInt>(V)) {
		int val = ci->getSExtValue();
		unsigned num_bit = ((IntegerType *) V->getType())->getBitWidth();
		if (num_bit == 1)
			ret = z3_ctx.bool_val(val);
		else
#if INT_ARITHMETIC
			ret = z3_ctx.int_val(val);
#else
			ret = z3_ctx.bv_val(val, BIT_WIDTH);
#endif
	} else if (ConstantFP *cf = dyn_cast<ConstantFP>(V)) {
		double val;
		APFloat apf = cf->getValueAPF();
		const struct llvm::fltSemantics & semantics = apf.getSemantics();
		if (apf.semanticsPrecision(semantics) == 53)
			val = apf.convertToDouble();
		else if (apf.semanticsPrecision(semantics) == 24)
			val = apf.convertToFloat();
		else
			assert(0 && "Wrong with Float Type!");

//		cerr << setiosflags(ios::fixed) << val << "\n";
		char s[200];
		sprintf(s, "%f", val);
		ret = z3_ctx.real_val(s);
	} else if (dyn_cast<ConstantPointerNull>(V)) {
		//%cmp = icmp eq %struct.bounded_buf_tag* %tmp, null
#if INT_ARITHMETIC
		ret = z3_ctx.int_val(0);
#else
		ret = z3_ctx.bv_val(0, BIT_WIDTH);
#endif
	} else if (llvm::ConstantExpr* constantExpr = dyn_cast<llvm::ConstantExpr>(
			V)) {
		Instruction* inst = constantExpr->getAsInstruction();
		if (IntToPtrInst::classof(inst)) {
			//cmp26 = icmp eq i8* %tmp19, inttoptr (i32 -1 to i8*)
			IntToPtrInst * ptrtoint = dyn_cast<IntToPtrInst>(inst);
			ConstantInt * ci = dyn_cast<ConstantInt>(ptrtoint->getOperand(0));
			assert(ci && "Impossible!");
			int val = ci->getValue().getLimitedValue();
#if INT_ARITHMETIC
			ret = z3_ctx.int_val(val);
#else
			ret = z3_ctx.bv_val(val, BIT_WIDTH);	//to pointer, the default is 32bit.
#endif
		} else {
			assert(0 && "unknown type of Value:1");
		}
		delete inst;		//must be done
	} else {
		assert(0 && "unknown type of Value:2");
	}

	return ret;
}

z3::sort Encode::llvmTy_to_z3Ty(const Type *typ) {
	switch (typ->getTypeID()) {
	case Type::VoidTyID:
		assert(0 && "void return value!");
		break;
	case Type::HalfTyID:
	case Type::FloatTyID:
	case Type::DoubleTyID:
		return z3_ctx.real_sort();
	case Type::X86_FP80TyID:
		assert(0 && "couldn't handle X86_FP80 type!");
		break;
	case Type::FP128TyID:
		assert(0 && "couldn't handle FP128 type!");
		break;
	case Type::PPC_FP128TyID:
		assert(0 && "couldn't handle PPC_FP128 type!");
		break;
	case Type::LabelTyID:
		assert(0 && "couldn't handle Label type!");
		break;
	case Type::MetadataTyID:
		assert(0 && "couldn't handle Metadata type!");
		break;
	case Type::X86_MMXTyID:
		assert(0 && "couldn't handle X86_MMX type!");
		break;
	case Type::IntegerTyID: {
		unsigned num_bit = ((IntegerType *) typ)->getBitWidth();
		if (num_bit == 1) {
			return z3_ctx.bool_sort();;
		} else {
#if INT_ARITHMETIC
			return z3_ctx.int_sort();
#else
			return z3_ctx.bv_sort(BIT_WIDTH);
#endif
		}
		break;
	}
	case Type::FunctionTyID:
		assert(0 && "couldn't handle Function type!");
		break;
	case Type::StructTyID:
#if INT_ARITHMETIC
		return z3_ctx.int_sort();
#else
		return z3_ctx.bv_sort(BIT_WIDTH);
#endif
		break;
	case Type::ArrayTyID:
		assert(0 && "couldn't handle Array type!");             //must
		break;
	case Type::PointerTyID:
#if INT_ARITHMETIC
		return z3_ctx.int_sort();
#else
		return z3_ctx.bv_sort(BIT_WIDTH);
#endif
	case Type::VectorTyID:
		assert(0 && "couldn't handle Vector type!");
		break;
	case Type::NumTypeIDs:
		assert(0 && "couldn't handle NumType type!");
		break;
		//case Type::LastPrimitiveTyID: assert(0); break;
		//case Type::FirstDerivedTyID: assert(0); break;
	default:
		assert(0 && "No such type!");
		break;
	}
#if INT_ARITHMETIC
	return z3_ctx.int_sort();
#else
	return z3_ctx.bv_sort(BIT_WIDTH);
#endif
}        //

void Encode::buildMemoryModelFormula() {
#if FORMULA_DEBUG
	cerr << "\nMemoryModelFormula:\n";
#endif
	z3_solver.add(z3_ctx.int_const("E_INIT") == 0);
	//statics
	formulaNum++;
//level: 0 bitcode; 1 source code; 2 block
	controlGranularity(2);
//
//initial and final
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		//initial
		Event* firstEvent = thread->at(0);
		expr init = z3_ctx.int_const("E_INIT");
		expr firstEventExpr = z3_ctx.int_const(firstEvent->eventName.c_str());
		expr temp1 = (init < firstEventExpr);
#if FORMULA_DEBUG
		cerr << temp1 << "\n";
#endif
		z3_solver.add(temp1);

		//final
		Event* finalEvent = thread->back();
		expr final = z3_ctx.int_const("E_FINAL");
		expr finalEventExpr = z3_ctx.int_const(finalEvent->eventName.c_str());
		expr temp2 = (finalEventExpr < final);
#if FORMULA_DEBUG
		cerr << temp2 << "\n";
#endif
		z3_solver.add(temp2);
		//statics
		formulaNum += 2;
	}

//normal events
	int uniqueEvent = 1;
	for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
		std::vector<Event*>* thread = trace->eventList[tid];
		if (thread == NULL)
			continue;
		for (unsigned index = 0, size = thread->size(); index < size - 1;
				index++) {
			Event* pre = thread->at(index);
			Event* post = thread->at(index + 1);
			//by clustering
			if (pre->eventName == post->eventName)
				continue;
			uniqueEvent++;
			expr preExpr = z3_ctx.int_const(pre->eventName.c_str());
			expr postExpr = z3_ctx.int_const(post->eventName.c_str());
			expr temp = (preExpr < postExpr);
#if FORMULA_DEBUG
			cerr << temp << "\n";
#endif
			z3_solver.add(temp);
			//statics
			formulaNum++;

			//eventNameInZ3 will be used at check_if
			eventNameInZ3.insert(
					map<string, expr>::value_type(pre->eventName, preExpr));
			eventNameInZ3.insert(
					map<string, expr>::value_type(post->eventName, postExpr));
		}
	}
	z3_solver.add(
			z3_ctx.int_const("E_FINAL") == z3_ctx.int_val(uniqueEvent) + 100);
	//statics
	formulaNum++;
}

//level: 0--bitcode; 1--source code; 2--block
void Encode::controlGranularity(int level) {
//	map<string, InstType> record;
	if (level == 0)
		return;
	else if (level == 1) {
		for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
			std::vector<Event*>* thread = trace->eventList[tid];
			if (thread == NULL)
				continue;
			Event* pre = thread->at(0);
			int preLineNum = pre->inst->info->line;
			InstType preInstType = getInstOpType(thread->at(0));
			string preEventName = thread->at(0)->eventName;

			for (unsigned index = 1, size = thread->size(); index < size;
					index++) {
				Event* curr = thread->at(index);
				InstType currInstType = getInstOpType(curr);

				//debug
//				curr->inst->inst->print(cerr);
//				if (currInstType == NormalOp)
//					cerr << "\noptype : NormalOp\n";
//				else if (currInstType == GlobalVarOp)
//					cerr << "\noptype : GlobalVarOp\n";
//				else if (currInstType == ThreadOp)
//					cerr << "\noptype : ThreadOp\n";
//				else
//					assert(0);

				int currLineNum = thread->at(index)->inst->info->line;

				if (currLineNum == preLineNum) {
					if (preInstType == NormalOp) {
						curr->eventName = preEventName;
						preInstType = currInstType;
					} else {
						if (currInstType == NormalOp) {
							curr->eventName = preEventName;
						} else {
							preInstType = currInstType;
							preEventName = curr->eventName;
						}
					}
				} else {
					preLineNum = currLineNum;
					preInstType = currInstType;
					preEventName = curr->eventName;
				}
			}
		}
	} else {
		for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
			std::vector<Event*>* thread = trace->eventList[tid];
			if (thread == NULL)
				continue;
			Event* pre = thread->at(0);
			InstType preInstType = getInstOpType(pre);
			string preEventName = pre->eventName;

			for (unsigned index = 1, size = thread->size(); index < size;
					index++) {
				Event* curr = thread->at(index);
				InstType currInstType = getInstOpType(curr);

				//debug
//				curr->inst->inst->print(cerr);
//				cerr << "\n";
//				if (currInstType == NormalOp)
//					cerr << "NormalOp!\n";
//				else if (currInstType == GlobalVarOp)
//					cerr << "GlobalVarOp!\n";
//				else if (currInstType == ThreadOp)
//					cerr << "ThreadOp!\n";

				if (preInstType == NormalOp) {
					curr->eventName = preEventName;
				} else {
					preEventName = curr->eventName;
				}
				preInstType = currInstType;
			}
		}
	}
}

InstType Encode::getInstOpType(Event * event) {
	if (event->isGlobal) {
		return GlobalVarOp;
	}
	Instruction *I = event->inst->inst;
//	if (BranchInst::classof(I)) {
//		BranchInst* brI = dyn_cast<BranchInst>(I);
//		if (brI->isConditional()) {
//			return GlobalVarOp; //actually it's a br. just using
//		}
//	}
	if (!CallInst::classof(I)) {
		return NormalOp;
	}
//switch
//	CallInst* callI = dyn_cast<CallInst>(I);
//	if (callI->getCalledFunction() == NULL)
	if (event->calledFunction == NULL) {
		return NormalOp;
	}
//switch
//	const char* functionName = callI->getCalledFunction()->getName().data();
	const char* functionName = event->calledFunction->getName().data();

	if (strncmp("pthread", functionName, 7) == 0) {
		return ThreadOp;
	}
	return NormalOp;
}

void Encode::buildPartialOrderFormula() {
#if FORMULA_DEBUG
	cerr << "\nPartialOrderFormula:\n";
#endif
//handle thread_create
	std::map<Event*, uint64_t>::iterator itc = trace->createThreadPoint.begin();
	for (; itc != trace->createThreadPoint.end(); itc++) {
		//the event is at the point of creating thread
		string creatPoint = itc->first->eventName;
		//the event is the first step of created thread
		string firstStep = trace->eventList[itc->second]->at(0)->eventName;
		expr prev = z3_ctx.int_const(creatPoint.c_str());
		expr back = z3_ctx.int_const(firstStep.c_str());
		expr twoEventOrder = (prev < back);
#if FORMULA_DEBUG
		cerr << twoEventOrder << "\n";
#endif
		z3_solver.add(twoEventOrder);
	}
	//statics
	formulaNum += trace->createThreadPoint.size();

//handle thread_join
	std::map<Event*, uint64_t>::iterator itj = trace->joinThreadPoint.begin();
	for (; itj != trace->joinThreadPoint.end(); itj++) {
		//the event is at the point of joining thread
		string joinPoint = itj->first->eventName;
		//the event is the last step of joined thread
		string lastStep = trace->eventList[itj->second]->back()->eventName;
		expr prev = z3_ctx.int_const(lastStep.c_str());
		expr back = z3_ctx.int_const(joinPoint.c_str());
		expr twoEventOrder = (prev < back);
#if FORMULA_DEBUG
		cerr << twoEventOrder << "\n";
#endif
		z3_solver.add(twoEventOrder);
	}
	//statics
	formulaNum += trace->joinThreadPoint.size();
}

void Encode::buildReadWriteFormula(solver z3_solver_rw) {
#if FORMULA_DEBUG
	cerr << "\nReadWriteFormula:\n";
#endif
//prepare
	markLatestWriteForGlobalVar();
//
//	cerr << "size : " << trace->readSet.size()<<"\n";
//	cerr << "size : " << trace->writeSet.size()<<"\n";
	map<string, vector<Event *> >::iterator read;
	map<string, vector<Event *> >::iterator write;

//debug
//print out all the read and write insts of global vars.
	if (false) {
		read = trace->usefulReadSet.begin();
		for (; read != trace->usefulReadSet.end(); read++) {
			cerr << "global var read:" << read->first << "\n";
			for (unsigned i = 0; i < read->second.size(); i++) {
				cerr << read->second[i]->eventName << "---"
						<< read->second[i]->globalVarFullName << "\n";
			}
		}
		write = trace->usefulWriteSet.begin();
		for (; write != trace->usefulWriteSet.end(); write++) {
			cerr << "global var write:" << write->first << "\n";
			for (unsigned i = 0; i < write->second.size(); i++) {
				cerr << write->second[i]->eventName << "---"
						<< write->second[i]->globalVarFullName << "\n";
			}
		}
	}
//debug

	map<string, vector<Event *> >::iterator ir = trace->usefulReadSet.begin(); //key--variable,
	Event *currentRead;
	Event *currentWrite;
	for (; ir != trace->usefulReadSet.end(); ir++) {
		map<string, vector<Event *> >::iterator iw = trace->usefulWriteSet.find(
				ir->first);
		//maybe use the initial value from Initialization.@2014.4.16
		//if(iw == writeSet.end())
		//continue;
		for (unsigned k = 0; k < ir->second.size(); k++) {
			vector<expr> oneVarAllRead;
			currentRead = ir->second[k];
			expr r = z3_ctx.int_const(currentRead->eventName.c_str());

			//compute the write set that may be used by currentRead;
			vector<Event *> mayBeRead;
			unsigned currentWriteThreadId;
			if (iw != trace->usefulWriteSet.end()) {
				for (unsigned i = 0; i < iw->second.size(); i++) {
					if (iw->second[i]->threadId == currentRead->threadId)
						continue;
					else
						mayBeRead.push_back(iw->second[i]);
				}
			}
			if (currentRead->latestWrite != NULL) {
				mayBeRead.push_back(currentRead->latestWrite);
			} else//if this read don't have the corresponding write, it may use from Initialization operation.
			{
				//so, build the formula constrainting this read uses from Initialization operation

				vector<expr> oneVarOneRead;
				expr equal = z3_ctx.bool_val(1);
				bool flag = readFromInitFormula(currentRead, equal);
				if (flag != false) {
					//statics
					formulaNum++;
					oneVarOneRead.push_back(equal);
					for (unsigned j = 0; j < mayBeRead.size(); j++) {
						currentWrite = mayBeRead[j];
						expr w = z3_ctx.int_const(
								currentWrite->eventName.c_str());
						expr order = r < w;
						oneVarOneRead.push_back(order);
					}
					//statics
					formulaNum += mayBeRead.size();
					expr readFromInit = makeExprsAnd(oneVarOneRead);
					oneVarAllRead.push_back(readFromInit);
				}
			}
			//

			for (unsigned i = 0; i < mayBeRead.size(); i++) {
				//cause the write operation of every thread is arranged in the executing order
				currentWrite = mayBeRead[i];
				currentWriteThreadId = currentWrite->threadId;
				vector<expr> oneVarOneRead;
				expr equal = readFromWriteFormula(currentRead, currentWrite,
						ir->first);
				oneVarOneRead.push_back(equal);

				expr w = z3_ctx.int_const(currentWrite->eventName.c_str());
				expr rw = (w < r);
				//statics
				formulaNum += 2;
				//-----optimization-----//
				//the next write in the same thread must be behind this read.
				if (i + 1 <= mayBeRead.size() - 1 &&			//short-circuit
						mayBeRead[i + 1]->threadId == currentWriteThreadId) {
					expr nextw = z3_ctx.int_const(
							mayBeRead[i + 1]->eventName.c_str());
					//statics
					formulaNum++;
					rw = (rw && (r < nextw));
				}
				//

				oneVarOneRead.push_back(rw);

				unsigned current = i;
				for (unsigned j = 0; j < mayBeRead.size(); j++) {
					if (current == j
							|| currentWriteThreadId == mayBeRead[j]->threadId)
						continue;
					expr temp = enumerateOrder(currentRead, currentWrite,
							mayBeRead[j]);
					//statics
					formulaNum += 2;
					oneVarOneRead.push_back(temp);
				}
				//equal if-and-only-if possibleOrder
				expr if_and_only_if = makeExprsAnd(oneVarOneRead);
				oneVarAllRead.push_back(if_and_only_if);
			}

			expr oneReadExprs = makeExprsOr(oneVarAllRead);
#if FORMULA_DEBUG
			cerr << oneReadExprs << "\n";
#endif
			z3_solver_rw.add(oneReadExprs);
		}
	}
}

expr Encode::readFromWriteFormula(Event * read, Event * write, string var) {
	Instruction *I = read->inst->inst;
	const Type * type = I->getType();
	while (type->getTypeID() == Type::PointerTyID) {
		type = type->getPointerElementType();
	}
//assert(I->getType()->getTypeID() == Type::PointerTyID && "Wrong Type!");
	const z3::sort varType(llvmTy_to_z3Ty(type));
	expr r = z3_ctx.constant(read->globalVarFullName.c_str(), varType);
	string writeVarName = "";
	if (write->globalVarFullName == "" && !write->implicitGlobalVar.empty()) {
		for (unsigned i = 0; i < write->implicitGlobalVar.size(); i++) {
			if (strncmp(var.c_str(), write->implicitGlobalVar[i].c_str(),
					var.size()) == 0) {
#if FORMULA_DEBUG
				cerr << "Event name : " << write->eventName << "\n";
				cerr<< "rw : " << var.c_str() << "---"
//						<< it->first.c_str()
						<< "\n";
#endif
				writeVarName = write->implicitGlobalVar[i];
				break;
			}

		}
	} else
		writeVarName = write->globalVarFullName;

	expr w = z3_ctx.constant(writeVarName.c_str(), varType);
	return r == w;
}
/**
 * build the formula representing equality to initial value
 */
bool Encode::readFromInitFormula(Event * read, expr& ret) {
	Instruction *I = read->inst->inst;
	const Type * type = I->getType();
	while (type->getTypeID() == Type::PointerTyID) {
		type = type->getPointerElementType();
	}
	const z3::sort varType(llvmTy_to_z3Ty(type));
	expr r = z3_ctx.constant(read->globalVarFullName.c_str(), varType);
	string globalVar = read->varName;
	std::map<std::string, llvm::Constant*>::iterator tempIt =
			trace->useful_global_variable_initializer.find(globalVar);
//	assert(
//			(tempIt != data.global_variable_initializer.end())
//					&& "Wrong with global var!");
//	cerr << "current event: " << read->eventName << "  current globalVar: " << globalVar << "\n";
	if (tempIt == trace->useful_global_variable_initializer.end())
		return false;
	string str = tempIt->first + "_Init";
	expr w = z3_ctx.constant(str.c_str(), varType);
	ret = r == w;
	return true;
}

expr Encode::enumerateOrder(Event * read, Event * write, Event * anotherWrite) {
	expr prev = z3_ctx.int_const(write->eventName.c_str());
	expr back = z3_ctx.int_const(read->eventName.c_str());
	expr another = z3_ctx.int_const(anotherWrite->eventName.c_str());
	expr o = another < prev || another > back;
	return o;
}

void Encode::buildSynchronizeFormula() {
#if FORMULA_DEBUG
	cerr << "\nSynchronizeFormula:\n";
	cerr << "The sum of locks:" << trace->all_lock_unlock.size() << "\n";
#endif

//lock/unlock
	map<string, vector<LockPair *> >::iterator it =
			trace->all_lock_unlock.begin();
	for (; it != trace->all_lock_unlock.end(); it++) {
		vector<LockPair*> tempVec = it->second;
		int size = tempVec.size();
		/////////////////////debug/////////////////////////////
		//print out all the read and write insts of global vars.
		if (false) {
			cerr << it->first << "\n";
			for (int k = 0; k < size; k++) {
				cerr << "#lock#: " << tempVec[k]->lockEvent->eventName;
				cerr << "  #unlock#: " << tempVec[k]->unlockEvent->eventName
						<< "\n";
			}
		}
		/////////////////////debug/////////////////////////////
		for (int i = 0; i < size - 1; i++) {
			expr oneLock = z3_ctx.int_const(
					tempVec[i]->lockEvent->eventName.c_str());
			if (tempVec[i]->unlockEvent == NULL) {		//imcomplete lock pair
				continue;
			}
			expr oneUnlock = z3_ctx.int_const(
					tempVec[i]->unlockEvent->eventName.c_str());
			for (int j = i + 1; j < size; j++) {
				if (tempVec[i]->threadId == tempVec[j]->threadId)
					continue;

				expr twoLock = z3_ctx.int_const(
						tempVec[j]->lockEvent->eventName.c_str());
				expr twinLockPairOrder = z3_ctx.bool_val(1);
				if (tempVec[j]->unlockEvent == NULL) {	//imcomplete lock pair
					twinLockPairOrder = oneUnlock < twoLock;
					//statics
					formulaNum++;
				} else {
					expr twoUnlock = z3_ctx.int_const(
							tempVec[j]->unlockEvent->eventName.c_str());
					twinLockPairOrder = (oneUnlock < twoLock)
							|| (twoUnlock < oneLock);
					//statics
					formulaNum += 2;
				}
				z3_solver.add(twinLockPairOrder);
#if FORMULA_DEBUG
				cerr << twinLockPairOrder << "\n";
#endif
			}
		}
	}

//new method
//wait/signal
#if FORMULA_DEBUG
	cerr << "The sum of wait:" << trace->all_wait.size() << "\n";
	cerr << "The sum of signal:" << trace->all_signal.size() << "\n";
#endif
	map<string, vector<Wait_Lock *> >::iterator it_wait =
			trace->all_wait.begin();
	map<string, vector<Event *> >::iterator it_signal;

	for (; it_wait != trace->all_wait.end(); it_wait++) {
		it_signal = trace->all_signal.find(it_wait->first);
		if (it_signal == trace->all_signal.end())
			assert(0 && "Something wrong with wait/signal data collection!");
		vector<Wait_Lock *> waitSet = it_wait->second;
		string currCond = it_wait->first;
		for (unsigned i = 0; i < waitSet.size(); i++) {
			vector<expr> possibleMap;
			vector<expr> possibleValue;
			expr wait = z3_ctx.int_const(waitSet[i]->wait->eventName.c_str());
			expr lock_wait = z3_ctx.int_const(
					waitSet[i]->lock_by_wait->eventName.c_str());
			vector<Event *> signalSet = it_signal->second;
			for (unsigned j = 0; j < signalSet.size(); j++) {
				if (waitSet[i]->wait->threadId == signalSet[j]->threadId)
					continue;
				expr signal = z3_ctx.int_const(signalSet[j]->eventName.c_str());
				//Event_wait < Event_signal < lock_wait
				expr exprs_0 = wait < signal && signal < lock_wait;

				//m_w_s = 1
				stringstream ss;
				ss << currCond << "_" << waitSet[i]->wait->eventName << "_"
						<< signalSet[j]->eventName;
				expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
				expr exprs_1 = (map_wait_signal == 1);
				//range: p_w_s = 0 or p_w_s = 1
				expr exprs_2 = map_wait_signal >= 0 && map_wait_signal <= 1;

				possibleMap.push_back(exprs_0 && exprs_1);
				possibleValue.push_back(exprs_2);
				//statics
				formulaNum += 3;
			}
			expr one_wait = makeExprsOr(possibleMap);
			expr wait_value = makeExprsAnd(possibleValue);
#if FORMULA_DEBUG
			cerr << one_wait << "\n";
#endif
			z3_solver.add(one_wait);
			z3_solver.add(wait_value);
		}
	}

	//Sigma m_w_s <= 1
	it_signal = trace->all_signal.begin();
	for (; it_signal != trace->all_signal.end(); it_signal++) {
		it_wait = trace->all_wait.find(it_signal->first);
		if (it_wait == trace->all_wait.end())
			continue;
		vector<Event *> signalSet = it_signal->second;
		string currCond = it_signal->first;
		for (unsigned i = 0; i < signalSet.size(); i++) {
			vector<Wait_Lock *> waitSet = it_wait->second;
			string currSignalName = signalSet[i]->eventName;
			vector<expr> mapLabel;
			for (unsigned j = 0; j < waitSet.size(); j++) {
				stringstream ss;
				ss << currCond << "_" << waitSet[j]->wait->eventName << "_"
						<< currSignalName;
				expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
				mapLabel.push_back(map_wait_signal);
			}
			expr sum = makeExprsSum(mapLabel);
			expr relation = (sum <= 1);
			z3_solver.add(relation);
		}
	}

	//Sigma m_s_w >= 1
	it_wait = trace->all_wait.begin();
	for (; it_wait != trace->all_wait.end(); it_wait++) {
		it_signal = trace->all_signal.find(it_wait->first);
		if (it_signal == trace->all_signal.end())
			continue;
		vector<Wait_Lock *> waitSet = it_wait->second;
		string currCond = it_wait->first;
		for (unsigned i = 0; i < waitSet.size(); i++) {
			vector<Event *> signalSet = it_signal->second;
			string currWaitName = waitSet[i]->wait->eventName;
			vector<expr> mapLabel;
			for (unsigned j = 0; j < signalSet.size(); j++) {
				stringstream ss;
				ss << currCond << "_" << currWaitName << "_"
						<< signalSet[j]->eventName;
				expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
				mapLabel.push_back(map_wait_signal);
			}
			expr sum = makeExprsSum(mapLabel);
			expr relation = (sum >= 1);
			z3_solver.add(relation);
		}
	}

	//wipe off the w/s matching in the same thread
	it_wait = trace->all_wait.begin();
	for (; it_wait != trace->all_wait.end(); it_wait++) {
		it_signal = trace->all_signal.find(it_wait->first);
		if (it_signal == trace->all_signal.end())
			continue;
		vector<Wait_Lock *> waitSet = it_wait->second;
		string currCond = it_wait->first;
		for (unsigned i = 0; i < waitSet.size(); i++) {
			vector<Event *> signalSet = it_signal->second;
			string currWaitName = waitSet[i]->wait->eventName;
			unsigned currThreadId = waitSet[i]->wait->threadId;
			for (unsigned j = 0; j < signalSet.size(); j++) {
				if (currThreadId == signalSet[j]->threadId) {
					stringstream ss;
					ss << currCond << "_" << currWaitName << "_"
							<< signalSet[j]->eventName;
					expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
					z3_solver.add(map_wait_signal == 0);
				}
			}
		}
	}

//barrier
#if FORMULA_DEBUG
	cerr << "The sum of barrier:" << trace->all_barrier.size() << "\n";
#endif
	map<string, vector<Event *> >::iterator it_barrier =
			trace->all_barrier.begin();
	for (; it_barrier != trace->all_barrier.end(); it_barrier++) {
		vector<Event *> temp = it_barrier->second;
		for (unsigned i = 0; i < temp.size() - 1; i++) {
			if (temp[i]->threadId == temp[i + 1]->threadId)
				assert(0 && "Two barrier event can't be in a same thread!");
			expr exp1 = z3_ctx.int_const(temp[i]->eventName.c_str());
			expr exp2 = z3_ctx.int_const(temp[i + 1]->eventName.c_str());
			expr relation = (exp1 == exp2);

#if FORMULA_DEBUG
			cerr << relation << "\n";
#endif
			z3_solver.add(relation);
		}
	}
}

expr Encode::makeExprsAnd(vector<expr> exprs) {
	unsigned size = exprs.size();
	if (size == 0)
		return z3_ctx.bool_val(1);
	if (size == 1)
		return exprs[0];
	expr ret = exprs[0];
	for (unsigned i = 1; i < size; i++)
		ret = ret && exprs[i];
	ret.simplify();
	return ret;
}

expr Encode::makeExprsOr(vector<expr> exprs) {
	unsigned size = exprs.size();
	if (size == 0)
		return z3_ctx.bool_val(1);
	if (size == 1)
		return exprs[0];
	expr ret = exprs[0];
	for (unsigned i = 1; i < size; i++)
		ret = ret || exprs[i];
	ret.simplify();
	return ret;
}

expr Encode::makeExprsSum(vector<expr> exprs) {
	unsigned size = exprs.size();
	if (size == 0)
		assert(0 && "Wrong!");
	if (size == 1)
		return exprs[0];
	expr ret = exprs[0];
	for (unsigned i = 1; i < size; i++)
		ret = ret + exprs[i];
	ret.simplify();
	return ret;
}
}

