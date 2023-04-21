import sys
import getopt
import functools
import operator
from queue import Queue
import os
from pathlib import Path
import csv
import re
from openpyxl import Workbook
import shutil
  

       
  
def process_data():
  stats = {}
  stat_con = {}
  times = {}
  kissat_times = {}
  kissat_results = {}
  avoid_ls = [] #["50bit.dimacs", "66bit.dimacs"]
  benchmarks = []
  time_lists = {}
  
          
  original_solve = {'lt10':{} , '10-50':{}}
  pr_solve = {'lt10':{} , '10-50':{}}
  for bench_set in ["lt10", "10-50"] :
    with open(bench_set+".csv", mode='r') as csvFile:
        csvReader = csv.DictReader(csvFile)
        for line in csvReader:
          temp_b = line["bench"]
          pr_solve[bench_set][temp_b] = line
          original_solve[bench_set][temp_b] = {}
          original_solve[bench_set][temp_b]["solve time"] = line["default-kissat-time"]
          original_solve[bench_set][temp_b]["result"] = line["default-kissat-result"]
        
  inproc_data = {}
  with open("inprocessing.csv", mode='r') as csvFile:
    csvReader = csv.DictReader(csvFile)
    for line in csvReader:
      c = line["\ufeffconfig"]
      if c not in inproc_data: inproc_data[c] = {}
      b = line["bench"]
      inproc_data[c][b] = line
      
  perm_var_data = {}
  with open("variable-permuting.csv", mode='r') as csvFile:
    csvReader = csv.DictReader(csvFile)
    for line in csvReader:
      b = line["\ufeffbench"]
      perm_var_data[b] = line
  
  
  lt10_benches =pr_solve['lt10'].keys()
  gt10_benches =pr_solve['10-50'].keys()
  
  tables = True
  if tables:
    '''
    Table 2
    '''
    print("TABLE 2")
    print("Set | Benches | Avg (s) | Generated Reducts | Satisfiable Reducts | Percent Satisfiable | Failed Literals")
    for bench_set in ["lt10", "10-50"] :
      hasPR = 0
      total_time = 0
      generated_reducts = 0
      sat_reducts = 0
      failed_literals = 0
      for b in pr_solve[bench_set].keys():
        d = pr_solve[bench_set][b]
        if (int(d['pr-binaries']) + int(d['pr-units'])) > 0: hasPR += 1
        total_time += float(d['pr-time'])
        generated_reducts += int(d['generated'])
        sat_reducts += int(d['satisfied'])
        failed_literals += int(d['units'])
      print("{} {}/{} {} {} {} {} {} ".format(bench_set, hasPR,len(pr_solve[bench_set].keys()) ,round(total_time/len(pr_solve[bench_set].keys()), 2), generated_reducts, sat_reducts, round(sat_reducts/generated_reducts,4),failed_literals))
      
    '''
    Table 3
    '''
    print("TABLE 3")
    print("Set | Type |  Total w | Total w/o | Exclusively w | Exclusively w/o | Improved w | Improved w/o")
    for bench_set in ["lt10", "10-50"] :
      TotalWithPR = [0,0]
      TotalWithoutPR = [0,0]
      ExclWithPR = [0,0]
      ExclWithoutPR = [0,0]
      Improved = [0,0]
      Worsened = [0,0]
      for b in pr_solve[bench_set].keys():
        d = pr_solve[bench_set][b]
        d_orig = original_solve[bench_set][b]
        
        res = -1
        if d_orig["result"] == "SAT-VERIFIED" or d["solve-result"] == "SAT-VERIFIED":
          res = 0
        if d_orig["result"] == "UNSAT" or d["solve-result"] == "UNSAT":
          if res == 0: print("ERROR DUAL RESULTS")
          res = 1
      
        if d_orig["result"] != "UNKNOWN":
          TotalWithoutPR[res] += 1
          if d["solve-result"] == "UNKNOWN":
            ExclWithoutPR[res] += 1
        if d["solve-result"] != "UNKNOWN":
          TotalWithPR[res] += 1
          result_pr = 1
          if d_orig["result"] == "UNKNOWN":
            ExclWithPR[res] += 1
      
        if res >= 0:
          diff = float(d_orig["solve time"]) - float(d["total-time"])
          if diff >= 1 and max(float(d["total-time"]),float(d_orig["solve time"])) / min(float(d["total-time"]),float(d_orig["solve time"])) >= 1.01   :
            Improved[res] += 1
        if res >= 0:
          diff =  float(d["total-time"]) - float(d_orig["solve time"])
          if diff >= 1 and max(float(d["total-time"]),float(d_orig["solve time"])) / min(float(d["total-time"]),float(d_orig["solve time"])) >= 1.01   :
            Worsened[res] += 1
      
        
      for i in range(2):
        if i == 0: type = "SAT"
        else : type = "UNSAT"
        print("{} {} {} {} {} {} {} {} ".format(bench_set, type, TotalWithPR[i],TotalWithoutPR[i],ExclWithPR[i],ExclWithoutPR[i],Improved[i],Worsened[i]))
      
      
  colors = ["blue","redpurple","midgreen","mildgray","clearyellow","darkestblue", "browngreen","redpurple","black","darkred", "midgreen", "midgreen"]
  marks = ["diamond","","triangle", "square","square"]
  figure7 = True
  if figure7:
    '''
    FIGURE 7
    '''
    print("FIGURE 7")
    for bench_set in ["lt10", "10-50"] :
      print("{} tikz plot".format(bench_set))
      for b in pr_solve[bench_set].keys():
        d = pr_solve[bench_set][b]
        d_orig = original_solve[bench_set][b]
    
        res = -1
        if d_orig["result"] == "SAT-VERIFIED" or d["solve-result"] == "SAT-VERIFIED":
          res = 0
        if d_orig["result"] == "UNSAT" or d["solve-result"] == "UNSAT":
          if res == 0: print("ERROR DUAL RESULTS")
          res = 1
          
        result_pr = False
        if d["solve-result"] != "UNKNOWN" : result_pr = True
        
        truth_value = res
        origTime = float(d_orig["solve time"])
        solveTime = float(d["total-time"])
        prTime = float(d["pr-time"])
        truth_value = res
        if truth_value == -1: continue
        if solveTime < 1:
          solveTime = 1
        if origTime < 1 : origTime = 1
        plot = "\\addplot[color="+colors[truth_value]+",mark="+marks[truth_value]+"*] coordinates { "
        plot += "("+str(solveTime) + "," + str(origTime) + ") "
        if solveTime <= 5000 and result_pr > 0:
          plot += "("+str(solveTime-prTime) + "," + str(origTime) + ") "
        plot += " };"

        print(plot)
    

  
  figure8 = True
  if figure8:
    '''
    FIGURE 8
    '''
    print("FIGURE 8")
    cnt = 0
    for con in inproc_data.keys():
      print(con)
      solved=0
      times = []
      for b in pr_solve["lt10"].keys():
        p = inproc_data[con][b]
        if p["solve-result"] == "UNKNOWN":
          if float(p["total-time"]) < 5000: print("BAD TIME")
          times.append(5000)
        else:
          if p['inproc-solved'] != 'True' :
            times.append(float(p["total-time"]))
          else: # solved in inprocessing
            if con == "default_PR_inproc.sh" or con == "default_PR_inproc_PR.sh" :
              times.append(float(p["inproc-time"])+float(p["pr-time"]))
            elif con == "default_inproc_PR.sh" :
              times.append(float(p["inproc-time"]))
            elif con == "default_inproc.sh" :
              times.append(float(p["inproc-time"]))
          
          solved += 1

      times.sort()
      plot = "\\addplot[color="+colors[cnt]+",mark="+marks[0]+"*] coordinates { "
      plot += "(0,0) "
      slved = 1
      for t in times:
        if t >= 5000:
          plot += "( 5500," + str(slved-1) + ") "
          break
        plot += "("+str(t) + "," + str(slved) + ") "
        slved += 1
      plot += " };"
      cnt += 1
      print(plot)
#      print(slved)
      
    solved = 0
    times = []
    for b in pr_solve["lt10"].keys():
      p = pr_solve["lt10"][b]
      if p["solve-result"] == "UNKNOWN":
        if float(p["total-time"]) < 5000: print("BAD TIME")
        times.append(5000)
      else:
        times.append(float(p["total-time"]))
        solved += 1

    times.sort()
    plot = "\\addplot[color="+colors[cnt]+",mark=+] coordinates { "
    plot += "(0,0) "
    slved = 1
    for t in times:
      if t >= 5000:
        plot += "( 5500," + str(slved-1) + ") "
        break
      plot += "("+str(t) + "," + str(slved) + ") "
      slved += 1
    plot += " };"
    cnt += 1
    print(plot)
#    print(slved)
  
  
  figure9 = True
  if figure9:
    '''
    FIGURE 9
    '''
    print("FIGURE 9")
    plot1 = []
    plot2 = []
    for b in pr_solve["lt10"].keys():
      d = pr_solve["lt10"][b]
      p = inproc_data['default_inproc_PR.sh'][b]
      
      res = -1
      if p["solve-result"] == "SAT-VERIFIED" or d["solve-result"] == "SAT-VERIFIED":
        res = 0
      if p["solve-result"] == "UNSAT" or d["solve-result"] == "UNSAT":
        if res == 0: print("ERROR DUAL RESULTS")
        res = 1
      
      truth_value = res
      solvePR = int(p["satisfied"])
      origPR = int(d["satisfied"])
      if solvePR < 1 : solvePR = 0.9
      if origPR < 1 : origPR = 0.9
      if solvePR >= 1 or origPR >= 1:
        if p['inproc-solved'] != 'True' :
          plot = "\\addplot[color="+colors[truth_value]+",mark="+marks[truth_value]+"*] coordinates { "
          plot += "("+str(solvePR) + "," + str(origPR) + ") "
          plot += " };"
          plot1.append(plot)
      
      
      solveTime = float(p["total-time"])
      
      if p['inproc-solved'] == 'True' :
        solveTime = float(p['inproc-time'])
      origTime = float(d["total-time"])
      if truth_value == -1: continue
      if solveTime < 1:
        solveTime = 1
      if origTime < 1 : origTime = 1
      plot = "\\addplot[color="+colors[truth_value]+",mark="+marks[truth_value]+"*] coordinates { "
      plot += "("+str(solveTime) + "," + str(origTime) + ") "
      plot += " };"
      plot2.append(plot)
      
    print("PR clauses tikz plot")
    for s in plot1: print(s)
    print("Solve times tikz plot")
    for s in plot2: print(s)
      
  
  figure10 = True
  if figure10:
    '''
    FIGURE 10
    '''
    print("FIGURE 10")
    plot1 = []
    plot2 = []
    for b in pr_solve["lt10"].keys():
      d = pr_solve["lt10"][b]
      p = perm_var_data[b]
      
      res = -1
      if p["solve-result"] == "SAT-VERIFIED" or d["solve-result"] == "SAT-VERIFIED":
        res = 0
      if p["solve-result"] == "UNSAT" or d["solve-result"] == "UNSAT":
        if res == 0: print("ERROR DUAL RESULTS")
        res = 1
      
      truth_value = res
      solvePR = int(p["satisfied"])
      origPR = int(d["satisfied"])
      if solvePR < 1 : solvePR = 0.9
      if origPR < 1 : origPR = 0.9
      if solvePR >= 1 or origPR >= 1:
        plot = "\\addplot[color="+colors[truth_value]+",mark="+marks[truth_value]+"*] coordinates { "
        plot += "("+str(solvePR) + "," + str(origPR) + ") "
        plot += " };"
        plot1.append(plot)
      
      
      solveTime = float(p["total-time"])
      origTime = float(d["total-time"])
      if truth_value == -1: continue
      if solveTime < 1:
        solveTime = 1
      if origTime < 1 : origTime = 1
      plot = "\\addplot[color="+colors[truth_value]+",mark="+marks[truth_value]+"*] coordinates { "
      plot += "("+str(solveTime) + "," + str(origTime) + ") "
      plot += " };"
      plot2.append(plot)
      
    print("PR clauses tikz plot")
    for s in plot1: print(s)
    print("Solve times tikz plot")
    for s in plot2: print(s)
      
      

  
def run(name, args):
    
    process_data()
        

if __name__ == "__main__":
    run(sys.argv[0], sys.argv[1:])
