
from pyabc import *
import pyabc_split
import redirect
import sys
import os
import time
import math
import filecmp
import random
import operator
import pyaig

### this will set up things to simulate the 4 core hwmcc'15 competition.
##import affinity
##affinity.sched_setaffinity(os.getpid(), [0, 2, 4, 6])

try:
    import regression
except:
    pass
    
global G_C,G_T,latches_before_abs,latches_before_pba,n_pos_before,x_factor,methods,last_winner
global last_cex,JV,JP, cex_list,max_bmc, last_cx, pord_on, trim_allowed, temp_dec, abs_ratio, ifbip
global if_no_bip, gabs, gla, sec_options,last_gasp_time, abs_ref_time, bmcs1, total_spec_refine_time
global last_gap

"""
The functions that are currently available from module _abc are:

int n_ands();
int n_pis();
int n_pos();
int n_latches();
int n_bmc_frames();
int prob_status(); 1 = unsat, 0 = sat, -1 = unsolved
int cex_get()
int cex_put()
int run_commandhar* cmd);
int n_nodes();
int n_levels();

bool has_comb_model();
bool has_seq_model();
bool is_true_cex();
bool is_valid_cex();
  return 1 if the number of PIs in the current network and in the current counter-example are equal
int  n_cex_pis();
  return the number of PIs in the current counter-example
int  n_cex_regs();
  return the number of flops in the current counter-example
int  cex_po();
  returns the zero-based output PO number that is SAT by cex
int  cex_frame();
  return the zero-based frame number where the outputs is SAT
The last four APIs return -1, if the counter-example is not defined. 
""" 
#global variables
#________________________________________________
stackno_gabs = stackno_gore = stackno_greg= 0
STATUS_UNKNOWN = -1
STATUS_SAT = 0
STATUS_UNSAT = 1
RESULT = ('SAT', 'SAT', 'UNSAT', 'UNDECIDED', 'UNDECIDED', 'ERROR')
Sat = Sat_reg = 0
Sat_true = 1
Unsat = 2
Undecided = Undecided_reduction = 3
Undecided_no_reduction = 4
Error = 5
Restart = 6
xfi = x_factor = 1  #set this to higher for larger problems or if you want to try harder during abstraction
max_bmc = -1
last_time = 0
j_last = 0
seed = 113
init_simp = 1
temp_dec = True
ifpord1 = 1
K_backup = init_time = 0
last_verify_time = 20
last_cex = last_winner = 'None'
last_cx = 0
trim_allowed = True
pord_on = False
sec_sw = False
sec_options = ''
pairs = cex_list = []
TERM = 'USL'
##last_gasp_time = 10000 -- controls BMC_VER_result time limit
##last_gasp_time = 500
last_gasp_time = 1500 #set to conform to hwmcc15 for 1 hours
use_pms = True

#gabs = False #use the gate refinement method after vta
#abs_time = 100

####################################
#default abstraction methods
gabs = False #False = use gla refinement, True = use reg refinement.
gla = True #use gla_abs instead of vta_abs
##abs_time = 10000 #number of sec before initial abstraction terminates.
abs_time = 150
abs_time = 5000
abs_time = 500
abs_time = 200 #changed for hwmcc15
abs_time = 1000 #changed for hwmcc17
abs_ref_time = 50 #number of sec. allowed for abstraction refinement.
##total_spec_refine_time = 150
total_spec_refine_time = 200 # changed for hwmcc15
ifbip = 0 # sets the abtraction method to vta or gla, If = 1 then uses ,abs
if_no_bip = False #True sets it up so it can't use bip and reachx commands.
abs_ratio = .6 #this controls when abstraction is too big and gives up
abs_ratio = .80 
#####################################

############## No bip Settings ########################
##abs_time = 500  #number of sec before initial abstraction terminates.
##abs_ref_time = 1000 #number of sec. allowed for abstraction refinement.
##if_no_bip = True #True sets it up so it can't use bip and reachx commands.
#######################################


def abstr_a(t1=200,t2=200,absr=0):
    global abs_time, abs_ref_time, abs_ratio
    if not absr == 0:
        abs_ratio_old = abs_ratio
        abs_ratio = absr
    abs_time = t1
    abs_ref_time = t2
    abstracta(False)
    if not absr == 0:
        abs_ratio = abs_ratio_old

t_init = 2 #initial time for poor man's concurrency.

def set_global(s=''):
    global G_C,G_T,latches_before_abs,latches_before_pba,n_pos_before,x_factor,methods,last_winner
    global last_cex,JV,JP, cex_list,max_bmc, last_cx, pord_on, trim_allowed, temp_dec, abs_ratio, ifbip
    global if_no_bip, gabs, gla, sec_options,last_gasp_time,abs_ref_time, abs_time,use_pms, engines
    exec(s)


methods = ['PDR', 'INTRP', 'BMCe', 'SIM', 'REACHX',
           'PRE_SIMP', 'simple', 'PDRM', 'REACHM', 'BMC3','Min_Retime',
           'For_Retime','REACHP','REACHN','PDR_sd','prove_part_2',
           'prove_part_3','verify','sleep','PDRM_sd','prove_part_1',
           'run_parallel','INTRPb', 'INTRPm', 'REACHY', 'REACHYc','RareSim','simplify', 'speculate',
           'quick_sec', 'BMC_J', 'BMC2', 'extract -a', 'extract', 'PDRa', 'par_scorr', 'dsat',
           'iprove','BMC_J2','splitprove','pdrm_exact', 'AVY', 'PDRae', 'PDRMnc', 'PDRMyuf',
           'PDRMnct', 'BMCsp', 'BMC3s' ]
engines = ['PDR', 'INTRP', 'BMCe', 'SIM', 'REACHX',
           'PDRM', 'REACHM', 'BMC3',
           'REACHP','REACHN','PDR_sd',
           'PDRM_sd',
           'INTRPb', 'INTRPm', 'REACHY', 'REACHYc','RareSim',
           'BMC_J', 'BMC2', 'PDRa',  'dsat',
           'iprove','BMC_J2','pdrm_exact', 'AVY', 'PDRae', 'PDRMnc', 'PDRMyuf',
           'PDRMnct' , 'bmc_jump', 'BMCsp', 'BMC3s']

#'0.PDR', '1.INTERPOLATION', '2.BMCe', '3.SIMULATION',
#'4.REACHX', '5.PRE_SIMP', '6.simple', '7.PDRM', '8.REACHM', 9.BMC3'
# 10. Min_ret, 11. For_ret, 12. REACHP, 13. REACHN 14. PDRseed 15.prove_part_2,
#16.prove_part_3, 17.verify, 18.sleep, 19.PDRMm, 20.prove_part_1,
#21.run_parallel, 22.INTRP_bwd, 23. Interp_m 24. REACHY 25. REACHYc 26. Rarity Sim 27. simplify
#28. speculate, 29. quick_sec, 30 bmc3 -S, 31. BMC2 32. extract -a
#33. extract 34. pdr_abstract
#35 par_scorr, 36. dsat, 37. iprove 38. BMC_J2 39. splitprove 40. pdrm_exact
#41. AVY, 42. PDRae, 43. pdr -nc, 44. pdr -yuf, 45. pdrm -nct, 46 BMCsp, 47. BMC3s
win_list = [(0,.1),(1,.1),(2,.1),(3,.1),(4,.1),(5,-1),(6,-1),(7,.1)]
FUNCS = ["(pyabc_split.defer(pdr)(t))",
##         "(pyabc_split.defer(abc)('&get;,pdr -vt=%f'%t))",
         "(pyabc_split.defer(intrp)(t))",
##         "(pyabc_split.defer(abc)('&get;,imc -vt=%f'%(t)))",
##         "(pyabc_split.defer(abc)('&get;,imc-sofa -vt=%f'%(t)))",
         "(pyabc_split.defer(bmce)(t))", #rkb  -40 istemp change for hwmcc14 depth bound competition
##         "(pyabc_split.defer(abc)('&get;,bmc -vt=%f'%t))",
         "(pyabc_split.defer(simulate)(t))",
         "(pyabc_split.defer(reachx)(t))",
##         "(pyabc_split.defer(abc)('reachx -t %d'%t))",
         "(pyabc_split.defer(pre_simp)())",
##         "(pyabc_split.defer(super_prove)(2))",
         "(pyabc_split.defer(simple)(t))",
         "(pyabc_split.defer(pdrm)(t))",
         "(pyabc_split.defer(abc)('&get;&reachm -vcs -T %d'%t))",
         "(pyabc_split.defer(bmc3)(t))",
##         "(pyabc_split.defer(abc)('bmc3 -C 1000000 -T %f'%t))",
         "(pyabc_split.defer(abc)('dretime;&get;&lcorr;&dc2;&scorr;&put;dretime'))",
         "(pyabc_split.defer(abc)('dretime -m;&get;&lcorr;&dc2;&scorr;&put;dretime'))",
         "(pyabc_split.defer(abc)('&get;&reachp -vr -T %d'%t))",
         "(pyabc_split.defer(abc)('&get;&reachn -vr -T %d'%t))",
##         "(pyabc_split.defer(abc)('&get;,pdr -vt=%f -seed=521'%t))",
         "(pyabc_split.defer(pdrseed)(t))",
         "(pyabc_split.defer(prove_part_2)())",
         "(pyabc_split.defer(prove_part_3)())",
         "(pyabc_split.defer(verify)(JV,t))",
         "(pyabc_split.defer(sleep)(t))",
         "(pyabc_split.defer(pdrmm)(t))",
         "(pyabc_split.defer(prove_part_1)())",
         "(pyabc_split.defer(run_parallel)(JP,t,'TERM'))",
         "(pyabc_split.defer(abc)('&get;,imc -bwd -vt=%f'%t))",
##         "(pyabc_split.defer(abc)('int -C 1000000 -F 10000 -K 2 -T %f'%t))",
         "(pyabc_split.defer(intrpm)(t))",
##         "(pyabc_split.defer(abc)('int -C 1000000 -F 10000 -K 1 -T %f'%t))",
         "(pyabc_split.defer(reachy)(t))",
##         "(pyabc_split.defer(abc)('&get;&reachy -v -T %d'%t))",
         "(pyabc_split.defer(abc)('&get;&reachy -cv -T %d'%t))",
##         does rarity simulation 
         "(pyabc_split.defer(simulate2)(t))",
         "(pyabc_split.defer(simplify)())",
         "(pyabc_split.defer(speculate)())",
         "(pyabc_split.defer(quick_sec)(t))",
         "(pyabc_split.defer(bmc_j)(t))",
##         "(pyabc_split.defer(abc)('bmc2 -C 1000000 -T %f'%t))",
         "(pyabc_split.defer(bmc2)(t))",
         "(pyabc_split.defer(extractax)('a'))",
         "(pyabc_split.defer(extractax)())",
         "(pyabc_split.defer(pdra)(t))",
         "(pyabc_split.defer(pscorr)(t))",
         "(pyabc_split.defer(dsat)(t))",
         "(pyabc_split.defer(iprove)(t))",
         "(pyabc_split.defer(bmc_j2)(t))",
         "(pyabc_split.defer(splitprove)(t))",
         "(pyabc_split.defer(pdrm_exact)(t))",
         "(pyabc_split.defer(avy)(t))",
         "(pyabc_split.defer(pdrae)(t))",
##         "(pyabc_split.defer(bmc_par_jmps)(t))"
         "(pyabc_split.defer(pdrmnc)(t))",
         "(pyabc_split.defer(pdrmyuf)(t))",
         "(pyabc_split.defer(pdrmnct)(t))",
         "(pyabc_split.defer(BMCsp)(t))",
         "(pyabc_split.defer(bmc3s)(t))"
          ]
##         "(pyabc_split.defer(abc)('bmc3 -C 1000000 -T %f -S %d'%(t,int(1.5*max_bmc))))"
#note: interp given 1/2 the time.

## Similar engines below listed in the order of priority, high to low.
allreachs = [8,12,13,24,25]
allreachs = [24]
reachs = [24]
##allpdrs = [14,7,34,19,0]
#allpdrs = [34,7,14,0,42,43,44,45]
pdrs = allpdrs = [34,43,45,7,0]
bmcs1 = [9]
bmcs = allbmcs = [46,47,2,9,38]
exbmcs = exactbmcs = [9,2,31,46,47]
##exbmcs = [2,9,31]
##bmcs = [9,30,2,38]

#added AVY as a new interpolation method
#no AVY = 41 for hwmcc15
##allintrps = [41,23,1,22]
allintrps = [23,1,22]
##bestintrps = [41,23]
bestintrps = [23]
intrps = [23,1]
##intrps = [41,23,1] #putting ,imc-sofa first for now to test
##intrps = [41,23] #rkb
# done adding AVY

allsims = [26,3]
sims = [26] 
allslps = [18]
slps = [18]
pre = [5]
combs = [36,37,39]

JV = pdrs+intrps+bmcs+sims #sets what is run in parallel '17. verify' above
JP = JV + [27] # sets what is run in  '21. run_parallel' above 27 simplify should be last because it can't time out.
#_____________________________________________________________


# Function definitions:
# simple functions: ________________________________________________________________________
# set_globals, abc, q, x, has_any_model, is_sat, is_unsat, push, pop

# ALIASES

def initialize():
    global xfi, max_bmc, last_time,j_last, seed, init_simp, K_backup, last_verify_time
    global init_time, last_cex, last_winner, trim_allowed, t_init, sec_options, sec_sw
    global n_pos_before, n_pos_proved, last_cx, pord_on, temp_dec, abs_time, gabs, gla,m_trace
    global smp_trace,hist,init_initial_f_name, skip_spec, t_iter_start,last_simp, final_all, scorr_T_done
    global last_gap, last_gasp_time, max_pos,pairs
    xfi = x_factor = 1  #set this to higher for larger problems or if you want to try harder during abstraction
    max_bmc = -1
    last_time = 0
##    last_gasp_time = 2001 #set to conform to hwmcc12
    last_gasp_time = 1500 #set to conform to hwmcc15
    last_gasp_time = 3600 #set to 1 hour
    j_last = 0
    seed = 113
    init_simp = 1
    temp_dec = True
    K_backup = init_time = 0
    last_verify_time = 20
    last_cex = last_winner = 'None'
    last_cx = 0
    trim_allowed = True
    pord_on = False
    t_init = 2 #this will start sweep time in find_cex_par to 2*t_init here
    sec_sw = False
    sec_options = ''
    smp_trace = m_trace = []
    cex_list = []
    n_pos_before = n_pos()
    n_pos_proved = 0
##    if n_ands() > 100000:
##        abs_time = 300
##    else:
##        abs_time = 150 #timeout for abstraction
    abs_time = 100000 #let size terminate this.
    abs_time = 500
    abs_time = 150
    abs_time = 200 #for hwmcc15
    abs_time = 1000 #for hwmcc17 examples
    abs_ref_time = 50 #number of sec. allowed for abstraction refinement.
##    total_spec_refine_time = 150 # timeout for speculation refinement
    total_spec_refine_time = 200 # timeout for speculation refinement changed for hwmcc15
    abs_ratio = .5 
##    hist = []
    skip_spec = False
    t_iter_start = 0
    inf = 10000000
    last_simp = [inf,inf,inf,inf]
    final_all = 1
    final_all = 0
    scorr_T_done = 0
    last_gap = 50
    max_pos = 1000
    pairs = []
##    abs_time = 100
##    gabs = False
##    abs_time = 500
##    gabs = True

def set_abs_method():
    """ controls the way we do abstraction, 0 = no bip, 1 = old way, 2 use new bip and -dwr
    see absab()
    """
    global ifbip, abs_time,gabs,gla,if_no_bip
    print 'current values ifbip = %d, abs_time = %d'%(ifbip,abs_time)
    print 'Set method of abstraction: \n0 = vta for 500 and gla refin., \n1 = old way, \n2 = ,abs and -dwr, \n3 = vta for 100 followed by gla refine.,\n4 = vta for 500 then gla refine. but no bip methods gla refine., \n5 = gla and gla refine.'
    s = raw_input()
    s = remove_spaces(s)
    if s == '1': #use the old way with ,abs but no dwr
        ifbip = 1 #old way
        abs_time = 100
        if_no_bip = False
        gabs = True
        gla = False
    elif s == '0':#use vta and gla refinement
        ifbip = 0 
        abs_time = 500
        if_no_bip = False
        gabs = False
        gla = False
    elif s == '2':  #use ,abc -dwr
        ifbip = 2 
        abs_time = 100
        if_no_bip = False
        gabs = True #use register refinement
        gla = False
    elif s == '3': #use vta and gla refinement
        ifbip = 0
        abs_time = 100
        if_no_bip = False
        gabs = False
        gla = False
    elif s == '4': #use vta, gla refine. and no bip
        ifbip = 0
        abs_time = 100
        if_no_bip = True
        gabs = True
        gla = False
    elif s == '5': #use gla and gla_refinement
        ifbip = 0
        abs_time = 100
        if_no_bip = False
        gabs = False
        gla = True
    #should make any of the methods able to us no bip
    print 'ifbip = %d, abs_time = %d, gabs = %d, if_no_bip = %d, gla = %d'%(ifbip,abs_time,gabs,if_no_bip,gla)
    
def ps():
    out = print_circuit_stats()
    return out

def iprove(t=100):
    abc('iprove')

def dsat(t=100):
    abc('dsat')

def splitprove(t=900):
    abc('&get;&splitprove -v -P 30 -L 5 -T 15')

def n_real_inputs():
    """This gives the number of 'real' inputs. This is determined by trimming away inputs that
    have no connection to the logic. This is done by the ABC alias 'trm', which changes the current
    circuit. In some applications we do not want to change the circuit, but just to know how may inputs
    would go away if we did this. So the current circuit is saved and then restored afterwards."""
##    abc('w %s_savetempreal.aig; logic; trim; st ;addpi'%f_name)
    abc('w %s_savetempreal.aig'%f_name)
    with redirect.redirect( redirect.null_file, sys.stdout ):
##        with redirect.redirect( redirect.null_file, sys.stderr ):
        reparam()
    n = n_pis()
    abc('r %s_savetempreal.aig'%f_name)
    return n

def timer(t):
    btime = time.clock()
    time.sleep(t)
    print t
    return time.clock() - btime

def sleep(t):
##    print 'Sleep time = %d'%t
    time.sleep(t)
    return Undecided
        
def abc(cmd):
    """ executes an ABC command and represses all outputs"""
    abc_redirect_all(cmd)

def xa(cmd):
    """ executes an ABC command and shows all outputs"""
    return run_command( cmd )

def abc_redirect( cmd, dst = redirect.null_file, src = sys.stdout ):
    """This is our main way of calling an ABC function. Redirect, means that we suppress any output from ABC"""
    with redirect.redirect( dst, src ):
        return run_command( cmd )

def abc_redirect_all( cmd ):
    """This is our main way of calling an ABC function. Redirect, means that we suppress any output from ABC, including error printouts"""
    with redirect.redirect( redirect.null_file, sys.stdout ):
        with redirect.redirect( redirect.null_file, sys.stderr ):
            return run_command( cmd )

##def convert(t):
##    t = int(t*100)
##    return str(float(t)/100)

def set_engines(N=0):
    """
    Called only when read_file is called.
    Sets the MC engines that are used in verification according to
    if there are 4 or 8 processors. if if_no_bip = 1, we will not use any bip and reachx engines
    """
    global reachs,pdrs,sims,intrps,bmcs,n_proc,abs_ratio,ifbip,bmcs1, if_no_bip, allpdrs,allbmcs
    bmcs1 = [9] #BMC3
    #for HWMCC we want to set N = 
    if N == 0:
        N = n_proc = os.sysconf(os.sysconf_names["SC_NPROCESSORS_ONLN"])
##        N = 4 # this was for hwmcc15
        N = n_proc = 2*N
##        N = n_proc = 8 ### simulate 4 processors for HWMCC - turn this off a hwmcc.
    else:
        n_proc = N
##    print 'n_proc = %d'%n_proc
    #strategy is to use 2x number of processors 
    if N <= 1:
        reachs = [24]
        pdrs = [7]
##        bmcs = [30]
        bmcs = [9]
        intrps = []
        sims = []
        slps = [18]
    elif N <= 2:
        reachs = [24]
        pdrs = [7]
        bmcs = [46,47]
        intrps = []
        sims = []
        slps = [18]
    elif N <= 4: #this will be the operative one for hwmcc'15
        reachs = [24] #reachy
        pdrs = [7,34] #prdm pdr_abstract
        if if_no_bip:
            allpdrs = pdrs = [7,19] #pdrm pdrmm
        bmcs = [46,47,2] #bmc3 bmc3 -S
        intrps = [23] #interp_m
        sims = [26] #Rarity_sim
        slps = [18] #sleep
# 0.PDR, 1.INTERPOLATION, 2.BMC, 3.SIMULATION,
# 4.REACHX, 5.PRE_SIMP, 6.simple, 7.PDRM, 8.REACHM, 9.BMC3
# 10.Min_ret, 11.For_ret, 12.REACHP, 13.REACHN 14.PDRseed 15.prove_part_2,
# 16.prove_part_3, 17.verify, 18.sleep, 19.PDRMm, 20.prove_part_1,
# 21.run_parallel, 22.INTRP_bwd, 23.Interp_m 24.REACHY 25.REACHYc 26.Rarity Sim 27.simplify
# 28.speculate, 29.quick_sec, 30.bmc3 -S, 31.BMC2 32.extract -a 33.extract 34.pdr_abstract
# 35.par_scorr, 36.dsat, 37.iprove

# BIPS = 0.PDR, 1.INTERPOLATION, 2.BMC, 14.PDRseed, 22.INTRP_bwd, 34.pdr_abstract
#       also  reparam which uses ,reparam 

    elif N <= 8: #used for HWMCC'15
        reachs = [24] #REACHY
        allpdrs = pdrs = [7,34,14] #PDRM pdr_abstract PDR_seed
##        intrps = [41,23,1] #Interp_m
        intrps = [23] #rkb
        allbmcs = bmcs = [46,47,9,2] #BMC3 bmc3 -S BMC 
        if if_no_bip:
            allpdrs = pdrs = [7,19] #PDRM PDRMm
            intrps = allintrps = [41,23] #Interp_m
            bmcs = allbmcs = [46,47,9,38]
        sims = [26] #Rarity_Sim
        slps = [18] #sleep
    else:
        reachs = [24] #REACHY REACHX
        pdrs = allpdrs
##        pdrs = [7,34,14,19,0] #PDRM pdr_abstract PDR_seed PDRMm PDR
##        pdrs = allpdrs =[7,34,14]
##        intrps = [41,23,1] #Interp_m INTERPOLATION
##        intrps = [41,23] #rkb
        intrps = [23,1] #Interp_m INTERPOLATION
        intrps = [23] #rkb
        bmcs = allbmcs   #allbmcs = [9,30,2,31,38,46,47]
        if if_no_bip:
            allpdrs = pdrs = [7,19] #PDRM PDRMm
            intrps = allintrps = [41,23] #Interp_m
            reachs = [24] #REACHY
            bmcs = [46,47,9,38] 
        sims = [26] #Rarity_Sim
        slps = [18] #sleep
    print 'No. engines = %d,%d '%(N,n_proc)
    print 'pdrs = %s'%str(pdrs)
    print 'bmcs = %s'%str(bmcs)
        
def set_globals():
    """This sets global parameters that are used to limit the resources used by all the operations
    bmc, interpolation BDDs, abstract etc. There is a global factor 'x_factor' that can
    control all of the various resource limiting parameters"""
    global G_C,G_T,x_factor
    nl=n_latches()
    na=n_ands()
    np = n_pis()
    #G_C = min(500000,(3*na+500*(nl+np)))
    G_C = x_factor * min(100000,(3*na+500*(nl+np)))
    #G_T = min(250,G_C/2000)
    G_T = x_factor * min(75,G_C/2000)
    G_T = max(1,G_T)
    #print('Global values: BMC conflicts = %d, Max time = %d sec.'%(G_C,G_T))
    
def a():
    """this puts the system into direct abc input mode"""
    print "Entering ABC direct-input mode. Type q to quit ABC-mode"
    n = 0
    while True:
        print '     abc %d> '%n,
        n = n+1
        s = raw_input()
        if s == "q":
            break
        run_command(s)

def remove_spaces(s):
    y = ''
    for t in s:
        if not t == ' ':
            y = y + t
    return y

def seq_name(f):
    names = []
    f = f + '_'
    names = []
    while len(f)>0:
        j = f.find('_')
        if j == -1:
            break
        names = names + [f[:j]]
##        print names
        f = f[j+1:]
##        print f
    return names

def revert(f,n):
    l = seq_name(f)
    for j in range(n):
        if len(l)>0:
            l.pop()
    name = construct(l)
    return name

def n_eff_pos():
    N=n_pos()
    l=len(list_0_pos())
    return N-l

def construct(l):
    ll = l
    name = ''
    while len(l)>0:
        name = '_'+ll.pop()+name
    return name[1:]

def process_sat():
    l = seq_name(f_name)

def add_trace(s):
    global m_trace
    m_trace = m_trace + [s] 

def read_file_quiet_i(fname=None):
    """ this preserves t_inter_start and is called internally by some functons."""
    global t_iter_start
    ts = t_iter_start
    read_file_quiet(fname)
    t_iter_start = ts

def read_file_quiet(fname=None):
    """This is the main program used for reading in a new circuit. The global file name is stored (f_name)
    Sometimes we want to know the initial starting name. The file name can have the .aig extension left off
    and it will assume that the .aig extension is implied. This should not be used for .blif files.
    Any time we want to process a new circuit, we should use this since otherwise we would not have the
    correct f_name."""
    global max_bmc,  f_name, d_name, initial_f_name, x_factor, init_initial_f_name, win_list,seed, sec_options
    global win_list, init_simp, po_map, aigs, hist, init_initial_f_name
    abc('fraig_restore') #clear out any residual fraig_store
    set_engines() #temporary
    init_simp = 1
    win_list = [(0,.1),(1,.1),(2,.1),(3,.1),(4,.1),(5,-1),(6,-1),(7,.1)] #initialize winning engine list
    po_map = range(n_pos())
    initialize()
##    x_factor = 1
##    seed = 223
##    max_bmc = -1
    if fname is None:
        print 'Type in the name of the aig file to be read in'
        s = raw_input()
        s = remove_spaces(s)
##        print s
    else:
        s = fname
    if s[-4:] == '.aig':
        f_name = s[:-4]
    elif s[-5:] == '.blif':
        f_name = s[:-5]
    else:
        f_name = s
        s = s+'.aig'
##    run_command(s)
##    print s
    init_initial_f_name = initial_f_name = f_name
    run_command('r %s;st'%s)
##    run_command('fold') #only does something if some of the outputs are constraints.
    sz = sizeof()
    hist = []
    aigs_pp('push','initial')
    run_command('logic;undc;st;zero')
    if not sz == sizeof():
        aigs_pp('push','undc')
    print 'history = %s'%hist
##    if s[-4:] == '.aig':
##        run_command('&r %s;&put'%s) 
##        run_command('r %s'%s)
##        run_command('logic;undc;st;zero')
    if s[-5:] == '.blif': #this is a blif file
##        run_command('r %s'%s)
##        run_command('logic,undc')
##        abc('st;&get;&put') #changes names to generic ones for doing cec later.
##        run_command('zero;w %s.aig'%f_name)
        abc('&get;&put;w %s.aig'%f_name) #warning: changes names to generic ones.
    run_command('fold')
    set_globals()
##    hist = []
##    init_initial_f_name = initial_f_name = f_name
##    run_command('fold') #only does something if some of the outputs are constraints.
##    aigs_pp('push','initial')
    #aigs = create push/pop history of aigs
    #aigs.push() put the initial aig on the aig list.
    print 'Initial f_name = %s'%f_name
    abc('addpi') #only does something if there are no PIs
    #check_pos() #this removes constant outputs with a warning -
    #needed when using iso. Need another fix for using iso.
    ps()
    return

def aigs_pp(op='push', typ='reparam'):
    global hist,init_initial_f_name
    """ hist ia a sequence of types in {reparam, phase, initial, tempor}
    and the corresponding aigs are stored in numbered files
    These are used to unmap the cex back to the origina. The unmaapping is done by """
##    print hist
    if op == 'push':
        hist.append(typ)
        abc('w %s_aigs_%d.aig'%(init_initial_f_name,len(hist)))
    if op == 'pop':
##        print hist
        abc('cexsave') #protect current cex from a read
        abc('r %s_aigs_%d.aig'%(init_initial_f_name,len(hist)))
        abc('cexload')
        ps()
        typ = hist.pop()
##    print hist
    return typ

def scl():
    abc('&get;&scl;&put')
    ps()

def cex_trim_g(F_init=0,tail=0,m=''):
    abc('w %s_cex.aig'%f_name)
    N=cex_frame()
    G = N - tail
    F = F_init
    abc('cexsave')
    while True:
        print 'F = %d, G = %d'%(F,G)
        abc('r %s_cex.aig'%f_name)
        abc('cexload')
        if m == '':
            abc('cexcut -F %d -G %d'%(F,G))
        else:
            abc('cexcut -m -F %d -G %d'%(F,G))
##        abc('drw')
##        ps()
        res = run_parallel(slps+bmcs,20)
##        run_command('bmc2 -v -T 20')
##        if is_sat(): #got a shortening of cex
        if not res == Undecided:
            Nb = cex_frame() #size of shortcut
            abc('cexmerge -F %d -G %d'%(F,G))
            abc('r %s_cex.aig'%f_name)
            abc('cexload')
            abc('testcex -a')
            if cex_po() <0:
                return 'ERROR2'
            Nt=cex_frame() #current cex length
            print 'Cex length reduced from %d to %d'%(N,Nt)
            return
        F = F + (G-F)/2
##        G = N - i*delta
        if F >= G:
           return

def cex_trim(factor=1):
    t_begin = time.time()
    abc('w %s_cex.aig'%f_name)
    N=cex_frame()
    inc = min(N/10,100)
    F = 0
    G = inc
    abc('cexsave')
    abc('cexcut -n -F %d -G %d'%(F,G))
    run_command('bmc2 -v -F %d -T 5'%(.9*inc))
    inc = max(int(factor*n_bmc_frames()),2)
    F = N - inc
    G = N
    print 'inc = %d'%inc
    while True:
        abc('r %s_cex.aig'%f_name)
        abc('cexload')
        abc('cexcut -n -F %d -G %d'%(F,G))
##        abc('drw')
##        ps()
##        run_command('bmc2 -v -F %d -T 20'%(.9*inc))
        run_parallel(slps+bmcs,10)
        if not is_sat():
            abc('cex_load') #leave current cex in buffer
            Nb = inc
        else:
            Nb = cex_frame() #size of shortcut
            abc('cexmerge -F %d -G %d'%(F,G))
        abc('r %s_cex.aig'%f_name)
        abc('cexload')
        abc('testcex -a')
        if cex_po() <0:
            return 'ERROR2'
##        abc('cexload')
        Nt=cex_frame() #current cex length
        print 'Cex length = %d'%Nt
        G=F
        F = max(0,F - inc)
        print 'F = %d, G = %d'%(F,G)
        if G <= 2:
            abc('cexload')
            print 'Time: %0.2f'%(time.time() - t_begin) 
            return
    
        
def read_file():
    global win_list, init_simp, po_map
    read_file_quiet()
##    ps()
##    init_simp = 1
##    win_list = [(0,.1),(1,.1),(2,.1),(3,.1),(4,.1),(5,-1),(6,-1),(7,.1)] #initialize winning engine list
##    po_map = range(n_pos())

def rf():
##    set_engines(4) #temporary
    read_file()
    abc('zero')

def write_file(s):
    """this is the main method for writing the current circuit to an AIG file on disk.
    It manages the name of the file, by giving an extension (s). The file name 'f_name'
    keeps increasing as more extensions are written. A typical sequence is
    name, name_smp, name_smp_abs, name_smp_abs_spec, name_smp_abs_spec_final"""
    global f_name
    """Writes out the current file as an aig file using f_name appended with argument"""
    f_name = '%s_%s'%(f_name,s)
    print '^^^ New f_name = %s'%f_name
    ss = '%s.aig'%(f_name)
    print 'WRITING %s: '%ss,
    ps()
    abc('w '+ss)

def get_max_bmc(chtr=False):
    return get_bmc_depth(chtr)

def get_bmc_depth(chtr=False):
    """ Finds the number of BMC frames that the latest operation has used. The operation could be BMC, reachability
    interpolation, abstract, speculate. max_bmc is continually increased. It reflects the maximum depth of any version of the circuit
    including g ones, for which it is known that there is not cex out to that depth."""
    global max_bmc
    c = cex_frame()
    if c > 0:
        b = c-1
    else:
        b = n_bmc_frames()
    if b > max_bmc:
        set_max_bmc(b,chtr)
        if chtr:
            report_bmc_depth(max_bmc)
    return max_bmc

def null_status():
    """ resets the status to the default values but note that the &space is changed"""
    abc('&get;&put')

##def set_bmc_depth(b,chtr=False):
##    set_max_bmc(b,chtr)

def set_max_bmc(b,chtr=False):
    """ Keeps increasing max_bmc which is the maximum number of time frames for
    which the current circuit is known to be UNSAT for"""
    global max_bmc
    if b > max_bmc and chtr:
        max_bmc = b
        report_bmc_depth(max_bmc)
    return max_bmc

def report_bmc_depth(m):
##    return #for non hwmcc applications
    print 'u%d'%m

def print_circuit_stats():
    """Stardard way of outputting statistice about the current circuit"""
    global max_bmc
    i = n_pis()
    o = n_pos()
    l = n_latches()
    a = n_ands()
    s='ANDs'
    if a == -1:
        a = n_nodes()
        s = 'Nodes'
##    b = max(max_bmc,bmc_depth()) # don't want to do this because bmc_depth can change max_bmc
    b = get_max_bmc(chtr=False)
    c = cex_frame()
    if b>= 0:
        if c>b:
            out ='PIs=%d,POs=%d,FF=%d,%s=%d,max depth=%d,CEX depth=%d'%(i,o,l,s,a,b,c)
        elif is_unsat():
            out = 'PIs=%d,POs=%d,FF=%d,%s=%d,max depth = infinity'%(i,o,l,s,a)
        else:
            out = 'PIs=%d,POs=%d,FF=%d,%s=%d,max depth=%d'%(i,o,l,s,a,b)            
    else:
        if c>=0:
            out = 'PIs=%d,POs=%d,FF=%d,%s=%d,CEX depth=%d'%(i,o,l,s,a,c)
        else:
            out = 'PIs=%d,POs=%d,FF=%d,%s=%d'%(i,o,l,s,a)
    print out
    return out

def is_unsat():
    if prob_status() == 1:
        return True
    else:
        return False

def is_sat():
    if prob_status() == 0:
        return True
    else:
        return False

def wc(file):
    """writes <file> so that costraints are preserved explicitly"""
    abc('&get;&w %s'%file)

def rc(file):
    """reads <file> so that if constraints are explicit, it will preserve them"""
    abc('&r -s %s;&put'%file)                         

#more complex functions: ________________________________________________________
#, abstract, pba, speculate, final_verify, dprove3

def timer(s):
    btime = time.clock()
    abc(s)
    print 'time = %0.2f'%(time.clock() - btime)

def med_simp():
    x = time.time()
    abc("&get;&scl;&dc2;&lcorr;&dc2;&scorr;&fraig;&dc2;&put;dretime")
    #abc("dc2rs")
    ps()
    print 'time = %0.2f'%(time.time() - x)

##def simplify_old(M=0):
##    """Our standard simplification of logic routine. What it does depende on the problem size.
##    For large problems, we use the &methods which use a simple circuit based SAT solver. Also problem
##    size dictates the level of k-step induction done in 'scorr' The stongest simplification is done if
##    n_ands < 20000. Then it used the clause based solver and k-step induction where |k| depends
##    on the problem size """
##    set_globals()
##    abc('&get;&scl;&lcorr;&put')
##    p_40 = False
##    n =n_ands()
##    if n >= 70000 and not '_smp' in f_name:
####        abc('&get;&scorr -C 0;&put')
##        scorr_T(30)
##        ps()
##    n =n_ands()
##    if n >= 100000:
##        abc('&get;&scorr -k;&put')
##        ps()
##    if (70000 < n and n < 150000):
####        print '1'
##        p_40 = True
##        abc("&get;&dc2;&put;dretime;&get;&lcorr;&dc2;&put;dretime;&get;&scorr;&fraig;&dc2;&put;dretime")
####        print 2'
##        ps()
##        n = n_ands()
####        if n<60000:
##        if n < 80000:
##            abc("&get;&scorr -F 2;&put;dc2rs")
##            ps()
##        else: # n between 60K and 100K
##            abc("dc2rs")
##            ps()
##    n = n_ands()
####    if (30000 < n  and n <= 40000):
##    if (60000 < n  and n <= 70000):
##        if not p_40:
##            abc("&get;&dc2;&put;dretime;&get;&lcorr;&dc2;&put;dretime;&get;&scorr;&fraig;&dc2;&put;dretime")
##            abc("&get;&scorr -F 2;&put;dc2rs")
##            ps()
##        else:
##            abc("dc2rs")
##            ps()
##    n = n_ands()
####    if n <= 60000:
##    if n <= 70000:
##        abc('scl -m;drw;dretime;lcorr;drw;dretime')
##        ps()
##        nn = max(1,n)
##        m = int(min( 70000/nn, 16))
##        if M > 0:
##            m = M
##        if m >= 1:
##            j = 1
##            while j <= m:
##                set_size()
##                if j<8:
##                    abc('dc2')
##                else:
##                    abc('dc2rs')
##                abc('scorr -C 1000 -F %d'%j) #was 5000 temporarily 1000
##                if check_size():
##                    break
##                j = 2*j
##                print 'ANDs=%d,'%n_ands(),
##                if n_ands() >= .98 * nands:
##                     break
##                continue
##            if not check_size():
##                print '\n'
##    return get_status()

def simplify(M=0,N=0):
    """Our standard simplification of logic routine. What it does depende on the problem size.
    For large problems, we use the &methods which use a simple circuit based SAT solver. Also problem
    size dictates the level of k-step induction done in 'scorr' The stongest simplification is done if
    n_ands < 20000. Then it used the clause based solver and k-step induction where |k| depends
    on the problem size
    Does not change #PIs.
    """
    global smp_trace
    set_globals()
    smp_trace = smp_trace + ['&scl;&lcorr']
    abc('&get;&scl;&lcorr;&put')
##    abc('scl') # RKB temp
    if n_latches == 0:
        return get_status()
    p_40 = False
    n =n_ands()
    if N == 0 and n >= 70000 and not '_smp' in f_name:
##        abc('&get;&scorr -C 0;&put')
##        print 'Trying scorr_T'
        scorr_T(30)
        if n_latches() == 0:
            return get_status()
        ps()
    n =n_ands()
    if n >= 100000:
        smp_trace = smp_trace + ['&scorr']
        abc('&get;&scorr -k;&put')
        ps()
    if (70000 < n and n < 150000):
        p_40 = True
        smp_trace = smp_trace + ['&dc2;dretime;&lcorr;&dc2;dretime;&scorr;&fraig;&dc2;dretime']
        abc("&get;&dc2;&put;dretime;&get;&lcorr;&dc2;&put;dretime;&get;&scorr;&fraig;&dc2;&put;dretime")
##        abc("&get;&dc2;&put;dretime;&get;&dc2;&put;dretime;&get;&scorr;&fraig;&dc2;&put;dretime")
        ps()
    n = n_ands()
##    if (30000 < n  and n <= 40000):
    if (30000 < n  and n <= 70000):
        if not p_40:
            smp_trace = smp_trace + ['&dc2;dretime;&lcorr;&dc2;dretime;&scorr;&fraig;&dc2;dretime']
            abc("&get;&dc2;&put;dretime;&get;&lcorr;&dc2;&put;dretime;&get;&scorr;&fraig;&dc2;&put;dretime")
##            abc("&get;&dc2;&put;dretime;&get;&dc2;&put;dretime;&get;&scorr;&fraig;&dc2;&put;dretime")
            smp_trace = smp_trace + ['&scorr -F 2;dc2rs']
            abc("&get;&scorr -F 2;&put;dc2rs")
            ps()
        else:
            abc("dc2rs")
            smp_trace = smp_trace + ['dc2rs']
            ps()
    n = n_ands()
##    if n <= 60000:
    if n <= 35000:
        smp_trace = smp_trace + ['scl -m;drw;dretime;lcorr;drw;dretime']
        abc('scl -m;drw;dretime;lcorr;drw;dretime')
        ps()
        nn = max(1,n)
        m = int(min( 70000/nn, 16))
        if M > 0:
            m = M
        if N == 0 and m >= 1:
            j = 1
            while j <= m:
                set_size()
                if j<8:
                    abc('dc2')
                else:
                    abc('dc2rs')
                smp_trace = smp_trace + ['scorr -F %d'%j]
                abc('scorr -C 1000 -F %d'%j) #was 5000 temporarily 1000
                if check_size():
                    break
                j = 2*j
                print 'ANDs=%d,'%n_ands(),
                if n_ands() >= .98 * nands:
                     break
                continue
            if not check_size():
                print '\n'
    return get_status()
            
def simulate2(t=2001):
    """Does rarity simulation. Simulation is restricted by the amount
    of memory it might use. At first wide but shallow simulation is done, followed by
    successively more narrow but deeper simulation. 
    seed is globally initiallized to 113 when a new design is read in"""
    global x_factor, f_name, tme, seed
    btime = time.clock()
    tt = time.time()
    diff = 0
    while True:
        f = 20
        w = 64
        b = 16
        r = 700
        for k in range(9): #this controls how deep we go
            f = min(f*2, 3500)
            w = max(((w+1)/2)-1,1)
            abc('sim3 -F %d -W %d -N %d -R %d -B %d'%(f,w,seed,r,b))
            seed = seed+23
            if is_sat():
##                print 'RareSim time = %0.2f at frame %d'%((time.time() - tt),cex_frame())
                return 'SAT'
            if ((time.clock()-btime) > t):
                return 'UNDECIDED'

def simulate(t=2001):
    abc('&get')
    result = eq_simulate(t)
    return result

def eq_simulate(t):
    """Simulation is restricted by the amount
    of memory it might use. At first wide but shallow simulation is done, followed by
    successively more narrow but deeper simulation. The aig to be simulated must be in the & space
    If there are equivalences, it will refine them. Otherwise it is a normal similation
    seed is globally initiallized to 113 when a new design is read in"""
    global x_factor, f_name, tme, seed
    btime = time.clock()
    diff = 0
    while True:
        f = 5
        w = 255
        for k in range(9):
            f = min(f *2, 3500)
            w = max(((w+1)/2)-1,1)
##            abc('&sim3 -R %d -W %d -N %d'%(r,w,seed))
            abc('&sim -F %d -W %d -N %d'%(f,w,seed))
            seed = seed+23
            if is_sat():
                return 'SAT'
            if ((time.clock()-btime) > t):
                return 'UNDECIDED'

def generate_abs(n):
    """generates an abstracted  model (gabs) from the greg file or gla. The gabs file is automatically
    generated in the & space by &abs_derive or gla_derive. We store it away using the f_name of the problem
    being solved at the moment. The f_name keeps changing with an extension given by the latest
    operation done - e.g. smp, abs, spec, final, group. """
    global f_name
    #we have a cex and we use this generate a new gabs (gla) file
    if gabs: #use the register refinement method
        abc('&r -s %s_greg.aig; &abs_derive; &put; w %s_gabs.aig'%(f_name,f_name)) # do we still need the gabs file
    else: #use the gate refinement method
        run_command('&r -s %s_gla.aig; &gla_derive; &put'%f_name)
        if n_ands() < 2000:
            run_command('scl;scorr;dretime')
        run_command('w %s_gabs.aig'%f_name)
    if n == 1:
        #print 'New abstraction: ',
        ps()
    return   

def refine_with_cex():
    """Refines the greg or gla file (which contains the original problem with the set of FF's or gates
    that have been abstracted).
    This uses the current cex to modify the greg or gla file to reflect which regs(gates) are in the
    new current abstraction"""
    global f_name
    if gabs:
        abc('&r -s %s_greg.aig;&w %s_greg_before.aig'%(f_name,f_name))
        run_command('&abs_refine -s; &w %s_greg.aig'%f_name)
    else:
        run_command('&r -s %s_gla.aig;&w %s_gla_before.aig'%(f_name,f_name))
        run_command('&gla_refine; &w %s_gla.aig'%f_name)
    return

def refine_with_cex_suffix():
    """Refines the greg or gla file (which contains the original problem with the set of FF's or gates
    that have been abstracted).
    This uses the current cex to modify the greg or gla file to reflect which regs(gates) are in the
    new current abstraction"""
    global f_name
    return Undecided_no_reduction
    t = 5
    cexf = cex_frame()
    suf = .9*cexf
    run_command('write_status %s_temp.status'%f_name)
    ub = int(cexf -min(10, .02*cexf))
    lb = int(min(10,.02*cexf))
    suf = int(.5*(ub-lb))
    if_last = 0
    N = 0
    while True:
        N = N+1
        tt = time.time()
        run_command('read_status %s_temp.status'%f_name)
        print 'Refining using suffix %d with time = %d'%(suf,t)
        run_command('&r -s %s_gla.aig;&w %s_gla_before.aig'%(f_name,f_name))
        F = create_funcs([18],t) #create a timer function with timeout = t
        F = F + [eval('(pyabc_split.defer(abc)("&gla_refine -F %d; &w %s_gla.aig"))'%(suf,f_name))]
        for i,res in pyabc_split.abc_split_all(F): #need to do a binary search
            if i == 0:  #timeout
                lb = int(suf)
                dec = 'increasing'
                break
            elif same_abs(): #suffix did not refine - need to decrease suf
                ub = int(suf)
                dec = 'decreasing'
                break
            else: #refinement happened
                print 'refinement happened.'
                return
        print 'ub = %.2f, lb = %.2f, suf = %.2f'%(ub,lb,suf)
        suf = int(lb+.5*(ub-lb))
        if (ub-lb)< (max(1.1,min(10,.02*cexf))) or if_last or N >=4: # not refining in time allowed, give up
            print '(ub-lb) = %0.2f'%(ub-lb)
            print 'could not refine in resources allowed'
            return Undecided_no_reduction
    
def same_abs():
    run_command('r %s_gabs.aig'%f_name)
    set_size()
##    ps()
    run_command('&r -s %s_gla.aig; &gla_derive; &put'%f_name)
    if n_ands() < 2000:
        run_command('scl;scorr;dretime')
##    ps()
    return check_size()

def abstraction_refinement(latches_before,NBF,ratio=.75):
    """Subroutine of 'abstract' which does the refinement of the abstracted model,
    using counterexamples found by BMC, BDD reachability, etc"""
    global x_factor, f_name, last_verify_time, x, win_list, last_winner, last_cex, t_init, j_last, sweep_time
    global cex_list, last_cx, abs_ref_time
    sweep_time = 2
    T1 = time.time()
    if NBF == -1:
        F = 2000
    else:
        F = 2*NBF
    print '\nIterating abstraction refinement'
    add_trace('abstraction refinement')
    J = slps+intrps+pdrs+bmcs+sims
    J=modify_methods(J)
    print sublist(methods,J)
    last_verify_time = t = x_factor*max(50,max(1,2.5*G_T))
##    t = 1000 #temporary
    t = abs_time
    initial_verify_time = last_verify_time = t
    reg_verify = True
    print 'Verify time set to %d'%last_verify_time
    while True: #cex based refinement
        generate_abs(1) #generate new gabs file from refined greg or gla file
        set_globals()
        latches_after = n_latches()
        if small_abs(ratio):
            print 'abstraction too large'
            return Undecided_no_reduction
        if (time.time() - T1)> abs_ref_time:
            print 'abstraction time ran out'
            break
        t = last_verify_time
        yy = time.time()
        abc('w %s_beforerpm.aig'%f_name)
        rep_change = reparam() #new - must do reconcile after to make cex compatible
##        if rep_change:
##            add_trace('reparam')
        abc('w %s_afterrpm.aig'%f_name)
##        if reg_verify:
        status = verify(J,t)
        print 'status = ',
        print status
##        else:
##            status = pord_1_2(t)
###############
        if status[0] == Sat_true:
            print 'Found true cex'
            reconcile_a(rep_change)
##            add_trace('SAT by %s'%status[1])
            return Sat_true
        if status[0] == Unsat:
##            add_trace('UNSAT by %s'%status[1])      
            return Unsat
        if status[0] == Sat:
##            add_trace('SAT by %s'%status[1])
            abc('write_status %s_after.status'%f_name)
            reconcile_a(rep_change) # makes the cex compatible with original before reparam and puts original in work space
            abc('write_status %s_before.status'%f_name)
            if gabs: #global variable
                refine_with_cex()
            else:
                result = refine_with_cex_suffix()
                if result == Sat:
                    return Sat
##                result = refine_with_cex()
                if result == Undecided_no_reduction:
                    return result
            if is_sat(): # if cex can't refine, status is set to Sat_true
                print 'Found true cex in output %d'%cex_po()
                return Sat_true
            else:
                continue
        else:
            break
    print '**** Latches reduced from %d to %d'%(latches_before, n_latches())
    return Undecided_reduction

def small_abs(ratio=.75):
    """ tests is the abstraction is too large"""
##    return ((rel_cost_t([pis_before_abs,latches_before_abs, ands_before_abs])> -.1)
##           or (n_latches() >= ratio*latches_before_abs))
    return (n_latches() >= ratio*latches_before_abs)

##def abstract(if_bip=True):
##    global ratio
##    if if_bip:
##        return abstractb(True) #old method using abstraction refinement
##    else:
##        return abstractb(False) #not using bip and reachx

def abstractb():
    """ abstracts using N Een's method 3 - cex/proof based abstraction. The result is further refined using
    simulation, BMC or BDD reachability. abs_ratio is the the limit for accepting an abstraction"""
    global G_C, G_T, latches_before_abs, x_factor, last_verify_time, x, win_list, j_last, sims
    global latches_before_abs, ands_before_abs, pis_before_abs, abs_ratio
    if ifbip < 1:
        print 'using ,abs in old way'
    tt = time.time()
    j_last = 0
    set_globals()
    #win_list = []
    latches_before_abs = n_latches()
    ands_before_abs = n_ands()
    pis_before_abs = n_real_inputs()
    abc('w %s_before_abs.aig'%f_name)
    print 'Start: ',
    ps()
    funcs = [eval('(pyabc_split.defer(initial_abstract)())')]
    # fork off BMC3 and PDRm along with initial abstraction
    t = 10000 #want to run as long as initial abstract takes.
##    J = sims+pdrs+bmcs+intrps
    J = slps+pdrs+bmcs+intrps
    J = modify_methods(J,1)
##    if n_latches() < 80:
##        J = J + [4]
    funcs = create_funcs(J,t) + funcs
    mtds = sublist(methods,J) + ['initial_abstract'] #important that initial_abstract goes last
    m,result = fork_last(funcs,mtds)
    if is_sat():
        print 'Found true counterexample in frame %d'%cex_frame()
        return Sat_true
    if is_unsat():
        return Unsat
##    set_max_bmc(NBF)
    NBF = get_bmc_depth(True)
    print 'Abstraction good to %d frames'%NBF
    #note when things are done in parallel, the &aig is not restored!!!
    abc('&r -s %s_greg.aig; &w initial_greg.aig; &abs_derive; &put; w initial_gabs.aig; w %s_gabs.aig'%(f_name,f_name))
    set_max_bmc(NBF,True)
    print 'Initial abstraction: ',
    ps()
    abc('w %s_init_abs.aig'%f_name)
    latches_after = n_latches()
##    if latches_after >= .90*latches_before_abs: #the following should match similar statement
##    if ((rel_cost_t([pis_before_abs, latches_before_abs, ands_before_abs])> -.1) or
##        (latches_after >= .75*latches_before_abs)):
    if small_abs(abs_ratio):
        abc('r %s_before_abs.aig'%f_name)
        print "Too little reduction!"
        print 'Abstract time wasted = %0.2f'%(time.time()-tt)
        return Undecided_no_reduction
    sims_old = sims
    sims=sims[:1] #make it so that rarity sim is not used since it can't find a cex
    result = abstraction_refinement(latches_before_abs, NBF,abs_ratio)
    sims = sims_old
    if result <= Unsat:
        return result
##    if n_latches() >= .90*latches_before_abs:
##    if ((rel_cost_t([pis_before_abs, latches_before_abs, ands_before_abs])> -.1) or (latches_after >= .90*latches_before_abs)):
##    if rel_cost_t([pis_before_abs,latches_before_abs, ands_before_abs])> -.1:
    if small_abs(abs_ratio) or result == Undecided_no_reduction: #r is ratio of final to initial latches in abstraction. If greater then True
        abc('r %s_before_abs.aig'%f_name) #restore original file before abstract.
        print "Too little reduction!  ",
        print 'Abstract time wasted = %0.2f'%(time.time()-tt)
        result = Undecided_no_reduction
        return result
    #new
    else:
        write_file('abs') #this is only written if it was not solved and some change happened.
    print 'Abstract time = %0.2f'%(time.time()-tt)
    return result

def initial_abstract_old():
    global G_C, G_T, latches_before_abs, x_factor, last_verify_time, x, win_list
    set_globals()
    time = max(1,.1*G_T)
    abc('&get;,bmc -vt=%f'%time)
    set_max_bmc(get_bmc_depth(True),True)
    c = 2*G_C
    f = max(2*max_bmc,20)
    b = min(max(10,max_bmc),200)
    t = x_factor*max(1,2*G_T)
    s = min(max(3,c/30000),10) # stability between 3 and 10 
    cmd = '&get;,abs -bob=%d -stable=%d -timeout=%d -vt=%d -depth=%d'%(b,s,t,t,f)
##    print cmd
    print 'Running initial_abstract with bob=%d,stable=%d,time=%d,depth=%d'%(b,s,t,f)
    abc(cmd)
    abc('&w %s_greg.aig'%f_name)
##    ps()

def initial_abstract(t=100):
    global G_C, G_T, latches_before_abs, x_factor, last_verify_time, x, win_list, max_bmc, ifbip
    set_globals()
    time = max(1,.1*G_T)
    time = min(time,t)
    abc('&get;,bmc -vt=%f'%time)
    set_max_bmc(get_bmc_depth(True),True)
    c = 2*G_C
    f = max(2*max_bmc,20)
    b = min(max(10,max_bmc),200)
    t1 = x_factor*max(1,2*G_T)
    t = max(t1,t)
    s = min(max(3,c/30000),10) # stability between 3 and 10
    cmd = '&get;,abs -bob=%d -stable=%d -timeout=%d -vt=%d -depth=%d'%(b,s,t,t,f)
    if ifbip == 2:
        cmd = '&get;,abs -bob=%d -stable=%d -timeout=%d -vt=%d -depth=%d -dwr=%s_vabs'%(b,s,t,t,f,f_name)
        print 'Using -dwr=%s_vabs'%f_name
##    print cmd
    print 'Running initial_abstract with bob=%d,stable=%d,time=%d,depth=%d'%(b,s,t,f)
    abc(cmd)
##    get_bmc_depth()
##    pba_loop(max_bmc+1)
    abc('&w %s_greg.aig'%f_name)
    return max_bmc

def abs_m():
    set_globals()
    y = time.time()
    nl = n_abs_latches() #initial set of latches
    c = 2*G_C
    t = x_factor*max(1,2*G_T) #total time
    bmd = get_bmc_depth()
    if bmd < 0:
        abc('bmc3 -T 2') #get initial depth estimate
        bmd = get_bmc_depth()
    f = bmd
    abc('&get')
    y = time.time()
    cmd = '&abs_cba -v -C %d -T %0.2f -F %d'%(c,.8*t,bmd) #initial absraction
##    print '\n%s'%cmd
    abc(cmd)
    b_old = b = n_bmc_frames()
    f = min(2*bmd,max(bmd,1.6*b))
    print 'cba: latches = %d, depth = %d'%(n_abs_latches(),b)
##    print n_bmc_frames()
    while True:
        if (time.time() - y) > .9*t:
            break
        nal = n_abs_latches()
        cmd = '&abs_cba -v -C %d -T %0.2f -F %d'%(c,.8*t,f) #f is 2*bmd and is the maximum number of frames allowed
##        print '\n%s'%cmd
        abc(cmd)
##        print n_bmc_frames()
        b_old = b
        b = n_bmc_frames() 
        nal_old = nal 
        nal = n_abs_latches() #nal - nal_old is the number of latches added by cba
        #b - b_old is the additional time frames added by cba
        f = min(2*bmd,max(bmd,1.6*b))   #may be this should just be bmd
        f = max(f,1.5*bmd)
        print 'cba: latches = %d, depth = %d'%(nal,b)
        if ((nal == nal_old) and (b >= 1.5*b_old) and b >= 1.5*bmd):
            """
            Went at least bmd depth and saw too many frames without a cex
            (ideally should know how many frames without a cex)
            """
            print 'Too many frames without cex'
            break
        if b > b_old: #if increased depth
            continue
        if nal > .9*nl: # try to minimize latches
##            cmd = '&abs_pba -v -S %d -F %d -T %0.2f'%(b,b+2,.2*t)
            cmd = '&abs_pba -v -F %d -T %0.2f'%(b+2,.2*t)
##            print '\n%s'%cmd
            abc(cmd)
            b = n_bmc_frames()
            nal_old = nal
            nal = n_abs_latches()
            print 'pba: latches = %d, depth = %d'%(nal,b)
##            print n_bmc_frames()
            if nal_old < nal: #if latches increased there was a cex
                continue
            if nal > .9*nl: # if still too big 
                return
        continue 
##    b = n_bmc_frames()
    cmd = '&abs_pba -v -F %d -T %0.2f'%(b+2,.2*t)
##    print '\n%s'%cmd
    abc(cmd)
    b = n_bmc_frames()
    print 'pba: latches = %d, depth = %d'%(n_abs_latches(),b)
##    print n_bmc_frames()
    print 'Total time = %0.2f'%(time.time()-y)

def n_abs_latches():
    abc('&w pba_temp.aig') #save the &space
    abc('&abs_derive;&put')
    abc('&r -s pba_temp.aig')
    return n_latches()
        
def pba_loop(F):
    n = n_abs_latches()
    while True:
        run_command('&abs_pba -v -C 0 -F %d'%F)
        abc('&w pba_temp.aig')
        abc('&abs_derive;&put')
        abc('&r -s pba_temp.aig')
        N = n_latches()
##        if n == N or n == N+1:
##            break
##        elif N > n:
        if N > n:
            print 'cex found'
        break

def ssm(options=''):
    """ Now this should be the same as super_prove(1) """
    y = time.time()
    result = prove_part_1() # simplify first
    if result == 'UNDECIDED':
        result = ss(options)
    print 'Total time taken on file %s by function ssm(%s) = %d sec.'%(initial_f_name,options,(time.time() - y))
    return result

def ssmg():
    return ssm('g')

def ssmf():
    return ssm('f')

def ss(options=''):
    """
    Alias for super_sec
    This is the preferred command if the problem (miter) is suspected to be a SEC problem
    """
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time, sec_options
    sec_options = options
    print '\n*************Executing speculate************'
    y = time.time()
    abc('scl')
    result = speculate()
    # if result is 1 then it is a real SAT since we did not do anything before
    if result > 2: #save the result and read in with /rf so that files are initialized correctly
        if not '_spec' in f_name:
            write_file('spec') #make sure we do not overwrite original file
        read_file_quiet_i('%s'%f_name) #this resets f_name and initial_f_name etc.
        print '\n************* Executing super_prove ************'
        print 'New f_name = %s'%f_name
        result = super_prove()
        if result[0] == 'SAT':
            result = 'UNDECIDED' #because speculation was done initially.
    elif result == 1:
        result = 'SAT'
    else:
        result = RESULT[result]
    print 'Total time taken on file %s by function ss(%s) = %d sec.'%(initial_f_name,options,(time.time() - y))
    return result

def quick_sec(t):
##    fb_name = f_name[:-3]+'New'
##    abc('&get;&miter -s %s.aig;&put'%fb_name)
##    abc('w %s.%s_miter.aig'%(f_name,fb_name))
    quick_simp()
    verify(slps+ pdrs+bmcs+intrps,t)
    if is_unsat():
        return 'UNSAT'
    if is_sat():
        return 'SAT'
    else:
        return'UNDECIDED'

def pre_sec():
    """ put files to be compared into Old and New aigs. Simplify, but
    turn off reparameterization so that PIs in Old and New match after simplification.
    """
    global trim_allowed
##    trim_allowed = False
##    print 'trim allowed = ',trim_allowed
    print 'First file: ',
    read_file_quiet_i() #note - reads into & space and then does &put
    ps()
    prs(False)
    ps()
    abc('&w Old.aig')
    print 'Second file: ',
    read_file_quiet_i()
    ps()
    prs(False)
    ps()
    abc('&w New.aig')
        
def cec():
    print 'Type in the name of the aig file to be compared against'
    s = raw_input()
    s = remove_spaces(s)
    if not 'aig' in s:
        s = s+'.aig'
    run_command("&get;&cec -v %s"%s)

def sec(B_part,options):
    """
    Use this for AB filtering and not sup_sec
    Use pp_sec to make easy names for A and B, namely Old and New.
    This assumes that the original aig (renamed A_name below) is already read into the working space.
    Then we form a miter using &miter between two circuits, A_name, and B_name.
    We then do speculate immediately. Optionally we could simplify A and B
    and then form the miter and start from there. The only difference in speculate
    is that &srm2 is used, which only looks at equivalences where one comes from A and
    one from B. Options are -a and -b which says use only flops in A or in B or both. The
    switch sec_sw controls what speculate does when it generates the SRM.
    """
    global f_name,sec_sw, A_name, B_name, sec_options
    yy = time.time()
    A_name = f_name # Just makes it so that we can refer to A_name later in &srm2
    B_name = B_part
    run_command('&get; &miter -s %s.aig; &put'%B_name)
##    abc('orpos')
    f_name = A_name+'_'+B_name+'_miter' # reflect that we are working on a miter.
    abc('w %s.aig'%f_name)
    print 'Miter = ',
    ps()
    sec_options = options
    if sec_options == 'ab':
        sec_options = 'l' #it will be changed to 'ab' after &equiv
    sec_sw = True 
    result = speculate() 
    sec_options = ''
    sec_sw = False
    if result <= Unsat:
        result = RESULT[result]
    else:
        result = super_prove()
        if result[0] == 'SAT':
            result = 'UNDECIDED'
    print 'Total time = %d'%(time.time() - yy)
    return result

def filter(opts):
    global A_name,B_name
    #temp for yen-sheng's examples
##    return
    #temp
##    print 'Filtering with options = %s'%opts
    """ This is for filter which effectively only recognizes options -f -g"""
    if (opts == '' or opts == 'l'): #if 'l' this is used only for initial &equiv2 to get initial equiv creation
        return
    print 'filter = %s  '%opts,
    if opts == 'ab':
        print A_name ,
        print B_name
##        run_command('&ps')
        run_command('&filter -fi %s.aig %s.aig'%(A_name,B_name))
        return
####    if not opts == 'f':
####        opts = 'g'
##    print 'filter = %
    run_command('&filter -i -%s'%opts)

def check_if_spec_first():
    global sec_sw, A_name, B_name, sec_options, po_map
    set_globals()
    t = max(1,.5*G_T)
    r = max(1,int(t))
    abc('w check_save.aig')
    abc('&w check_and.aig')
    abc("&get; &equiv3 -v -F 20 -T %f -R %d"%(t,5*r))
    filter('g')
    abc("&srm -A %s_gsrm.aig; r %s_gsrm.aig"%(f_name,f_name))
    print 'Estimated # POs = %d for initial speculation'%n_pos()
    result = n_pos() > max(50,.25*n_latches())
    abc('r check_save.aig')
    abc('&r -s check_and.aig')
    return result


def sp_file(file_in=None):
    """ do super_prove on given file"""
    if file_in == None:
        return
    else:
        read_file_quiet_i(file_in)
        res = sp(n=3) #do not do speculation
##        res = simple()
        return res

def try_all_gsrms(srms):
    """ try to prove each filtered speculation with super_prove"""
    assert not srms == []
    fn = init_initial_f_name
    funcs = []
    if 'f' in srms:
        funcs = [eval('(pyabc_split.defer(sp_file)("%s_gsrm_f.aig"))'%fn)]
    if 'g' in srms:
        funcs = funcs + [eval('(pyabc_split.defer(sp_file)("%s_gsrm_g.aig"))'%fn)]
    if '' in srms:
        funcs = funcs + [eval('(pyabc_split.defer(sp_file)("%s_gsrm_0.aig"))'%fn)]
    mtds = srms
    count = 0
    for i,res in pyabc_split.abc_split_all(funcs):
        print res[0]
        if res[0] == 'UNSAT':
            return [res[0],mtds[i]]
        if res[0] == 'SAT':
            count += 1
    if count == len(srms): #all are SAT
        print 'all srms are SAT'
        return [None, 'all_sat']
    else:
        print 'at least one srm was UNDECIDED'
        return ['UNDECIDED','one is hard']

    

def initial_speculate(sec_opt='',t=0):
    global sec_sw, A_name, B_name, sec_options, po_map,f_name
    set_globals()
    if sec_options == '':
        sec_options = sec_opt
    # 1000 - 15, 5000 - 25, 10000 - 30, 50000 - 50
    n_latch_init = n_latches()
    na = n_ands()
##    t = max(1,G_T)
    if t == 0:
        if na < 1000:
            t =20
        elif na < 5000:
            t = 20 + ((na-1000)/4000)*20
        elif na < 10000:
            t = 40 + ((na-5000)/5000)*20
        elif na < 50000:
            t = 60 + ((na-40000)/40000)*15
        else:
            t = 75
    r = max(1,int(t))
    rounds = 30*r
    print 'Initial sec_options = %s'%sec_options
##    if sec_options == 'l':
##        cmd = "&get; &equiv3 -lv -F 20 -T %f -R %d -S %d"%(3*t,rounds,rounds/20)
##    else:
##        cmd = "&get; &equiv3 -v -F 20 -T %f -R %d -S %d"%(3*t,rounds,rounds/20)
    cmd = "&get; &equiv3 -v -F 20 -T %d -R %d -S %d"%(int(t),0,0) #####
    print cmd
    abc(cmd)
##    print 'AND space after &equiv3: ',
##    run_command('&ps')
    if (sec_options == 'l'):
        if sec_sw:
            sec_options = 'ab'
        else:
            sec_options = 'f'
##    print 'A_name: ',
##    run_command('r %s.aig;ps'%A_name)
##    print 'B_name: ',
##    run_command('r %s.aig;ps'%B_name)
    fn = init_initial_f_name
    abc('&w %s_initial_gore_no_filter.aig'%fn)
    if not sec_sw:
        f_name_protect = f_name
        print 'fn = ',fn
        abc('&r -s %s_initial_gore_no_filter.aig'%fn)
        filter('f')
        cmd = "&srm -A %s_gsrm_f.aig; r %s_gsrm_f.aig; &w %s_gore_f.aig"%(fn,fn,fn)
        abc(cmd)
        print "SRM with filter 'f': ",
        res =q_simp()
        if iso():
            abc('w %s_gsrm_f.aig'%fn)
            print 'wrote ','%s_gsrm_f.aig'%fn
        size_f = sizeof()
        size_f.append(n_eff_pos())
        print size_f
        
        abc('&r -s %s_initial_gore_no_filter.aig'%fn)
        filter('g')
        cmd = "&srm -A %s_gsrm_g.aig; r %s_gsrm_g.aig; &w %s_gore_g.aig"%(fn,fn,fn)
        abc(cmd)
        print "SRM with filter 'g': ",
        res =q_simp()
        if iso():
            abc('w %s_gsrm_g.aig'%fn)
            print 'wrote ','%s_gsrm_g.aig'%fn
        size_g = sizeof()
        size_g.append(n_eff_pos())
        print size_g
        
        abc('&r -s %s_initial_gore_no_filter.aig'%fn)
        filter('')
        cmd = "&srm -A %s_gsrm_0.aig; r %s_gsrm_0.aig; &w %s_gore_0.aig"%(fn,fn,fn)
        abc(cmd)
        print "SRM with filter '': ",
        res =q_simp()
        if iso(): #if iso did something it returns True
            abc('w %s_gsrm_0.aig'%fn)
            print 'wrote ','%s_gsrm_0.aig'%fn
        size_0 = sizeof()
        size_0.append(n_eff_pos())
        print size_0
        
        srms = [] #filter out if too many latches, or not enough new POs or if 2 srms are equal
    # can spend a lot of time when all 3 have no cex's and are hard.
    # Need only do one.
    # All 3 may seem equally good in terms of flops. 0 has more POs so more to prove, but
    # also more reduction maybe. Note no_eff_pos can be smaller than initial so use POs
        print n_latch_init
        print size_f
        print size_g
        print size_0
        if size_f[1] > n_pos_before + 2 and size_f[2] <= .9*n_latch_init:
            srms.append('f')
        if ( size_f[2] >= size_g[2]+1) or srms == []:
            if size_g[1] > n_pos_before + 2 and size_g[2] <= .9*n_latch_init:
                srms.append('g')
        if (size_g[2]>= size_0[2] + 1 and 'g' in srms) or  (size_f[2] >= size_0[2] + 2 and 'f' in srms):
            if size_0[1] > n_pos_before + 2 and size_0[2] <= .9*n_latch_init:
                srms.append('')
        
        if srms == []:
            print 'not enough reduction on any of srms'
            return ['UNDECIDED','not enough reduction']
        else:
            print 'trying %s srms'%str(srms)
            
        if len(srms)>0:
            spec_undec = False
            res = try_all_gsrms(srms) # calls multiple super_proves
            if res[0] == 'UNSAT':
                print 'gsrm_%s was proved UNSAT'%res[1]
                return res
            elif res[0] == 'UNDECIDED':
                print 'one srm was too hard'
                return res
            elif res[0] == None:
                print 'all srms were proved SAT. Refinement needed'
            else:
                assert False, 'return from try_all_srms invalid %s'%str(res[0])
        
        #choose the best
        print 'f_names: %s, %s'%(f_name_protect,f_name)
        f_name = f_name_protect
        if size_f[2] <= size_g[2] or size_g[1] > max_pos: #comparing flops and POs
            if size_f[2] <= size_0[2] or size_0[1] > max_pos: #f wins
                abc('&r -s %s_gore_f.aig;&w %s_gore.aig'%(fn,f_name))
                abc("&srm -A %s_gsrm.aig; r %s_gsrm.aig"%(f_name,f_name)) #regenerate gsrm_f
                ps()
                print 'f wins'
                return [None,'f']
        if size_g[2] <= size_0[2] or size_0[1] > max_pos:  #g wins
            abc('&r -s %s_gore_g.aig;&w %s_gore.aig'%(fn,f_name))
            abc("&srm -A %s_gsrm.aig; r %s_gsrm.aig"%(f_name,f_name)) #regenerate gsrm_g
            ps()
            print 'g wins'
            return [None,'g']
        else:
            xa('&r -s %s_gore_0.aig;&w %s_gore.aig'%(fn,f_name))
            xa("&srm -A %s_gsrm.aig; r %s_gsrm.aig"%(f_name,f_name)) #regenerate gsrm_0
            ps()
            print "'' wins"
            return [None,'']
    else: # this may not work now.
        print 'miter: ',
        run_command('&ps')
        print 'A_name: ',
        run_command('r %s.aig;ps'%A_name)
        print 'B_name: ',
        run_command('r %s.aig;ps'%B_name)
        cmd = "&srm2 -%s %s.aig %s.aig; r gsrm.aig; w %s_gsrm.aig; &w %s_gore.aig"%(sec_options,A_name,B_name,f_name,f_name)
        abc(cmd)
        po_map = range(n_pos())
        return [None, sec_options]


##___________________________________________            
##        #temp pick best option
##        sec_potions = ''
##        return sec_options
##
##    
####    print 'Running &srm'
##    if sec_sw:
##        print 'miter: ',
##        run_command('&ps')
##        print 'A_name: ',
##        run_command('r %s.aig;ps'%A_name)
##        print 'B_name: ',
##        run_command('r %s.aig;ps'%B_name)
##        cmd = "&srm2 -%s %s.aig %s.aig; r gsrm.aig; w %s_gsrm.aig; &w %s_gore.aig"%(sec_options,A_name,B_name,f_name,f_name)
##        abc(cmd)
##        po_map = range(n_pos())
##        return sec_options
##    else:
####        abc('&r %s_gore.aig; &srm ; r gsrm.aig; w %s_gsrm.aig'%(f_name,f_name))
##        cmd = "&srm -A %s_gsrm.aig; r %s_gsrm.aig; &w %s_gore.aig"%(f_name,f_name,f_name)
##        print 'Running %s'%cmd
##        abc(cmd)
##        print 'done with &srm'
##        po_map = range(n_pos())
##        if sec_options == '' or sec_options == 'g':
####            if n_pos() > 10000:###temp
##            if n_eff_pos() > 1000: ##### Temporary
##                sec_options = 'g'
##                print 'sec_options set to %s'%'g'
##                abc('&r -s %s_gore.aig'%f_name)
##                filter(sec_options)
####                print 'Running &srm'
##                cmd = "&srm -A %s_gsrm.aig; r %s_gsrm.aig; &w %s_gore.aig"%(f_name,f_name,f_name)
####                print 'Running %s'%cmd
##                abc(cmd)
##                po_map = range(n_pos())
##                if n_eff_pos() > 500:
####                if n_pos() > 20000:####temp
##                    sec_options = 'f'
##                    print 'sec_options set to %s'%'f'
##                    abc('&r -s %s_gore.aig'%f_name)
##                    filter(sec_options)
##                    print 'Running &srm'
##                    cmd = "&srm -A %s_gsrm.aig; r %s_gsrm.aig; &w %s_gore.aig"%(f_name,f_name,f_name)
##                    print 'Running %s'%cmd
##                    abc(cmd)
##                    po_map = range(n_pos())
##    return sec_options
##________________________________________
                
##                    if n_pos() > 2000:
##                        return sec_options
                        
        
def test_against_original():
    '''tests whether we have a cex hitting an original PO'''
    abc('&w %s_save.aig'%f_name) #we preserve whatever was in the & space
    abc('&r -s %s_gore.aig'%f_name) #This is the original
    abc('testcex') #test the cex against the &space
    PO = cex_po()
##    print 'test_against original gives PO = %d'%PO 
    abc('&r -s %s_save.aig'%f_name)
    if PO > -1:
        return True
    else:
        abc('write_status %s_status.status'%f_name)
        return False

def set_cex_po(n=0):
    """
    if cex falsifies a non-real PO return that PO first,
    else see if cex_po is one of the original, then take it next
    else return -1 which means that the cex is not valid and hence an error.
    parameter n = 1 means test the &-space
    """
    global n_pos_before, n_pos_proved #these refer to real POs
    if n == 0:
        abc('testcex -a -O %d'%(n_pos_before-n_pos_proved)) #test regular AIG space
    else:
        abc('testcex -O %d'%(n_pos_before-n_pos_proved)) #test the &-AIG
    PO = cex_po()
##    print 'cex_po = %d, n_pos_before = %d, n_pos_proved = %d'%(PO, n_pos_before, n_pos_proved)
    if PO >= (n_pos_before - n_pos_proved): #cex_po is not an original
##        print '1. cex PO = %d'%PO
        return PO # after original so take it.
    if n == 0:
        abc('testcex -a') #test regular
    else:
        abc('testcex')  #test &space
    PO = cex_po()
    print '2. cex PO = %d'%PO
    cx = cex_get()
    if PO > -1:
        if test_against_original(): #this double checks that it is really an original PO
            cex_put(cx)
            print 'test_against_original was valid'
            return PO
        else:
            print '1. PO is not valid'
            return -1 #error
    if PO < 0 or PO >= (n_pos_before - n_pos_proved): # not a valid cex because already tested outside original.
##        print 'cex_po = %d, n_pos_before = %d, n_pos_proved = %d'%(PO, n_pos_before, n_pos_proved)
        print '2. PO is not valid'
        PO = -1 #error
##    print '3. cex PO = %d'%PO
    return PO

def cex_stats():
    print 'cex_pis = %d, cex_regs = %d, cex_po = %d, cex_frame = %d'%(n_cex_pis(),n_cex_regs(),cex_po(),cex_frame())

def speculate(t=0):
    """Main speculative reduction routine. Finds candidate sequential equivalences and refines them by simulation, BMC, or reachability
    using any cex found. """    
    global G_C,G_T,n_pos_before, x_factor, n_latches_before, last_verify_time, trim_allowed, n_pos_before
    global t_init, j_last, sec_sw, A_name, B_name, sec_options, po_map, sweep_time, sims, cex_list, n_pos_proved,ifpord1
    global last_cx, total_spec_refine_time, skip_spec
##    print 'sec_options = %s'%sec_options
    if skip_spec:
        return Undecided_no_reduction
    add_trace('speculate')
    if t > 0:
        total_spec_refine_time = t
    abc('scl') #make sure no dangling flops
    abc('orpos')
    last_cx = 0
    ifpord1 = 1
    initial_po_size = last_srm_po_size = n_pos()
    initial_sizes = [n_pis(),n_pos(),n_latches(),n_ands()]
    if sec_sw:
        print 'A_name = %s, B_name = %s, f_name = %s, sec_options = %s'%(A_name, B_name, f_name, sec_options)
#temp for yen-sheng's examples
##    elif n_ands() > 40000 and sec_options == '':
####        add_trace('sec options g')
##        sec_options = 'g'
##        print 'sec_options set to "g"'
####        add_trace('sec_options ="g"')
        
    def refine_with_cex():
        """Refines the gore file to reflect equivalences that go away because of cex"""
        global f_name
        abc('write_status %s_before_refine.status'%f_name)
        abc('&r -s %s_gore.aig; &resim -m'%f_name)
##        run_command('&ps')
##        cex_stats()
        filter(sec_options)
        run_command('&w %s_gore.aig'%f_name)
        return

    def refine_without_cex(L=[]):
        """removes the POs in the current SRM in the list L. Alters the equivalence classes in the
            gore file accordingly.
        """
        global f_name
        if L == []:
            return
        print 'Entered refine_without_cex'
        abc('write_status %s_before_refine.status'%f_name)
        create_abc_array(L)
        print 'wrote array'
        abc('&r -s %s_gore.aig; &equiv_filter'%f_name)
        print 'filtered gore using L'
        filter(sec_options)
        print 'filtered with %s'%sec_options
        run_command('&w %s_gore.aig'%f_name)
        return
    
    def set_cex(lst):
        """ assumes only onecex in lst for now"""
        for j in range(len(lst)):
            cx = lst[j]
            if cx == None:
                continue
            else:
                cex_put(cx)
                break
            
    def retry(t):
        add_trace('retrying')
        print 'retrying winner cex which did not refine'
        abc('r %s_gsrm_before.aig'%f_name) #restore previous gsrm
        abc('w %s_beforerpm.aig'%f_name)
        rep_change = reparam() #must be paired with reconcile below if cex
        if rep_change:
            add_trace('reparam')
        abc('w %s_afterrpm.aig'%f_name)
        if last_winner == 'RareSim':
            simulate2(t)
        elif last_winner == 'PDR':
            pdr(t)
        elif last_winner == 'BMC':
            bmc(t)
        elif last_winner == 'INTRP':
            intrp(t)
        elif last_winner == 'PDRM':
            pdrm(t)
        elif last_winner == 'BMC3':
            bmc3(t)
        elif last_winner == 'PDR_sd':
            pdrseed(t)
        elif last_winner == 'PDRM_sd':
            pdrmm(t)
        elif last_winner == 'INTRPm':
            intrpm(t)
        elif last_winner == 'REACHY':
            reachy(t)
        elif last_winner == 'BMC_J':
            bmc_j(t)
        elif last_winner == 'PDRa':
            pdra(t)
        else:
            reconcile(rep_change)
            return False
        reconcile(rep_change)
        if not is_sat():
            return False
        abc('&r -s %s_gore_before.aig ;&w %s_gore.aig'%(f_name,f_name)) #restore old gore file
        return True
    
    def generate_srm():
        """generates a speculated reduced model (srm) from the gore file"""
        global f_name, po_map, sec_sw, A_name, B_name, sec_options, n_pos_proved
##        print 'Generating'
        pos = n_pos()
        ab = n_ands()
        abc('w %s_oldsrm.aig'%f_name) #save for later purposes
        if sec_sw:
            run_command('&r -s %s_gore.aig; &srm2 -%s %s.aig %s.aig; r gsrm.aig; w %s_gsrm.aig'%(f_name,sec_options,A_name,B_name,f_name))
        else:
            abc('&r -s %s_gore.aig; &srm -A %s_gsrm.aig ; r %s_gsrm.aig'%(f_name,f_name,f_name)) #do we still need to write the gsrm file
##        ps()
        po_map = range(n_pos())
        ps()
        n_pos_proved = 0
        return 'OK'

    n_pos_before = n_pos()
    n_pos_proved = 0
    n_latches_before = n_latches()    
    set_globals()
##    t = max(1,.5*G_T)#irrelevant
##    r = max(1,int(t))
    t = 1000
    j_last = 0
    J = slps+sims+pdrs+bmcs+intrps
    J = modify_methods(J,1)
    print 'sec_options = %s'%sec_options 
    funcs = [eval('(pyabc_split.defer(initial_speculate)("%s"))'%sec_options)]
    funcs = create_funcs(J,10000)+funcs #want other functins to run until initial speculate stops
    mtds = sublist(methods,J) + ['initial_speculate'] #important that initial_speculate goes last
    print mtds
    res = fork_last(funcs,mtds) #break when last initial_speculate ends
    print 'init_spec return = ',
    print res
    if res == None:
        add_trace('de_speculate')
        return Undecided_no_reduction
    if res[0] == 'UNSAT':
        add_trace('UNSAT by filter "%s" inside initial_speculate'%res[1])
        return Unsat
    if res[0] == 'UNDECIDED' or res[0] == None:
        add_trace('de_speculate')
        return Undecided_no_reduction # even one of the initial speculations too hard
    if res[1] in ['f','g','']:
        sec_options = res[1]
    add_trace('sec_options = %s'%sec_options)
    add_trace('Number of POs: %d'%n_pos())
##    ps()
    if not res[0] == None: # None indicates all srms were SAT and need to be refined.
        if is_unsat():
            return Unsat
        if is_sat():
            return Sat_true
    if n_pos_before == n_pos():
        print 'No new outputs. Quitting speculate'
        add_trace('de_speculate')
        return Undecided_no_reduction # return result is unknown
    if n_eff_pos() > 1999:
        print 'Too many POs'
        add_trace('de_speculate')
        return Undecided_no_reduction
    abc('r %s_gsrm.aig'%f_name)
    print 'Initial speculation: ',
    ps()
    abc('w %s_initial_gsrm.aig'%f_name)
    if n_eff_pos() > max_pos:
        print 'Too many new outputs. Quitting speculate'
        add_trace('de_speculate')
        return Undecided_no_reduction # return result is unknown
    if n_pos() <= n_pos_before + 2:
        print 'Too few new outputs. Quitting speculate'
        add_trace('de_speculate')
        return Undecided_no_reduction # return result is unknown
    if n_latches() > .9*n_latches_before:
        print 'not enough reduction in SRM'
        add_trace('de_speculate')
        return Undecided_no_reduction
    if n_latches() == 0:
        return check_sat() 
    if use_pms: #
        p,q,r=par_multi_sat(0)
        q = indices(r,1)
        print sumsize(r)
        tot = len(r)
        ud = count_less(r,0) #undecided L=-1 means undecided, L=0 means unsat, L=1 means sat
        us = count_less(r,1)-ud #unsat
        sa = count_less(r,2) - (ud+us) #sat
        if sa > .5*tot or sa >.3*ud:
            print 'too many POs are already SAT'
            add_trace('de_speculate')
            return Undecided_no_reduction
    if sec_options == 'l' and sec_sw:
        sec_options = 'ab' #finished with initial speculate with the 'l' option
        print "sec_options set to 'ab'"
    elif sec_options == 'l':
        sec_options = 'f'
        print "sec_options set to 'f'"
    po_map = range(n_pos()) #we need this because the initial_speculate is done in parallel and po_map is not passed back.
    npi = n_pis()
    set_globals()
    if is_sat():
        return Sat_true
    simp_sw = init = True
    add_trace('speculative refinement')
    print '\nIterating speculation refinement'
    sims_old = sims
    sims = sims[:1] 
##    J = slps+sims+pdrs+intrps+bmcs
    J = slps+sims+pdrs+bmcs #changed for hwmcc15
    J = modify_methods(J)
    print 'Parallel refinement methods = ',
    print sublist(methods,J)
    t = max(50,max(1,2*G_T))
    last_verify_time = t
    ### temp
    last_verify_time = total_spec_refine_time
    ###
    print 'Verify time set to %d'%last_verify_time
    reg_verify = True
    ref_time = time.time()
    sweep_time = 2
    ifpord1=1
    par_verify = re_try = False
##    total_spec_refine_time = 150
    while True: ##################### refinement loop
        set_globals()
        yy = time.time()
        time_used = (yy-ref_time)
        print 'Time_used = %0.2f'%time_used
        if time_used > total_spec_refine_time:
            print 'Allotted speculation refinement time is exceeded'
            add_trace('de_speculate')
            return Undecided_no_reduction
        if n_latches() > .9 * n_latches_before:
            print 'Not enough reduction in flop count in SRM'
            add_trace('de_speculate')
            return Undecided_no_reduction
        if not init:
            abc('r %s_gsrm.aig'%f_name) #this is done only to set the size of the previous gsrm.
            abc('w %s_gsrm_before.aig'%f_name)
            set_size()
            result = generate_srm()
            if n_pos() <= n_pos_before + 1: #heuristic that if only have one equivalence, then not worth it
                abc('r %s.aig'%f_name) #revert to previous aig
                sims = sims_old
                print 'UNDECIDED'
                print 'Refinement time = %0.2f'%(time.time() - ref_time)
                add_trace('de_speculate')
                return Undecided_no_reduction
            if n_latches() > 9.*n_latches_before:
                print 'Allotted speculation refinement time is exceeded'
                add_trace('de_speculate')
                return Undecided_no_reduction
            last_srm_po_size = n_pos()
            yy = time.time()
            # if the size of the gsrm did not change after generating a new gsrm
            # and if the cex is valid for the gsrm, then the only way this can happen is if
            # the cex_po is an original one.
            if check_size(): #same size before and after
                if check_cex(): #valid cex failed to refine possibly
                    if 0 <= cex_po() and cex_po() < (n_pos_before - n_pos_proved): #original PO
                        print 'Found cex in original output number = %d'%cex_po()
                        print 'Refinement time = %0.2f'%(time.time() - ref_time)
                        return Sat_true
                    elif check_same_gsrm(f_name): #if two gsrms are same, then failed to refine
                        print 'CEX failed to refine'
                        add_trace('de_speculate')
                        return Error
                else:
                    print 'not a valid cex'
                    print 'Last winner = %s'%last_winner
                    print 're_try = %d'%re_try
                    if re_try:
                        add_trace('de_speculate')
                        return Error #abort speculation
                    re_try = True
            else:
                re_try = False # just got a valid refinement so reset.
            if n_latches() == 0:
                print 'Number of latches reduced to 0'
                print 'CEX refined incorrectly'
                abc('r %s.aig'%f_name) #revert to previous aig
                sims = sims_old
                add_trace('de_speculate')
                return Error
        init = False # make it so that next time it is not the first time through
        if not t == last_verify_time: # heuristic that if increased last verify time,
                                      # then try pord_all 
            t = last_verify_time
            if reg_verify:
                t_init = (time.time() - yy)/2 #start poor man's concurrency at last cex fime found
                t_init = min(10,t_init)
                t = last_verify_time
                print 'Verify time set to %d'%t
        if not re_try:
##            abc('w %s_beforerpm.aig'%f_name)
##            rep_change = reparam() #must be paired with reconcile below if cex
####            if rep_change:
####                add_trace('reparam')
##            abc('w %s_afterrpm.aig'%f_name)
            rep_change = False #TEMP
            if reg_verify:
                if par_verify:
                    S,L_sat_POs,s = par_multi_sat(120)
                    L_sat_POs = indices(s,1)
##                    L_sat_POs = L[1]
                    L=[]
                    for j in range(len(L_sat_POs)): #eliminate any of the original POs
                        if L_sat_POs[j] >= (n_pos_before-n_pos_proved):
                            L=L+[L_sat_POs[j]]
                    L_sat_POs = L
                    print L
                    if not L_sat_POs == []:
                        ress = [1,[['multi_sat']]]
                        add_trace(['multi_sat'])
                    else:
                        reg_verify = False
                        ress = pord_1_2(t)
                        add_trace(ress[1])
                else:
                    ttt = time.time() #find time it takes to find a cex
                    ress = verify(J,t)
                    t_last_verify = time.time() - ttt
            else:
                ress = pord_1_2(t)
##                print ress
                add_trace(ress[1])
            result = ress[0]
##            add_trace(ress[1])
        else:
            if not retry(100):
                add_trace('de_speculate')
                return Error
            result = get_status()
##        print result
        if result == Unsat:
            add_trace('UNSAT by %s'%ress[1])
            print 'UNSAT'
            print 'Refinement time = %0.2f'%(time.time() - ref_time)
            return Unsat
        if result < Unsat:
            abc('&r -s %s_gore.aig;&w %s_gore_before.aig'%(f_name,f_name)) #we are making sure that none of the original POs fail
            if par_verify:
                refine_without_cex(L_sat_POs)
                print 'refining without cex done'
                continue
            if not reg_verify:
                set_cex(cex_list)
##            if not re_try:
####                rec = reconcile(rep_change) #end of pairing with reparam()TEMP
####                if rec == 'error':
####                    add_trace('de_speculate')
####                    return Error
##                 (npi == n_cex_pis()),'ERROR: #pi = %d, #cex_pi = %d'%(npi,n_cex_pis())
            abc('&r -s %s_gore.aig;&w %s_gore_before.aig'%(f_name,f_name)) #we are making sure that none of the original POs fail
            if reg_verify:
                PO = set_cex_po(0) #testing the regular space
            else:
                abc('&r -s %s_gsrm.aig'%f_name)
                PO = set_cex_po(1) # test against the &space.
            print 'cex_PO is %d,  '%PO,
            if (-1 < PO and PO < (n_pos_before-n_pos_proved)):
                print 'Found cex in original output %d'%cex_po()
                print 'Refinement time = %0.2f'%(time.time() - ref_time)
                return Sat_true
            if PO == -1:
                add_trace('de_speculate')
                return Error
            refine_with_cex()    #change the number of equivalences
            if not par_verify and t_last_verify > 2500:
                par_verify = True #switch to finding many POs at a time
            continue
        elif (is_unsat() or n_pos() == 0):
            print 'UNSAT'
            print 'Refinement time = %0.2f'%(time.time() - ref_time)
            return Unsat
        else: #if undecided, record last verification time
            print 'Refinement returned undecided in %d sec.'%t
            last_verify_time = t
            #########################added
            if reg_verify: #try one last time with parallel POs cex detection (find_cex_par) if not already tried
                print 'aig size after initial refinement = ',
                ps() 
##                abc('r %s_beforerpm.aig'%f_name) # to continue refinement, need to restore original
##                print 'beforermp aig size = ',
##                ps()
                t_init = min(last_verify_time,(time.time() - yy)/2) #start poor man's concurrency at last cex fime found
                t_init = min(10,t_init)
                reg_verify = False
                t = last_verify_time # = 2*last_verify_time
                abc('w %s_beforerpm.aig'%f_name)
                rep_change = reparam() #must be paired with reconcile()below
                abc('w %s_afterrpm.aig'%f_name)
                print 'entering pord_1_2 ,',
                ps()
                ress = pord_1_2(t) #main call to verification
                print ress
                result = ress[0]
                add_trace(ress[1])
                if result == Unsat:
                    print 'UNSAT'
                    print 'Refinement time = %0.2f'%(time.time() - ref_time)
                    return Unsat
                if is_sat() or result == Sat:
##                    assert result == get_status(),'result: %d, status: %d'%(result,get_status())
                    print 'result: %d, status: %d'%(result,get_status())
                    set_cex(cex_list)
                    rec = reconcile(rep_change)
                    if rec == 'error':
                        add_trace('de_speculate')
                        return Error
                    abc('&r -s %s_gsrm.aig'%f_name)
                    PO = set_cex_po(1) #testing the & space
                    if (-1 < PO and PO < (n_pos_before-n_pos_proved)):
                        print 'Found cex in original output %d'%cex_po()
                        print 'Refinement time = %0.2f'%(time.time() - ref_time)
                        return Sat_true
                    if PO == -1:
                        add_trace('de_speculate')
                        return Error
                    refine_with_cex()    #change the number of equivalences
                    continue
                else: #if undecided, record last verification time
                    last_verify_time = t
                    print 'UNDECIDED'
                    break
            ################### added
            else:
                break
    sims = sims_old
    print 'UNDECIDED'
    print 'Refinement time = %0.2f'%(time.time() - ref_time)
##    if last_srm_po_size == initial_po_size: #essentially nothing happened. last_srm_po_size will be # POs in last srm.
    if initial_sizes == [n_pis(),n_pos(),n_latches(),n_ands()]:
        abc('r %s.aig'%f_name)
        add_trace('de_speculate')
        return Undecided_no_reduction #thus do not write spec file
    else: #file was changed, so some speculation happened. If we find a cex later, need to know this.
        write_file('spec')
        return Undecided_reduction

##def sst(t=2000):
##    '''simple SAT which writes out an unmapped cex to a file for reporting to hwmcc'''
##    y = time.time()
##    J = allbmcs+pdrs+sims+[5] #5 is pre_simp
##    funcs = create_funcs(J,t)
##    mtds =sublist(methods,J)
##    print mtds
##    fork_last(funcs,mtds)
##    result = get_status()
##    if result > Unsat:
##        write_file('smp')
##        result = verify(slps+allbmcs+pdrs+sims,t)
##        result = get_status()
##    if result < Unsat: #rkb
##        print 'unmapping cex'
##        res = unmap_cex()
####        result = ['SAT'] + result1
##        report_cex(1) #0 writes the unmapped cex into a cex file called init_initial_f_name_cex.status and 1 to stdout
##    print 'Time for simple_sat = %0.2f'%(time.time()-y)
##    report_bmc_depth(max(max_bmc,n_bmc_frames()))
##    return [RESULT[result]] + ['sst']
##
##
##def simple_sat(t=2001):
##    """
##    aimed at trying harder to prove SAT
##    """
##    y = time.time()
##    bmcs2 = [9,31]
##    bmcs2 = [9,30]
##    J = bmcs+pdrs+sims+[5] #5 is pre_simp
####    J = modify_methods(J)
####    J = [14,2,7,9,30,31,26,5] 
##    funcs = create_funcs(J,t)
##    mtds =sublist(methods,J)
##    print mtds
##    fork_last(funcs,mtds)
##    result = get_status()
##    if result > Unsat:
##        write_file('smp')
##        result = verify(slps+allbmcs+pdrs+sims,t)
##    print 'Time for simple_sat = %0.2f'%(time.time()-y)
##    report_bmc_depth(max(max_bmc,n_bmc_frames()))
##    return [RESULT[result[0]]] + [result[1]]
##
##def spd(t=900):
##    """
##    parallel super_deep
##    tries bmcs both before and after simplify
##    """
##    y=time.time()
##    funcs = create_funcs([18],t-2) #sleep
##    funcs = funcs + [eval('(pyabc_split.defer(super_deep_i)(t))')]
##    funcs = funcs + [eval('(pyabc_split.defer(super_deep_s)(t))')]
##    mtds = ['sleep','initial','after_simp']
##    print mtds
##    mx = -1 
##    for i,res in pyabc_split.abc_split_all(funcs):
##        print i,res
##        if i == 0:
##            break
##        if res == 'SAT' or res < Unsat:
##            mx = n_bmc_frames()
##            break
##        print 'Method %s: depth = %d, time = %0.2f '%(mtds[i],res,(time.time()-y))
##        if res > mx:
##            mx = res
##            report_bmc_depth(mx)
##    report_bmc_depth(mx)
##    print 'Best depth = %d'%mx
##    return mx
##   
##
##def super_deep_i(tt=900):
##    """
##    aimed at finding the deepest valid depth starting from the initial aig
##    """
##    y = z = time.time()
##    J = [9,31,40]
##    if n_latches() < 200:
##        J = J + [24]
##    t = tt-10
##    funcs = create_funcs([18],t) #sleep
##    funcs = funcs + create_funcs([2],max(5,t-40))
##    funcs = funcs + create_funcs(J,t-5)
##    mtds =['sleep'] + sublist(methods,[2]+J)
##    print mtds
##    mx = -1
##    for i,res in pyabc_split.abc_split_all(funcs):
##        if i == 0:
##            break
##        if res == 'SAT'or res < Unsat:
##            set_max_bmc(n_bmc_frames())
##            return 'SAT'
##        if n_bmc_frames() > mx:
##            mx = n_bmc_frames()
##        print 'Method on initial %s: depth = %d, time = %0.2f '%(mtds[i],n_bmc_frames(),(time.time()-z))
##    print 'Time for super_deep_i = %0.2f'%(time.time()-z)
##    print 'max good depth initial = %d'%(mx)
##    report_bmc_depth(mx)
##    return mx
##
##def super_deep_s(tt=900):
##    """
##    aimed at finding the deepest valid depth - simplifies first
##    """
##    z = y = time.time() #make it seem like it started 15 sec before actually
##    rel = prs(1,1) # pre simplicatin
##    time_used = time.time() - y
##    J = [9,31,40]
##    if n_latches() < 200:
##        J = J + [24]
##    ttt = tt-10
##    t = max(0,ttt-time_used) #time left
##    funcs = create_funcs([18],t) #sleep
##    funcs = funcs + create_funcs([2],max(5,t-40))
##    funcs = funcs + create_funcs(J,t-5)
##    mtds =['sleep'] + sublist(methods,[2]+J)
##    print mtds
##    mx = -1
##    for i,res in pyabc_split.abc_split_all(funcs):
##        if i == 0:
##            break
##        if res == 'SAT' or res < Unsat:
##            set_max_bmc(n_bmc_frames())
##            return 'SAT'
##        if n_bmc_frames() > mx:
##            mx = n_bmc_frames()
##        print 'Method on simplified %s: depth = %d, time = %0.2f '%(mtds[i],n_bmc_frames(),(time.time()-z))
##    print 'Time for super_deep_s = %0.2f'%(time.time()-z)
##    print 'max good depth simplified = %d'%(mx)
##    report_bmc_depth(mx)
##    return mx

def smpl(check_trace=True):
    check_trace = True #temp
    b=bmc3(5)
    get_bmc_depth(True)
    if b == 'SAT' and check_trace:
        abc('w %s_save.aig'%f_name)
        unmap_cex()
        report_cex(1)
##        abc('r %s_save.aig'%f_name)
        return ['SAT']+['bmc3']
    else:
        return simple()

def simple(t=100000,no_simp=0,check_trace=True):
    check_trace = True 
    y = time.time()
##    pre_simp()
    if not no_simp:
##        prove_part_1(frames_2=False) #do not use try_frames_2
        prove_part_1(frames_2=True) #use try_frames_2
        if is_sat():
            if check_trace:
                abc('w %s_save.aig'%f_name)
                unmap_cex()
                report_cex(1)
##                abc('r %s_save.aig'%f_name)
            return ['SAT']+['pre_simp']
        if is_unsat():
            return ['UNSAT']+['pre_simp']
        if n_latches() == 0:
            return [RESULT[check_sat()]]+['pre_simp']
##    J = slps+sims+bmcs+pdrs+intrps+pre
##    J = slps+sims+allbmcs+allpdrs+intrps
    J = slps+sims+pdrs+intrps+bmcs
    J = modify_methods(J)
    mtds = sublist(methods,J)
    print mtds
    result = verify(J,t)
    
    if is_sat():
        print 'cex_po() = ', cex_po()
        if check_trace:
            abc('w %s_save.aig'%f_name)
            unmap_cex()
            report_cex(1)
##            abc('r %s_save.aig'%f_name)
##    add_pord('%s by %s'%(result[0],result[1])
    return [RESULT[result[0]]] + [result[1]]


##def simple_bip(t=1000):
##    y = time.time()
##    J = [0,14,1,2,30,5] #5 is pre_simp
##    funcs = create_funcs(J,t)
##    mtds =sublist(methods,J)
##    fork_last(funcs,mtds)
##    result = get_status()
##    if result > Unsat:
##        write_file('smp')
##        result = verify(slps+[0,14,1,2,30],t)
##    print 'simple_bip = %0.2f'%(time.time()-y)
##    return RESULT[result] 

def check_same_gsrm(f):
##    return False #disable the temporarily until can figure out why this is there
    """checks gsrm miters before and after refinement and if equal there is an error"""
    global f_name
    abc('r %s_gsrm.aig'%f)
##    ps()
    run_command('miter -c %s_gsrm_before.aig'%f)
##    ps()
    abc('&get; ,bmc -timeout=5')
    result = True #if the same
    if is_sat(): #if different
        result = False
    abc('r %s_gsrm.aig'%f)
##    ps()
    return result

def check_cex():
    """ check if the last cex still asserts one of the outputs.
    If it does then we have an error"""
    global f_name
    abc('read_status %s_before_refine.status'%f_name)
    abc('&r -s %s_gsrm_before.aig'%f_name)
##    abc('&r %s_gsrm.aig'%f_name)
    run_command('testcex') #test the cex against the &-space aig.
##    print 'cex po = %d'%cex_po()
    return cex_po() >=0

def set_size():
    """Stores  the problem size of the current design.
    Size is defined as (PIs, POs, ANDS, FF)""" 
    global npi, npo, nands, nff, nmd
    npi = n_pis()
    npo = n_pos()
    nands = n_ands()
    nff = n_latches()
    nmd = max_bmc
    #print npi,npo,nands,nff

def check_size():
    """Assumes the problem size has been set by set_size before some operation.
    This checks if the size was changed
    Size is defined as (PIs, POs, ANDS, FF, max_bmc)
    Returns TRUE is size is the same""" 
    global npi, npo, nands, nff, nmd
    #print n_pis(),n_pos(),n_ands(),n_latches()
    result = ((npi == n_pis()) and (npo == n_pos()) and (nands == n_ands()) and (nff == n_latches()) )
    return result

def inferior_size():
    """Assumes the problem size has been set by set_size beore some operation.
    This checks if the new size is inferior (larger) to the old one 
    Size is defined as (PIs, POs, ANDS, FF)""" 
    global npi, npo, nands, nff
    result = ((npi < n_pis()) or (npo < n_pos()) or (nands < n_ands()) )
    return result

##def quick_verify(n):
##    """Low resource version of final_verify n = 1 means to do an initial
##    simplification first. Also more time is allocated if n =1"""
##    global last_verify_time
##    trim()
##    if n == 1:
##        simplify()
##        if n_latches == 0:
##            return check_sat()
##        trim()
##        if is_sat():
##            return Sat_true
##    #print 'After trimming: ',
##    #ps()
##    set_globals()
##    last_verify_time = t = max(1,.4*G_T)
##    if n == 1:
##        last_verify_time = t = max(1,2*G_T)
##    print 'Verify time set to %d '%last_verify_time
##    J = [18] + intrps+bmcs+pdrs+sims
##    status = verify(J,t)
##    return status

def process_status(status):
    """ if there are no FF, the problem is combinational and we still have to check if UNSAT"""
    if n_latches() == 0:
        return check_sat()
    return status
    
def get_status():
    """this simply translates the problem status encoding done by ABC
    (-1,0,1)=(undecided,SAT,UNSAT) into the status code used by our
    python code. -1,0,1 => 3,0,2
    """
##    if n_latches() == 0:
##        return check_sat()
    status = prob_status() #interrogates ABC for the current status of the problem.
    # 0 = SAT i.e. Sat_reg = 0 so does not have to be changed.
    if status == 1:
        status = Unsat
    if status == -1: #undecided
        status = Undecided
    return status

def two_temp(t=20):
    tt = time.time()
##    abc('tempor;scl;drw;&get;&rpm;&put;tempor;scl;drw;&get;&rpm;&put;scorr')
##    The above use of &rem causes an error in unmapping cex
    abc('tempor;scl;drw;tempor;scl;drw;scorr')
    print 'Time for two_temp = %.2f : '%(time.time()-tt),
    ps()
    return get_status()

def reparam_m():
    """eliminates PIs which if used in abstraction or speculation must be restored by
    reconcile and the cex made compatible with file beforerpm
    Uses the &-space
    """
    abc('w %s_temp.aig'%f_name)
    n = n_pis()
    t1 = time.time()
##    abc('&get;,reparam -aig=%s_rpm.aig; r %s_rpm.aig'%(f_name,f_name))
    abc('&get;&rpm;&put')
    tm = (time.time() - t1)
    if n_pis() == 0:
        print 'Number of PIs reduced to 0. Added a dummy PI'
        abc('addpi')
    nn = n_pis()
    if nn < n:
        print 'Reparam_m: PIs %d => %d, time = %.2f'%(n,nn,tm)
        rep_change = True
    else:
        abc('r %s_temp.aig'%f_name)
        rep_change = False
    return rep_change

def reparam_e():
    """eliminates PIs which if used in abstraction or speculation must be restored by
    reconcile and the cex made compatible with file beforerpm
    Uses the &-space
    """
    abc('w %s_temp.aig'%f_name)
    npos_old = n_pos()
    n = n_pis()
    t1 = time.time()
    abc('&get;,reparam -aig=%s_rpm.aig; r %s_rpm.aig'%(f_name,f_name))
    if not n_pos() == npos_old:
        print "reparam_e removed some POs - aborting Een's method"
        abc('r %s_temp.aig'%f_name)
        return reparam_m()
##    abc('&get;&rpm;&put')
    tm =(time.time() - t1)
    if n_pis() == 0:
        print 'Number of PIs reduced to 0. Added a dummy PI'
        abc('addpi')
    nn = n_pis()
    if nn < n:
        print 'Reparam_e: PIs %d => %d, time = %.2f'%(n,nn,tm)
        rep_change = True
    else:
        abc('r %s_temp.aig'%f_name)
        rep_change = False
    return rep_change

def reparam():
##    abc('w %s_temp.aig'%f_name)
##    res = reparam_e()
##    res = reparam_m()
    res = reparam_e()
    return res

##def try_and_rpm():
##    abc('w %s_temp.aig'%f_name)
##    n = n_pis()
##    t1 = time.time()
##    abc('&get;&rpm;&put')
##    print 'time &rpm = %.2f'%(time.time() - t1)
##    if n_pis() == 0:
##        print '&rpm: Number of PIs reduced to 0. Added a dummy PI'
##        abc('addpi')
##    nn = n_pis()
##    if nn < n:
##        print '&rpm: Reparam: PIs %d => %d'%(n,nn)
####        rep_change = True
##    abc('r %s_temp.aig'%f_name)
####    else:
####        abc('r %s_temp.aig'%f_name)
####        return False

def reconcile(rep_change):
    """used to make current cex compatible with file before reparam() was done.
    However, the cex may have come
    from extracting a single output and verifying this.
    Then the cex_po is 0 but the PO it fails could be anything.
    So testcex rectifies this. Assumes current cex is stored internally."""
    global n_pos_before, n_pos_proved
##    print 'rep_change = %s'%rep_change
    if rep_change == False:
        return
    abc('&r -s %s_beforerpm.aig; &w tt_before.aig'%f_name)
    abc('write_status %s_after.status;write_status tt_after.status'%f_name)
    abc('&r -s %s_afterrpm.aig;&w tt_after.aig'%f_name)
    POa = set_cex_po(1)   #this should set cex_po() to correct PO. A 1 here means it uses &space to check
    abc('reconcile %s_beforerpm.aig %s_afterrpm.aig'%(f_name,f_name))
        # reconcile modifies cex and restores work AIG to beforerpm
    abc('write_status %s_before.status;write_status tt_before.status'%f_name)
    POb = set_cex_po()#does not make sense if we are in absstraction refinement
    if POa != POb:
        abc('&r -s %s_beforerpm.aig; &w tt_before.aig'%f_name)
        abc('&r -s %s_afterrpm.aig; &w tt_after.aig'%f_name)
        print 'cex PO afterrpm = %d not = cex PO beforerpm = %d'%(POa,POb)
    if POa < 0: #'cex did not assert any output'
        return 'error'

def reconcile_a(rep_change):
    """ This is the reconcile used in abstraction refinement
    used to make current cex compatible with file before reparam() was done.
    However, the cex may have come
    from extracting a single output and verifying this.
    Then the cex_po is 0 but the PO it fails could be anything.
    So testcex rectifies this."""
    global n_pos_before, n_pos_proved
##    print 'rep_change = %s'%rep_change
    if rep_change == False:
        return
    abc('&r -s %s_beforerpm.aig; &w tt_before.aig'%f_name)
    abc('write_status %s_after.status;write_status tt_after.status'%f_name)
    abc('&r -s %s_afterrpm.aig;&w tt_after.aig'%f_name)
    POa = set_cex_po(1)   #this should set cex_po() to correct PO. A 1 here means it uses &space to check
    abc('reconcile %s_beforerpm.aig %s_afterrpm.aig'%(f_name,f_name))
    # reconcile modifies cex and restores work AIG to beforerpm
    abc('write_status %s_before.status;write_status tt_before.status'%f_name)
    if POa < 0: #'cex did not assert any output'
        return 'error'

def reconcile_all(lst, rep_change):
    """reconciles the list of cex's"""
    global f_name, n_pos_before, n_pos_proved
    if rep_change == False:
        return lst
    list = []
    for j in range(len(lst)):
        cx = lst[j]
        if cx == None:
            continue
        cex_put(cx)
        reconcile(rep_change)
        list = list + [cex_get()]
    return list
    

##def try_rpm():
##    """rpm is a cheap way of doing reparameterization and is an abstraction method, so may introduce false cex's.
##    It finds a minimum cut between the PIs and the main sequential logic and replaces this cut by free inputs.
##    A quick BMC is then done, and if no cex is found, we assume the abstraction is valid. Otherwise we revert back
##    to the original problem before rpm was tried."""
##    global x_factor
##    if n_ands() > 30000:
##        return
##    set_globals()
##    pis_before = n_pis()
##    abc('w %s_savetemp.aig'%f_name)
##    abc('rpm')
##    result = 0
##    if n_pis() < .5*pis_before:
##        bmc_before = get_bmc_depth()
##        #print 'running quick bmc to see if rpm is OK'
##        t = max(1,.1*G_T)
##        #abc('bmc3 -C %d, -T %f'%(.1*G_C, t))
##        abc('&get;,bmc -vt=%f'%t)
##        if is_sat(): #rpm made it sat by bmc test, so undo rpm
##            abc('r %s_savetemp.aig'%f_name)
##        else:
##            trim()
##            print 'WARNING: rpm reduced PIs to %d. May make SAT.'%n_pis()
##            result = 1
##    else:
##        abc('r %s_savetemp.aig'%f_name)
##    return result
            
def verify(J,t):
    """This method is used for finding a cex during refinement, but can also
    be used for proving the property. t is the maximum time to be used by
    each engine J is the list of methods to run in parallel. See FUNCS for list"""
    global x_factor, final_verify_time, last_verify_time, methods
    set_globals()
    t = int(max(1,t))
    J = modify_methods(J)
    mtds = sublist(methods,J)
##    print mtds
    #print J,t
    F = create_funcs(J,t)
    (m,result) = fork_break(F,mtds,'US') #FORK here
##    result = fork_break(F,mtds,'US') #FORK here
##    print result
##    assert result[0] == get_status(),'result: %d, status: %d'%(result[0],get_status())
    return result

def dsat_all(t=100,c=100000):
    print 't=%d,c=%d'%(t,c)
    N = n_pos()
    abc('&get')
    J = range(N)
    ttt = time.time()
    J.reverse()
    abc('w %s_temp.aig'%f_name)
    for j in J:
        tt = time.time()
        abc('r %s.aig'%f_name)
        run_command('cone -O %d; dc2; dsat -C %d'%(j,c))
        if is_unsat():
            print 'Output %d is %s'%(j,RESULT[2]),
        else:
            print 'Output %d is %s'%(j,RESULT[3]),
        T = time.time() -tt
        print 'time = %0.2f'%T
        if time.time() - tt > t:
            break
    print 'Total time = %0.2f'%(time.time() - ttt)
            
def check_sat(t=2001):
    """This is called if all the FF have disappeared, but there is still some logic left. In this case,
    the remaining logic may be UNSAT, which is usually the case, but this has to be proved. The ABC command 'dsat' is used fro combinational problems"""
    global smp_trace
    if not n_latches() == 0:
        print 'circuit is not combinational'
        return Undecided
    print 'Circuit is combinational - checking with dsat, iprove, &splitprove'
    L = list_const_pos()
    if not count_less(L,0) == len(L):
        if 1 in L:
            print "circuit has a constant 1 output"
            return Sat
        elif 0 in L and not -1 in L:
            return Unsat
    abc('&get') #save the current circuit
    abc('orpos')
    J = combs+slps
    mtds = sublist(methods,J)
##    print mtds
    F = create_funcs(J,t)
    (m,result) = fork(F,mtds) #FORK here
    print result
    print '%s: '%mtds[m],
##    smp_trace = smp_trace + ['%s'%mtds[m]]
    res = prob_status()
    print res
    if res == 0: #sat
##    if is_sat():
##        abc('&put')
        if n_pos() == 1:
            abc('&put')
            return Sat_true
        else:
            abc('&put')
            return Undecided_no_reduction #some POs could be unsat.
##    elif is_unsat():
    elif res == 1: #unsat
        abc('&put')
        return Unsat
    else:
        abc('&put') #restore
        return Undecided_no_reduction

def try_era(s):
    """era is explicit state enumeration that ABC has. It only works if the number of PIs is small,
    but there are cases where it works and nothing else does"""
    if n_pis() > 12:
        return
    cmd = '&get;&era -mv -S %d;&put'%s
    print 'Running %s'%cmd
    run_command(cmd)

def try_induction(C):
    """Sometimes proving the property directly using induction works but not very often.
    For 'ind' to work, it must have only 1 output, so all outputs are or'ed together temporarily"""
    return Undecided_reduction
    print '\n***Running induction'
    abc('w %s_temp.aig'%f_name)
    abc('orpos; ind -uv -C %d -F 10'%C)
    abc('r %s_savetemp.aig'%f_name)
    status = prob_status()
    if not status == 1:
        return Undecided_reduction
    print 'Induction succeeded'
    return Unsat
        
def smp():
    abc('smp')
    write_file('smp')

def dprove():
    abc('dprove -cbjupr')

def trim():
    global trim_allowed,smp_trace
    if not trim_allowed:
        return False
    result = reparam()
    return result

def prs(x=True,y=0):
    global trim_allowed, smp_trace
    """ If x is set to False, no reparameterization will be done in pre_simp"""
    global smp_trace
    smp_trace = []
    trim_allowed = x
    print 'trim_allowed = ',trim_allowed
    y = time.time()
    result = pre_simp(y)
    print 'Time = %0.2f'%(time.time() - y)
    write_file('smp')
    return RESULT[result[0]]

def check_push():
    """save the current aig if it has a different number of latches from last aig on lst"""
    result = False
    n = n_latches()
##    ps()
    abc('&get;cexsave') #save the current aig (cex?)
##    typ = hist[-1:]
##    print hist
    run_command('r %s_aigs_%d.aig'%(init_initial_f_name,len(hist)))
##    typ = aigs_pp('pop')
##    aigs.pop() #check latches in last aig.
    nn = n_latches()
##    ps()
##    aigs.push() # put back last aig.
##    aigs_pp('push',typ)
    abc('&put;cexload') # restore current aig (cex?)
##    print 'check_push: current n=%d, previous nn=%d'%(n,nn)
    if not n == nn: #if number of latches changed, need to push the current aig so that reconcile can work.
##        aigs.push()
##        print 'n /= nn'
        aigs_pp('push','reparam0') #default is push,reparam
        result = True
    return result

def dump():
    """ get rid of the last aig on the list"""
    abc('&get')
##    aigs.pop()
    aigs_pp('pop')
    abc('&put')

def test_no_simp():
    global last_simp
    ri = float(n_pis())/float(last_simp[0])
    ro = float(n_pos())/float(last_simp[1])
    rl = float(n_latches())/float(last_simp[2])
    ra = float(n_ands())/float(last_simp[3])
    val = min(ri,ro,rl,ra)
    if val < .95:
        print 'simplification seems worthwhile'
        return False
    print 'simplification not worthwhile'
    return True
        
def pre_simp(n=0,N=0):
    """This uses a set of simplification algorithms which preprocesses a design.
    Includes forward retiming, quick simp, signal correspondence with constraints, trimming away
    PIs, and strong simplify. If n not 0, then do not do phase abs"""
    global trim_allowed, temp_dec
    global smp_trace, aigs, last_simp
    chk_sat = 0
    smp_trace = []
    tried_constr = False
    while True:
        if n_latches() == 0:
            print 'Circuit is combinational'
            chk_sat = 1
            break
        if test_no_simp():
            break
        ttime = time.time()
        set_globals()
        if n_ands() < 18000:
            tried_constr = True
            try_scorr_constr()
        smp_trace = smp_trace + ['&scl']
        abc('&get; &scl; &put')
        print 'after &scl: ',
        ps()
        if n_latches() == 0:
##            print '# latches = 0'
            chk_sat = 1
            break
        if n_ands() < 18000 and not tried_constr:
            tried_constr = True
            try_scorr_constr()
        if (n_ands() > 200000 or n_latches() > 50000 or n_pis() > 40000):
            smp_trace = smp_trace + ['scorr_T']
            scorr_T(50)
            ps()
        if ((n_ands() > 0) or (n_latches()>0)):
            res =a_trim()
##            print hist
        if n_latches() == 0:
            chk_sat = 1
            break
        status = get_status()
        if (n == 0 and (not '_smp' in f_name) or '_cone' in f_name):
            best_fwrd_min([10,11])
            ps()
            if n_latches() > 0 and not tried_constr:
                status = try_scorr_constr()
        if ((n_ands() > 0) or (n_latches()>0)):
            res = a_trim()
##            print hist
        if n_latches() == 0:
            chk_sat = 1
            break
        status = process_status(status)
        if status <= Unsat:
            last_simp = [n_pis(),n_pos(),n_latches(),n_ands()]
            return [status,smp_trace,hist]
        print 'Starting simplify ',
        simplify(n,N)
        print 'Simplify: ',
        ps()
        if n_latches() == 0:
            chk_sat = 1
            break
        if trim_allowed and n == 0:
            t = min(15,.3*G_T)
            if (not '_smp' in f_name) or '_cone' in f_name: #try this only once on a design
                tt = 25
                if n_ands() > 500000:
                    tt = 30
                print 'trying try_temps'
                res,F = try_temps(tt) 
                if res:
                    print 'tempor worked'
                    aigs_pp('push','tempor')
                    #temporary
                    simplify(n,N)
                    #temporary
                if n_latches() == 0:
                    chk_sat = 1
                    break
                if n == 0:
                    print 'trying try_phases'
                    res,N = try_phases()
                    if res:
                        print 'phase worked'
                        aigs_pp('push','phase')
                if n_latches() == 0:
                    chk_sat = 1
                    break
            if ((n_ands() > 0) or (n_latches()>0)):
                res = a_trim()
##                print hist
        status = process_status(status)
        print 'Simplification time = %0.2f'%(time.time()-ttime)
        last_simp = [n_pis(),n_pos(),n_latches(),n_ands()]
        if chk_sat:
            status = check_sat()
        return [status, smp_trace,hist]
    last_simp = [n_pis(),n_pos(),n_latches(),n_ands()]
    if n_ands() == 0 or chk_sat:
        status = check_sat()
    else:
        status = Undecided
    return [status,smp_trace,hist]


def try_scorr_constr():
    set_size()
    abc('w %s_savetemp.aig'%f_name)
    status = scorr_constr()
    if inferior_size():
        abc('r %s_savetemp.aig'%f_name)
    return status

def factors(n):
    l = [1,]
    nn = n
    while n > 1:
        for i in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53):
            if not i <nn:
                break
            if n%i == 0:
                l = l + [i,]
                n = n/i
        if not n == 1:
            l = l + [n,]
        break
    return sorted(l)

def select(x,y):
    z = []
    for i in range(len(x)):
        if x[i]:
            z = z + [y[i],]
    return z
    
def ok_phases(n):
    """ only try those where the resulting n_ands does not exceed 60000"""
    f = factors(n)
    sp = subproducts(f)
    s = map(lambda m:m*n_ands()< 120000,sp)
    z = select(s,sp)
    return z

def subproducts(ll):
    ss = (product(ll),)
    #print ll
    n = len(ll)
    if n == 1:
        return ss
    for i in range(n):
        kk = drop(i,ll)
        #print kk
        ss = ss+(product(kk),)
        #print ss
        ss = ss+subproducts(kk)
        #print ss
    result =tuple(set(ss))
    #result.sort()
    return tuple(sorted(result))

def product(ll):
    n = len(ll)
    p = 1
    if n == 1:
        return ll[0]
    for i in range(n):
        p = p*ll[i]
    return p

def drop(i,ll):
    return ll[:i]+ll[i+1:]

def try_phases():
####    print 'entered try_phases ',
##    ps()
    no = n_pos()
    res = try_phase()
    print 'after try_phase ',
    ps()
    N = n_pos()/no
    if N > 1:
        res = True
    else:
        res = False
    return res,N

def try_phase():
    """Tries phase abstraction. ABC returns the maximum clock phase it found using n_phases.
    Then unnrolling is tried up to that phase and the unrolled model is quickly
    simplified (with retiming to see if there is a significant reduction.
    If not, then revert back to original"""
    global init_simp, smp_trace,aigs
    n = n_phases()
    print 'Phases = %d'%n
##    if ((n == 1) or (n_ands() > 45000) or init_simp == 0):
    if ((n == 1) or (n_ands() > 60000)):
        return False
##    init_simp = 0
    res = a_trim()
##    print hist
    print 'Trying phase abstraction - Max phase = %d'%n
    abc('w %s_phase_temp.aig'%f_name)
    na = n_ands()
    nl = n_latches()
    ni = n_pis()
    no = n_pos()
    z = ok_phases(n) # factors n into prime factors
    print z,
    if len(z) == 1:
        return False
    #p = choose_phase()
    p = z[1]
    abc('phase -F %d'%p)
    if no == n_pos(): #nothing happened because p is not mod period
        print 'Phase %d is incompatible'%p
        abc('r %s_phase_temp.aig'%f_name)
        if len(z)< 3:
            return False
        else:
            p = z[2]
            #print 'Trying phase = %d:  '%p,
            abc('phase -F %d'%p)
            if no == n_pos(): #nothing happened because p is not mod period
                print 'Phase %d is incompatible'%p
                abc('r %s_phase_temp.aig'%f_name)
                return False
            else:
                smp_trace = smp_trace + ['phase -F %d'%p]
                abc('r %s_phase_temp.aig'%f_name)
                abc('&get;&frames -o -F %d;&scl;&put'%p)
    else:
        abc('r %s_phase_temp.aig'%f_name)
        abc('&get;&frames -o -F %d;&scl;&put'%p)
        smp_trace = smp_trace + ['phase -F %d'%p]
    print 'Simplifying with %d phases: => '%p,
    smp_trace = smp_trace + ['simplify(1)']
    simplify(1)
##    res = a_trim() #maybe we don't need this because rel_cost uses n_real_inputs
    ps()
    cost = rel_cost([ni,nl,na])
    print 'New relative cost = %f'%(cost)
    if cost <  -.01:
        abc('w %s_phase_temp.aig'%f_name)
        if ((n_latches() == 0) or (n_ands() == 0)):
            return True
        if n_phases() == 1: #this bombs out if no latches. Need to see if any more phases to be tried.
            aigs_pp('push','phase') #this code can be simplified - 
            print 'n_phases = %d'%n_phases()
            return False
        else:
            aigs_pp('push','phase')
            result = try_phase()
            return result
    elif len(z)>2: #Try the next eligible phase.
        abc('r %s_phase_temp.aig'%f_name)
        if p == z[2]: #already tried this
            return False
        p = z[2]
        print 'Trying phase = %d: => '%p,
        abc('phase -F %d'%p)
        if no == n_pos(): #nothing happened because p is not mod period
            print 'Phase = %d is not compatible'%p
            return False
        abc('r %s_phase_temp.aig'%f_name)
        abc('&get;&frames -o -F %d;&scl;&put'%p)
        smp_trace = smp_trace + ['phase -F %d'%p]
        print 'Simplify with %d phases: '%p,
        simplify(1)
##        res =a_trim() #maybe we don't need this because rel_cost uses n_real_inputs
        cost = rel_cost([ni,nl,na])
        print 'New relative cost = %f'%(cost)
        if cost < -.01:
            print 'Phase abstraction with %d phases obtained:'%p,
            print_circuit_stats()
            abc('w %s_phase_temp.aig'%f_name)
            if ((n_latches() == 0) or (n_ands() == 0)):
                return True
            if n_phases() == 1: # this bombs out if no latches
                return True
            else:
                aigs_pp('push','phase')
                result = try_phase()
                return result
        else:
            smp_trace = smp_trace + ['de_phase']
    abc('r %s_phase_temp.aig'%f_name)
    return False

def try_temp(t=15):
    global smp_trace,aigs
    btime = time.clock()
##    res = a_trim() #maybe we don't want this here.
    print'Trying temporal decomposition - for max %0.2f sec. '%(t),
    abc('w %s_best_temp.aig'%f_name)
##    ni = n_pis()
    ni = n_real_inputs()
    nl = n_latches()
    na = n_ands()
    best = [ni,nl,na]
    cost_best = 0
    i_best = 0
    n_done = 0
    print 'best = ',
    print best
    F = create_funcs([18],t) #create a timer function
    F = F + [eval('(pyabc_split.defer(struc_temp)())')]
    F = F + [eval('(pyabc_split.defer(full_temp)(best))')]
    F = F + [eval('(pyabc_split.defer(two_temp)())')]
    for i,res in pyabc_split.abc_split_all(F):
        print i,res
        ps()
        if i == 0:
            break
        if n_latches() == 0:
            return True
        n_done = n_done+1
        if n_done == 2 and n_ands() > 5*best[2]:
            break
        cost = rel_cost(best)
        if cost<0:
            nri=n_real_inputs()
            best = (nri,n_latches(),n_ands())
            ps()
            abc('w %s_best_temp.aig'%f_name)
            i_best = i
            cost_best = cost
            print 'cost = %.2f, best = '%cost,
            print best
        if n_done > 2:
            break
    cost = cost_best
    print 'cost = %0.2f'%cost
    abc('r %s_best_temp.aig'%f_name)
    if cost<0:
        ps()
        return True
    else:
##        smp_trace = smp_trace + ['de_tempor']
##        abc('r %s_best_temp.aig'%f_name)
        return False

def struc_temp():
    abc('tempor -s;scr')
    result = q_simp()
    if result == 'UNSAT':
        return Unsat
    elif result == 'SAT':
        return Sat
    return Undecided

def full_temp(b):
    abc('tempor')
    q_simp()
    print 'Full_temp: ',
    ps()
    if n_ands() > 5*b[2]:
        return Undecided
    return simplify(1)

def try_temps(t=20):
    """ need to modify something to be able to update cex"""
    global smp_trace
    abc('w %s_try_temps.aig'%f_name)
    best = (n_pis(),n_latches(),n_ands())
    npi = n_pis()
    F = 1
    while True:
        res = try_temp(t)
        ps()
        if n_latches() == 0:
            break
        if res == False:
            return False,F
        if ((best == (n_pis(),n_latches(),n_ands())) or n_ands() > .9 * best[2] ):
            break
        else: #made progress
            smp_trace = smp_trace + ['tempor']
            aigs_pp('push','tempor')
            best = (n_pis(),n_latches(),n_ands())
    return True,n_pis()/npi
        
def rel_cost_t(J):
    """ weighted relative costs versus previous stats."""
    if (n_latches() == 0 and J[1]>0):
        return -10
    nli = J[0]+J[1]
    na = J[2]
    if ((nli == 0) or (na == 0)):
        return 100
    nri = n_real_inputs()
    #ri = (float(nri)-float(ni))/float(ni)
    rli = (float(n_latches()+nri)-float(nli))/float(nli)
    ra = (float(n_ands())-float(na))/float(na)
    cost = 10*rli + 1*ra #changed from .5 to 1 on ra
    return cost    

def rel_cost(J):
    """ weighted relative costs versus previous stats."""
    global f_name
    if (n_latches() == 0 and J[1]>0):
        return -10
    nri = n_real_inputs()
    ni = J[0]
    nl = J[1]
    na = J[2]
    if (ni == 0 or na == 0 or nl == 0):
        return 100
    ri = (float(nri)-float(ni))/float(ni)
    rl = (float(n_latches())-float(nl))/float(nl)
    ra = (float(n_ands())-float(na))/float(na)
##    cost = 1*ri + 5*rl + .25*ra  
    cost = 1*ri + 6*rl + .25*ra #temporary
##    print 'Relative cost = %0.2f'%cost
    return cost

def best_fwrd_min(J,t=30):
    global f_name, methods,smp_trace
    J=[18]+J
    mtds = sublist(methods,J)
    F = create_funcs(J,t)
    (m,result) = fork_best(F,mtds) #FORK here
    print '%s: '%mtds[m],
    smp_trace = smp_trace + ['%s'%mtds[m]]
    
def ind_syn():
    run_command('st;if;sop;ps -f;&get;&icheck -M 1; mfs2 -i -M 1000000 -W 100;ps -f')

def try_forward():
    """Attempts most forward retiming, and latch correspondence there. If attempt fails to help simplify, then we revert back to the original design
    This can be effective for equivalence checking problems where synthesis used retiming"""
    abc('w %s_savetemp.aig'%f_name)
    if n_ands() < 30000:
        abc('dr')
        abc('lcorr')
        nl = n_latches()
        na = n_ands()
        abc('w %s_savetemp0.aig'%f_name)
        abc('r %s_savetemp.aig'%f_name) 
        abc('dretime -m')
        abc('lcorr')
        abc('dr')
        if ((n_latches() <= nl) and (n_ands() < na)):
            print 'Forward retiming reduced size to: ',
            print_circuit_stats()
            return
        else:
            abc('r %s_savetemp0.aig'%f_name)
            return
    return

def qqsimp():
    abc('&get;&scl;,reparam;&scorr -C 0;&scl;,reparam;&put')
    shrink()
    abc('w %ssimp.aig'%f_name)
    ps()
    
def q_simp():
    abc('&get;&scl;&scorr -C 0;&scl;&put')
    print 'q_simp = ',
    ps()
    status = process_status(get_status())
    if status <= Unsat:
        return RESULT[status]
    else:
        return 'UNDECIDED'

def quick_simp():
    """A few quick ways to simplify a problem before more expensive methods are applied.
    Uses & commands if problem is large. These commands use the new circuit based SAT solver"""
    na = n_ands()
    if na < 60000:
        abc('scl -m;lcorr;drw')
    else:
        abc('&get;&scl;&lcorr;&put')
    if n_ands() < 500000:
        abc('drw')
    print 'Quick simplification = ',
    status = process_status(get_status())
    if status <= Unsat:
        result = RESULT[status]
    else:
        ps()
        result = 'UNDECIDED'
    return result

def scorr_constr():
    """Extracts implicit constraints and uses them in signal correspondence
    Constraints that are found are folded back when done"""
    global aigs
    if n_latches() == 0:
        return Undecided_no_reduction
    na = max(1,n_ands())
    n_pos_before = n_pos()
    if ((na > 40000) or n_pos()>1):
        return Undecided_no_reduction
    abc('w %s_savetemp.aig'%f_name)
    na = max(1,n_ands())
##    f = 1
    f = 40000/na  #**** THIS can create a bug 10/15/11. see below
    f = min(f,4)
    f = max(2,f)
    print 'Looking for constraints with -F %d - '%f,
    if n_ands() > 18000:
        cmd = 'unfold -s -F 2'
    else:
        cmd = 'unfold -F %d -C 5000'%f
    print cmd
    abc(cmd)
    ps()
    if n_pos() == n_pos_before:
        print 'no constraints found'
        return Undecided_no_reduction
    if (n_ands() > na): #no constraints found
        abc('r %s_savetemp.aig'%f_name)
        return Undecided_no_reduction
    na = max(1,n_ands())
##    f = 1 #put here until bug is fixed.
    print 'Found %d constraints'%((n_pos() - n_pos_before))
    abc('scorr -c -F %d'%f)
    abc('fold')
    res = a_trim()
##    print hist
    print 'Constrained simplification: ',
    ps()
    return Undecided_no_reduction

def a_trim():
    """ this is set up to put the aig on the aigs list if trim was successful
    we keep track of the aigs after a trim, so the we can undo the  trimming recursively until we get to
    the oritinal aig and make the cex compatible with this."""
##    print 'trimming'
##    print 5.1
    pushed = check_push() #checking if a push is needed and if so do it.
                        #It is not needed if flops match previous aig
##    print 5.2
    res = trim()
##    print 5.3
    if res:
        aigs_pp()
##        aigs.push() #store the aig after rpm if it did something
    elif pushed: #since trim did not do anything, we don't need the last push done by check push
        dump() #dump the last aig on the list
##    print 5.4
    return res

def try_scorr_c(f):
    """ Trying multiple frames because current version has a bug."""
    global aigs
    set_globals()
    abc('unfold -F %d'%f)
    abc('scorr -c -F %d'%f)
    abc('fold')
    t = max(1,.1*G_T)
    abc('&get;,bmc3 -vt=%f'%t)
    if is_sat(): 
        return 0
    else:
        res = a_trim()
##        print hist
        return 1
    

def input_x_factor():
    """Sets the global x_factor according to user input"""
    global x_factor, xfi
    print 'Type in x_factor:',
    xfi = x_factor = input()
    print 'x_factor set to %f'%x_factor


def prove(a=0,abs_tried = False):
    """Proves all the outputs together. If ever an abstraction
        was done then if SAT is returned,
        we make RESULT return "undecided".
        is a == 0 do smp and abs first
        If a == 1 do smp and spec first 
        if a == 2 do quick simplification instead of full simplification, then abs first, spec second
        if a == 3 do not do speculation
        """  
    global x_factor,xfi,f_name, last_verify_time,K_backup, t_init, sec_options, spec_found_cex
    print 'entering prove'
    spec_first = False
    set_max_bmc(-1,True)
    abs_found_cex_after_spec = spec_found_cex_after_abs = False
    if not '_smp' in f_name: #if already simplified, then don't do again
        if a == 2 : #do quick simplification
            result = quick_simp() #does not write 'smp' file
##            print result
        else :
            print 'entering prove_part_1'
            result = prove_part_1() #do full simplification here
            print 'prove_part_1 is done'
        if ((result == 'SAT') or (result == 'UNSAT')):
            return result
##    if n_latches() == 0:
##        return 'UNDECIDED'
        assert n_latches > 0, 'number of latches == 0'
    if a == 1:
        spec_first = True
    t_init = 2
    abs_found_cex_before_spec = spec_found_cex_before_abs = False
##    First phase
    if spec_first:
        print 'entering prove_part_3'
        result = prove_part_3() #speculation done here first
        if result == 'UNDECIDED' and abs_tried and n_pos() <= 2:
            add_trace('de_speculate')
            return result
        if abs_tried:
            return result
    else:
        abs_tried = True
        print 'entering prove_part_2'
        result = prove_part_2() #abstraction done here first
    if ((result == 'SAT') or (result == 'UNSAT') or a == 3):
        return result
##    Second phase
    if spec_first: #did spec already in first phase
        t_init = 2
        if not abs_tried:
            abs_tried = True
            print 'entering prove_part_2'
            result = prove_part_2() #abstraction done here second
            if result == 'SAT':
                abs_found_cex_after_spec = True
        else:
            return result
    else:
        print 'entering prove_part_3'
        result = prove_part_3()  #speculation done here second
        if result == 'SAT':
            if '_abs' in f_name:
                spec_found_cex_after_abs = True
            else:
                return result
    if result == 'UNSAT': 
        return result
    status = get_status()
    if result == 'ERROR':
        status = Error
    if ('_abs' in f_name and spec_found_cex_after_abs): #spec file should not have been written in speculate
        f_name = revert(f_name,1) #it should be as if we never did abstraction.
        print '^^^ f_name reverted to %s'%f_name
        add_trace('de_abstract')
##        print 'f_name = %s'%f_name
        abc('r %s.aig'%f_name) #restore previous
        t_init = 2
        if not '_rev' in f_name or not a == 3:
            print 'proving speculation first'
            write_file('rev') #maybe can get by with just changing f_name
            print 'f_name = %s'%f_name
            result = prove(1,True) #1 here means do smp and then spec but not abs
            if ((result == 'SAT') or (result == 'UNSAT')):
                return result
    elif ('_spec' in f_name and abs_found_cex_after_spec): #abs file should not have been written in abstract
        f_name = revert(f_name,1) #it should be as if we never did speculation.
        print '^^^ f_name reverted to %s'%f_name
        add_trace('de_speculate')
        abc('r %s.aig'%f_name) #restore previous 
        t_init = 2
        if not '_rev' in f_name:
            print 'proving abstraction first'
            write_file('rev') #maybe can get by with just changing f_name
            result = prove(0)
            if ((result == 'SAT') or (result == 'UNSAT')):
                return result
    else:
        return 'UNDECIDED'

def prove_part_1(frames_2=True):
    global x_factor,xfi,f_name, last_verify_time,K_backup,aigs
##    print 'Initial: ',
##    ps()
    x_factor = xfi
    set_globals()
##    abc('&get;&scl;&syn2;&put')
    abc('&get;&scl;&syn2;&scl;&put')
    print 'Initial quick simplified result: ',
    ps()
    if n_latches() > 0:
##        ps()
        res = False
        if frames_2:
            res = try_frames_2()
        if res:
            print 'frames_2: ',
            ps()
            aigs_pp('push','phase') #frames_2 is equivalent to 2 phase trasnform.
        print '\n***Running run_par_simplify with pre_simp'
        add_trace('run_par_simplify with pre_simp')
        result = run_par_simplify()
        print 'run_par_simplify is done'
        status = result[0]
        method = result[1]
        if 'scorr' in method: #run_par_simplify must have proved something
            add_trace(method)
            return RESULT[status]
    else:
        print '\n***Circuit is combinational, running check_sat'
        add_trace('comb_check')
        status = check_sat()
    if ((status <= Unsat) or (n_latches() == 0)):
        return RESULT[status]
    res =a_trim()
##    print hist
    if not '_smp' in f_name:
        write_file('smp') #need to check that this was not written in pre_simp
    set_globals()
    return RESULT[status]

def run_par_simplify():
    set_globals()
    t = 1000
    ps()
    funcs = [eval('(pyabc_split.defer(pre_simp)())')]
    J = [35]+pdrs[:3]+bmcs[:3]+intrps[:1]+sims  # 35 is par_scorr
    J = modify_methods(J,1)
    if n_latches() == 0:
        J = []
##    J = J + bestintrps
    funcs = create_funcs(J,t)+ funcs #important that pre_simp goes last
    mtds =sublist(methods,J) + ['PRE_SIMP']
    print 'methods run in parallel with initial simplify = ',str(mtds)
    i,result = fork_last(funcs,mtds)
    print 'fork_last is done'
    status = get_status()
    if result < 3:
        return [result,mtds[i]]
    return [status,mtds[i]]

def try_frames_2():
    abc('scl')
    nl = n_latches()
    if n_ands()> 35000:
        return False
    abc('w %s_temp.aig'%f_name)
    abc('&get;&frames -o -F 2;&scl;&put')
    if n_latches() < .75*nl:
        print 'Expanded to 2 frames per cycle: latches reduced to %d'%n_latches()
        add_trace('frames_2')
##        res = reparam()
##        handle this. I guess no need to do reparametrization here.
##      should do something about #PIs and depth of cex's
##        if res:
##            aigs.push()
        return True
    abc('r %s_temp.aig'%f_name)
    return False
    
def prove_part_2(ratio=.75):
    """does the abstraction part of prove"""
    global x_factor,xfi,f_name, last_verify_time,K_backup, trim_allowed,ifbip
    print'\n***Running abstract'
##    print 'ifbip = %d'%ifbip
    status = abstract(ifbip) #ABSTRACTION done here
    status = process_status(status)
    print 'abstract done, status is %s'%str(status)
    result = RESULT[status]
    if status < Unsat:
        print 'CEX in frame %d'%cex_frame()
        return result #if we found a cex we do not want to trim.
    return result
    
def prove_part_3():
    """does the speculation part of prove"""
    global x_factor,xfi,f_name, last_verify_time,init_initial_f_name
    global max_bmc, sec_options
##    if ((n_ands() > 36000) and sec_options == ''):
##        sec_options = 'g'
##        print 'sec_options set to "g"'
    print '\n***Running speculate on %s: '%f_name,
    ps()
##    add_trace('speculate')
    status = speculate() #SPECULATION done here
    status = process_status(status)
##    print 'speculate done, status is %d'%status
    result = RESULT[status]
    if status < Unsat:
        print 'CEX in frame %d'%cex_frame()
        return result
    return result

def prove_all(dir,t):
    """Prove all aig files in this directory using super_prove and record the results in results.txt
    Not called from any subroutine
    """
##    t = 1000 #This is the timeoout value
    xtime = time.time()
##    dir = main.list_aig('')
    results = []
    f =open('results_%d.txt'%len(dir), 'w')
    for name in dir:
        read_file_quiet_i(name)
        print '\n         **** %s:'%name,
        ps()
        F = create_funcs([18,6],t) #create timer function as i = 0 Here is the timer
        for i,res in pyabc_split.abc_split_all(F):
            break
        tt = time.time()
        if i == 0:
            res = 'Timeout'
        str = '%s: %s, time = %0.2f'%(name,res,(tt-xtime))
        if res == 'SAT':
            str = str + ', cex_frame = %d'%cex_frame()
        str = str +'\n'
        f.write(str)
        f.flush()
        results = results + ['%s: %s, time = %0.2f'%(name,res,(tt-xtime))]
        xtime = tt
##    print results
    f.close()
    return results  

def remove_pos(lst):
    """Takes a list of pairs where the first part of a pair is the PO number and
    the second is the result 1 = disproved, 2 = proved, 3 = unresolved. Then removes
    the proved and disproved outputs and returns the aig with the unresolved
    outputs"""
    proved = disproved = unresolved = []
    for j in range(len(lst)):
        jj = lst[j]
        if jj[1] == 2:
            proved = proved + [jj[0]]
        if (jj[1] == 1 or (jj[1] == 0)):
            disproved = disproved +[jj[0]]
        if jj[1] > 2:
            unresolved = unresolved +[jj[0]]
    print '%d outputs proved'%len(proved)
    if not proved == []:
        if ((max(proved)>n_pos()-1) or min(proved)< 0):
            print proved
        remove(proved,0)
            

#functions for proving multiple outputs in parallel
#__________________________________________________

def prove_only(j):
    """ extract the jth output and try to prove it"""
    global max_bmc, init_initial_f_name, initial_f_name, f_name,x
    #abc('w %s__xsavetemp.aig'%f_name)
    extract(j,j)
    set_globals()
    ps()
    print '\nProving output %d'%(j)
    f_name = f_name + '_%d'%j
    print '^^^ f_name changed to %s'%f_name
    result = prove_1()
    #abc('r %s__xsavetemp.aig'%f_name)
    if result == 'UNSAT':
        print '********  PROVED OUTPUT %d  ******** '%(j)
        return Unsat
    if result == 'SAT':
        print '********  DISPROVED OUTPUT %d  ******** '%(j)
        return Sat
    else:
        print '********  UNDECIDED on OUTPUT %d  ******** '%(j)
        return Undecided

def verify_only(j,t):
    """ extract the jth output and try to prove it"""
    global max_bmc, init_initial_f_name, initial_f_name, f_name,x, reachs, last_cex, last_winner, methods
##    ps()
##    print 'Output = %d'%j
    extract(j,j)
##    ps()
    set_globals()
    if n_latches() == 0:
        result = check_sat()
    else:
        f_name = f_name + '_%d'%j
        print '^^^ f_name changed to %s'%f_name
        # make it so that jabc is not used here
        reachs_old = reachs
        reachs = reachs[1:] #just remove jabc from this.
        res = verify(slps+sims+pdrs+bmcs+intrps,t) #keep the number running at the same time as small as possible.
##        res = verify(sims+pdrs+bmcs+intrps,t) #keep the number running at the same time as small as possible.
        reachs = reachs_old
        result = get_status()
        assert res == result,'result: %d, status: %d'%(res,get_status())
    if result > Unsat:
##        print result
##        print '******* %d is undecided ***********'%j
        return result
    elif result == Unsat:
##        print '******** PROVED OUTPUT %d  ******** '%(j)
        return result
    elif ((result < Unsat) and (not result == None)):
        print '******** %s DISPROVED OUTPUT %d  ******** '%(last_cex,j)
##        print ('writing %d.status'%j), result, get_status()
        abc('write_status %d.status'%j)
        last_winner = last_cex
        return result
    else:
        print '****** %d result is %d'%(j,result) 
        return result

def verify_range(j,k,t):
    """ extract the jth thru kth output and try to prove their OR"""
    global max_bmc, init_initial_f_name, initial_f_name, f_name,x, reachs, last_cex, last_winner, methods
    extract(j,k)
    abc('orpos')
    set_globals()
    if n_latches() == 0:
        result = check_sat()
    else:
        f_name = f_name + '_%d'%j
        print '^^^ f_name changed to %s'%f_name
        # make it so that jabc is not used here
        reachs_old = reachs
        reachs = reachs[1:] #just remove jabc from this.
        res = verify(sims+pdrs+bmcs+intrps,t) #keep the number running at the sme time as small as possible.
        reachs = reachs_old
        result = get_status()
        assert res == result,'result: %d, status: %d'%(res,get_status())
    if result > Unsat:
##        print result
##        print '******* %d is undecided ***********'%j
        return result
    elif result == Unsat:
##        print '******** PROVED OUTPUT %d  ******** '%(j)
        return result
    elif ((result < Unsat) and (not result == None)):
        print '******** %s DISPROVED OUTPUT %d  ******** '%(last_cex,j)
##        print ('writing %d.status'%j), result, get_status()
        abc('write_status %d.status'%j)
        last_winner = last_cex
        return result
    else:
        print '****** %d result is %d'%(j,result) 
        return result

def prove_n_par(n,j):
    """prove n outputs in parallel starting at j"""
    F = []
    for i in range(n):
        F = F + [eval('(pyabc_split.defer(prove_only)(%s))'%(j+i))]
    #print S
    #F = eval(S)
    result = []
    print 'Proving outputs %d thru %d in parallel'%(j,j+n-1)
    for i,res in pyabc_split.abc_split_all(F):
        result = result +[(j+i,res)]
    #print result
    return result

def prove_pos_par(t,BREAK):
    """Prove all outputs in parallel and break on BREAK"""
    return run_parallel([],t,BREAK)

def prove_pos_par0(n):
    """ Group n POs grouped and prove in parallel until all outputs have been proved"""
    f_name = initial_f_name
    print '^^^ f_name changed to %s'%f_name
    abc('w %s__xsavetemp.aig'%f_name)
    result = []
    j = 0
    N = n_pos()
    while j < N-n:
        abc('r %s__xsavetemp.aig'%f_name)
        result = result + prove_n_par(n,j)
        j = j+n
    if N > j:
        result = result + prove_n_par(N-j,j)
    abc('r %s__xsavetemp.aig'%initial_f_name)
    ps()
##    print result
    remove_pos(result)
    write_file('group')
    return

def prop_decomp():
    """decompose a single property into multiple ones (only for initial single output),
    by finding single and double literal primes of the outputs."""
    if n_pos()>1:
        return
    run_command('outdec -v -L 2')
    if n_pos()>1:
        ps()


def distribute(N,div):
    """
    we are going to verify outputs in groups
    """
    n = N/div
    rem = N - (div * (N/div))
    result = []
    for j in range(div):
        if rem >0:
            result = result +[n+1]
            rem = rem -1
        else:
            result = result + [n]
    return result    

        
def extract(n1,n2):
    """Extracts outputs n1 through n2"""
    no = n_pos()
    if n2 > no:
        return 'range exceeds number of POs'
    abc('cone -s -O %d -R %d'%(n1, 1+n2-n1))

def remove_intrps(J):
    global n_proc,ifbip
##    print J
    npr = n_proc
    if 18 in J:
        npr = npr+1
    if len(J) <= npr:
##        print J
        return J
    JJ = []
    alli = [23,1,22] # if_no_bip, then this might need to be changed
    if if_no_bip == True:
        alli=[23]
    l = len(J)-npr
    alli = alli[l:]
##    J.reverse() #strip off in reverse order.
    for i in J:
        if i in alli: 
            continue
        else:
            JJ = JJ+[i]
##    print JJ
    return JJ

def restrict(lst,v=0):
    '''restricts the aig to the POs in the list'''
    #this assumes that there are no const-v POs. Warning,
    #this will not remove any const-(~v) POs
    N = n_pos()
    lst_plus = lst + [N]
    print lst
    r_lst = gaps(lst_plus) #finds POs not in lst
    if len(r_lst) == N:
        return
    remove(r_lst,v)

##def rmv(lst,sublst):
##    """removes sublst from lst""" 
##    ret = []
##    for i in range(len(lst)):
##        if not lst[i] in sublst:
##            ret = ret + [i]
##    return ret
        
        



##def list_0_pos():
##    """ returns a list of const-0 pos and does not remove them
##    """
##    abc('w %s_savetemp.aig'%f_name)
##    L = range(n_pos())
##    L.reverse()
##    ll = []
##    for j in L:
##        i = is_const_po(j)
##        if i == 0:
##            abc('removepo -N %d'%j) #removes const-0 output
####            print 'removed PO %d'%j
##            ll = [j] + ll
##    abc('r %s_savetemp.aig'%f_name)
##    return ll

##def listr_1_pos():
##    """ returns a list of const-1 pos and removes them
##    """  
##    L = range(n_pos())
##    L.reverse()
##    ll = []
##    for j in L:
##        i = is_const_po(j)
##        if i == 1:
##            abc('removepo -z -N %d'%j) #removes const-1 output
####            print n_pos()
##            ll = [j] + ll
##    return ll


def unmap_cex():
    """ aig before trim is put in reg-space and after trim in the &space
        Before and after need to have same number of flops in order to do reconcile
        aigs list should be such that if before and after don't match in number of latches,
        then some operation changed the flops and we just update the aig with the new number
        reconcile leaves before aig in reg-space after cex has been updated so cex and aig
        always match
    """
    global aigs,hist
##    print hist
##    while not aigs == []:
    if len(hist)==0:
        print 'length of history is 0'
        size = str([n_pis(),n_pos(),n_latches(),n_ands()])
        print 'cex length = %d'%cex_frame()
        tr = ['cex length = %d'%cex_frame()] + ['cex matches original aig = %s'%size]
        print 'cex matches original aig'
        return tr
    while not len(hist) == 0:
        n = n_latches()
        abc('&get') #save the current aig in &-space
        print 'Number of PIs in cex = %d'%n_cex_pis()
        typ = aigs_pp('pop') #puts new aig in reg-space
        print typ,
        ps()
        if typ == 'undc':
            typ2 = aigs_pp('pop') #gets the aig before undc
            print typ2
            ps()
            run_command('&ps')
            run_command('undc -c')
            print 'Number of PIs in cex = %d, Number of frames = %d'%(n_cex_pis(),cex_frame())
            run_command('testcex -a')
            hist = hist + [typ2]
            continue
        if typ == 'phase':
            print 'before conversion'
            run_command('testcex') #tests cex against aig in &-space
            typ2 =aigs_pp('pop') #gets the aig before phase
            abc('phase -c') # -c means update the current CEX derived for a new AIG after "phase"
                             #to match the current AIG (the one before "phase") [default = no]
            print 'Number of PIs in cex = %d, Number of frames = %d'%(n_cex_pis(),cex_frame())
            print 'after conversion'
            run_command('testcex -a') #-a means that we test against the aig in the reg-space
            hist = hist + [typ2] # we do not want to change hist if phase or tempor was done
            continue
        if typ == 'tempor':
            typ2 = aigs_pp('pop') #gets the aig before tempor
            abc('tempor -c')
            print 'Number of PIs in cex = %d, Number of frames = %d'%(n_cex_pis(),cex_frame())
            run_command('testcex -a')
            hist = hist + [typ2]
            continue
        if typ == 'reparam':
            nn = n_latches()
            abc('&get') #put 'after' in &space
            typ2 = aigs_pp('pop') #get previous to put before in reg-space
            run_command('reconcile')
            print 'Number of PIs in cex = %d'%n_cex_pis()
##                reconcile(True) #maps the cex from &-space aig to current aig
            run_command('testcex -a')
            if not typ2 == 'reparam0':
                hist = hist + [typ2] #put back (aig iss still there so just have to restore hist
            continue
            #else we just leave the aig updated
        else:
            assert typ == 'initial','type is not initial'
            size = str([n_pis(),n_pos(),n_latches(),n_ands()])
            print 'cex length = %d'%cex_frame()
            tr = ['cex length = %d'%cex_frame()] + ['cex matches original aig = %s'%size]
            print 'cex matches original aig'
            return tr
##    print 'cex matches original aig'
        

""" _______________________running regressions ________________________"""

##def run(cmd='super_prove',ex,tag=None,t=900):
##    regression.run(cmd,ex,tag,None,t)

"""
to see arguments of regression.run, do help('regression.run' or any function)
"""
"""
cmds can be "super_prove" "multi_prove" "simple" "simple_sat" "simple_bip" "simple_live"

    regression.kill(tag)
    regression.remove(tag)
    regression.analyze(tags)
    regression.print_summary(tags)
To generate a scatter plot comparing two runs:
    regression.scatter_plot(tag1, tag2, png_file, timeout=None )
        This will write a scatter plot to a file whose name is png_file comparing the results of run_tag1 and run_tag2 with the supplied timeout. If timeout is None, it will use the minimum timeout of the corresponding runs, or if both runs were done without a timeout, the maximum run time of any of the properties.
Results are stored at
/hd/common/regression/runs/<tag> :
    benchmarks (the list of benchmarks used)
    log (the log file for the run script - should not be very interesting, just which benchmarks were run on which cores)
    status (started, killed, done, error)
    logs/
        <benchmark name>.log - the log file of the solver
_______________________________________
"""
                   
def avg(L):
    sum = 0
    if L == []:
        return 0
    for i in range(len(L)):
        sum = sum + L[i]
    return sum/len(L)

def sp(n=0,t=200001,check_trace=True): #check_trace = True for hwmcc15
    """Alias for super_prove, but also resolves cex to initial aig"""
    global initial_f_name
    check_trace = True #temp
    print '\n               *** Executing super_prove ***'
    print '%s: '%f_name,
    ps()
    # commented out because bmc3 does not handle timeout mechanism well. Need to fix.
##    b = bmc3(5)
##    get_bmc_depth(True)
##    if b == 'SAT':
##        result = ['SAT']+[['bmc3']]
##    else:
    if True:
        print 'entering super_prove'
        result = super_prove(n,t)
    print '%s is done and is %s'%(initial_f_name,result[0])
##    print 'sp: ',
##    print result
    if result[0] == 'SAT' and check_trace:
        abc('w %s_save.aig'%f_name)
        res = unmap_cex()
        result1 = result[1]+ res
        result = ['SAT'] + result1
        report_cex(1) #0 writes the unmapped cex into a cex file called init_initial_f_name_cex.status and 1 to stdout
##        abc('r %s_save.aig'%f_name)
    report_bmc_depth(max(max_bmc,n_bmc_frames()))
    return result

def report_cex(stdout = 0):
    if stdout:
        abc('write_cex /dev/stdout')
    else:
        abc('write_cex %s.cex'%init_initial_f_name)

#******************************** beginning of multi_prove stuff *********************************

def mp(opos=[]):
    multi_prove_iter(opos)


def sp_iter(t=200,L=[],globs=[[],[],[],[],0,[]],opo=[]):
    """if n == 0 do smp and abs first, then spec
    if n == 1 do smp and spec first then abs
    if n == 2 just do quick simplification instead of full simplification, then abs first, spec second
    c means check the cex trace
    if_sp ==> use super_prove. May change aig
    """
    global f_name
    global init_initial_f_name, methods, last_verify_time,f_name,last_gasp_time
    last_gasp_time = t
    if opo == []:
        opo = range(n_pos())
    assert len(opo) == n_pos(),str((n_pos(),opo))
    tt = time.time()
    LL=list(L)
    pos = [i for i in xrange(len(LL)) if LL[i] == -1] #create a list of unsolved POs relative to L
##    assert len(LL) == n_pos(), 'len(L) and n_pos are different'
    opop = list(opo)
    print 'sp_iter - unproved POs: ',str(opop)
    POs = list(pos)
    f_name_iter = f_name = '%s_spiter'%f_name
    print '^^^ Temporary f_name = %s'%f_name 
    abc('w %s_init.aig'%f_name_iter) # will restore this on exit from sp_iter.
    if not n_pos() == len(pos):
        print 'sp_iter_init before: ',str(ps())
        remove_proved_pos(LL)
        print 'sp_iter_init after: ',str(ps())
    assert n_pos() == len(pos), 'npos = %d, lenpos = %d'%(n_pos(),len(pos))
    abc('scl')
    abc('w %s.aig'%f_name_iter)
    times = []
    told = time.time()
    abc('bmc3 -T 5')
    cxf = n_bmc_frames()+1 #used for estimating where to start bmc
    while True:
        ps()
        cexframe = cxf
##        DL=output2(list(L),globs) #length error here
        print '\n*** estimated next bmc cex_frame = %d ***'%cexframe
        #here in sp_iter we try several jumped bmcs and simple and might try sp
        result = par_bss(t,cexframe-1) #here we try to find more SAT POs
        print 'sp_iter: ',result
        jmp = result[1] == 'bmcjmps'
##        print POs
        if result[0] == 'SAT' or result[0] == 0:
##            assert cexpo == cex_po(), 'cexpo,cex_po() = %d,%d'%(cexpo,cex_po())
            print 'cex_po(), opop: ' , cex_po(),opop
            # here in sp_iter we should report new results using output2?
            if jmp:
                cxf = cex_frame()
            else: #simple got it so not reliable depth
                cxf = min(cxf+1,cex_frame())
##            cx = cex_po()
            cx =cex_po()
            
            assert cx <len(POs) and cx > -1,'cx = %d'%cx
            px = POs[cx] #mapped into associated PO of L2 (=LL)
            ocx = opop[cx]
            print 'cx,px,opop: ', str((cx,px,ocx))
            assert px < len(LL),'px = %d, len(LL) = %d'%(px,len(LL))
            assert LL[px] == -1,'px = %d, LL[px] = %d'%(px,LL[px])
            LL[px] = 1
##            print LL[px]
            #temp
            print 'output %d is SAT'%ocx
            print 'LL = ',str(LL)
            # disabled because it causes a length error here
##            DL=output2(list(LL),globs) #outputs a new result Trying it again to see if error has gone away
            if not -1 in LL: #all POs are proved.
                print 'all POs have been proved.',
                print sumsize(LL)
                break
            assert px in POs,'px not in POs'
            i = POs.index(px)
            print i
            
            POs = POs[:i]+POs[i+1:] #eliminates ith element from list - just proved
            print 'Pos = ',str(POs)
            opop = opop[:cx] + opop[cx+1:]
            print 'opop = ',str(opop)
            abc('r %s.aig'%f_name_iter) #temp, done to reset status
##            abc('restore')
##            assert n_pos() > 1,'n_pos() = %d'%n_pos()
            if n_pos() == 1: #all POs have been processed and found SAT
                print 'exiting sp_iter. Can not remove the only remaining PO'
                break
            abc('zeropo -N %d;removepo -N %d'%(cx,cx)) # remove that PO from aig
            abc('scl') #do more simplification here?
##            abc('backup')
            abc('w %s.aig'%f_name_iter) #done so sp can back up to correct start if necessary
            f_name = f_name_iter #done if sp changed f_name
            print '^^^ f_name restored as %s'%f_name
            tnew = time.time()
            times = [tnew - told] + times
            told = tnew
            lp = min(5,len(times))
            print 'times = ',['%.1f'%times[i] for i in xrange(lp)]
            if len(times) >= 5: #check if for last 5 avg(delta_t) > t/2
##                print 'times = ',['%.1f'%times[i] for i in xrange(5)]
                if min(times[:5]) > 50 or avg(times[:3]) >= 100: #taking too long on remaining POs
                    print 'Timing out in sp_iter'
##                    print 'times = ',['%.1f'%times[i] for i in xrange(5)]
                    break
        elif result[0] == 'UNSAT' or result[0] == 2:
            print 'all remaining POs proved unsat'
            for i in range(len(LL)):
                if LL[i] == -1:
                    LL[i] = 0
##            DL = output2(list(LL),globs)
            opop = []
            print 'LL = ',str(LL)
            break
        else: # we can't prove anything more in the time allowed
            print 'result is neither SAT nor UNSAT'
            print 'LL = ',str(LL)
            break
    abc('r %s_init.aig'%f_name_iter) #restoring initial aig when entering
    f_name = f_name_iter #
    print '^^^ f_name restored as %s'%f_name
    print 'time used in sp_iter = %0.2f'%(time.time() - tt)
    return LL


def sumsize(L):
    d = count_less(L,0) #undecided L=-1 means undecided, L=0 means unsat, L=1 means sat
    u = count_less(L,1)-d #unsat
    s = count_less(L,2) - (d+u) #sat
    return 'SAT = %d, UNSAT = %d, UNDECIDED = %d'%(s,u,d)

def unmap(L,L2,mp):
    """ used in multiprove"""
    if mp == []:
        return L
    mx = max(mp)
##    assert len(map) == len(L2),'len(mp) = %d, len(L2) = %d'%(len(map),len(L2))
    assert mx < len(L),'max of map = %d, length of L = %d'%(mx,len(L))
    for j in range(len(mp)):
        L[mp[j]] = L2[j] #expand results of L2 into L
    return L

def unmap2(L2,mp):
    mx = max(list(mp))
    assert mx < len(L2),'max of map = %d, length of L2 = %d'%(mx,len(L2))
    L=[-1]*len(mp)
    for j in range(len(mp)):
        L[j] = L2[mp[j]] #expand results of L2 into L
    return L 

def create_map(L,N):
    """ map equivalence classes into their representative."""
##    print L
    mapp = [-1]*N
    m = -1
    error = False
    for j in range(len(L)):
        lj = L[j] # jth equivalence class
        for k in range(len(lj)):
            mapp[lj[k]] = j #put j in those positions
##        print lj
        mm = min(lj)
##        print mm
        if not mm == lj[0]: #check if rep is not first on list
            print 'ERROR: rep is not first, mm = %d, lj[0] = %d'%(mm,lj[0])
            error = True
        if mm <= m: #check if iso_classes are in increasing order of representatives.
            print 'ERROR: in iso map mm < m, mm = %d, m = %d'%(mm,m)
            error = True
        m = mm
    assert not error,'ERROR'
    return mapp


def weave(L1,lst0,lst1):
    """ interleave values of L1 and with 1's in positions given in lst1,
        and 0's in lst0. It is assumed that these lists are in num order..
        Final list has len = len(L1)+len(lst0)+len(lst1)"""
    L = [-1]*(len(L1)+len(lst0)+len(lst1))
##    print len(L)
    if lst0 == []:
        if lst1 == []:
            return L1
        lst = lst1
        v = 1
    if lst1 == []:
        lst = lst0
        v = 0
    l = k = 0
    for j in range(len(L)):
##        print L
        if j == lst[l]:
            L[j] = v
            if l+1 < len(lst):
                l = l+1
        else: #put in value in L1
            L[j] = L1[k]
            if k+1 < len(L1):
                k = k+1
    return L

##def quick_mp(t):
##    t1 =time.time()
##    l1 = list_v_pos(v=0)
##    S,l2,s = par_multi_sat(t)
##    l2 = indices(s,1)
##    remove(l2,1)
##    abc('scl')
##    simple()#does simplification first
##    ps()
##    print'time = %0.2f'%(time.time() - t1)

def indices(s,v):
    """return in indices of s that have value v"""
    L = []
    for i in range(len(s)):
        if s[i]== v:
            L = L+[i]
    return L

def expand(s,ind,v):
    """expand s by inserting value v at indices ind of expanded s"""
    N = len(s)+len(ind)
    ind1 = ind+[N]
    g = gaps(ind1) 
    ss = [-1]*N
    for i in ind:
        ss[i] = v
    j = 0
    for i in g: #put original values in ss
        ss[i] = s[j]
        j = j+1
    for j in ind:
        assert ss[j] == v, 'ss = %s, ind = %s'%(str(ss),str(ind))
    return ss

def remove_v(ss,v):
    """ removes from ss those that have value v"""
    s = []
    for i in range(len(ss)):
        if ss[i] == v:
            continue
        else:
            s = s + [ss[i]]
    return s
                 
def multi_prove(op='simple',tt=2001,n_fast=0, final_map=[], opos=[]):
    """two phase prove process for multiple output functions"""
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time
    global f_name_save,nam_save,_L_last,file_out, pos_sat, pos_unsat
##    global map1g,map2g,lst0g,lst1g,NPg,final_mapg
    print
    NP=1
    pos_sat = []
    pos_unsat = []
    x_init = time.time()
    abc('backup')
    npos_old = n_pos()
    npis_old = n_pis()
    if opos == []:
        opos = range(n_pos())
    print 'PO names = ',str(opos)
    abc('&get;&scl;&put')
    if not n_pos() == npos_old or not n_pis() == npis_old:
        print 'there was a change in n_pos or n_pis due to &scl. Restore original aig.'
        abc('restore')
##    xa('&get,reparam -aig=%s_rpm.aig; r %s_rpm.aig')
    print 'Initial after &scl',
    ps()
    abc('w %s_initial_save.aig'%init_initial_f_name)
    #handle single output case differently
    _L_last = [-1]*n_pos() #non solved yeet
    
    if n_pos() == 1:
        result = super_prove(2001)
##        abc('w %s_unsolved.aig'%init_initial_f_name)
        rs=result[0]
        if rs == 'SAT':
            report_result(0,1)
            L = [1]
            pos_sat = pos_sat + [opos[0]]
            print opos[0]
            pos_sat = remove_dup(list(pos_sat))
            print 'pos_sat = %s'%str(pos_sat)
        elif rs == 'UNSAT':
            report_result(0,0)
            L = [0]
            pos_unsat = pos_unsat + [opos[0]]
            pos_unsat = remove_dup(list(pos_unsat))
            print 'number of pos_unsat = %s'%str(len(pos_unsat))
        elif rs == 'UNDECIDED':
            report_result(0,-1)
            L = [-1]
        else: #error
            L = [2]
        res = sumsize(L)
        rr = '\n@@@@ %s: Time =  %d '%(init_initial_f_name,(time.time() - t_iter_start)) + res
##        rr = '%s: '%init_initial_f_name + rr
##        print rr
        file_out.write(rr+ '\n')
        file_out.flush()
        return L
    
##    print 'Removing const-0 POs'
    NNN = n_pos()
    lst0 = []
##    lst0 = listr_v_pos(v=0) #   **** Temp disabled. remove const-0 POs and record
##    print lst0
    lst0.sort()
    N = n_pos()
    L = [-1]*N     
    print 'Removed %d const-0 POs'%len(lst0)
    
    tlst = [opos[lst0[i]] for i in range(len(lst0))] #tlst0 used later for expand to
    tlst0 = list(tlst)                                                  #expand back to original PO numbering
    pos_unsat = pos_unsat + tlst0
    print 'pos_unsat = %s'%str(len(pos_unsat))
    print 'Removed UNSAT POs: %s'%str(tlst)
    opos = remove_sub(list(opos),tlst)
    assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())

    res = 'SAT = 0, UNSAT = %d, UNDECIDED = %d'%(len(lst0),N)
    rr = '\n@@@@ %s: Time =  %.2f: '%(init_initial_f_name,(time.time() - t_iter_start))
    report_L(tlst,0) ##########
    print 'new unsats = ',str(tlst)
    rr = rr + res
##    rr = '%s: '%init_initial_f_name + rr
    print rr
    file_out.write(rr + '\n')
    file_out.flush()
    ttt = n_ands()/1000
    if ttt < 10:
        ttt=10
    elif ttt<20:
        ttt = 20
    elif ttt< 30:
        ttt = 30
    else:
        ttt = 50
    S,dump,s = par_multi_sat(ttt,1,1,1,list(opos)) #run engines in parallel looking for SAT outputs.
    # Here lst1 is not used
    remove_all = not -1 in s #indicates if all solved
    lst1 = indices(s,1)# these are the SAT POs found - local variables.
    
##
    if not remove_all:
##        print S,lst1
        #put 0 values into lst0. Should this be in original PO numbering
        lst10 = indices(s,0) #new unsat POs in local indices (with lst0 removed)
    ##    if not lst10 == []:
    ##        print 'lst10 = %s'%str(lst10)
        lst11 = indices(s,1) # new sat POs, local variables
        assert -1 in s, 'remove_all should be True'
        ss = expand(s,tlst0,0) #ss will reflect original indices
        report_s(ss)

        lst0_old = list(lst0)
        lst0 = indices(ss,0) #additional unsat POs added to initial lst0 (in original indices)
    ##    print 'lst0 = %s'%str(lst0)
        
        assert len(lst0) == len(lst0_old)+len(lst10), 'lst0 = %s, lst0_old = %s, lst10 = %s'%(str(lst0),str(lst0_old),str(lst10))
        sss = remove_v(ss,0) #remove the 0's from ss. sss is shorter by numberr of 0's in ss. So sss has no 0's
        assert len(sss) == len(ss)-len(lst0), 'len(sss) = %d, len(ss) = %d, len(lst0) = %d'%(len(sss),len(ss),len(lst0))
        lst1_1 = indices(sss,1) #The sats now reflect the new local indices.
                    #It makes it as if the newly found unsat POs were removed initially
                    #done with new code
        assert len(lst1_1) == len(lst1), 'mismatch, lst1 = %d, lst1_1 = %d'%(len(lst1),len(lst1_1))
        lst1 = list(lst1_1) #lst1 should be in original minus lst0
    ##    print 'Found %d SAT POs'%len(lst1)
    ##    print 'Found %d UNSAT POs'%len(lst10)
        res = 'SAT = %d, UNSAT = %d, UNDECIDED = %d'%(len(lst1),len(lst0),NNN-(len(lst1)+len(lst0)))
    ##    rr = '\n@@@@ Time =  %.2f: '%(time.time() - t_iter_start)
        rr = '\n@@@@ %s: Time =  %.2f: '%(init_initial_f_name,(time.time() - t_iter_start))
        print 'In multi_prove, after par_multi_sat: ',rr,res
        file_out.write(rr + res + '\n')
        file_out.flush()
        N = n_pos()
    ##    print len(lst10),n_pos()
        if not len(lst10) == n_pos() and len(lst10) > 0:
            print 'n_pos,len(opos) = ',(N,len(opos))
            print 'removing lst10' #not original POs
            remove(lst10,0) #remove 0 POs (puts 0 in lst10 and removes all 0 POs in aig)
            #hopefully, par_multi_sat found them already and put them in lst10.
            print 'Removed %d UNSAT POs'%len(lst10) #not original POs
            N = n_pos()
            print 'n_pos,len(opos) = ',(N,len(opos))
            print 'lst10 = ',lst10
            tlst0 = [opos[lst10[i]] for i in range(len(lst10))]
            pos_unsat = pos_unsat + tlst0
            pos_unsat = remove_dup(list(pos_unsat))
            print 'number of pos_unsat = %s'%str(len(pos_unsat))
            
            print 'tlst0 = ',tlst0
            print 'opos = ',opos
            opos = remove_sub(list(opos),tlst0) #opos shortened
            print 'opos = ',opos
            print 'n_pos,len(opos) = ',(N,len(opos))
            assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())
        elif len(lst10) == n_pos():
            remove_all = True #can't physically remove all POs in an AIG.
            #Must proceed as if there are no POs. But all POs are UNSAT.
    ##    print len(lst1),N,S #note: have not removed the lst1 POs.
            
    if remove_all or len(lst1) == N or S == 'UNSAT' or N == 0: #all POs are solved
        L = [0]*N #could just put L as all 1's. If N = 0, all POs are UNSAT and lst1 = []
        for i in range(len(lst1)): #put 1's in SAT POs
            L[lst1[i]]=1
        L = weave(list(L),lst0,[]) #expand L, and put back 0 in L. 
        report_results(list(L)) #L in original POs in 0,1,-1 format
        print sumsize(L)
        print 'Time = %.2f'%(time.time() - x_init) 
        return L
    
##    print 'removing them'
    if not len(lst1)== n_pos():
        print 'removing lst1'
        remove(lst1,1) #here we removed all POs in lst1 (local indices)
        tlst1 = [opos[lst1[i]] for i in range(len(lst1))] #translated lst1
        pos_sat = pos_sat + tlst1
        print 'tlst1 = %s'%str(tlst1)
        pos_sat = remove_dup(list(pos_sat))
        print 'pos_sat = %s'%str(pos_sat)
##        print 'tlst1 = ',tlst1
##        tlst1 = [opos[lst1[i]] for i in range(len(lst1))]
        opos = remove_sub(list(opos),tlst1)
        assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())
        abc('&get;&scl;&put')
    ##    lst1 = bmcj_ss_r(2) #find easy cex outputs
    ##    write_file('bmc1')
        print 'Removed %d SAT POs'%len(lst1)
        N = n_pos()
    else:
        N = 0
    if N == 1: #this was wrong. Need to report in original indices???
        result = super_prove(2001)
        rs=result[0]
        #need to find out original index of remaining PO
        if rs == 'SAT':
            v = 1
        elif rs == 'UNSAT':
            v = 0
        elif rs == 'UNDECIDED':
            v = -1
        else: #error should not happen, but be conservative
            v = -1
        L = [v]*N
        L = weave(list(L),[],lst1) #put back 1 in L
        L = weave(list(L),lst0,[]) #put back 0 in L
        report_results(list(L)) #L in original POs in 0,1,-1 format
        res = sumsize(L)
        rr = '\n@@@@ Time =  %d '%(time.time() - t_iter_start) + res
        rr = '%s: '%init_initial_f_name + rr
        print rr
        file_out.write(rr+ '\n')
        file_out.flush()
        return L

    # Do iso here if problem is not too big
    did_iso_1 = False
    L = [-1]*N
    L1 = list(L)
    if N > 1 and N < 10000 and n_ands() < 500000: #keeps iso in
##    if N > 1 and N < 10000 and False: #*************temporarily disable iso
        res = iso() # We do Isomorphisms here. Can reduce number of POs
        print 'First isomorphism: ',res
        if res == True:
            did_iso_1 = True
            abc('&get;&scl;&put')
            write_file('iso1')
            leq = eq_classes()
##        print leq
            map1 = create_map(leq,N) #creates map into original if there were isomorphisms
##        print map1
            if not count_less(L,0) == N:
                print 'L = %s'%sumsize(L)
            L1 = [-1]*n_pos()
##        L1 = pass_down(L,list(L1),map1) # no need to pass down because L will have no values at this point.
        else:
            map1 =range(N)
    else: #didn"t do iso
        map1 = range(N)
    N = n_pos()
##    print 4
    r = pre_simp(1) #pre_simp 1 here make it not use phase.
    write_file('smp1')
##    NP = n_pos()/N #if NP > 1 then NP unrollings were done in pre_simp.
    if r[0] == Unsat: #all remaining POs are Unsat
        L1 = [0]*N 
        L = unmap2(L1,map1)
        L = weave(list(L),[],lst1) #put back 1 in L
        L = weave(list(L),lst0,[]) #put back 0 in L
        print sumsize(L)
        print 'Time = %.2f'%(time.time() - x_init)
        report_results(list(L)) #L in original POs in 0,1,-1 format
        return L
    
    f_name_save = f_name
    nam_save = '%s_initial_save.aig'%f_name
    #########do second iso here
    N = n_pos()
    if N == 1:
        map2 = [0]
        L2=[-1]
##        write_file('1')
##        L = output(list(L),list(L1),L2,map1,map2,lst0,lst1,NP)
        g = [map1,map2,lst0,lst1,NP,[]]
        L = output2(list(L2),g)
        uns = indices(L,-1)
        if not uns == pos:
            print 'uns and pos are not equal'
            print 'uns = ',uns
            print 'opos = ',pos
        result = simple(2001,1) # 1 here means do not do simplification first
        Ss = rs = result[0]
        if rs == 'SAT':
            L2 = [1]
            pos_sat = pos_sat + [opos[0]]
            print opos[0]
            pos_sat = remove_dup(list(pos_sat))
            print 'pos_sat = %s'%str(pos_sat)
        if rs == 'UNSAT':
            L2 = [0]
            pos_unsat = pos_unsat + [opos[0]]
            pos_unsat = remove_dup(list(pos_unsat))
            print 'pos_unsat = %s'%str(len(pos_unsat))
    else: #more than 1 PO left
##        if False and N < 10000: #temp disable iso
        if N < 10000 and n_ands() < 500000: 
            res = iso() #second iso - changes number of POs
            print 'Second isomorphism: ',res
            did_iso_2 = res
            if res == True:
                abc('&get;&scl;&put')
                map2 = create_map(eq_classes(),N) #creates map into previous
                write_file('iso2')
            else:
                map2 = range(n_pos())
        else:
            map2 = range(n_pos())
        
        print '*******************entering par_multi_sat**********************'
        abc('w %s_L2.aig'%init_initial_f_name)
        S,dump,L2 = par_multi_sat(2*ttt,1,1,1,opos) #look for SAT POs
        # L2 set here and has same length as n_pos here
        lmbc1 = indices(L2,1)
        lmbc0 = indices(L2,0)
##        lst = [i for i in range(len(L2)) if L2[i]>-1]
##        tlst = [opos[lst[i]] for i in range(len(lst))]
##        opos = remove_sub(list(opos),tlst)
        print '******************par_multi_sat ended**************************'
        
        if len(lmbc0)>0 or len(lmbc0)>0:
            print 'found %d SAT POs'%len(lmbc1)
            print 'found %d UNSAT POs'%len(lmbc0)
            pos_sat = pos_sat + [opos[i] for i in lmbc1]
            print [opos[i] for i in lmbc1]
            pos_sat = remove_dup(list(pos_sat))
            print 'pos_sat = %s'%str(pos_sat)
            pos_unsat = pos_unsat + [opos[i] for i in lmbc0]
            pos_unsat = remove_dup(list(pos_unsat))
            print 'number of pos_unsat = %s'%str(len(pos_unsat))
##        L2 = s #first mention of L2 except in single PO case (N=1)
##        #first mprove for 10-20 sec.
        ps()
        print 'Before first mprove2, L2 = %s'%sumsize(L2)
        g = [map1,map2,lst0,lst1,NP,[]] #map1 is due to first isomorphism and map2 due to the second,
        # NP is due to phase abstraction, lst0 and lst1 are 
        L = output2(list(L2),g) #reporting intermediate results in 0,1,-1 format
        remain = []
        uns = indices(L,-1)
##        if not uns == opos:
##            print 'uns and opos are not equal'
##            print 'uns = ',uns
##            print 'opos = ',opos
##        print 'opos - len(opos), opos = ',len(opos),opos
        
##        DDL = output3(range(len(L2)),map1,map2,lst0,lst1,NP)
##        print 'DDL = %s'%str(DDL)
        if n_fast == 1:
            return L
        NN=n_ands()
        ttt = 100
        print 'Entering first mprove2 for %d sec.'%ttt
        print 'opos: ',str(opos)
        g = [map1,map2,lst0,lst1,NP,[]]
        Ss,L2,opo = mprove2(list(L2),op,ttt,1,g,list(opos)) #populates L2, sp_iter is done here
        print 'multi_prove: mprove2 is done'
        print 'opo: ',str(opo)
        print 'L2: ',str(L2)
    
        abc('r %s_L2.aig'%init_initial_f_name)

        #opos = report(list(opos),list(L2))?
##        if 1 in ss or 0 in ss #something solved
##            if -1 in ss: #not all solved
##                rem0 = indices(ss,0)
##                rem1 = indices(ss,1)
##                rem = rem0+rem1
##                rem.sort()
##                if not len(rem) == n_pos():
##                  print 'Removing %d POs'%len(rem)
##                  remove(rem,1)
##                  tlst1 = [opos[rem1[i]] for i in range(len(rem1))]
##                  tlst0 = [opos[rem0[i]] for i in range(len(rem0))]
##                  pos_sat = pos_sat + tlst1
##                  pos_unsat = pos_unsat + tlst1
##                  opos = remove_sub(list(opos),(tlst1+tlst0))
##                  assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())
##        abc('w %s_unsolved.aig'%init_initial_f_name) #update unsolved

        opos = report(list(opos),list(L2))
        
##        remove_proved_pos(L2) #here n_pos will differ from len(L2)
##        #proved POs - remove from opos list
##        lst1 = [i for i in range(len(L2)) if L2[i]==1]
##        lst0 = [i for i in range(len(L2)) if L2[i]==0]
##        rem = lst1+lst0
##        rem.sort
##        tlst1 = [opos[lst[i]] for i in range(len(lst1))]
##        pos_sat = pos_sat + tlst1
##        tlst0 = [opos[lst[i]] for i in range(len(lst0))]
##        pos_unsat = pos_unsat + tlst1
##        opos = remove_sub(list(opos),(tlst1+tlst0))
####        assert opo == opos,'opo = %s, opos = %s '%(str(opo),str(opos))
##        if not len(opos) == 0: 
##            assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())
##        print 'writing unsolved file with n_pos = %d'%n_pos()
##        abc('w %s_unsolved.aig'%init_initial_f_name)
        
##        if Ss == 'SAT':
##            print 'At least one PO may be SAT'
            
        if Ss == 'ALL_SOLVED':
            if count_less(L2,0)>0:
                print 'ERROR'
##            L = output(list(L),list(L1),L2,map1,map2,lst0,lst1,NP) # final report of results.
            g = [map1,map2,lst0,lst1,NP,[]]
            L = output2(list(L2),g)
            uns = indices(L,-1)
            if not uns == opos:
                print 'uns and opos are not equal'
                print 'uns = ',uns
                print 'opos = ',opos
            return L
        
        print 'After first mprove2: %s'%sumsize(L2)
        
    time_left = tt - (time.time()-x_init)
    N_unsolved = count_less(L2,0)
    if N_unsolved > 0 and n_fast == 0:
        g = [map1,map2,lst0,lst1,NP,[]]
        L = output2(list(L2),g)
        uns = indices(L,-1)
        if not uns == opos:
            print 'uns and opos are not equal'
            print 'uns = ',uns
            print 'opos = ',opos
        t = max(100,time_left/N)
        t_all = 100
    S = sumsize(L2)
    T = '%.2f'%(time.time() - x_init)
    print '%s in time = %s'%(S,T)
    N = n_pos()
    ttime = last_gasp_time #RKB: temp
    J = slps+intrps+pdrs+bmcs+sims
    #do each output for ttime sec.
    
    if N_unsolved > 0:
        # entering end game. Doing
        #1. sp
        #2. par_multi_sat for a long time,
        #3. scorr_easy
        #4. simple on each PO cone if unproved < 20, else sp_iter.
        #5. simple for long time
##        assert N_unsolved == n_pos(),'len N_unsolved not = n_pos',str(N_unsolved,n_pos())
        found_sat = False
##        print 'final_all = %d, Ss = %s'%(final_all,str(Ss))
        
        if (final_all and not found_sat) or N_unsolved == 1:
            print 'Trying to prove all %d remaining POs at once with super_prove'%N_unsolved
            #simplify here?
            #unsolved.aig is always updated to contain only unsolved POs
            result = super_prove() #RKB put in sp_iter here because it would also find PO that is SAT?
            r0 = result[0]
            if r0 == 'UNSAT' or (r0 == 'SAT' and N_unsolved == 1): #all remaining POs are UNSAT
                for i in range(len(L2)):
                    if L2[i] < 0:
                        if r0 == 'UNSAT':
                            L2[i] = 0
                        if r0 == 'SAT':
                            L2[i] = 1
##                L = output(list(L),list(L1),L2,map1,map2,lst0,lst1,NP) # final report of results. 
                g = [map1,map2,lst0,lst1,NP,[]]
##                print ' entering final reporting 1'
                L = output2(list(L2),g)
                uns = indices(L,-1)
                if not uns == opos:
                    print 'uns and opos are not equal'
                    print 'uns = ',uns
                    print 'opos = ',opos
                return L
            if r0 == 'SAT': #N_unsolved >1. Did super_prove but do not know which PO was hit
                found_sat = 1
        
        if found_sat or not final_all: #RKB do something here with pdraz
            map3 = [i for i in xrange(len(L2)) if L2[i] == -1] #map from unsolved to L2
            ttime = 100
            #first try par_multi_sat hard (5*ttime)
            print 'Trying par_multi_sat for %.2f sec.'%(5*ttime)
            SS,LL,ss3 = par_multi_sat(5*ttime) #this causes gap = ttime
            if 1 in ss3: #we found a sat PO - reset_found_sat
                found_sat = 0
            abc('r %s_unsolved.aig'%init_initial_f_name)
            opos = report(list(opos),list(ss3)) # xxxxread ?
            
##            if 1 in ss3 or 0 in ss3: #something solved 
##                if -1 in ss3: #not all solved
##                    rem0 = indices(ss3,0)
##                    rem1 = indices(ss3,1)
##                    rem = rem0+rem1
##                    rem.sort()
##                    if not len(rem) == n_pos():
##                        print 'Removing %d POs'%len(rem)
##                        remove(rem,1)
##                        tlst1 = [opos[rem1[i]] for i in range(len(rem1))]
##                        tlst0 = [opos[rem0[i]] for i in range(len(rem0))]
##                        pos_sat = pos_sat + tlst1
##                        pos_unsat = pos_unsat + tlst1
##                        opos = remove_sub(list(opos),(tlst1+tlst0))
##                        assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())
##                        abc('w %s_unsolved.aig'%init_initial_f_name) #update unsolved
            
            L2 = unmap(list(L2),ss3,map3) #inserts the new values in the proper place in L    
            g = [map1,map2,lst0,lst1,NP,[]]
            L = output2(list(L2),g)
            uns = indices(L,-1)
            if not uns == opos:
                print 'uns and opos are not equal'
                print 'uns = ',uns
                print 'opos = ',opos
            #put scorr here for easy unsat's. create map3 again and use as above.
                
            print 'trying scorr_easy'
            if -1 in L2:
                map4 = [i for i in xrange(len(L2)) if L2[i] == -1] #map from unsolved to L2
                        #scorr_easy works on reduced aig
                ss4 = scorr_easy() #ss refers to current POs. Have to map up to POs before map3
                if 1 in ss4:
                    found_sat = 0 # reset found_sat to 0
                abc('r %s_unsolved.aig'%init_initial_f_name)
                opos = report(list(opos),list(ss4))
                
##                if 1 in ss4 or 0 in ss4: #something solved
##                    if -1 in ss4: #not all solved
##                        rem0 = indices(ss4,0)
##                        rem1 = indices(ss4,1)
##                        rem = rem0+rem1
##                        rem.sort()
##                        if not len(rem) == n_pos():
##                            print 'Removing %d POs'%len(rem)
##                            remove(rem,1)
##                            tlst1 = [opos[rem1[i]] for i in range(len(rem1))]
##                            tlst0 = [opos[rem0[i]] for i in range(len(rem0))]
##                            pos_sat = pos_sat + tlst1
##                            pos_unsat = pos_unsat + tlst1
##                            opos = remove_sub(list(opos),(tlst1+tlst0))
##                            assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())
##                            abc('w %s_unsolved.aig'%init_initial_f_name) #update unsolved
            
                L2 = unmap(L2,ss4,map4) #inserts the new values in the proper place in L2
                g = [map1,map2,lst0,lst1,g,[]]
                L = output2(list(L2),g)
                uns = indices(L,-1)
                if not uns == opos:
                    print 'uns and opos are not equal'
                    print 'uns = ',uns
                    print 'opos = ',opos
            print 'trying each cone if n_pos < 20, else try  sp_iter'
            print 'L2: ',sumsize(L2),str(L2)
            abc('r %s_unsolved.aig'%init_initial_f_name)
            if -1 in L2:
                nL2 = len(L2)
                print 'nL2 = %s, n_pos() = %s'%(nL2,n_pos())
##                print 'Trying each remaining PO for %d sec.'%ttime
                unproved = [i for i in xrange(len(L2)) if L2[i] == -1]
                print 'unproved = %s'%str(unproved)
                assert n_pos() >= len(unproved), 'n_pos() = %d, len(unproved) = %d'%(n_pos(),len(unproved))
##                map5 = [i for i in xrange(len(L2)) if L2[i] == -1]
                simplify()
                'after simplify: ',str(ps())
                if len(unproved) < 20:
                    print 'trying each cone for %d'%ttime
                    L3 = [-1]*n_pos()
                    for i in unproved:
                        j = unproved.index(i)
                        print '\n**** cone %d/%d ****'%(i,nL2)
                        abc('r %s_unsolved.aig'%init_initial_f_name)
                        abc('cone -s -O %d'%i)
                        abc('&get;&scl;&lcorr;&put')
        ##                abc('scl') #RKB temp
                        result = verify(J,ttime)
                        r = result[0]
                        if r > Unsat: #Wasn't proved
                            continue
                        elif r == Unsat:
                            L3[i]=L2[i] = 0 #updating L3 and L2
                            pos_unsat = pos_unsat + [opos[j]]
                            pos_unsat = remove_dup(list(pos_unsat))
                            print 'number of pos_unsat = %s'%str(len(pos_unsat))
                        else:
                            L3[i]=L2[i] = 1 #updating L3 and L2
                            pos_sat = pos_sat + [opos[j]]
                            print opos[j]
                            pos_sat = remove_dup(list(pos_sat))
                            print 'pos_sat = %s'%str(pos_sat)
                            found_sat = True
                        g = [map1,map2,lst0,lst1,NP,[]]
                        L = output2(list(L2),g)
                        uns = indices(L,-1)
                        if not uns == opos:
                            print 'uns and opos are not equal'
                            print 'uns = ',uns
                            print 'opos = ',opos
                    abc('r %s_unsolved.aig'%init_initial_f_name)
     
##                    abc('r %s_unsolved.aig'%init_initial_f_name)
##                    if -1 in L3:
##                        remove_proved_pos(L3)
##                        lst = [i for i in range(len(L3)) if L3[i]>-1]
##                        tlst = [opos[lst[i]] for i in range(len(lst))]
##                        opos = remove_sub(list(opos),tlst)
##                        assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())
##                        abc('w %s_unsolved.aig'%init_initial_f_name)
                    
                else:
                    print 'trying sp_iter'
                    abc('r %s_L2.aig'%init_initial_f_name)
                    assert n_pos() >= len(L2),'npos = %d, len(L2) = %d'%(n_pos(),len(L2))
                    g = [map1,map2,lst0,lst1,NP,[]]
                    print 'L2 = ',str(L2)
                    print 'opos = ', str(opos)
                    L2 = sp_iter(101,list(L2),g,list(opos)) #can we use unsolved in sp_iter?
                    print 'after sp_iter'
                    print 'L2 = ',str(L2)
                    print 'opos = ', str(opos)
                    L = output2(list(L2),g)
                    abc('r %s_L2.aig'%init_initial_f_name)
                    opos = report(list(opos),list(L2))
                    
##                    remove_proved_pos(L2)
##                    lst = [i for i in range(len(L2)) if L2[i]>-1]
##                    tlst = [opos[lst[i]] for i in range(len(lst))]
##                    opos = remove_sub(list(opos),tlst)
##                    assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())
##                    uns = indices(L,-1) ######################## stopped here
##                    if not uns == opos:
##                        print 'uns and opos are not equal'
##                        print 'uns = ',uns
##                        print 'opos = ',opos
##                    abc('w %s_unsolved.aig'%init_initial_f_name)
                    
##                if Ss == 'SAT' and found_sat: #previous solve_all was SAT and found at least 1 PO SAT
                abc('r %s_L2.aig'%init_initial_f_name)
                assert n_pos() >= len(L2),'mismatch in n_pos and len(L2) %d,%d'%(n_pos(),len(L2))
                opos = report(list(opos),list(L2))
                
##                if -1 in L2:
##                    remove_proved_pos(L2)
##                    lst = [i for i in range(len(L2)) if L2[i]>-1]
##                    tlst = [opos[lst[i]] for i in range(len(lst))]
##                    opos = remove_sub(list(opos),tlst)
##                    assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())
                
                simplify()
                write_file('save')
                result = simple(2001,1)# 1 here means do not do simplification first
                assert count_less(L2,0) == 1,'n_pos = 1 but more than one -1 in L2'
                for i in range(len(L2)):
                    if L2[i] == -1:
                        if result[0] =='UNSAT': #all are unsat
                            L2[i] = 0
                            pos_unsat = pos_unsat + [opos[i]]
                            pos_unsat = remove_dup(list(pos_unsat))
                            print 'number of pos_unsat = %s'%str(len(pos_unsat))
                        elif result[0] == 'SAT':#all are sat
                            L2[i] = 1
                            pos_sat = pos_sat + [opos[i]]
                            print opos[i]
                            pos_sat = remove_dup(list(pos_sat))
                            print 'pos_sat = %s'%str(pos_sat)
                                
##    L = output(list(L),list(L1),L2,map1,map2,lst0,lst1,NP) # final report of results.
    g = [map1,map2,lst0,lst1,NP,[]]
##    print 'entering final reporting 3'
    L = output2(list(L2),g)#xxxx
    uns = indices(L,-1)
    if not uns == opos:
        print 'uns and opos are not equal'
        print 'uns = ',uns
        print 'opos = ',opos
    return L

def report(opos,ss):
    global pos_sat,pos_unsat
    if 1 in ss or 0 in ss: #something solved
##        if -1 in ss: #not all solved
        if True:
            print 'len(ss),n_pos(),len(opos) = ',str((len(ss),n_pos()),len(opos))
            rem0 = indices(ss,0)
            rem1 = indices(ss,1)
##            rem = rem0+rem1
##            rem.sort()
            rem = remove_dup(rem0+rem1)
            print 'rem = ',str(rem)
            if not len(rem) == n_pos():
                print 'Removing %d POs'%len(rem)
                print 'rem: ',str(rem)
                remove(rem,1)
            else:
                print "can't remove all remaining POs"
            print opos
            tlst1 = [opos[rem1[i]] for i in range(len(rem1))]
            tlst0 = [opos[rem0[i]] for i in range(len(rem0))]
            pos_sat = pos_sat + tlst1
            print tlst1
            pos_unsat = pos_unsat + tlst0
##            opos = remove_sub(list(opos),(tlst1+tlst0))
##            assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())
    abc('w %s_unsolved.aig'%init_initial_f_name) #update unsolved
    pos_sat = remove_dup(list(pos_sat)) #remove duplicates and sorts
    pos_unsat = remove_dup(list(pos_unsat))
    print 'pos_sat = %s'%str(pos_sat)
    print 'number of pos_unsat = %s'%str(len(pos_unsat))
    return opos
        


def scorr_easy():
    L = [-1]*n_pos()
    na = n_ands()
    if na > 30000:
        abc('&get;&scorr;&put')
    else:
        k=1+30000/na
        abc('scorr -k = %d'%k)
    solv = list_const_pos()
    if max(solv) > -1: #something solved
        L = put(solv,L)
    return L
            
        
        
def create_unsolved(L):
    abc('r %s_initial_save.aig'%init_initial_f_name) 
    lst = []
    assert len(L) == n_pos(),'lengths of L and n_pos = %d,%d'%(len(L),n_pos())
    for i in range(len(L)):
        if L[i] > -1: #solved PO
            lst = lst + [i]
    assert max(lst) < n_pos(), 'error in lengths'
    assert count_less(L,0) == n_pos() - len(lst),'mismatch'
    remove(lst,-1) # remove solved
    
def multi_prove_iter(opos=[]):
    global t_iter_start,file_out,ff_name
    print 'PO names = ',str(opos)
    ff_name = init_initial_f_name
    file_out = open('%s_time_results.txt'%init_initial_f_name, 'w')
    t_iter_start = time.time()
    L = multi_prove(opos=list(opos))
    uu = len(pos_unsat)
    ss = len(pos_sat)
    dd = npos() -(uu+ss)
    overlap = [i for i in uu and i in ss]
    assert overlap == [],'overlap = %s'%str(overlap)
    d = count_less(L,0)
    u = count_less(L,1)-d
    s = count_less(L,2) - (d+u)
    assert uu == u and ss == s and dd == d, 'uu = %d, u = %d,aa = %d, s = %d, dd = %d, d = %d'%(uu,u,ss,s,dd,d)
    rr =  '\n@@@@@ %s: Final time =  %.2f '%(init_initial_f_name,(time.time() - t_iter_start))
    rr = rr + 'SAT = %d, UNSAT = %d, UNDECIDED = %d '%(s,u,d)
    rr = '%s: '%init_initial_f_name + rr
    print rr
    file_out.write(rr)
    res = PO_results(L) #here we group POs in SAT UNSAT and UNSOLVED and write out aig files.
    file_out.write(res)
##    print res
    file_out.flush()
    file_out.close()
    #here we could restrict to SAT(UNSAT) POs and invoke solver to verify all POs are SAT(UNSAT)
    # we also could retry mp on UNSOLVED aig file
    return

def restrict_v(L,v):
    """ L is a list of 0,1,-1"""
    lst = []
    for j in range(len(L)):
        if L[j] == v:
            lst = lst + [j]
    restrict(lst)
    return lst

def PO_results(L):
    global ff_name,pos_sat,pos_unsat
    pos_sat = remove_dup(list(pos_sat))
    pos_unsat = remove_dup(list(pos_unsat))
    print '\n**** pos_sat = %s ****'%str(pos_sat)
    print '\n**** pos_unsat = %s ****'%str(pos_unsat)
    print '\n'
    S=U=UD=[] #this is OK because all are scalers for the moment
    for j in range(len(L)):
        ll = L[j]
        if ll == -1:
            UD = UD + [j]
        elif ll == 0:
            U = U + [j]
        elif ll == 1:
            S = S + [j]
        else:
            print 'error, L contains a non -1,0,1'
    res = "[[SAT = %s], [UNSAT = %s], [UNDECIDED = %s]"%(str(S),str(U),str(UD))
    #restore initial unsolved POs
    if len(S) == len(L) or len(U) == len(L) or len(UD) == len(L):
        # in these cases stored files would be same as original
        return res
    abc('r %s.aig'%ff_name)
    assert n_pos() > max(UD+U+S), 'mismatch in # POs'
    #NOTICE - if there were initially const_1 POs, they are handled correctly
    if not UD == []:
        remove(U+S,1) # we do it this way to preserve constraints
##        restrict(UD,0)
        abc('w %s_UNSOLVED.aig'%ff_name) # we want to keep constraints unfolded
        print 'Unsolved POs restored as %s_UNSOLVED.aig'%ff_name
##        print 'Unsolved POs = %s'%str(UD)
        print 'Suggest trying multi_prove again on %s_UNSOLVED.aig'%ff_name
    else:
        print 'All POs were solved'
    abc('r %s.aig;fold'%ff_name) # if original had constraints they are folded in
    if not U == []: 
        restrict(U,1) #we use 1 here because do not want to remove const-0 POs which should be in U
        abc('w %s_UNSAT.aig'%ff_name)
        print 'Unsat POs restored as %s_UNSAT.aig'%ff_name
##        print 'Unsat POs = %s'%str(U)
    abc('r %s.aig;fold'%ff_name)
    if not S == []:
        restrict(S,0) # U + UD are set to 0 and removed. Thus does not remove const-1 POs.
        abc('w %s_SAT.aig'%ff_name)
        print 'Sat POs restored as %s_SAT.aig'%ff_name
##        print 'Sat POs = %s'%str(S)
    return res

def output2(L2,globs=[[],[],[],[],0,[]]):
    global t_iter_start
##    global map1g,map2g,lst0g,lst1g,NPg,final_mapg
    [map1,map2,lst0,lst1,NP,final_map] = globs
    L1 = unmap2(L2,map2)
    L = unmap2(L1,map1)
    L = weave(list(L),[],lst1) #put back 1 in L
    L = weave(list(L),lst0,[]) #put back 0 in L
    report_results(list(L),final_map) #L in original POs in 0,1,-1 format
    return L

def report_L(lst=[],v=0):
    """lst must refer to original PO numbering"""
    global _L_last
    if lst == []:
        return
    for j in lst:
        if _L_last[j] == -1: #means not reported yet
            _L_last[j] = v
            report_result(j,v)

def report_s(s=[]):
    """s must refer to original PO numbering
    Differs from above """
    global _L_last
    assert len(s) == len(_L_last), 'two lengths are not equal'
    if s == []:
        return
    for j in range(len(s)):
        if not _L_last[j] == s[j]: #means not reported yet
            assert _L_last[j] == -1, 'j = %d, _L_last[j] = %d, s[j] = %d'%(j,_L_last[j],s[j])
            if _L_last[j] == -1:
                _L_last[j] = s[j]
                report_result(j,s[j])
    

def report_results(L,final_map=[],if_final=False):
    global _L_last,t_iter_start,file_out
    print 'report_results = %s'%sumsize(L)
    #L is original POs in 0,1,-1 format
    out = '\n@@@@ %s: Time = %.2f: results = %s'%(init_initial_f_name,(time.time()- t_iter_start),sumsize(L))
    print out
    file_out.write(out + '\n')
    out = 'current aig size: ' + ps()
    file_out.write(out)
    assert len(L) == len(_L_last),str((len(L),len(_L_last)))
    s = [i for i in xrange(len(L)) if ((L[i] == 1) and _L_last[i] == -1)]
    if not len(s) == 0:
        ss = 'new SATs = ' + str(s)
        print ss
        file_out.write(ss)
    u = [i for i in xrange(len(L)) if ((L[i] == 0) and _L_last[i] == -1)]
    if not len(u)== 0:
        uu = 'new UNSATs = ' + str(u)
        print uu
        file_out.write(uu)
    file_out.flush()
    for j in range(len(L)):
        if not L[j] == _L_last [j]:
            assert _L_last[j] == -1, '_L_last[j] = %d, L[j] = %d'%(_L_last[j],L[j])
            if _L_last[j] == -1: #not reported yet
                report_result(j,L[j])
    mm = [j for j in range(len(L)) if (not L[j] == _L_last[j] and not _L_last[j] == -1)]
    if len(mm) > 0:
        print 'mismatches between L and _L_last = %s '%str(mm)
    print 'report before: _L_last = %s'%sumsize(_L_last)
    _L_last = list(L) #update _L_last
    print 'report after: _L_last = %s'%sumsize(_L_last)
    print '\n'

def report_result(POn, REn, final_map=[]):
    return #for non hwmcc application
    trans = ['UNSAT','SAT']
    assert not REn < 0, 'reporting  non proved PO'
    if final_map == []:
##        print 'PO = %d, Result = %d:  '%(POn, REn),
        print 'PO = (%d,%d):  '%(POn,REn),
    else:
        print 'PO = %d, Result = %d:  '%(final_map[POn], REn),
        print 'PO = (%d,%d):  '%(final_map[POn],REn),
##    print '\n'


def pass_down(L,L1,map):
    """map maps L into L1.Populate L1 with values in L"""
##    print len(L),len(L1),len(map),max(map)
##    print sumsize(L)
##    print sumsize(L1)              
    for j in range(len(map)):
        if L[j] == -1:
            continue
        assert L1[map[j]] == -1 or L1[map[j]] == L[j], 'L1=%d, L = %d'%(L1[map[j]],L[j]) 
        L1[map[j]] = max(L[j],L1[map[j]])
    return L1

def list_const_pos(ll=[]):
    """ creates an indicator of which PO are const-0 and which are const-1
        does not change number of POs
    """
    n=n_pos()
    L = range(n)
    ind = [-1]*n
    for j in L:
        ind[j] = is_const_po(j)
    print sumsize(ind)
    return ind

def remove_const_v_pos(v=-1):
    global po_map
    """removes the const 0  or 1 pos according to n, but no pis because we might
    get cexs and need the correct number of pis
    """
    if v > -1:
        run_command('&get; &trim -i -V %d; &put'%v) #v is 0 or 1
    else:
        run_command('&get; &trim -i; &put') #removes both constants

def remove(lst,v=0):
    """Removes outputs in lst (a list of PO indices), v denotes how they are zeroed out
    can remove both SAT and UNSAT POs
    WARNING will not remove all POs even if in lst
    """
    global po_map
    n_before = n_pos()
    if v == -1:
        v = 1 # This makes zero does as before.
    zero(lst,v)
    l=remove_const_v_pos(v) #uses value v to remove
    if not len(lst) == (n_before - n_pos()):
        print'WARNING: Inadvertantly removed some const-0 POs.\nPO_before = %d, n_removed = %d, PO_after = %d'%(n_before, len(lst), n_pos())

##    print 'PO_before = %d, n_removed = %d, PO_after = %d'%(n_before, len(lst), n_pos())
##    assert len(lst) == (n_before - n_pos()),'Inadvertantly removed some const-0 POs.\nPO_before = %d, n_removed = %d, PO_after = %d'%(n_before, len(lst), n_pos())
##    print 'PO_before = %d, n_removed = %d, PO_after = %d'%(n_before, len(lst), n_pos())


def zero(list,v=0):
    """Zeros out POs of AIG in list"""
    if v == 0:
        cmd = 'zeropo -s -N ' #puts const-0 in PO
    else:
        cmd = 'zeropo -so -N ' #puts const-1 in PO
    for j in list:
        run_command('%s%d'%(cmd,j)) #-s prevents the strash after every zeropo
    abc('st')

def listr_v_pos(v=0):
    """ returns a list of const-v pos and removes them
    """  
    L = range(n_pos())
    L.reverse()
    ll = []
    for j in L:
        i = is_const_po(j)
        if i == v:
            abc('removepo -N %d'%j) #removes const-v output
##            print 'removed PO %d'%j
            ll = [j] + ll
    return ll



# ********************************** end of multi_prove stuff *************************************



def syn3():
    t = time.clock()
    run_command('&get;&b; &jf -K 6; &b; &jf -K 4; &b;&put')
    ps()
    print 'time = %.2f'%(time.clock() - t)

def syn4():
    t = time.clock()
    abc('&get;&b; &jf -K 7; &fx; &b; &jf -K 5; &fx; &b;&put')
    ps()
    print 'time = %.2f'%(time.clock() - t)


##def solve_parts(n): #xxxx
##    global t_iter_start,file_out
##    r=range(n)
##    r.reverse()
##    name = init_initial_f_name
##    results = []
##    for i in r:
##        file_out.write('\n@@@@ Starting part%d: \n'%i)
##        file_out.flush()
##        abc('r %s_part%d.aig'%(name,i))
##        print '\nPart%d: '%i
##        L = multi_prove()
##        rr =  '\n@@@@ Time =  %.2f '%(time.time() - t_iter_start)
##        rr = rr + 'Part%d: '%i
##        ssl = sumsize(L)
##        rr = rr + ssl
##        results = results + [[ssl]]
##        print rr
##        file_out.write(rr + '\n')
##        file_out.flush()
##    return results
##
##def cp(n=10):
##    return chop_prove(n)
##
##def chop_prove(n=10,t=100):
##    global t_iter_start,file_out
##    tm = time.time()
##    abc('w %s_chop_temp.aig'%f_name)
##    N = max(5,n_pos()/n)
##    J = 0
##    total = []
##    np = n_pos()
##    while J < np:
##        abc('r %s_chop_temp.aig'%f_name)
##        E = J+N-1
##        R = N
##        if E > np-1:
##            R = N - (E - (np -1))
##        abc('cone -s -O %d -R %d'%(J,R))
##        npp = n_pos()
##        print '\n\n*****     solving outputs %d to %d     *****'%(J,(J+R-1))
##        f_map = str([J]*R + range(R))
##        funcs = create_funcs(slps,t)
##        funcs = funcs + [eval('(pyabc_split.defer(mp)(simple,%s,1,%s))'%(t,f_map))] #1 means do fast mp
####        funcs = funcs + [eval('(pyabc_split.defer(sp)())')]
##        for i,res in pyabc_split.abc_split_all(funcs):
##            print 'Method %d returned first with result = %s'%(i,res)
##            if i == 0:
##                res = 'SAT = 0, UNSAT = 0, UNDECIDED = %d'%npp
##                rr = '\n@@@@ Time =  %.2f: '%(time.time() - t_iter_start)
##                rr = rr + 'chop%d: '%i
##                rr = rr + res
##                print rr
##                file_out.write(rr + '\n')
##                file_out.flush()
##                break
##            if i == 1:
##                rr = '\n@@@@ Time =  %.2f: '%(time.time() - t_iter_start)
##                rr = rr + 'chop%d: '%i
##                rr = rr + res
##                file_out.write(rr + '\n')
##                file_out.flush()
####                print res
##                break
##            else:
##                if res == 'UNSAT':
##                    res = 'SAT = 0, UNSAT = %d, UNDECIDED = 0'%npp
##                    rr = '\n@@@@ Time =  %.2f: '%(time.time() - t_iter_start)
##                    rr = rr + 'chop%d: '%i
##                    rr = rr + res
##                    print rr
##                    file_out.write(rr + '\n')
##                    file_out.flush()
##                    break
##                else:
##                    res = 'SAT = 0, UNSAT = 0, UNDECIDED = %d'%npp
##                    rr = '\n@@@@ Time =  %.2f: '%(time.time() - t_iter_start)
##                    rr = rr + 'chop%d: '%i
##                    rr = rr + res
##                    print rr
##                    file_out.write(rr + '\n')
##                    file_out.flush()
##                    break
####        print res
##        total = total + [[res]]
##        print total
##        J = J + R
##    c = get_counts(total)
##    tm = time.time() - tm
##    rr = '\n@@@@ Total time for chop = %.2f, SAT = %d, UNSAT = %d, UNDECIDED = %d'%(tm,c[0],c[1],c[2])
##    file_out.write(rr + '\n')
##    file_out.flush()
##    print rr
##    return total

##def get_counts(L):
##    s=u=d=0
##    for i in range(len(L)):
##        li = L[i][0]
####        print li
##        j1=li.find('=')
##        j2 = li.find(',')
##        num = int(li[j1+1:j2])
##        s = s+num
##        li = li[j2+1:]
##        j1=li.find('=')
##        j2 = li.find(',')
##        num = int(li[j1+1:j2])
##        u = u+num
##        li = li[j2+1:]
##        j1=li.find('=')
##        j2 = li.find(',')
##        num = int(li[j1+1:])
##        d = d+num
##    return [s,u,d]
##        



##def print_all(L,L1,L2,map1,map2,lst0,lst1,NP,final_map=[]):
####    return
##    print 'L = ',
##    print L
##    print 'L1 = ',
##    print L1
##    print 'L2 = ',
##    print L2
##    print 'map1 = ',
##    print map1
##    print 'map2 = ',
##    print map2
##    print 'lst0 = ',
##    print lst0
##    print 'lst1 = ',
##    print lst1


##def rnge(n,m):
##    """ return interval n+range(m)"""
##    N = []
##    for j in range(m):
##        N = N + [n + j]
##    return N
##
##def create_cluster(n=0,p=1,L=100):
##    """n is the start node and p is the multiplier on the # of POs to extract
##        ll is the limit on the number of latches to include"""
##    clstr=rem = [] #make a list of nodes to remove because not compatible
##    N = 0 #number of end skips
##    init = False
##    skip=0 #number of initial skips
##    abc('w temp.aig')
##    np = n_pos()
##    for i in range(np):
##        if n + p*(i+1-skip) > np:
##            if n_latches() > L:
##                bp = n_pos()-p 
##                remove(rnge(bp,p),1) #remove last p
##                abc('scl')
##            return clstr
##        abc('r temp.aig')
##        abc('cone -s -O %d -R %d;scl'%(n,p*(i+1-skip)))
##        xx = n_pos()
##        if n_latches() > L:
##            if not init: #have not found start point yet
##                n=n+p #increase start point
##                print 'n,FF = %d,%d'%(n,n_latches())
##                skip = skip + 1
##                continue
##        else:
##            if not init:
####                nn=p*(i-skip)
####                clstr = clstr + rnge(nn,p*(i+1-skip))
####                print clstr #initial cluster
##                init = True
####        abc('w old.aig')
##        remove(rem,1)
##        abc('scl')
##        ps()
##        if n_latches() > L:
##            x = xx - p #remove last p POs
##            rem = rem + rnge(x,p)
####            print len(rem)
##            print 'x,len(rem) = %d,%d,%d'%(x,len(rem))
##            N = N+1
##        else:
##            bn=p*(i-skip)
##            nr=rnge(bn,p)
##            clstr = clstr + nr
##        if N > 100: #don't do more than 10 end-skips
##            bp = n_pos()-p 
##            remove(rnge(bp,p),1) #put last p on remove list
##            abc('scl')
##            return clstr
##
##def generate_clusters(b=0,inc=10,end=100):
##    abc('w temp_gen_clstr.aig')
##    abc('w t_gen_cl.aig')
##    clusters = []
##    while True:
##        abc('r t_gen_cl.aig')
##        clstr = create_cluster(b,inc,end)
##        clusters = clusters + [clstr]
##        abc('r t_gen_cl.aig')
##        if clstr == []:
##            return clusters
##        remove(clstr,1)
##        abc('w t_gen_cl.aig')
##
##def map_clusters_to_original(cl):
##    L = range(n_pos())
##    Clstrs = []
##    k = 0
##    for j in range(len(cl)):
##        c = cl[j]
##        cc = pick(L,c)
##        Clstrs = Clstrs + [cc]
##        L = pick_not(L,cc)
##    return Clstrs

def pick(L,c):
    """ computes L(c) """
    x=[]
    for i in range(len(c)):
        x = x + [L[c[i]]]
    return x

def pick_not(L,c):
    """ computes L(~c)"""
    x = []
    for i in range(len(L)):
        if not i in c:
            x = x + [L[i]]
    return x


def scorr_T(t=10000):
    global smp_trace, scorr_T_done
    if scorr_T_done:
        return
    scorr_T_done = 1
    print 'Trying scorr_T (scorr -C 2, &scorr, &scorr -C 0, &lcorr) for %d sec'%t
    funcs = [eval('(pyabc_split.defer(sleep)(t))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("scorr -C 2"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("&get;&scorr;&put"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("&get;&scorr -C 0;&put"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("&get;&lcorr;&put"))')]
##    funcs = create_funcs(slps,t)+funcs
    mtds = sublist(methods,slps) + ['scorr2','&scorr','&scorr0','&lcorr']
##    print mtds
    best = n_ands()
    abc('w %s_best_T.aig'%f_name)
    name1 = '%s_sc1.aig'%f_name
    if os.access(name1,os.R_OK):
        os.remove(name1)
    name2 = '%s_sc2.aig'%f_name
    if os.access(name2,os.R_OK):
        os.remove(name2)
    name3 = '%s_sc3.aig'%f_name
    if os.access(name3,os.R_OK):
        os.remove(name3)
    name4 = '%s_sc4.aig'%f_name
    if os.access(name4,os.R_OK):
        os.remove(name4)
    N=m_best = 0
    for i,res in pyabc_split.abc_split_all(funcs):
##        print N,i,res
        if i == 0: #timeout
            print 'scorr_T timeout'
            break
        if i == 1:
            abc('w %s_sc1.aig'%f_name)
            print 'scorr: ',
            ps()
            N=N+1
        if i == 2:
            abc('w %s_sc2.aig'%f_name)
            print '&scorr: ',
            ps()
            N=N+1
            if N == 4:
                break
        if i == 3:
            abc('w %s_sc3.aig'%f_name)
            print '&scorr0: ',
            ps()
            N=N+1
            if N == 4:
                break
        if i == 4:
            abc('w %s_sc4.aig'%f_name)
            print '&lcorr: ',
            ps()
            N=N+1
        if N == 4 or n_latches() == 0:
            break
    if os.access(name1,os.R_OK):
        abc('r %s'%name1)
        if n_ands() < best or n_latches() == 0:
            best = n_ands()
            m_best = 1
            abc('w %s_best_T.aig'%f_name)
    if os.access(name2,os.R_OK):
        abc('r %s'%name2)
        if n_ands() < best or n_latches() == 0:
            m_best = 2
            best = n_ands()
            abc('w %s_best_T.aig'%f_name)
    if os.access(name3,os.R_OK):
        abc('r %s'%name3)
        if n_ands() < best or n_latches() == 0:
            m_best = 3
            best = n_ands()
            abc('w %s_best_T.aig'%f_name)
    if os.access(name4,os.R_OK):
        abc('r %s'%name4)
        if n_ands() < best or n_latches() == 0:
            m_best = 4
            best = n_ands()
            abc('w %s_best_T.aig'%f_name)
    smp_trace = smp_trace + ['%s'%mtds[m_best]]
    abc('r %s_best_T.aig'%f_name)
    print '%s: '%mtds[m_best],
    ps()

def pscorr(t=2001):
    result = par_scorr(t)
    if n_ands() == 0:
        return result
    else:
        return 'UNDECIDED'

def par_scorr(t=30,ratio = 1):
    t_init = time.time()
##    abc('dr -m;drw')
    abc('dretime;dc2')
    funcs = [eval('(pyabc_split.defer(abc)("scorr -vq -F 1"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("scorr -vq -F 2"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("scorr -vq -F 4"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("scorr -vq -F 8"))')]
    funcs = funcs + [eval('(pyabc_split.defer(abc)("scorr -vq -F 16"))')]
    funcs = create_funcs(slps,t)+funcs
    mtds = sublist(methods,slps) + ['scorr1','scorr2', 'scorr4', 'scorr8', 'scorr16']
    best = n_ands()
    print 'par_scorr: best = %d'%best
    abc('w %s_best.aig'%f_name)
    idone = []
    mtd = 'initial'
    for i,res in pyabc_split.abc_split_all(funcs):
##        print i,res
        if i == 0: #timeout
            mtd = mtds[0]
            break
        else:
            idone = idone + [i]
            if n_ands() <= ratio * best:
                best = n_ands()
                mtd = mtds[i]
##                print 'par_scorr: best = %d, method = %s'%(best, mtds[i])
                abc('w %s_best.aig'%f_name)
                if best == 0 or len(idone) >= 5:
                    break
            else:
                break
##    print 'Time: %.2f'%(time.time() - t_init)
    abc('r %s_best.aig'%f_name)
##    if best == 0:
##        print mtd
    return mtd

def par_scorr_q(t=10000,ratio = 1):
    abc('dretime;dc2')
    abc('bmc2 -T 5')
    depth = n_bmc_frames()
    mtds = funcs = []
    n=1
    while True:
        funcs = funcs + [eval('(pyabc_split.defer(abc)("scorr -vq -F %d"))'%n)]
        mtds = mtds + ['scorr%d'%n]
        n = 2* n
        if n > max(1,min(depth,16)):
            break
    funcs = create_funcs(slps,t)+funcs
    mtds = sublist(methods,slps) + mtds
    best = n_ands()
    print 'best = %d'%best
    abc('w %s_best.aig'%f_name)
    idone = []
    for i,res in pyabc_split.abc_split_all(funcs):
##        print i,res
        if i == 0:
            break
        else:
            idone = idone + [i]
            if n_ands() <= ratio * best:
                best = n_ands()
                print 'best = %d, method = %s'%(best, mtds[i])
                abc('w %s_best.aig'%f_name)
                if best == 0 or len(idone) >= len(mtds)-1:
                    break
            else:
                break
    abc('r %s_best.aig'%f_name)


##def indicate_0_pos(L2):
##    """
##    puts 0's in L2 where the corresponding output is driven by a const-0
##    """
####    assert n_pos() == len(L2), 'list L2=%d and n_pos=%d in current AIG dont match'%(len(L2),n_pos())
##    for j in range(n_pos()):
##        i=is_const_po(j)
##        if i == 0:
##            L2[j]=0
##    return L2

def list_0_pos():
    """
    returns indices of outputs driven by  const-0
    """
    L = []
    for j in range(n_pos()):
        i=is_const_po(j) #returns const value of PO if const. Else -1
        if i == 0:
            L = L + [j]
    return L

def mprove2(L=0,op='simple',t=200,Fnn=0,globs=[[],[],[],[],0,[]], opo=[]):
    global _L_last, f_name, skip_spec, last_gasp_time
    print 'mprove2 entered' ,
    if L == 0:
        L = [-1]*n_pos()
    ps()
    if opo == []:
        opo = range(n_pos())
    print 'mprove2 entered with L = ',
    print sumsize(L)
    assert len(opo) == n_pos(), 'opo and n_pos not eq length: %s'%str(n_pos(),opo)
    abc('w %s_mp2.aig'%f_name) #save aig before pos removed
    old_f_name = f_name #we may call super_prove() which can change f_name
    n = count_less(L,0)
    opo0 = [opo[j] for j in range(n_pos()) if L[j] == 0]
    print 'POs proved UNSAT: ',str(opo0)
    opo1 = [opo[j] for j in range(n_pos()) if L[j] == 1]
    print 'POs proved SAT: ',str(opo1)
    solved = [j for j in range(len(L)) if L[j] > -1]
    if len(solved) == n_pos(): #all POs already solved
        opo = []
        for i in range(len(L)):
            if L[i] == -1:
                L[i] = 0
        return 'ALL_SOLVED',L,opo
    remove(solved,-1) #remove solved POs
    tlst = [opo[solved[i]] for i in range(len(solved))] #removing solved POs
    opo = remove_sub(opo,tlst)
    print 'opo: ',opo
    if len(solved)>0:
        print 'Removed %d proved POs'%len(solved)
    if n_pos() == 0:
        f_name = old_f_name
        print '^^^ f_name restored as %s'%f_name
        abc('r %s_mp2.aig'%f_name)
        opo = []
        for i in range(len(L)):
            if L[i] == -1:
                L[i] = 0
        return 'ALL_SOLVED',L,opo
    ps()
    N = n_pos()
    if N == 1: #only one PO left
        
        v = -1
        skip_spec_old = skip_spec
        skip_spec = True
        result = simple(2001,1)# 1 here means do not do simplification first
        ff_name = f_name
        f_name = ff_name
        print '^^^ f_name restored as %s'%f_name
        skip_spec = skip_spec_old
        res = result[0]
        print 'result of simple = ',
        print res
####        print result
        if res == 'SAT':
            v = 1
            print 'PO = %d proved SAT'%opo[0]
        if res == 'UNSAT':
            v = 0
            print 'PO = %d proved UNSAT'%opo[0]
        i = L.index(-1) #only 1 PO left unsolved so flll L in -1 with v
##        print 'i=%d,v=%d,L=%s'%(i,v,str(L))
        L[i] = v
        f_name = old_f_name #if super_prove() changed f_name need to revert to old f_name
        print '^^^ f_name restored as %s'%f_name
        abc('r %s_mp2.aig'%f_name) #going back to incoming aig. L has info about this
        print 'reverting %s_mp2.aig'%f_name,
        ps()
        print sumsize(L)
        if v > -1:
            res = 'ALL_SOLVED'
            opo = []
            for i in range(len(L)):
                if L[i] == -1:
                    L[i] = v
        return res,L,opo
    
    r = pre_simp() #this may increase the number of POs if phases was increased inside pre_simp
    NP = n_pos()/N
    
    L1 = [-1]*n_pos()
    L2 = list(L1)
    Llst0 = []
##    print 'L1: ',len(L1)
    if r[0] == Unsat:
        L1 = [0]*N
        L2 = list(L1)
    elif n_latches() == 0:
        if check_sat() == Unsat:
            L1 = [0]*N
            L2 = list(L1)
    else:
        Llst0 = list_0_pos()#lists the POs that are const-0
        Llst0.sort()
##        print 'Llst0 = %s'%str(Llst0)
        n_0 = len(Llst0)
        if n_0 > 0:
            print 'Found %d const-0 POs'%n_0
            remove(Llst0,0) #
            print 'Removed %d const-0 POs'%len(Llst0)
            tlst = [opo[Llst0[i]] for i in range(len(Llst0))]
            print 'POs proved UNSAT: ',str(tlst)
            opo = remove_sub(opo,tlst)
        if NP > 1: # we want to do iso here because more than one phase was found.
            iso()  # additional iso - changes number of POs
            #what do we do about opo here???
            print 'phase must has been done, so opo will be wrong.'
            map3 = create_map(eq_classes(),N) #creates map into previous
##        tb = min(n_pos(),20)
        N = n_pos()
        tb = min(N,50)
##        print 'Trying par_multi_sat for %d sec.'%tb
        S,lst1,s = par_multi_sat(tb,1,1,1,opo) #this gives a list of SAT POs, lst1 not used
        print 'par_multi_sat done'
        s10 = s
        L2 = list(s)
        n_solved = n_pos() - count_less(s10,0)
        if 1 in s10 or 0 in s10: #something was solved 
            if n_solved < N: #not all solved
                solved = indices(s,0)+indices(s,1)
##                print 'solved: ',
##                print solved
                solved.sort()
                remove(solved,1)
                print 'n_pos(): ',n_pos()
##                print 'opo: ', opo
                tlst = [opo[solved[i]] for i in range(len(solved))]
                print 'POs SAT: ', str([opo[j] for j in indices(s,1)])
                print 'POs UNSAT: ', str([opo[j] for j in indices(s,0)])
                opo = remove_sub(list(opo),tlst)
                assert n_pos() == len(opo),'n_pos(),opo = %s'%str(n_pos(),opo)
                print 'opo: ',str(opo)
                
##                print opo
##                """ if lst1 > 1 element, simplify and run par_multi_sat again to get lst2
##                then merge lst1 and lst2 appropriately to create new lst1 for below.
##                """
                tb = tb+25
                gap = max(15,.2*tb)
                if len(solved) > 0:
                    s210 = list(s10)
                    #iterate here as long as at least 1 PO is found SAT
                    n_solved = n_pos() - count_less(s210,0) 
                    while n_solved > 0:
                        print 'n_solved = %d'%n_solved
                        gap = int(1+1.2*gap)
                        print 'gap = %.2f'%gap
                        pre_simp(1) #warning this may create const-0 pos xxx
                        S,lst2,s210 = par_multi_sat(tb,gap,1,1,opo) #this can find UNSAT POs
                        n_solved = n_pos() - count_less(s210,0)
                        # put xxxx
                        s10 = put(s210,list(s10)) # len(s210) is # -1's in s10. This
                        #puts the values in s210 replacing some of the -1's in s10
                        if count_less(s10,0) == 0 or n_solved == 0: #all solved or nothing solved
                            print 's210 = %s'%sumsize(s210)
                            break #s10 has the results
                        else: #something solved but not all POs.
                            out = '\n@@@@ %s: Time = %.2f: additional POs found SAT = %d'%(init_initial_f_name,(time.time()- t_iter_start),len(lst2))
                            print out
                            file_out.write(out + '\n')
                            file_out.flush()
                            solved = indices(s210,0)+indices(s210,1)
                            solved.sort()
                            print 'len(solved),n_pos:', len(solved),n_pos()
                            remove(solved,1) #this zeros the l210 and then removes ALL const-1 POs.
                            print 'n_pos, len(opo): ',n_pos, len(opo)
                            #If there are more than lst2 removed, it fires an assertion.
                            
                            print 'POs SAT: ', str([opo[j] for j in indices(s210,1)])
                            print 'POs UNSAT: ', str([opo[j] for j in indices(s210,0)])#
                            tlst = [opo[solved[i]] for i in range(len(solved))]
                            opo = remove_sub(opo,tlst)
                            continue
                    L2 = list(s10) #put results of s10 into L2
                else: #lst1 is empty or S == SAT'
                    print 'no cex found or S = UNSAT'
            else: #all solved
                print 'all POs solved'
                opo = []
            print 'Removed %d '%(len(s10) - count_less(s10,0))
        else:
            print 'nothing solved'
##        write_file('bmc2') #why is this done?
            abc('w %s_bmc2.aig'%f_name)
        if -1 in s10: #still some unsolved. Trying sp_iter *******
            last_gasp_time_old = last_gasp_time
            last_gasp_time = max(2*t,200)
            print '\n**** entering super_prove/simple iteration (sp_iter) ****'
            old_f_name = f_name
            L2t = list(s10) #s10  the size of original less the original const-0 POs
                                # found initially (L1t) and that found in xxxx
            Lt = list(L2t)
##            print 'L2t: ',str(L2t)
##            print 'L1st0: ',str(Llst0)
            L1t = inject(L2t,Llst0,0)
##            print 'L1t: ',str(L1t)
            Lt = insert(L1t,list(L))
##            print 'Lt:',str(Lt)
##            print 'L: ',str(L)
            print 'len(s10),len(L1t), len(Lt) ',len(s10),len(L1t), len(Lt)
            print 'length of Lt = %d, size = %s'%(len(Lt),str(sumsize(Lt)))
            print 'len(L),n_pos:',len(L),n_pos()
            print 'sp_iter started'
            print 'opo - ',str(opo)
            s210 = sp_iter(101,Lt,globs,list(opo)) #s210 same length as Lt. *******
            print 'sp_iter done'
            print 'opo = ',str(opo)
            po_unsat = []
            po_sat = []
            i=0
            print 's210 = ',str(s210)
            print 'Lt = ',str(Lt)
            for j in range(len(s210)):
                if Lt[j] == -1:
                    if s210[j] == 1:
                        po_sat = po_sat + [opo[i]]
                        i=i+1
                    elif s210[j] == 0:
                        po_unsat = po_unsat + [opo[i]]
                        i=i+1
            print 'new POs found SAT: ',str(po_sat)
            print 'new POs found UNSAT: ',str(po_unsat)
            f_name = old_f_name
            abc('r %s_bmc2.aig'%f_name) #restore aig before sp_iter was done
            print '^^^ f_name restored as %s'%f_name
            last_gasp_time = last_gasp_time_old
            L2 = list(s210)
        else: #all POs solved
            L2 = list(s210)
            opo = []
    assert NP == 1, 'NP > 1: ERROR'
    L1 = inject(list(L2),Llst0,0)
    print 'L1: ',len(L1),len(L2),len(Llst0)
    assert len(L1)<=len(L),"len(L1) = %d larger than len(L) = %d"%(len(L1),len(L))
    L = insert(L1,list(L)) # replace -1's in L with values in L1. Size of L1<=L L is really L2
    print sumsize(L)
    f_name = old_f_name
    print '^^^ f_name restored as %s'%f_name
    abc('r %s_mp2.aig'%f_name) #restore original aig when mprove2 entered
    if 1 in L:
        S = 'SAT'
    if not -1 in L:
        opo = []
        S = 'ALL_PROVED'
    print 'mprove2: mprove2 is done'
    return S,L,opo

def merge(L1,L2,n=0):
    """L2 refers to POs that were solved after POs in L1 were removed
    modifies L2 to refer to the original POs.
    if n=0 adds in L1 and sorts
    """
    if L1 == []:
        return L2
    if L2 == []:
        if n == 0:
            return L1
        else:
            return [] 
    m = max(L1)
    LL1 = L1 + [3+m+max(L2)] #this makes sure that there are enough gaps
    g = gaps(LL1)
##    print g
    L = []
    for i in range(len(L2)):
        l2i=L2[i]
        assert  l2i < len(g),'ERROR, L2 = %s,g = %s'%(str(L2),str(g))
        L = L + [g[l2i]]
##        print L
    if n == 0:
        L = L + L1
        L.sort()        
    return L            #L is already sorted

def put(s2,s11):
    """ put in the values of s2 into s11 where there should be only -1's and return s1 """
    s1 = list(s11)
    k = 0
    assert len(s2) == count_less(s1,0),'mismatch in put #-1s in s11 should equal len(s2)'
    for j in range(len(s1)):
        if s1[j] == -1:
            s1[j] = s2[k]
            k=k+1
    assert k == len(s2),'did not put in all values of s2 into s1'
    return s1

def gaps(L1):
    """L2 refers to POs that were solved after POs in L1 were removed
    modifies L2 to refer to the original POs.
    if n=0 adds in L1 and sorts
    """
    if L1 == [] or max(L1)+1 == len(L1):
        return []
    L1_gaps = []
    i=0
    for j in range(len(L1)):
        lj=L1[j]
##        print lj,i
        if lj == i:
            i = i+1
            continue
        assert lj > i,'Error'
        while  lj > i:
            L1_gaps = L1_gaps + [i]
            i = i+1
##            print L1_gaps
        i=i+1
    return L1_gaps


def inject(L,lst,v):
    """
    expends the len(L) by len(lst). puts value v in expanded position
    Preserves values in L, at the end LL should have v in positions lst
    """
    k = i = j = 0 #i indexes L, j indexes lst, and k is total length of LL
    if lst == []:
        return L
    LL = []
    N = len(L) + len(lst)
    while True:
        if lst[j] == k:
            LL= LL + [v]
            if j < len(lst)-1:
                j = j+1
        else:
            LL = LL + [L[i]]
            if i < len(L)-1:
                i = i+1
        k = k+1
        if k >= N:
            break
    return LL

def insert(L1,L):
    """ insert L1 in L in the first places with -1 in L, and return L"""
    k=0
    for j in range(len(L)):
        if L[j] > -1:
            continue
        else:
            L[j] = L1[k]
            k = k+1
            if k >= len(L1):
                break
    return L                   
    

##def duplicate_values(L1,NP):
##    """ append values """
####    L=L1*NP
##    L = L1
##    for j in range(NP-1):
##        L = L+[-1]*len(L1)
##    return L

##def check_and_trim_L(NP,L):
##    """This happens when an unrolling creates additional POs
##    We want to check that L[j] = L[j+kN] etc to make sure the PO results agree
##    in all phases, i.e. sat, unsat, or undecided. if one is sat then make all L[j+kN] sat,
##    If one is unsat, then all L[j+kN] must be unsat. If not then make L[j]=-1.
##    Return first N of L.
##    """
##    N = len(L)/NP #original number of POs
##    for j in range(N):
##        if L[j] == 1:
##            continue
##        for k in range(NP)[1:]: #k = 1,2,...,NP-1
##            if L[j+k*N] == 1:
##                L[j] = 1
##                break
##            elif L[j] == -1:
##                continue #we have to continue to look for a 1
##            elif L[j] == 0:
##                if L[j+k*N] == -1:
##                    print 'some copies of PO unsat and some undecided'
##                    L[j] = -1
##                    break
##            continue #have to make sure that all phases are 0
##    return L[:N]



##def mpr():
##    tt = time.time()
##    N=n_pos()
##    r = pre_simp()
##    if r == Unsat:
##        L = [0]*N
##    else:
##        L = mprove([-1]*n_pos(),'simple',100)
##    L = L[:N]
##    print sumsize(L)
##    print 'Time = %.2f'%(time.time() - tt)
##    return L
##                
##
##def mprove(L,op='simple',tt=1000):
##    """ 0 = unsat, 1 = sat, -1 = undecided"""
##    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time
##    global f_name_save, nam_save, temp_dec, f_name
##    f_name_save = f_name
##    nam_save = '%s_mp_save.aig'%f_name
##    abc('w %s'%nam_save)
##    N = len(L)
##    print 'Length L = %d, n_pos() = %d'%(len(L),n_pos())
##    t = tt #controls the amount of time spent on each cone
##    funcs = [eval('(pyabc_split.defer(%s)())'%op)]
##    funcs = create_funcs(slps,t)+funcs
##    mtds = sublist(methods,slps) + [op]
##    res = L
##    NN = count_less(L,0)
##    rr = range(N)
##    rr.reverse()
##    init_name = init_initial_f_name
##    for j in rr:
##        if L[j] > -1:
##            continue #already solved
##        print '\n************** No. Outputs = %d ******************************'%NN
##        abc('r %s'%nam_save) #restore original function
####        ps()
##        x = time.time()
##        name = '%s_cone_%d.aig'%(f_name,j)
##        print '________%s(%s)__________'%(op,name)
##        abc('cone -s -O %d;scl'%j)
##        abc('w %s_cone.aig'%f_name)
####        ps()
##        read_file_quiet_i('%s_cone.aig'%f_name) #needed to reset initial settings
####        ps()
##        temp_dec = False
##        i,result = fork_last(funcs,mtds)
####        print '\ni = %d, result = %s'%(i,str(result))
##        f_name = f_name_save #restore original f_name
##        print '^^^ f_name restored as %s'%f_name
##        T = '%.2f'%(time.time() - x)
##        out = get_status()
####        print '\nout= %d, result = %s'%(out,str(result))
##        rslt = Undecided
##        if not out == result:
##            print 'out = %d, result = %d'%(out,result)
####        assert out == result,'out = %d, result = %d'%(out,result)
##        if out == Unsat or result == 'UNSAT' or result == Unsat:
##            res[j] = 0
##            rslt = Unsat
##        if out < Unsat:
##            res[j] = 1
##            rslt = Sat
##        print '\n%s: %s in time = %s'%(name,RESULT[rslt],T)
##    abc('r %s'%nam_save) #final restore of original function for second mprove if necessary.
##    init_initial_f_name = init_name
##    print '^^^ init_initial_f_name restored as %s'%init_initial_f_name
####    print res
##    return res
##
####def sp1(options = ''):
####    global sec_options
####    sec_options = options
####    return super_prove(1)
##
def super_prove(n=0,t=2001):
    """Main proof technique now. Does original prove and if after speculation there are multiple output left
    if will try to prove each output separately, in reverse order. It will quit at the first output that fails
    to be proved, or any output that is proved SAT
    n controls call to prove(n)
    if n == 0 do smp and abs first, then spec
    if n == 1 do smp and spec first then abs
    if n == 2 just do quick simplification instead of full simplification, then abs first, spec second
    """
    global max_bmc, init_initial_f_name, initial_f_name,win_list, last_verify_time, f_name
##    print 'sec_options = %s'%sec_options
##    init_initial_f_name = initial_f_name
##    print 'entering super_prove'
    size = str([n_pis(),n_pos(),n_latches(),n_ands()])
    add_trace('[%s: size = %s ]'%(f_name,size))
    if x_factor > 1:
        print 'x_factor = %f'%x_factor
        input_x_factor()
    set_max_bmc(-1,True)
    x = time.time()
    add_trace('prove')
    result = prove(n)
##    print 'prove result = ',
##    print result
    tt = time.time() - x
    if ((result == 'SAT') or (result == 'UNSAT')):
        print '%s: total clock time taken by super_prove = %0.2f sec.'%(result,tt)
        add_trace('%s'%result)
        add_trace('Total time = %.2f'%tt)
        print m_trace
        return [result]+[m_trace]
    elif ((result == 'UNDECIDED') and (n_latches() == 0)):
        add_trace('%s'%result)
        add_trace('Total time = %.2f'%tt)
        print m_trace
        return [result]+[m_trace]
    print '%s: total clock time taken by super_prove so far = %0.2f sec.'%(result,(time.time() - x))
    y = time.time()
    print 'Entering BMC_VER_result'
    add_trace('BMC_VER_result')
    result = BMC_VER_result() #this does backing up if cex is found
    print 'Total clock time taken by last gasp verification = %0.2f sec.'%(time.time() - y)
    tt = time.time() - x
    print 'Total clock time for %s = %0.2f sec.'%(init_initial_f_name,tt)
    add_trace('%s'%result)
    add_trace('Total time for %s = %.2f'%(init_initial_f_name,tt))
    print m_trace
    return [result]+[m_trace]

def reachm(t):
    x = time.clock()
    abc('&get;&reachm -vcs -T %d'%t)
    print 'reachm done in time = %f'%(time.clock() - x)
    return get_status()

def reachp(t):
    x = time.clock()
    abc('&get;&reachp -rv -T %d'%t)
    print 'reachm2 done in time = %f'%(time.clock() - x)
    return get_status()

def scorr():
    run_command('scorr')
    ps()

def select_undecided(L):
    res = []
    for j in range(len(L)):
        l = L[j]
        if l[1] == 'UNDECIDED':
            res = res + [l[0]]
    return res
        

def execute_op(op,L,t):
    """
    run the files in the list L using operation "op", each for max time = t
    """
    global res
    funcs = [eval('(pyabc_split.defer(%s)())'%op)]
    funcs = create_funcs(slps,t)+funcs
    mtds =sublist(methods,slps) + [op]
    res = []
    for j in range(len(L)):
        x = time.time()
        name = L[j]
        print '\n\n\n\n________%s__________'%op
        read_file_quiet_i(name)
        m,result = fork_last(funcs,mtds)
        if result == Undecided:
            result = RESULT[result]
        T = '%.2f'%(time.time() - x)
        new_res = [name,result,T]
        res = res + [new_res]
        print '\n%s'%new_res
    return res

def x_ops(ops,L,t):
    """ execute each op in the set of ops on each file in the set of files of L, each for time t"""
    result = []
    for j in range(len(ops)):
        op = ops[j]
        result.append('Result of %s'%op)
        result.append(execute_op(op,L,t))
    return result

def iso(n=0):
    if n_ands() > 1000000 and not n_latches() == 0:
        print 'circuit too large - over 1000000 ANDS'
        return False
    if n_pos() < 2:
        print 'no more than 1 output'
        return False
    npos=n_pos()
    if n == 0:
        abc('&get;&iso -q;&put')
        if n_pos() == npos:
##            print 'no reduction'
            return False
    else:
        run_command('&get;&iso;&put')
        if n_pos() == npos:
##            print 'no reduction'
            return False
    print 'Reduced n_pos from %d to %d'%(npos,n_pos())
    return True

def isost(n=0):
    if n_ands() > 1000000 and not n_latches() == 0:
        print 'circuit too large - over 1000000 ANDS'
        return False
    if n_pos() < 2:
        print 'no more than 1 output'
        return False
    npos=n_pos()
    if n == 0:
        abc('&get;&isost;&put')
        if n_pos() == npos:
##            print 'no reduction'
            return False
    else:
        run_command('&get;&iso;&put')
        if n_pos() == npos:
##            print 'no reduction'
            return False
    print 'Reduced n_pos from %d to %d'%(npos,n_pos())
    return True

def check_iso(N):
    ans = get_large_po()
    if ans == -1:
        return 'no output found'
    n_iso = count_iso(N)
    return n_iso

def count_iso(N):
    abc('&get;write_aiger -u file1.aig') #put this cone in & space and write file1
##    print 'PO %d is used'%i
    n_iso = 0 #start count
    for i in range(N):
        abc('permute;write_aiger -u file2.aig')
        n = filecmp.cmp('file1.aig','file2.aig')
        print n,
        n_iso = n_iso+n
    print 'the number of isomorphisms was %d out of %d'%(n_iso,N)
    return n_iso

def get_large_po():
##    remove_const_v_pos() #get rid of constant POs
    NL = n_latches()
    NO = n_pos()
    abc('&get') #put the in & space
    n_latches_max = 0
    nl = imax = -1
    for i in range(NO): #look for a big enough PO
        abc('&put;cone -s -O %d;scl'%i)
        nl = n_latches()
        if nl >.15*NL:
            imax = i
##            print 'cone %d has %d FF'%(i,nl)
            break
        if nl> n_latches_max:
            n_latches_max = nl
            imax = i
            print i,nl
        if i == NO-1:
            print 'no PO is big enough'
            return -1
    print 'PO_cone = %d, n_latches = %d'%(imax,nl)

def scorro():
    run_command('scorr -o')
    l = remove_const_v_pos(0)
    ps()

def drw():
    run_command('drw')
    ps()

def dc2rs():
    abc('dc2rs')
    ps()

def reachn(t):
    x = time.clock()
    abc('&get;&reachn -rv -T %d'%t)
    print 'reachm3 done in time = %f'%(time.clock() - x)
    return get_status()
    
def reachx(t=2001):
    x = time.time()
    abc('reachx -t %d'%t)
    print 'reachx  done in time = %f'%(time.time() - x)
    return get_status()

def reachy(t=10001):
    x = time.clock()
    abc('orpos;unfold2;fold2;&get;&reachy -T %d'%t)
##    print 'reachy done in time = %f'%(time.clock() - x)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'reachy returned %s'%str(gs)
    return RESULT[get_status()]
    
def create_funcs(J,t):
    """evaluates strings indexed by J in methods given by FUNCS
    Returns a list of lambda functions for the strings in FUNCs
    If J = [], then create provers for all POs"""
    funcs = []
    for j in range(len(J)):
        k=J[j]
        funcs = funcs + [eval(FUNCS[k])]
    return funcs

def check_abs():
    global init_initial_f_name
    abc('w %s_save.aig'%init_initial_f_name)
    ni = n_pis()
    nl = n_latches()
    na = n_ands()
    abc('r %s_smp_abs.aig'%init_initial_f_name)
    if ((ni == n_pis()) and (nl == n_latches()) and (na == n_ands())):
        return True
    else:
        abc('r %s_save.aig'%init_initial_f_name)
        return False

def modify_methods(J,dec=0):
    """ adjusts the engines to reflect number of processors"""
    N = get_bmc_depth(False)
    L = n_latches()
    I = n_real_inputs()
    npr = n_proc - dec
    reachi = reachs
    if 18 in J: #if sleep in J add 1 more processor
        npr = npr+1
    if ( ((I+L<550)&(N>100))  or  (I+L<400) or (L<80) ):
        if not 24 in J: #24 is reachy
            if L < 70 and not 4 in reachs:
                reachi = reachs #[4] = reachx
            J = reachi+J # add all reach methods
##RKB: temp to test out avy            
##            if len(J)>npr:
##                J = remove_intrps(J) #removes only if len(J)<n_processes
    if len(J)< npr: #if not using all processors, add in pdrs
        for j in range(len(allpdrs)):
            if allpdrs[j] in J: #leave it in
                continue
            else: #add it in
                J = J + [allpdrs[j]]
                if len(J) == npr:
                    break            
    if len(J)>npr:
        J = remove_intrps(J)
    return J


def BMC_VER_result(t=0):
##    return 'UNDECIDED'   #TEMP
    global init_initial_f_name, methods, last_verify_time,f_name,last_gasp_time
    xt = time.time()
    result = 5
    abc('r %s.aig'%f_name)
    abc('scl')
    print '\n***Running proof on %s after scl:'%f_name,
    ps()
##    if t == 0:
####        t = max(2*last_verify_time,last_gasp_time)
##        t = last_gasp_time
##        #each time a new time-out is set t at least 1000 sec.
    if t == 0:
        t = last_gasp_time
    print 'Verify time set to %d'%t
    J = slps + allpdrs + bmcs + intrps + sims
    last_name = seq_name(f_name).pop()
    if not last_name in ['abs','spec']:
        J = slps +allpdrs +bmcs + intrps + sims
##    if 'smp' == last_name or last_name == f_name: # then we try harder to prove it.
    J = modify_methods(J) #if # processors is enough and problem is small enough then add in reachs
    F = create_funcs(J,t)
    mtds = sublist(methods,J)
    print '%s'%mtds
    (m,result) = fork(F,mtds)
    result = get_status()
    if result == Unsat:
        return 'UNSAT'
##    if last_name == 'smp' or last_name == f_name:   # can't backup so just return result
    if not last_name in ['abs','spec']:
        if result < Unsat:
            return 'SAT'
        if result > Unsat: #still undecided
            return 'UNDECIDED'
    else:    # (last_name == 'spec' or last_name == 'abs') - the last thing we did was an "abstraction"
        if result < Unsat:
            if last_name == 'abs':
                add_trace('de_abstract')
            if last_name == 'spec':
                add_trace('de_speculate')
            f_name = revert(f_name,1) # revert the f_name back to previous
            print '^^^ f_name reverted to %s'%f_name
            abc('r %s.aig'%f_name)
            abc('scl')
            return BMC_VER_result() #recursion here.
        else:
            return 'UNDECIDED'
            
def try_split():
    abc('w %s_savetemp.aig'%f_name)
    na = n_ands()
    split(3)
    if n_ands()> 2*na:
        abc('r %s_savetemp.aig'%f_name)
    
def time_diff():
    global last_time
    new_time = time.clock()
    diff = new_time - last_time
    last_time = new_time
    result = 'Lapsed time = %.2f sec.'%diff
    return result

def prove_all_ind():
    """Tries to prove output k by induction, using other outputs as constraints.
    If ever an output is proved
    it is set to 0 so it can't be used in proving another output to break circularity.
    Finally all zero'ed outputs are removed.
    Prints out unproved outputs Finally removes 0 outputs
    """
    global n_pos_proved, n_pos_before
    print 'n_pos_proved = %d'%n_pos_proved
    n_proved = 0
    N = n_pos()
##    l=remove_const_v_pos()
##    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    if n_pos() == 1:
        return
    abc('w %s_osavetemp.aig'%f_name)
    lst = range(n_pos())
##    lst.reverse()
##    list.reverse()
##    for j in list[1:]:
    for j in lst:
##        abc('zeropo -N 0')
        abc('swappos -N %d'%j)
##        l=remove_const_v_pos() #may not have to do this if constr works well with 0'ed outputs
        abc('constr -N %d'%(n_pos()-1))
        abc('fold')
        n = max(1,n_ands())
        f = max(1,min(40000/n,16))
        f = int(f)
##        abc('ind -C 10000 -F %d'%f)
        abc('ind -C 1000 -F %d'%f)
##        run_command('print_status')
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name) #have to restore original here
        if status == Unsat:
##            print 'sign = +',
            abc('zeropo -N %d'%j)
            abc('w %s_osavetemp.aig'%f_name) #if changed, store it permanently
            if j < n_pos_before - n_pos_proved:
                n_proved = n_proved + 1 # keeps track of real POs proved.
        elif status < Unsat:
            print '-%d'%j,
        else:
            print '*%d'%j,
    l=remove_const_v_pos(0)
    n_pos_proved = n_pos_proved + n_proved 
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    print 'n_pos_proved = %d'%n_pos_proved
    #return status

def prove_j_assuming_rest(j):
    global f_name
    ff = f_name
    abc('w %s_temprest.aig'%f_name)
    abc('swappos -N %d'%j)
    abc('constr -N %d'%(n_pos()-1))
    abc('fold')
    super_prove()
    f_name = ff
    print '^^^ f_name restored as %s'%f_name
    abc('r %s_temprest.aig'%f_name)


def prove_all_iso():
    """Tries to prove output k by isomorphism. Gets number of iso-eq_classes as an array of lists.
    Updates n_pos_proved
    """
    global n_pos_proved, n_pos_before
    n_proved = 0
    N = n_pos()
    if n_pos() == 1:
        return
    print 'n_pos_proved = %d'%n_pos_proved
##    run_command('&get;&iso;&put')
    abc('&get;&iso')
    L = eq_classes()
##    print L
    remove_iso(L)
    print '\nThe number of POs reduced by iso was from %d to %d'%(N,n_pos())

def count_less(L,n):
    count = 0
    for j in range(len(L)):
        if L[j] < n:
            count = count + 1
    return count

def prove_all_mtds(t):
    """
    Tries to prove output k  with multiple methods in parallel,
    using other outputs as constraints. If ever an output is proved
    it is set to 0 so it can't be used in proving another output to break circularity.
    Finally all zero'ed ooutputs are removed.
    """
    N = n_pos()
##    l=remove_const_v_pos()
##    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        run_command('swappos -N %d'%j)
##        l=remove_const_v_pos() #may not have to do this if constr works well with 0'ed outputs
        abc('constr -N %d'%(n_pos()-1))
        abc('fold')
##        cmd = '&get;,pdr -vt=%d'%t #put in parallel.
##        abc(cmd)
        verify(pdrs+bmcs+intrps+sims,t)
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name)
        if status == Unsat:
##            print 'sign = +',
            abc('zeropo -N %d'%j)
            abc('w %s_osavetemp.aig'%f_name) #if changed, store it permanently
        print '%d'%j,
    assert not is_sat(), 'one of the POs is SAT' #we can do better than this
    l=remove_const_v_pos(0)
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_all_pdr(t):
    """Tries to prove output k by pdr, using other outputs as constraints. If ever an output is proved
    it is set to 0 so it can't be used in proving another output to break circularity.
    Finally all zero'ed outputs are removed. """
    N = n_pos()
##    l=remove_const_v_pos()
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        abc('swappos -N %d'%j)
##        l=remove_const_v_pos() #may not have to do this if constr works well with 0'ed outputs
        abc('constr -N %d'%(n_pos()-1))
        abc('fold')
        cmd = '&get;,pdr -vt=%d'%t #put in parallel.
        abc(cmd)
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name)
        if status == Unsat:
            print 'sign = +',
            abc('zeropo -N %d'%j)
            abc('w %s_osavetemp.aig'%f_name) #if changed, store it permanently
        print '%d'%j,
    l=remove_const_v_pos(0)
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_each_ind():
    """Tries to prove output k by induction,  """
    N = n_pos()
    l=remove_const_v_pos(0)
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        abc('cone -s -O %d'%j)
        n = max(1,n_ands())
        f = max(1,min(40000/n,16))
        f = int(f)
        abc('ind -u -C 10000 -F %d'%f)
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name)
        if status == Unsat:
            print 'sign = +',
            abc('zeropo -N %d'%j)
            abc('w %s_osavetemp.aig'%f_name) #if changed, store it permanently
        print '%d'%j,
    l=remove_const_v_pos(0)
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_each_pdr(t):
    """Tries to prove output k by PDR. If ever an output is proved
    it is set to 0. Finally all zero'ed outputs are removed. """
    N = n_pos()
    l=remove_const_v_pos(0)
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        abc('cone -O %d -s'%j)
        abc('scl -m')
        abc('&get;,pdr -vt=%d'%t)
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name)
        if status == Unsat:
            print 'sign = +',
            abc('zeropo -N %d'%j)
            abc('w %s_osavetemp.aig'%f_name) #if changed, store it permanently
        print '%d'%j,
    l=remove_const_v_pos(0)
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def prove_POs_sp(t=10000):
    """Tries to prove output k by super_prove.  """
    global f_name
    ffname = f_name
    N = n_pos()
    abc('w %s_POtemp.aig'%f_name)
    list = range(n_pos())
    results = []
    for j in list:
        f_name = ffname #reset name
        print '^^^ f_name restored as %s'%f_name
        f_name = f_name + '_PO_%s'%j
        print '^^^ temp f_name set to %s'%f_name
        abc('r %s_POtemp.aig'%f_name)
        print '\n\n********Solving %s PO %d with super_prove()************'%(f_name,j)
        abc('cone -O %d -s'%j)
        abc('scl -m')
        super_prove()
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name)
        if status == Unsat:
            result='UNSAT'
        elif status == Sat:
            result = 'SAT'
        else:
            result = 'UNDECIDED'
        print '\nPO %d found %s'%(j,result)
        results = results = results + [result]
    return results
    #return status

def disprove_each_bmc(t):
    """Tries to prove output k by PDR. If ever an output is proved
    it is set to 0. Finally all zero'ed ooutputs are removed. """
    N = n_pos()
    l=remove_const_v_pos(0)
    print '0 valued output removal changed POs from %d to %d'%(N,n_pos())
    abc('w %s_osavetemp.aig'%f_name)
    list = range(n_pos())
    for j in list:
        abc('cone -O %d -s'%j)
        abc('scl -m')
        abc('bmc3 -T %d'%t)
        status = get_status()
        abc('r %s_osavetemp.aig'%f_name)
        if status == Sat:
            print 'sign = +',
            abc('zeropo -N %d'%j)
            abc('w %s_osavetemp.aig'%f_name) #if changed, store it permanently
        print '%d'%j,
    l=remove_const_v_pos(0)
    print '\nThe number of POs reduced from %d to %d'%(N,n_pos())
    #return status

def add_pord(s):
    global pord_trace
    pord_trace = pord_trace + [s]

def pord_1_2(t):
    """ two phase pord. First one tries with 10% of the time. If not solved then try with full time"""
    global n_pos_proved, ifpord1, pord_on, pord_trace
    #first eliminate easy POs
    ttt = n_ands()/1000
    if ttt < 100:
        ttt=100
    elif ttt<200:
        ttt = 200
    elif ttt< 300:
        ttt = 300
    else:
        ttt = 500
    S,lst,L = par_multi_sat(ttt,1,1,1)
    lst = indices(L,1)
    if 1 in L:
        return [Sat]+[['par_multi_sat: SAT']]
    if -1 in L:
        restrict_v(L,-1)
    else: return [Unsat] + [['par_multi_sat: UNSAT']]
    pord_trace = []
    pord_on = True # make sure that we do not reparameterize after abstract in prove_2
    n_pos_proved = 0
    if n_pos()<4:
        return [Undecided] +[pord_trace]
    if ifpord1:
        add_pord('pord1')
        t_time = .1*t
        print 'Trying each output for %0.2f sec'%(.1*t)
        result = pord_all(.1*t) #we want to make sure that there is no easy cex.
        if (result <= Unsat):
            return [result] + [pord_trace]
    return [Undecided] + [pord_trace]
        
def pord_all(t,n=4):
    """Tries to prove or disprove each output j by PDRM BMC3 or SIM. in time t"""
    global cex_list, n_pos_proved, last_cx, pord_on, ifpord1,pord_trace
    print 'last_cx = %d, time = %0.2f'%(last_cx,t)
    btime = time.time()
    N = n_pos()
    prove_all_ind() ############ change this to keep track of n_pos_proved
    nn = n_pos()
    abc('w %s_osavetemp.aig'%f_name)    
    if nn < n or nn*t > 300: #Just cut to the chase immediately.
        return Undecided
    lst = range(n_pos())
    proved = disproved = []
    abc('&get') #using this space to save original file.
    ### Be careful that & space is not changed.
    cx_list = []
    n_proved = 0
    lcx = last_cx + 1
    lst = lst[lcx:]+lst[:lcx]
    lst.reverse()
    n_und = 0
    for j in lst:
        print '\ncone %s. '%j,
        abc('&r -s %s_osavetemp.aig'%f_name) #for safety
        abc('&put; cone -s -O %d'%j) #puts the &space into reg-space and extracts cone j
        #requires that &space is not changed. &put resets status. Use &put -s to keep status
        abc('scl -m')
        ps()
##        print 'running sp2'
        ###
        result = run_sp2_par(t)
        if result == 'UNDECIDED':
            n_und = n_und + 1
            status = Undecided
            if ((n_und > 1) and not ifpord1):
                break
        elif result == 'SAT':
            status = Sat
            disproved = disproved + [j]
            last_cx = j
            cx = cex_get()
            cx_list = cx_list + [cx]
            assert len(cx_list) == len(disproved), cx_list
            if len(cx_list) > 0:
                break
        else: #is unsat here
            status = Unsat
            proved = proved + [j]
            if j < n_pos_before - n_pos_proved:
                n_proved = n_proved +1
##    n_pos_proved = n_pos_proved + n_proved. #this should not be here because we should start fresh
    print '\nProved %d outputs'%len(proved)
    print 'Disproved %d outputs'%len(disproved)
    print 'Time for pord_all was %0.2f'%(time.time() - btime)
    NN = len(proved+disproved)
    cex_list = cx_list
    if len(disproved)>0:
        assert status == Sat, 'status = %d'%status
        n_pos_proved = 0 #we want to reset this because of a bad speculation
        return Sat
    else:
        n_pos_proved1 = n_pos_proved + n_proved
        n_pos_proved2 = n_pos_proved + len(proved) #don't know why we need this
        if nn == n_pos_proved1 or nn == n_pos_proved2:
            return Unsat
        abc('r %s_osavetemp.aig'%f_name)
##        abc('&put') # returning original to work spece
        remove(proved,0)
        print '\nThe number of unproved POs reduced from %d to %d'%(N,n_pos()),
        ps()
        if n_pos() > 0:
            return Undecided
        else:
            return Unsat

##def bmc_ss(t):
##    """
##    finds a set cexs in t seconds starting at 2*N where N is depth of bmc -T 1
##    The cexs are put in the global cex_list
##    """
##    global cex_list
##    x = time.time()
##    abc('bmc3 -a -C 1000000 -T %f'%(t))
##    if is_sat():
##        cex_list = cex_get_vector() #does this get returned from a concurrent process?
##        n = count_non_None(cex_list)
##        L = list_non_None(cex_list)
##        print '%d cexs found in %0.2f sec'%(n,(time.time()-x))
####        remove_disproved_pos(cex_list)
##    else:
##        L = []
##    return L

def iso_slp(t=30):
    F = [eval('pyabc_split.defer(sleep)(t))')]
    F = F = F+[eval('(pyabc_split.defer(iso)())')]
    for i,res in pyabc_split.abc_split_all(F):
        if i == 0:
            return 

def show_partitions(L):
    for i in range(len(L)):
        abc('&r -s %s.aig'%L[i])
        print '\nSize = ',
        run_command('&ps')
        abc('&popart')
        eqs = eq_classes()
        N = len(eqs)
        print 'No. of partitions = %d'%N
        if N == 1:
            continue
        l = []
        for j in range(N):
            l=l + [len(eqs[j])]
        print l


def r_part(name):
    read_file_quiet_i(name)
    abc('&get;&scl;&scorr -C 2;&put')
    res1 = reparam()
    res2 = False
    npos = n_pos()
##    if n_pos() < 100:
##        res2 = iso()
##    ps()
    if n_pos() < 1000:
        iso()
    if n_pos() < 500:
        abc('r %s.aig'%name)
        abc('w %s_leaf.aig'%name)
        return 
##        abc('w %s_leaf.aig'%name)
##        return 
    res = two_eq_part()
    if res == False:
        abc('r %s.aig'%name)
        abc('w %s_leaf.aig'%name)
        return
    elif min(res) < .2*max(res) and min(res) < 500:
        abc('r %s.aig'%name)
        abc('w %s_leaf.aig'%name)
        return
    else:                           #recur
        r_part('%s_p0'%name)
        r_part('%s_p1'%name)
        return

def two_eq_part():
    abc('&get;&popart')
    part = eq_classes()
    if len(part) == 1:
        print 'Partition has only one part'
        return False
    abc('w %s_save.aig'%f_name)
    nn = n_pos()
    p1=p0 = []
    init = True
    for i in range(len(part)): #union first half together together
        if init == True:
            p0=p0 + part[i]
            if len(p0)>nn/2:
                init = False
        else:
            p1 = p1 + part[i]
    p0.sort()
    p1.sort()
    abc('&get')
    remove(p1,1)
    n0=n_pos()
##    print 'writing %s_p0.aig'%f_name
    abc('w %s_p0.aig'%f_name)
    abc('r %s_save.aig'%f_name)
    remove(p0,1)
##    print 'writing %s_p1.aig'%f_name
    n1=n_pos()
    abc('w %s_p1.aig'%f_name)
    return [n0,n1]

def merge_parts(p,n):
    parts = []
    end = []
    for i in range(len(p)):
        if len(p[i]) > n:
            parts = parts + [p[i]]
        else:
            end =end + p[i]
    parts = parts + [end]
    return parts
        

def extract_parts(S=11):
    abc('&get;&popart -S %d'%S)
    part = eq_classes()
    if len(part) == 1:
        print 'Partition has only one part'
        return 1
    parts = merge_parts(part,2)
    lp=len(parts)
    print 'Found %d parts'%lp
    abc('w %s_save.aig'%f_name)
    for i in range(lp):
        abc('r %s_save.aig'%f_name)
        p=[]
        for j in range(lp):
            if i == j:
                continue
            else:
                p = p + parts[j]
        remove(p,1)
        abc('&get;&scl;&lcorr;&put')
        abc('w %s_part%d.aig'%(f_name,i))
    return len(parts)

def two_part():
    abc('&get;&popart')
    part = eq_classes()
    if len(part) == 1:
        print 'Partition has only one part'
        return False
    part1 = part[1:] #all but the 0th
    p1=[]
    for i in range(len(part1)): #union together
        p1=p1 + part1[i]
    p1.sort()
    abc('w %s_p.aig'%f_name)
    remove(p1,1)
##    print 'writing %s_p0.aig'%f_name
    abc('w %s_p0.aig'%f_name)
    n0=n_pos()
    abc('r %s_p.aig'%f_name)
    p0 = part[0]
    p0.sort()
    remove(p0,1)
##    print 'writing %s_p1.aig'%f_name
    n1=n_pos()
    abc('w %s_p1.aig'%f_name)
    return [n0,n1]

def set_t_gap(t1,t2):
    nam = max(30000,n_ands())
    ratio = 1+float(nam-30000)/float(70000)
    gp = .5*ratio*t2
##    gp = min(100,gp)
    t = min(100,ratio*t1)
    return (t,gp)
    
def par_multi_sat(t=10,gap=0,m=1,H=0,opo=[]):
    """ m = 1 means multiple of 1000 to increment offset"""
    global last_gap
    abc('w %s_save.aig'%f_name)
    if opo == []:
        opo = range(n_pos())
    if not gap == 0:
        gt = gap = last_gap
        if t < 1000:
            if not t == 0:
                if gap == 0:
                    gap = max(.2,.5*t)
                    gap = max(15,gap)
                if gap > t:
                    t=gap
                t,gt = set_t_gap(t,gap)
                gt = max(15,gt)
                if gt <= last_gap:
                    gt = 1.3*last_gap
            else:
                t = gt = 5
            gt = min(350,gt)
            if gt > t:
                t = 1.5*gt
            last_gap = gt
        ##    H = max(100, t/n_pos()+1)
            if not H == 0: #set timeout limit per output
                H = (gt*1000)/n_pos()
                H = max(min(H,1000*gt),100)
    else:
        last_gap = gt = gap = t
    tme = time.time()
    tt = 1.3*t
    list0 = []
##    list0 = listr_v_pos(v=0) #reduces POs
##    list0.sort()
####    print 'list0 = %s'%str(list0)
####    if len(list0)>0:
####        print 'removed %d cost-0 POs'%len(list0)
####    ps()
##    if len(list0)> 0:
##        print 'Found initial %d const-0 POs'%len(list0)
##        tlst = [opos[list0[i]] for i in range(len(list0))]
##        opos = remove_sub(list(opos),tlst)
##        assert len(opos) == n_pos(),'len(opos),n_pos() = %d,%d'%(len(opos),n_pos())
####        print ll
    print 'par_multi_sat entered for %.2f sec. and gap = %.2f  sec., H = %.2f'%(tt,gt,H)
    base = m*1000
    if not m == 1:
        offset = (m-1)*32000
        abc('&get;&cycle -F %d;&put'%offset)
    mx = 1000000000/max(1,n_latches())
    N = n_pos()
    na = n_ands()
    print 't,gap,H(per PO) = %.2f,%.2f,%.2f'%(tt,gt,H)
    F = [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,H))'%(0))]
##    if na < 50000:
    F = F + [eval('(pyabc_split.defer(pdraz)(t,gt,H))')] #need pdr in??
    F = F + [eval('(pyabc_split.defer(mprove_and)(t,gt,0,H))')]
    F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,0,4,0))')]
    F = F + [eval('(pyabc_split.defer(sleep)(tt))')]
    F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,4,0))'%(100))]
    F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(100))]
    if mx > 1*base:      
        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,1,97))'%(1*base))]
        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(1*base))]
##    if mx > 2*base:
##        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d))'%(2*base))]
##        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(2*base))]
    if mx > 4*base and na < 400000:
        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,4,23))'%(4*base))]
        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(4*base))]
##    if mx > 8*base and na < 300000:
##        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,3,53))'%(8*base))]
##        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(8*base))]
##    if mx > 16*base and na < 200000 :
##        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,2,79))'%(16*base))]
##        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(16*base))]
##    if mx > 32*base and na < 100000:      
##        F = F + [eval('(pyabc_split.defer(sim3az)(t,gt,%d,1,97))'%(32*base))]
##        F = F + [eval('(pyabc_split.defer(bmc3az)(t,gt,%d,0))'%(32*base))]
    ss=LL=L = [] 
    S = 'UNDECIDED'
    bmc0_done = pdr0_done = sim30_done = False
    s=ss = [-1]*n_pos()
    ii = []
    nn = len(F)
    for i,res in pyabc_split.abc_split_all(F): #res[0] not used.
        ii = ii + [i]
        if i == 4: #sleep timeout
            print 'sleep timeout'
            break
        if i == 0:# bmc with start at 0 is done
            bmc0_done = True 
        if i == 1: #pdr with start 0 is done
            pdr0_done = True
        if i == 3:#sim3 with start 0 is done
            sim30_done = True
        if res == None: #this can happen if one of the methods bombs out
            print 'Method %d returned None'%i
            continue
        n_old = count_less(s,0)
        s = merge_s(list(s),res[1])
        new_res = not n_old == count_less(s,0)
        if count_less(s,0) == 0: #all POs solved
            S = 'UNSAT'
            break
        if not new_res and bmc0_done and pdr0_done and sim30_done:
            break
        if len(ii) == len(F)-1: #all done but sleep
            break
    print 'time = %.2f'%(time.time()-tme)
    ss = expand(s,list0,0) #xxxx list0 = [] local variables
    print 'SAT = ',[opo[j] for j in range(len(ss)) if ss[j] == 1] #xxxx
    print 'UNSAT = ',[opo[j] for j in range(len(ss)) if ss[j] == 0]
##    assert list0 == indices(ss,0)
    print '\nPar_multi_sat result = %s'%sumsize(ss)
##    assert check_consistancy(L,ss), 'inconsistant'
    abc('r %s_save.aig'%f_name) #restore initial aig
    return S,[],ss


def check_consistancy(L,s):
    """ L is list of SAT's found. s is index of all"""
    consistant = True
    print 'checking s[L]'
    for j in L: #make sure that s[L] = 1
##        print j,
##        print s[j]
        if not s[j] == 1:
            print j,
            consistant = False
    print 'checking s=1 => L'
    for j in range(len(s)): #make sure that there are no other 1's
        if s[j] == 1:
            if not j in L:
                print j,
                consistant = False
    return consistant
        

def check_s(s1,s2):
    #same as [i for i in xrange(len(s1)) if (s1[i] == 0 and s2[i] == 1) or (s1[i] == 1 and s2[i] == 0)]
    assert len(s1) == len(s2),'lengths do not match'
    miss = []
    for i in range(len(s1)):
        if (s1[i] == 0 and s2[i] == 1) or (s1[i] == 1 and s2[i] == 0):
            miss = miss + [i]
    print miss
        

def merge_s(s1,s2):
    # same as [max(s1[i],s2[i]) for i in xrange(len(s1))]
    if s2 == []:
        return s1
    assert len(s1) == len(s2), 'error in lengths, s1 = %s, s2 = %s'%(str(s1),str(s2))
    s = [-1]*len(s1)
    for i in range(len(s1)):
        if not s1[i] == s2[i]:
            if s1[i] == -1 or s2[i] == -1:
                s[i] = max(s1[i],s2[i])
            else:
                print 'error: conflict in values at i = %d'%i
                print 's1[i]=%d,s2[i]=%d'%(s1[i],s2[i])
        else: #put in common value
            s[i] = s1[i]
    return s

def switch(ss):
    """ This changes the convention of SAT and UNSAT to SAT = 1, UNSAT = 0"""
    #same as [not ss[i] for i in xrange(len(ss)) if ss[i] == 0 or ss[i] == 1]
    s1 = ss
    for i in range(len(ss)):
        si = ss[i]
        if si == 0:
            s1[i] = 1
        elif si == 1:
            s1[i] = 0
    return s1
        

##def pdr_ss_r(t):
##    """
##    assumes that 0 POs have been removed
##    finds a set cexs in t seconds. Returns list of SAT POs found
##    """
##    global cex_list
##    x = time.time()
##    abc('pdr -az -T %f'%(t))
##    if is_sat():
##        print 'entering cex  get vector'
##        cex_list = cex_get_vector() #does this get returned from a concurrent process?
####        n = count_non_None(cex_list)
##        print len(cex_list)
##        L = list_non_None(cex_list)
##        n = len(L)
##        print '%d cexs found in %0.2f sec.'%(n,(time.time()-x))
##        if n == len(cex_list):
##            print 'all remaining POs are SAT'
####            return L
##        else:
##            remove_disproved_pos(cex_list) #note that this will not remove all POs
##    else:
##        L = []
##    print 'T = %0.2f'%(time.time()-x)
##    return L

##def bmc_ss_r(t):
##    """
##    assumes that 0 POs have been removed
##    finds a set cexs in t seconds. Returns list of SAT POs found
##    """
##    global cex_list
##    x = time.time()
##    abc('bmc3 -az -C 1000000 -T %f'%(t))
##    if is_sat():
##        print 'entering cex  get vector'
##        cex_list = cex_get_vector() #does this get returned from a concurrent process?
####        n = count_non_None(cex_list)
##        L = list_non_None(cex_list)
##        n= len(L)
##        print '%d cexs found in %0.2f sec.'%(n,(time.time()-x))
##        if n == len(cex_list):
##            print 'all remaining POs are SAT'
####            return L
##        else:
##            remove_disproved_pos(cex_list) #note that this will not remove all POs
##    else:
##        L = []
##    print 'T = %0.2f'%(time.time()-x)
##    return L

##def sim_ss_r(t):
##    """
##    assumes that 0 POs have been removed
##    finds a set cexs in t seconds. Returns list of SAT POs found
##    """
##    global cex_list
##    x = time.time()
##    run_command('sim3 -az -T %f'%(t))
##    if is_sat():
##        print 'entering cex  get vector'
##        cex_list = cex_get_vector() #does this get returned from a concurrent process?
####        n = count_non_None(cex_list)
##        L = list_non_None(cex_list)
##        n = len(L)
##        print '%d cexs found in %0.2f sec.'%(n,(time.time()-x))
##        if n == len(cex_list):
##            print 'all remaining POs are SAT'
####            return L
##        else:
##            remove_disproved_pos(cex_list) #note that this will not remove all POs
##    else:
##        L = []
##    print 'T = %0.2f'%(time.time()-x)
##    return L

##def check_None_status(L,s=[],v=0):
##    """ L is the PO numbers that had non_None in
##    0 means sat and 1 means unsat is
##    v tells which value means sat"""
##    if s == []:
##        s = status_get_vector()
##    error = False
##    for j in L:
##        if s[j] == v:
##            continue
##        else:
##            error = True
##    for i in range(len(s)):
##        if s[i] == v:
##            if i in L:
##                continue
##        else:
##            error = True
##    if error:
##        print 'status and non_None do not agree'
##        print 'L = %d'%L
##        print 'SAT and UNSAT counts switched'
##        print sumsize(s)


def list_non_None(lst):
    """ return [i for i,s in enumerate(cex_list) if not s == None]"""
    L = []
    for i in range(len(lst)):
        if not lst[i] == None:
            L = L + [i]
    return L

def get_frames(lst):
    """lst is a list of cex's"""
    L = []
    for i in xrange(len(lst)):
        if not lst[i] == None:
            L.append(lst[i].get_frame())
    return res

def count_non_None(lst):
    #return len([i for i,s in enumerate(cex_list) if not s == None]
    count = 0
    for i in range(len(lst)):
        if not lst[i] == None:
            count = count + 1
    return count

##def remove_disproved_pos(lst):
##    for i in range(len(lst)):
##        if not lst[i] == None:
##            abc('zeropo -N %d'%i)
##    l=remove_const_v_pos(0)

def remove_proved_pos(lst):
    for i in range(len(lst)):
        if  lst[i] > -1:
            abc('zeropo -N %d'%i)
    remove_const_v_pos(0)

def bmc_par_jmps(t=2001,s=0,j=1,c=500,d=0):
    """ s is starting frame, j is number of frames to jump,
    c is conflict limit per PO, and d is total conflictbefore jump
    when (not d == 0) is specified, it keeps jumping after d conclicts
    """
    mtds = funcs =[]
    s0 = s-2
    for i in range(5):
        s = s0+2*i
        mtds = mtds + ['bmc_jump(%d)'%(s)]
        funcs = funcs + [eval('(pyabc_split.defer(bmc_j)(t,s,j,c,d))')]
##    print mtds
    mtd,res = fork(funcs,mtds)
    print res
    return [res[0],mtd]

def par_bss(t,s):
    funcs = [eval('(pyabc_split.defer(sleep)(t))')]
    funcs = funcs + [eval('(pyabc_split.defer(bmc_par_jmps)(t,s))')]
    funcs = funcs + [eval('(pyabc_split.defer(simple)(t,1))')]
##    funcs = funcs + [eval('(pyabc_split.defer(sp)(2,t,False))')]
    mtds = ['sleep','bmcjmps','simple','simple']
    mtds = mtds[:3]
##    print mtds
    i,res = fork(funcs,mtds) #all these should be returning 'SAT', 'UNSAT'...
    #assert cexpo == cex_po(), 'cexpo,cex_po() = %d,&d'%(cexpo,cex_po())
    print mtds[i],res
    return res
                          
def bmc_j(t=2001,s=0,j=2,c=5000,d=5000):
    cmd = 'bmc3 -r -C %d -J %d -D %d -S %d'%(c,j,d,s)
    abc(cmd)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'bmc_j returned %s'%str(gs)
    return RESULT[get_status()]

        
def bmc_j2(t=2001):
    """ finds a cex in t seconds starting at 2*N where N is depth of bmc -T 1"""
    x = time.time()
    tt = min(5,max(1,.05*t))
    abc('bmc3 -r -T %0.2f'%tt)
    if is_sat():
##        print 'cex found in %0.2f sec at frame %d'%((time.time()-x),cex_frame())
        return RESULT[get_status()]
##    abc('bmc3 -T 1')
    N = n_bmc_frames()
    N = max(1,N)
##    print bmc_depth()
##    abc('bmc3 -C 1000000 -T %f -S %d'%(t,int(1.5*max(3,max_bmc))))
##    cmd = 'bmc3 -J 2 -D 4000 -C 1000000 -T %f -S %d'%(t,2*N)
    cmd = 'bmc3 -r -C 2000 -J %d'%(2*N+2)
##    print cmd
    abc(cmd)
##    if is_sat():
##        print 'cex found in %0.2f sec at frame %d'%((time.time()-x),cex_frame())
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'bmc_j2 returned %s'%str(gs)
    return RESULT[get_status()]

def pdrseed(t=2001):
    """uses the abstracted version now"""
##    abc('&get;,treb -rlim=60 -coi=3 -te=1 -vt=%f -seed=521'%t)
    abc('&get;,treb -rlim=100 -vt=%f -seed=521'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'pdr_seed returned %s'%str(gs)
    return RESULT[get_status()]

def pdrold(t):
    abc('&get; ,pdr -vt=%f'%t)
    return RESULT[get_status()]

def pdr(t=2001):
    abc('&get; ,treb -vt=%f'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'pdr returned %s'%str(gs)
    return RESULT[get_status()]

def avy(t=2001):
##    abc('&get; avy --verbose=3 --min-suffix=1 --sat-simp=0 --itp-simp=0\
##    --shallow-push=1 --reset-cover=1 --glucose --glucose-itp --opt-bmc=1')
    abc('&get; avy --reset-cover=1 --itp=0 --min-suffix=yes '
                '-a --tr0 --shallow-push=1 --stutter=0')
##    abc('&get; avy')
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'avy returned %s'%str(gs)
    return RESULT[get_status()]

def pdr0(t=2001):
    abc('&get; ,pdr -rlim=100 -vt=%f'%t)
    return RESULT[get_status()]

def pdra(t=2001):
####    temporarily disabled for experiment
##    return 'UNDECIDED'
##    abc('&get; ,treb -abs -rlim=100 -sat=abc -vt=%f'%t)
    abc('&get; ,treb -abs -rlim=100 -vt=%f'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'pdra returned %s'%str(gs)
    return RESULT[get_status()]

def pdrae(t=2001):
    abc('&get; ,treb -abs -rlim=100 -vt=%f'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'pdra returned %s'%str(gs)
    return RESULT[get_status()]

def pdrm(t=2001):
    abc('pdr -C 0 -T %f'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'pdrm returned %s'%str(gs)
    return RESULT[get_status()]

def pdrmnct(t=2001):
    abc('pdr -nct -C 0 -T %f'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'pdrm returned %s'%str(gs)
    return RESULT[get_status()]

def pdrmnc(t=2001):
    abc('pdr -nc -C 0 -T %f'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'pdrm returned %s'%str(gs)
    return RESULT[get_status()]

def pdrmyuf(t=2001):
    abc('pdr -yuf -C 0 -T %f'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'pdrm returned %s'%str(gs)
    return RESULT[get_status()]

def pdrm_exact(t=2001):
    abc('pdr -s -C 0 -T %f'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'pdr_exact returned %s'%str(gs)
    return RESULT[get_status()]

def pdrmm(t):
    abc('pdr -C 0 -M 298 -T %f'%t)
    return RESULT[get_status()]

def bmc2(t):
    abc('bmc2 -T %d'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'bmc2 returned %s'%str(gs)
    return RESULT[get_status()]

def BMCsp(t):
##    return RESULT[3] #temp maybe a bug in &bmcs
    ''' uses new sat solver from Valera
     P refers to glucose instead of satuko'''
    abc('&get; &bmcs -P 1 -T %d'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print '&bmcs returned %s'%str(gs)
    return RESULT[get_status()]

def bmce(t=2001):
##    abc('&get; ,bmc -vt=%d'%t)
    abc('&get; ,bmc -timeout=%0.2f -vt=%0.2f'%(t,t))
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'bmc returned %s'%str(gs)
    return RESULT[get_status()]

def intrp(t=2001):
    abc('&get; ,imc -vt=%d'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'intrp returned %s'%str(gs)
    return RESULT[get_status()]

def mprove_and(t=2001,gt=10,C=999,H=0):
    t_init = time.time()
    tt = .9*t
    if  not C == 0:
        abc('&get; &cycle -F %d; &put'%C) 
    abc('&get; &mprove -T %.2f -G %.2f -H %.2sf'%(tt,gt,H))
    cex_list = cex_get_vector()
    if cex_list is None:
        cex_list = [None]*n_pos()
    L = list_non_None(cex_list)
    tt = time.time()-t_init
    print 'mprove_and(%.2f,%.2f,%.2f): time = %.2f, SAT = %d'%(tt,gt,H,tt,len(L))
##    print 'Length CEXs = %d'%(len(L))
    s = status_get_vector()
##    print sumsize(s)
    if s is None:
        s = [-1]*n_pos()
    elif len(s) == 0: #error if this happens check with Alan
        s = [-1]*n_pos()
    sss = switch(list(s))
##    print 's_status = %s'%sumsize(sss)
    return L,sss

def bmc3az(t=2001,gt=10,C=999,H=0):
    t_init = time.time()
    if  not C == 0:
        abc('&get; &cycle -F %d; &put'%C) 
    abc('bmc3 -azr -T %.2f -G %.2f -H %.2f'%(t,gt,H))
##    cex_list = cex_get_vector()
##    L = list_non_None(cex_list)
    print 'bmc3az(%.2f,%.2f,%d,%d): time = %.2f'%(t,gt,C,H,(time.time()-t_init)),
    ss = status_get_vector()
    if ss is None:
        s = [-1]*n_pos()
    else:
        s = switch(ss)
    print sumsize(s)
    return -1,s

def set_initial(start):
    if start == 0:
        xa('init -z')
    elif start == 1:
        xa('init -o')
    else:
        assert len(start) == n_latches(),'new initial state not = n_latches'
        xa('init -S start')

def remove_sub(L,I):
    """removes sublist I from list L"""
    return [L[i] for i in xrange(len(L)) if not L[i] in I]

def keep_sub(L,I):
    """like L[I]"""
    return [L[i] for i in xrange(len(L)) if L[i] in I]

def sum_col(d,j):
    """ print the sum of column j"""
    sum = 0
    for i in range(len(d)):
        sum += d[i][j]
    return sum

def print_d_stats(d):
    res = []
    for i in d.keys():
        res.append([i,len(d[i])])
    print res

def count_cycles(d):
    sum1 = sum2 = di_old = 0
    for i in xrange(len(d)):
        di0 = eval(d[i][0])
        di1 = d[i][1]
        sum1 += di0*di1
        sum2 += (di0 - di_old)+di1
        di_old = di0
    max_comp = sum1/sum2
    print max_comp, sum1,sum2


def bmc3x(t=20,start=0,f=1):
    """ start at state and run bmc3 for f frames
    return the set of POs hit"""
    set_initial(start)
    abc('bmc3 -axvr -T %.2f -F %d'%(t,f))
    x =cex_get_vector()
    #the value of  get_frame here is one less than get_frame after a single cex
    D = [1+x[i].get_frame() for i in xrange(len(x)) if not x[i] == None]
    POs = [i for i in xrange(len(x)) if not x[i] == None]
##    print D
    set_initial(0)
    return POs,D

def chain_cycles_pos(t=40,restart=1):
    """ builds a list of [cycles to next bad state,pos] """
    itime = time.time()
    reinit = True
    poh_chain = []
    pos_hit = []
    po_summary = []
    poh_tot = 0
    dmin = -1
    POs_left = range(n_pos())
    abc('w %s_init.aig'%f_name) #this is the aig with the original initial state.
    while True:
        #find distance to closest bad state
        if dmin == -1:
            abc('bmc3 -T %d'%t)
            dmin = cex_frame()
            if dmin == -1:
                print "\ncan't continue present chain"
                if pos_hit == 0:
                    break
        if dmin == -1:
            if restart: # restart at the initial state with hit POs removed
                ps()
                run_command('r %s_init.aig'%f_name)
                POs_left = range(n_pos()) #global PO IDs
##                print poh_chain
                pos_hit = pos_hit + keep_sub(POs_left,poh_chain)
                print '\ntotal POs hit so far: %d'%len(pos_hit)
##                print pos_hit
                POs_left = remove_sub(POs_left,pos_hit)
                assert max(pos_hit) < n_pos(),'max PO is %d'%max(pos_hit)
                remove(pos_hit,1) #pos_hit are global id's of POs hit so far
                abc('scl')
                print '\ntrying a new chain'
                ps()
                abc('bmc3 -T %d'%t)
                dmin = cex_frame()
                if dmin == -1: #can't get anything new restarting from initial aig
                    print 'nothing new on new chain'
                    break
                else:
                    print '\nstarting new chain with first depth = %d'%dmin
                    reinit = True
                    poh_chain = []
            else:
                break
        else: #continue chain
            abc('init -c;zero') #initialize to bad state
            poh_new,D = bmc3x(40,0,1) # get all hit POs in 1 frame
            poh_chain = poh_chain + keep_sub(POs_left,poh_new)
            po_summary.append([dmin,len(poh_new),reinit]) #running summary
            if len(poh_new) == n_pos(): #can't remove all POs.
                print 'all POs are hit'
                break
            POs_left = remove_sub(POs_left,poh_new)
            remove(poh_new,1)
            abc('scl')
            print [dmin, len(poh_new)],
            dmin = -1
    print '\nchain: fname = %s, time = %.2f'%(f_name,time.tFime()-itime)
    return po_summary

def list_depth_pos(t=20,start=0,f=1):
    """ builds a list of [depth,#pos hit at that depth]"""
    itime = time.time()
    S = []
    d =[]
    POs,D = bmc3x(t,start,f)
##    D.sort()
    for i in range(len(D)):
        if D[i] in S:
            continue
        di = D[i] #depth of ith cex
        pos = [POs[j] for j in xrange(len(D)) if D[j] == di] #POs hit at depth di
        if not pos == []:
            S.append(di)
##            print S
##            d.update({di:pos}) #put in dictionary
            d.append([di,len(pos)]) #temp
##            print d
##            print [di,len(pos)]
##        print d
    print '\ndepths: fname = %s, time = %.2f'%(f_name,time.time()-itime)
##    print d
    d.sort()
##    print d
    return d

def run_example(t=40,restart=True):
    print 'example: %s'%f_name,
    ps()
    d = list_depth_pos(t,0,10000)
    if not d == []:
        d1=[d[i][1] for i in xrange(len(d))]
        print '\nnumber POs hit by depths = %d'%reduce(lambda x,y:x+y,d1)
    dc = chain_cycles_pos(t,restart)
    ratio = compression_ratio(d,dc)
    new_ratio = new_compression_ratio(d,dc)
    return new_ratio,d,dc

def compression_ratio(d,dc):
    """ this is only approximate since d and dc may hit a different # or POs"""
    if not d == []:
        d0=[d[i][0] for i in xrange(len(d))]
        d1=[d[i][1] for i in xrange(len(d))]
        print '\nnumber POs hit by depths = %d'%reduce(lambda x,y:x+y,d1)
        dp=[d0[i]*d1[i] for i in xrange(len(d))]
        old_cycles = reduce(lambda x,y:x+y,dp)
    if not dc == []:
        dc0=[dc[i][0] for i in xrange(len(dc))]
        dc1=[dc[i][1] for i in xrange(len(dc))]
        print 'number POs hit by chain = %d'%reduce(lambda x,y:x+y,dc1)
        dcp=[dc0[i]+dc1[i] for i in xrange(len(dc))]
        new_cycles = reduce(lambda x,y:x+y,dcp)
        ratio = float(new_cycles)/float(old_cycles)
        print 'old_cycles = %d'%old_cycles
        print 'new_cycles = %d'%new_cycles
##        print 'compression ratio = %.2f'%ratio
        return ratio
    return 0


def new_compression_ratio(d,dc):
    """ Only compares the first N PO hits."""
    if not d == [] and not dc == []:
        d0=[d[i][0] for i in xrange(len(d))]
        d1=[d[i][1] for i in xrange(len(d))]
        po_totd = reduce(lambda x,y:x+y,d1)
        dc0=[dc[i][0] for i in xrange(len(dc))]
        dc1=[dc[i][1] for i in xrange(len(dc))]
        po_totdc = reduce(lambda x,y:x+y,dc1)
        dp=[d0[i]*d1[i] for i in xrange(len(d))]
        d_cycles = reduce(lambda x,y:x+y,dp)
        dcp = [dc0[i]+dc1[i] for i in xrange(len(dc))]
        dc_cycles = reduce(lambda x,y:x+y,dcp)
        print '\ncomparing # cycles to hit first %d POs'%min(po_totd,po_totdc)
        if po_totd < po_totdc:
            dc_cycles = pot = 0
            for i in range(len(dc)):
                dc_cycles = dc_cycles + dc0[i] + dc1[i]
                pot = pot + dc1[i]
                if pot > po_totd:
                    break
        else:
            d_cycles = pot = 0
            for i in range(len(d)):
                d_cycles = d_cycles + d0[i]*d1[i]
                pot = pot + d1[i]
                if pot > po_totdc:
                    break
        ratio = float(dc_cycles)/float(d_cycles)
        print 'new compression ratio = %.2f'%ratio
        return ratio            
    return 0


def display_dict(d):
    r = d.keys()
    r.sort()
    ss = [len(d[k]) for k in r]
    print zip(r,ss)

def remove_pos_list(nlist):
    l = [-1]*n_pos()
    for i in range(len(l)):
        l[i]=1
    remove_pos(l)

##def bmc3as(t=0,start=0,C=0,H=0):
##    t_init = time.time()
##    abc('bmc3 -azxr -T %.2f -S %d'%(t,start))
##    x = cex_get_vector()
####    L = [i for i in xrange(n_pos()) if not x[i] == None]
##    D = [x[i].get_frame() for i in xrange(len(x)) if not x[i] == None]
##    print 'bmc3as(%.2f,%d): time = %.2f'%(t,start,(time.time()-t_init)),
##    s = switch(status_get_vector())
##    print sumsize(s),
##    D.append(set_max_bmc(max_bmc,chtr=False))
##    d = max(D)
##    print ' max depth = %d'%d
##    return d,s

def pdraz(t=2001,gt=10,H=0):
    """ H = runtimelimit per output. 0 => none
    gt is gap time """
##    print 'pdraz entered with t = %.2f, gt = %.2f, H = %.2f'%(t,gt,H)
    t_init = time.time()
    run_command('pdr -az -T %d -G %d -H %.2f'%(t,gt,H))
##    cex_list = cex_get_vector()
##    L = list_non_None(cex_list)
##    check_None_status(L)
    ss = status_get_vector()
    if ss is None:
        s = [-1]*n_pos()
    else:
        s = switch(ss)
##    print sumsize(s)
##    print 'Number of UNSAT POs = %d'%(len(s) - count_less(s,1))
    print 'pdraz(%.2f,%.2f,%d): time = %.2f'%(t,gt,H,(time.time()-t_init)),
    print sumsize(s)
    return -1,s

def sim3az(t=2001,gt=10,C=1000,W=5,N=0):
    """ N = random seed, gt is gap time, W = # words, F = #frames"""
    t_init = time.time()
    if  not C == 0:
        abc('&get; &cycle -F %d; &put'%C) 
    abc('sim3 -az -T %.2f -G %.2f -F 40 -W %d -N %d'%(t,gt,W,N)) #this is only one simulation???
    ss = status_get_vector()
##    print ss
    if ss is None:
        s = [None]*n_pos()
    else:
        s = switch(ss)
    L = list_non_None(s)
##    check_None_status(L)
    s = [-1]*n_pos()
    for i in L:
        s[i] = 1 #1 indicates SAT here
    print 'sim3az(%.2f,%.2f,%d,%d,%d): time = %.2f'%(t,gt,C,W,N,(time.time()-t_init)),
    print sumsize(s)
    return -1,s


##def sim3az2(t=2001,gt=10):
##    """ N = random seed, gt is gap time, W = #words, F = #frames
##    a round R is simulation for F frames. After each round, rarity info is
##    collected and updated. A restart is  done after S rounds, when a new
##    random seed is gotten, we restart from the initial state, but rarity information
##    is preserved.
##    """
##    global seed
##    t_init = time.time()
##    s = [-1]*n_pos()
##    f,w,b,r,res = (20,50,16,700,0)
##    while True:
##        ss = list(s)
##        for k in range(9):
##            t_old = time.time()
####            f = min(f*2, 3500)
####            res = min(max(f/4,30),50)
####            w = max(((w+1)/2)-1,2)
##            abc('sim3 -az -T %.2f -G %.2f -F %d -W %d -N %d -B %d -R %d -S %d'%(gt,gt/2,f,w,seed,b,r,res))
##            print 'done with sim3'
##            L = list_non_None(cex_get_vector())
##            print 'len(L) = %d'%len(L)
##            seed = seed + 23
##            s_old = list(s)
##            print sumsize(s)
##            for i in L:
##                s[i] = 1 #1 indicates SAT here
##            print sumsize(s)
##            no_new = (s == s_old)
##            t_new = time.time()
##            lap_time = (t_new - t_old)
##            print 'lap_time = %.2f, '%lap_time,
##            print sumsize(s)
##            print no_new, t, gt,(t_new-t_init),(t_new+lap_time-t_init)
##            print f,w,seed,b,r,res
##            if (lap_time > gt and no_new) or lap_time > t or (t_new - t_init) > t:
##                break
##            if (t_new+lap_time -t_init) > t: #not enough time left for another lap
##                break
##        no_new = (s == ss)
##        if (lap_time > gt and no_new) or lap_time > t or (t_new - t_init) > t:
##            break
##        if (t_new+lap_time - t_init) > t: #not enough time left
##            break 
##    print 'sim3az2(%.2f,%.2f): time = %.2f'%(t,gt,(time.time()-t_init)),
##    print sumsize(s)
##    return -1,s
    
def bmc3(t=2001):
    abc('bmc3 -r  -T %d'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'bmc3 returned %s'%str(gs)
    return RESULT[get_status()]

def bmc3s(t=2001):
    abc('bmc3 -rs  -T %d'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'bmc3 returned %s'%str(gs)
    return RESULT[get_status()]

def intrpm(t=2001):
    abc('int -T %d'%t)
    gs = prob_status()
    if not gs in [0,1,-1]:
        print 'intrpm returned %s'%str(gs)
    #print 'intrpm: status = %d'%get_status() 
    return RESULT[get_status()]

def split(n):
    global aigs
    abc('orpos;&get')
    abc('&posplit -v -N %d;&put;dc2'%n)
    res =a_trim()

def keep_splitting():
    for j in range(5):
        split(5+j)
        no = n_pos()
        status = prove_g_pos_split()
        if status <= Unsat:
            return status
        if no == n_pos():
            return Undecided

def drill(n):
    run_command('&get; &reachm -vcs -H 5 -S %d -T 50 -C 40'%n)


def pre_reduce():
    x = time.clock()
    pre_simp()
    write_file('smp')
    abstract(ifbip)
####    write_file('abs')
    print 'Time = %0.2f'%(time.clock() - x)

def sublist(L,I):
    """ like L[I] """
    # return [s for i,s in enumerate(L) if i in I]
    z = []
    for i in range(len(I)):
        s = L[I[i]],
        s = list(s)
        z = z + s
    return z

#PARALLEL FUNCTIONS
"""  funcs should look like
funcs = [pyabc_split.defer(abc)('&get;,bmc -vt=50;&put'),pyabc_split.defer(super_prove)()]
After this is executed funcs becomes a special list of lambda functions
which are given to abc_split_all to be executed as in below.
It has been set up so that each of the functions works on the current aig and
possibly transforms it. The new aig and status is always read into the master when done
"""

def tf():
    result = top_fork()
    return result

def top_fork(J,t):
    global x_factor, final_verify_time, last_verify_time, methods
    set_globals()
    mtds = sublist(methods,J)
    F = create_funcs(J,t)
    print 'Running %s in parallel for max %d sec.'%(mtds,t)
    (m,result) = fork_last(F,mtds) #FORK here
    return get_status()

def run_sp2_par(t):
    """ Runs the single method simple, timed for t seconds."""
    global cex_list,methods, pord_trace
    J = slps+[6] #6 is the 'simple' method
##    mtds = sublist(methods,J)
##    print mtds,
    print 'time = %0.2f'%t
    funcs = create_funcs(J,t) 
    y = time.time()
    for i,res in pyabc_split.abc_split_all(funcs):
##        print 'i,res = %d,%s'%(i,res)
        T = time.time()-y
        if i == 0:
            print 'Timer expired in %0.2f'%T
            return 'UNDECIDED'
        else:
##            print i,res
            #note simple returns a vector
            mtd = res[1]
            ress = res[0]
            if ress == 'UNSAT':
                print 'simple proved UNSAT in %0.2f sec.'%T
                add_pord('UNSAT by %s'%mtd)
                return 'UNSAT'
            elif ress == 'UNDECIDED':
                print 'simple returned UNDECIDED in %0.2f sec.'%T
                return 'UNDECIDED'
            if ress == 'SAT':
                print 'simple found cex in %0.2f sec. in output %d'%(T,cex_po())
                add_pord('SAT by %s'%mtd)
                return 'SAT'
            else:
                assert False, 'ress = %s'%ress

def run_parallel(J,t,BREAK='US'):
    """ Runs the listed methods J, each for time = t, in parallel and
    breaks according to BREAK = subset of '?USLB'"""
    global cex_list,  methods
    mtds = sublist(methods,J)
    F = create_funcs(J,t) #if J = [] we are going to create functions that process each output separately.
                            #if 18, then these are run in parallel with sleep
    if ((J == []) ):
        result = fork_break(F,mtds,BREAK)
##        #redirect here to suppress printouts.
##        with redirect.redirect( redirect.null_file, sys.stdout ):
##            with redirect.redirect( redirect.null_file, sys.stderr ):
##                result = fork_break(F,mtds,BREAK)
    elif 'L' in BREAK:
        result = fork_last(F,mtds)
    elif 'B' in BREAK:
        result = fork_best(F,mtds)
    else:
        result = fork_break(F,mtds,BREAK)
    return result

def fork_all(funcs,mtds):
    """Runs funcs in parallel and continue running until all are done"""
    global methods
    y = time.time()
    for i,res in pyabc_split.abc_split_all(funcs):
        status = prob_status()
        t = time.time()-y
        if not status == -1: #solved here
            if status == 1: #unsat
                print '%s proved UNSAT in %f sec.'%(mtds[i],t)
            else:
                print '%s found cex in %f sec. in output %d - '%(mtds[i],t,cex_po()),
                if not mtds[i] == 'REACHM':
                    print 'cex depth at %d'%cex_frame()
                else:
                    print ' '
            continue
        else:
            print '%s was undecided in %f sec. '%(mtds[i],t)
    return i,res

def fork_break(funcs,mtds,BREAK='US'):
    """
    Runs funcs in parallel and breaks according to BREAK <= '?US'
    If mtds = 'sleep' or [], we are proving outputs in parallel
    Saves cex's found in cex_list in case we are proving POs.
    """
    global methods,last_verify_time,seed,cex_list,last_winner,last_cex
    seed = seed + 3 # since parallel processes do not chenge the seed in the prime process, we need to change it here
    cex_list = lst = []
    y = time.time() #use wall clock time because parent fork process does not use up compute time.
    for i,res in pyabc_split.abc_split_all(funcs):
        status = get_status()
        t = time.time()-y
        lm = len(mtds)
        if ((lm < 2) and not i == 0): # the only single mtds case is where it is 'sleep'
            M = 'Output %d'%(i-lm)
        else:
            M = mtds[i]
            last_winner = M
        if M == 'sleep':
            print 'sleep: time expired in %0.2f sec.'%(t)
##            return 0,[Undecided]+[M]
##            assert status >= Unsat,'status = %d'%status
            break
        if ((status > Unsat) and '?' in BREAK): #undecided
            break
        elif status == Unsat or res == 'UNSAT': #unsat
            print '%s: UNSAT in %0.2f sec.'%(M,(t))
            status = Unsat
            if 'U' in BREAK:
                break
        elif status < Unsat or res == 'SAT': #status == 0 - cex found
            status = Sat
            if M in methods:                
                if methods.index(M) in exbmcs+allreachs+allpdrs+[1]: #set the known best depth so far. [1] is interp
                    set_max_bmc(n_bmc_frames(),True)
            last_cex = M
            if M in engines: #in recursive calls after a sat result lwe may come through here more than once we want to record the underlying
                    #PO that was found SAAT by a true engine.
##                print cex_po()
##                cexpo = cex_po() #store this because it  might get corrupted????
                print '%s: -- cex in %0.2f sec. at depth %d in output %d => '%(M,t,cex_frame(),cex_po()),
                cex_list = cex_list+[cex_get()] #accumulates multiple cex's and puts them on list.
                if len(cex_list)>1:
                    print 'len(cex_list): %d'%len(cex_list)
            if 'S' in BREAK:
                break
        else:
            continue
    add_trace('%s by %s'%(RESULT[status],M))
##    if status == Sat:
##        assert cexpo == cex_po(), 'cexpo,cex_po() = %d,%d'%(cexpo,cex_po())
    return i,[status]+[M]

def fork_best(funcs,mts):
    """ fork the functions, If not solved, take the best result in terms of AIG size"""
    global f_name
    n = len(mts)-1
    r = range(len(mts))
    y = time.time()
    m_best = -1
    best_size = [n_pis(),n_latches(),n_ands()]
##    print best_size
    abc('w %s_best_aig.aig'%f_name)
    for i,res in pyabc_split.abc_split_all(funcs):
        if mts[i] == 'sleep':
            m_best = i
            break
        r = delete(r,i)
        if len(r) == 1:
            if mts[r[0]] == 'sleep':
                break
        status = prob_status()
        if not status == -1: #solved here
            m = i
            t = time.time()-y
            if status == 1: #unsat
                print '%s proved UNSAT in %f sec.'%(mts[i],t)
            else:
                print '%s found cex in %f sec. in output %d - '%(mts[i],t,cex_po()),
            break
        else:
            cost = rel_cost(best_size)
            if cost < 0:
                best_size = [n_pis(),n_latches(),n_ands()]
                m_best = i
                abc('w %s_best_aig.aig'%f_name)
    abc('r %s_best_aig.aig'%f_name)
    add_trace('%s'%mts[m_best])
    return m_best,res

def delete(r,i):
    """ remove element in the list r that corresponds to i """
    ii = r.index(i)
    z = []
    for i in range(len(r)):
        if i == ii:
            continue
        else:
            z = z + [r[i]]
    return z
    

def take_best(funcs,mts):
    """ fork the functions, If not solved, take the best result in terms of AIG size"""
    global f_name
    n = len(mts)-1
    y = time.time()
    m_best = -1
    best_size = 1000000
    abc('w %s_best_aig.aig'%f_name)
    for i,res in pyabc_split.abc_split_all(funcs):
        if n_ands() < best_size:
            best_size = n_ands()
            m_best = i
            abc('w %s_best_aig.aig'%f_name)
    abc('r %s_best_aig.aig'%f_name)
    return m_best,res

def fork_last(funcs,mtds):
    """ fork the functions, and take first definitive answer, but
    if last method ends first, then kill others"""
    global m_trace,hist,sec_options
    n = len(mtds)-1
    m = -1
    y = time.time()
    sres =lst = ''
##    print mtds
    #print 'starting fork_last'
    for i,res in pyabc_split.abc_split_all(funcs):
##        print i,res
##        print 'Method %s: depth = %d '%(mtds[i],n_bmc_frames())
        status = prob_status()
        if mtds[i] == 'par_scorr' and n_ands() == 0:
            add_trace('UNSAT by %s'%res)
            return i,Unsat
        if mtds[i] == 'initial_speculate':
            add_trace('initial_speculate: %s'%str(res))
            print 'initial_speculate returned %s'%str(res)
            return res
        if not status == -1 or res in ['SAT','UNSAT']: #solved here
            m = i
            t = int(time.time()-y)
            if status == 1 or res == 'UNSAT': #unsat
                sres = str(res)
                res = Unsat
                print '%s proved UNSAT in %d sec.'%(mtds[i],t)
            else:
                res = Sat
                print '%s found cex in %0.2f sec. in output %d - '%(mtds[i],(t),cex_po()),
            break
        elif i == n: #last forked call ended.
##            print res
            if mtds[i] == 'PRE_SIMP':
                m_trace = m_trace + [res[1]]
                hist = res[2] #pre_simp must return hist because hist in not passed otherwise.
##                print hist
            t = int(time.time()-y)
            m = i
##            print res
            if not (res == 'UNSAT' or  res[0] == Unsat):
                print '%s: UNDECIDED in %d sec.'%(mtds[i],t)
                res = Undecided
            else:
                res = Unsat
            ps()                
            break
        elif mtds[i] == 'sleep':
            res = Undecided
            t = time.time()-y
            print 'Timer expired in %0.2f'%t
            break
        lst = lst + ', '+mtds[i]
##    sres = str(res)
    if sres[:5] == 'scorr':
        add_trace('UNSAT by %s'%sres)
        return m,Unsat
    add_trace('%s by %s'%(RESULT[res],mtds[i]))
    return m,res

def fork(funcs,mtds):
    """ runs funcs in parallel This keeps track of the verify time
    when a cex was found, and if the time to find
    the cex was > 1/2 allowed time, then last_verify_time is increased by 2"""
    global win_list, methods, last_verify_time,seed
    beg_time = time.time()
    i,res = fork_break(funcs,mtds,'US') #break on Unsat of Sat.
    t = time.time()-beg_time        #wall clock time because fork does not take any compute time.
    if t > .4*last_verify_time:
##    if t > .15*last_verify_time: ##### temp
        t = last_verify_time = last_verify_time + .1*t
        #print 'verify time increased to %s'%convert(t)
    assert res[0] == get_status(),'res: %d, status: %d'%(res,get_status())
##    add_trace('%s by %s'%(RESULT[res[0]],mtds[i]))
    
##    assert cexpo == cex_po(), 'cexpo,cex_po() = %d,%d'%(cexpo,cex_po())
    return i,res

def save_time(M,t):
    global win_list,methods
    j = methods.index(M)
    win_list = win_list + [(j,t)]
    #print win_list

def summarize(lst):
    result = [0]*10
    for j in range(len(lst)):
        k = lst[j]
        result[k[0]]=result[k[0]]+k[1]
    return result

def top_n(lst,n):
    result = []
    ll = list(lst) #makes a copy
    m = min(n,len(ll))
    for i in range(m):
        mx_index = ll.index(max(ll))
        result = result + [mx_index]
        ll[mx_index] = -1
    return result

def super_pre_simp():
    while True:
        nff = n_latches()
        print 'Calling pre_simp'
        pre_simp()
        if n_latches() == nff:
            break

#______________________________
#new synthesis command

####def synculate(t):
####    """
####    Finds candidate sequential equivalences and refines them by simulation, BMC, or reachability
####    using any cex found. If any are proved, then they are used to reduce the circuit. The final aig
####    is a new synthesized circuit where all the proved equivalences are merged.
####    If we put this in a loop with increasing verify times, then each time we work with a simpler model
####    and new equivalences. Should approach srm. If in a loop, we can remember the cex_list so that we don't
####    have to deal with disproved equivalences. Then use refine_with_cexs to trim the initial equivalences.
####    If used in synthesis, need to distinguish between
####    original outputs and new ones. Things to take care of: 1. a PO should not go away until it has been processes by merged_proved_equivalences
####    2. Note that &resim does not use the -m option where as in speculation - m is used. It means that if
####    an original PO isfound to be SAT, the computation quits becasue one of the output
####    miters has been disproved.
####    """    
####    global G_C,G_T,n_pos_before, x_factor, n_latches_before, last_verify_time, f_name,cex_list, max_verify_time
####    
####    
####    def refine_with_cexs():
####        """Refines the gores file to reflect equivalences that go away because of cexs in cex_list"""
####        global f_name
####        abc('&r %s_gores.aig'%f_name)
####        for j in range(len(cex_list)):
####            cex_put(cex_list[j])
####            run_command('&resim') #put the jth cex into the cex space and use it to refine the equivs
####        abc('&w %s_gores.aig'%f_name)
####        return
####    
####    def generate_srms():
####        """generates a synthesized reduced model (srms) from the gores file"""
####        global f_name, po_map
####        abc('&r %s_gores.aig; &srm -sf; r gsrms.aig; w %s_gsrms.aig'%(f_name,f_name))
####        print 'New srms = ',ps()
####        po_map = range(n_pos())
####        return 'OK'
####
####    def merge_proved_equivalences():
####        #this only changes the gores file.
####        run_command('&r %s_gores.aig; &equiv_mark -vf %s_gsrms.aig; &reduce -v; &w %s_gores.aig'%(f_name,f_name,f_name))
####        return
####
####    def generate_equivalences():
####        set_globals()
####        t = max(1,.5*G_T)
####        r = max(1,int(t))
####        cmd = "&get; &equiv2 -C %d -F 200 -T %f -S 1 -R %d"%((G_C),t,r)
####        abc(cmd)
####        #run_command('&ps')
####        eq_simulate(.5*t)
####        #run_command('&ps')
####        cmd = '&semi -W 63 -S 5 -C 500 -F 20 -T %d'%(.5*t)
####        abc(cmd)
####        #run_command('&ps')
####        run_command('&w %s_gores.aig'%f_name)
####
####    l=remove_const_v_pos() #makes sure no 0 pos to start
####    cex_list = []
####    n_pos_before = n_pos()
####    n_latches_before = n_latches()
######    print 'Generating equivalences'
####    generate_equivalences()
######    print 'Generating srms file'
####    generate_srms() #this should not create new 0 pos
######    if n_pos()>100:
######        removed
####    l=remove_const_v_pos()
####    n_pos_last = n_pos()
####    if n_pos_before == n_pos():
####        print 'No equivalences found. Quitting synculate'
####        return Undecided_no_reduction
####    print 'Initial synculation: ',ps()
######    ps()
####    set_globals()
####    simp_sw = init = True
####    simp_sw = False #temporary
####    print '\nIterating synculation refinement'
####    abc('w initial_sync.aig')
####    max_verify_time = t
####    print 'max_verify_time = %d'%max_verify_time
####    """
####        in the following loop we increase max_verify_time by twice time spent to find last cexs or Unsat's
####        We iterate only when we have proved cex + unsat > 1/2 n_pos. Then we update srms and repeat.        
####    """
####    while True:                 # refinement loop
####        t = max_verify_time     #this may have been increased since the last loop
######        print 'max_verify_time = %d'%max_verify_time
####        set_globals()
####        if not init:
####            generate_srms()     #generates a new gsrms file and leaves it in workspace
######            print 'generate_srms done'
####            if n_pos() == n_pos_before:
####                break
####            if n_pos() == n_pos_last:   #if nothing new, then quit if max_verification time is reached.
####                if t > max_verify_time:
####                    break
####            if simp_sw:                     #Warning: If this holds then simplify could create some 0 pos
####                na = n_ands()
####                simplify()
####                while True:
####                    npo = n_pos()
######                    print 'npos = %d'%npo
####                    merge_proved_equivalences() #So we need to merge them here. Can merging create more???
####                    generate_srms()
####                    if npo == n_pos():
####                        break
####                if n_ands() > .7*na:            #if not significant reduction, stop simplification
####                    simp_sw = False             #simplify only once.
####            if n_latches() == 0:
####                return check_sat()
####        n_pos_last = n_pos()
####        init = False                        # make it so that next time it is not the first time through
####        syn_par(t)
####        if (len(cex_list)+len(result)) == 0: #nothing happened aand ran out of time.
####            break
####        abc('w %s_gsrms.aig'%f_name)
####        #print 'No. of cexs after syn_parallel = %d'%len(cex_list)
####        merge_proved_equivalences()         #changes the underlying gores file by merging fanouts of proved eqs
####        #print 'merge done'
####        refine_with_cexs()                  #changes the gores file by refining the equivalences in it using cex_list.
####        #print 'refine_with_cexs done'
####        continue
####    extract(0,n_pos_before) #get rid of unproved outputs
####    return
####
####def syn_par(t):
####    """prove n outputs at once and quit at first cex. Otherwise if no cex found return aig
####    with the unproved outputs"""
####    global trim_allowed,max_verify_time, n_pos_before
####    global cex_list, result
####    b_time = time.time()
####    n = n_pos()
####    if n == n_pos_before:
####        return
####    mx = n_pos()
####    if n_pos() - n_pos_before > 50:
####        mx = n_pos_before + 50
####    r = range(n_pos_before, mx)     
####    N = max(1,(mx-n_pos_before)/2)
####    abc('w %s__ysavetemp.aig'%f_name) 
####    F = [eval(FUNCS[18])] #create a timer function
####    #print r
####    for i in r:
####        F = F + [eval('(pyabc_split.defer(verify_only)(%d,%d))'%(i,t))]
####    cex_list = result = []
####    outcome = ''
####    #redirect printout here
######    with redirect.redirect( redirect.null_file, sys.stdout ):
######        with redirect.redirect( redirect.null_file, sys.stderr ):
####    for i,res in pyabc_split.abc_split_all(F):
####        status = get_status()
######        print i
####        if i == 0:          #timed out
####            outcome = 'time expired after = %d'%(time.time() - b_time)
####            break
####        if status < Unsat:
####            cex_list = cex_list + [cex_get()]                    
####        if status == Unsat:
####            result = result + [r[i-1]]
####        if (len(result)+len(cex_list))>= N:
####            T = time.time() - b_time
####            if T > max_verify_time/2:
####                max_verify_time = 2*T
####            break
####        continue
####    if not outcome == '':
####        print outcome
######    print 'cex_list,prove_list = ',cex_list,result
####    abc('r %s__ysavetemp.aig'%f_name) #restore initial aig so that pos can be 0'ed out
####    if not result == []: # found some unsat's
######        min_r = min(result)
######        max_r = max(result)
######        no = n_pos()
######        assert (0 <= min_r and max_r < no), 'min_r, max_r, length = %d, %d, %d'%(min_r,max_r,len(result))
####        zero(result)
####    return
####    #print "Number PO's proved = %d"%len(result)
####
####def absec(n):
####    #abc('w t.aig')
####    for j in range(n):
####        print '\nFrame %d'%(j+1)
####        run_command('absec -F %d'%(j+1))
####        if is_unsat():
####            print 'UNSAT'
####            break
####    
####
####"""
####    we might be proving some original pos as we go, and on the other hand we might have some equivalences that we
####    can't prove. There are two uses, in verification
####    verification - we want to remove the proved pos whether they are original or not. But if a cex for an original, then need to
####                    remember this.
####    synthesis - the original outputs need to be kept and ignored in terms of cex's - supposedly they can't be proved.
####"""
####
####""" Experimental"""
####
####def csec():
####    global f_name
####    if os.path.exists('%s_part0.aig'%f_name):
####        os.remove('%s_part0.aig'%f_name)
####    run_command('demiter')
####    if not os.path.exists('%s_part0.aig'%f_name):
####        return
####    run_command('r %s_part0.aig'%f_name)
####    ps()
####    run_command('comb')
####    ps()
####    abc('w %s_part0comb.aig'%f_name)
####    run_command('r %s_part1.aig'%f_name)
####    ps()
####    run_command('comb')
####    ps()
####    abc('w %s_part1comb.aig'%f_name)
####    run_command('&get; &cec %s_part0comb.aig'%(f_name))
####    if is_sat():
####        return 'SAT'
####    if is_unsat():
####        return 'UNSAT'
####    else:
####        return 'UNDECIDED'

    ###########################
####        we will verify outputs ORed in groups of g[i]
####        here we take div = N so no ORing
##        div = max(1,N/1)
##        g = distribute(N,div)
##        if len(g) <= 1:
##            t = tt
##        g.reverse()
####        print g
##        x = 0
##        G = []
##        for i in range(div):
##            y = x+g[i]
##            F = F + [eval('(pyabc_split.defer(verify_range)(%d,%d,%s))'%(x,y,convert(t)))]
##            G = G + [range(x,y)]
##            x = y
####        print G
###########################


def get_lib():
    run_command('read_genlib vsclib013.genlib')

def map_a_iter():
    run_command('map -a')
    mm = n_area()
    abc('write_blif %s_min_map.blif'%f_name)
    while True:
        run_command('st; dch; map -a; ps')
        if n_area() < mm:
            mm = n_area()
            abc('write_blif %s_min_map.blif'%f_name)
        else:
            break
    abc('read_blif %s_min_map.blif'%f_name)
    return n_area()
        
    
""" These commands map into luts and leave the result in mapped format. To return to aig format, you
have to do 'st'
"""
def sop_balance(k=4):
    '''minimizes LUT logic levels '''
##    kmax = k
    kmax=min(k+2,15)
    abc('st; if -K %d;ps'%kmax)
    print nl(),
##    for i in range(1):
##        abc('st; if -K %d;ps'%kmax)
##        run_command('ps')
    kmax=min(k+2,15)
    abc('st; if  -g -C %d -K %d -F 2;ps'%(10,kmax)) #balance
    print nl(),
    for i in range(1):
        abc('st;dch; if -C %d -K %d;ps'%(10,kmax))
        print nl(),

def speedup(k=6):
    run_command('&get;&st;&syn2;&st;&if -K %d -C 16 -g;&ps;&st;&synch2;&st;&if -K %d -C 16;&ps;&mfs;&ps;&put'%(k,k))
    print nl()

#+++++++++++++++++ start SCC +++++++++++++++++++++++++++++++
def get_SCCs():
    global fi,fo,all_seen
    global n_init_pis, n_init_latches,n_init_pos

##    fi = fi_sig(n_init_pis,n_init_pos)
##    fo = fo_sig(fi)
    check_fifo(fi,fo)
    all_seen = set([]) #indicates it is already in an SCC
    sccs = []
    for i in range(n_pos()): # do each of the POs
        if i in all_seen: # already in some scc
            continue
        if fo[i] == [] or fi[i] == []:
            scci = set([-i]) # -i means scc singleton with no self loop
        else:
            tfoi = tfo(i) # list of nodes in transitive fanout of i
                #excluding all_seen
##            print len(tfoi)
            tfii = tfi(i) # list of nodes in transitive fanin of i
                #excluding all_seen
            scci = tfoi&tfii
##            print [len(tfii),len(tfoi),len(scci)],
            if len(scci) == 1 and not i in fo[i]: #i is always in tfii and tfoi
                scci = set([-i]) #case when no self loop on node i
        sccs.append(list(scci)) # list of co's in same scc as co i
        if len(scci) > 1:
            print 'SCC size %d '%len(scci),
        if scci == [-i]:
            all_seen.add(i) # a singeton scc
        else:
            all_seen = all_seen | scci
    return sccs

def fo_sig(fi=[]):
    """ get fanout signals of each comb PO"""
    global n_init_pis, n_init_latches,n_init_pos,lengths
    if fi == []:
        fis = fi_sig(n_init_pis,n_init_pos)
    else:
        fis = fi       
    fos = [set([]) for i in range(n_pos())]
    for i in range(len(fos)):
        for j in fis[i]:
            if j > -1:
                fos[j].add(i)
    fos = [list(fos[j]) for j in xrange(len(fos))]
    return fos

def fo_sig_pi(fi=[]):
    """ get fanouts of the pis"""
    global n_init_pis, n_init_latches,n_init_pos,lengths
    if fi == []:
        fis = fi_sig(n_init_pis,n_init_pos)
    else:
        fis = fi       
    fos = [set([]) for i in range(n_init_pis)]
    for i in range(n_pos()):
        fisi= [(abs(j)-1) for j in fis[i] if j < 0] #restrict to PIs
        for j in fisi:
            fos[j].add(i)
    for j in range(len(fos)):
        fosj = list(fos[j])
        fosj.sort()
        fos[j] = fosj
##    fos = [list(fos[j]) for j in xrange(len(fos))]
    return fos

def iso_map(fo_pi,isos2):
    """ map fanouts into their iso groups"""
    mp = get_map(isos2)
    res = []
    for j in range(len(fo_pi)):
        foj = fo_pi[j]
        setj = set([])
        for i in foj:
            setj.add(mp[i])
        lj = list(setj)
        lj.sort()
        res.append(lj)
    return res

def group_PIs(fi,isos2):
    """ find common groupa of fanouts and put them in same 'iso' group of PIs"""
    fo_pi = fo_sig_pi(fi)
    iso_fo = iso_map(fo_pi,isos2)
    fog = [[iso_fo[i],i] for i in range(len(iso_fo))]
    fog.sort()
    sort_order = [fog[i][1] for i in xrange(len(fog))] # split apart
    fos = [fog[i][0] for i in xrange(len(fog))] #XXX
    ispi = gp_pis(fos,sort_order)
    return fo_pi,fos,sort_order,ispi
            
def gp_pis(x,o): #XXX
    res = []
    lst = []
    last = -100000
    for i in range(len(x)):
        if x[i] == last:
            lst.append(o[i]) #add to list
        else:
            res.append(lst)
            last = x[i]
            lst = [o[i]] #start new list
    res.append(lst)
    return res[1:]
    


def fi_sig(npi=0,npo=1):
    """ get the fanins signals of each comb PO"""
    global n_init_pis, n_init_latches,n_init_pos,lengths
    if npi == 0 and npo == 1:
        npi = n_init_pis
        npo = n_init_pos
    fis=[]
    for i in range(n_pos()): # no. of co's
        coi = co_supp(i) # fanins of ith PO or flop Needs original comb circuit in space
        co = set([])
        for j in coi:
            if j < npi:
                co.add(j-npi)
            else:
                co.add(j-npi+npo)
        fis.append(list(co))
    return fis


def print_pr(L):
    for j in range(len(L)):
        if not len(L[j]) == 0:
            print '%d. '%j+prpr(L[j])


def prpr(L0):
    """ print with only the beginning and end of consecutive numbers"""
    s=''
    j_old =-2
    L = L0+[-1]
    for j in L:
        if not j == j_old +1:
            if not j_old == -2:
                if j_beg == j_old:
                    s = s + ', %d'%(j_beg)
                else:
                    s = s + ', %d-%d'%(j_beg,j_old)
            j_beg = j
        j_old = j
    return s[2:]

                    
def get_map(x):
    """ expands list of lists x into index list L where L[i] = j
    means i is in jth list of x"""
    xc=list(x)
    x_map = [-1]*n_pos()
    for i in range(len(xc)):
        xci = xc[i]
        if len(xci) == 1:
            xci[0] = abs(xci[0])
        for j in xci: # PO j is in the ith x
            x_map[j]=i # in ith x
    return x_map


def layer(x):
    Lx = len(x)
    ly = [0]*Lx
    tbd = set(range(Lx))
    while not len(tbd) == 0:
        i = tbd.pop()
        for j in x[i]:
            if ly[j] <= ly[i]:
                ly[j] = ly[i]+1
                tbd.add(j)
                assert ly[j] < Lx,'loop'
##        tbd.add(x[i])
    return ly

def lsort(x):
    """ sorts a lattice, given the immediate fanins of each node."""
    ly = layer(x)
    xx = []
    for i in range(max(ly)+1):
        for j in range(len(x)):
            if ly[j] == i:
                xx.append(j)
    return xx
        
##def fi_scc(scc,fi):
##    """ get list of signal inputs for each scc """
##    fi_sc=[]
##    for i in range(len(scc)):
##        fii= set([])
##        for j in scc[i]:
##            fii = fii | set(fi[j])
##        fii = list(fii)
##        fii.sort()
##        fi_sc.append(fii)
##    return fi_sc


##def scc_fi(scc,fi):
##    """ get the immediate fanins of the scc's in terms of scc's """
##    if len(scc) < 2:
##        print "single node SCC  for entire graph"
##        return [[]]
##    scc_map = get_map(scc)
##    print 'scc_map done'
##    assert not -1 in scc_map, '-1 at location %d'%scc_map.index(-1)
##    scfi = []
##    for j in range(len(scc)): # jth scc
##        fij = get_scfi(j,scc,fi,scc_map) #returns a set
##        fij = list(fij)
##        fij.sort()
##        scfi.append(fij)
##    return scfi

#+++++++++++++++ end SCC ++++++++++++++++++++++++++++++++++++

def get_ctrl_data(gp,fi,counts=False):
    """ a control signal is one that is a common input to a non-trivial group"
     and a data signal i ""n input that is not common"""
    Lg = [i for i in range(len(gp)) if len(gp[i]) > 7]
##    Lg.sort()
    print 'non-trivial widths/frequency: ',[[Lg[i],len(gp[Lg[i]])] for i in range(len(Lg))]
##    ct = [] #list of common fanins for non-trivial groups
    ct = []
    dt = [] #will become group fanins
    cnt = []
    for j in Lg:
        gpj=gp[j] #list of signals in group j
        width = len(gpj)
        met1 = set([]) #signals that have been seen once.
        cnts = []
        for i in range(len(gpj)):
            fig=fi[gpj[i]]
            for k in fig:
                if k in met1:
                    met1.remove(k)
                else:
                    met1.add(k)             
            cnts = cnts + fig
        gmet1 = lim_met1(met1,Lg,gp)
        dt.append(gmet1) 
        cts = count_reps(cnts)
        cts = [cts[i][1] for i in range(len(cts))] #just keep frequency
        cnt.append(cts)
    return ct,dt,cnt #leave ct empty

def lim_met1(m1,L,gp):
    """ m1 is a list of signals that fanout to exactly 1 of gpj
        L is a list of groups of length > 7
        want to find groups > 7 that have all of its signals among m1
    """
    res = []
    for i in L:
        gpLi = gp[i] #list of signals in i th group
        allin = True
        for j in gpLi:
            if not j in m1:
                allin = False
                break
        if allin:
            res.append(i)
    return res
                

def count_reps(y):
    x=list(y)
    x.sort()
    last = -10000000
    x.append(-1000000)
    k = 0
    cts = []
    for i in range(len(x)):
        if x[i] == last:
            k = k+1
        else:
            cts.append([last,k])
            k=1
            last = x[i]
    return cts[1:]


#def group_inputs():
    """ want to gorup inputs into control and data. A data group has
    to fan out to nontrivial groups output groups where each bit
    (or pair or triple) goes
    to a different member of an output group. For each output group
    it fans out to, this has to old. We assume that all inputs have
    been classified into control or data. If an input looks like
    a control going to one group and data going to another, it
    should be classified as control or maybe just nothing. 
    """
    
def gp_fan(gp,fan,ALL):
    """ get the immediate (gp) fanins of the gp's in terms of gp's """
    global L2
    if len(gp) < 2:
        print "single node group  for entire graph"
        return [[]]
    gp_map = get_map(gp)
    print 'gp_map done'
    assert not -1 in gp_map, '-1 at location %d'%gp_map.index(-1)
    gpfan = []
    L2 = set([i for i in range(len(gp)) if len(gp[i]) > 1])
    for j in range(len(gp)): # jth scc
        fanj = get_gpfan(gp[j],fan,gp_map,ALL) #returns a set
        fanj = list(fanj)
        fanj.sort()
        gpfan.append(fanj)
    return gpfan


def get_gpfan(gpj,fan,gp_map,ALL=False):
    """ get set of immediate gp fans (in or out) of jth gp """
    fanj = set([])
##    print gpj
    if ALL:
        fanj = L2 #non-trivial groups
    for k in gpj:
        if not k in L2:
            return set([])
        fanjk = fan[k] # immediate fanins of kth element of jth gp
        fanjk.sort()
        mfanjk = [gp_map[n] for n in fanjk if n > -1]
        # mfanjk is immediate gp fanins of signal k excluding PIs
        # choose between at least one or all
        if ALL:
            fanj = fanj & set(mfanjk)
        else:
            fanj = fanj | set(mfanjk)
    return fanj

def group_pis(isos2,fi):
    L2 = [i for i in range(len(isos2)) if len(isos2[i]) > 7]
    res = []
    for i in L2:
        gp = isos2[i] #ith iso group
##        fi0 = fi[gp[0]] # fanin of first member of isos2[i]
##        pi0 = [fi0[k] for k in range(len(fi0)) if fi0[k] < 0] #keep only pis
        fig = [] #initialize
        for j in gp:
            fij = fi[j] # fanin of j th member of isos2[i]
            fij = [fij[k] for k in range(len(fij)) if fij[k] < 0]
            fig = fig + fij
##            print fig
            #want to keep only pis that fanout to all the gp
##        print fig
        res.append(list(fig))
    # now sort into unique disjoint groups.
    # If one intersects with another, replace by both interesection and
    # add differences
##    ffg = refine(res)
    return res

def refine(fig):
##    L = [set(fig[i]) for i in range(len(fig))]
    LL = [[len(fig[i]), fig[i]] for i in range(len(fig))]
    LL.sort()
    L = [set(LL[i][1]) for i in range(len(LL))]
    L = uniquify_sets(L)
    return L

def uniquify_sets(L):
    res = []
    last = []
    for i in range(len(L)):
##        print last,L[i],res
        if L[i] == last:
            continue
        else:
            res.append(L[i])
            last = L[i]
    return res

##    for 
##    res = []
##    while not L == []:
##        s = L.pop()
##        if L == []:
##            res.push(s)
##            return res
##        ss = L.pop()
##        if len(s&ss) == 0:
##            
        
            

            
def begin(part=0,ALL=False,ifisost=True):
    global fi,fo,all_seen
    global n_init_pis, n_init_latches,n_init_pos,lengths
    n_init_pos = n_pos()
    if n_latches() > 0:
        abc('scl')
        if n_ands() == 0:
            print 'nil circuit after scl'
            return ['nil']*13 #need to return 7 things
    n_init_pos = n_pos()
    n_init_latches = n_latches()
    reparam()
    n_init_pis = n_pis()
    abc('comb')
    abc('w %s_comb.aig'%f_name)
    ps()
    fi = fi_sig(n_init_pis,n_init_pos)
    fo = fo_sig(fi)
    isos1 = super_iso(part,ifisost)
    abc('w %s_comb_red.aig'%f_name)
    abc('r %s_comb.aig'%f_name)
    isos2, lengths = make_indep(isos1)
##    lengths = [l_supp(isos2[i][0]) for i in range(len(isos2))]
##    print_eq_counts(isos2)
    isfi=gp_fan(isos2,fi,ALL)
##    print 'done isfi'
    isfo=gp_fan(isos2,fo,ALL)
    c,d,cnt=get_ctrl_data(isos2,fi)
    f_c = count_freq(cnt)
    L2=[i for i in range(len(isos2)) if len(isos2[i]) > 7]
    fcc = [[len(isos2[L2[i]]),f_c[i]] for i in range(len(f_c))]
##    print 'fanin fanout for groups: \n',
    io=[['%d: len=%d '%(i,len(isos2[L2[i]])),[len(c[i]),len(d[i])]] for i in range(len(c))]
    return isos1,isos2,lengths,fi,fo,isfi,isfo,L2,c,d,cnt,fcc,io
##    scc = get_SCCs()
##    IG=group_iso_scc(isos2,scc)
##    sccm = merge_ind_gps(IG,scc)
##    sccmfi=scc_fi(sccm,fi)
##    sccmfo=scc_fi(sccm,fo)
##    fii=fi_scc(sccm,fi)
##    return scc,isos,fi,fo,fii,sccm,sccmfi,sccmfo

def count_freq(cnt):
    res = []
    for i in range(len(cnt)):
        cti=cnt[i]
        cti.sort()
        res.append(count_fq(cti))
    return res

def make_indep(isos):
    isc = []
    lens = []
    print '\nsplitting iso classes into independent sets'
    for j in range(len(isos)):
        isosj = isos[j]
        lnj = lengths[j]
        if len(isosj) == 1:
            isc.append(isosj)
            lens.append(lnj)
            continue
        isji = split_i(isosj)
        isc = isc + isji
        lens = lens + [lnj]*len(isji)
    print '\n'
    return isc,lens

def split_i(isj):
    """ split the iso class isj into independent sets"""
##    if len(isj)> 1:
##        print len(isj)
    isc = []
    #create list of fan outs in isj for each member of isj
    for i in isj:
        isi =[]
        for j in isj:
            if not j == i:
                if j in fo[i]:
                    isi.append(j) # these are those flops that i fans out to
        isc.append(isi)  #fan out lists of flops
##    print isc
    J = [] #first sub-group
    #put in 0th group all those that do not have any fanout to any in isj
    isc_J_list = set([]) # a list of sets
##    print isc_J_list
    for i in range(len(isc)):
        if isc[i] == []:
            J.append(isj[i])
            isc_J_list = isc_J_list | set(isc[i]) #fan out set of 0th sub-group
##            print isc_J_list
##    print isc_J_list
    if len(J) == len(isj):
        return [isj]
    isc_J_list = [isc_J_list]
    J_list =  [J] #independent sub-groups of flops
##    print J
##    print len(J)
    for i in range(len(isj)):
        if isj[i] in J:
            continue
        J1 = isc[i] #set of fanout flops of isj[i]
        new = True
##        print J_list
        for j in range(len(J_list)):
            J2 = J_list[j] #list of flops
            if  not disj(J1,J2) or isj[i] in isc_J_list[j]: #J1 has a fanout in J2 or v.v
                continue
            else:  #add isj[i] to jth sub-list
                J_list[j].append(isj[i])
                isc_J_list[j] = isc_J_list[j] | set(isc[i])
                new = False
                break
        if new: #add a new independent sub-group
            J_list.append([isj[i]])
            isc_J_list.append(set(isc[i]))
    if len(J_list)>1:
        print [len(J_list[i]) for i in range(len(J_list))],
##        print_eq_counts(J_list)
    return J_list
            
def disj(J1,J2):
    """ is set J1 in set J2"""
    j1 = set(J1)
    res = j1.isdisjoint(set(J2))
    return res
                
def group_iso_scc(iso,scc):
    """ combines iso and scc into word-level scc's
    if two sccs have the same list of isos then scc's are combined
    """
    global fi,fo,all_seen
    global n_init_pis, n_init_latches,n_init_pos
    global sccfi,fi,level
    N = len(scc)
    scm = get_map(scc)
    ism = get_map(iso)
    iso_lists = []
    for j in range(N):
        sccj = scc[j]
        isosj = [ism[i] for i in sccj] # the set of isos in sccj
        isosj.sort() # now look for scc with same set of isos
        iso_lists.append(isosj)
    iso_group = [-1]*N
    for j in range(N):
        if iso_group[j] == -1:
            iso_group[j]=j
            for i in [k for k in range(N) if k > j]:
                if iso_group[i] == -1:
                    if iso_lists[j] == iso_lists[i]:
                        iso_group[i]=j
    #now all sccs have been assigned to an iso_scc. We want to merge
    #all sccs with the same iso_group number.
    mm = list(set(iso_group))
    M = len(mm) # number of unique iso numbers
    print ' No. of unique iso groups numbers', M
    IG = [[] for i in range(M)]
    n = 0
    for i in range(N):
        ii = mm.index(iso_group[i]) #ii th iso_group
        IG[ii].append(i)
    return IG
##    return get_word_scc(IG,scc)

def xloop(x, lo=0):
    """ lo = 1 means return a loop, else just ondicate if a loop or not """
    Lx = len(x)
    ly = [0]*Lx
    tbd = set(range(Lx))
    lp = False
    while not len(tbd) == 0:
        i = tbd.pop()
        if x[i] == []:
            continue
        for j in x[i]:
            if ly[j] > ly[i]:
                continue
            ly[j] = ly[i]+1
            if not x[j] == []:
                tbd.add(j)
            if not ly[j] < Lx+10:
                lp = True
                break
    if lp == False or lo == 0:
        return lp
    else:
        #gather loop
        Lx = max(ly)
        lp = []
        while True:
            lpi = [k for k in range(len(ly)) if ly[k] == Lx]
            if len(lpi) == 0:
                break
            lp = lp + lpi
            Lx = Lx-1
    return lp



def indep(x,k,l):
    Lx = len(x)
    ly = [0]*Lx #start at layer 0
    tbd = set(k) #start at node k
    done = set([])
    while not len(tbd) == 0:
        i = tbd.pop()
        if i in done:
            continue
        done.add(i)
        if l in x[i]:
            return False
        for j in x[i]: #j in fanin of i
            if ly[j] <= ly[i]:
                ly[j] = ly[i]+1
                tbd.add(j)
                if not ly[j] < Lx:
                    return True
##        tbd.add(x[i])
    return True
    
    
def get_wl_scc(iso,scc):
    IG = group_iso_scc(iso,scc)
    ind_IG = split_ind_gps(IG,scc)
    wl_scc = merge_ind_gps(ind_IG,scc)
    return wl_scc
    

def split_ind_gps(IG,scc):
    global sccfi,fi,level
    """ splits up iso_groups into independent groups to be merged """
    fi = fi_sig(n_init_pis,n_init_pos)
    sccfi=scc_fi(scc,fi)
    if not xloop(sccfi):
        return IG
##    level=layer(sccfi)
    IGi=list(IG)
    IGi.reverse()
    ind_IG = []
    while len(IGi)>0:
        I = IGi.pop() #split into independent sets
        #(not in the fanin or fanout of each other)
        Igs = split_iso(I) #split groups into subgroups
        print [len(I),len(Igs)], #I is a single set of SCC's to be split
        #IGs is a set of sets
        print Igs
        for i in len(range(Iga)):
            ind_IG.append(Igs[i])
    return ind_IG
    
    

def merge_ind_gps(ind_IG,scc):
    wlscc = []
    for i in range(len(ind_IG)):
        II = ind_IG[i] #ith group
        l=[]
        for j in II: #merge all the (independent) groups together 
            l = l + scc[j]
        l.sort() # not necessary really. Also sccs are disjoint so no repeats.
        wlscc.append(l)
    return wlscc # returns a new set of scc's

def split_iso(I):
    """ I is a set of scc's given by number"""
    if len(I) == 1:
        return [I] #the whole group
    ind = [0]*len(I) #indicate if assigned yet
    sps = []
    while 0 in ind:
        j = ind.index(0) # next scc not assigned
        ind[j] = 1
        # j th scc in I
        lst=[I[j]]
        for i in [i for i in range(len(ind)) if i > j]:
            if ind[i] == 0:
                if not indep(I[i],I[j]):
                    continue
                else:
                    lst.append(I[i])
                    ind[i] = 1 #now seen and assigned
        sps.append(lst)
    return sps # a set of sets

def indep(s1,s2):
    """ returns True if  scc s1 not in tfi scc s2 or vice versa
    """
    global fi, sccfi, level
    # can't use level
    if level[s1] == level[s2]:                         
        return True
    if level[s1]<level[s2]: #swap
        s=s1
        s1=s2
        s2=s
    tbt=set([s1]) #initialize
    done = set([]) #sscc's already traced.
    while len(tbt)>0:
        i = tbt.pop()
        if i in done:
            continue
        done.add(i)
        sci = sccfi[i]
        if s2 in sci:
            return False
        tbt = tbt | set(sci)
    return True
        


#+++++++++++++++++ start iso +++++++++++++++++++++++++++++++

def merge_eqs(eql,eqh):
    """ eql is a set of old eq_classes and eqh is a set of newly found ones in terms of
    the old classes. we want to merge old classes to get a new smaller set of classses.
    As merge_eqs is the aig containing only the representatives shrinks because iso does this.
    """
    res = []
    for k in range(len(eqh)):
        resk = []
        lh = eqh[k]
        for i in range(len(lh)):
            resk = resk + eql[lh[i]]
##            print resk
        res = res + [resk]
##    print [len(res[i]) for i in range(len(res))]
    return res



def get_supp(cl=[]):
    """ gets the union of the supports of a single isomorphic class."""
    sup_cl = []
    npi = n_init_pis #pis are CIs which are PIs,FF
    npo = n_init_po
##    s0 = [0]*n_pis()
    for i in range(len(cl)):
##        s=list(s0)
        #i is a flop number = #po + #FF[i]
        supi = co_supp(cl[i])
##        for j in range(len(supi)):
##            s[supi[j]]=1
##        supi=[]
        spi = []
        for j in supi: #need to shift regs by +n_init_pos
            if j < npi:
                spi.append(j-npi) #shift so that primary inputs are negative.
            else:
                spi.append(j-npi+npo) #leave space for initial pos so reg input and output numbers are the same        sup_cl= sup_cl + supi
    return sup_cl

#_____________________________

def get_mapped_fos(eq):
    """ get the fanouts of each comb PO in terms of group numbers"""
    s2g = get_po_map(eq)
    fo2g = []
    for i in range(len(fo)):
        foi = fo[i]
        foi2g = [s2g[j] for j in foi]
        foi2g = list(set(foi2g))
        foi2g.sort()
        fo2g.append(foi2g)
    return fo2g


def get_po_map(eq):
    """ get the mapping from signal to group"""
    s2g = [-1]*(n_init_pos+n_init_latches)
    for i in range(len(eq)):
        eqi = eq[i]
        for j in eqi:
            s2g[j]=i
    return s2g

def fodj(cl,fo2g):
    """ partition eq iso class cl into disjoint fanout groups """
    dj_fo_gps = []
    J = []
    for i in cl:
##        print '\nnewi = %d'%i,
        foi = set(fo2g[i])
        Ji = set([i])
        if dj_fo_gps == []:
            dj_fo_gps.append(foi)
            J.append(Ji)
            continue
        j0 = -1
        for j in range(len(dj_fo_gps)):
##            print j,
            gj = dj_fo_gps[j]
            Jj = J[j]
            if not len(gj&foi) == 0: #not disjoint so merge
                if j0 == -1: #first time non-disjoint group found
                    j0 = j
                else: #more than 1 intersections
                    dj_fo_gps[j] = set([]) #get rid of jth set
                    J[j]=set([])
                foi = foi|gj # replace by union
                Ji = Ji | Jj
        if j0 == -1: # found new disjoint group
            dj_fo_gps.append(foi)
            J.append(Ji)
        else: #replace first group that intersected.
            dj_fo_gps[j0] = foi
            J[j0] = Ji #put i in j0 group
    res = []
    for i in range(len(J)): #eliminate null sets
        if not J[i] == set([]):
            res.append(list(J[i])) #convert from set to list
    return res

def part_eq(eq,fo2g):
    """ create new iso groups by partitioning each into disjoint fanout groups"""
    global lengths
    eq_new = []
    lths = []
    for i in range(len(eq)):
        split = fodj(eq[i],fo2g)
        for j in range(len(split)):
            eq_new.append(split[j])
            lths.append(lengths[i]) #support is unchanged
    lengths = lths
##    pr_sort(lengths)
    return eq_new

def pr_sort(L):
    ll=list(set(L))
    ll.sort()
    print ll

def part_eq_iter(eq):
    """ iteration the partitioning because fanout groups change."""
    global n_init_pis, n_init_latches,n_init_pos,lengths
##    ps()
##    abc('r %s_red.aig'%f_name)
##    n_init_pis = n_pis()
##    n_init_pos = n_pos()
##    n_init_latches = n_latches()
##    abc('r %s_comb_red.aig'%f_name)
##    ps()
    eq_new = list(eq)
    lengths = [l_supp(eq[i][0]) for i in range(len(eq))]
##    pr_sort(lengths)
    wt_old = print_eq_counts(eq,1)
##    fos = fo_sig()
    while True:
        fo2g = get_mapped_fos(eq_new)
        eq_new = part_eq(eq_new,fo2g)
        wt = print_eq_counts(eq_new,0)
        if wt == wt_old:
            break
        wt_old = wt
    wt = print_eq_counts(eq_new,1)
    return eq_new

def print_eq_counts(eq,p=1):
    """ prints out the lengths of eq and their frequency"""
    global lengths
    L=[[len(eq[i]),lengths[i]] for i in range(len(eq))]
    L.sort()
    wt = print_counts(L,p)
    return wt

def print_counts(L,p=1):
    n_old = L[0][0]
    R=[]
    s = 0
    wt = 0
    sups= []
    for i in range(len(L)):
        n = L[i][0]
        if n == n_old:
            s = s+1 # count number of iso groups of same width
            sups.append(L[i][1])
        else:
            sups = list(set(sups))
            sups.sort()
            wt = wt + s*(n_old -1)
            R.append('[%d]*%d(%s)'%(n_old,s,prpr(sups)))
            n_old = n
            s=1
            sups = [L[i][1]]
    wt = wt + s*(n_old -1)
    sups = list(set(sups))
    sups.sort()
    R.append('[%d]*%d(%s)'%(n_old,s,prpr(sups)))
    if p:
        print '\n',R
        print 'iso weight, efficiency = %d, %.2f '%(wt,float(wt)/float(n_init_pos+n_init_latches))
    else:
        print wt,
    return wt

#__________________________________
        


def get_class_supp(eq=[]):
    """ eq is a set of isomorphic classes. Computes the support of each iso class.
    Repeated supports indicate that common signals appear in the supports of a
    class. input numbering is PIs first, then flops.
    """
    abc('w %s_comb_red.aig'%f_name) #this needs the original aig
    abc('r %s_comb.aig'%f_name)
    sg = []
    for i in range(len(eq)):
        eis = get_supp(eq[i]) #get the support of the ith iso class. This includes
            #PIs which have negative numbers
        if eis == None or eis == []:
            print 'WARNING: eq_group %d has no support'%i
        sg.append(eis)
##    abc('w %s_comb.aig'%f_name)
    abc('r %s_comb_red.aig'%f_name)
    return sg



def check_fifo(fi,fo):
    for i in range(len(fi)):
        fii = fi[i]
        for j in fii: # j->i and j not a PI
            if j > -1:
                assert i in fo[j], 'fanin discrepancy (%d,%d)'%(j,i) #j is a fanin of i
            # j->i
    for i in range(len(fo)):
        foi = fo[i]
        for j in foi: #i->j
            assert i in fi[j], 'fanout discrepancy (%d,%d)'%(i,j) #j is a fanin of i
            #i->j
    return 'OK'

""" remember to have Alan create a command that makes each flop input a
PO. We want to try to prove some flop inputs are equal. need to miter pairs
together and try to properties them as properties. Use iso, scorr? Or given
a pair of flop inputs, a command makes a miter of them. Then we try to prove
them equivalent by superprove.

"""            

def get_iso_classes(n=0):
    global n_init_pis, n_init_latches,n_init_pos,lengths,orig_supp
    orig_supp = [l_supp(i) for i in range(n_pos())]
    if n == 0:
        if not iso():
            return 'nil'
    else:
        if not isost():
            return 'nil'
    eq = eq_classes()
    print 'number of POs: ',
    print len(orig_supp),n_pos()
##    print n_pos()
    abc('&get;&isonpn;&put')
##    ps()
    eq = merge_eqs(eq,eq_classes())
    print 'number of POs after isonpn: ',
    print n_pos()
    while True:
##        dc2_iter()
##        abc('dc2')
        abc('&get;&syn2;&put')
##        abc('fraig')
        if n == 0:
            if iso():
                eq = merge_eqs(eq,eq_classes())
                continue
        else:
            if isost():
                eq = merge_eqs(eq,eq_classes())
                continue
        print 'fraiging'
        abc('&get;&fraig;&syn2;&put')
        if n == 0:
            if not iso():
                break
        else:
            if not isost():
                break
        eq = merge_eqs(eq,eq_classes())
##    lengths = [orig_supp[eq[i][0]] for i in range(len(eq))]
    print 'number of POs after syn2 fraig iteration: ',
    print n_pos()
##    wt=print_eq_counts(eq,1)
    abc('&get;&isonpn;&put')
    eq = merge_eqs(eq,eq_classes())
    print 'number of POs after isonpn: ',
    print n_pos()
    lengths = [orig_supp[eq[i][0]] for i in range(len(eq))]
    print '[iso class width]*frequency(min support,max support): ',
    wt=print_eq_counts(eq,0)
    return eq

def l_supp(j):
    cs = co_supp(j)
    res = 0
    if not cs == None:
        res = len(cs)
    return res

            
def super_iso(part=0,ifisost=True):
    global n_init_pis, n_init_latches,n_init_pos,lengths,orig_supp
##    abc('w %s_initial_iso.aig'%f_name)
    print 'initial n_pos: ',n_pos()
    eq = get_iso_classes(ifisost)
    if  eq == 'nil':
##        print eq
        return 'nil'
##    print 'n_pos after get_iso_classes: ',n_pos()
    lengths = [orig_supp[eq[i][0]] for i in range(len(eq))]
##    pr_sort(lengths)
##    if part:
##        eq = part_eq_iter(eq)
    return eq

def count_fq(zz):
    """ x is a sorted list with repeats. returns a list of [count,value]
    where count is the number of times value is repeated in the list"""
    res = []
    s = 0
    z = list(zz)
    z.append(-100000)
    for i in range(len(z)-1):
        if not z[i] == z[i+1]:
            v = [s+1,z[i]]
            res.append(v)
            s = 0
        else:
            s=s+1
    return res

#____________end iso ____________________

def factor_nsf():
    abc('short_name')
    dc2_iter()
    abc('comb')
    while True:
        dc2_iter()
        if not iso():
            break
    ps()
    abc('&get')
    for k in range(n_pos()): 
        run_command('&put;cone -O %d;dc2'%k)
        if n_ands() > 15:
##            print n_ands()
            continue
        print '\n\n%d.  '%k ,
        run_command('clp;sop;pf')
        

## Begin synthesis functions
        
def speed2_tradeoff(k=6,dec=1):
    print nl(),
    abc('write_blif %s_best_speed.blif'%f_name)
    L_best = n_levels()
    A_best = n_nodes()
    abc('st;&get')
    while True:
        run_command('&syn2;&st; &if -K 6 -C 16 -g;&synch2;&st;&if -K 6 -C 16;&mfs;&put')
##        abc('speedup;if -D %d -F 2 -K %d -C 11'%(L,k))
        if n_levels() < L_best:
            L_best = n_levels()
            A_best = n_nodes()
            run_command('write_blif %s_best_speed.blif'%f_name)
            print nl(),
        elif n_levels() == L_best:
            if n_nodes() < A_best:
                run_command('write_blif %s_best_speed.blif'%f_name)
            print nl()
            break
        else: # levels went up
            print '\nNumber of levels went up: ',
            print nl()
            break
        continue
    abc('r %s_best_speed.blif'%f_name)
    print nl()

def speed_tradeoff(k=6,dec=1):
    print nl(),
    best = n_levels()
    abc('write_blif %s_bestsp.blif'%f_name)
    L_init = n_levels()
    while True:
        L_old = n_levels()
        L = L_old -dec
        abc('speedup;if -D %d -F 2 -K %d -C 11'%(L,k))
        if n_levels() < best:
            best = n_levels()
            abc('write_blif %s_bestsp.blif'%f_name)
        if n_levels() == L_old:
            break
        print nl(),
        continue
    abc('r %s_bestsp.blif'%f_name)
    print nl()
    return

def area_tradeoff(k=4):
    """ try to get better area by relaxing delay"""
    print nl(),
    best = n_nodes()
    abc('write_blif %s_bestsp.blif'%f_name)
    L_init = n_levels()
    while True:
        L_old = n_levels()
        L = L_old +1
        n_nodes_old = n_nodes()
        abc('/psspeedup;if -a -D %d -F 2 -K %d -C 11'%(L,k))
        if n_nodes() < best:
            best = n_nodes()
            abc('write_blif %s_bestsp.blif'%f_name)
        if n_levels() >= L_old:
            if n_nodes >= n_nodes_old:
                print nl()
                break
        print nl(),
        continue
    abc('r %s_bestar.blif'%f_name)
    return

def area_tradeoff2(k=6):
    """ try to get better area by relaxing delay"""
    print nl(),
    best = n_nodes()
    abc('write_blif %s_bestar.blif'%f_name)
    L_init = n_levels()
    while True:
        L_old = n_levels()
        L = L_old +2
##        n_nodes_old = n_nodes()
        abc('&get;&st;&synch2;&st; &if -f -D %d -F 1 -K %d -C 11;&put'%(L,k))
        print nl()
        if n_nodes() < best:
            best = n_nodes()
            abc('write_blif %s_bestar.blif'%f_name)
##        if n_levels() >= L_old:
        else:
            abc('read_blif %s_bestar.blif'%f_name)
            break
##        print nl(),
        continue
    abc('r %s_bestar.blif'%f_name)
    print nl()
    return

##def map_lut_dch_x(k=6,synch=1):
##    '''minimizes area '''
####    satlut(k)
##    best = n_nodes()
##    run_command('write_blif %s_best.blif'%f_name)
##    if synch:
##        abc('mfs2 -a  ;ps; lutpack ;ps')
####        abc('st; &get;&synch2;&lf -am -K %d -F 2 -C 11;&put;mfs2 -a  ;ps; lutpack ;ps'%k)
##    else:
##        abc('st; dch;ps; if -a  -F 2 -K %d -C 11;ps; mfs2 -a  ;ps; lutpack ;ps'%k)
##    if best <= n_nodes():
##        run_command('read_blif %s_best.blif'%f_name)


def map_lut_dch(k=6,synch=1):
    '''minimizes area '''
##    satlut(k)
    best = n_nodes()
    run_command('write_blif %s_best.blif'%f_name)
    if synch:
        abc('&get;&st;&synch2;&st;&if -a -K %d -F 2 -C 11'%k)
        print n_nodes(),
##        abc('&satlut')
##        print 'satlut: %d'%n_nodes(),
        abc('&put;mfs2 -a;lutpack')
        print n_nodes(),
##old        abc('st; &get;&synch2;&if -a -K %d -F 2 -C 11;&put;mfs2 -a  ;ps; lutpack ;ps'%k)
##        abc('st; &get;&synch2;&lf -am -K %d -F 2 -C 11;&put;mfs2 -a  ;ps; lutpack ;ps'%k)
    else:
        abc('st; dch;ps; if -a  -F 2 -K %d -C 11;ps; mfs2 -a  ;ps; lutpack ;ps'%k)
    if best <= n_nodes():
        run_command('read_blif %s_best.blif'%f_name)

def if_a_iter_old(k=6):
    best = n_nodes()
    run_command('write_blif %s_best.blif'%f_name)
    n=0
    while True:
        abc('if -a -K %d'%k)
##        abc('lf -am -K %d'%k)
        if n_nodes()< best:
            assert check_blif(),'inequivalence'
            best = n_nodes()
            n = 0
            abc('write_blif %s_best.blif'%f_name)
            assert check_blif(),'inequivalence'
            print nl(),
            continue
        else:
            n = n+1
            if n>2:
                break    
    abc('r %s_best.blif'%f_name)

def if_a_iter(k=6):
    best = n_nodes()
    run_command('write_blif %s_best.blif'%f_name)
    n=0
    while True:
        abc('&get;&st;&if -a -K %d;&satlut&put'%k)
##        abc('lf -am -K %d'%k)
        if n_nodes()< best:
            assert check_blif(),'inequivalence'
            best = n_nodes()
            n = 0
            abc('write_blif %s_best.blif'%f_name)
            assert check_blif(),'inequivalence'
            print nl(),
            continue
        else:
            n = n+1
            if n>2:
                break    
    abc('r %s_best.blif'%f_name)

def if_synch_iter(k=6):
    best = n_nodes()
    run_command('write_blif %s_best.blif'%f_name)
    abc('&get;&st; &synch2 -K %d; &if -a -F 2 -K %d; &satlut; &put'%(k,k))
    n=0
    while True:
        abc('&get;&st; &synch2 -K %d; &if -a -F 2 -K %d ; &satlut; &put'%(k,k))
        if n_nodes()< best:
##            assert check_blif(),'inequivalence'
            best = n_nodes()
            n = 0
            abc('write_blif %s_best.blif'%f_name)
##            assert check_blif(),'inequivalence'
            print nl(),
            continue
        else:
            n = n+1
            if n>2:
                break    
    abc('r %s_best.blif'%f_name)
    
def map_lut_dch_iter(k=6,synch=1,alt=0,m=2):
    global pairs
##    print 'entering map_lut_dch_iter with k = %d'%k
    best = n_nodes()
    sy=synch
    if alt:
        sy = not synch
##    print best
##    print nl()
    run_command('write_blif %s_best.blif'%f_name)
    n=0
##    print nl()
    while True:
        if alt:
            sy = not sy
        map_lut_dch(k,sy)
        if n_nodes()< best:
            best = n_nodes()
            print '%d '%best,
##            print 'best=%d'%best
            n = 0
            abc('write_blif %s_best.blif'%f_name)
            print nl(),
            if checknl(nl()):
                print 'Repeat'
                break
            continue
        else:
##            sy = not sy
            n = n+1
            if n>m:
                break    
##    if_a_iter(k)
    abc('r %s_best.blif'%f_name)
##    if n_nodes() >= best:
##        abc('r %s_best.blif'%f_name)
##    else:
##        print nl()
        
    

def checknl(np):
    global pairs
    if np in pairs:
        return True
    else:
        pairs = pairs + [np]
        return False

def map_lut_synch(k=6):
    '''minimizes area '''
    abc('&get;&st; &synch2 -K %d; &ps; &st; &if -F 2 -K %d -C 11 -E .1;&put;ps; mfs2 -a  ;ps; lutpack ;ps'%(k,k))
    
def map_lut_synch_iter(k=6):
##    print 'entering map_lut_dch_iter with k = %d'%k
    best = n_nodes()
##    print best
##    print nl()
    run_command('write_blif %s_best.blif'%f_name)
    n=0
##    print nl()
    while True:
        map_lut_synch(k)
        if n_nodes()< best:
            best = n_nodes()
##            print 'best=%d'%best
            n = 0
            abc('write_blif %s_best.blif'%f_name)
            print nl(),
            continue
        else:
            n = n+1
            if n>2:
                break    
    abc('r %s_best.blif'%f_name)

def dmitri_iter(k=8):
    best = 100000
    n=0
    while True:
        dmitri(k)
        if n_nodes()< best:
            best = n_nodes()
##            print '\nbest=%d'%best
            n = 0
            abc('write_blif %s_best.blif'%f_name)
            continue
        else:
            n = n+1
        if n>2:
            break
    abc('r %s_best.blif'%f_name)
##    run_command('cec -n %s.aig'%f_name)
    print nl()

def shrink():
    tm = time.time()
    best = n_ands()
    while True:
        abc('&get;&st;&if -K 4 -F 1 -A 0 -a;&shrink;&put')
        print n_ands(),
        if n_ands()< .99*best:
            best = n_ands()
            continue
        break
    print 't = %.2f, '%(time.time()-tm),
    ps()

def shrink_lut():
    tm = time.time()
    abc('&get;&st;&if -K 4 -F 1 -A 0 -a;&put')
    best = n_nodes()
    print best,
    abc('&shrink')
    while True:
        abc('&st;&if -K 4 -F 1 -A 0 -a;&put')
        print n_nodes(),
        if n_nodes() < .99*best:
            best = n_nodes()
            abc('&shrink')
            continue
        break
    abc('&put')
    print 'time = %.2f, '%(time.time()-tm),
    ps()


def map_lut(k=6):
    '''minimizes edge count'''
    for i in range(2):
        abc('st; if -e -K %d; ps;  mfs2 -a ;ps; lutpack ; ps'%(k))
##        print nl(),

def extractax(o=''):
    abc('extract -%s'%o)

def nl():
    return [n_nodes(),n_levels()]

def syn4_iter(th=.999):
    """ try both &syn4 and dc2 and take the best"""
    abc('st')
    tm = time.time()
    abc('w %s_last.aig')
    na_last = n_ands()
    while True:
        win='dc2'
        abc('&get;&syn4;&put')
        abc('w %s_tsyn.aig')
        na_syn = n_ands()
        abc('r %s_last.aig')
        abc('&get;&dc2;&put')
        na_new = n_ands()
        if na_syn < na_new:
            na_new = na_syn
            abc('r %s_tsyn.aig')
            win = 'syn'
        abc('w %s_last.aig')
        print '[%d,%s]'%(na_new,win)
##        print nl(),
        if na_new > th*na_last:
            break
        na_last = na_new
    print 't = %.2f, '%(time.time()-tm),
    ps()


##def syn4dc2_iter(th=.999):
##    abc('st')
##    tm = time.time()
##    while True:
##        na=n_ands()
##        abc('w 
##        abc('&get;&syn4;&put')
##        print n_ands(),
####        print nl(),
##        if n_ands() > th*na:
##            break
##    print 't = %.2f, '%(time.time()-tm),
##    ps()

def dc2_iter(th=.999):
##    syn4_iter()
##    return
    abc('st')
    tm = time.time()
    abc('&get')
    while True:
        na=n_ands()
        abc('&dc2;&put')
        print n_ands(),
##        print nl(),
        if n_ands() > th*na:
            break
##    print 't = %.2f, '%(time.time()-tm),
    ps()
##    print n_ands()

def dc(n=3):
    if n == 3:
        abc('&get; &b; &jf -K 6; &b; &jf -K 4; &b; &put')
    else:
        abc('&get; &b; &jf -K 7; &fx; &b; &jf -K 5; &fx; &b; &put')
    ps()

def dc2():
    dc()
    abc('dc2')
    ps()

def drw_iter(th=.999):
    abc('st')
    tm = time.time()
    while True:
        na=n_ands()
        abc('drw')
        print n_ands(),
##        print nl(),
        if n_ands() > th*na:
            break
    print 't = %.2f, '%(time.time()-tm),
    ps()
##    print n_ands()

def adc2_iter(th=.999):
    abc('st;&get')
    while True:  
        na=n_ands()
        abc('&dc2;&put')
##        print n_ands(),
        if n_ands() > th*na:
            break
    print n_ands()
        
def try_extract():
##    abc('dc2;dc2')
    print 'Initial: ',
    ps()
    na = n_ands()
##    abc('w %s_savetemp.aig'%f_name)
    #no need to save initial aig since fork_best will return initial if best
    J = [32,33]
    mtds = sublist(methods,J)
    F = create_funcs(J,0)
    (m,result) = take_best(F,mtds) #FORK here
    if not m == -1:
        print 'Best extract is %s: '%mtds[m],
        ps()
##    if (n_ands() < na):
##        return
##    else:
##        abc('r %s_savetemp.aig'%f_name)

def speedup_iter(k=8):
    abc('st;if -K %d'%k)
    run_command('ps')
    abc('write_blif %s_bests.blif'%f_name)
    run_command('ps')
    best = n_levels()
    print 'n_levels before speedup = %d'%n_levels()
    n=0
    while True:
        nl()
        abc('speedup;if -K %d'%k)
        print nl()
        if n_levels() < best:
            best = n_levels()
            abc('write_blif %s_bests.blif'%f_name)
            n=0
        else:
            n = n+1
        if n>2:
            break
    abc('r %s_bests.blif'%f_name)
    print 'n_levels = %d'%n_levels()

def jog(n=16):
    """ applies to a mapped blif file"""
    print 'jogging'
    run_command('if -a -K %d'%(n/2))
    #ps()
    run_command('eliminate -V 5 -N %d'%n)
    #ps()
    run_command('sop;fxch')
##    ps()
##    run_command('st;if -K %d'%(n/2))
##    ps()
##    run_command('sop;fxch')
##    ps()
    print 'done jogging'
    ps()
    

##def perturb_f(k=4):
##    abc('st;dch;if -E .1 -R 1.2 -K %d'%(k))
####    snap()
##    abc('speedup;if -E .1 -R 1.2 -K %d -C 10'%(k))
####    jog(5*k)
####    snap()
####    abc('if -a -K %d -C 11 -F 2;mfs -a -L 50;lutpack -L 50'%k

def perturb(k=6):
##    ps()
##    run_command('&get;&st;&put;dch;if -g -K %d;if -K %d'%(k,k))
    run_command('&get;&st;&synch2;&if -g -K %d;&st;&if -K %d;&put'%(k,k))
    ps()
    snap()
    run_command('speedup;&get;&st;&if -K %d -C 10;&put'%(k))
##    ps()
    jog(5*k)
##    snap()
    ps()
    
##def preprocess_2(k=6,ifprep=1):
##    global bestk
##    if not ifprep:
##        return 1
##    n_initial = n_nodes()
##    n_clp_lut = n_clp = 1000000
##    abc('write_blif %s_temp_initial.blif'%f_name)
##    abc('w %s_temp_initial.aig'%f_name)
##    res = 1
##    bestk = save_bestk(bestk,k)
##    print 'plain: ',nl()
##    abc('st')
##    if n_pis()/n_pos() > 500 or n_ands() > 1000:
##        bestk = try_elim(k,bestk)
##        if n_nodes() < bestk:
##            bestk = save_bestk(n_nodes(),k)
##    else:
##        bestk = try_clp(k,bestk)
##        if n_nodes() < bestk:
##            bestk = save_bestk(n_nodes(),k)
##    bestk = unsave_bestk(k)

def preprocess(k=6,ifprep=1):
##    global bestk
    if not ifprep:
        return 1
    map_lut_dch(k)
    if_a_iter(k)
    bestk = save_bestk(100000,k)
    print 'initial: ',nl()
    abc('st')
##    t = 30 #sleep time
    funcs = create_funcs([18],30) #sleep
    funcs = funcs + [eval('(pyabc_split.defer(try_elim)(k,bestk))')]
    funcs = funcs + [eval('(pyabc_split.defer(try_clp)(k,bestk))')]
    funcs = funcs + [eval('(pyabc_split.defer(try_plain)(k,bestk))')]
    mtds = ['sleep','elim','clp','plain']
    print mtds
    abc('st')
    j=0
    for i,res in pyabc_split.abc_split_all(funcs):
        print i,res
        if i == 0:
            print 'sleep timeout'
            if j > 0: #timeout and at least 1 terminiated.
                break
        j=j+1
        if res < bestk:
            print '%s got: %d'%(mtds[i],res)
            run_command('if -a -K %d'%k)
            print nl()
            bestk = save_bestk(bestk,k)
        if j > 2:
            break
    bestk = unsave_bestk(k)

def try_plain(k=6,bk=10000):
    map_lut_dch(k)
    if_a_iter(k)
    print '\nplain: ', nl()
    nn = n_nodes()
##    if n_nodes() < bk:
##        bk = save_bestk(bk,k)
    run_command('st')
    return nn
    
def try_elim(k=6,bk=100000):
##    abc('st')
    elim_iter()
##    print nl()
    run_command('st;logic;eliminate -V 5;bdd')
##    abc('st;dc2')
##    abc('if -a -K %d'%k)
    map_lut_dch(k)
    print '\nelim: ', nl()
    nn = n_nodes()
##    if n_nodes() < bk:
##        bk = save_bestk(bk,k)
    run_command('st')
    return nn

def try_clp(k=6,bk=100000):
    t1 = time.time()
    run_command('clp')
    nn = n_nodes()
    run_command('muxes;st')
    if not nn == n_nodes(): #st worked
        abc('dc2')
        map_lut_dch(k)
        print '\nclp: ', nl()
        nn = n_nodes()
    run_command('st')
    print time.time() - t1
    return nn

##        bk = save_bestk(bk,k)
##        abc('r %s_temp_initial.blif'%f_name)
        

##    # clp_lutmin
##    if stworked:
##        abc('read_blif %s_temp_clp.blif'%f_name)
##        run_command('st;lutmin -K %d'%k)
##        abc('write_blif %s_temp_clp.blif'%f_name)
##        print '\nclp lutmin: ',nl()
##        n_clp_lut = n_nodes()
            
    unsave_bestk(k)
##    if n_plain <= min(n_clp,n_clp_lut):
##        abc('r %s_temp_plain.blif'%f_name)
##    elif n_clp < n_clp_lut:
##        abc('r %s_temp_clp.blif'%f_name)
##    else:
##        abc('r %s_temp_clp_lut.blif'%f_name)
##    assert check_blif(),'inequivalence'
    
    return res

def elim_iter():
    abc('st;logic;eliminate -V 1 -N 12')
    nbest = n_nodes()
    ni = n_pis()
    val = 2
    while True:
        abc('eliminate -V %d -N %d'%(val,ni/2))
        if n_nodes() < nbest:
            nbest = n_nodes()
            print nbest,
            val = val*2
        else:
            return
        

def preprocess_old(k=4):
    n_initial = n_nodes()
    abc('write_blif %s_temp_initial.blif'%f_name)
##    abc('st;dc2')
    abc('w %s_temp_initial.aig'%f_name)
    ni = n_pis() + n_latches()
    res = 1
    abc('st;if -a -K %d'%k) # to get plain direct map
    if n_nodes() > n_initial:
        abc('r %s_temp_initial.blif'%f_name)
        res = 1
    #plain
    n_plain = n_nodes()
##    print nl()
    abc('write_blif %s_temp_plain.blif'%f_name)
##    print 'wrote blif'
    #clp
    print nl()
    n_clp_lut = n_clp = 1000000
##    if n_nodes() < 250:
    if True:
##        run_command('st;clp -B 10000')
        run_command('st;clp')
        nn = n_nodes()
        run_command('st')
        if not nn == n_nodes(): #st did not work
            run_command('if -a -K %d'%k)
            print nl()
            abc('write_blif %s_temp_clp.blif'%f_name)
            n_clp = n_nodes()
    abc('r %s_temp_initial.blif'%f_name)
##    print 'read blif'
##    if n_nodes() < 250:
    if True:
##        run_command('st;clp -B 10000')
        run_commnd('st;clp')
        nn = n_nodes()
        run_command('st')
        if not nn == n_nodes(): #st did not work
            run_command('lutmin -K %d'%k)
##            print nl()
            abc('write_blif %s_temp_clp.blif'%f_name)
##            n_clp = n_nodes()
            print nl()
##    print nl()
    if n_plain <= min(n_clp,n_clp_lut):
        abc('r %s_temp_plain.blif'%f_name)
        res = 1
    elif n_clp < n_clp_lut:
        abc('r %s_temp_clp.blif'%f_name)
        res = 1
    else:
        abc('r %s_temp_clp_lut.blif'%f_name)
        res = 1
##    print nl()
    assert check_blif(),'inequivalence'
    return res

def snap_bestk(k):
    abc('write_blif %s_temp.blif'%f_name)
    unsave_bestk(k)
    snap()
    abc('read_blif %s_temp.blif'%f_name)

def cec_it():
    """ done because &r changes the names. Can't use -n because rfraig_store reorders pis and pos."""
    abc('write_blif %s_temp.blif'%f_name)
    abc('&r -s %s.aig;&put'%f_name)
    run_command('cec %s_temp.blif'%f_name)
    abc('r %s_temp.blif'%f_name)

def save_bestk(current_best,k):
##    if os.access('%s_best%d.blif'%(f_name,k),os.R_OK):
##        res = get_bestk_value(k)
##    else:
    """ saves the best, returns bestk and if not best, leaves blif unchanged""" 
    res = current_best
    if n_nodes() < res:
        res = n_nodes()
        abc('write_blif %s_best%d.blif'%(f_name,k))
        print '\n*** best%d for %s *** = %d\n'%(k,f_name,res)
        assert check_blif(),'inequivalence'
    return res
##    unsave_bestk(k)

def unsave_bestk(k):
    run_command('read_blif %s_best%d.blif'%(f_name,k))
    return n_nodes()

def snap():
##    abc('fraig;fraig_store')
    run_command('&get;&st;&put;fraig_store')

def fxch_store(k=6):
    run_command('fraig_store;sop;fxch;eliminate;fraig_store;eliminate -V 5;fraig_store;fraig_restore;if -a -K %d'%k)
##    ps()
    run_command('&get;&if -a -K %d;&satlut;&put'%k)
##    ps()

def fx_iter(k=6):
    best = n_nodes()
    run_command('write_blif %s_best.blif'%f_name)
    n=0
    while True:
        fxch_store(k)
##        print 'done',
        print n_nodes()
##        abc('if -am -K %d'%k)
        if n_nodes()< best:
            assert check_blif(),'inequivalence'
            best = n_nodes()
            n = 0
            abc('write_blif %s_best.blif'%f_name)
            assert check_blif(),'inequivalence'
            continue
        else:
            n = n+1
            if n>2:
                break    
    abc('r %s_best.blif'%f_name)

        
def unsnap(k=6):
##    snap()
##    abc('fraig_restore')
##    map_lut_dch(k)
##    assert check_blif(),'inequivalence-1'
    print 'starting fraig_restore'
    run_command('fraig_restore')
##    run_command('ps')
    abc('if -a -F 2 -C 11 -K %d'%k)
    check_blif()
##    run_command('ps')
##    assert check_blif(),'inequivalence-1'
##    print nl()
    abc('mfs2 -a ')
    print nl()
##    assert check_blif(),'inequivalence-2'
    abc('lutpack ')
    print nl()

def map_until_conv(k=6,prep=1):
    global pairs
##    pairs = []
    kk = 2*k
##    kk = k + 1
    # make sure that no residual results are left over.
    if True:
        if os.access('%s_best%d.blif'%(f_name,k),os.R_OK):
            os.remove('%s_best%d.blif'%(f_name,k))
        if os.access('%s_best%d.blif'%(f_name,kk),os.R_OK):
            os.remove('%s_best%d.blif'%(f_name,kk))
        pairs = []
    tt = time.time()
    if not prep:
        map_lut_dch(k)
##        ps()
        if_a_iter(k)
##        ps()
    ##    map_lut_synch(k)
        bestk = save_bestk(100000,k)
        print 'first map_lut_dch yields: ',
        print nl()
    else:
        print 'preprocess entered'
        res = preprocess(k=k,ifprep = prep) #get best of initial, clp, and lutmin versions
        print nl()
        print 'preprocess done'
        bestk = save_bestk(100000,k)
    print 'starting mapping iteration with %d-LUTs'%k
##    map_lut_dch_iter(k,1,0,1) #initialize with mapping with kk input LUTs
##    map_lut_synch_iter(kk) PUT IN QUICKER TERMINATTOR
    if_synch_iter(k)
    bestk = save_bestk(bestk,k)
    print nl(), k, kk
    abc('r %s_bestk%d.blif'%(f_name,k))
    print 'iterating map'
    map_iter(k) #1
    bestk = save_bestk(bestk,k)
    bestkk = 1000000
    while True:
        print '\nPerturbing with %d-Lut'%kk
##        map_lut_dch_iter(kk,1,0,1)
##        if_synch_iter(k)
        map_lut_synch_iter(kk)
        bestkk_old = bestkk
        bestkk = save_bestk(bestkk,kk)
        if bestkk >= bestkk_old:
            break
        snap() #puts bestkk in fraig store
        unsave_bestk(k)
        snap()
        unsnap(k) #fraig restore and maps into k-luts
        bestk_old = bestk
        map_iter(k)
        bestk = save_bestk(bestk,k)
        if bestk >= bestk_old:
            break
        continue
    abc('fraig_restore') #dump what is left in fraig_store
    unsave_bestk(k)
##    if_a_iter(k)
    if_synch_iter(k)
##    run_command('&get;&satlut;&put')
##    satlut(k)
    bestk = save_bestk(bestk,k)
    unsave_bestk(k)
    print '\nFinal size = ',
    print nl()
    print 'time for %s = %.02f'%(f_name,(time.time()-tt))
##    cec_it()

def get_bestk_value(k=6):
    abc('write_blif %s_temp.blif'%f_name)
    unsave_bestk(k)
    res = n_nodes()
    abc('read_blif %s_temp.blif'%f_name)
    return res

def map_iter(k=6):
    tt = time.time()
##    bestk = get_bestk_value(k)
    n=0
    bestk = unsave_bestk(k)
##    bestk = n_nodes()
    while True:
        print 'perturbing'
        abc('if -a -K %d'%(k+2))
        snap()
        perturb(k) #
        snap()
        perturb(k)
        snap()
        old_bestk = bestk
        unsnap(k)
        abc('if -a -K %d'%k)
##        map_lut(k)
        bestk = save_bestk(bestk,k)
##        print 'iterating map_lut_dch'
##        if_a_iter(k)
##        if_synch_iter(k)
##        print '#nodes after if_synch_iter = %d'%n_nodes()
####        print '#nodes after if_a_iter = %d'%n_nodes()
####        if n_nodes() > 1.2*bestk: rkb-temp
        if n_nodes() > 2*bestk:
            print 'perturbation too big'
            break 
        map_lut_dch_iter(k)
        if n_nodes() > 1.5*bestk:
            print 'not enough progress'
            break
        bestk = save_bestk(bestk,k)
##        print bestk
        if bestk < old_bestk:
            n=0 # keep it up
            continue
        elif n == 2: #perturb 
            break
        else:
            print 'trying fx_iter'
            fx_iter(k)
            if n_nodes() > 1.5*bestk:
                print 'not enough progress'
                break
            bestk = save_bestk(bestk,k)
##        print bestk
            if bestk < old_bestk:
                n=0 # keep it up
                continue
            n = n+1
            print '%d-perturb'%n
    unsave_bestk(k)

def check_star(name='adder'):
    run_command('read_blif %s_best_star.blif'%name)
    run_command('st;&get')
    run_command('&cec %s.aig'%(name))

def check_blif():
    return True #disabling
##    print 'Checking: ',
    abc('write_blif %s_bb.blif'%f_name)
    abc('read_blif %s_best_star.blif'%f_name)
    abc('st;&get')
    run_command('&cec -n %s.aig'%f_name)
##    run_command('cec %s_bb.blif %s.aig'%(f_name,f_name))
    res = True
    if is_sat():
        res = False
        print '*** NOT OK ***'
##    else:
##        print'OK',
    abc('read_blif %s_bb.blif'%f_name)
    return res

def satlut(k=6):
    if k <= 6:
        run_command('&get;&st;&if -a -K %d;&satlut;&put'%k)
    else:
        run_command('&get;&st;&if -a -K %d;&put'%k)
##    ps()

def map_star(k=6):
    global pairs
    pairs = []
    tt = time.time()
    print '\n**************Starting first map_until_conv**: \n'
    map_until_conv(k,1) #1 means do preprocess
    abc('write_blif %s_best_star.blif'%f_name)
    assert check_blif(),'inequivalence'
    best = n_nodes()
    while True:
        jog(2*k)
        print '\n*************Starting next map_until_conv**: \n'
        map_until_conv(k,0)
        if n_nodes() >= best:
            break
        else:
            best = n_nodes()
            abc('write_blif %s_best_star.blif'%f_name)
            assert check_blif(),'inequivalence'
    abc('r %s_best_star.blif'%f_name)
    print '\n\n*** SIZE = %d, TIME = %.2f for %s ***'%(n_nodes(),(time.time() - tt),f_name)

def decomp_444():
    abc('st; dch; if -K 10 -S 444')
    abc('write_blif -S 444 %s_temp.blif; r %s_temp.blif'%(f_name,f_name)) 

def dmitri(k=8):
##    abc('w t.aig')
##    dc2_iter()
##    print 'first iter done:  %d'%n_ands()
##    abc('dc2rs')
####    dc2_iter()
##    print 'second iter done:  %d'%n_ands()
##    sop_balance(k)
##    abc('w t_before.aig')
##    run_command('cec -n t.aig')
##    speedup_iter(k)
##    print 'n_levels after speedup = %d'%n_levels()
##    abc('write_blif %s_save.blif'%f_name)
##    nn=n_levels()
    abc('st;dch; if -g -K %d'%(k))
##    print 'n_levels after sop balance = %d'%n_levels()
##    if n_levels() > nn:
##        run_command('r %s_save.blif'%f_name)
##        print 'n_levels = %d'%n_levels()
##    print 'final n_levels = %d'%n_levels()
##    print 'sop_balance done:  ',
##    print nl()
##    run_command('st;w t_after.aig')
##    run_command('cec -n t.aig')
    abc('if -G %d '%k)
##    print 'after if -G %d:  '%k,
##    print nl()
##    run_command('cec -n t.aig')
    abc('cubes')
##    print 'after cubes:  ',
##    print nl()
##    run_command('cec -n t.aig')
    abc('addbuffs -v')
##    print 'after addbuffs:  ',
    print nl(),
##    run_command('cec -n t.aig')

def lut():
    dc2_iter()
    abc('extract -a')
    print nl()
    dc2_iter()
##    ps()
    sop_balance(6)
    map_lut_dch()
    map_lut()
    print nl()
##    run_command('ps')

################################## gate level abstraction
    """
    Code for using
    for abstraction
    """

def bip_abs(t=100):
    """ t is ignored here"""
    set_globals()
    time = max(1,.1*G_T)
    abc('&get;,bmc -vt=%f'%time)
    set_max_bmc(get_bmc_depth(False))
    c = 2*G_C
    f = max(2*max_bmc,20)
    b = min(max(10,max_bmc),200)
    t1 = x_factor*max(1,2*G_T)
    t = max(t1,t)
    s = min(max(3,c/30000),10) # stability between 3 and 10 
##    cmd = '&get;,abs -bob=%d -stable=%d -timeout=%d -vt=%d -depth=%d -dwr=vabs'%(b,s,t,t,f)
    cmd = '&get;,abs -timeout=%d -vt=%d -dwr=%s_vabs'%(t,t,f_name)
    print 'Running %s'%cmd
##    abc(cmd)
    run_command(cmd)
##    get_bmc_depth()
    abc('&w %s_greg.aig'%f_name)
    return max_bmc

def check_frames():
    abc('read_status vta.status')
    return n_bmc_frames()

def vta_abs(t):
    """ Do gate-level abstraction for F frames """
    r = 100 *(1 - abs_ratio)
##    abc('orpos; &get;&vta -dv -A %s_vabs.aig -P 2 -T %d -R %d; &vta_gla;&w %s_gla.aig;&gla_derive; &put; w %s_gabs.aig'%(f_name,t,r,f_name,f_name))
    abc('orpos; &get;&vta -dv -A %s_vabs.aig -P 2 -T %d -R %d; &vta_gla;&w %s_gla.aig'%(f_name,t,r,f_name))
    
##    write_file('abs')
    

def sizeof():
    return [n_pis(),n_pos(),n_latches(),n_ands()]

def abstract(ifb=2):
    global abs_ratio, abs_time
##    print 'ifb = %d'%ifb
    if ifb == 0: #new way using vta_abs and no bip
        add_trace('abstracta')
        return abstracta(False)
    elif ifb == 1: #old way using ,abs
        assert ifb == ifbip, 'call to abstract has ifb not = global ifbip'
        add_trace('abstractb')
        return abstractb()
    else:
        #new way using ,abs -dwr -- (bip_abs)
        add_trace('abstracta')
        return abstracta(True)

def abstracta(if_bip=True):
    """
    if_bip = 0 it uses a new abstraction based on &vta (gate level abstraction) and no bip operations
    Right now, if we do not prove it with abstraction in the time allowed,
    we abandon abstraction and go on with speculation
    if_bip = 1, we use ,abs -dwr
    """
    global G_C, G_T, latches_before_abs, x_factor, last_verify_time, x, win_list, j_last, sims
    global latches_before_abs, ands_before_abs, pis_before_abs, abs_ratio, abs_time
##    n_vabs = 0
    latches_before_abs = n_latches()
    ands_before_abs = n_ands()
    pis_before_abs = n_real_inputs()
    tt = time.time()
    print 'using abstracta, ',
##    print 'if_bip = %d'%if_bip
##    latch_ratio = abs_ratio
##    t = 100
    t = 1000 #temporary
    t = abs_time
    if if_bip == 0:
        t = 1000 #timeout on vta
        t = abs_time
    tt = time.time()
##    if n_pos() > 1 and if_bip == 0:
##        abc('orpos')
##        print 'POs ORed together, ',
    initial_size = sizeof()
    abc('w %s_before_abs.aig'%f_name)
    # 25 below means that it will quit if #FF+#ANDS > 75% of original
##    funcs = [eval("(pyabc_split.defer(abc)('orpos;&get;&vta -d -R 25'))")] #right now we need orpos
    if if_bip:
        print 'using bip_abs'
        mtds = ['bip_abs']
        funcs = [eval('(pyabc_split.defer(bip_abs)(t))')]
    else:
        if gla:
            print 'using gla_abs_iter for %0.2f sec.'%(t-2)
            mtds = ['gla_abs_iter']
            add_trace('gla_abs')
            funcs = [eval('(pyabc_split.defer(gla_abs_iter)(t-2))')]
        else:
            print 'using vta_abs for %0.2f sec.'%(t-2)
            mtds = ['vta_abs']
            funcs = [eval('(pyabc_split.defer(vta_abs)(t-2))')]
    funcs = funcs + [eval('(pyabc_split.defer(monitor_and_prove)())')]
##    J = [34,30]
##    J = pdrs[:1]+bmcs[:1] #just use one pdr and one bmc here.
##    J = pdrs[:3]+[46,47,2] + [26] #rkb
    J = pdrs[:3]+[46,47,2] #rkb

##    J = pdrs+bmcs
##    J = modify_methods(J,2)
    funcs = funcs + create_funcs(J,1000)
    mtds = mtds + ['monitor_and_prove'] + sublist(methods,J)
    print 'methods in parallel with gla = ',str(mtds)
    print mtds
    vta_term_by_time=0
    for i,res in pyabc_split.abc_split_all(funcs):
        print 'initial result parallel mtds = ', str((i,res))
        if i == 0: #vta or gla ended first
            print 'time taken = %0.2f'%(time.time() - tt)
            if is_sat():
                print 'vta/gla abstraction found cex in frame %d'%cex_frame()
                add_trace('SAT by gla')
                return Sat
            if is_unsat():
                print 'vta/gla abstraction proved UNSAT'
                add_trace('UNSAT by gla')
                return Unsat
            else: #undecided
                if if_bip:
                    abc('&r -s %s_greg.aig; &abs_derive; &put; w %s_gabs.aig'%(f_name,f_name))
                else:
                    abc('&r -s %s_gla.aig;&gla_derive; &put; w %s_gabs.aig'%(f_name,f_name))   
                if time.time() - tt < .95*t:
                    print 'abstraction terminated'
                    vta_term_by_time = 0
                    break
                else:
                    print 'abstraction terminated by a timeout of %0.2f'%t
##                    print 'final abstraction: ',
##                    ps()
                    vta_term_by_time=1
                    break
        if i == 1: #monitor and prove ended first (sleep timed out)
            print 'monitor_and_prove: '
##            print i,res
            if res == None:
                print 'monitor and prove had an error'
                continue
            result = res[0]
            if res[0] > Undecided: #we abandon abstraction
                add_trace('de_abstract')
                print 'monitor and prove timed out or too little reduction'
                abc('r %s_before_abs.aig'%f_name)
                return Undecided_no_reduction
            if res[0] == Undecided:
                break
            else: 
                if not initial_size == sizeof(): #monitor and prove should not return SAT in this case'
                    assert not is_sat(), 'monitor_and_prove returned SAT on abstraction!' 
                print 'time taken = %0.2f'%(time.time() - tt)
                if is_unsat() or res[0] == 'UNSAT' or res[0] == Unsat:
                    add_trace('UNSAT by %s'%res[1])
                    return Unsat
                elif is_sat() or res[0] < Unsat:
                    add_trace('SAT by %s'%res[1])
                    return Sat
                else:
                    abc('r %s_before_abs.aig'%f_name)
                    return Undecided_no_reduction
        else: #one of the engines got an answer
            print 'time taken = %0.2f'%(time.time() - tt)
##            add_trace('initial %s'%mtds[i])
            if is_unsat():
                print 'Initial %s proved UNSAT'%mtds[i]
                add_trace('UNSAT by initial %s'%mtds[i])
                return Unsat
            if is_sat():
                bad_po = cex_po()
                print 'Initial %s proved SAT for output %d'%(mtds[i],cex_po())
                add_trace('SAT by initial %s'%mtds[i])
                return Sat
            else: # an engine failed here
                print 'Initial %s terminated without result'%mtds[i]
                add_trace('method %s failed'%mtds[i])
##                return Undecided
                continue
    read_abs_values()
    set_max_bmc(abs_depth-1,True)
    if  vta_term_by_time == 0 and if_bip == 0 and gabs: #vta timed out itself
        print 'Trying to verify final abstraction',
        ps()
        result = verify([7,9,19,23,24,30],100)
        if result[0] == Unsat:
            add_trace('UNSAT by %s'%result[1])
            print 'Abstraction proved valid'
            return result[0]
    # should do abstraction refinement here if if_bip==1
    if if_bip == 0 and gabs: # thus using vta or gla abstraction and no refinement
        print 'abstraction no good - restoring initial simplified AIG',
        abc('r %s_before_abs.aig'%f_name)
        add_trace('de_abstract')
        ps()
        return Undecided_no_reduction
    else: # thus using bip_abs (ifbip=1) or gate abstraction (ifbip=0&gabs=False) and refinement
        if is_sat():
            print 'Found true counterexample in frame %d'%cex_frame()
            add_trace('SAT')
            return Sat_true
        if is_unsat():
            add_trace('UNSAT')
            return Unsat
    ##    set_max_bmc(NBF)
        NBF = get_bmc_depth(True)
        print 'Abstraction good to %d frames'%max_bmc
        #note when things are done in parallel, the &aig is not restored!!!
        if if_bip:
            abc('&r -s %s_greg.aig; &w initial_greg.aig; &abs_derive; &put; w initial_gabs.aig; w %s_gabs.aig'%(f_name,f_name))
        else:
            run_command('&r -s %s_gla.aig; &w initial_gla.aig; &gla_derive; &put; w initial_gabs.aig; w %s_gabs.aig'%(f_name,f_name))
        set_max_bmc(NBF,True)
        print 'Initial abstraction: ',
        ps()
        abc('w %s_init_abs.aig'%f_name)
        latches_after = n_latches()
    ##    if latches_after >= .90*latches_before_abs: #the following should match similar statement
    ##    if ((rel_cost_t([pis_before_abs, latches_before_abs, ands_before_abs])> -.1) or
    ##        (latches_after >= .75*latches_before_abs)):
        if small_abs(abs_ratio):
            abc('r %s_before_abs.aig'%f_name)
            print "Too little reduction!"
            print 'Abstract time wasted = %0.2f'%(time.time()-tt)
            add_trace('de_abstract')
            return Undecided_no_reduction
        sims_old = sims
        sims=sims[:1] #make it so that rarity sim is not used since it can't find a cex
##        result = Undecided_no_reduction
        print 'small_abs = %.2f, vta_term_by_time = %d'%(small_abs(abs_ratio),vta_term_by_time)
        if not vta_term_by_time:
            print 'Entering abstraction_refinement'
            result = abstraction_refinement(latches_before_abs, NBF,abs_ratio)
            sims = sims_old
            if result <= Unsat:
                return result
        if small_abs(abs_ratio): #r is ratio of final to initial latches in absstraction. If greater then True
##        if small_abs(abs_ratio) or result == Undecided_no_reduction or vta_term_by_time: #r is ratio of final to initial latches in absstraction. If greater then True
            abc('r %s_before_abs.aig'%f_name) #restore original file before abstract.
            print "Too little reduction!  ",
            print 'Abstract time wasted = %0.2f'%(time.time()-tt)
            add_trace('de_abstract')
            return Undecided_no_reduction
        elif vta_term_by_time:
            abc('r %s_gabs.aig'%f_name)
            print 'Simplifying and testing abstraction'
            reparam()
            result = simplify()
            assert result >= Unsat, 'simplify returned SAT'
            if result > Unsat: #test if abstraction is unsat
                result = simple(check_trace=False)# does simplification first
                res = result[0]
                if res == 'UNSAT':
                    return Unsat
                else:
                    abc('r %s_before_abs.aig'%f_name) #restore original file before abstract.
                    print "Timed out with bad abstraction",
                    print 'Abstract time wasted = %0.2f'%(time.time()-tt)
                    add_trace('de_abstract')
                    return Undecided_no_reduction
##                if res == 'SAT':
####                    result = Sat #this was an error
##                    result = Undecided_no_reduction
##                elif res == 'UNSAT':
##                    result = Unsat
##                else:
##                    result = Undecided_no_reduction
##                return result
        else:
            write_file('abs') #this is only written if it was not solved and some change happened.
        print 'Abstract time = %0.2f'%(time.time()-tt)
    return result

def gla_abs_iter(t):
    """ this iterates &gla every x sec and checks if it should be stopped or continued.
        Uses the fact that when &gla ends
        it leaves the result in the &-space showing which elements are abstracted.
        cex_abs_depth, time_abs_prev and time_abs come from monitor_and_prove
        gla_abs_iter and monitor_and_prove are run in parallel
        """
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    it_interval = 10000 
    total = 10000 #do not want &gla to timeout by itself
    tt = time.time()
    run_command('orpos;&get')
    abs_depth = abs_depth_prev = 0
    r = 100*abs_ratio
    q = r #############TEMP
    time_remain = total - (time.time() - tt) #time remaining
    it = min(it_interval,time_remain)
    cmd = '&gla -m -B 1 -A %s_vabs.aig -T %d -R %d -Q %d -S %d -B 1'%(f_name,it,r,q,abs_depth)
    print 'Executing %s'%cmd
    name = '%s_vabs.aig'%f_name
    name_old = '%s_vabs_old.aig'%f_name
    run_command(cmd)
    if os.access(name,os.R_OK):
        print 'New abstraction written. Possibly grew too big'
        run_command('&r -s %s_vabs.aig'%f_name) #get the last abstraction result
        run_command('&w %s_gla.aig'%f_name) #saves the result of abstraction.
    elif os.access(name_old,os.R_OK):
        print 'Old abstraction written. New abstraction got too big'
        run_command('&r -s %s_vabs_old.aig'%f_name) #get the last abstraction result
        run_command('&w %s_gla.aig'%f_name) #saves the result of abstraction.
    else: #this should not happen
        print 'No vabs file found'
        return 
    print 'wrote %s_gla file'%f_name
    run_command('&gla_derive;&put')
    run_command('w %s_gabs.aig'%f_name)
    
def read_abs_values():
    """here we read in the abs values written by monitor and prove"""
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    if not os.access('%s_ab.txt'%f_name,os.R_OK):
        print '%s_ab.txt does not exist'%f_name
        return #file does not exist so do nochange values
##    print '%s_ab.txt file exists and is readable'%f_name
    ab = open('%s_ab.txt'%f_name,'r')
##    print '%s_ab.txt is opened'%f_name
    s = ab.readline()
##    print s
    cex_abs_depth = int(s)
    s = ab.readline()
##    print s
    time_abs_prev = float(s)
    s = ab.readline()
##    print s
    time_abs = float(s)
    s = ab.readline()
##    print s
    abs_depth_prev = int(s)
    s = ab.readline()
##    print s
    abs_depth = int(s)
    ab.close()
##    print 'read: ',
##    print cex_abs_depth,time_abs_prev,time_abs,abs_depth_prev,abs_depth
##    print 'it is closed'

def write_abs_values():
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    """here we write in the abs values written by monitor and prove"""
    print 'cex_depth=%d,abs_depth=%d,prev=%d,time_diff = %0.2f'%(cex_abs_depth,abs_depth,abs_depth_prev,(time_abs-time_abs_prev))
    ab = open('%s_ab.txt'%f_name,'w')
    ab.write(str(cex_abs_depth)+'\n')
    ab.write(str(time_abs_prev)+'\n')
    ab.write(str(time_abs)+'\n')
    ab.write(str(abs_depth_prev)+'\n')
    ab.write(str(abs_depth))
    ab.close()

def abs_done(time_remain):
    """ heuristic to see if we are not making any progress and should quit
        look at frame of last cex found (cex_abs_depth)  for current abstraction using a parallel engine
        look at depth of current abstraction (abs_depth) and last abstraction (abs_deptth_prev)
        look at time between new abstractions time_abs - time_abs_prev.
        compute approximate frames_per_sec
        if  frames_to_next_cex > frames_per_sec * time_remain
        then won't get there is the time allowed.
        We have to pass all the information along when we are doing things in parallel by writing a file
        with this info in it and reading it in later. This is because monitor_and prove
        runs in parallel and global variables are not passed around.
    """
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
##    print 'checking if abs has enough time to next cex'
    frames_to_next_cex = cex_abs_depth - abs_depth
    div = time_abs - time_abs_prev
    div = max(.1,div)
    frames_per_sec = (abs_depth - abs_depth_prev)/div
    if frames_per_sec <= 0:
        return False #something wrong 
##    print 'frames_per_sec = %0.2f, frames_to_next_cex = %d, time remaining = %0.2f'%(frames_per_sec, frames_to_next_cex, time_remain)
    if frames_to_next_cex > 0.2*(frames_per_sec * time_remain): #later frames will take longer so factor of 5 here
        print 'not enough abs time to next cex'
        return True
    return False

##def gla_abs(t): 
##    """ Do gate-level abstraction for F frames """
##    r = 100 *(1 - abs_ratio)
##    run_command('orpos; &get;&gla -dv -A %s_vabs.aig -T %d -R %d; &w %s_gla.aig'%(f_name,t,r,f_name))
    
        
def monitor_and_prove():
    """
    monitor and prove. Runs in parallel with abstraction method.
    It looks for a new vabs and if found, will try to verify it in parallel
    We want to write a file that has variables
    cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    which will be used by abs_done called by gla_abs_iter which is to replace gla_abs
    """
    global ifbip
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    #write the current aig as vabs.aig so it will be regularly verified at the begining.
    name = '%s_vabs.aig'%f_name
    if os.access('%s'%name,os.R_OK): #make it so that there is no initial abstraction
        os.remove('%s'%name)
    initial_size = sizeof()
    print 'initial size = ',ps()
    time_abs = time_abs_prev = time.time()
    cex_abs_depth = 0
    abs_depth = abs_depth_prev = 0
    write_abs_values()
    t = abs_time
    t=10000 # do not want side engines to time out
    tt = time.time()
    abs_bad = 1 # start out with abstraction bad because it does not exist
    #a return of Undecided means that abstraction might be good and calling routine will check this
    while True: #here we iterate looking for a new abstraction and trying to prove it
        time_done = 0
        funcs = [eval('(pyabc_split.defer(read_and_sleep)())')]
        #J = sims+intrps+pdrs+bmcs
        J = intrps+[0,7,34,43,45] # temp
        #J = modify_methods(J,1)
        funcs = funcs + create_funcs(J,t) 
        mtds = ['read_and_sleep'] + sublist(methods,J)
        print 'methods = %s'%mtds
        monitor_done = False
        for i,res in pyabc_split.abc_split_all(funcs):
            if i == 0: # read_and_sleep terminated
                if res == False: #found new abstraction
                    read_abs_values()
                    set_max_bmc(abs_depth-1,True)
                    time_abs_prev = time_abs
                    time_abs = time.time()
                    write_abs_values()
                    abs_bad = 0 #new abs starts out good.
                    if not initial_size == sizeof() and n_latches() > abs_ratio * initial_size[2]:
                        return [Undecided_no_reduction]+['read_and_sleep']
                    else:
                        break
                elif res == True: # read and sleep timed out
                    time_done = 1
                    print 'read_and_sleep timed out'
                    if abs_bad:
                        return [Undecided_no_reduction]+['read_and_sleep']
                    else: #abs is still good. Let other engines continue
                        monitor_done = True
                        continue
                else:
                    assert False, 'something wrong. read and sleep did not return right thing'
            if i > 0: #got result from one of the verify engines
                if res == None:
                    print 'Method %s failed'%mtds[i]
                    continue
                if is_unsat() or res == Unsat or res == 'UNSAT':
                    print '\nParallel %s proved UNSAT on current abstr\n'%mtds[i]
                    return [Unsat] + [mtds[i]]
                elif is_sat() or res < Unsat or res == 'SAT': #abstraction is not good yet.
##                    print 'method = %s'%mtds[i]
                    print 'side method %s found SAT in frame %d \n'%(mtds[i],cex_frame())
                    if monitor_done:
                        return [Undecided_no_reduction]+['read_and_sleep']
                    if not mtds[i] == 'RareSim': #the other engines give a better estimate of true cex depth
                        read_abs_values()
                        set_max_bmc(abs_depth-1,True)
                        cex_abs_depth = cex_frame()
                        write_abs_values()
####                    print '\nParallel %s found SAT on current abstr in frame %d\n'%(mtds[i],cex_frame())
##                    print 'n_vabs = %d'%n_vabs
                    if initial_size == sizeof():# the first time we were working on an aig before abstraction
                        print 'initial_size == abstraction_size'
                        return [Sat]+[mtds[i]]
##                    print 'current abstraction invalid'
                    abs_bad = 1 
                    break #this kills off other verification engines working on bad abstraction
                else: #one of the engines undecided for some reason - failed?
                    print '\nParallel %s terminated without result on current abstr\n'%mtds[i]
                    continue
        if abs_bad and not time_done: #here we wait until have a new vabs.
            time_remain = abs_time -(time.time() - tt)
            abc('r %s_abs.aig'%f_name) #read in the abstraction to destroy is_sat().
            if abs_done(time_remain):
                return [Undecided_no_reduction]+['timeout']
            res = read_and_sleep(5) #this will check every 5 sec, until abs_time sec has passed without new abs            
            if res == False: #found new vabs. Now continue if vabs small enough
##                print 'n_vabs = %d'%n_vabs
                if (not initial_size == sizeof()) and n_latches() > abs_ratio * initial_size[2]:
                    return [Undecided_no_reduction]+['no reduction']
                else:
                    continue
            elif res == True: #read_and_sleep timed out
##                print 'read_and_sleep timed out'
                return [Undecided_no_reduction]+['no reduction']
            else:
                break #this should not happen
        elif abs_bad and time_done:
            print 'current abstraction bad, time has run out'
            return [Undecided_no_reduction]+['no reduction']
        else: #abs good 
            continue #continue even if time_done
##            print 'current abstraction still good, time has not run out'
    return [len(funcs)]+['error']

def read_and_sleep(t=5):
    """
    keeps looking for a new vabs every 5 seconds. This is usually run
    in parallel with &vta -d or &gla_iter
    when new abstraction is found returns False, and
    returns True when time runs out.
    """
    global cex_abs_depth, abs_depth, abs_depth_prev, time_abs_prev, time_abs
    #t is not used at present
    tt = time.time()
    T = abs_time
    set_size()
    name = '%s_vabs.aig'%f_name
    name_old = '%s_vabs_old.aig'%f_name
    #sleep(5) #should remove this if &gla first writes a null map
    while True:
        if (time.time() - tt) > T: #too much time between abstractions
            print 'read_and_sleep timed out after %d sec. between abstractions'%T
            return True
        if os.access(name,os.R_OK):
            #possible race condition
            run_command('&r -s %s; &w %s_vabs_old.aig'%(name,f_name))
            #save new vabs in old
##            print '%s exists'%name
            if not os.access(name,os.R_OK): #if new not readable now then what was read in might not be OK.
                print '%s does not exist'%name
                continue
            os.remove(name) #remove the new one - it is in memory now
            run_command('read_status %s_vabs.status'%f_name)
            #name is the derived model (not the model with abstraction info
            if os.access(name_old,os.R_OK):
                run_command('&r -s %s_vabs_old.aig'%f_name)
                run_command('&w %s_gla.aig'%f_name)
                run_command('&gla_derive;&put') #abstraction derived  from vabs file
                run_command('w %s_gabs.aig'%f_name)
    ##            print '%s is removed'%name
                read_abs_values()
                set_max_bmc(abs_depth-1,True)
                time_abs_prev = time_abs
                time_abs = time.time()
    ##            print 'abs values has been read'
                run_command('read_status %s_vabs.status'%f_name) 
                abs_depth_prev = abs_depth
                abs_depth = n_bmc_frames()
                write_abs_values()
                time_remain = T - (time.time() - tt)
    ##            if not check_size():
                if True:
                    print '\nNew abstraction: ',
                    ps()
                    set_size()
                    abc('w %s_abs.aig'%f_name)
                    return False #new abstraction is found so return to read&sleep
                #if same size, keep going.
        print '.',
        sleep(5) #repeat in 5 sec.

        
######################## FINDING ADDER ############################


""" the following is for unraveling an adder whose PIs and POs have been permuted"""
def b2d(n):
    """ binary to decimal conversion"""
    num = 0
    nn = list(n)
    nn.reverse()
    for j in range(len(nn)):
        if nn[j]==0:
            continue
        num = num+2**j
    return num
def d2b(n,N):
    """ decimal to binary conversion"""
    b = [0]*N
    if n <= 0:
        return b
    while True:
        j = int(math.log(n,2))
        b[j] = 1
        n = n-2**j
##        print n,b
        if n <= 0:
            break
    b.reverse()
    return b
    

def add(x,y):
    """x and y are binary numbers. convert to decimal and add, and then convert the result back to binary"""
    n1 = b2d(x)
    n2 = b2d(y)
    s = n1+n2
    res = d2b(s,len(x)+1)
    return res

def sub(x,y):
    """ take the absolute value of the difference of x and y"""
    n1 = b2d(x)
    n2 = b2d(y)
    if n1>n2:
        s = n1-n2
    else:
        s = n2-n1
    res = d2b(s,len(x))
    return res

def mult(x,y):
    """multiply x by y"""
    n1 = b2d(x)
    n2 = b2d(y)
    a = n1 * n2
    res = d2b(a,2*len(x))
    return res

def shift(x,y):
    """shifts x left by number of places given by binary y"""
    n1 = b2d(x)
    n2 = b2d(y)
    a = n1 << n2
    res = d2b(a,2*len(x))
    return res


def addp(xyp):
    """ x and y are binary, pi is the permutation of the inputs
        and po is the permutation of the outputs """
    global pi,po
    assert len(xyp)== len(pi),'length of input /= length of input permutation'
    xyp = permute(xyp,pi)
    N = len(xyp)/2
    x = xyp[:N]
    y = xyp[N:]
    n1 = b2d(x)
    n2 = b2d(y)
    s = n1+n2
    res = d2b(s,len(x)+1)
    assert len(res) == len(po), 'length of result /= length output permutation'
    res = permute(res,po)
    return res

def inc(x):
    n=b2d(x)
    y = n+1
    z=d2b(y,len(x)+1)
    return z

def dec(x):
    if not 1 in x:
        return x
    n=b2d(x)
    y = n-1
    z=d2b(y,len(x)+1)
    return z

def incp(xy):
    """ xy is binary, pi is the permutation of the input
        and po is the permutation of the output """
    global pi,po
    xyp = permute(xy,pi[:len(xy)])
    n1 = b2d(xyp)
    n2 = 1
    s = n1+n2
    res = d2b(s,len(xy)+1)
    res = permute(res,po[:len(res)])
    return res

def permute(r,p):
    assert len(r) == len(p),'result and permutation length differ'
    res = [0]*len(r)
    for i in range(len(r)):
        res[i] = r[p[i]]
    return res

def loop(n):
    """ n is the length of the arguments"""
    all0=[0]*n
    all1=[1]*n
    print dec(all0)
    print dec(all1)
    print '\n'
    rng = range(n)
    rng.reverse()
    for i in rng:
        t0=list(all0)
        t0[i]=1
        t1=list(all1)
        t1[i]=0
        print t0
##        r0=add(t0,all0)
        r0=dec(t0)
        print r0, num1(r0)
        print t1
##        r1=add(t1,all1)
        r1=dec(t1)
        print r1, num1(r1)
        print '\n'
        
def num1(x):
    s = 0
    for i in range(len(x)):
        if x[i] == 1:
            s = s+1
    return s
        
def find_io_perms(n):
    """ find the permutation of the PIs to an adder
    n is the length of a summand. pi is the input permutation. po is the output
    permutation. These are only used for comparison at the end as well as
    instantiating permutted adder, addp.
    We us the fact that bit j in  summand 1 can be interchanged with bit j
    of summand 2 in an adder"""
    global pi,po
    in_perm_1 = in_perm_2 = []
    out_perm = []
    N=2*n
    all1=[1]*N
    for k in range(n):
        #find next position for both the left and right summands
        max1 = 0
        for i in range(N):
            if i in in_perm_1+in_perm_2:
                continue
            xyp=list(all1)
            for j in range(N): # put 0's in the first found bits of the first summand
                if j in in_perm_1 or j == i:
                    xyp[j]=0
            r =addp(xyp)#this is an adder where its inputs and outputs are permuted
            t = num1(r)
            if t > max1: #found a new max
                max1 = t
                maxi_1 = i
                continue
            if t == max1: #found the second max
                maxi_2 = i
        in_perm_1 = [maxi_1] + in_perm_1 
        in_perm_2 = [maxi_2] + in_perm_2
    #in_perm now has the correct permutation
    print 'computed pi perm = '
    print in_perm_1
    print in_perm_2
    print 'pi perm = '
    print pi[:n]
    print pi[n:]
    print '\n'
    # now find the output permutation
    out_perm = []
    rng = range(n)
    rng.reverse()
    all0 = [0]*(2*n)
    for i in rng:
        xyp = list(all0)
        xyp[in_perm_1[i]]=1
        r=addp(xyp)
        j=operator.indexOf(r,1)
        out_perm = [j] + out_perm 
    #find carry out bit.
    for i in range(n+1):
        if not i in out_perm:
            k = i
            break
    out_perm = [k] +out_perm
    out_perm = inv_perm(out_perm)
    print 'computed po perm = ',out_perm
    print 'po perm = ',po
    

def inv_perm(p):
    pq = [-1]*len(p)
    for i in range(len(p)):
        pq[p[i]] = i
        n=len(p)/2 - 1
##    print pq[:n],pq[n:]
    return pq

def set_perms(n):
    global pi,po
    pi=range(2*n)
    random.shuffle(pi)
    po = range(n+1)
    random.shuffle(po)
###################################

######################### SPARSE #########################################
""" The functions below are for manipulating sparse ISF functions """

################# trensformers #####################

def ttISF_cubeISF(ttISF):
##    print len(ttISF)
    res = []
    for j in range(len(ttISF)):
        ttt = ttISF[j] #jth PO ISF
        if ttt[0] == m.const(1): #onset
            newres = [[['-'*n_pi],[]]]
        elif ttt[0] == m.const(0):
            newres = [[[],'-'*n_pi]]
        else: 
            newres = [[sop(ttt[0]),sop(ttt[1])]]
        res = res + newres
##    print len(res)
    return res

def read_ISF_aig(name='test'):
    global m,fname,n_pi
    """  reads in an aig file containing ISFs [...,[ttonset,ttoffset],...]
    and returns a list of tt's pairs """
    m,res = pyaig.aig_to_tt_fname('%s_ISF.aig'%name)
    return res

def cubes(s):
    """ converts a SOP in tt format into a sop"""
    sp=s
    c=[]  
    while len(sp)>1:
        n = sp.find(' ')
        c=c+[sp[:n]]
        sp=sp[n+3:]
##        print c
    return c

def ttcube(cube):
    """converts a cube into a truth table"""
##    print 'entering ttcube',
##    print cube
##    print m.const(0)
    if cube == []:
        return m.const(0)
    t_t=m.const(1)
    for j in range(len(cube)):
        if cube[j]== '-':
            continue
        tj=m.var(j)
        if cube[j] =='0':
            tj=~tj
        t_t = t_t & tj
    return t_t

def set_str(st):
    res = ''
    N = m.N
    for j in range(N):
        if j+1 in st:
            res=res + '1'
        elif -(j+1) in st:
            res = res+'0'
        else:
            res = res + '-'
    return res

def sets_sop(sts):
    res = []
    for j in range(len(sts)):
        res = res + [set_str(sts[j])]
    return res
        

def tt(sp): #sop_tt
    """converts a sop into a tt"""
    t_t = m.const(0)
    for j in range(len(sp)):
        t_t = t_t | ttcube(sp[j])
    return t_t

def sop(t_t): #tt_sop
    """ converts a tt into an sop"""
    s=t_t.SOP() # actually returns isop in internal format '--1-001 1'.
    return cubes(s) #converts into '--1-001' format

def s_stt(s): # sop_tv
    """ creates a list of tt's from an sop"""
    res = []
    for j in range(len(s)):
        res = res + [ttcube(s[j])]
    return res

def stt_s(stt): # tv_sop but makes sure tts are cubes
    """ creates a sop from a list of truth tables """
    res = []
    for j in range(len(stt)):
        res = res + [min_cube(stt[j])]

def min_cube(tt):
    """finds a minimum cube containing a all minterms of tt
    N is the number of inputs. Same as tt.m.N?? """
##    print sop(tt)
    N = tt.m.N
    res = ''
    for j in range(N):
        if m.var(j,1)&tt == tt:
            res = res+'1'
        elif m.var(j,0)&tt ==tt:
            res = res+'0'
        else:
            res = res + '-'
##        print j,res
    return res

def sttx(stt,j):
    """gets the tt of stt (a list of tt but each is not necessarily a cube.)
    except jth element"""
    res = m.const(0)
    for i in range(len(stt)):
        if not i == j:
            res = res | stt[i]
    return res


def str2v(s):
    """ s is a cube (given by a string of 0,1,- and result is a list of 0,1,2
    called a vector here"""
    res = []
    for j in range(len(s)):
        if s[j] == '-':
            res = res +[2]
        elif s[j] == '0':
            res = res + [0]
        else:
            res = res + [1]
    return res

def v2str(v):
    res = ''
    for j in range(len(v)):
        if v[j] == 2:
            res = res +'-'
        elif v[j] == 0:
            res = res + '0'
        else:
            res = res + '1'
    return res

def minus(x,y):
    """ sop x minus sop y"""
    tx=tt(x)
    ty=tt(y)
    res=tx&~ty
    return sop(res)


################ synthesis and verification ###############

def synthesize(resyn_first=True):
    abc('w temp.aig')
    if resyn_first:
        run_command('ps;&get;resyn2rs;ps;renode;eliminate -V 0;ps;bdd;sop;fx')
        run_command('eliminate -V 0;ps;&get;&put;st;resyn2rs;ps;&get;&put;ps')
    else:
        run_command('ps;&get;renode;eliminate -V 0;ps;bdd;sop;fx')
        run_command('eliminate -V 0;ps;&get;&put;st;resyn2rs;ps;&get;&put;ps')
    
def ISOP(tton,ttoff):
    """ inputs are truth tables of a ISP, output is a sop """
    res = m.isop(tton,~ttoff,0)
##    print res[0]
    ttr=res[1]
    result = sop(ttr)
    check_ired(result,tton)
    return result

def check_ired(isop,tton):
    return
##    size = len(isop)
##    isopv = sop_tv(isop)
##    isopv_irr = iredv(isopv,tton)
##    assert size == len(isopv_irr),('sop is not irredundant',isop)

##def sparse_syn_ver(name='test',ife=True):
##    global m,fname,n_pi,cost_mux,cost_dav,if_espresso
##    #set equivalent #ands for mux and davio constructions
##    cost_mux = 2 #temp
##    cost_dav = 4
##    if_espresso = ife
##    ############# synthesize
##    ti=time.time()
##    N_all_syn = []
##    tree_all = []
##    cost_all = []
##    res = sparsify(name)
##    final_cost = 0
##    for i in range(len(res)):
##        on = res[i][0] 
##        off = res[i][1]
##        fname = name + '_' + str(i)
##        print ' '
##        print '**** fname = %s ****'%fname
##        tr,cost_init,cost = mux_init(on,off) # mux can choose to implement the complement
##        tree_all = tree_all + [tr]
##        cost_all = cost_all + [cost]
####        ppt(tr)
##        final_cost = final_cost + cost
####        print '%s: time = %0.2f, initial cost = %d, final cost = %d'%(fname,(time.time()-ti),cost_init,cost)
##        ######### aet up verification
##        N_syn = tree2net(n_pi,tr)
##        write_net_to_aigfile(N_syn,'%s-syn.aig'%fname)
##        N_on = tree2net(n_pi,['+',on])
##        write_net_to_aigfile(N_on,'%s_on.aig'%fname)
##        N_off = tree2net(n_pi,['+',off])
##        write_net_to_aigfile(N_off,'%s_off.aig'%fname)
##        N_onoff = combine_two_nets(N_on,N_off)
##        write_net_to_aigfile(N_onoff,'%s_onoff.aig'%fname)
##    ##    on_po = res[0]
##    ##    off_po = res[1]
##        onoff_POs = list(N_onoff.get_POs())
##        ############ verify
##        check_syn_on_off(N_syn,N_onoff)
##        N_all_syn = combine_two_nets(N_all_syn,N_syn)
##    print '%s: time = %0.2f, final cost = %d'%(fname,(time.time()-ti),final_cost)
##    write_net_to_aigfile(N_all_syn,'%s-syn.aig'%name)
##    return N_all_syn,tree_all,cost_all

def p_red(c):
    t=0
    for i in range(len(c)):
        t = t + c[i]
    return t

def syn2():
    abc('&get;&syn2;&put')
    ps()

def syn5():
    abc('&get;&synch2;&syn2;&put')
    ps()

def get_on_off(name='temp'):
    global m,fname,n_pi,if_espresso
    if_espresso=1
    m,res = pyaig.aig_to_tt_fname('%s.aig'%name)
    res0=res[0][0]
    res1=res[0][1]
    return res1,res0

##def esp(name='temp'):
##    global m,fname,n_pi,if_espresso
##    if_espresso=1
##    m,res = pyaig.aig_to_tt_fname('%s.aig'%name)
##    res0=res[0][0]
##    res1=res[0][1]
##    print 'on: ',len(sop(res0)),lit(sop(res0))
##    print 'off: ',len(sop(res1)),lit(sop(res1))
##    te = time.time()
####    r1 = espresso(sop(res0),sop(res1))
####    print 'espresso time = ',(time.time() - te), len(r1), lit(r1)
##    ttv = time.time()
####    print ''
##    r2 = tvespresso(res0,res1,0)
##    print 'tvespresso time = ',(time.time() - ttv), len(r2),
####    r2 = tv_sop(r2)
####    print lit(r2)
##    res0,res1 = res1,res0
##    te = time.time()
####    r3 = espresso(sop(res0),sop(res1))
####    print 'espresso time = ',(time.time() - te), len(r3), lit(r3)
####    print ''
##    ttv = time.time()
##    r4 = espresso(res0,res1,0)
##    print 'tvespresso time = ',(time.time() - ttv), len(r4),
####    r4 = tv_sop(r4)
##    print lit(r4)
##    return res1,res0

def get_tts():
    abc('w %s_iso_reduced')
    abc('&get')
    tts = []
    for i in range(n_pos()):
        abc('&put;cone -O i;')
        

                  
def sparsify(name='test'):
    """ ABC reads in test.aig and extracts output O. Then samples its onset and
    offset by taking a 10% sample of minterms and creates an file 'test_sp_O.aig'
    Returns sop of onset and sop of offset
    """
    global m,fname,n_pi
    run_command('r %s.aig'%name)
    npi = n_pis()
    assert npi<17,'number of PIs exceeds 16'
    p = 10
    if npi > 12:
        tabl=[9,9,8,8]
        p = tabl[(npi-12)-1]
##    ps()
##    run_command('cone -O %d'%O)
##    ps()
    print 'collasping isf'
    run_command('st;ps;clp;sparsify -N %d;st;ps'%p) #creates ISFs for each PO.
##    ps()
##    fname = '%s_%d'%(name,O)
##    fname = name
    print 'writing isf'
    run_command('w %s_ISF.aig'%name)
    print 'reading isf'
    res = read_ISF_aig(name) #assumes on's,off's are interleaved POs. Here m is created
    #res is a list of tt ISFs for each PO of the aig read in
    n_pi = m.N # number of PIs
##    print len(res)
##    print len(res[0])
    print 'converting tt to tv'
    result = ttISF_cubeISF(res)
    print 'done'
    return result

def syn2_iter():
    best = n_ands()
    abc('w temp_best.aig')
    abc('&get')
    while True:
        abc('&syn2;&put')
        if n_ands() < best:
            abc('&save')
            best = n_ands()
            print best,
        else:
            abc('&load')
            print '\n'
            return

def syn5_iter():
    best = n_ands()
    abc('w temp_best.aig')
    while True:
        syn5()
        if n_ands() < best:
            abc('w temp_best.aig')
            best = n_ands()
            print best
        else:
            abc('r temp_best.aig')
            return       
        

def comb(fn):
    """ extracts the combinational part of a sequential aig and writes it out"""
    abc('r %s.aig;comb;w %s-comb.aig'%(fn,fn))


def check_syn_on_off(N_synthesized, N_onoff):
    """ Main verification. Verifies that the synthesized network f is correct.
    Does this in two steps. f does not intersect off and ~f does not
    intersect on. S.solve(a,b) is SAT if a and b intersect, i.e. the assumptions
    a and b are compatible
    """
    OK=True
    N, f, onset, offset = pre_check(N_synthesized, N_onoff)
    S = pyzz.solver(N)
    if S.solve( onset, ~f) == pyzz.solver.SAT:
        print 'f does not cover the onset'
        OK=False
    if S.solve( f, offset ) == pyzz.solver.SAT:
        print 'f intersects offset'
        OK=False
    if OK:
        print "synthesis verified"
    return OK

def pre_check(N_synthesized, N_onoff):
    """Creates net with PO's = (f,on,off)"""
    N, (xlat_syn, xlat_onoff) = pyzz.combine_cones(N_synthesized, N_onoff)
##    f = get_POs(xlat_syn,N_synthesized)
    syn_POs = list(N_synthesized.get_POs())
##    print syn_POs
    f = xlat_syn[ syn_POs[0][0] ] # synthesized. The last [0] gets the fanin of the PO
    onoff_POs = list(N_onoff.get_POs())
##    print 'onoff_POs = ',onoff_POs
    onset = xlat_onoff[ onoff_POs[0][0] ] #onset of ISF
    offset = xlat_onoff[ onoff_POs[1][0] ] #offset of ISF
    return N, f, onset, offset


def check(c1,c0,x1,x0):
    ontt = tt(x1)
    offtt = tt(x0)
    c1tt = tt(c1)
    c0tt = tt(c0)
    outtt = c1tt&~c0tt
##    return ontt.implies(outtt) & offtt.implies(~outtt)
    if not outtt&ontt == ontt:
        print 'out does not cover on'
        return False
    if not ~outtt&offtt == offtt:
        print 'out intersects off'
        return False
    return True

def check_off(cube,offtt):
    """ check if cube intersects the tt offset"""
    tt_cube = ttcube(cube)
    intt = tt_cube & offtt
    #if cube does not intersect the offset, return 1
    return m.const(0)== intt

def covers(x,y):
    """ x is a sop aand y a tt"""
    return tt(x) & y == y

###############################
                            
def d2b(d,N):
    res = [0]*N
    J = range(N)
    J.reverse()
    for j in J:
##        print d >= 2**j
        if d >= 2**j:
            res[N-(j+1)] = 1
            d=d-2**j
##        print j,d,res
    return res

################ new espresso based entirely on truth tables ##############

def sparse_syn_verv(name='test',ife=True,density=10):
    global m,fname,n_pi,cost_mux,cost_dav,if_espresso
    #set equivalent #ands for mux and davio constructions
    cost_mux = 2
    cost_dav = 4
    if_espresso = ife
    ############# synthesize
    ti=time.time()
    N_all_syn = []
    tree_all = []
    cost_all = []
    all_OK = True
    res = sparsifyv(name,density) #res is a set if ISFs where each is [tton,ttoff]
    final_cost = 0
##    print len(res[0])
    for i in range(len(res)):
##        assert type(res[i]) == list, (i,res[i])
##        assert len(res[i])>1,(i,res[i])
        tton = res[i][0]
        ttoff=res[i][1]
##        ton = or_red(res[i][0])
##        toff = or_red(res[i][1])
        fname = name + '_' + str(i)
        print ' '
        print '**** fname = %s ****'%fname
        tr,cost_init,cost = mux_initv(tton,ttoff) # mux can choose to implement the complement
##        print tr
##        tr = [str(i)+'. '] + tr
        tree_all = tree_all + [str(i)+'. '] + [tr]
        cost_all = cost_all + [cost]
##        ppt(tr)
        final_cost = final_cost + cost
##        print '%s: time = %0.2f, initial cost = %d, final cost = %d'%(fname,(time.time()-ti),cost_init,cost)
        ######### aet up verification
        N_syn = tree2net(n_pi,tr)
        write_net_to_aigfile(N_syn,'%s-syn.aig'%fname)
        on = sop(tton)
        off = sop(ttoff)
        N_on = tree2net(n_pi,['+',on])
        write_net_to_aigfile(N_on,'%s_on.aig'%fname)
        N_off = tree2net(n_pi,['+',off])
        write_net_to_aigfile(N_off,'%s_off.aig'%fname)
        N_onoff = combine_two_nets(N_on,N_off)
        write_net_to_aigfile(N_onoff,'%s_onoff.aig'%fname)
    ##    on_po = res[0]
    ##    off_po = res[1]
        onoff_POs = list(N_onoff.get_POs())
        ############ verify
        all_OK = all_OK and check_syn_on_off(N_syn,N_onoff)
        N_all_syn = combine_two_nets(N_all_syn,N_syn)
    print '%s: time = %0.2f, final cost = %d'%(fname,(time.time()-ti),final_cost)
    if all_OK:
        print 'all synthesized POs verified correct'
    else:
        print '**** one of the POs failed verification ****'
    write_net_to_aigfile(N_all_syn,'%s-syn.aig'%name)
    return N_all_syn,tree_all,cost_all

def mux_initv(tton,ttoff):
    """ initial call to create a cofactoring tree with minimum cost"""
    ttime = time.time()
##    print 'entering tvespresso'
    pp = tvespresso(tton,ttoff,0,ifesp=if_espresso) # 0 here means return sop, 1 return isop
##    print 'done, entering tv_sop'
##    pp=tv_sop(tvpp)
##    print 'done'
##    print 'sop size = ',len(pp)
    cost = count_fact_sop(pp)
    cost_init = cost
    #begin the recursion
    if cost > 0:
        tree_r,cost = cof_recurv(tton,ttoff,pp,cost)
##        print ''
##        ppt(tree_r)
    else:
        tree_r = ['+',pp]
    print 'time = %0.2f, initial cost = %d, final cost = %d'%((time.time()-ttime),cost_init,cost)
##    print tree_r
##    print_tree(tree_r)
    return tree_r,cost_init,cost

def tv_sop(tv):
    s=[]
    for i in range(len(tv)):
        s = s + [tv_cube(tv[i])] 
    return s

def sparsifyv(name='test',density=10):
    """ ABC reads in test.aig and extracts output O. Then samples its onset and
    offset by taking a 10% sample of minterms and creates an file 'test_sp_O.aig'
    Returns sop of onset and sop of offset
    """
    global m,fname,n_pi
    run_command('r %s.aig'%name)
    npi = n_pis()
    assert npi<17,'number of PIs exceeds 16'
    p = density
    if p == 10:
        if npi > 12:
            tabl=[9,9,8,8]
            p = tabl[(npi-12)-1]
    run_command('st;ps;clp;sparsify -N %d;st;ps'%p) #creates ISFs for each PO.
##    print 'writing ISF file'
    run_command('w %s_ISF.aig'%name)
    res = read_ISF_aig(name) #assumes on's,off's are interleaved POs.
    #Here m is created
    #res is a list of tt ISFs for each PO of the aig read in
    n_pi = m.N # number of PIs
##    print len(res)
##    print len(res[0])
##    print 'converting to tv'
##    result = res #can take a long time
##    print 'done'
    return res

def cof_recurv(tton,ttoff,sop_in,cost):
    """ cofactoring wrt a single variable has to beat incoming cost
    a tree is either an sop or an expantion -  ite - [[v,method],tree1,tree2]
    the input is the ISF (ton,toff) to be implemented.
    Incoming cost is an upper bound for implementation.
    This returns (sop_in, cost) if there is no expansion that can beat cost.
    Otherwise, it returns expansion tree for the ISF.
    (tton,ttoff) is the current ISF and sop_in is its SOP
    """
##    if lit(sop(tton))<=1:#we are at a leaf because tton is a single variable. don't do anything
##        return ['+',sop_in],cost
    assert not type(tton) == int, (tton,ttoff,sop_in,cost)
    N=tton.m.N
##    ton = or_red(tvon)
##    toff = or_red(tvoff)
    tton_init = tton
    cost_in = cost
    sop_r,cost,sign =choose_signv(tton,ttoff,sop_in,cost)
    assert cost <= cost_in,'cost_in = %d, cost = %d'%(cost_in,cost)
    cost_in = cost
    print '\ninitial factored cost = %d'%cost_in
##    print ''
##    print 'sign = %s, cost = %d'%(sign,cost)
    if sign == '-':
        tton,ttoff = ttoff,tton
    imin,leaf1,leaf0,cost1,cost0,method = get_split_var2v(tton,ttoff) #most binate
    # sign is '+' or '-'.  If '-' then ton and toff need to be switched
    #method at this point is 'shannon'
##    print 'most binate variable = ',imin
    cost_add = cost_mux
    newcost1 = cost0+cost1+cost_add
    if imin == -1:
        newcost1 = 10000
    imin2,leaf12,leaf02,cost12,cost02,method2 = get_split_varv(tton,ttoff)
    newcost2 = cost02+cost12+cost_add
    cxor,i_xor,pxor,sxor,ntton,nttoff,xsign = get_xor_var(tton,ttoff)
    if cxor < min(cost,newcost1,newcost2) and i_xor > -1:
        print '*** XOR wins ***'
        tree1,cost1 = cof_recurv(ntton,nttoff,sxor,cxor)
        assert cost1 <= cxor,'espresso did not beat ISOP'
        if pxor == 0:
            i_xor = -(1+i_xor) #done to distinguish +0 from -0
        print 'final cost = %d'%cost1
        return [[i_xor,'xor',xsign,sign],tree1],cost1
    if min(newcost1,newcost2) >= cost:
        print 'final cost = %d'%cost_in
        return [sign,sop_r],cost_in # tree is just initial sop + or -
    elif newcost2< newcost1:
        print '*** mux2 wins, newcost2 = %d ***'%newcost2
        cost = newcost2
        imin,leaf1,leaf0,cost1,cost0,method = imin2,leaf12,leaf02,cost12,cost02,method2
    else:
        print '*** mux1 wins, newcost1 = %d ***'%newcost1
        cost = newcost1
    #recur here since a variable exists, namely imin, whose two cofactors can be
    #implemented as sop's plus a mux with less cost than the incoming 'cost'
    if cost1 > 0: 
        tton1=cofactor(tton,imin,1)
        ttoff1=cofactor(ttoff,imin,1)
        tree1,cost1 = cof_recurv(tton1,ttoff1,leaf1,cost1)
    else: #a single literal cube has 0 cost
        tree1=['+',leaf1]
    if cost0 > 0:
        tton0=cofactor(tton,imin,0)
        ttoff0=cofactor(ttoff,imin,0)
        tree0,cost0 = cof_recurv(tton0,ttoff0,leaf0,cost0)
    else: #a single literal cube has 0 cost
        tree0=['+',leaf0]
    newcost = cost0+cost1+cost_add
    assert newcost <= cost,'counts not compatible: cost = %d, cofactors count = %d'%(cost,newcost)
    print 'final cost = %d'%newcost
    return [[imin,method,sign],tree1,tree0],newcost

def choose_signv(tton,ttoff,pp1,cost1):
    """Choose which phase to implement. Return best sop, its cost and if complementwas chosen"""
##    pp1=espresso(on,off)
    pp0=tvespresso(ttoff,tton,0,ifesp=if_espresso)
##    pp0 = tv_sop(tvpp0)
##    cost1 = count_and_sop(pp1)
    cost0 = count_fact_sop(pp0)
    if cost1 <= cost0:
        cost = cost1
        pp = pp1
        sign = '+'
    else:
        cost = cost0
        pp = pp0
        sign = '-'
##    print 'sign = ',sign
    return pp,cost,sign

def get_split_varv(tton,ttoff):
    """ pick the variable and method for expansion with the least cost
    Currently only Shannon is done here. Uses real espresso on final choice"""
    global if_espresso
    if_espresso_old = if_espresso
    N=tton.m.N
##    print N
    cost_min = 100000
    if_espresso = 0 # forces using bbop in espresso to find imin
    for i in range(N):
##        print v_in(i,ton)
        if not v_in(i,tton): # i does not exist in tton
            continue
        cost1,cost0,leaf1,leaf0,method = mux_vv(tton,ttoff,i) #uses ISOP here to find imin
        cost_add = cost_mux
        if not method == 'shannon':
            cost_add = cost_dav
##        print cost_add
        cost = cost0+cost1+cost_add
        if cost < cost_min:
            leaf1_min = leaf1
            leaf0_min = leaf0
            cost_min = cost
            cost0_min = cost0
            cost1_min = cost1
            imin=i
            method_min = method
    if if_espresso_old == 0: #done
        return imin,leaf1_min,leaf0_min,cost1_min,cost0_min,method_min
    else: #we try to get a better cost with espresso, but maybe not
        if_espresso = 1
        cost1e,cost0e,leaf1e,leaf0e,methode = mux_vv(tton,ttoff,imin) #uses full espresso on imin cofactors
        coste = cost1e+cost0e+cost_add
##        print 'coste,cost_min = ',(coste,cost_min)
        if coste >= cost_min: # espresso lost to isop
            return imin,leaf1_min,leaf0_min,cost1_min,cost0_min,method_min
        else:
            return imin,leaf1e,leaf0e,cost1e,cost0e,methode

def cofactor_isp(f,v):
    return [f[0].cofactor(v,0),f[1].cofactor(v,0)],[f[0].cofactor(v,1),f[1].cofactor(v,1)]

def cofactor(t_t,v,ph):
    ttc = t_t.cofactor(v,ph)
##    tvc=[]
##    for i in range(len(tv)):
##        tvc = tvc + [tv[i].cofactor(v,ph)]
    return ttc

def mux_vv(tton,ttoff,v):
    """ try a cofactoring variable v and return its costs and leaves
    if_espresso = 0 ==> uses ISOP"""
    tton1 = cofactor(tton,v,1)
    ttoff1 = cofactor(ttoff,v,1)
    leaf1 = tvespresso(tton1,ttoff1,0,ifesp=if_espresso)
##    leaf1 = tv_sop(tvleaf1)
    cost1=count_fact_sop(leaf1)
    ################
    tton0 = cofactor(tton,v,0)
    ttoff0 = cofactor(ttoff,v,0)
    leaf0 = tvespresso(tton0,ttoff0,0,ifesp=if_espresso)
##    leaf0 = tv_sop(tvleaf0)
    cost0=count_fact_sop(leaf0)
    return cost1,cost0,leaf1,leaf0,'shannon'

def get_split_var2v(tton,ttoff): #find most binate variable
    """ pick the variable and method for expansion with the most binateness
    """
    global if_espresso
    N=tton.m.N
##    print N
    cost_min = 100000
##    if_espresso_old = if_espresso
##    if_espresso = 0 # set to have espresso return ISOP
    epos = tvespresso(tton,ttoff,0,ifesp=if_espresso) # real espresso here
##    epos = tv_sop(tvepos)
    imin = get_most_binate_var(epos)
##    if_espresso = if_espresso_old #restore if_espresso
    if imin == -1:
        return -1,0,0,0,0,0
    cost1,cost0,leaf1,leaf0,method = mux_vv(tton,ttoff,imin) #calls real espresso on imin cofactors
    return imin,leaf1,leaf0,cost1,cost0,method

def bbop(tton,ttoff):
    """ does both isop and bsop and chooses the best"""
    isp = ISOP(tton,ttoff)
    bsp = bsop(tton,~ttoff)
    res = isp
    if lit(bsp) < lit(isp):
        res = bsp
    return res

def bsop(tton,uv,varbs=[]):
    """ like isop, but at each step tries to make result independant of variable v
    Like isop result is dependent on the order of the variables.
    tton is the lower bound and uv is the upperbound
    """
    N = m.N
##    if v == -1:
##        v = N-1
    if tton == m.const(0):
##        print ''
##        print v,[]
        return []
    elif uv == m.const(1) or len(varbs) == N:
##        print ''
        bsp = ['-'*N]
##        print v,bsp
        return bsp
    else:
        v = choose_varb(tton,uv,varbs)
        new_varbs = varbs + [v]
        L1 = tton.cofactor(v,1)
        L0 = tton.cofactor(v,0)
        U1 = uv.cofactor(v,1)
        U0 = uv.cofactor(v,0)
        R0 = bsop(L0&~(U1 | (L1 & ~U0)),U0,new_varbs)
##        print R0
        R1 = bsop(L1&~(U0 | (L0 & ~U1)),U1,new_varbs)
##        print R1
        R2 = bsop((L0&~tt(R0) | L1&~tt(R1)),U0&U1,new_varbs)
##        print R2
        result = R2 + addv(v,1,R1) + addv(v,0,R0)
        return result

def choose_varb(tton,uv,varbs):
    """ chooses the variable with the least number of minterms covered in onset
    of both R0 and R1. The heuristic is that this would make R0 and R1
    as simple as possible (maybe).
    """
    N = m.N
    min_count = 100000
    minv = -1
    for i in range(N):
        if i in varbs:
            continue
        else:
            L1 = tton.cofactor(i,1)
            L0 = tton.cofactor(i,0)
            U1 = uv.cofactor(i,1)
            U0 = uv.cofactor(i,0)
            both = (L0&~(U1 | (L1 & ~U0))) | (L1&~(U0 | (L0 & ~U1)))
            cnt = both.count()
            if cnt < min_count:
                min_count = cnt
                minv = i
    return minv

def exop(f, v=0):
    """ f is a ISF, [on,off] where each is a tt.
    esop returns a list of cubes when xor-ed together forms a cover of on and
    does not intersect off"""
    N = m.N
##    print v
    on = f[0]
    off = f[1]
##    assert type(on) == pyaig.truthtables._truth_table, (lb,ub)
##    assert type(off) == pyaig.truthtables._truth_table, (lb,ub)
##    assert (not (on == m.const(0) and off == m.const(0))),'both on and off = 0'
    if on == m.const(0):
        return []
    elif off == m.const(0) or v == N-1: #or len(varbs) == N:
        return ['-'*N]
    else:
##        v = choose_varb(tton,uv,varbs)
##        new_varbs = varbs + [v]
##        on_1 = on.cofactor(v,1) # pos cofactor is [on1,off1] = f_1
##        off_1 = off.cofactor(v,1)
##        on_0 = on.cofactor(v,0) # neg cofactor is [on0,off0] = f_0
##        off_0 = off.cofactor(v,0)
        f_0,f_1 = cofactor_isp(f,v)
##        vxor = ixor(f_0,f_1)
        ##        f_1 = [on_1,off_1]
##        vxor = [on_1&off_0|on_0&off_1,on_1&on_0|off_1&off_0] #xor of f_0 and f_1
##            # or ixor is [(f[0]&~g[1])|(~f[1]&g[0]),(f[0]&g[0])|(~f[1]&~g[1])]
        R0 = exop(f_0,v+1)
        print R0
        R1 = exop(f_1,v+1)
        print R1
##        R2 = exop(vxor,v+1)
##        print R2
        n0 = len(R0)
        n1 = len(R1)
        ttR0 = tt(R0)
        ttR1 = tt(R1)
        if n0 <= n1: # Make R2'
            tv0 = m.var(v)&ttR0
            R2_p = exop([tv0&f_1[0],tv0&f_1[1]],v)
            ttR2 = tv0 &~tt(R2_p) | (~tv0)&tt(R2_p)
            R2 = sop(ttR2)
            n2 = len(R2)
        else:
            tv1 = (~m.var(v))&ttR1
            R2_p = exop([tv1&f_1[0],tv1&f_1[1]],v)
            ttR2 = tv1 &~tt(R2_p) | (~tv1)&tt(R2_p)
            R2 = sop(ttR2)
            n2 = len(R2)
        print n0,n1,n2
        mx = max(n0,n1,n2)
        if n0 == mx:
            return R1 + R2  #negative davio 
        if n1 == mx:
            return R0 + R2 # poaitive davio
        else:
            return addv(v,0,R0) + addv(v,1,R1) # shannon


    

##def bsopr(tton,ttup,v=-1):
##    """ like isop, but at each step tries to make result independant of variable v
##    Like isop result is dependent on the order of the variables."""
##    N = m.N
##    if v == -1:
##        v = N-1
##    if tton == m.const(0):
##        return []
##    elif ttup == m.const(1):
####        print ''
##        bsp = ['-'*N]
####        print v,bsp
##        return bsp
##    else:
##        uv = ttup
##        L1 = tton.cofactor(v,1)
##        L0 = tton.cofactor(v,0)
##        U1 = uv.cofactor(v,1)
##        U0 = uv.cofactor(v,0)
##        R0 = bsopr(L0&~U1,U0,v-1)
####        print R0
##        R1 = bsopr(L1&~U0,U1,v-1)
####        print R1
##        R2 = bsopr((L0&~tt(R0) | L1&~tt(R1)),U0&U1,v-1)
####        print R2
##        result = R2 + addv(v,1,R1) + addv(v,0,R0)
##        return result
##
##def bsop(tton,ttoff):
##    resf=bsopf(tton,~ttoff)
##    resr = bsopr(tton,~ttoff)
##    result = ired(resf+resr,tton)
##    return result


##    on_x = onv1 | onv0
##    assert on_x & tton == tton, 'on_x does not cover tton'
####    off_x = offv1 | offv0
##    off_x = ttoff
##    assert off_x & ttoff == ttoff, 'off_x does not cover ttoff'
##    if on_x & off_x == m.const(0): # result is independent of variable v
####        print 'result independent of variable %d'%v
##        bsp = bsop(on_x, off_x, v+1)
##        print ''
##        print '*',v,bsp
##        return bsp
##    else:
##        bp = bsop(onv1, offv1,v+1)
##        bn = bsop(onv0, offv0,v+1)
##        x2,x1,x0=merge(bp,bn)
##        bsp =  x2+addv(v,1,x1)+addv(v,0,x0)
##        print ''
##        print v,bsp
##        assert tt(bsp) & tton == tton, 'onset not covered. v, x2,x1,x0 = %d,   %s,   %s,   %s'%(v,str(x2),str(x1),str(x0))
##        return bsp
        

def addv(v,ph,s):
    res = []
    for i in range(len(s)):
        si = s[i]
        lsi = list(si)
        assert lsi[v] == '-', 's is not independent of v'
        lsi[v] = '01'[ph]
        res = res + [strl_str(lsi)]
    return res

##def addv(v,ph,s):
##    """ puts in literal [v,ph] into sop s """
##    tts = tt(s)
##    return sop(tts & m.var(v,ph))
    
##def merge(sp,sn):
##    """ finds common cubes and puts them in res2 and takes these away from sp and sn """
##    s2 = sp+sn
##    s2.sort()
##    res2 = []
##    for i in range(len(s2)-1):
##        if s2[i] == s2[i+1]:
##            res2 = res2 + [s2[i]]
##    res1 = []
##    for i in range(len(sp)):
##        if not sp[i] in res2:
##            res1 = res1 + [sp[i]]
####            print res1
##    res0 = []
##    for i in range(len(sn)):
##        if not sn[i] in res2:
##            res0 = res0 + [sn[i]]
##    return res2,res1,res0
            
def tvespresso(tton,ttoff,returntv=1,ifesp=1):
    """ tton and ttoff are ISOPs and truth tables
    returntv => return a tv, else sop
    ifesp => use full espresso, else use isop
    """
    global m,fname,n_pi
    m=tton.m
##    print len(tton),len(ttoff)
    if tton == m.const(0): # on = 0 so []
####        print ''
        return []
    if ttoff==m.const(0): #no offset so return 1
##        print ''
        if returntv:
            return [m.const(1)]
        else:
            return sop(m.const(1))
##    time0=time.time()
    if not ifesp:
        if returntv:
            return sop_tv(bbop(tton,ttoff))
        else:
            return bbop(tton,ttoff)
##    tv1=list(tton)        # new
##    isop = ISOP(tton,ttoff) # new
##    print 'isop: %d, %d'%(len(isop), lit(isop))
##    bsp = bsop(tton,~ttoff)
##    print 'bsop: %d, %d'%(len(bsp), lit(bsp))
##    if lit(bsp) < lit(isop):
##        isop = bsp
    isop = bbop(tton,ttoff)
    tv1 = sop_tv(isop)
    Jess,nJess = qessentials(isop) #returns list of essential primes
    tv1,tvessen = sublist(tv1,nJess),sublist(tv1,Jess)
##    isop,isopessen = sublist(tv1,nJess),sublist(tv1,Jess)
##    tton = or_red(tton)
##    print sop(tton)
    while True: #iterate until no reduction
        size=len(tv1)
        tv1old = tv1
##        print 'before: ',len(tv1),litv(tv1)
        tv1_red = reduce_tv(tv1,tton,tvessen)
##        print 'after ', len(tton_red),litv(tton_red)
        tv1=two_levelv(tv1_red,ttoff)
##        print 'two_level: ',len(tv1),litv(tv1)
        if len(tv1)>=size:
            break
        tv1=shffle(tv1)
    if len(tv1) > len(tv1old):
        tv1=tv1old
    elif len(tv1) == len(tv1old):
        if litv(tv1old)<litv(tv1):
            tv1=tv1old
##    print 'time of espresso = ',time.time()-time0
##    print 'espresso: cubes = %d, lits = %d'%size_of(t1)
##    print ''
    res = tv1+tvessen
    if returntv:
        return res
    else:
        return tv_sop(res)

def max_reduce(tv,j):
    tvj = tv[j]
    ttrest = or_redx(tv,j)
    tres = min_cubev(tvj&~ttrest)
    return tres

def essentials(sop_in,tton,ttoff):
    """ max reduce each cube cj (cj = -1-1--0')to cj_max (cj_max = '-1-1100').
    for each place where both have literals, try to expand cj_max.
    If expansion exists, then not essential
    """
    tv = sop_tv(sop_in)
    ess = []
    N=m.N
##    print N
    for j in range(len(sop_in)):
        ttj = tv[j] #tt of j the cube
        ttj = ttj&tton # only interested in care onset
        sj=sop_in[j]
##        print ''
##        print sj
        ans = True
        for i in range(N):
            if sj[i] == '-':
                continue
            sji = int(sj[i]) # literal i in sj
##            print i,sji,
            assert m.var(i,sji)& ttj == ttj, 'ttj is not in %d_%s'%(i,sji)
            ttjd1 = ttj.cofactor(i,sji) & m.var(i,not sji) # project along var i
            ttjd1 = ttjd1&~ttoff # restrict to on/dc in dist-1 cube
            ttj1 = ttjd1.cofactor(i,not sji) & m.var(i,sji) # project back along var i
            ttj = ttj&~ttj1 # take away those that have a on/dc neighbor
            if ttj == m.const(0): # j is not essential
##                print '%d is not essential'%j
                ans = False
                break # go to next cube
        if ans:
            ess = ess + [j] # aomething left in jth cube, so essential
##    print ess
    return sublist(sop_in,ess)

def qessentials(sop_in):
    """ quick finding of minterm primes plus single literal primes """
    ness = ess = []
    for j in range(len(sop_in)):
        sj=sop_in[j]
        if not '-' in sj: # a minterm prime is essential
            ess = ess + [j]
            continue
        count = 0
        for i in range(m.N):
            if sj[i] == '-':
                continue
            else:
                count =count +1
        if count == 1: # single literal prime is essential
            ess = ess + [j]
        else:
            ness = ness + [j]
##    print ess
    return ess,ness


def litv(tv):
    count=0
    for j in range(len(tv)):
        count = count + lit_cubev(tv[j])
    return count

def lit_cubev(tvc):
    count = 0
    N = m.N
    for i in range(N):
        if m.var(i,0) & tvc == tvc or m.var(i,1) & tvc == tvc:
            count = count + 1
    return count

def tv_cube(tvc): 
    """ takes a tt, tvc, which should be a cube and creates a sop cube
    """
    res = ''
    N = m.N
    for i in range(N):
        if m.var(i,0) & tvc == tvc:
            res = res + '0'
        elif m.var(i,1) & tvc == tvc:
            res = res + '1'
        else:
            res = res + '-'
    return res

def v_ISOP_v(tvon,tvoff):
    """ inputs are truth table vectors """
    tton = or_red(tvon)
    ttoff = or_red(tvoff)
    res = m.isop(tton,~ttoff,0) #res[1] is a truth table, res[0] is a sop in set form
    return set_tv(res[0])
##    ttr=res[1]
##    tvr = tt_tv(ttr)
##    return tvr

def set_tv(st):
    """convert a set st into a tv"""
    tv = []
    for j in range(len(st)):
        cj=st[j] #a set
##        print cj
        tcj=m.const(1)
        for i in cj:
            tcj =tcj&m.var(abs(i)-1,abs(i)==i)
        tv = tv + [tcj]
    return tv
        

def t_ISOP_v(tton,ttoff):
    """ inputs are truth table vectors """
    res = m.isop(tton,~ttoff,0)
##    print res
    result = set_tv(res[0])
    check_ired(result,tton)
    return result
##    ttr=res[1]
##    tvr = tt_tv(ttr)
##    return tvr

def tv_tt(tv):
    return or_red(tv)

def or_red(tv):
    res = m.const(0)
    for i in range(len(tv)):
        res = res|tv[i]
    return res

def or_redx(tv,j):
    res = m.const(0)
    for i in range(len(tv)):
        if not i == j:
            res = res|tv[i]
    return res

def two_levelv(tvon,ttoff,rev=1):
    """ only used in espresso. Makes primes and removes duplicates and selects
    a subset in order of which cover the most remaining minterms of 'on' """
    time0=time.time()
    tvc1= []
    ttc1=m.const(0)
    tton = or_red(tvon)
    p1=make_primesv(tvon,ttoff)
    if rev:
        p1=p1+make_primesv(tvon,ttoff,1) #do in reverse order of variables
    if not p1 == []:
        tvp1=remove_dup(p1)
    else:
        tvp1 = p1
##    print 'two_level1: ',len(tvp1)
##    ttp1 = tt_of_p(p1) #vector of truth tables
    while True: # iteratively include the cube that covers the most minterms not yet covered 
        t1=tton&~ttc1 # onset still to be covered
        if t1.count()==0:
            break
        j1,count1=max_countv(tvp1,t1)
        tvc1 = tvc1 + [tvp1[j1]]
        ttc1 = ttc1 | tvp1[j1]
##        ttc1 = tton&ttc1 #restrict to onset
##    print 'two-level2: ',len(tvc1)
    tvc1=iredv(tvc1,ttc1)
##    print 'two_level3: ',len(tvc1)
##    print 'cubes = %d, lits = %d'%(len(c1),lit(c1))
##    print 'time for two_level = ',time.time() - time0
    return tvc1


def make_primesv(tvx11,ttoff,rev=0):
    """expands cubes of x1 against offset x0"""
##    tvx1 = remove_dup(tvx11)
    tvx1=tvx11
    tvp=[]
##    ttr=m.const(0)#
    for j in range(len(tvx1)):
##        if tvx1[j]&~ttr == m.const(0):#
##            continue #
        tvpj=make_primev(tvx1[j],ttoff,rev)
##        tvp.append(tvpj)
        tvp = tvp+[tvpj]
##        ttr = ttr | tvpj #
    return tvp

def make_primev(tcube,ttoff,rev=0):
    """ expands aa cube into a prime. off must be a tt"""
    J = range(m.N)
    if rev:
        J.reverse()
    res = tcube
    for j in J:
        cjex = res.cofactor(j,0) | res.cofactor(j,1)
        if not ((cjex & ttoff) == m.const(0)):
            continue
        else: #expansion OK
            res = cjex
    return res

def iredv(tvp,tton):
    """ makes sop tvp irredundant relative to onset truth table"""
    res = []
    red = list(tvp)
    for j in range(len(tvp)):
        tvj=tvp[j]&tton #care part of cube j
        if (tvj&~or_redx(red,j)) == m.const(0): # reduce jth cube to 0
            red[j]=m.const(0)
        else: #keep cube j
            res = res + [tvp[j]]
    return res

def max_countv(tvs,tton):
    """ find the cube that covers the most minterms in ontt"""
    maxc = -1
    maxj = -1
    for j in range(len(tvs)):
        ctt = tvs[j]
##        ctt = tt([c])
        tc = ctt&tton
        count = tc.count()
        if count > maxc:
            maxc = count
            maxj = j
    return maxj,maxc

def reduce_tv(tvs,tton,essen=[]):
    """reduces cube in tvs to a minimum cube containing onset minterms not in rest of cubes
    Replaces each ttcube with reduced ttube. Done in the given given order of cubes"""
##    ontt = tt(on)
    if tvs == []:
        return []
    m = tton.m
    N = m.N
##    stt = s_stt(s)
    J = range(len(tvs))
    J.reverse()
    tvpp=list(tvs)
    ttess = m.const(0)
    tton1=tton
    if not essen == []:
##        print essen
        ttess = or_red(essen)
        tton1 = tton&~ttess
    for j in J:
        tvj = tvs[j]&tton1 & ~or_redx(tvpp,j) #care part of j not overed by rest
        tvpp[j]=min_cubev(tvj) # put back reduced cube for j
    return tvpp

def min_cubev(tt):
    """finds a minimum cube containing a all minterms of tt
    N is the number of inputs. Same as tt.m.N?? """
##    print sop(tt)
    N = tt.m.N
##    print sop(tt),
    res = m.const(1)
    for j in range(N): # for each variable
        if m.var(j,1)&tt == tt: #all minterms in x_j face
            res = res & m.var(j,1)
        elif m.var(j,0)&tt == tt: # all in ~x_j face
            res = res & m.var(j,0)
        else: #points on both faces so merge both faces (cube will have a '-' in jth spot
            continue
##        print j,res
##    print sop(res)
    return res

def ttISF_tvISF(ttISF):
    """ converts a list of ISFs, each given as a tt, to a list of ISFs each given as
    a [tv for on, tv for off]
    """
    res = []
    for j in range(len(ttISF)):
        ttj = ttISF[j] #jth PO ISF
        if ttj[0] == m.const(1): #onset
            newres = [m.const(1),m.const(0)]
        elif ttj[0] == m.const(0):
            newres = [m.const(0),m.const(1)]
        else: 
            newres = [[tt_tv(ttj[0]),tt_tv(ttj[1])]] 
        res = res + newres
    return res

def tt_tv(tt):
##    s = sop(tt)
##    tv=t_ISOP_v(tt,tt)
    tv = sop_tv(sop(tt))
    return tv

def sop_tv(s):
    """ converts a sop into a tv"""
    res = []
    for j in range(len(s)):
        res = res + [ttcube(s[j])]
    return res

################# espresso ##########                            

##def espresso(on,off):
##    """ on and off are SOPs
##    returns a SOP """
##    if len(on) == 0: # on = [] so 0
##        return on
##    if len(off)==0: #no offset so return 1
##        n_v = len(on[0])
##        return ['%s'%'-'*n_v]
####    time0=time.time()
##    if not if_espresso:
##        return ISOP(tt(on),tt(off))
##    s1=list(on)
##    while True: #iterate until no reduction
##        size=len(s1)
##        s1old = s1
##        s1=two_level(reduce_sop(s1,on),off)
##        if len(s1)>=size:
##            break
##        s1=shffle(s1)
##    if len(s1) > len(s1old):
##        s1=s1old
##    elif len(s1) == len(s1old):
##        if lit(s1old)<lit(s1):
##            s1=s1old
####    print 'time of espresso = ',time.time()-time0
####    print 'espresso: cubes = %d, lits = %d'%size_of(t1)
##    return s1

def expand_cube(cube,j):
    """expands a cube along the jth direction by putting in a '-' there """
    res=''
    for i in range(len(cube)):
        if i == j:
            res = res + '-'
        else:
            res = res+cube[i]
    return res

def reverse_st(st):
    strl=list(st)
    strl.reverse()
    return strl_str(strl)

def reverse_sop(s):
    srev = []
    for j in range(len(s)):
        srev = srev + [reverse_st(s[j])]
    return srev
        

def str_strl(st):
    return list(st)

def strl_str(strl):
    st=''
    for j in range(len(strl)):
        st=st+strl[j]
    return st
        


def make_primes(x11,x0,rev=0):
    """expands cubes of x1 against offset x0"""
    offtt = tt(x0)
    x1 = remove_dup(x11)
    p=[]
    for j in range(len(x1)):
        pj=make_prime(x1[j],offtt,rev)
        p = p+[pj]
    return p

def make_prime(cube,offtt,rev=0):
    """ expands aa cube into a prime. off must be a tt"""
    res = str(cube)
    J = range(len(res))
    if rev:
        J.reverse()
    for j in J:
        if res[j] == '-':
            continue
        cj=expand(res,j)
        if check_off(cj,offtt):
            res = cj
    return res

def ired(p,ontt):
    """ makes sop p irredundant relative to onset truth table"""
    tvp = []
    tvp = sop_tv(p)
    rs = iredv(tvp,ontt)
    res = tv_sop(rs)
    return res
##    red = list(p)
##    for j in range(len(p)):
##        tj=tt([p[j]])&ontt# onset of cube j
##        tt
##        if tj&~tt(res) == m.const(0):
##            continue
##        else:
##            res=res+[p[j]]
##    return res

def tt_of_p(p):
    res = []
    for i in range(len(p)):
        res = res + [ttcube(p[i])]
    return res
                   

def two_level(on,off,rev=1):
    """ only used in espresso. Makes primes and removes duplicates and selects
    a subset in order of which cover the most remaining minterms of 'on' """
    time0=time.time()
    c1 =[]
    ttc1=m.const(0)
    ontt=t1=tt(on)
    p1=make_primes(on,off)
    if rev:
        p1=p1+make_primes(on,off,1)
    p1=remove_dup(p1)
    ttp1 = tt_of_p(p1) #vector of truth tables
    while True: # iteratively include the cube that covers the most minterms not yet covered 
        t1=ontt&~ttc1 # onset still to be covered
        if t1.count()==0:
            break
        j1,count1=max_count(ttp1,t1)
        c1 = c1 + [p1[j1]]
        ttc1 = ttc1 | ttp1[j1]
        ttc1 = ontt&ttc1
    c1=ired(c1,ttc1)
##    print 'cubes = %d, lits = %d'%(len(c1),lit(c1))
##    print 'time for two_level = ',time.time() - time0
    return c1


def reduce_sop(s,on):
    """reduces cube in s to a minimum cube containing onset minterms not in rest of cubes
    Replaces each cube with reduced cube. Done in the given order of cubes"""
    ontt = tt(on)
    N = len(s[0])
    stt = s_stt(s)
    J = range(len(s))
    J.reverse()
    pp=list(s)
    for j in J:
        ttj = stt[j]&ontt
        ttj = ttj & ~sttx(stt,j)
        stt[j]=ttj
        pp[j]=min_cube(ttj)
    return pp
        
 
def remove_dup(p):
    if len(p)<2:
        return p
    d = list(p)
    d.sort()
    res = []
    for j in range(len(d)-1):
        if not d[j] == d[j+1]:
            res = res + [d[j]]
    res = res + [d[len(d)-1]]
    return res

def shffle(x):
    J=range(len(x))
    res = [-1]*len(x)
    t=-2
    for j in J:
        t = (t+2)
        if t > len(J)-1:
            t=1
        res[t] = x[j]
    return res

def reexpand(c1,c0,on,off):
    tc1=tt(c1)
    tc0=tt(c0)
    ton=tt(on)
    toff=tt(off)
    d1=espresso(sop(tc1&ton),sop(toff&~(toff&tc1)))
    d0=espresso(sop(toff&tc0),on)
    return d1,d0

######### counting ###############
    
def max_count(tts,ontt):
    """ find the cube that covers the most minterms in ontt"""
    maxc = -1
    maxj = -1
    for j in range(len(tts)):
        ctt = tts[j]
##        ctt = tt([c])
        tc = ctt&ontt
        count = tc.count()
        if count > maxc:
            maxc = count
            maxj = j
    return maxj,maxc

def print_sizes(c1,c0):
##    print c0
    print 'c1: cubes, lit = ',len(c1),lit(c1)
    print 'c0: cubes, lit = ',len(c0),lit(c0)

def size_of(s):
    res = len(s),lit(s)
##    print 'cubes = %d, lits = %d'%res
    return res
                   
def lit(s):
    count=0
    for j in range(len(s)):
        count = count + lit_cube(s[j])
    return count

def lit_cube(c):
    count = 0
    for i in range(len(c)):
        if c[i] == '-':
            continue
        count = count + 1
    return count

def count_and_sop(sop):
    """ #cubes -1 + sum_i (lit(cub_i) - 1) =
    #cubes -1 - #cubes + lits(sop)"""
##    if sop == []:
##        return -2
    c = lit(sop) -1
    return c

def count_fact_sop(sopp):
##    print sopp
    if lit(sopp) == 0:
##        print -1
        return -1
    if len(sopp) <= 1:
        c = count_and_sop(sopp)
##        print c
        return c
    count2,count1,count0 = binate_count(sopp)
    jmax,count,sign  = get_max(count1,count0)
    if count == 1:
        c=count_and_sop(sopp)
##        print c
        return c
    else:
        lsop,rsop = fctr(sopp,jmax,sign)
##        print lsop,rsop
        assert len(lsop) > 1,sopp
        cL = count_fact_sop(lsop) +1
        cR = count_fact_sop(rsop)
        c=cR + cL +1
##        print c
        return c

def fact(sop):
    if len(sop) <= 1:
        return sop
    count2,count1,count0 = binate_count(sop)
    jmax,count,sign  = get_max(count1,count0)
    if count <= 1:
        return sop
    else:
        lsop,rsop = fctr(sop,jmax,sign)
##        print lsop,rsop
        cL = fact(lsop)
        if len(rsop) == 0:
            return [[jmax,sign],[cL,[]]]
        cR = fact(rsop)
        return [[jmax,sign],[cL,cR]]

def fctr(sop,j,sign):
    """ factors literal (j,sign) out of SOP. Returns two sop's, L is
    those with literal removed and R the remaining unchanged."""
    c = ['0','1']
    ph = c[sign]
    L=R=[]
    for i in range(len(sop)):
        si=sop[i]
        if si[j] == ph:
            sij = subst_string(si,j,'-')
            L=L + [sij]
        else:
            R=R + [si]
    return L,R

def subst_string(s,j,ch):
    """ substitutes string 'ch' for jth element in string  """
    res = ''
    ls = list(s)
    for i in range(len(s)):
        if i == j:
            res = res + ch
        else:
            res = res + ls[i]
    return res

def get_max(count1,count0):
    """ finds the index of the max number in two lists and
    which list contained the max  """
    max0_count=max1_count = -1
    J = range(len(count1))
    for j in J:
        if count1[j] > max1_count:
            max1_count = count1[j]
            j1max = j
        if count0[j] > max0_count:
            max0_count = count0[j]
            j0max = j
    if max1_count >= max0_count:
        return j1max,max1_count,1
    else:
        return j0max,max0_count,0

#######################
        
def choose_sign(ton,toff,pp1,cost1):
    """Choose which phase to implement. Return best sop, its cost and if complementwas chosen"""
##    pp1=espresso(on,off)
    pp0=espresso(sop(toff),sop(ton))
##    cost1 = count_and_sop(pp1)
    cost0 = count_fact_sop(pp0)
    if cost1 <= cost0:
        cost = cost1
        pp = pp1
        sign = '+'
    else:
        cost = cost0
        pp = pp0
        sign = '-'
##    print 'sign = ',sign
    return pp,cost,sign
                
######################## pretty printing a tree ###############

def ppt_all(t,c):
    for i in range(len(t)):
        print ' '
        print 'PO = %d, cost = %d'%(i,c[i])
        ppt(t[i])
    print 'cost = ',p_red(c)
    
def ppt(tree):
    """header fir pretty printing tree"""
    global tab
    tab = '   '
    pprint_tree('',tree)

def pprint_tree(spacer,tree):
    """ recursive subroutine for pretty printing tree"""
##    print 'tab = "%s"'%str(tab)
##    print 'spacer = "%s"'%str(spacer)
    if tree == []:
        print spacer+str(tree)
        return
    space = spacer+tab
    header = tree[0]
    if len(header)==3 and type(header[0]) == int: # a cofactoring
        print spacer+str(header)
        pprint_tree(space,tree[1])
        pprint_tree(space,tree[2])
    elif len(header)== 4: # an xor
        hd0 = header[0]
        if hd[0] < 0:
            header[0] = abs(hd0) - 1
            st_head = "-"+str(header)
        else:
            st_head = str(header)
        print spacer+st_head
        pprint_tree(space,tree[1])
    else:
        if header == '+' or header == '-': # a tree_sop
            print spacer+header
            s=tree[1] #take away tree_sop header
            pprint_tree(space,s)
            return
        s=tree # no tree header
        #we have either sop or fact_sop
        if s == []:
            print spacer+'[]'
##            print 'ss = ',s
            return
        if lit(s) == 0:
            print spacer,s[0]
            return
        if type(s[0][0]) == str: # a sop
            #factor it
            f = fact(s)
            pp_fact(spacer,f)
        else: # we have an error
            print 'Error ',
            print s
            return

def pp_fact(spacer,f,tabb='    '):
    global tab
    if f == []:
##        print 'f = empty'
        return
    if type(f[0]) == str:
        print_sop(spacer,f)
        return
##    print '***f = ',f
    tab = tabb
    space = spacer+tab
    if type(f[0][0]) == int: # first of pair is a literal
        print spacer,f[0]
        pp_fact(space,f[1][0],tab) # quotient
        pp_fact(spacer,f[1][1],tab) # remainder
        return
    elif type(f[0][0][0]) == str: # first of pair is an sop
        print_sop(spacer,f[0])
        if f[1] == []:
            return
        if type(f[1][0][0]) == str:
            print ''
            print_sop(spacer,f[1]) #second is a sop
            return
        else: # second is a fact
            pp_fact(spacer,f[1],tab)
            return
    else: # first is a factor 
        pp_fact(spacer,f[0],tab)
        #check second
        if f[1] == []:
            return
        if type(f[1][0]) == str:
            print_sop(spacer,f[1])
            return
        if f[1] == []:
            return
        pp_fact(spacer,f[1],tab)
        return
                
def print_sop(space,s):
    for i in range(len(s)):
        print space,s[i]
##################
            
def mux_init(on,off):
    """ initial call to create a cofactoring ttree with minimum cost"""
    ttime = time.time()
    pp = espresso(on,off)
    cost = count_fact_sop(pp)
    cost_init = cost
    #begin the recursion
    if cost > 0:
        tree_r,cost = cof_recur(tt(on),tt(off),pp,cost)
##        print ''
##        ppt(tree_r)
    else:
        tree_r = ['+',pp]
    print 'time = %0.2f, initial cost = %d, final cost = %d'%((time.time()-ttime),cost_init,cost)
##    print tree_r
##    print_tree(tree_r)
    return tree_r,cost_init,cost

def get_split_var(ton,toff):
    """ pick the variable and method for expansion with the least cost
    Currently only Shannon is done here"""
    global if_espresso
    if_espresso_old = if_espresso
    N=ton.m.N
##    print N
    cost_min = 100000
    if_espresso = 0
    for i in range(N):
##        print v_in(i,ton)
        if not v_in(i,ton): # i does not exist in ton
            continue
        cost1,cost0,leaf1,leaf0,method = mux_v(ton,toff,i)
        cost_add = cost_mux
        if not method == 'shannon':
            cost_add = cost_dav
##        print cost_add
        cost = cost0+cost1+cost_add
        if cost < cost_min:
            leaf1_min = leaf1
            leaf0_min = leaf0
            cost_min = cost
            cost0_min = cost0
            cost1_min = cost1
            imin=i
            method_min = method
    if if_espresso_old == 0:
        return imin,leaf1_min,leaf0_min,cost1_min,cost0_min,method_min
    else:
        if_espresso = 1
        cost1,cost0,leaf1,leaf0,method = mux_v(ton,toff,imin)
        return imin,leaf1,leaf0,cost1,cost0,method

def get_split_var2(ton,toff):
    """ pick the variable and method for expansion with the most binateness
    """
    global if_espresso
    N=ton.m.N
##    print N
    cost_min = 100000
    s_on = sop(ton)
    s_off = sop(toff)
    if_espresso_old = if_espresso
    if_espresso = 0
    s_epos = espresso(s_on,s_off)
    imin = get_most_binate_var(s_epos)
    if_espresso = if_espresso_old
    cost1,cost0,leaf1,leaf0,method = mux_v(ton,toff,imin)
    return imin,leaf1,leaf0,cost1,cost0,method
 

def binate_count(ss):
    n_v = len(ss[0])
    count1 = [0]*n_v
    count0 = [0]*n_v
    count2 = [0]*n_v
    for j in range(len(ss)):
        cubej = ss[j]
##        print cubej
        for i in range(n_v):
            cji = cubej[i]
            if cji == '-':
                count2[i] = count2[i] + 1
            elif cji == '1':
                count1[i] = count1[i] + 1
            else:
                count0[i] = count0[i] + 1
##        print count1,count0
    return count2,count1,count0

def get_most_binate_var(ss):
    if len(ss) < 2:
        return -1
    Jess,nJess = qessentials(ss)
    if len(nJess) < 2: 
        return -1
    ness = sublist(ss,nJess)
    count2,count1,count0=binate_count(ness)
    abmin=cmin=100000
    for j in range(len(count1)):
        cc = count0[j]+count1[j]+2*count2[j]
        if cc < cmin: # get ine with least total cubes
            jmin = j
            cmin = cc
            abmin = abs(count1[j]-count0[j])
        elif cc == cmin:
            if abs(count1[j]-count0[j]) < abmin: #break ties with more even split
                jmin = j
                abmin = abs(count1[j]-count0[j])
##        c2= count2[j]
##        ab = abs(count1[j]-count0[j])
##        if  c2 < cmin: # get min of count2
##            jmin=j
##            cmin = c2
##            abmin = ab 
##        elif c2 == cmin and ab < abmin: # break ties with ab
##            jmin=j
##            cmin = c2
##            abmin = ab
    assert jmin > -1, jmin
    return jmin                       
    
##def cof_recur(ton,toff,sop_in,cost):
##    """ cofactoring wrt a single variable has to beat incoming cost
##    a tree is either an sop or an expandion -  ite - [[v,method],tree1,tree2]
##    the input is the ISF (ton,toff) to be implemented.
##    Incoming cost is an upper bound for implementation.
##    This returns (sop_in, cost) if there is no expansion that can beat cost.
##    Otherwise, it returns expansion tree for the ISF.
##    (ton,toff) is the current ISF and sop_in is its SOP
##    """
####    print ''
####    print 'in: ',sop_in
####    if leaf == []:
####        print 'leaf is empty'
##    if lit(sop(ton))<=1:#we are at a leaf because ton is a single variable. don't do anything
####        print ''
####        print 'out: ',['+',sop_in]
##        return ['+',sop_in],cost
##    N=ton.m.N
##    ton_init = ton
##    sop_r,cost,sign =choose_sign(ton,toff,sop_in,cost)
##    assert ton==ton_init,'ton was switched internally'
##    if sign == '-':
##        ton,toff = toff,ton
####        eoffon= espresso(sop(ton),sop(toff))
####        if not eoffon == sop_r:
####            print eoffon,sop_r
####            assert False,'ERROR'
####    imin,leaf1,leaf0,cost1,cost0,method = get_split_var(ton,toff)
##    imin,leaf1,leaf0,cost1,cost0,method = get_split_var2(ton,toff)
##    # sign us '+' or '-'.  If '-' then ton and toff need to be switched
##    #method at this point is 'shannon'
##    cost_add = cost_mux
##    newcost1 = cost0+cost1+cost_add
####    print cost,newcost1,cost1,cost0
##    if newcost1 >= cost: # try a different split choice
##        imin_old,leaf1_old,leaf0_old,cost1_old,cost0_old,method_old = imin,list(leaf1),list(leaf0),cost1,cost0,method
##        imin,leaf1,leaf0,cost1,cost0,method = get_split_var(ton,toff)
##        newcost2 = cost0+cost1+cost_add
####        print cost,newcost2,cost1,cost0
##        if newcost2 >= cost: #try davio
##            return [sign,sop_r],cost
####            #go back to first set
####            if newcost1 < newcost2:
####                print 'switching back to first set'
####                imin,leaf1,leaf0,cost1,cost0,method = imin_old,leaf1_old,leaf0_old,cost1_old,cost0_old,method_old
########### Trmporarily disabling Davio ##########
######    or leaf1 == [] or leaf0 == []: #we are at a leaf. don't do anything
####            print 'Trying Davio'
####            leaf2,cost2 = try_davio(ton,toff,imin) #just trying last var chosen
####            print 'f2, cost2 = ',
####            print leaf2,cost2
####            newcost_dav = cost2+min(cost0,cost1)+cost_dav
####            print 'Davio would give newcost = %d'%newcost_dav
####            print cost,newcost_dav,cost2,cost1,cost0
####            if newcost_dav >= cost:
####                print 'out: ',[sign,sop_r]
####                print ''
####                return [sign,sop_r],cost
####            else:#davio wins. decide + or -
####                print 'Davio wins'
####                print 'ton = ',ton
####                print 'toff = ',toff
####                print 'leaf0 = ',leaf0
####                print 'leaf1 = ',leaf1
####                print 'leaf2 = ',leaf2 
####                cost_add = cost_dav
####                if cost0 <= cost1:
####                    method = '+davio'
####                    leaf1 = leaf0
######                    leaf0 = list(leaf2)
####                    cost1 = cost0
######                    cost0 = cost2
####                else:
####                    method = '-davio'
####                leaf0 = leaf2
####                cost0 = cost2
####    print 'splitting variable = %d, method = %s'%(imin,method)
##    #recur here since a variable exists, namely imin, whose two cofactors can be
##    #implemented as sop's plus a mux with less cost than the incoming 'cost'
####    print 'costs before: ',cost,cost1_min,cost0_min
##    if cost1 > 0: #a single literal cube has 0 cost
##        ton1=ton.cofactor(imin,1)
##        toff1=toff.cofactor(imin,1)
##        tree1,cost1 = cof_recur(ton1,toff1,leaf1,cost1)
####        print ""
####        print 'out: ',tree1
##    else:
##        tree1=['+',leaf1]
##    if cost0 > 0:
##        ton0=ton.cofactor(imin,0)
##        toff0=toff.cofactor(imin,0)
##        tree0,cost0 = cof_recur(ton0,toff0,leaf0,cost0)
####        print ''
####        print 'out: ',tree0
##    else:
##        tree0=['+',leaf0]
####    print 'initial cost = %d, final cofactor costs = %d,%d'%(cost,cost1,cost0)
##    newcost = cost0+cost1+cost_add
##    if not cost >= cost0+cost1+cost_add:
##        print 'counts not compatible: cost = %d, cofactors count = %d'%(cost,newcost)
####    print 'cof_recur returns: ',[sop_in1,sop_in0],cost0+cost1+cost_add
####    print 'out: ',[[imin,method,sign],tree1,tree0]
####    print ''
##    return [[imin,method,sign],tree1,tree0],cost0+cost1+cost_add

##def try_davio(ton,toff,v):
##    """ f,f0,f1,f2 """
##    f = [toff,ton]
##    f0 = [f[0].cofactor(v,0),f[1].cofactor(v,0)]
##    f1 = [f[0].cofactor(v,1),f[1].cofactor(v,1)]
##    f2 = ixor(f0,f1)
##    f2_sop = espresso(sop(f2[1]),sop(f2[0]))
##    cost = count_fact_sop(f2_sop)
##    return f2_sop,cost

##def mux_v(tton,ttoff,v):
##    """ try a cofactoring variable v and return its costs and leaves"""
##    tton1 = tton.cofactor(v,1)
##    ttoff1 = ttoff.cofactor(v,1)
##    leaf1 = espresso(sop(tton1),sop(ttoff1))
##    cost1=count_fact_sop(leaf1)
##    ################
##    tton0 = tton.cofactor(v,0)
##    ttoff0 =ttoff.cofactor(v,0)
##    leaf0 = espresso(sop(tton0),sop(ttoff0))
##    cost0=count_fact_sop(leaf0)
##    return cost1,cost0,leaf1,leaf0,'shannon'


def v_in(v,ttr):
    """ check if variable is in the support of truth table ttr """ 
    ttr1 = ttr.cofactor(v,1)
    ttr0 = ttr.cofactor(v,0)
    if ttr0 == ttr1:
        return False
    else:
        return True

def random_subset(lst,r):
    res = []
    for j in range(len(lst)):
        if random.random() < r:
            res=res +[lst[j]]
    return res

def if_lit(tr):
    if len(tr)< 2:
        return False
    return tr[1] in [0,1]



###################################################
""" sig methods, which are methods to combine  and create signals in a network
    A sig is a signal in a net"""
import pyzz 

##def start_network(n_in):
##    """starts a new netlist with n_in PIs"""
##    net = pyzz.netlist()
##    PIs = [net.add_PI() for _ in xrange(n_in)]
##    return net,PIs


def write_net_to_aigfile(net,aigfile):
    net.write_aiger(aigfile)

def tree2net(n_in,tree=[]):
    """ takes a single output tree and creates an equivalent network
    and writes it out as name.aig
    Returns new net with n_in PIs and a single PO """
    net = pyzz.netlist() #create a new network
    PIs = [net.add_PI() for _ in xrange(n_in)]
    sig=tree2sig(net,tree)
    net.add_PO(fanin=sig)
##    net.write_aiger('%s.aig'%name)
##    print 'network written as %s.aig'%name
    return net
    
                                      
def cube2sig(net,cube):
    """ create the sig for a cube in network net
    Inputs of cube assumed to be PIs of net """
    if ((not '0' in cube) and (not '1' in cube)):
        return net.get_True()
    PIs = PIsOf(net)
    conj = []
    for j in range(len(cube)):
        if cube[j] == '-':
            continue
        elif cube[j] == '1':
            conj = conj + [PIs[j]]
        else:
            conj = conj + [~PIs[j]]
    sig = pyzz.conjunction(net,conj)
    return sig

def sop2sig(net,sop):
##    PIs = PIsOf(net)
    if len(sop) == 0:
        return ~net.get_True() # i.e. False
    disj = []
    for j in range(len(sop)):
        disj = disj + [cube2sig(net,sop[j])]
    sig = pyzz.disjunction(net,disj)
    return sig

def tree2sig(net,tree):
    """ creates a sig from a tree. A tree is either a 3-tuple or a sop"""
##    print 'length of tree = ',len(tree)
    if tree == []:
        return ~net.get_True()
    sign = tree[0]
    if type(tree[0]) == str: # tree is a sop
        sig = sop2sig(net,tree[1])
        if tree[0] == '-':
            sig = ~sig
        return sig                    
    PIs=PIsOf(net)
    assert len(tree[0]) > 2, tree[0]
    if len(tree) == 2: #an XOR
##        print tree[0]
        assert tree[0][1] == 'xor', tree[0][1]
        variable = tree[0][0]
        xsign = tree[0][2]
        sign = tree[0][3]
        ph = 1
        if variable < 0:
            ph = 0
            variable = -(variable+1) # -1->0,-2 -> 1
        variable= PIs[variable]
        if ph == 0:
            variable = ~variable
        N1 = tree2sig(net,tree[1])
        sig = variable ^ N1 # xor with the literal
        if xsign == '-': #add an invertor
            sig = ~sig
        if sign == '-':
            sig = ~sig
        return sig
    variable = PIs[tree[0][0]] #splitting variable
    method = tree[0][1]
    sign = tree[0][2] # '-' means complement was implemented
    assert len(tree) == 3, tree
    N1 = tree2sig(net,tree[1])
    N2 = tree2sig(net,tree[2])
    if method == 'shannon': #N1 = f_1, N2 = f_0
        sig = variable.ite(N1,N2)
        if sign == '-':
            sig = ~sig
        return sig
    elif method == '+davio': #N1 = f_0, N2 = f_2
        return N1^(variable&N2)
    elif method == '-davio': #N1 = f_1, N2 = f_2
        return N1^(N2&~variable)
    else:
        assert False, 'ERROR: Not known method'
    
def PIsOf(net):
    return [x for x in net.get_PIs()]

#########################
#methods for verifying result

"""combine_cones, creates a new network N from networks N1 and N2 and creates
translators from names in N1 to names in N and similarly for N2. """


def list_po_sizes():
    abc('&get')
    for j in range(n_pos()):
        abc('&put')
        abc('cone -O %d'%j)
        print '%d: '%j,
        ps()

def combine_nets(nets):
    """ nets is a list of networks"""
    N = combine_nets(nets[0],nets[1])
    for i in range(len(nets)-2):
        N = combine_two_nets(N,net[i+2])
    return N

def combine_two_nets(N_1,N_2):
    """ combines two networks and returns the new network and its POs
    For the moment each net can have only a single PO """
    if N_1 == []:
        return N_2
    if N_2 == 0:
        return N_1
    N, (xlat_1, xlat_2) = pyzz.combine_cones(N_1, N_2)
    POs_N1 = list(N_1.get_POs())
##    POs = []
    for j in range(len(POs_N1)):
        PO_fanin = xlat_1[ POs_N1[j][0] ] # The last [0] gets the fanin of the PO
##        POs = POs + [N.add_PO(fanin=PO_fanin)]
        N.add_PO(fanin=PO_fanin)
    POs_N2 = list(N_2.get_POs())
    for j in range(len(POs_N2)):
        PO_fanin = xlat_2[ POs_N2[j][0] ] # The last [0] gets the fanin of the PO
##        POs = POs + [N.add_PO(fanin=PO_fanin)]
        N.add_PO(fanin=PO_fanin)
    return N


################# manipulating ISFs ###############
""" an ISF is and interval, [on,off] where each is a truthtable."""
def iand(f,g):
    """ an ISF is [offset,onset]"""
    return [(f[0]&g[0]),(f[0]&~g[1])| (~f[1]&g[0])|(~f[1]&~g[1])]

def ior(f,g):
    """ same as inot(iand(inot(f),inot(g)))"""
##    res = inot(iand(inot(f),inot(g)))
    res = [(f[0]|g[0]),(~f[1]&~g[1])]
    return res

def inot(f):
    return [~f[1],~f[0]]

def ixor(f,g):
    """ f and g are ISPs given as [on,off["""
##    fb = inot(f)
##    gb = inot(g)
##    y1 = iand(fb,g)
##    y2 = iand(f,gb)
##    return ior(y1,y2)
##    res =ior(iand(inot(f),g),iand(f,inot(g)))
##    res = [(f[0]&~g[1])|(~f[1]&g[0]),(f[0]&g[0])|(~f[1]&~g[1])]
    res = [(f[0]&g[1])|(f[1]&g[0]),(f[0]&g[0])|(f[1]&g[1])]

    return res

def get_xor_var(tton,ttoff):
    xor_cost = 2
    m = tton.m
    N = m.N
##    tvon = tt_tv(tton)
##    tvoff = tt_tv(ttoff)
##    s1 = tv_sop(tvespresso(tvon,tvoff))
    s1=bbop(tton,ttoff)
    c1 = count_fact_sop(s1)
    c_min = c1
    i_min = -1
    ph_min = 1
    s_min=s1
    sign = '+'
##    s0 = tv_sop(tvespresso(tvoff,tvon))
    s0=bbop(ttoff,tton)
    c0 = count_fact_sop(s0)
    if c0<c_min:
        c_min = c0
        i_min = -1
        ph_min = 0
        s_min=s0
        tton,ttoff = ttoff,tton
        sign = '-'
    c_min_init =c_min
##    print 'none: + = %d, - = %d'%(c1,c0)
    for i in range(N):
        r1,r0 = var_xor(i,1,tton,ttoff) # results are tt
##        s = tv_sop(tt_tv(r1),tt_tv(r0)))
        s = bbop(r1,r0)
        c1 = count_fact_sop(s)+xor_cost
        if c1<c_min:
            c_min = c1
            i_min = i
            ph_min = 1
            s_min=s
##            r1_min = r1
##            r0_min = r0
##        r1,r0 = var_xor(i,0,tton,ttoff)
##        s = tv_sop(tvespresso(tt_tv(r1),tt_tv(r0)))
        s = bbop(r0,r1)
        c0 = count_fact_sop(s)+xor_cost
        if c0<c_min:
            c_min = c0
            i_min = i
            ph_min = 0
            s_min = s
##            r1_min = r1
##            r0_min = r0
##        print 'var %d : + = %d, - = %d'%(i,c1,c0)
    ph = ['-','+'][ph_min]
    if i_min > -1: #found a good xor variable
        r1,r0 = var_xor(i_min,ph_min,tton,ttoff)
##        tvon = tt_tv(r1)
##        tvoff = tt_tv(r0)
        s_esp = tvespresso(r1,r0,0,ifesp=if_espresso)
        c_esp = count_fact_sop(s_esp) + xor_cost
##        print 'espresso based xor cost = %d'%c_esp
        if c_esp < c_min:
            c_min = c_esp
            s_min = s_esp
        print 'xor cost = %d'%c_min
        return c_min,i_min,ph_min,s_min,r1,r0,sign
    else:
        return 0,i_min,0,0,0,0,0
                       

def var_xor(v,ph,on,off):
    m=on.m
    nph = 0
    if ph == 0:
        nph = 1
    new_on = m.var(v,ph)&off | m.var(v,nph)&on
    new_off = m.var(v,ph)&on | m.var(v,nph)&off
    return new_on,new_off

##def icofactor(f,x):
##    f_x1 = [f[0].cofactor(x,1),f[1].cofactor(x,1)]
##    f_x0 = [f[0].cofactor(x,0),f[1].cofactor(x,0)]
##    return [f_x0,f_x1]
##        
##
##def ipdavio(x,f):
##    cof = icofactor(f,x)
##    f0 = cof[0]
##    f1 = cof[1]
##    f2 = ixor(f0,f1)
##    res = ixor(f0,x&f2)
##    return resultF
##


##def build_miters(N1, N2):
##    """builds translators from names in N1 to names in N and similarly
##    similarly for N2. Then XORs corresponding POs"""
##    N, (xlat1, xlat2) = pyzz.combine_cones(N1, N2)
##    N1_pos = [ xlat1[po[0]] for po in N1.get_POs() ]
##    N2_pos = [ xlat2[po[0]] for po in N2.get_POs() ]
##    return N, [ f1^f2 for f1, f2 in zip(N1_pos, N2_pos) ]


##def build_check_netlist(N_synthesized, N_onoff):
##    """ add two POs, that if UNSAT states that onset does not intersect ~f and
##    offset does not inteersect f
##    """
##    N, f, onset, offset = pre_check(N_synthesized, N_onoff)
##    N.add_PO( fanin=(onset&~f) ) #first PO
##    N.add_PO( fanin=(offset&f) ) #second PO
##    return N


##def get_POs(xlat,net):
##    net_pos = list(net.get_POs())
##    return xlat[net_pos[0][0]]
##

##def print_tree(tr):
##    """ prints a tree by enumerating a lits of paths in depth-first order"""
##    if if_lit(tr) or len(tr) == 0:
##        #tr is a lit, don't print
##        return
##    elif if_lit(tr[0]): # at a leaf so print
##        print tr
##        return
##    else:
##        print_tree(tr[0])
##        print_tree(tr[1])

    
##def mux_var(on,off,v):
##    N=len(v)
##    res = [-1]*(2**N)
##    J = range(2**N)
##    for j in J:
##        ph=d2b(j,len(v))
##        con,coff = cofactors(on,off,v,ph)
####        print lit(con),lit(coff)
####        print con,coff
##        if lit(con)==0:
##            res[j]=[0]
##        elif lit(coff)==0:
##            res[j]=[1]
##        else:
##            res[j]=espresso(con,coff)
####    print 'and count = ',count_and(res)
##    return res
       
##def cof_pairs(on,off):
##    N = len(on[0])
##    cmin=1000000
##    imin = -1
##    for i in range(N):
##        pp = mux_var(on,off,[i])
##        count = count_and(pp)
##        if count < cmin:
##            cmin = count
##            ppmin = pp
##            imin=i
##            cof=[imin]
##    for j in range(N):
##        if imin == j:
##            continue
##        pp = mux_var(on,off,[imin,j])
##        count = count_and(pp)
##        if count < cmin:
##            cmin = count
##            ppmin = pp
##            cof=[imin,j]
##    return cof,ppmin
##    
            
        
##def log2(ss):
##    assert ss <= 2**5, 'integer exceeds limit'
##    if ss<=1:
##        return 0
##    elif ss<=2:
##        return 1
##    elif xx<= 4:
##        return 2
##    elif ss<= 8:
##        return 3
##    elif xx <= 16:
##        return 4
##    return 5


##def ite2sig(net,ite):
##    PIs = PIsOf(net)
##    control = PIs[0]
##    t = tree2sig(ite[1])
##    e = tree2sig(ite[2])
##    sig = control.ite(t,e)
##    return sig

##def tree2sig(net,tree):
##    """ creates an sig from a tree. A tree is either a 3-tuple or a sop"""
##    if tree == []:
##        return ~net.get_True()
##    if type(tree[0]) == str: # tree is a sop
##        return sop2sig(net,tree)
##    else:
##        PIs = PIsOf(net)
##        control = PIs[tree[0]]
##        t = tree2sig(net,tree[1])
##        e = tree2sig(net,tree[2])
##        sig = control.ite(t,e)
##        return sig

##def mux_v2(tton,ttoff,v):
##    """ try a cofactoring variable v and return its costs and leaves
##    It chooses the best method of [shannon,+davio or -davio] for expansion """
##    on_1=ton1 = tton.cofactor(v,1)
##    off_1=toff1 = ttoff.cofactor(v,1)
##    leaf1 = espresso(sop(ton1),sop(toff1)) #first espresso for f_1
##    cost1=count_and_sop(leaf1)
##    ################
##    on_0=ton0 = tton.cofactor(v,0)
##    off_0=toff0 =ttoff.cofactor(v,0)
##    leaf0 = espresso(sop(ton0),sop(toff0)) #second espresso for f_0
##    cost0=count_and_sop(leaf0)
##    ################ creating f_1 XOR f_0
####    toff2 = (ton1 | toff0)&(toff1 | ton0)
####    #need to compute on and off for
####    #(f2_on,f2_off) = (on_1,on_0) XOR (off_1,off_0)
####    off2 = toff2 = (off_0 & ~on_1)|((~on_0) & off_1)
####    on2 = ton2 = ((~on_0) & on_1) | (on_0 & ~on_1)
####    ##    print sop(ton2),sop(toff2)
####    leaf2 = espresso(sop(ton2),sop(toff2)) #third espresso for f_2
####    cost2 = count_and_sop(leaf2)
####    ##### temp to disable davio
##    cost2 = 100000
##    ######
##    ################
##    ##    print cost0,leaf0,cost1,leaf1,cost2,leaf2
##    cost10 = cost0 + cost1
##    cost12 = cost1 + cost2
##    cost02 = cost0 + cost2
##    if cost10 < cost12:
##        if cost10 < cost02: #shannon
####            print [cost1,cost0,leaf1,leaf0,'shannon']
##            return cost1,cost0,leaf1,leaf0,'shannon'
##        elif cost02 < cost12: # poaitive davio
####            print [cost0,cost2,leaf0,leaf2,'+davio']
##            return cost0,cost2,leaf0,leaf2,'+davio'
##        else: # negative davio
####            print [cost1,cost2,leaf1,leaf2,'-davio']
##            return cost1,cost2,leaf1,leaf2,'-davio'
##    elif cost12 < cost02:
####        print [cost1,cost2,leaf1,leaf2,'-davio']
##        return cost1,cost2,leaf1,leaf2,'-davio'
##    else:
####        print [cost0,cost2,leaf0,leaf2,'+davio']
##        return cost0,cost2,leaf0,leaf2,'+davio'

##def count_and(ss):
##    res = 3*((2*len(ss))-1) # 3 is the assumed cost of a mux
##    for j in range(len(ss)): # for each cofactor
##        cj=0
##        ssj=ss[j]
##        if ssj == [1] or ssj == [0]:
##            continue
##        cj=cj+len(ssj)-1 # number of or's
##        for i in range(len(ssj)):
##            ssji=ssj[i] #ith cube if cofactor
##            cj = cj+(lit(ssji)-1) # number of ands to implement a cube
##        res = res+cj
##    return res

##def reduce_primes(p,on):
##    res = []
##    on_tt = tt(on)
##    pp=list(p)
##    J = range(len(p))
##    J.reverse()
##    for j in J:
##        c=pp[j]
##        cr = max_reduce(c,pp[:j]+pp[j+1:],on_tt)
##        pp[j] = cr
##    return pp
##
##def max_reduce(c,pr,ontt):
##    """ maximally reduce cube c against primes pr where cube c is deleted. ontt is a tt of onset"""
##    cv = str2v(c)
##    ttpr = tt(pr)
##    for j in range(len(cv)):
##        if not cv[j] == 2:
##            continue
##        cv[j]=1
##        cs=v2str(cv)
##        ttcs = tt([cs])
##        if ((ttcs|ttpr)&ontt) == ontt:
####        if covers([cs]+pr,ontt):
##            continue
##        cv[j]=0
##        cs=v2str(cv)
##        ttcs=tt([cs])
####        if covers([cs]+pr,ontt):
##        if ((ttcs|ttpr)&ontt) == ontt:
##            continue
##        else:
##            cv[j]=2
##    return v2str(cv)
    

##def cofactors(tton,ttoff,v,ph):
##    ttonv=tton
##    ttoffv=ttoffi
##    for i in range(len(v)):
##        ttonv=ttonv.cofactor(v[i],ph[i])
##        ttoffv=ttoffv.cofactor(v[i],ph[i])
##    return ttonv,ttoffv


##def three_level(on,off,ifc0=1,rev=0):
##    """ construct a 3 level network by assigning cubes covering x1 to the left
##    and assigning cubes covering x0 to the right. Each set of cubes is ored and
##    the right result is inverted. These are then anded to form the output. """
##    time0=time.time()
##    c1 =c0=[]
##    ttc1=ttc0=m.const(0)
##    s1=list(on)
##    ontt=t1=tt(s1)
##    s0=list(off)
##    offtt=t0=tt(s0)
##    rat0=-1
##    last= first = 1
##    p0=make_primes(s0,on)
##    if rev:
##        p0=p0+make_primes(s0,on,1)
##    p0=remove_dup(p0)
##    p0=ired(p0,tt(off))
##    while True:
##        if last == 1:
##            t1=ontt&~ttc1 # onset still to be covered
##            if t1.count()==0:
##                break
##            s1=sop(t1)
##        if last == 0 or first:
##            t0=offtt&~ttc0 # offset still to be covered
##            if t0.count()==0:
##                break
##            s0=sop(t0)    
##        if last == 1:
##            p1=make_primes(s1,s0)
##            if rev:
##                p1=p1+make_primes(s1,s0,1)
##            p1=remove_dup(p1)
####        if last == 0 or first:
####            p0=make_primes(s0,on)
####            if rev:
####                p0=p0+make_primes(s0,on,1)
####            p0=remove_dup(p0)
##        if last == 1:
##            j1,count1=max_count(p1,t1)
####        print 'count1 = ',count1
##        if last == 0 or first:
##            j0,count0=max_count(p0,t0)
####        print 'count0 = ',count0
##        if last == 1:
##            rat1=float(count1)/float(t1.count())
##        if last == 0 or first:
##            rat0=float(count0)/float(t0.count())
####        if count1 >= count0 or not ifc0:
##        if rat1>= rat0 or not ifc0:
##            last = 1
##            c1 = c1 + [p1[j1]]
####            c1 = make_primes(sop(tt(c1)&ontt),s0)
##            ttc1 = ontt&tt(c1)
##        else:
##            last = 0
##            c0 = c0 + [p0[j0]]
####            c0 = make_primes(sop(tt(c0)&offtt),on) #do not let offset encroach on onset
##            ttc0 = offtt&tt(c0)
##        first = 0
####        ttc1off = tt(c1)&offtt
####        assert ttc1off&ttc0 == ttc1off,'off minterm in c1 not in c0'
####    return ired(c1,ttc1),ired(c0,ttc0)
####    print c0,c1
##    print_sizes(c1,c0)
##    c1=ired(c1,ttc1)
##    print_sizes(c1,c0)
##    print check(c1,c0,on,off)
####    c0=ired(c0,ttc0)
##    c0=ired(c0,tt(c1)&tt(off))
##    print_sizes(c1,c0)
##    print check(c1,c0,on,off)
##    d1=esp(c1,c0,on,off)
##    print_sizes(d1,c0)
##    print check(d1,c0,on,off)
##    d1off = tt(d1)&tt(off)
##    d0=ired(c0,d1off)
##    print_sizes(d1,d0)
##    print check(d1,d0,on,off)
##    print 'time for three_level = ',time.time()-time0
##    return d1,d0


##def cofactors(on,off,v,ph):
##    tton=tt(on)
##    ttoff=tt(off)
##    for j in range(len(v)):
##        tton=tton.cofactor(v[j],ph[j])
##        ttoff=ttoff.cofactor(v[j],ph[j])
##    return sop(tton),sop(ttoff)
##


##def contained_in(x,y):
##    """x and y are sops"""
##    tx=tt(x)
##    ty=tt(y)
##    txy=tx&ty
##    if txy== tx:
##        return True
##    else:
##        return False
##    
##def contain(p,off):
##    """creates a 01 vector indicating if cube j of offset is covered by the other primes"""
##    res=[0]*len(p)
##    for j in range(len(p)):
##        c = off[j]
##        cm = p[:j]+p[j+1:]
##        if contained_in(c,cm):
##            res[j]=1
##    return res

##def esp(c1,c0,on,off):
##    d1=ired(make_primes(c1,sop(tt(off)&~tt(c0))),tt(on))
##    offset = tt(off) & ~tt(c0)
##    onset = tt(on) & tt(c1)
##    p1=make_primes(sop(onset),sop(offset))
##    d1 = ired(p1,onset)
##    return d1


