from pyabc import *
import pyabc_split
import redirect
import sys
import os
import time
import math
import main
import filecmp
import regression

"""UTILITIES"""

global G_C,G_T,latches_before_abs,latches_before_pba,n_pos_before,x_factor,methods,last_winner
global last_cex,JV,JP, cex_list,max_bmc, last_cx, pord_on, trim_allowed, temp_dec, abs_ratio, ifbip
global if_no_bip, gabs, gla, sec_options,last_gasp_time, abs_ref_time, bmcs1, total_spec_refine_time
global last_gap


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
cex_list = []
TERM = 'USL'
last_gasp_time = 10000
last_gasp_time = 500
last_gasp_time = 2001 #set to conform to hwmcc12
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
abs_time = 100
abs_ref_time = 50 #number of sec. allowed for abstraction refinement.
total_spec_refine_time = 150
ifbip = 0 # sets the abtraction method to vta or gla, If = 1 then uses ,abs
if_no_bip = False #True sets it up so it can't use bip and reachx commands.
abs_ratio = .5 #this controls when abstraction is too big and gives up
#####################################


def initialize():
    global xfi, max_bmc, last_time,j_last, seed, init_simp, K_backup, last_verify_time
    global init_time, last_cex, last_winner, trim_allowed, t_init, sec_options, sec_sw
    global n_pos_before, n_pos_proved, last_cx, pord_on, temp_dec, abs_time, gabs, gla,m_trace
    global smp_trace,hist,init_initial_f_name, skip_spec, t_iter_start,last_simp, final_all, scorr_T_done
    global last_gap
    xfi = x_factor = 1  #set this to higher for larger problems or if you want to try harder during abstraction
    max_bmc = -1
    last_time = 0
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
    if n_ands() > 100000:
        abs_time = 300
    else:
        abs_time = 150 #timeout for abstraction
    abs_ref_time = 50 #number of sec. allowed for abstraction refinement.
    total_spec_refine_time = 150 # timeout for speculation refinement
    abs_ratio = .5 
    hist = []
    skip_spec = False
    t_iter_start = 0
    inf = 10000000
    last_simp = [inf,inf,inf,inf]
    final_all = 1
    scorr_T_done = 0
    last_gap = 0
##    abs_time = 100
##    gabs = False
##    abs_time = 500
##    gabs = True

def abc(cmd):
    abc_redirect_all(cmd)

def abc_redirect( cmd, dst = redirect.null_file, src = sys.stdout ):
    """This is our main way of calling an ABC function. Redirect, means that we suppress any output from ABC"""
    with redirect.redirect( dst, src ):
        return run_command( cmd )

def abc_redirect_all( cmd ):
    """This is our main way of calling an ABC function. Redirect, means that we suppress any output from ABC, including error printouts"""
    with redirect.redirect( redirect.null_file, sys.stdout ):
        with redirect.redirect( redirect.null_file, sys.stderr ):
            return run_command( cmd )

## Similar engines below listed in the order of priority, high to low.
allreachs = [8,12,13,24,25]
allreachs = [24]
reachs = [24]
##allpdrs = [14,7,34,19,0]
allpdrs = [34,7,14,19,0]
allpdrs2 = [34,7,14,19,0]
pdrs = [34,7,14,0]
allbmcs = [9,30,2,31]
exbmcs = [2,9,31]
bmcs = [9,30]
bmcs1 = [9]
allintrps = [23,1,22]
bestintrps = [23]
##intrps = [23,1]
intrps = [23,1] #putting ,imc-sofa first for now to test
allsims = [26,3]
sims = [26] 
allslps = [18]
slps = [18]
imc1 = [1]
pre = [5]
combs = [36,37]

JVprove = [7,23,24]
JV = pdrs+intrps+bmcs+sims #sets what is run in parallel '17. verify' above
JP = JV + [27] # sets what is run in  '21. run_parallel' above 27 simplify should be last because it can't time out.


def set_engines(N=0):
    """
    Called only when read_file is called.
    Sets the MC engines that are used in verification according to
    if there are 4 or 8 processors. if if_no_bip = 1, we will not use any bip and reachx engines
    """
    global reachs,pdrs,sims,intrps,bmcs,n_proc,abs_ratio,ifbip,bmcs1, if_no_bip, allpdrs,allbmcs
    bmcs1 = [9] #BMC3
##    #for HWMCC we want to set N = 8
##    N = 8
    if N == 0:
        N = n_proc = 1+os.sysconf(os.sysconf_names["SC_NPROCESSORS_ONLN"])
##        N = n_proc = 8 ### simulate 4 processors for HWMCC - turn this off a hwmcc.
    else:
        n_proc = N
##    print 'n_proc = %d'%n_proc
    #strategy is to use 2x number of processors
    N = n_proc = -1+2*N
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
        bmcs = [30]
        intrps = []
        sims = []
        slps = [18]
    elif N <= 4:
        reachs = [24] #reachy
        pdrs = [7,34] #prdm pdr_abstract
        if if_no_bip:
            allpdrs = pdrs = [7,19] #pdrm pdrmm
        bmcs = [9,30] #bmc3 bmc3 -S
        intrps = [23] #unterp_m
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

    elif N <= 8: #used for HWMCC
        reachs = [24] #REACHY
        allpdrs = pdrs = [7,34,14] #PDRM pdr_abstract PDR_seed
        intrps = [23,1] #Interp_m
        allbmcs = bmcs = [9,30,31] #BMC3 bmc3 -S 
        if if_no_bip:
            allpdrs = pdrs = [7,19] #PDRM PDRMm
            intrps = allintrps = [23] #Interp_m
            bmcs = allbmcs = [2]
        sims = [26] #Rarity_Sim
        slps = [18] #sleep
    else:
        reachs = [24] #REACHY REACHX
        pdrs = [7,34,14,19,0] #PDRM pdr_abstract PDR_seed PDRMm PDR
        intrps = [23,1] #Interp_m INTERPOLATION
        bmcs = allbmcs
        if if_no_bip:
            allpdrs = pdrs = [7,19] #PDRM PDRMm
            intrps = allintrps = [23] #Interp_m
            reachs = [24] #REACHY
            bmcs = [9,30] #BMC3 bmc3 -S 
        sims = [26] #Rarity_Sim
        slps = [18] #sleep
        
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

def read_file():
    global win_list, init_simp, po_map
    read_file_quiet()

def ps():
    print_circuit_stats()

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
    b = max_bmc
    c = cex_frame()
    if b>= 0:
        if c>=0:
            print 'PIs=%d,POs=%d,FF=%d,%s=%d,max depth=%d,CEX depth=%d'%(i,o,l,s,a,b,c)
        elif is_unsat():
            print 'PIs=%d,POs=%d,FF=%d,%s=%d,max depth = infinity'%(i,o,l,s,a)
        else:
            print 'PIs=%d,POs=%d,FF=%d,%s=%d,max depth=%d'%(i,o,l,s,a,b)            
    else:
        if c>=0:
            print 'PIs=%d,POs=%d,FF=%d,%s=%d,CEX depth=%d'%(i,o,l,s,a,c)
        else:
            print 'PIs=%d,POs=%d,FF=%d,%s=%d'%(i,o,l,s,a)


def rf():
##    set_engines(4) #temporary
    read_file()
    abc('zero')


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
    if s[-4:] == '.aig':
##        run_command('&r %s;&put'%s) #warning: changes names to generic ones.
        run_command('r %s'%s)
        run_command('zero')
    else: #this is a blif file
        run_command('r %s'%s)
        abc('st;&get;&put') #changes names to generic ones for doing cec later.
        run_command('zero;w %s.aig'%f_name)
    set_globals()
    hist = []
    init_initial_f_name = initial_f_name = f_name
    run_command('fold') #only does something if some of the outputs are constraints.
    aigs_pp('push','initial')
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
##    print hist
    if op == 'push':
        hist.append(typ)
        abc('w %s_aigs_%d.aig'%(init_initial_f_name,len(hist)))
    if op == 'pop':
        abc('cexsave') #protect current cex from a read
        abc('r %s_aigs_%d.aig'%(init_initial_f_name,len(hist)))
        abc('cexload')
        typ = hist.pop()
##    print hist
    return typ


"""SYNTHESIS"""

def get_lib():
    run_command('read_genlib vsclib013.genlib')

def map_a_iter():
    run_command('map -a;ps')
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
    kmax=min(k+2,15)
    abc('st; if  -g -C %d -K %d -F 2;ps'%(10,kmax)) #balance
    print nl(),
    for i in range(1):
        abc('st;dch; if -C %d -K %d;ps'%(10,kmax))
        print nl(),

def speedup(k=4):
    run_command('speedup;if -K %d'%k)
    print nl()

def speed_tradeoff(k=4):
    print nl(),
    best = n_nodes()
    abc('write_blif %s_bestsp.blif'%f_name)
    L_init = n_levels()
    while True:
        L_old = n_levels()
        L = L_old -1
        abc('speedup;if -D %d -F 2 -K %d -C 11'%(L,k))
        if n_nodes() < best:
            best = n_nodes()
            abc('write_blif %s_bestsp.blif'%f_name)
        if n_levels() == L_old:
            break
        print nl(),
        continue
    abc('r %s_bestsp.blif'%f_name)
    return

def area_tradeoff(k=4):
    print nl(),
    best = n_nodes()
    abc('write_blif %s_bestsp.blif'%f_name)
    L_init = n_levels()
    while True:
        L_old = n_levels()
        L = L_old +1
        n_nodes_old = n_nodes()
        abc('speedup;if -a -D %d -F 2 -K %d -C 11'%(L,k))
        if n_nodes() < best:
            best = n_nodes()
            abc('write_blif %s_bestsp.blif'%f_name)
##        if n_levels() == L_old:
        if n_nodes == n_nodes_old:
            break
        print nl(),
        continue
    abc('r %s_bestar.blif'%f_name)
    return


def map_lut_dch(k=4):
    '''minimizes area '''
    abc('st; dch; if -a  -F 2 -K %d -C 11; mfs2 -a -L 50 ; lutpack -L 50'%k)
    
def map_lut_dch_iter(k=8):
##    print 'entering map_lut_dch_iter with k = %d'%k
    best = n_nodes()
    abc('write_blif %s_best.blif'%f_name)
    n=0
    while True:
        map_lut_dch(k)
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


def map_lut(k=4):
    '''minimizes edge count'''
    for i in range(5):
        abc('st; if -e -K %d; ps;  mfs ;ps; lutpack -L 50; ps'%(k))
        print nl(),

def nl():
    return [n_nodes(),n_levels()]

def dc2_iter(th=.999):
    abc('st')
    tm = time.time()
    while True:
        na=n_ands()
        abc('dc2')
        print n_ands(),
##        print nl(),
        if n_ands() > th*na:
            break
    print 't = %.2f, '%(time.time()-tm),
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
    run_command('eliminate -N %d;fx'%n)
    run_command('if -K %d'%(n/2))
    run_command('fx')

def perturb_f(k=4):
    abc('st;dch;if -g -K %d'%(k))
##    snap()
    abc('speedup;if -K %d -C 10'%(k))
    jog(5*k)

def perturb(k=4):
    abc('st;dch;if -g -K %d'%k)
##    snap()
    abc('speedup;if -K %d -C 10'%(k))
    
def preprocess(k=4):
    n_initial = n_nodes()
    abc('write_blif %s_temp_initial.blif'%f_name)
##    abc('st;dc2')
    abc('w %s_temp_initial.aig'%f_name)
    ni = n_pis() + n_latches()
    res = 1
    if ni >= 101:
        abc('st;if -a -F 2 -K %d'%k)
        return res
##    dc2_iter()
    abc('st;if -a -K %d'%k) # to get plain direct map
    if n_nodes() > n_initial:
        abc('r %s_temp_initial.blif'%f_name)
        res = 1
    #plain
    n_plain = n_nodes()
##    print nl()
    abc('write_blif %s_temp_plain.blif'%f_name)
    #clp
    abc('st;clp; if -a -K %d'%k)
##    print nl()
    abc('write_blif %s_temp_clp.blif'%f_name)
    n_clp = n_nodes()
    #clp_lutmin
    abc('r %s_temp_initial.blif'%f_name)
    abc('st;clp;lutmin -K %d;'%k)
    abc('write_blif %s_temp_clp_lut.blif'%f_name)
    n_clp_lut = n_nodes()
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
    return res

def snap():
##    abc('fraig;fraig_store')
    abc('fraig_store')

def snap_bestk(k):
    abc('write_blif %s_temp.blif'%f_name)
    unsave_bestk(k)
    snap()
    abc('r %s_temp.blif'%f_name)


def save_bestk(b,k):
##    if os.access('%s_best%d.blif'%(f_name,k),os.R_OK):
##        res = get_bestk(k)
##    else:
    """ saves the best, returns bestk and if not best, leaves blif unchanged""" 
    res = b
    if n_nodes() < res:
        res = n_nodes()
        abc('write_blif %s_best%d.blif'%(f_name,k))
        print 'best%d = %d'%(k,res)
    return res
##    unsave_bestk(k)

def unsave_bestk(k):
    abc('r %s_best%d.blif'%(f_name,k))
        
def unsnap(k=4):
##    snap()
    abc('fraig_restore')
    map_lut_dch(k)
##    abc('fraig_restore;if -a -F 2 -C 11 -K %d'%k)

def map_until_conv(k=4):
    kk = 2*k
    # make sure that no residual results are left over.
    if os.access('%s_best%d.blif'%(f_name,k),os.R_OK):
        os.remove('%s_best%d.blif'%(f_name,k))
    if os.access('%s_best%d.blif'%(f_name,kk),os.R_OK):
        os.remove('%s_best%d.blif'%(f_name,kk))
    tt = time.time()
    #get initial map and save
    map_lut_dch(k)
    bestk = save_bestk(100000,k)
    print nl()
##    snap()
    res = preprocess() #get best of initial, clp, and lutmin versions
    print nl()
    map_lut_dch_iter(kk) #initialize with mapping with 2k input LUTs
    bestkk = save_bestk(100000,kk)
    snap()
    unsnap(k) #have to do snap first if want current result snapped in.
        # unsnap fraigs snapshots and does map_lut_dch at end
    print nl()
    bestk = save_bestk(bestk,k)
    abc('r %s_bestk%d.blif'%(f_name,k))
    map_iter(k) #1
    bestk = save_bestk(bestk,k)
    while True:
        print 'Perturbing with %d-Lut'%kk
##        snap()
        map_lut_dch_iter(kk)
##        snap()
        bestkk_old = bestkk
        bestkk = save_bestk(bestkk,kk)
        if bestkk >= bestkk_old:
            break
        snap()
        unsnap(k) #fraig restore and map
##        bestk = save_bestk(bestk,k)
##        snap()
        bestk_old = bestk
        map_iter(k)
        bestk = save_bestk(bestk,k)
        if bestk >= bestk_old:
            break
        continue
    abc('fraig_restore') #dump what is left in fraig_store
    unsave_bestk(k)
    print '\nFinal size = ',
    print nl()
    print 'time for %s = %.02f'%(f_name,(time.time()-tt))
##    cec_it()

def get_bestk(k=4):
    abc('write_blif %s_temp.blif'%f_name)
    unsave_bestk(k)
    res = n_nodes()
    abc('r %s_temp.blif'%f_name)
    return res

def map_iter(k=4):
    tt = time.time()
    bestk = get_bestk(k)
    map_lut_dch(k)
    bestk = save_bestk(bestk,k)
    n=0
    unsave_bestk(k)
    while True:
##        snap()
        perturb(k) #
##        snap()
        perturb(k)
        old_bestk = bestk
##        print old_bestk
        map_lut_dch_iter(k)
        bestk = save_bestk(bestk,k)
        print bestk
        if bestk < old_bestk:
            n=0 # keep it up
            continue
        elif n == 2: #perturb 
            break
        else:
            n = n+1
            print '%d-perturb'%n
##            snap()
##            unsave_bestk(k)
    unsave_bestk(k)

def map_star(k=4):
    tt = time.time()
    map_until_conv(k)
    abc('write_blif %s_best_star.blif'%f_name)
    best = n_nodes()
    while True:
        jog(2*k)
        map_until_conv(k)
        if n_nodes() >= best:
            break
        else:
            best = n_nodes()
            abc('write_blif %s_best_star.blif'%f_name)
    abc('r %s_best_star.blif'%f_name)
    print 'SIZE = %d, TIME = %.2f for %s'%(n_nodes(),(time.time() - tt),f_name)

def decomp_444():
    abc('st; dch; if -K 10 -S 444')
    abc('write_blif -S 444 %s_temp.blif; r %s_temp.blif'%(f_name,f_name)) 


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

def sizeof():
    return [n_pis(),n_pos(),n_latches(),n_ands()]
