import sys
import os
import pyabc
import par
import tempfile
import shutil
import redirect
import optparse

from contextlib import contextmanager

def read_cmd(args):
    if len(args)==2:
        par.read_file_quiet(args[1])
    else:
        par.read_file()
    return 0

pyabc.add_abc_command(read_cmd, "ZPython", "/rf", 0)

def chdir_cmd(args):
    os.chdir( args[1] )
    return 0

pyabc.add_abc_command(chdir_cmd, "ZPython", "/cd", 0)

def pwd_cmd(args):
    print os.getcwd()
    return 0

pyabc.add_abc_command(pwd_cmd, "ZPython", "/pwd", 0)

def ls_cmd(args):
    os.system("ls " + " ".join(args[1:]))
    return 0

pyabc.add_abc_command(ls_cmd, "ZPython", "/ls", 0)

pushd_temp_stack = []

def pushdtemp_cmd(args):
    tmpdir = tempfile.mkdtemp()
    pushd_temp_stack.append( (os.getcwd(), tmpdir) )
    os.chdir(tmpdir)
    return 0
    
pyabc.add_abc_command(pushdtemp_cmd, "ZPython", "/pushdtemp", 0)

def popdtemp_cmd(args):
    prev, temp = pushd_temp_stack.pop()
    os.chdir(prev)
    shutil.rmtree(temp, ignore_errors=True)
    return 0
    
pyabc.add_abc_command(popdtemp_cmd, "ZPython", "/popdtemp", 0)

pushredirect_stack = []

def push_redirect_cmd(args):
    
    if len(args) > 1:
        dest = open(args[1], 'w')
    else:
        dest = redirect.null_file
    
    fdout = redirect.start_redirect( dest, sys.stdout)
    pushredirect_stack.append( (sys.stdout, fdout) )
    
    fderr = redirect.start_redirect( dest, sys.stderr)
    pushredirect_stack.append( (sys.stderr, fderr) )
    
    return 0
    
pyabc.add_abc_command(push_redirect_cmd, "ZPython", "/pushredirect", 0)

def pop_redirect_cmd(args):
    
    err, fderr = pushredirect_stack.pop()
    redirect.end_redirect(err, fderr)
 
    out, fdout = pushredirect_stack.pop()
    redirect.end_redirect(out, fdout)
    
    return 0
    
pyabc.add_abc_command(pop_redirect_cmd, "ZPython", "/popredirect", 0)

def print_aiger_result(args):
    status = pyabc.prob_status()
    
    if status==1:
        print 0
    elif status==0:
        print 1
    else:
        print 2
    
    return 0
    
pyabc.add_abc_command(print_aiger_result, "ZPython", "/print_aiger_result", 0)

@contextmanager
def replace_report_result(multi):
    
    def report_result(po, result):
        
        print "REPORT RESULT: ", po, result
        
        print >> stdout, "%d"%result
        print >> stdout, "b%d"%po
        print >> stdout, "."
        
    def report_liveness_result(po, result):
        
        print "REPORT RESULT: ", po, result
        
        print >> stdout, "%d"%result
        print >> stdout, "j%d"%po
        print >> stdout, "."

    def report_bmc_depth(depth):
        
        if not multi:
            print "REPORT BMC DEPTH:", depth
            print >> stdout, "u%d"%depth
    
    with redirect.save_stdout() as stdout:
        
        old_report_result = par.report_result
        par.report_result = report_result
        
        #old_report_liveness_result = par.report_liveness_result
        par.report_liveness_result = report_liveness_result

        old_report_bmc_depth = par.report_bmc_depth
        par.report_bmc_depth = report_bmc_depth
        
        try:
            yield
        finally:
            par.report_result = old_report_result
            #~ par.report_liveness_result = report_liveness_result
            par.report_bmc_depth = old_report_bmc_depth

def proof_command_wrapper_internal(prooffunc, category_name, command_name, change, multi=False):

    def wrapper(argv):
        
        usage = "usage: %prog [options] <aig_file>"
    
        parser = optparse.OptionParser(usage, prog=command_name)
    
        parser.add_option("-n", "--no_redirect", dest="noisy", action="store_true", default=False, help="don't redirect output")
        parser.add_option("-r", "--redirect", dest="redirect", default=None, help="redirect output to file")
        parser.add_option("-d", "--current_dir", dest="current_dir", action="store_true", default=False, help="stay in current directory")

        options, args = parser.parse_args(argv)
        
        if len(args) != 2:
            parser.print_usage()
            return 0
            
        if options.noisy and options.redirect:
            print 'error: options -n/--no_redirect and -r/--redirect are mutually exclusive'
            return 0
            
        aig_filename = os.path.abspath(args[1])

        with replace_report_result(multi):

            if options.redirect:
                pyabc.run_command('/pushredirect %s'%options.redirect)
            elif not options.noisy:
                pyabc.run_command('/pushredirect')
                
            if not options.current_dir:
                pyabc.run_command('/pushdtemp')
                
            try:
                for d in os.environ['PATH'].split(':'):
                    bip = os.path.join(d, 'bip')
                    if os.path.exists(bip):
                        pyabc.run_command("load_plugin %s Bip"%bip)
                        break

                basename = os.path.basename( aig_filename )
                shutil.copyfile(aig_filename, basename)
                aig_filename = basename

                result = prooffunc(aig_filename)
                
                par.cex_list = []
            except:
                result = None

            if not multi:
                
                if result=="SAT":
                    par.report_result(0,1)
                elif result=="UNSAT":
                    par.report_result(0,0)
                elif type(result)==list and len(result)>0 and result[0] == "SAT":
                    par.report_result(0,1)
                elif type(result)==list and len(result)>0 and result[0] == "UNSAT":
                    par.report_result(0,0)
                else:
                    par.report_result(0,2)

            if not options.current_dir:
                pyabc.run_command('/popdtemp')

            if not options.noisy:
                pyabc.run_command('/popredirect')
                
        return 0
    
    pyabc.add_abc_command(wrapper, category_name, command_name, change)

def proof_command_wrapper(prooffunc, category_name, command_name, change, multi=False):
    def pf(aig_filename):
        par.read_file_quiet(aig_filename)
        return prooffunc()
    return proof_command_wrapper_internal(pf, category_name, command_name, change, multi)

proof_command_wrapper(par.sp,  'HWMCC13', '/super_prove_aiger',  0)
proof_command_wrapper(par.simple,  'HWMCC13', '/simple_aiger',  0)
proof_command_wrapper(par.simple_bip,  'HWMCC13', '/simple_bip_aiger',  0)
proof_command_wrapper(par.simple_sat,  'HWMCC13', '/simple_sat_aiger',  0)
proof_command_wrapper(par.mp,  'HWMCC13', '/multi_prove_aiger',  0, multi=True)

def simple_liveness_prooffunc(aig_filename):
    
    import niklas
    from pyaig import utils

    def simplify(aiger_in, aiger_out):
        
        with niklas.temp_file_names(2, suffix='.aig') as tmp:

            saved = utils.save_po_info(aiger_in, tmp[0])
            
            par.read_file_quiet(tmp[0])
            
            par.pre_simp()
            
            pyabc.run_command( 'write_aiger %s'%tmp[1] )

            utils.restore_po_info( saved, tmp[1], aiger_out )
            
            return True
        
    def report_result(id, res):
        
        if res and 'result' in res:
            result = res['result']
            if result=='proved':
                par.report_liveness_result(id, 0)
                return True
            elif result=='failed':
                par.report_liveness_result(id, 1)
                return True
            
        return False

    try:
        niklas.run_niklas_multi(aig_filename, simplify=simplify, report_result=report_result)
    except:
        import traceback
        traceback.print_exc()

proof_command_wrapper_internal( simple_liveness_prooffunc, "HWMCC13", "/simple_liveness_aiger", 0, multi=True)
