import os
import sys
import time
import tempfile
import subprocess

from contextlib import contextmanager

import affinity
import pyabc
import pyabc_split
import pyliveness
import pyzz

@contextmanager
def temp_file_names(N, suffix=""):
    
    files = []
    
    try:
        
        for i in xrange(N):
            files.append( tempfile.NamedTemporaryFile(suffix=suffix) )
            
        yield [ f.name for f in files ]
    
    finally:
        for f in files:
            f.close()
        
def parse_bip_status(status):
    
    res = {}
    
    for line in open(status, 'r'):
        
        line = line.strip()
        
        colon = line.find(':')
        
        if colon < 0:
            continue
            
        field = line[:colon]
        data = line[colon+2:]
        
        res[field] = data
    
    return res


def log(*args):
    print 'LIVENESS (%d):'%os.getpid(), " ".join(str(arg) for arg in args)


def run_bip(args, aiger):

    log('running: bip', " ".join(args), aiger)

    import redirect
    with redirect.redirect():

        with temp_file_names(1) as tmpnames:

            args = [
                'bip',
                '-abc',
                '-input=%s'%aiger,
                '-output=%s'%tmpnames[0],
            ] + args;
            
            rc = subprocess.call(args)
            
            if rc!=0:
                return None

            res = parse_bip_status(tmpnames[0])

    log('bip finished:', rc, res)
    return res



def run_super_prove(aiger_filename, used_cores, super_prove):

    log('running: super_prove on', aiger_filename, used_cores, super_prove)

    mask = affinity.sched_getaffinity(os.getpid())
    affinity.sched_setaffinity(os.getpid(), mask[used_cores:])

    res = super_prove(aiger_filename)

    log('super_prove returned:', res)

    return res


def compute_sc(simple_aiger, sc_aiger, l2s_aiger):

    log('computing stabilizing constraints')

    N0 = pyzz.netlist.read_aiger(simple_aiger)

    N, new_fg = pyliveness.extract_stabilizing_constraints(N0, 0, list(N0.get_Flops()))

    N.write_aiger(sc_aiger)

    M, xlat, loop_start = pyliveness.extract_liveness_as_safety(N, new_fg)
    M.write_aiger(l2s_aiger)

    log('done computing stabilizing constraints')

    return True


from pyaig import AIG, read_aiger, write_aiger, utils


def run_niklas_single(aiger, simplify, report_result, super_prove=None, timeout=None):

    log('run_niklas_single')
    
    orig_args = [
        [ ',live', '-k=l2s', '-eng=treb-abs' ],
        [ ',live', '-k=inc' ],
        [ ',live', '-k=l2s', '-eng=bmc' ],
    ]
    
    simplified_args = [
        [ ',live', '-k=l2s', '-eng=treb-abs' ],
        [ ',live', '-k=inc' ],
        [ ',live', '-k=l2s', '-eng=bmc' ],
        [ ',live', '-k=l2s', '-eng=treb' ],
    ]
    
    with temp_file_names(3, suffix='.aig') as temporary_files:

        simple_aiger, sc_aiger, l2s_aiger = temporary_files

        orig_funcs = [ pyabc_split.defer(run_bip)(a, aiger) for a in orig_args ]
        simplified_funcs = [ pyabc_split.defer(run_bip)(a, simple_aiger) for a in simplified_args ]

        with pyabc_split.make_splitter() as splitter:

            timeout_id = splitter.add_timer(timeout) if timeout else None
            
            ids = splitter.fork_all( orig_funcs )
            log('running engines:', ids)
            kill_if_simplified = ids[1:]
            
            simplifier_id = splitter.fork_one( pyabc_split.defer(simplify)(aiger, simple_aiger) )
            log('running simplifier:', simplifier_id)

            sc_id = None
            
            for id, res in splitter:

                log('process %d finished with'%id, res)

                if id in kill_if_simplified:
                    kill_if_simplified.remove(id)
                
                if id == timeout_id:
                    log('timeout')
                    return False
                
                elif id == simplifier_id:
                    log('simplify ended')
                    if not res:
                        continue
                    log('killing', kill_if_simplified)
                    for kill_id in kill_if_simplified:
                        splitter.kill(kill_id)
                    tmp_ids = splitter.fork_all( simplified_funcs )
                    log('running engines:', tmp_ids)

                    sc_id = splitter.fork_one( pyabc_split.defer(compute_sc)(simple_aiger, sc_aiger, l2s_aiger))
                    log('running sc:', sc_id)
                    continue

                elif id == sc_id:

                    log('sc ended')

                    if res:
                        tmp_id = splitter.fork_one( pyabc_split.defer(run_bip)([',live', '-k=inc'], sc_aiger) )
                        log('running engine:', tmp_id)
                        if super_prove:
                            tmp_id = splitter.fork_one( pyabc_split.defer(run_super_prove)(l2s_aiger, 3, super_prove) )
                            log('running super_prove:', tmp_id)

                elif report_result(res):
                    log('RESULT', res)
                    return True

    return False

def run_niklas_multi(aiger, simplify, report_result, super_prove=None):
    
    with open(aiger, 'r') as fin:
        aig = read_aiger( fin )
        
    n_j_pos = aig.n_justice()
    assert n_j_pos > 0
    
    if n_j_pos==1:
        return run_niklas_single( aiger, simplify, report_result=lambda res: report_result(0, res), super_prove=super_prove )
    
    with temp_file_names(n_j_pos, suffix='.aig') as single_aiger:
        
        def extract(j_po):
            with open(single_aiger[j_po], 'w') as fout:
                write_aiger(utils.extract_justice_po(aig, j_po), fout)
                
        for _ in pyabc_split.split_all_full( [pyabc_split.defer(extract)(i) for i in xrange(n_j_pos) ] ):
            pass
            
        unsolved = set( xrange(n_j_pos) )
        
        timeout = 1
        
        while unsolved:
            for j_po in sorted(unsolved):
                if run_niklas_single( single_aiger[j_po], simplify, report_result=lambda res: report_result(j_po, res), timeout=timeout, super_prove=super_prove ):
                    unsolved.remove(j_po)
            timeout *= 2
        
    return not unsolved
    
if __name__ == "__main__":    

    import click

    def simplify(aiger_in, aiger_out):

        with temp_file_names(2, suffix='.aig') as tmp:

            saved = utils.save_po_info(aiger_in, tmp[0])

            pyabc.run_command( 'read_aiger %s'%tmp[0] )
            pyabc.run_command( 'dc2 ; dc2 ; dc2 ; dc2' )
            pyabc.run_command( 'write_aiger %s'%tmp[1] )

            utils.restore_po_info( saved, tmp[1], aiger_out )
            
        return True

    def report_result(id, res):
        
        if res and 'result' in res:
            result = res['result']
            if result=='proved':
                log("PROVED:", id)
                return True
            elif result=='failed':
                log("FAILED:", id)
                return True
            
        return False
        
    @click.command()
    @click.argument("aiger", type=click.Path(exists=True, dir_okay=False))
    def main(aiger):

        try:
            run_niklas_multi(aiger, simplify=simplify, report_result=report_result)
        except:
            import traceback
            traceback.print_exc()

    main()
