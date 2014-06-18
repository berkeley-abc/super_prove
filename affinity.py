import os

import ctypes
import ctypes.util

_number_of_cores = os.sysconf('SC_NPROCESSORS_ONLN')

_pid_t = ctypes.c_int32
_mask_t = ctypes.c_uint64

def _or( values ):

    res = 0

    for v in values:
        res |= v

    return res

def sched_getaffinity(pid):

    _libc = ctypes.CDLL('libc.so.6', use_errno=True)

    mask = _mask_t()

    rc = _libc.sched_getaffinity(
        ctypes.c_int32(pid),
        ctypes.sizeof(mask),
        ctypes.byref(mask)
    )

    if rc!=0:
        raise OSError(ctypes.get_errno(), 'sched_getaffinity(): %s'%os.strerror(ctypes.get_errno()))

    mask = mask.value
    return [ i for i in xrange(_number_of_cores) if mask&(1<<i) ]


def sched_setaffinity(pid, cpus):

    _libc = ctypes.CDLL('libc.so.6', use_errno=True)

    mask = _mask_t(_or(1<<c for c in cpus))

    rc = _libc.sched_setaffinity(
        ctypes.c_int32(pid),
        ctypes.sizeof(mask),
        ctypes.byref(mask)
    )

    if rc!=0:
        raise OSError(ctypes.get_errno(), 'sched_setaffinity(): %s'%os.strerror(ctypes.get_errno()))

    return mask.value

if __name__=='__main__':
    print sched_getaffinity(os.getpid())
    sched_setaffinity(os.getpid(), [0,1])
    print sched_getaffinity(os.getpid())
