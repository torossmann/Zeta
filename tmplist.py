"""
A stack that might live in a temporary file instead of system memory.
"""
from sage.all import dumps, loads

from . import common
import contextlib
import os
import struct

from .util import TemporaryDirectory

_INTSIZE = 8
_INTSYMB = '=q'


class DiskList:
    # Write operations are not thread safe, but reading is.
    # Exceptions during changes may leave the list in an inconsistent state.

    def __init__(self, filename):
        self._data = filename
        self._index = filename + '.index'
        self._sizes = filename + '.sizes'

        # Make sure all files exist.
        with open(self._data, 'ab'), open(self._index, 'ab'), \
                open(self._sizes, 'ab'):
            pass

    def __len__(self):
        return os.path.getsize(self._index) // _INTSIZE

    def unlink(self):
        for f in [self._data, self._index, self._sizes]:
            os.remove(f)

    def append(self, x):
        s = dumps(x)

        with open(self._index, 'ab') as f:
            f.write(struct.pack(_INTSYMB, os.path.getsize(self._data)))
        with open(self._sizes, 'ab') as f:
            f.write(struct.pack(_INTSYMB, len(s)))
        with open(self._data, 'ab') as f:
            f.write(s)

    def extend(self, it):
        for x in it:
            self.append(x)

    def __getitem__(self, index):
        if index < 0:
            index = len(self) - index
        if index < 0 or index >= len(self):
            raise IndexError('index out of range')

        # Get position
        with open(self._index, 'rb') as f:
            f.seek(_INTSIZE * index)
            pos, = struct.unpack(_INTSYMB, f.read(_INTSIZE))

        # Get size
        with open(self._sizes, 'rb') as f:
            f.seek(_INTSIZE * index)
            size, = struct.unpack(_INTSYMB, f.read(_INTSIZE))

        # Read data
        with open(self._data, 'rb') as f:
            f.seek(pos)
            return loads(f.read(size))

    def pop(self):
        length = len(self)
        if not length:
            raise IndexError('cannot pop an empty stack')

        # Read and delete the position of the last chunk.
        with open(self._index, 'r+b') as f:
            f.seek(_INTSIZE * (length - 1))
            pos, = struct.unpack(_INTSYMB, f.read(_INTSIZE))
            f.seek(_INTSIZE * (length - 1))
            f.truncate()

        # Read and delete the size of the last chunk.
        with open(self._sizes, 'r+b') as f:
            f.seek(_INTSIZE * (length - 1))
            size, = struct.unpack(_INTSYMB, f.read(_INTSIZE))
            f.seek(_INTSIZE * (length - 1))
            f.truncate()

        # Read and delete the chunk itself.
        with open(self._data, 'r+b') as f:
            f.seek(pos)
            top = f.read(size)
            f.seek(pos)
            f.truncate()
        return loads(top)

    def __iter__(self):
        for i in range(len(self)):
            yield self[i]


@contextlib.contextmanager
def TemporaryList(use_disk=False):
    if common.save_memory or use_disk:
        with TemporaryDirectory() as tmpdir:
            yield DiskList(os.path.join(tmpdir, 'list'))
    else:
        yield []
