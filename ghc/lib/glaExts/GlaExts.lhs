%
% (c) The AQUA Project, Glasgow University, 1994-1996
%
\section[GlaExts]{The @GlaExts@ interface}

Compatibility cruft: Deprecated! Don't use!  This rug will
dissappear from underneath your feet very soon.

This module will eventually be the interface to GHC-ONLY extensions:
i.e. unboxery and primitive operations over unboxed values.

OLD:
The @GlaExts@ packages up various Glasgow extensions and
exports them all through one interface. The Idea being that
a Haskell program using a Glasgow extension doesn't have to
selective import of obscure/likely-to-move (believe me, we
really like to move functions around for the prelude bits!)
GHC interfaces - instead import the GlaExts rag bag and you should be away!

\begin{code}
module GlaExts

       (
        ST, RealWorld,

	unsafePerformIO, 
	unsafeInterleaveIO,
        
        -- operations for interfacing IO and ST
        --
        stToIO,       -- :: ST RealWorld a -> IO a
	ioToST,	      -- :: IO a -> ST RealWorld a

	-- compatibility cruft
	PrimIO,
	ioToPrimIO,
	primIOToIO,
	unsafePerformPrimIO,

        -- Everything from module ByteArray:
	module ByteArray,

        -- Same for Mutable(Byte)Array interface:
	module MutableArray,
	
        -- the representation of some basic types:
        Int(..),Addr(..),Word(..),Float(..),Double(..),Integer(..),Char(..),

        -- misc bits
	trace,
	Lift(..),

        -- and finally, all the unboxed primops of GHC!
        module GHC

       ) where

import GHC
import STBase
import IOExts
import PrelBase
import ByteArray
import MutableArray
import Monad
import IOBase
import Foreign

type PrimIO a = IO a
primIOToIO io = io
ioToPrimIO io = io
unsafePerformPrimIO = unsafePerformIO

\end{code}
