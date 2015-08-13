{-# OPTIONS_GHC -w #-}
{-# OPTIONS -fglasgow-exts -cpp #-}
{-# OPTIONS -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module Amath.Expr.ParExp where
import Amath.Expr.AbsExp
import Amath.Expr.LexExp
import Amath.Expr.ErrM
import qualified Data.Array as Happy_Data_Array
import qualified GHC.Exts as Happy_GHC_Exts

-- parser produced by Happy Version 1.18.6

newtype HappyAbsSyn  = HappyAbsSyn HappyAny
#if __GLASGOW_HASKELL__ >= 607
type HappyAny = Happy_GHC_Exts.Any
#else
type HappyAny = forall a . a
#endif
happyIn13 :: (Ident) -> (HappyAbsSyn )
happyIn13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn13 #-}
happyOut13 :: (HappyAbsSyn ) -> (Ident)
happyOut13 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut13 #-}
happyIn14 :: (Integer) -> (HappyAbsSyn )
happyIn14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn14 #-}
happyOut14 :: (HappyAbsSyn ) -> (Integer)
happyOut14 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut14 #-}
happyIn15 :: (Pmemory) -> (HappyAbsSyn )
happyIn15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn15 #-}
happyOut15 :: (HappyAbsSyn ) -> (Pmemory)
happyOut15 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut15 #-}
happyIn16 :: (PRule) -> (HappyAbsSyn )
happyIn16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn16 #-}
happyOut16 :: (HappyAbsSyn ) -> (PRule)
happyOut16 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut16 #-}
happyIn17 :: ([PRule]) -> (HappyAbsSyn )
happyIn17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn17 #-}
happyOut17 :: (HappyAbsSyn ) -> ([PRule])
happyOut17 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut17 #-}
happyIn18 :: ([Exp]) -> (HappyAbsSyn )
happyIn18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn18 #-}
happyOut18 :: (HappyAbsSyn ) -> ([Exp])
happyOut18 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut18 #-}
happyIn19 :: (Exp) -> (HappyAbsSyn )
happyIn19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn19 #-}
happyOut19 :: (HappyAbsSyn ) -> (Exp)
happyOut19 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut19 #-}
happyIn20 :: (Exp) -> (HappyAbsSyn )
happyIn20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn20 #-}
happyOut20 :: (HappyAbsSyn ) -> (Exp)
happyOut20 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut20 #-}
happyIn21 :: (Exp) -> (HappyAbsSyn )
happyIn21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn21 #-}
happyOut21 :: (HappyAbsSyn ) -> (Exp)
happyOut21 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut21 #-}
happyIn22 :: (Exp) -> (HappyAbsSyn )
happyIn22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn22 #-}
happyOut22 :: (HappyAbsSyn ) -> (Exp)
happyOut22 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut22 #-}
happyIn23 :: (Exp) -> (HappyAbsSyn )
happyIn23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn23 #-}
happyOut23 :: (HappyAbsSyn ) -> (Exp)
happyOut23 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut23 #-}
happyIn24 :: (Exp) -> (HappyAbsSyn )
happyIn24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyIn24 #-}
happyOut24 :: (HappyAbsSyn ) -> (Exp)
happyOut24 x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOut24 #-}
happyInTok :: (Token) -> (HappyAbsSyn )
happyInTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyInTok #-}
happyOutTok :: (HappyAbsSyn ) -> (Token)
happyOutTok x = Happy_GHC_Exts.unsafeCoerce# x
{-# INLINE happyOutTok #-}


happyActOffsets :: HappyAddr
happyActOffsets = HappyA# "\x00\x00\x92\x00\x00\x00\x00\x00\x13\x00\x13\x00\x13\x00\x13\x00\x13\x00\x09\x00\x92\x00\x00\x00\x00\x00\x00\x00\x8a\x00\x13\x00\x00\x00\x8f\x00\x53\x00\x00\x00\x09\x00\xfa\xff\x00\x00\x14\x00\x7c\x00\x7e\x00\x95\x00\x3f\x00\x59\x00\x01\x00\x88\x00\x4c\x00\x2e\x00\x2e\x00\x40\x00\x00\x00\x23\x00\x00\x00\x13\x00\x13\x00\x13\x00\x13\x00\x13\x00\x13\x00\x00\x00\x13\x00\x91\x00\x00\x00\x8d\x00\x00\x00\x26\x00\x26\x00\x87\x00\x83\x00\x83\x00\x1c\x00\x0f\x00\x00\x00\x00\x00\x00\x00\x06\x00\x00\x00\x00\x00"#

happyGotoOffsets :: HappyAddr
happyGotoOffsets = HappyA# "\x98\x00\x81\x00\x08\x00\x18\x00\x2d\x00\x4f\x00\x6b\x00\x71\x00\x7d\x00\x7f\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x4a\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x21\x00\x6d\x00\x00\x00\x00\x00\x00\x00\x6d\x00\x00\x00\x07\x00\x00\x00\x5f\x00\x5b\x00\x3e\x00\x6e\x00\x1b\x00\x31\x00\x00\x00\x39\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xfc\xff\x21\x00\x00\x00\x00\x00"#

happyDefActions :: HappyAddr
happyDefActions = HappyA# "\xf1\xff\x00\x00\xf1\xff\xef\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf5\xff\xe0\xff\xe1\xff\x00\x00\x00\x00\xf4\xff\xe0\xff\x00\x00\xe2\xff\x00\x00\x00\x00\xe5\xff\x00\x00\xe7\xff\x00\x00\xea\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xf3\xff\xf0\xff\x00\x00\xee\xff\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\xe4\xff\x00\x00\x00\x00\xdf\xff\x00\x00\xe6\xff\xe8\xff\xe9\xff\x00\x00\xeb\xff\xec\xff\x00\x00\x00\x00\xed\xff\xe3\xff\xef\xff\x00\x00\xf2\xff"#

happyCheck :: HappyAddr
happyCheck = HappyA# "\xff\xff\x05\x00\x01\x00\x09\x00\x00\x00\x01\x00\x05\x00\x01\x00\x01\x00\x0f\x00\x01\x00\x05\x00\x04\x00\x0c\x00\x0d\x00\x0b\x00\x0f\x00\x0b\x00\x0c\x00\x0d\x00\x01\x00\x0c\x00\x0d\x00\x03\x00\x05\x00\x0a\x00\x06\x00\x00\x00\x01\x00\x05\x00\x02\x00\x0c\x00\x0d\x00\x00\x00\x01\x00\x0f\x00\x09\x00\x0a\x00\x0b\x00\x06\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x01\x00\x09\x00\x0d\x00\x00\x00\x01\x00\x06\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x01\x00\x0a\x00\x0b\x00\x0f\x00\x00\x00\x01\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x01\x00\x0c\x00\x01\x00\x0f\x00\x00\x00\x01\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x07\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x01\x00\x04\x00\x05\x00\x00\x00\x01\x00\x08\x00\x0f\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x01\x00\x00\x00\x00\x00\x01\x00\x03\x00\x00\x00\x01\x00\x08\x00\x09\x00\x0a\x00\x0b\x00\x09\x00\x0a\x00\x0b\x00\x09\x00\x0a\x00\x0b\x00\x00\x00\x01\x00\x00\x00\x01\x00\x00\x00\x04\x00\x05\x00\x03\x00\x09\x00\x03\x00\x0a\x00\x0b\x00\x06\x00\x0b\x00\x04\x00\x05\x00\x0f\x00\x07\x00\x02\x00\x01\x00\x04\x00\x05\x00\x02\x00\x0c\x00\x04\x00\x05\x00\x0f\x00\x03\x00\x0f\x00\x02\x00\x06\x00\x04\x00\xff\xff\x0c\x00\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff"#

happyTable :: HappyAddr
happyTable = HappyA# "\x00\x00\x3c\x00\x10\x00\x2c\x00\x0c\x00\x0d\x00\x15\x00\x10\x00\x37\x00\xff\xff\x10\x00\x15\x00\x1e\x00\x0c\x00\x11\x00\x2c\x00\xff\xff\x3e\x00\x0c\x00\x11\x00\x10\x00\x0c\x00\x11\x00\x2a\x00\x15\x00\x3c\x00\x2b\x00\x11\x00\x0d\x00\x1d\x00\x39\x00\x0c\x00\x11\x00\x11\x00\x0d\x00\xff\xff\x32\x00\x16\x00\x13\x00\x25\x00\x1c\x00\x1a\x00\x18\x00\x16\x00\x13\x00\x11\x00\x0d\x00\x2c\x00\x11\x00\x11\x00\x0d\x00\x1b\x00\x1c\x00\x1a\x00\x18\x00\x16\x00\x13\x00\x11\x00\x0d\x00\x31\x00\x13\x00\xff\xff\x11\x00\x0d\x00\x30\x00\x1a\x00\x18\x00\x16\x00\x13\x00\x34\x00\x1a\x00\x18\x00\x16\x00\x13\x00\x11\x00\x0d\x00\x0c\x00\x25\x00\xff\xff\x11\x00\x0d\x00\x2e\x00\x1a\x00\x18\x00\x16\x00\x13\x00\x19\x00\x1a\x00\x18\x00\x16\x00\x13\x00\x11\x00\x0d\x00\x27\x00\x28\x00\x11\x00\x0d\x00\x29\x00\xff\xff\x35\x00\x18\x00\x16\x00\x13\x00\x36\x00\x18\x00\x16\x00\x13\x00\x11\x00\x0d\x00\x1f\x00\x11\x00\x0d\x00\x23\x00\x11\x00\x0d\x00\x17\x00\x18\x00\x16\x00\x13\x00\x33\x00\x16\x00\x13\x00\x15\x00\x16\x00\x13\x00\x11\x00\x0d\x00\x0c\x00\x0d\x00\x1f\x00\x27\x00\x28\x00\x20\x00\x2c\x00\x2a\x00\x12\x00\x13\x00\x2b\x00\x0e\x00\x27\x00\x28\x00\xff\xff\x3a\x00\x3b\x00\x2e\x00\x27\x00\x28\x00\x30\x00\x0c\x00\x27\x00\x28\x00\xff\xff\x2a\x00\xff\xff\x21\x00\x2b\x00\x22\x00\x00\x00\x0c\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"#

happyReduceArr = Happy_Data_Array.array (10, 32) [
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32)
	]

happy_n_terms = 16 :: Int
happy_n_nonterms = 12 :: Int

happyReduce_10 = happySpecReduce_1  0# happyReduction_10
happyReduction_10 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TV happy_var_1)) -> 
	happyIn13
		 (Ident happy_var_1
	)}

happyReduce_11 = happySpecReduce_1  1# happyReduction_11
happyReduction_11 happy_x_1
	 =  case happyOutTok happy_x_1 of { (PT _ (TI happy_var_1)) -> 
	happyIn14
		 ((read ( happy_var_1)) :: Integer
	)}

happyReduce_12 = happySpecReduce_1  2# happyReduction_12
happyReduction_12 happy_x_1
	 =  case happyOut17 happy_x_1 of { happy_var_1 -> 
	happyIn15
		 (Pmem (reverse happy_var_1)
	)}

happyReduce_13 = happyReduce 7# 3# happyReduction_13
happyReduction_13 (happy_x_7 `HappyStk`
	happy_x_6 `HappyStk`
	happy_x_5 `HappyStk`
	happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut14 happy_x_3 of { happy_var_3 -> 
	case happyOut18 happy_x_6 of { happy_var_6 -> 
	happyIn16
		 (Rule happy_var_1 happy_var_3 (reverse happy_var_6)
	) `HappyStk` happyRest}}}

happyReduce_14 = happySpecReduce_0  4# happyReduction_14
happyReduction_14  =  happyIn17
		 ([]
	)

happyReduce_15 = happySpecReduce_2  4# happyReduction_15
happyReduction_15 happy_x_2
	happy_x_1
	 =  case happyOut17 happy_x_1 of { happy_var_1 -> 
	case happyOut16 happy_x_2 of { happy_var_2 -> 
	happyIn17
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_16 = happySpecReduce_0  5# happyReduction_16
happyReduction_16  =  happyIn18
		 ([]
	)

happyReduce_17 = happySpecReduce_2  5# happyReduction_17
happyReduction_17 happy_x_2
	happy_x_1
	 =  case happyOut18 happy_x_1 of { happy_var_1 -> 
	case happyOut19 happy_x_2 of { happy_var_2 -> 
	happyIn18
		 (flip (:) happy_var_1 happy_var_2
	)}}

happyReduce_18 = happyReduce 4# 6# happyReduction_18
happyReduction_18 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut20 happy_x_1 of { happy_var_1 -> 
	case happyOut20 happy_x_3 of { happy_var_3 -> 
	happyIn19
		 (EEqual happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_19 = happySpecReduce_3  7# happyReduction_19
happyReduction_19 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	case happyOut21 happy_x_3 of { happy_var_3 -> 
	happyIn20
		 (EAdd happy_var_1 happy_var_3
	)}}

happyReduce_20 = happySpecReduce_3  7# happyReduction_20
happyReduction_20 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_1 of { happy_var_1 -> 
	case happyOut21 happy_x_3 of { happy_var_3 -> 
	happyIn20
		 (ESub happy_var_1 happy_var_3
	)}}

happyReduce_21 = happySpecReduce_1  7# happyReduction_21
happyReduction_21 happy_x_1
	 =  case happyOut21 happy_x_1 of { happy_var_1 -> 
	happyIn20
		 (happy_var_1
	)}

happyReduce_22 = happySpecReduce_3  8# happyReduction_22
happyReduction_22 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut21 happy_x_1 of { happy_var_1 -> 
	case happyOut22 happy_x_3 of { happy_var_3 -> 
	happyIn21
		 (EMul happy_var_1 happy_var_3
	)}}

happyReduce_23 = happySpecReduce_3  8# happyReduction_23
happyReduction_23 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut21 happy_x_1 of { happy_var_1 -> 
	case happyOut22 happy_x_3 of { happy_var_3 -> 
	happyIn21
		 (EDiv happy_var_1 happy_var_3
	)}}

happyReduce_24 = happySpecReduce_1  8# happyReduction_24
happyReduction_24 happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	happyIn21
		 (happy_var_1
	)}

happyReduce_25 = happySpecReduce_3  9# happyReduction_25
happyReduction_25 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut22 happy_x_1 of { happy_var_1 -> 
	case happyOut23 happy_x_3 of { happy_var_3 -> 
	happyIn22
		 (EExp happy_var_1 happy_var_3
	)}}

happyReduce_26 = happySpecReduce_1  9# happyReduction_26
happyReduction_26 happy_x_1
	 =  case happyOut23 happy_x_1 of { happy_var_1 -> 
	happyIn22
		 (happy_var_1
	)}

happyReduce_27 = happySpecReduce_2  10# happyReduction_27
happyReduction_27 happy_x_2
	happy_x_1
	 =  case happyOut24 happy_x_2 of { happy_var_2 -> 
	happyIn23
		 (ENeg happy_var_2
	)}

happyReduce_28 = happyReduce 4# 10# happyReduction_28
happyReduction_28 (happy_x_4 `HappyStk`
	happy_x_3 `HappyStk`
	happy_x_2 `HappyStk`
	happy_x_1 `HappyStk`
	happyRest)
	 = case happyOut13 happy_x_1 of { happy_var_1 -> 
	case happyOut20 happy_x_3 of { happy_var_3 -> 
	happyIn23
		 (EFunc happy_var_1 happy_var_3
	) `HappyStk` happyRest}}

happyReduce_29 = happySpecReduce_1  10# happyReduction_29
happyReduction_29 happy_x_1
	 =  case happyOut24 happy_x_1 of { happy_var_1 -> 
	happyIn23
		 (happy_var_1
	)}

happyReduce_30 = happySpecReduce_1  11# happyReduction_30
happyReduction_30 happy_x_1
	 =  case happyOut14 happy_x_1 of { happy_var_1 -> 
	happyIn24
		 (EInt happy_var_1
	)}

happyReduce_31 = happySpecReduce_1  11# happyReduction_31
happyReduction_31 happy_x_1
	 =  case happyOut13 happy_x_1 of { happy_var_1 -> 
	happyIn24
		 (EVar happy_var_1
	)}

happyReduce_32 = happySpecReduce_3  11# happyReduction_32
happyReduction_32 happy_x_3
	happy_x_2
	happy_x_1
	 =  case happyOut20 happy_x_2 of { happy_var_2 -> 
	happyIn24
		 (happy_var_2
	)}

happyNewToken action sts stk [] =
	happyDoAction 15# notHappyAtAll action sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = happyDoAction i tk action sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 1#;
	PT _ (TS _ 2) -> cont 2#;
	PT _ (TS _ 3) -> cont 3#;
	PT _ (TS _ 4) -> cont 4#;
	PT _ (TS _ 5) -> cont 5#;
	PT _ (TS _ 6) -> cont 6#;
	PT _ (TS _ 7) -> cont 7#;
	PT _ (TS _ 8) -> cont 8#;
	PT _ (TS _ 9) -> cont 9#;
	PT _ (TS _ 10) -> cont 10#;
	PT _ (TS _ 11) -> cont 11#;
	PT _ (TV happy_dollar_dollar) -> cont 12#;
	PT _ (TI happy_dollar_dollar) -> cont 13#;
	_ -> cont 14#;
	_ -> happyError' (tk:tks)
	}

happyError_ tk tks = happyError' (tk:tks)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = (thenM)
happyReturn :: () => a -> Err a
happyReturn = (returnM)
happyThen1 m k tks = (thenM) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (returnM) a
happyError' :: () => [(Token)] -> Err a
happyError' = happyError

pPmemory tks = happySomeParser where
  happySomeParser = happyThen (happyParse 0# tks) (\x -> happyReturn (happyOut15 x))

pPRule tks = happySomeParser where
  happySomeParser = happyThen (happyParse 1# tks) (\x -> happyReturn (happyOut16 x))

pListPRule tks = happySomeParser where
  happySomeParser = happyThen (happyParse 2# tks) (\x -> happyReturn (happyOut17 x))

pListExp tks = happySomeParser where
  happySomeParser = happyThen (happyParse 3# tks) (\x -> happyReturn (happyOut18 x))

pExp tks = happySomeParser where
  happySomeParser = happyThen (happyParse 4# tks) (\x -> happyReturn (happyOut19 x))

pExp1 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 5# tks) (\x -> happyReturn (happyOut20 x))

pExp2 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 6# tks) (\x -> happyReturn (happyOut21 x))

pExp3 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 7# tks) (\x -> happyReturn (happyOut22 x))

pExp4 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 8# tks) (\x -> happyReturn (happyOut23 x))

pExp5 tks = happySomeParser where
  happySomeParser = happyThen (happyParse 9# tks) (\x -> happyReturn (happyOut24 x))

happySeq = happyDontSeq


returnM :: a -> Err a
returnM = return

thenM :: Err a -> (a -> Err b) -> Err b
thenM = (>>=)

happyError :: [Token] -> Err a
happyError ts =
  Bad $ "syntax error at " ++ tokenPos ts ++ 
  case ts of
    [] -> []
    [Err _] -> " due to lexer error"
    _ -> " before " ++ unwords (map (id . prToken) (take 4 ts))

myLexer = tokens
{-# LINE 1 "templates\GenericTemplate.hs" #-}
{-# LINE 1 "templates\\GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 1 "templates\\GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 30 "templates\\GenericTemplate.hs" #-}


data Happy_IntList = HappyCons Happy_GHC_Exts.Int# Happy_IntList





{-# LINE 51 "templates\\GenericTemplate.hs" #-}

{-# LINE 61 "templates\\GenericTemplate.hs" #-}

{-# LINE 70 "templates\\GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is 0#, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept 0# tk st sts (_ `HappyStk` ans `HappyStk` _) =
	happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
	(happyTcHack j (happyTcHack st)) (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
	= {- nothing -}


	  case action of
		0#		  -> {- nothing -}
				     happyFail i tk st
		-1# 	  -> {- nothing -}
				     happyAccept i tk st
		n | (n Happy_GHC_Exts.<# (0# :: Happy_GHC_Exts.Int#)) -> {- nothing -}

				     (happyReduceArr Happy_Data_Array.! rule) i tk st
				     where rule = (Happy_GHC_Exts.I# ((Happy_GHC_Exts.negateInt# ((n Happy_GHC_Exts.+# (1# :: Happy_GHC_Exts.Int#))))))
		n		  -> {- nothing -}


				     happyShift new_state i tk st
				     where (new_state) = (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#))
   where (off)    = indexShortOffAddr happyActOffsets st
         (off_i)  = (off Happy_GHC_Exts.+# i)
	 check  = if (off_i Happy_GHC_Exts.>=# (0# :: Happy_GHC_Exts.Int#))
			then (indexShortOffAddr happyCheck off_i Happy_GHC_Exts.==#  i)
			else False
         (action)
          | check     = indexShortOffAddr happyTable off_i
          | otherwise = indexShortOffAddr happyDefActions st

{-# LINE 130 "templates\\GenericTemplate.hs" #-}


indexShortOffAddr (HappyA# arr) off =
	Happy_GHC_Exts.narrow16Int# i
  where
        i = Happy_GHC_Exts.word2Int# (Happy_GHC_Exts.or# (Happy_GHC_Exts.uncheckedShiftL# high 8#) low)
        high = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr (off' Happy_GHC_Exts.+# 1#)))
        low  = Happy_GHC_Exts.int2Word# (Happy_GHC_Exts.ord# (Happy_GHC_Exts.indexCharOffAddr# arr off'))
        off' = off Happy_GHC_Exts.*# 2#





data HappyAddr = HappyA# Happy_GHC_Exts.Addr#




-----------------------------------------------------------------------------
-- HappyState data type (not arrays)

{-# LINE 163 "templates\\GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state 0# tk st sts stk@(x `HappyStk` _) =
     let (i) = (case Happy_GHC_Exts.unsafeCoerce# x of { (Happy_GHC_Exts.I# (i)) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((happyInTok (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) sts of
	 sts1@((HappyCons (st1@(action)) (_))) ->
        	let r = fn stk in  -- it doesn't hurt to always seq here...
       		happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
        happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))
       where (sts1@((HappyCons (st1@(action)) (_)))) = happyDrop k (HappyCons (st) (sts))
             drop_stk = happyDropStk k stk

happyMonad2Reduce k nt fn 0# tk st sts stk
     = happyFail 0# tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
       happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))
       where (sts1@((HappyCons (st1@(action)) (_)))) = happyDrop k (HappyCons (st) (sts))
             drop_stk = happyDropStk k stk

             (off) = indexShortOffAddr happyGotoOffsets st1
             (off_i) = (off Happy_GHC_Exts.+# nt)
             (new_state) = indexShortOffAddr happyTable off_i




happyDrop 0# l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n Happy_GHC_Exts.-# (1# :: Happy_GHC_Exts.Int#)) t

happyDropStk 0# l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Happy_GHC_Exts.-# (1#::Happy_GHC_Exts.Int#)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   {- nothing -}
   happyDoAction j tk new_state
   where (off) = indexShortOffAddr happyGotoOffsets st
         (off_i) = (off Happy_GHC_Exts.+# nt)
         (new_state) = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery (0# is the error token)

-- parse error if we are in recovery and we fail again
happyFail  0# tk old_st _ stk =
--	trace "failing" $ 
    	happyError_ tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  0# tk old_st (HappyCons ((action)) (sts)) 
						(saved_tok `HappyStk` _ `HappyStk` stk) =
--	trace ("discarding state, depth " ++ show (length stk))  $
	happyDoAction 0# tk action sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (action) sts stk =
--      trace "entering error recovery" $
	happyDoAction 0# tk action sts ( (Happy_GHC_Exts.unsafeCoerce# (Happy_GHC_Exts.I# (i))) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions


happyTcHack :: Happy_GHC_Exts.Int# -> a -> a
happyTcHack x y = y
{-# INLINE happyTcHack #-}


-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--	happySeq = happyDoSeq
-- otherwise it emits
-- 	happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
