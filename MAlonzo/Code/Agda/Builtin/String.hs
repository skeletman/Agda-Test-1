{-# LANGUAGE EmptyDataDecls, EmptyCase, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, RankNTypes,
             PatternSynonyms, OverloadedStrings #-}
module MAlonzo.Code.Agda.Builtin.String where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

name6 = "Agda.Builtin.String.String"
type T6 = Data.Text.Text
d6
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Builtin.String.String"
name10 = "Agda.Builtin.String.primStringUncons"
d10 = Data.Text.uncons
name12 = "Agda.Builtin.String.primStringToList"
d12 = Data.Text.unpack
name14 = "Agda.Builtin.String.primStringFromList"
d14 = Data.Text.pack
name16 = "Agda.Builtin.String.primStringAppend"
d16
  = ((Data.Text.append) :: Data.Text.Text->Data.Text.Text->Data.Text.Text)
name18 = "Agda.Builtin.String.primStringEquality"
d18
  = (\ x y -> ((==) :: Data.Text.Text -> Data.Text.Text -> Bool) ( x) ( y))
name20 = "Agda.Builtin.String.primShowChar"
d20 = (Data.Text.pack . show :: Char -> Data.Text.Text)
name22 = "Agda.Builtin.String.primShowString"
d22 = (Data.Text.pack . show :: Data.Text.Text -> Data.Text.Text)
name24 = "Agda.Builtin.String.primShowNat"
d24 = (Data.Text.pack . show :: Integer -> Data.Text.Text)
