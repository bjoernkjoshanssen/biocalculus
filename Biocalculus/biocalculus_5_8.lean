import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

example : ∫ x in Set.Ioi (0:ℝ), Real.exp (-x) = 1 := by
  rw [integral_exp_neg_Ioi]
  simp
