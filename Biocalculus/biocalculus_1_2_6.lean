import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals



def family (m : ℝ) : ℝ → ℝ := λ x ↦ 1 + m * (x + 3)

example (m : ℝ) : family m (-3) = 1 := by
  unfold family
  simp only [add_left_neg, mul_zero, add_zero]
