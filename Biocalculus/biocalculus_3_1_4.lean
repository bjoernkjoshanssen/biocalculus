import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

-- Calculate the derivative of x^3 - x at 1
lemma one : deriv (λ x : ℝ ↦ x^3 - x) = λ x ↦ 3 * x^2 - 1 := by
  ext x
  have := @deriv_sub ℝ _ ℝ _ _ (λ x ↦ x^3) id x
    (differentiableAt_pow 3) differentiableAt_id
  simp at *

example : deriv (λ x : ℝ ↦ x^3 - x) 1 = 2 := by
  rw [one]
  simp
  ring
