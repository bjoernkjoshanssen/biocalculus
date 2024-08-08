import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

-- Calculate the derivative of (1/2)x - 1/3
lemma one : deriv (λ x : ℝ ↦ (1/2)*x - 1/3) = λ x ↦ 1/2 := by
  ext x
  have := @deriv_sub ℝ _ ℝ _ _ (λ x ↦ (1/2)*x) (λ x ↦ 1/3) x
  rw [this]
  · let Q := @deriv_const_mul ℝ _ x ℝ _ _ id (1/2) differentiableAt_id
    simp at *
    rw [deriv_id] at Q
    simp at Q;tauto
  · let Q := @DifferentiableAt.mul_const ℝ _ ℝ _ _ x ℝ _ _ id
      differentiableAt_id (1/2)
    have : (λ x : ℝ ↦ x * (1/2)) = (λ x ↦ (1/2) * x) := by ext x;simp;ring
    rw [← this]
    tauto
  · exact differentiableAt_const (1 / 3)
