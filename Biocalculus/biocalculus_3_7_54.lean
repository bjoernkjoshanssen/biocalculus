import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

open Real

example : deriv log = (λ x ↦ 1/x) := by
  ext x
  rw [deriv_log]
  simp only [one_div]

example : deriv (λ x : ℝ ↦ x^8) = (λ x ↦ 8 * x^7) := by
  ext x
  apply deriv_pow

-- Note that Real.log is ln |x|
example (x : ℝ) (hx : x ≠ 0) :
  deriv (λ x : ℝ ↦ x^8 * log x) x
    = 8 * x^7 * log x + x^7 := by
  rw [deriv_mul (differentiableAt_pow 8) (differentiableAt_log hx)]
  simp
  exact (mul_inv_eq_iff_eq_mul₀ hx).mpr rfl
