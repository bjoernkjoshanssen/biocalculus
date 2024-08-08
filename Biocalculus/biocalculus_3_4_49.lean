import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp


example (f g : ℝ → ℝ)
  (h₀ : f 5 =  1) (h₁ : deriv f 5 = 6)
  (h₂ : g 5 = -3) (h₃ : deriv g 5 = 2) :
  deriv (f * g) 5 = -16 := by
    show deriv (λ x ↦ f x * g x) 5 = -16
    rw [deriv_mul]
    · rw [h₁,h₂,h₃,h₀]; ring
    · apply differentiableAt_of_deriv_ne_zero
      rw [h₁];simp
    · apply differentiableAt_of_deriv_ne_zero
      rw [h₃];simp
