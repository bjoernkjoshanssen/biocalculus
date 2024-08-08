import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

-- Newton's method:
noncomputable def newton (f : ℝ → ℝ) (x₀ : ℝ) : ℕ → ℝ := λ n ↦ match n with
|0 => x₀
|Nat.succ k => newton f x₀ k - (f (newton f x₀ k)) / (deriv f (newton f x₀ k))

example : newton (λ x ↦ x^2) 1 1 = 1/2 := by
  unfold newton
  simp
  show 1 - 1 ^ 2 / (2 * 1) = 2⁻¹
  ring_nf
