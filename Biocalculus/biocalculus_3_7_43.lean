import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

example : deriv (λ x ↦ (Real.arctan x)^2) = λ x ↦ 2 * Real.arctan x / (1 + x^2) := by
  ext x
  show deriv ((λ x ↦ x^2) ∘ Real.arctan) x = 2 * Real.arctan x / (1 + x^2)
  rw [deriv.comp, deriv_arctan]
  simp
  ring_nf
  · exact differentiableAt_id'
  · exact differentiableAt_pow 2
  · exact Real.differentiableAt_arctan x
