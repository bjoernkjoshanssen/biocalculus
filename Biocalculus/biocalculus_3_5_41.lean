import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

example : deriv (λ x : ℝ ↦ (1 + 2*x)^10) 0 = 20 := by
  show deriv ((λ x ↦ x^10) ∘ (λ x ↦ 1 + 2*x)) 0 = 20
  rw [deriv.comp]
  · simp
    rw [deriv_const_mul]
    simp
    ring_nf
    exact differentiableAt_id'
  · simp
  · refine DifferentiableAt.const_add ?hh.hf 1
    refine Differentiable.differentiableAt ?hh.hf.h
    apply Differentiable.const_mul
    exact differentiable_id'
