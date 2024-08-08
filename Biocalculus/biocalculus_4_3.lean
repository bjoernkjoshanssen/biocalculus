import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.Calculus.LHopital

-- This shows that the proper definition of a limit should use `nhdsWithin` not `nhds`.
example : Filter.Tendsto (λ x : ℝ ↦ Real.sin x / x) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
  apply deriv.lhopital_zero_nhds
  apply Filter.eventually_of_forall
  · exact fun x ↦ Real.differentiableAt_sin
  apply Filter.eventually_of_forall
  · simp
  apply Continuous.tendsto'
  · exact Real.continuous_sin
  · exact Real.sin_zero
  exact fun ⦃U⦄ a ↦ a
  rw [Real.deriv_sin]
  simp
  apply Continuous.tendsto'
  · exact Real.continuous_cos
  · exact Real.cos_zero
