import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals

noncomputable def f₀ : { x : ℝ // 0 < x} → ℝ := λ x ↦ Real.log x.1

example : Function.LeftInverse (λ x ↦ ⟨Real.exp x, Real.exp_pos x⟩) f₀ := by
  unfold Function.LeftInverse f₀
  intro x
  simp
  congr
  refine Real.exp_log ?e_val.hx
  exact x.2

example : Function.RightInverse (λ x ↦ ⟨Real.exp x, Real.exp_pos x⟩) f₀ := by
  unfold Function.RightInverse f₀
  intro x
  simp

noncomputable def f : { x : ℝ // -3 < x} → ℝ := λ x ↦ Real.log (x.1 + 3)

example : Function.LeftInverse (λ x ↦ ⟨(Real.exp x) - 3, by
  field_simp;exact Real.exp_pos x
⟩) f := by
  unfold Function.LeftInverse f
  intro x
  simp
  congr
  rw [Real.exp_log]
  ring
  let Q := x.2
  linarith

example : Function.RightInverse (λ x ↦ ⟨Real.exp x - 3, by field_simp;exact Real.exp_pos x⟩) f := by
  unfold Function.RightInverse f
  intro x
  simp
