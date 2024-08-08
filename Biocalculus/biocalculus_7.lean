import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.ODE.Gronwall

-- Differential equations:

lemma one (f : ℝ → ℝ) (h₀ : Differentiable ℝ f) (h : deriv f = (λ x ↦ 0)) :
  ∃ c, ∀ x, f x = c := by
  use f 0
  intro x
  apply is_const_of_deriv_eq_zero
  exact h₀
  intro x
  rw [h]

-- General solution to the differential equation f' = 0:
lemma two (f : ℝ → ℝ) (h₀ : Differentiable ℝ f) :
  deriv f = (λ x ↦ 0) ↔ ∃ c, ∀ x, f x = c := by
  constructor
  intro h
  apply one
  exact h₀
  exact h
  intro h
  let Q := @deriv_const ℝ _ ℝ _ _
  obtain ⟨c,hc⟩ := h
  have : f = (λ _ ↦ c) := (Set.eqOn_univ f fun _ ↦ c).mp fun ⦃x⦄ _ ↦ hc x
  rw [this]
  ext x
  rw [Q x]


-- General solution to the differential equation f' = g':
example (f g : ℝ → ℝ) (h₀ : Differentiable ℝ f)
  (h₁ : Differentiable ℝ g) :
  deriv f = deriv g ↔ ∃ c, ∀ x, f x = g x + c := by
  have h₂ : Differentiable ℝ (f-g) := Differentiable.sub h₀ h₁
  constructor
  · intro h
    have : deriv (f-g) = 0 := by
      ext x
      let Q := @deriv_sub ℝ _ ℝ _ _ f g x (h₀ x) (h₁ x);
      show deriv (fun y ↦ f y - g y) x = 0
      rw [Q, h]
      simp
    have : ∃ c, f-g = (λ _ ↦ c) := by
      let ⟨c,hc⟩ := (@two (f-g) h₂).mp this
      use c; ext x; apply hc
    obtain ⟨c,hc⟩ := this
    use c;intro x;simp at hc
    suffices f x - g x = c by linarith
    show (f - g) x = c
    rw [hc]
  · intro ⟨c,hc⟩
    have : f = (λ x ↦ g x + c) := (Set.eqOn_univ f fun x ↦ g x + c).mp fun ⦃x⦄ a ↦ hc x
    rw [this]
    simp


lemma should_follow (f : ℝ → ℝ) (t : ℝ) (h : deriv f t ≠ 0) :
  HasDerivWithinAt f (deriv f t) (Set.Ici t) t := by
    refine HasDerivAt.hasDerivWithinAt ?h
    refine DifferentiableAt.hasDerivAt ?h.h
    exact differentiableAt_of_deriv_ne_zero h

-- We can show y=Ce^x satisfies y'=y, but to show it's the only solution would
-- require that fancy theorem about ODEs.
-- Unique solution to y' = y
example (C : ℝ) : ∀ t ∈ Set.Ico 0 1,
  HasDerivWithinAt (λ x ↦ C * Real.exp x)
                  ((λ x ↦ C * Real.exp x) t) (Set.Ici t) t := by
  by_cases H : C = 0
  · subst H
    simp
    intro t _ _
    exact hasDerivWithinAt_const t (Set.Ici t) 0

  intro t _
  have : deriv (λ x ↦ C * Real.exp x) = (λ x ↦ C * Real.exp x) := by
    simp
  nth_rewrite 2 [← this]

  apply should_follow
  rw [this]
  simp
  tauto

example (f g : ℝ → ℝ)
  (h₀ : ContinuousOn f (Set.Icc 0 1))
  (h₁ : ContinuousOn g (Set.Icc 0 1))
  (h₂ :  ∀ t ∈ Set.Ico 0 1, HasDerivWithinAt f (f t) (Set.Ici t) t)
  (h₃ :  ∀ t ∈ Set.Ico 0 1, HasDerivWithinAt g (g t) (Set.Ici t) t)
  (h₄ : f 0 = g 0)
: Set.EqOn f g (Set.Icc 0 1) := by
  let Q := @ODE_solution_unique ℝ _ _ (λ x y ↦ y) 1 f g 0 1
    (by intro x;exact Isometry.lipschitz fun x1 ↦ congrFun rfl) h₀ h₂ h₁ h₃ h₄
  tauto
