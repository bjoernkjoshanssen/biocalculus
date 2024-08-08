import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

def f : ℝ → ℝ := λ x ↦ x^2

lemma one (a b : ℝ) (h : a < b) (h₀ : 0 ≤ a) : f a < f b := by
  unfold f
  rw [← lt_add_neg_iff_lt]
  have : b^2 + -a^2 = (b-a) * (b+a) := by ring_nf
  rw [this]
  apply Real.mul_pos
  linarith; linarith

lemma two (a b : ℝ) (h : a < b) (h₀ : b ≤ 0) : f b < f a := by
  unfold f
  have h₁: -b < -a := by linarith
  have h₂: 0 ≤ -b := by linarith
  let Q := one (-b) (-a) h₁ h₂
  unfold f at Q
  simp at Q
  tauto

example : StrictMonoOn Real.sin (Set.Icc 0 (Real.pi/2)) := by
  apply strictMonoOn_of_deriv_pos
  · apply convex_Icc
  · exact Real.continuousOn_sin
  · intro x hx
    rw [deriv_sin]
    · simp;simp at hx;refine Real.cos_pos_of_mem_Ioo ?hf'.hx;
      simp;constructor;linarith;tauto
    · simp

example : StrictMonoOn f (Set.Ici 0) := pow_left_strictMonoOn (by simp)

example : StrictAntiOn f (Set.Iic 0) := by
  intro a _ b hb h
  apply two
  exact h
  exact hb

lemma three (g : ℝ → ℝ) (A B : Set ℝ) (u v : ℝ) (h : {u,v} ⊆ A ∩ B)
  (h₀ : StrictMonoOn g A ∧ StrictAntiOn g B) : ¬ u < v := by
    by_contra hc
    have h₁: g u < g v := by
      apply h₀.1
      · simp at h
        tauto
      · simp at h
        apply h.1
        simp
      · tauto
    have h₂: g v < g u := by
      apply h₀.2
      · simp at h
        tauto
      · simp at h
        apply h.2
        simp
      · tauto
    have : g u < g u := gt_trans h₂ h₁
    exact (lt_self_iff_false (g u)).mp this

-- Sets of increase and sets of decrease must be almost disjoint:
lemma four (g : ℝ → ℝ) (A B : Set ℝ) (u v : ℝ) (h : {u,v} ⊆ A ∩ B)
  (h₀ : StrictMonoOn g A ∧ StrictAntiOn g B) : u = v := by
  have h' : {v, u} ⊆ A ∩ B := by
    intro w hw
    simp at *
    cases hw
    subst ‹w=v›
    constructor
    · apply h.1
      simp
    · apply h.2
      simp
    subst ‹w=u›
    constructor
    · apply h.1
      simp
    · apply h.2
      simp
  let Q₀ := three g A B u v h h₀
  let Q₁ := three g A B v u h' h₀
  linarith
