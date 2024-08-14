import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Compactification.OnePoint
import Mathlib.Topology.Instances.Real
import Mathlib.Algebra.Order.Group.Unbundled.Abs

open scoped LinearAlgebra.Projectivization OnePoint
open Projectivization

/-

This file is focused on proving `The_y__p_are_all_the_solutions` only.
-/

def mul_div_mul_cancel {a b c : ℝ} (h : a ≠ 0) :
  (a*b)/(a*c) = b/c := by ring_nf;field_simp

instance mys: Setoid ({v : Fin 2 → ℝ // v ≠ 0}) :=
  projectivizationSetoid ℝ (Fin 2 → ℝ)

lemma y_lemma (a b : { v // v ≠ 0 })
  (h : @HasEquiv.Equiv { v // v ≠ 0 } instHasEquivOfSetoid a b) :
  (fun u : {v : Fin 2 → ℝ // v ≠ 0} ↦ λ x ↦ (u.1 0 + u.1 1 * Real.exp x) / (u.1 0 - u.1 1 * Real.exp x)) a =
  (fun u x ↦ (u.1 0 + u.1 1 * Real.exp x) / (u.1 0 - u.1 1 * Real.exp x)) b
:= by
      simp only [Fin.isValue]
      ext x
      obtain ⟨y,hy⟩ := h
      rw [← hy]
      simp only [Pi.smul_apply]
      have : y • b.1 0 = y.1 * b.1 0 := rfl
      rw [this]
      have : y • b.1 1 = y.1 * b.1 1 := rfl
      rw [this]
      have : y *  b.1 0 + y * b.1 1 * Real.exp x
           = y * (b.1 0 +     b.1 1 * Real.exp x) := by ring_nf
      rw [this]
      have : y *  b.1 0 - y * b.1 1 * Real.exp x
           = y * (b.1 0 -     b.1 1 * Real.exp x) := by ring_nf
      rw [this, mul_div_mul_cancel (Units.ne_zero y)]

noncomputable def y_ (p : ℙ ℝ (Fin 2 → ℝ)) : (ℝ → ℝ) := @Quotient.lift
    { v : Fin 2 → ℝ // v ≠ 0} (ℝ → ℝ)
    (projectivizationSetoid ℝ (Fin 2 → ℝ))
    (λ u : { v : Fin 2 → ℝ // v ≠ 0} ↦
      λ x : ℝ ↦ ((u.1 0) + (u.1 1) * Real.exp x)
              / ((u.1 0) - (u.1 1) * Real.exp x))
    y_lemma p


lemma indomain_welldefined_on_projective (t : ℝ) (a b : { v // v ≠ 0 }) (h : mys.r a b) :
    (fun u ↦ u.1 0 - u.1 1 * Real.exp t ≠ 0) a
  = (fun u ↦ u.1 0 - u.1 1 * Real.exp t ≠ 0) b
:= by
      simp only [ne_eq, Fin.isValue, eq_iff_iff]
      obtain ⟨c,hc⟩ := h
      simp at hc
      rw [← hc]
      simp
      constructor
      · intro h₀
        contrapose h₀
        simp_all
        show  c * b.1 0 - c * b.1 1 * Real.exp t = 0
        suffices c * (b.1 0 - b.1 1 * Real.exp t) = 0 by
          rw [← this]
          ring_nf
        rw [h₀]
        simp
      · intro h₀
        contrapose h₀
        simp_all
        have : c * b.1 0 - c * b.1 1 * Real.exp t = 0 := h₀
        have h₁: c * (b.1 0 - b.1 1 * Real.exp t) = 0 := by
          rw [← this]
          ring_nf
        have : c.1 ≠ 0 := Units.ne_zero c
        exact (Units.mul_right_eq_zero c).mp h₁

noncomputable def indomain (p : ℙ ℝ (Fin 2 → ℝ)) (t : ℝ) : Prop := Quotient.lift
    (λ u : { v : Fin 2 → ℝ // v ≠ 0} ↦ u.1 0 - u.1 1 * Real.exp t ≠ 0)
    (indomain_welldefined_on_projective _) p

lemma Stewart_Example_9_1_1'_HasDerivAt (u v : ℝ)
  (t : ℝ) (htc : u - v * Real.exp t ≠ 0)
  :
      let y := λ t ↦ (u + v * Real.exp t) / (u - v * Real.exp t)
      HasDerivAt y ((1/2) * ((y t)^2 -1)) t := by
  have Q := @HasDerivAt.div ℝ _ t ℝ _ _
        (λ t ↦ (u + v * Real.exp t)) (λ t ↦ (u - v * Real.exp t))
        (v * Real.exp t) (- v * Real.exp t)
        (by
          refine HasDerivAt.const_add u ?hf
          refine HasDerivAt.const_mul v ?hf.hd
          exact Real.hasDerivAt_exp t
        ) (by
          simp
          refine HasDerivAt.const_sub u ?hf
        ) htc
  simp
  simp at Q
  have : ((v * Real.exp t * (u - v * Real.exp t) + (u + v * Real.exp t) * (v * Real.exp t)) / (u - v * Real.exp t) ^ 2)
    = (2⁻¹ * ((u + v * Real.exp t) ^ 2 / (u - v * Real.exp t) ^ 2 - 1)) := by
    field_simp
    rw [pow_two]
    ring_nf
  rw [← this]
  simp at this
  exact Q


theorem projectively_parametrized_ODE_solution_HasDerivAt
  {p : ℙ ℝ (Fin 2 → ℝ)} {t : ℝ} :
  indomain p t → HasDerivAt (y_ p) ((1/2) * ((y_ p t)^2 -1)) t  := by
  unfold y_
  simp
  exact @Quotient.ind ({v : Fin 2 → ℝ // v ≠ 0}) mys
    (
      λ p ↦ indomain p t →
      HasDerivAt
      (Quotient.lift (fun u x ↦ (u.1 0 + u.1 1 * Real.exp x) / (u.1 0 - u.1 1 * Real.exp x)) y_lemma p)
      (2⁻¹ * (Quotient.lift (fun u x ↦ (u.1 0 + u.1 1 * Real.exp x) / (u.1 0 - u.1 1 * Real.exp x)) y_lemma p t ^ 2 - 1))
      t
    )
    (by
      intro p
      simp
      intro htc'
      let Q := @Stewart_Example_9_1_1'_HasDerivAt (p.1 0) (p.1 1) t htc'
      simp at Q
      exact Q
    ) p



-- This is to be used to show there's a unique ODE solution through (t₀,y₀)
-- where e = Real.exp t₀.
lemma pass_through (y₀ : ℝ) {e : ℝ} (he : e ≠ 0) :
  ∃ p : { v : Fin 2 → ℝ // v ≠ 0},
  y₀ = (p.1 0 + p.1 1 * e) / (p.1 0 - p.1 1 * e) := by
    by_cases H : y₀ = 1
    · subst H
      simp only [ne_eq, Fin.isValue, Subtype.exists, exists_prop]
      use ![1,0]
      simp
    · use ⟨![e * (1 + y₀) / (1 - y₀),-1],by simp⟩
      simp
      have h₀: e * (1 + y₀) / (1 - y₀) + e ≠ 0 := by
        intro hc
        have : (e * (1 + y₀) / (1 - y₀) + e) * (1 - y₀) = 0 * (1 - y₀) := by
          rw [hc]
        rw [right_distrib,div_mul,div_self,div_one,zero_mul] at this
        · simp_all;
          rw [← left_distrib] at this
          have : 1 + y₀ + (1-y₀) = 0 := eq_zero_of_ne_zero_of_mul_left_eq_zero he this
          ring_nf at this
          simp_all
        · contrapose H; simp_all
      have h₁: 1 - y₀ ≠ 0 := by
        contrapose H
        simp_all
        linarith
      rw [← eq_div_of_mul_eq h₀]
      suffices (y₀ * (e * (1 + y₀) / (1 - y₀) + e)) * (1 - y₀)
             = (e * (1 + y₀) / (1 - y₀) + -e) * (1 - y₀) by
        rw [mul_eq_mul_right_iff] at this
        tauto
      rw [mul_assoc, right_distrib, right_distrib]
      have : e * (1 + y₀) / (1 - y₀) * (1 - y₀) = e * (1 + y₀) := by
        suffices e * ((1 + y₀) / (1 - y₀) * (1 - y₀)) = e * (1 + y₀) by
          rw [← this]
          field_simp
        rw [div_mul_cancel₀ (1 + y₀) h₁]
      rw [this]
      ring_nf



theorem LipschitzSquare {a b : Real}: LipschitzOnWith (max |a|.toNNReal |b|.toNNReal)
  (λ x : ℝ ↦ (1/2) * (x^2 - 1)) (Set.Icc a b) := by
  intro x hx y hy
  repeat rw [edist_dist]
  simp only [one_div, Real.toNNReal_abs, ENNReal.coe_max]
  have : max ↑(Real.nnabs a) ↑(Real.nnabs b) * ENNReal.ofReal (dist x y)
    = ENNReal.ofReal (max ↑(Real.nnabs a) ↑(Real.nnabs b) *  (dist x y)) := by
      simp
      have : max ↑(Real.nnabs a) ↑(Real.nnabs b)
        = ENNReal.ofReal (max ↑(Real.nnabs a) ↑(Real.nnabs b)) := by
        simp
        by_cases H : (|a|:ℝ) ≤ |b|
        repeat rw [max_eq_right]
        simp_all
        symm
        refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
        exact ENNReal.ofReal_ne_top
        exact ENNReal.coe_ne_top
        refine ENNReal.toReal_ofReal ?_
        exact abs_nonneg b
        tauto;simp;exact H;
        have h₀: |b| ≤ |a| := le_of_not_ge H
        repeat rw [max_eq_left]
        simp_all
        symm
        refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
        exact ENNReal.ofReal_ne_top
        exact ENNReal.coe_ne_top
        refine ENNReal.toReal_ofReal ?_
        exact abs_nonneg _
        exact h₀;simp;exact h₀
      rw [this]
      rw [← ENNReal.ofReal_mul]
      congr
      positivity
  rw [this]
  refine ENNReal.ofReal_le_ofReal_iff'.mpr ?_
  left
  have h₀: dist (2⁻¹ * (x ^ 2 - 1)) (2⁻¹ * (y ^ 2 - 1)) =
    2⁻¹ * dist ((x ^ 2 - 1)) ((y ^ 2 - 1)) := by
      have (u v w : ℝ) (h : 0 ≤ u) : u * dist v w = dist (u*v) (u*w) := by
        show u * |v-w| = |u*v - u*w|
        suffices |u| * |v-w| = |u*v - u*w| by
          rw [← this]
          simp
          left;exact Eq.symm (abs_of_nonneg h)
        rw [← abs_mul]
        ring_nf
      let Q := @this 2⁻¹ (x^2-1) (y^2-1) (by simp)
      rw [Q]
  rw [h₀]
  rw [
    show dist (x^2-1) (y^2-1) = dist (x^2) (y^2) by simp,
    show dist (x^2) (y^2) = |x^2 - (y^2)| by rfl,
    show dist x y = |x - y| by rfl
  ]
  suffices 2 * (2⁻¹ * |x ^ 2 - y ^ 2|) ≤ 2 * (max ↑(Real.nnabs a) ↑(Real.nnabs b) * |x - y|) by
    apply (inv_mul_le_iff _).mpr
    simp at this
    tauto
    simp
  simp
  rw  [show |x^2 -(y^2)| = |x+y| * |x-y| by
    rw [← abs_mul];congr;ring_nf]
  by_cases H : |x-y|=0
  · have : x-y=0 := abs_eq_zero.mp H
    have : x = y := by linarith
    subst this
    simp
  · rw [← mul_assoc]
    suffices  |x + y| ≤ 2 * ↑(max |a| |b|) by
      apply mul_le_mul this
      repeat simp
    have g₀ : |x| ≤ max (|(a:ℝ)|) |b| := abs_le_max_abs_abs hx.1 hx.2
    have g₁ : |y| ≤ max (|(a:ℝ)|) |b| := abs_le_max_abs_abs hy.1 hy.2

    calc _ ≤ |x| + |y| := abs_add x y
         _ ≤ _ := by linarith


def only_solution_through (t₀ y₀ : ℝ) (z_ : ℙ ℝ (Fin 2 → ℝ) → ℝ → ℝ) (p : ℙ ℝ (Fin 2 → ℝ)) : Prop :=
z_ p t₀ = y₀
∧ ∀ y : ℝ → ℝ, y t₀ = y₀ → ∀ i₀ i₁ j₀ j₁ : ℝ,
  let I := Set.Ioo i₀ i₁
  (hJ    : ∀ t ∈ Set.Ioo i₀ i₁, y    t ∈ Set.Ioo j₀ j₁) →
  (adhoc₂: ∀ t ∈ Set.Ioo i₀ i₁, z_ p t ∈ Set.Icc j₀ j₁) →
  (adhoc: ContinuousOn (z_ p) (Set.Icc i₀ i₁)) →
  (h₂   : ContinuousOn  y     (Set.Icc i₀ i₁)) →
  (H: ∀ t ∈ I, indomain p t) →
  (ht₀ : t₀ ∈ I) →
  (h₃ : ∀ t ∈ Set.Ioo i₀ i₁, HasDerivAt y (1 / 2 * (y (t)^ 2 - 1)) t) →
  ∀ t ∈ I, y t = z_ p t

/- Parametrizes all solutions to y'=(1/2)(y^2-1) using the projective real line. -/
/- We could also use the unit circle. -/
theorem The_y__p_are_all_the_solutions (t₀ y₀ : ℝ):
∃ p, only_solution_through t₀ y₀ y_ p := by
  obtain ⟨p,hp⟩ := pass_through y₀ (Real.exp_ne_zero t₀)
  use mk' ℝ p
  constructor
  · rw [hp]
    rfl
  · intro y h₀ i₀ i₁ j₀ j₁ I hJ adhoc₂ adhoc h₂ H ht₀ h₃ t ht
    exact ODE_solution_unique_of_mem_Icc
      (λ _ ↦ LipschitzSquare) ht₀ h₂ h₃
      (by intro _ ht; apply Set.Ioo_subset_Icc_self; apply hJ; exact ht)
      adhoc
      (λ t ht' ↦ projectively_parametrized_ODE_solution_HasDerivAt (H t ht'))
      adhoc₂
      (Eq.trans h₀ hp)
      (Set.Ioo_subset_Icc_self ht)
