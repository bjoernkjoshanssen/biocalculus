import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.Calculus.FDeriv.Basic

example : IsLocalMax Real.sin (Real.pi/2) := by
  unfold IsLocalMax IsMaxFilter Filter.Eventually
  simp only [Real.sin_pi_div_two]
  have : {x | Real.sin x ≤ 1} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact Real.sin_le_one x
  rw [this]
  exact Filter.univ_mem

example : IsLocalMin (λ x ↦ x^2) 0 := by
  unfold IsLocalMin IsMinFilter Filter.Eventually
  simp

example : IsLocalMin (λ x ↦ Real.sqrt x) 0 := by
  unfold IsLocalMin IsMinFilter
  apply Filter.eventually_of_forall
  simp
  exact Real.sqrt_nonneg

example : IsLocalMin (λ x ↦ NNReal.sqrt x) 0 := by
  apply Filter.eventually_of_forall
  simp only [NNReal.sqrt_zero, zero_le, implies_true]

-- Since Real.sqrt is 0 on negative inputs, -1 is also a local min.
example : IsLocalMin (λ x ↦ Real.sqrt x) (-1) := by
  unfold IsLocalMin IsMinFilter
  apply Filter.eventually_of_forall
  simp
  intro x
  have : √(-1) = 0 := by refine Real.sqrt_eq_zero'.mpr ?_;simp
  rw [this]
  simp
  exact Real.sqrt_nonneg x

lemma Towards_2nd_derivative_test' (f : ℝ → ℝ) (a:ℝ) (h₀ : StrictMonoOn f (Set.Iic a))
  (h₁ : StrictAntiOn f (Set.Ici a)) :
  IsLocalMax f a := by
    unfold IsLocalMax IsMaxFilter Filter.Eventually
    rw [nhds_def, Filter.mem_iInf]
    exists {Set.univ}
    exists (Set.finite_singleton Set.univ)
    exists (fun _ ↦ Set.univ)
    simp only [Set.mem_setOf_eq, Filter.univ_mem, implies_true, Set.iInter_univ, true_and]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    unfold StrictMonoOn at h₀
    by_cases H : x < a
    · have : f x < f a := @h₀ x (Set.mem_Iic_of_Iio H) a (Set.right_mem_Iic) H
      exact le_of_lt this
    · by_cases H₀ : x = a
      · subst H₀;simp
      · have : a < x := by
          have : x ≥ a := le_of_not_lt H
          exact lt_of_le_of_ne this fun a_1 ↦ H₀ (id (Eq.symm a_1))
        have : f x < f a := @h₁ a (Set.left_mem_Ici) x (Set.mem_Ici_of_Ioi this) this
        exact le_of_lt this

lemma First_derivative_test' (f : ℝ → ℝ) (h : Continuous f) (a:ℝ)
  (h₀ :  ∀ x ∈ interior (Set.Iic a), 0 < deriv f x)
  (h₁ :  ∀ x ∈ interior (Set.Ici a), deriv f x < 0)
  : IsLocalMax f a := by
    let Q₀ := @strictMonoOn_of_deriv_pos (Set.Iic a)
      (convex_Iic a) f (Continuous.continuousOn h) h₀
    let Q₁ := @strictAntiOn_of_deriv_neg (Set.Ici a)
      (convex_Ici a) f (Continuous.continuousOn h) h₁
    apply Towards_2nd_derivative_test'
    tauto;tauto

example : IsLocalMax (λ x : ℝ ↦ -x^2) 0 := by
  apply First_derivative_test'
  · refine Continuous.comp' ?h.hg ?h.hf;exact continuous_neg;exact continuous_pow 2
  · intro x hx;simp;simp at hx;linarith
  · intro x hx;simp;simp at hx;linarith


def ofnotin (P : Prop) (T : Type) (t : T) (Q : P → Set T) (h :
  t ∉ ⨅ i : P, Q i) : P := by
    simp at h
    obtain ⟨h,_⟩ := h
    tauto

def of_not_in (P : Prop) (T : Type) (t : Set T) (Q : P → Filter T) (h :
  t ∉ ⨅ i : P, (Q i).sets) : P := by
    exact @ofnotin P (Set T) t (λ hP ↦ (Q hP).sets) h

-- Note ⨅ becomes ⨆ for filters! i.e. ⨆ = ∩
def of_notin (P : Prop) (T : Type) (t : Set T) (Q : P → Filter T)
  (h₀ :
  t ∉ ⨆ i : P, Q i) : P := by
  apply of_not_in P T t Q
  simp at h₀
  simp
  tauto





-- August 29, 2024.
lemma isLocalMax_of_mono_anti_Icc' (f : ℝ → ℝ) (a b : ℝ)
  (g₀ : a < b) (g₁ : b < c)
  (h₀ : MonotoneOn f (Set.Icc a b))
  (h₁ : AntitoneOn f (Set.Icc b c)) : IsLocalMax f b := by
    unfold IsLocalMax IsMaxFilter Filter.Eventually
    rw [nhds_def, Filter.mem_iInf]
    simp
    exists {Set.Ioo a c}, (Set.toFinite _), (fun _ ↦ Set.Ioo a c ∪ {x | f x ≤ f b})
    simp only [Set.mem_singleton_iff, forall_eq, Set.mem_Ioo, Set.iInter_iInter_eq_left]
    constructor
    apply Filter.mem_iInf_of_mem
    · simp_all only [Filter.mem_principal, Set.subset_union_left]
    · simp_all only [and_self, true_and]
      exact isOpen_Ioo
    · ext u
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, iff_or_self, and_imp]
      intro H₀ H₁
      by_cases G : u < b
      · apply h₀
        simp_all only [Set.mem_Icc]
        · constructor; repeat linarith
        · simp only [Set.mem_Icc, le_refl, and_true]
          linarith
        · linarith
      · by_cases J : u = b
        · subst J
          exact Preorder.le_refl (f u)
        · apply h₁
          simp only [Set.mem_Icc, le_refl, true_and]
          linarith
          simp
          · constructor; repeat linarith
          · linarith


lemma isLocalMax_of_mono_anti_Icc {f : ℝ → ℝ} {a b c : ℝ}
  (g₀ : a < b) (g₁ : b < c)
  (h₀ : StrictMonoOn f (Set.Icc a b))
  (h₁ : StrictAntiOn f (Set.Icc b c)) :
  IsLocalMax f b := by
    apply isLocalMax_of_mono_anti_Icc' f a b g₀ g₁
    exact StrictMonoOn.monotoneOn h₀;
    exact StrictAntiOn.antitoneOn h₁

lemma isLocalMax_of_mono_anti_Ici (f : ℝ → ℝ) (a b : ℝ)
  (g₀ : a < b)
  (h₀ : StrictMonoOn f (Set.Icc a b))
  (h₁ : StrictAntiOn f (Set.Ici b)) : IsLocalMax f b :=
    isLocalMax_of_mono_anti_Icc g₀ (by show b < b+1; linarith) h₀ (by
      intro _ hx _ hy hxy
      apply h₁
      exact Set.mem_of_mem_inter_left hx
      exact Set.mem_of_mem_inter_left hy
      exact hxy
    )

lemma first_derivative_test_strongest {f : ℝ → ℝ} (h : Continuous f) {a b c:ℝ}
  {g₀ : a < b} {g₁ : b < c}
  (hd : DifferentiableOn ℝ f (Set.Ioo a c))
  (h₀ :  ∀ x ∈ interior (Set.Icc a b), 0 ≤ deriv f x)
  (h₁ :  ∀ x ∈ interior (Set.Icc b c), deriv f x ≤ 0)
  -- The strongest version should only have 0 ≤ deriv f x, but assume differentiability in the interval
  : IsLocalMax f b := by
  apply isLocalMax_of_mono_anti_Icc'
  exact g₀;exact g₁;
  refine monotoneOn_of_deriv_nonneg ?h₀.hD ?h₀.hf ?h₀.hf' h₀;
  exact convex_Icc a b
  exact Continuous.continuousOn h
  intro x hx;unfold DifferentiableOn at hd;
  have Q := hd x (by simp_all;linarith)
  apply DifferentiableWithinAt.mono
  exact Q;simp;intro z hz; simp_all;linarith

  refine antitoneOn_of_deriv_nonpos ?h₁.hD ?h₁.hf ?h₁.hf' h₁
  exact convex_Icc b c
  exact Continuous.continuousOn h
  intro x hx;unfold DifferentiableOn at hd;
  have Q := hd x (by simp_all;linarith)
  apply DifferentiableWithinAt.mono
  exact Q;simp;intro z hz; simp_all;linarith

lemma first_derivative_test_strongest! {f : ℝ → ℝ} (h : Continuous f) {a b c:ℝ}
  {g₀ : a < b} {g₁ : b < c}
  (hd : DifferentiableOn ℝ f (Set.Ioo a c))
  (h₀ :  ∀ x ∈ Set.Ioo a b, 0 ≤ deriv f x)
  (h₁ :  ∀ x ∈ Set.Ioo b c, deriv f x ≤ 0)
  : IsLocalMax f b := by
  apply first_derivative_test_strongest h hd
  simp_all; intros; apply h₁; simp_all; repeat tauto


lemma first_derivative_test {f : ℝ → ℝ} (h : Continuous f) {a b c:ℝ}
  {g₀ : a < b} {g₁ : b < c}
  (h₀ :  ∀ x ∈ interior (Set.Icc a b), 0 < deriv f x)
  (h₁ :  ∀ x ∈ interior (Set.Icc b c), deriv f x < 0)
  : IsLocalMax f b := by
    apply isLocalMax_of_mono_anti_Icc
    · exact g₀
    · exact g₁
    · exact strictMonoOn_of_deriv_pos (convex_Icc a b) (Continuous.continuousOn h) h₀
    · exact strictAntiOn_of_deriv_neg (convex_Icc b c) (Continuous.continuousOn h) h₁

-- We do not need to assume `b` is a critical point of `f` in the `first_derivative_test`.
-- In fact, by Fermat's theorem, it must be.
lemma first_derivative_test_missing_assumption (f : ℝ → ℝ) (h : Continuous f) (a b c:ℝ)
  (g₀ : a < b) (g₁ : b < c)
  (h₀ :  ∀ x ∈ interior (Set.Icc a b), 0 < deriv f x)
  (h₁ :  ∀ x ∈ interior (Set.Icc b c), deriv f x < 0) :
    deriv f b = 0 := by
    apply IsLocalMax.deriv_eq_zero
    apply first_derivative_test
    simp_all
    tauto;exact g₁;exact h₀;exact h₁


lemma first_derivative_test_unbounded (f : ℝ → ℝ) (h : Continuous f)
  (a b : ℝ)
  (g₀ : a < b)
  (h₀ :  ∀ x ∈ interior (Set.Icc a b), 0 < deriv f x)
  (h₁ :  ∀ x ∈ interior (Set.Ici b), deriv f x < 0)
  : IsLocalMax f b := by
    exact @first_derivative_test f h a b (b+1) g₀ (by linarith) h₀ (by intros; apply h₁; simp_all)


example : IsLocalMax Real.sin (Real.pi/2) := by
  apply first_derivative_test
  · exact Real.continuous_sin
  · show 0 < Real.pi/2;exact Real.pi_div_two_pos
  · show Real.pi/2 < Real.pi;refine div_two_lt_of_pos ?g₁.a
    exact Real.pi_pos
  · intro x hx;rw [deriv_sin];simp;simp at hx
    refine Real.cos_pos_of_mem_Ioo ?h₀.hx;simp
    · constructor;linarith;tauto
    simp
  intro x hx;rw [deriv_sin];simp;simp at hx
  refine Real.cos_neg_of_pi_div_two_lt_of_lt ?h₁.hx₁ ?h₁.hx₂
  tauto;linarith;exact differentiableAt_id'

example : IsLocalMax (λ x ↦ x * Real.exp (-x)) 1 := by
  have h₀ (x:ℝ) : DifferentiableAt ℝ Neg.neg x := DifferentiableAt.neg (differentiableAt_id')
  have h₁ (x:ℝ) : DifferentiableAt ℝ (fun x ↦ Real.exp (-x)) x := by
    refine DifferentiableAt.exp ?h₀.hd.hc
    tauto
  apply first_derivative_test_unbounded
  refine Continuous.mul ?h.hf ?h.hg
  exact continuous_id'
  refine Continuous.rexp ?h.hg.h
  exact continuous_neg
  show 0 < 1
  simp only [zero_lt_one]
  intro x hx
  rw [deriv_mul]
  simp
  simp at hx
  rw [deriv_exp]
  field_simp
  · tauto
  · tauto
  · simp
  tauto
  intro x hx
  rw [deriv_mul]
  simp
  simp at hx
  rw [deriv_exp]
  rw [deriv_neg]
  simp
  suffices 1 * Real.exp (-x) < x * Real.exp (-x) by
    linarith
  field_simp
  tauto
  tauto
  simp
  tauto
