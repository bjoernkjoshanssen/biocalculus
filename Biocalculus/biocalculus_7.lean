import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.ODE.Gronwall
import Biocalculus.PReal

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
    have : f = (λ x ↦ g x + c) := (Set.eqOn_univ f fun x ↦ g x + c).mp fun ⦃x⦄ _ ↦ hc x
    rw [this]
    simp


lemma should_follow (f : ℝ → ℝ) (t : ℝ) (h : deriv f t ≠ 0) :
  HasDerivWithinAt f (deriv f t) (Set.Ici t) t := by
    refine HasDerivAt.hasDerivWithinAt ?h
    refine DifferentiableAt.hasDerivAt ?h.h
    exact differentiableAt_of_deriv_ne_zero h

-- y=Ce^x satisfies y'=y
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
  let Q := @ODE_solution_unique ℝ _ _ (λ _ y ↦ y) 1 f g 0 1
    (by intro x;exact Isometry.lipschitz fun x1 ↦ congrFun rfl) h₀ h₂ h₁ h₃ h₄
  tauto

-- #check (-(⊤:ENNReal) : EReal)

-- #check (-⊤ : EReal)

example : (-(⊤:ENNReal) : EReal) = (-⊤ : EReal) := by
  simp


/-
The differential equation
y' = (1+ce^t)/(1-ce^t)
can be rewritten as
y' = (1/c + e^t) / ((1/c) - e^t)
and then as
- y' = (1/c + e^t) / (-(1/c) + e^t)
When c = ∞ this gives us a solution y = -1.
-/
example (t : EReal) (h₀ : t ≠ ⊥) (h₁ : t ≠ ⊤) :
  ((1/⊤) + EReal.exp t) / (-(1/⊤) + EReal.exp t) = ((1):EReal) := by
  simp
  refine EReal.div_self ?h₁ ?h₂ ?h₃
  contrapose h₀
  · simp at *
  contrapose h₁
  simp at *
  tauto
  contrapose h₀
  simp at *
  tauto

example (t : Real):
  - (((1/⊤) + EReal.exp t) / (-(1/⊤) + EReal.exp t)) = ((-1):EReal) := by
  simp
  refine EReal.div_self ?h₁ ?h₂ ?h₃
  · simp
  · simp
  · simp; exact Real.exp_pos t


lemma aug8 (a b : EReal) : - (a/b) = (-a)/b := by
  nth_rewrite 1 [div_eq_mul_one_div]
  nth_rewrite 2 [div_eq_mul_one_div]
  rw [neg_mul_eq_neg_mul]

lemma aug8₀ (e : EReal) : -(e/e) = e/(-e) := by
  by_cases H₀ : e = ⊤
  · subst H₀
    simp
  · by_cases H₁ : e = ⊥
    · subst H₁
      simp
    · by_cases H₂ : e = 0
      · subst H₂
        simp
      · have : e / e = 1 := by exact EReal.div_self H₁ H₀ H₂
        rw [this]
        have : e / (-e) = -1 := by
          have : (-e)/(-e) = 1 := by
            refine EReal.div_self ?h₁ ?h₂ ?h₃
            repeat (simp at *; tauto)
          rw [← this]
          have : -((-e) / (-e)) = (-(-e)) / (-e) := by
            apply aug8
          rw [this]
          have : - -e = e := InvolutiveNeg.neg_neg e
          rw [this]
        rw [this]

example : (⊤:EReal) / (⊤:EReal) = 0 := EReal.div_top


lemma Stewart_Example_9_1_1_infinite (t : Real):
  (((1/⊤) + EReal.exp t) / ((1/⊤) - EReal.exp t)) = ((-1):EReal) := by
  have h₀ : max (Real.exp t) 0 = Real.exp t := by
    apply max_eq_left
    exact Real.exp_nonneg t

  suffices - (((1/⊤) + EReal.exp t) / (-(1/⊤) + EReal.exp t)) = ((-1):EReal) by
    rw [← this]
    simp
    rw [h₀]
    rw [aug8₀]
  simp
  rw [h₀]
  refine EReal.div_self ?h₁ ?h₂ ?h₃
  simp;simp;simp


lemma Stewart_Example_9_1_1 (c : ℝ)
  (t : ℝ) (htc : (fun t ↦ 1 - c * Real.exp t) t ≠ 0)
  :
      let y := λ t ↦ (1 + c * Real.exp t) / (1 - c * Real.exp t)
      deriv y t = (1/2) * ((y t)^2 -1) := by
  simp
  have Q := @deriv_div ℝ _ t ℝ _ _
    (λ t ↦ (1 + c * Real.exp t)) (λ t ↦ (1 - c * Real.exp t))
    (by
      apply DifferentiableAt.add
      · simp
      · apply DifferentiableAt.const_mul
        exact Real.differentiableAt_exp
    ) (by
      · apply DifferentiableAt.const_sub
        apply DifferentiableAt.const_mul
        exact Real.differentiableAt_exp
    ) htc
  simp at *
  rw [Q]
  rw [deriv_sub]
  · field_simp; ring_nf -- wow!
  · simp
  · refine DifferentiableAt.const_mul ?_ c
    exact Real.differentiableAt_exp

-- for each c : EReal, this also holds with some casting
lemma Stewart_Example_9_1_1_like_the_infinite_case (c : ℝ)
  (t : ℝ)
  (htc : (fun t ↦ 1 - c * Real.exp t) t ≠ 0)
  :
      let y := λ t ↦ (1/c + Real.exp t) / (1/c - Real.exp t)
      deriv y t = (1/2) * ((y t)^2 -1) := by
  by_cases hc : c = 0
  · subst hc
    simp at *
  have htc₁ : (fun t ↦ c⁻¹ - Real.exp t) t ≠ 0 := by
    field_simp; tauto
  simp
  rw [deriv_div,deriv_add,deriv_const,deriv_exp,deriv_sub]
  field_simp
  ring_nf
  exact differentiableAt_const c⁻¹
  exact Real.differentiableAt_exp
  exact differentiableAt_id'
  exact differentiableAt_const c⁻¹
  exact Real.differentiableAt_exp
  · apply DifferentiableAt.const_add
    exact Real.differentiableAt_exp
  · apply DifferentiableAt.const_sub
    exact Real.differentiableAt_exp
  exact htc₁

lemma one_div_ereal (c : EReal) : 1/c.toReal = (1/c).toReal := by
    unfold EReal.toReal
    simp only [one_div]
    split
    next x =>
      simp_all only [not_false_eq_true, inv_zero]
      rfl
    next x =>
      simp_all only [not_false_eq_true, inv_zero]
      rfl
    next x x_1 =>
      rfl

-- The only thing missing here is the solution y=1
-- In theory that should work with 1/0=±⊤ but Lean makes 1/0=0.
-- So we have two versions of the ODE equivalent over ℝ
-- that cover all solutions.
-- We could go around this if ±⊤ is a single element 1/0:
-- https://en.wikipedia.org/wiki/Projectively_extended_real_line
-- Projective line vs. affine extended real line
lemma Stewart_Example_9_1_1_infinite_case (c : EReal)
  (t : ℝ) (htc : 1 - c * Real.exp t ≠ 0) :
      let y : ℝ → ℝ := λ t ↦ ((1/c).toReal + Real.exp t)
                           / ((1/c).toReal - Real.exp t)
      deriv y t = (1/2) * ((y t)^2 -1) := by
  have htc' : (fun t ↦ 1 - c.toReal * Real.exp t) t ≠ 0 := by
    by_cases H : c = 0
    · subst H; simp
    · by_cases H₁ : c = ⊤
      · subst H₁
        simp
      · by_cases H₂ : c = ⊥
        · subst H₂
          simp
        · simp
          simp at htc
          contrapose htc
          simp at *
          let Q := (@EReal.coe_eq_coe_iff (1 - c.toReal * Real.exp t) 0).mpr htc
          simp at Q
          rw [← Q]
          suffices (c.toReal : EReal) = c by rw [this]
          exact EReal.coe_toReal H₁ H₂
  let Q := @Stewart_Example_9_1_1_like_the_infinite_case (c.toReal)
    t htc'
  rw [← one_div_ereal]
  exact Q

lemma Stewart_Example_9_1_1_helper :
  let y : ℝ → ℝ := λ t ↦ -1
  deriv y = (1/2) * (y^2 - 1) := by ext; simp
-- which we can also prove as a corollary of above work:
lemma infinite_Stewart (t : ℝ):
  let y : ℝ → ℝ := λ t ↦ -1
  deriv y t =  (1/2) * ((y t)^2 -1) := by
    have := @Stewart_Example_9_1_1_infinite_case ⊤ t (by
      have : (⊤:EReal) * ↑(Real.exp t) = ⊤ := by
        refine EReal.top_mul_coe_of_pos ?h
        exact Real.exp_pos t
      rw [this]
      simp
    )
    simp_all


-- lemma Stewart_Example_9_1_1_infinite_case_PReal (c : PReal)
--   (t : ℝ) (htc : 1 - c * Real.exp t ≠ 0) :
--       let y : ℝ → ℝ := λ t ↦ ((1/c).toReal + Real.exp t)
--                            / ((1/c).toReal - Real.exp t)
--       deriv y t = (1/2) * ((y t)^2 -1) := by
--   have htc' : (fun t ↦ 1 - c.toReal * Real.exp t) t ≠ 0 := by
--     by_cases H : c = 0
--     · subst H; simp
--     · by_cases H₁ : c = ⊤
--       · subst H₁
--         simp
--       · by_cases H₂ : c = ⊥
--         · subst H₂
--           simp
--         · simp
--           simp at htc
--           contrapose htc
--           simp at *
--           let Q := (@EReal.coe_eq_coe_iff (1 - c.toReal * Real.exp t) 0).mpr htc
--           simp at Q
--           rw [← Q]
--           suffices (c.toReal : EReal) = c by rw [this]
--           exact EReal.coe_toReal H₁ H₂
--   let Q := @Stewart_Example_9_1_1_like_the_infinite_case (c.toReal)
--     t htc'
--   rw [← one_div_ereal]
--   exact Q
