import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.ODE.Gronwall

noncomputable section
/-
The projective real line.
Obtained from https://github.com/leanprover-community/mathlib4/blob/96a6efb931bacb29b366aa07146e1ac6a90b28d4/Mathlib/Data/Real/EReal.lean#L55-L56
by removing negative infinity, basically.
-/

def PReal : Type := WithTop ℝ
  deriving Zero, One, Nontrivial, AddMonoid, PartialOrder

example : (1:PReal) = (1:PReal) := rfl

instance : ZeroLEOneClass PReal := inferInstanceAs (ZeroLEOneClass (WithTop ℝ))
instance : SupSet PReal := inferInstanceAs (SupSet (WithTop ℝ))
instance : InfSet PReal := inferInstanceAs (InfSet (WithTop ℝ))


instance : LinearOrderedAddCommMonoid PReal :=
  inferInstanceAs (LinearOrderedAddCommMonoid (WithTop ℝ))

instance : AddCommMonoidWithOne PReal :=
  inferInstanceAs (AddCommMonoidWithOne (WithTop ℝ))

instance : DenselyOrdered PReal :=
  inferInstanceAs (DenselyOrdered (WithTop ℝ))

/-- The canonical inclusion from reals to preals. Registered as a coercion. -/
@[coe] def Real.toPReal : ℝ → PReal := some

namespace PReal

-- things unify with `WithBot.decidableLT` later if we don't provide this explicitly.
instance decidableLT : DecidableRel ((· < ·) : PReal → PReal → Prop) :=
  WithTop.decidableLT

instance : Top PReal := by
  refine { top := none }

instance : Coe ℝ PReal := ⟨Real.toPReal⟩

theorem coe_strictMono : StrictMono Real.toPReal :=
  WithTop.coe_strictMono

theorem coe_injective : Function.Injective Real.toPReal :=
  coe_strictMono.injective

@[simp, norm_cast]
protected theorem coe_le_coe_iff {x y : ℝ} : (x : PReal) ≤ (y : PReal) ↔ x ≤ y :=
  coe_strictMono.le_iff_le

@[simp, norm_cast]
protected theorem coe_lt_coe_iff {x y : ℝ} : (x : PReal) < (y : PReal) ↔ x < y :=
  coe_strictMono.lt_iff_lt

@[simp, norm_cast]
protected theorem coe_eq_coe_iff {x y : ℝ} : (x : PReal) = (y : PReal) ↔ x = y :=
  coe_injective.eq_iff

protected theorem coe_ne_coe_iff {x y : ℝ} : (x : PReal) ≠ (y : PReal) ↔ x ≠ y :=
  coe_injective.ne_iff

/-- The canonical map from nonnegative extended reals to extended reals -/
@[coe] def _root_.ENNReal.toPReal : ENNReal → PReal
  | ⊤ => ⊤
  | .some x => x.1

instance hasCoeENNReal : Coe ENNReal PReal :=
  ⟨ENNReal.toPReal⟩

instance : Inhabited PReal := ⟨0⟩

@[simp, norm_cast]
theorem coe_zero : ((0 : ℝ) : PReal) = 0 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : ℝ) : PReal) = 1 := rfl

/-- A recursor for `PReal` in terms of the coercion.

When working in term mode, note that pattern matching can be used directly. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def rec {C : PReal → Sort*}  (h_real : ∀ a : ℝ, C a) (h_top : C ⊤) :
    ∀ a : PReal, C a
  | (a : ℝ) => h_real a
  | ⊤ => h_top

/-- The multiplication on `PReal`. Our definition satisfies `0 * x = x * 0 = 0` for any `x`, and
picks the only sensible value elsewhere. -/
protected def mul : PReal → PReal → PReal
  | ⊤, ⊤ => ⊤
  | ⊤, (y : ℝ) => if y = 0 then 0 else ⊤
  | (x : ℝ), ⊤ => if x = 0 then 0 else ⊤
  | (x : ℝ), (y : ℝ) => (x * y : ℝ)


instance : Mul PReal := ⟨PReal.mul⟩

@[simp, norm_cast]
theorem coe_mul (x y : ℝ) : (↑(x * y) : PReal) = x * y :=
  rfl

/-- Induct on two `PReal`s by performing case splits on the sign of one whenever the other is
infinite. -/
@[elab_as_elim]
theorem induction₂ {P : PReal → PReal → Prop} (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : ℝ, x < 0 → P ⊤ x)
    (pos_top : ∀ x : ℝ, 0 < x → P x ⊤) (zero_top : P 0 ⊤)
    (coe_coe : ∀ x y : ℝ, P x y) (neg_top : ∀ x : ℝ, x < 0 → P x ⊤)
   : ∀ x y, P x y
  | (x : ℝ), (y : ℝ) => coe_coe _ _
  | (x : ℝ), ⊤ => by
    rcases lt_trichotomy x 0 with (hx | rfl | hx)
    exacts [neg_top x hx, zero_top, pos_top x hx]
  | ⊤, (y : ℝ) => by
    rcases lt_trichotomy y 0 with (hy | rfl | hy)
    exacts [top_neg y hy, top_zero, top_pos y hy]
  | ⊤, ⊤ => top_top

/-- Induct on two `PReal`s by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that the relation is symmetric. -/
@[elab_as_elim]
theorem induction₂_symm {P : PReal → PReal → Prop} (symm : ∀ {x y}, P x y → P y x)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0)
    (top_neg : ∀ x : ℝ, x < 0 → P ⊤ x)
    (coe_coe : ∀ x y : ℝ, P x y)
    : ∀ x y, P x y :=
  @PReal.induction₂ P top_top top_pos top_zero top_neg
    (fun _ h => symm <| top_pos _ h)
    (symm top_zero) coe_coe (fun _ h => symm <| top_neg _ h)

protected theorem mul_comm (x y : PReal) : x * y = y * x := by
  induction x <;> induction y  <;>
    try { rfl }
  rw [← coe_mul, ← coe_mul, mul_comm]


-- protected theorem PReal.zero_mul : ∀ x : PReal, 0 * x = 0
--   | ⊤ => (if_neg (lt_irrefl _)).trans (if_pos rfl)
--   | ⊥ => (if_neg (lt_irrefl _)).trans (if_pos rfl)
--   | (x : ℝ) => congr_arg Real.toEReal (zero_mul x)

-- protected theorem PReal.one_mul : ∀ x : PReal, 1 * x = x
--   | (x : ℝ) => congr_arg Real.toEReal (one_mul x)
--   | ⊤ =>  if_pos one_pos

-- instance : MulZeroOneClass EReal where
--   one_mul := EReal.one_mul
--   mul_one := fun x => by rw [EReal.mul_comm, EReal.one_mul]
--   zero_mul := EReal.zero_mul
--   mul_zero := fun x => by rw [EReal.mul_comm, EReal.zero_mul]

/-! ### Real coercion -/

instance canLift : CanLift PReal ℝ (↑) fun r => r ≠ ⊤ where
  prf x hx := by
    induction x
    · use ‹ℝ›
    · simp at hx

/-- The map from extended reals to reals sending infinities to zero. -/
def toReal : PReal → ℝ
  | ⊤ => 0
  | (x : ℝ) => x

@[simp]
theorem toReal_top : toReal ⊤ = 0 :=
  rfl

@[simp]
theorem toReal_zero : toReal 0 = 0 :=
  rfl

@[simp]
theorem toReal_one : toReal 1 = 1 :=
  rfl

@[simp]
theorem toReal_coe (x : ℝ) : toReal (x : PReal) = x :=
  rfl

@[simp]
theorem coe_lt_top (x : ℝ) : (x : PReal) < ⊤ :=
  WithTop.coe_lt_top _

@[simp]
theorem coe_ne_top (x : ℝ) : (x : PReal) ≠ ⊤ :=
  (coe_lt_top x).ne

@[simp]
theorem top_ne_coe (x : ℝ) : (⊤ : PReal) ≠ x :=
  (coe_lt_top x).ne'

@[simp]
theorem zero_lt_top : (0 : PReal) < ⊤ :=
  coe_lt_top 0

@[simp]
theorem zero_ne_top : (0 : PReal) ≠ ⊤ :=
  coe_ne_top 0

@[simp]
theorem top_ne_zero : (⊤ : PReal) ≠ 0 :=
  (coe_ne_top 0).symm

theorem range_coe : Set.range Real.toPReal = {⊤}ᶜ := by
  ext x
  induction x <;> simp

theorem range_coe_eq_Ioo : Set.range Real.toPReal = Set.Iio ⊤ := by
  ext x -- wow!
  induction x <;> simp

@[simp, norm_cast]
theorem coe_add (x y : ℝ) : (↑(x + y) : PReal) = x + y :=
  rfl

-- `coe_mul` moved up

@[norm_cast]
theorem coe_nsmul (n : ℕ) (x : ℝ) : (↑(n • x) : PReal) = n • (x : PReal) :=
  map_nsmul (⟨⟨Real.toPReal, PReal.coe_zero⟩, coe_add⟩ : ℝ →+ PReal) _ _

@[simp, norm_cast]
theorem coe_eq_zero {x : ℝ} : (x : PReal) = 0 ↔ x = 0 :=
  PReal.coe_eq_coe_iff

@[simp, norm_cast]
theorem coe_eq_one {x : ℝ} : (x : PReal) = 1 ↔ x = 1 :=
  PReal.coe_eq_coe_iff

theorem coe_ne_zero {x : ℝ} : (x : PReal) ≠ 0 ↔ x ≠ 0 :=
  PReal.coe_ne_coe_iff

theorem coe_ne_one {x : ℝ} : (x : PReal) ≠ 1 ↔ x ≠ 1 :=
  PReal.coe_ne_coe_iff

@[simp, norm_cast]
protected theorem coe_nonneg {x : ℝ} : (0 : PReal) ≤ x ↔ 0 ≤ x :=
  PReal.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_nonpos {x : ℝ} : (x : PReal) ≤ 0 ↔ x ≤ 0 :=
  PReal.coe_le_coe_iff

@[simp, norm_cast]
protected theorem coe_pos {x : ℝ} : (0 : PReal) < x ↔ 0 < x :=
  PReal.coe_lt_coe_iff


--

@[simp, norm_cast]
protected theorem coe_neg' {x : ℝ} : (x : PReal) < 0 ↔ x < 0 :=
  PReal.coe_lt_coe_iff

-- theorem toReal_le_toReal {x y : PReal} (h : x ≤ y) (hy : y ≠ ⊤) :
--     x.toReal ≤ y.toReal := by
--   lift x to ℝ using ne_top_of_le_ne_top hy h
--   lift y to ℝ using ⟨hy, ne_bot_of_le_ne_bot hx h⟩
--   simpa using h

theorem coe_toReal {x : PReal} (hx : x ≠ ⊤) : (x.toReal : PReal) = x := by
  lift x to ℝ using hx
  rfl

theorem le_coe_toReal {x : PReal} (h : x ≠ ⊤) : x ≤ x.toReal := by
  · simp only [le_refl, coe_toReal h]

theorem coe_toReal_le {x : PReal}  : ↑x.toReal ≤ x := by
  by_cases h' : x = ⊤
  · subst h';simp;exact right_eq_inf.mp rfl
  · simp only [le_refl, coe_toReal h']

theorem eq_top_iff_forall_lt (x : PReal) : x = ⊤ ↔ ∀ y : ℝ, (y : PReal) < x := by
  constructor
  · rintro rfl
    exact PReal.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.toReal, le_coe_toReal h⟩

/-! ### Intervals and coercion from reals -/

lemma exists_between_coe_real {x z : PReal} (h : x < z) : ∃ y : ℝ, x < y ∧ y < z := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_between h
  induction a with
  | h_real a₀ => exact ⟨a₀, ha₁, ha₂⟩
  | h_top => exact (not_top_lt ha₂).elim

-- @[simp]
-- lemma image_coe_Icc (x y : ℝ) : Real.toPReal '' Set.Icc x y = Set.Icc ↑x ↑y := by
--   -- refine (Set.image_comp WithBot.some WithTop.some _).trans ?_
--   -- rw [WithTop.image_coe_Icc, WithBot.image_coe_Icc]
--   -- rfl

-- @[simp]
-- lemma image_coe_Ico (x y : ℝ) : Real.toPReal '' Ico x y = Ico ↑x ↑y := by
--   refine (image_comp WithBot.some WithTop.some _).trans ?_
--   rw [WithTop.image_coe_Ico, WithBot.image_coe_Ico]
--   rfl

/-! ### ennreal coercion -/

@[simp]
theorem toReal_coe_ennreal : ∀ {x : ENNReal}, toReal (x : PReal) = ENNReal.toReal x
  | ⊤ => rfl
  | .some _ => rfl

@[simp]
theorem coe_ennreal_ofReal {x : ℝ} : (ENNReal.ofReal x : PReal) = max x 0 :=
  rfl

theorem coe_nnreal_eq_coe_real (x : NNReal) : ((x : ENNReal) : PReal) = (x : ℝ) :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_zero : ((0 : ENNReal) : PReal) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_one : ((1 : ENNReal) : PReal) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_ennreal_top : ((⊤ : ENNReal) : PReal) = ⊤ :=
  rfl

end PReal

end
