import Mathlib
import Submission.Work.HP.Defs

/-!
# Conics: infrastructure for `Work.HP.conics`

Definitions and elementary lemmas for ternary quadratic forms over `ZMod p` and `ZMod (p^2)`,
in the coefficient-vector representation `Mon 2 2 → R` used in `Submission/Work/HP/Defs.lean`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP.Conics

/-! ## The six degree-two monomials in three variables -/

/-- exponent vector of `x_0^2` -/
def m00 : Mon 2 2 := ⟨fun i => match i with | 0 => 2 | 1 => 0 | 2 => 0, by decide⟩
/-- exponent vector of `x_0 x_1` -/
def m01 : Mon 2 2 := ⟨fun i => match i with | 0 => 1 | 1 => 1 | 2 => 0, by decide⟩
/-- exponent vector of `x_0 x_2` -/
def m02 : Mon 2 2 := ⟨fun i => match i with | 0 => 1 | 1 => 0 | 2 => 1, by decide⟩
/-- exponent vector of `x_1^2` -/
def m11 : Mon 2 2 := ⟨fun i => match i with | 0 => 0 | 1 => 2 | 2 => 0, by decide⟩
/-- exponent vector of `x_1 x_2` -/
def m12 : Mon 2 2 := ⟨fun i => match i with | 0 => 0 | 1 => 1 | 2 => 1, by decide⟩
/-- exponent vector of `x_2^2` -/
def m22 : Mon 2 2 := ⟨fun i => match i with | 0 => 0 | 1 => 0 | 2 => 2, by decide⟩

theorem univ_mon : (Finset.univ : Finset (Mon 2 2)) = {m00, m01, m02, m11, m12, m22} := by decide

theorem card_mon : Fintype.card (Mon 2 2) = 6 := by decide

/-! ## Evaluating a quadratic form with coefficients in an arbitrary semiring -/

/-- The ternary quadratic form with coefficient vector `a`. -/
def qf {R : Type*} [CommSemiring R] (a : Mon 2 2 → R) (x : Fin 3 → R) : R :=
  ∑ m, a m * ∏ i, x i ^ (m.1 i : ℕ)

/-- The explicit expansion of a ternary quadratic form. -/
theorem qf_expand {R : Type*} [CommSemiring R] (a : Mon 2 2 → R) (x : Fin 3 → R) :
    qf a x = a m00 * x 0 ^ 2 + a m01 * (x 0 * x 1) + a m02 * (x 0 * x 2)
      + a m11 * x 1 ^ 2 + a m12 * (x 1 * x 2) + a m22 * x 2 ^ 2 := by
  rw [qf, univ_mon, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Fin.prod_univ_three, m00, m01, m02, m11, m12, m22]
  norm_num
  ring

/-- Agreement with the challenge's `formEval`. -/
theorem qf_formEval {R : Type*} [CommRing R] (a : Mon 2 2 → ℤ) (x : Fin 3 → R) :
    qf (fun m => (a m : R)) x = formEval 2 2 a x := by
  simp only [qf, formEval, veronese]

/-! ## The polar (bilinear) form -/

/-- The doubled polar form `qf a (x+y) - qf a x - qf a y`. -/
def pol {R : Type*} [CommRing R] (a : Mon 2 2 → R) (x y : Fin 3 → R) : R :=
  qf a (x + y) - qf a x - qf a y

theorem pol_expand {R : Type*} [CommRing R] (a : Mon 2 2 → R) (x y : Fin 3 → R) :
    pol a x y = a m00 * (x 0 * y 0 + y 0 * x 0) + a m01 * (x 0 * y 1 + x 1 * y 0)
      + a m02 * (x 0 * y 2 + x 2 * y 0) + a m11 * (x 1 * y 1 + y 1 * x 1)
      + a m12 * (x 1 * y 2 + x 2 * y 1) + a m22 * (x 2 * y 2 + y 2 * x 2) := by
  simp only [pol, qf_expand, Pi.add_apply]
  ring

theorem qf_smul {R : Type*} [CommRing R] (a : Mon 2 2 → R) (x : Fin 3 → R) (c : R) :
    qf a (c • x) = c ^ 2 * qf a x := by
  simp only [qf_expand, Pi.smul_apply]
  ring

theorem pol_smul_right {R : Type*} [CommRing R] (a : Mon 2 2 → R) (x z : Fin 3 → R) (c : R) :
    pol a x (c • z) = c * pol a x z := by
  simp only [pol_expand, Pi.smul_apply]
  ring

theorem pol_smul_left {R : Type*} [CommRing R] (a : Mon 2 2 → R) (x z : Fin 3 → R) (c : R) :
    pol a (c • x) z = c * pol a x z := by
  simp only [pol_expand, Pi.smul_apply]
  ring

theorem qf_add_pol {R : Type*} [CommRing R] (a : Mon 2 2 → R) (x y : Fin 3 → R) :
    qf a (x + y) = qf a x + qf a y + pol a x y := by
  simp only [pol]; ring

theorem qf_add_smul {R : Type*} [CommRing R] (a : Mon 2 2 → R) (x z : Fin 3 → R) (c : R) :
    qf a (x + c • z) = qf a x + c * pol a x z + c ^ 2 * qf a z := by
  simp only [qf_expand, pol_expand, Pi.add_apply, Pi.smul_apply]
  ring

/-! ## Reduction modulo `p` -/

/-- The reduction `ZMod (p^2) →+* ZMod p`. -/
def red (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by norm_num : (2:ℕ) ≠ 0)) (ZMod p)

/-- Coefficientwise reduction modulo `p` of a quadratic form. -/
def redC (p : ℕ) (A : Mon 2 2 → ZMod (p ^ 2)) : Mon 2 2 → ZMod p := fun m => red p (A m)

theorem red_qf (p : ℕ) (A : Mon 2 2 → ZMod (p ^ 2)) (x : Fin 3 → ZMod (p ^ 2)) :
    red p (qf A x) = qf (redC p A) (fun i => red p (x i)) := by
  simp only [qf, redC, map_sum, map_mul, map_prod, map_pow]

theorem red_pol (p : ℕ) (A : Mon 2 2 → ZMod (p ^ 2)) (x y : Fin 3 → ZMod (p ^ 2)) :
    red p (pol A x y) = pol (redC p A) (fun i => red p (x i)) (fun i => red p (y i)) := by
  have h1 : (fun i => red p ((x + y) i)) = (fun i => red p (x i)) + (fun i => red p (y i)) := by
    funext i; simp [Pi.add_apply]
  simp only [pol, map_sub, red_qf, h1]

/-! ## Sharpness: a quadratic form whose zero set is a single line, containing that line in
its radical. -/

/-- `SharpAt a v` says that `v ≠ 0`, that `v` lies in the radical of the polar form of `a`,
and that the zero set of `a` is exactly the line spanned by `v`. -/
def SharpAt {R : Type*} [CommRing R] (a : Mon 2 2 → R) (v : Fin 3 → R) : Prop :=
  v ≠ 0 ∧ (∀ y, pol a v y = 0) ∧ (∀ x, qf a x = 0 → ∃ t : R, x = t • v)

/-! ## Lifts mod `p^2` -/

/-- `v'` is a lift of `v` modulo `p`. -/
def IsLift (p : ℕ) (v' : Fin 3 → ZMod (p ^ 2)) (v : Fin 3 → ZMod p) : Prop :=
  ∀ i, red p (v' i) = v i

/-- The "lifted value at `v`" is nonzero: `qf A` does not vanish on any lift of `v`. -/
def II (p : ℕ) (A : Mon 2 2 → ZMod (p ^ 2)) (v : Fin 3 → ZMod p) : Prop :=
  ∃ v' : Fin 3 → ZMod (p ^ 2), IsLift p v' v ∧ qf A v' ≠ 0

/-- The bad set `Z_p`: forms mod `p^2` whose reduction mod `p` is sharp on some line `⟨v⟩`
and whose lift does not vanish on the lifts of `v`. Such forms have no primitive zero mod `p^2`. -/
def BadForm (p : ℕ) (A : Mon 2 2 → ZMod (p ^ 2)) : Prop :=
  ∃ v : Fin 3 → ZMod p, SharpAt (redC p A) v ∧ II p A v

/-! ## A model family of sharp forms: `q(x_1 - a x_0, x_2 - b x_0)` -/

/-- The coefficient vector of the quadratic form `α u^2 + β u v + γ v^2` with
`u = x_1 - a x_0`, `v = x_2 - b x_0`. -/
def mkForm {R : Type*} [CommRing R] (a b α β γ : R) : Mon 2 2 → R := fun m =>
  if m = m00 then α * a ^ 2 + β * (a * b) + γ * b ^ 2
  else if m = m01 then -(2 * α * a) - β * b
  else if m = m02 then -(β * a) - 2 * γ * b
  else if m = m11 then α
  else if m = m12 then β
  else γ

theorem mkForm_m00 {R : Type*} [CommRing R] (a b α β γ : R) :
    mkForm a b α β γ m00 = α * a ^ 2 + β * (a * b) + γ * b ^ 2 := by
  unfold mkForm; rw [if_pos rfl]

theorem mkForm_m01 {R : Type*} [CommRing R] (a b α β γ : R) :
    mkForm a b α β γ m01 = -(2 * α * a) - β * b := by
  unfold mkForm; rw [if_neg (by decide : ¬ (m01 = m00)), if_pos rfl]

theorem mkForm_m02 {R : Type*} [CommRing R] (a b α β γ : R) :
    mkForm a b α β γ m02 = -(β * a) - 2 * γ * b := by
  unfold mkForm
  rw [if_neg (by decide : ¬ (m02 = m00)), if_neg (by decide : ¬ (m02 = m01)), if_pos rfl]

theorem mkForm_m11 {R : Type*} [CommRing R] (a b α β γ : R) :
    mkForm a b α β γ m11 = α := by
  unfold mkForm
  rw [if_neg (by decide : ¬ (m11 = m00)), if_neg (by decide : ¬ (m11 = m01)),
      if_neg (by decide : ¬ (m11 = m02)), if_pos rfl]

theorem mkForm_m12 {R : Type*} [CommRing R] (a b α β γ : R) :
    mkForm a b α β γ m12 = β := by
  unfold mkForm
  rw [if_neg (by decide : ¬ (m12 = m00)), if_neg (by decide : ¬ (m12 = m01)),
      if_neg (by decide : ¬ (m12 = m02)), if_neg (by decide : ¬ (m12 = m11)), if_pos rfl]

theorem mkForm_m22 {R : Type*} [CommRing R] (a b α β γ : R) :
    mkForm a b α β γ m22 = γ := by
  unfold mkForm
  rw [if_neg (by decide : ¬ (m22 = m00)), if_neg (by decide : ¬ (m22 = m01)),
      if_neg (by decide : ¬ (m22 = m02)), if_neg (by decide : ¬ (m22 = m11)),
      if_neg (by decide : ¬ (m22 = m12))]

attribute [simp] mkForm_m00 mkForm_m01 mkForm_m02 mkForm_m11 mkForm_m12 mkForm_m22

theorem qf_mkForm {R : Type*} [CommRing R] (a b α β γ : R) (x : Fin 3 → R) :
    qf (mkForm a b α β γ) x
      = α * (x 1 - a * x 0) ^ 2 + β * ((x 1 - a * x 0) * (x 2 - b * x 0))
        + γ * (x 2 - b * x 0) ^ 2 := by
  simp only [qf_expand, mkForm_m00, mkForm_m01, mkForm_m02, mkForm_m11, mkForm_m12, mkForm_m22]
  ring

end Work.HP.Conics
