/-
# The Dirichlet character attached to the Jacobi symbol

For `b ≥ 1` the function `a ↦ J(a | b)` (Jacobi symbol of the representative `a.val`)
is a completely multiplicative function on `ZMod b` which vanishes exactly on the non-units
(Mathlib's `jacobiSym.eq_zero_iff_not_coprime`), hence it is a Dirichlet character of level `b`.
This is the character denoted `(·|b)` in Friedlander–Iwaniec (11.16), (22.5).

The file also records the elementary pointwise facts used by the main file
`Submission/Work/FIArea4/polya_vinogradov.lean`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `J(·|b)` on natural numbers, expressed through representatives: multiplicative in `n`. -/
lemma jacobiSym_mul_nat (b : ℕ) (m n : ℕ) :
    jacobiSym ((m * n : ℕ) : ℤ) b = jacobiSym (m : ℤ) b * jacobiSym (n : ℤ) b := by
  rw [Nat.cast_mul, jacobiSym.mul_left]

/-- The Jacobi symbol depends only on the class modulo `b`, so `a ↦ J(a.val | b)` is
multiplicative on `ZMod b`. -/
lemma jacobiSym_val_mul (b : ℕ) [NeZero b] (a a' : ZMod b) :
    jacobiSym ((a * a').val : ℤ) b = jacobiSym (a.val : ℤ) b * jacobiSym (a'.val : ℤ) b := by
  have h1 : a * a' = ((a.val * a'.val : ℕ) : ZMod b) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a, ← ZMod.natCast_zmod_val a']
    rw [← Nat.cast_mul]
  have hval : (a * a').val = (a.val * a'.val) % b := by
    rw [h1, ZMod.val_natCast]
  have hmod : (((a * a').val : ℕ) : ℤ) % (b : ℤ) = (((a.val * a'.val : ℕ)) : ℤ) % (b : ℤ) := by
    rw [hval, Int.natCast_emod]
    exact Int.emod_emod _ _
  rw [jacobiSym.mod_left' hmod]
  have hmod2 : (((a.val * a'.val : ℕ)) : ℤ) % (b : ℤ)
      = ((a.val : ℤ) * (a'.val : ℤ)) % (b : ℤ) := by
    rw [Nat.cast_mul]
  rw [jacobiSym.mod_left' hmod2, jacobiSym.mul_left]

/-- `a : ZMod b` is a unit iff its representative is coprime to `b`. -/
lemma isUnit_zmod_iff_coprime_val (b : ℕ) [NeZero b] (a : ZMod b) :
    IsUnit a ↔ Nat.Coprime a.val b := by
  have h := ZMod.isUnit_iff_coprime a.val b
  rwa [ZMod.natCast_zmod_val] at h

/-- The Jacobi symbol vanishes exactly at non-units of `ZMod b`. -/
lemma jacobiSym_eq_zero_iff_isUnit (b : ℕ) [NeZero b] (a : ZMod b) :
    jacobiSym (a.val : ℤ) b = 0 ↔ ¬ IsUnit a := by
  rw [jacobiSym.eq_zero_iff_not_coprime]
  constructor
  · intro h ha
    have hc : Nat.Coprime a.val b := (isUnit_zmod_iff_coprime_val b a).mp ha
    have : (a.val.gcd b) = 1 := Nat.coprime_iff_gcd_eq_one.mp hc
    exact h (by rw [Int.gcd_eq_natAbs]; exact_mod_cast this)
  · intro ha hcontra
    have hgcd : (a.val.gcd b) = 1 := by
      rw [Int.gcd_eq_natAbs] at hcontra
      exact_mod_cast hcontra
    exact ha ((isUnit_zmod_iff_coprime_val b a).mpr (Nat.coprime_iff_gcd_eq_one.mpr hgcd))

/-- **The Dirichlet character of level `b` given by the Jacobi symbol**: `a ↦ J(a.val | b)`.

It is well defined (`jacobiSym.mod_left`), multiplicative (`jacobiSym.mul_left`), and it takes
the value `0` exactly at the non-units of `ZMod b` (`jacobiSym.eq_zero_iff_not_coprime`).  -/
def jacobiChar (b : ℕ) [NeZero b] : DirichletCharacter ℂ b where
  toMonoidHom :=
    { toFun := fun a => (jacobiSym (a.val : ℤ) b : ℂ)
      map_one' := by
        have hval : (1 : ZMod b).val = 1 % b := by
          conv_lhs => rw [show (1 : ZMod b) = ((1 : ℕ) : ZMod b) from by simp]
          exact ZMod.val_natCast b 1
        have hmod : (((1 : ZMod b).val : ℕ) : ℤ) % (b : ℤ) = (1 : ℤ) % (b : ℤ) := by
          rw [hval, Int.natCast_emod]
          exact Int.emod_emod _ _
        rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
        norm_num
      map_mul' := fun a a' => by
        rw [jacobiSym_val_mul]
        push_cast
        ring }
  map_nonunit' := fun a ha => by
    show (jacobiSym (a.val : ℤ) b : ℂ) = 0
    rw [(jacobiSym_eq_zero_iff_isUnit b a).mpr ha]
    norm_num

@[simp] lemma jacobiChar_apply (b : ℕ) [NeZero b] (a : ZMod b) :
    jacobiChar b a = (jacobiSym (a.val : ℤ) b : ℂ) := rfl

/-- On natural numbers the value is the plain Jacobi symbol (no reduction needed). -/
lemma jacobiChar_natCast (b : ℕ) [NeZero b] (n : ℕ) :
    jacobiChar b (n : ZMod b) = (jacobiSym (n : ℤ) b : ℂ) := by
  rw [jacobiChar_apply, ZMod.val_natCast]
  congr 1
  exact (jacobiSym.mod_left (n : ℤ) b).symm

/-- The values of the Jacobi character have modulus at most one. -/
lemma norm_jacobiChar_le_one (b : ℕ) [NeZero b] (a : ZMod b) : ‖jacobiChar b a‖ ≤ 1 := by
  rw [jacobiChar_apply]
  rcases jacobiSym.trichotomy (a.val : ℤ) b with h | h | h <;> rw [h] <;> norm_num

/-- The Jacobi character vanishes exactly at the non-units. -/
lemma jacobiChar_eq_zero_iff (b : ℕ) [NeZero b] (a : ZMod b) :
    jacobiChar b a = 0 ↔ ¬ IsUnit a := by
  rw [jacobiChar_apply, Int.cast_eq_zero]
  exact jacobiSym_eq_zero_iff_isUnit b a

/-- The Jacobi character takes the values `0, 1, -1`. -/
lemma jacobiChar_eq_zero_or_one_or_neg_one (b : ℕ) [NeZero b] (a : ZMod b) :
    jacobiChar b a = 0 ∨ jacobiChar b a = 1 ∨ jacobiChar b a = -1 := by
  rw [jacobiChar_apply]
  rcases jacobiSym.trichotomy (a.val : ℤ) b with h | h | h
  · exact Or.inl (by rw [h]; norm_num)
  · exact Or.inr (Or.inl (by rw [h]; norm_num))
  · exact Or.inr (Or.inr (by rw [h]; norm_num))

/-- A unit value of the Jacobi character has modulus one. -/
lemma norm_jacobiChar_eq_one (b : ℕ) [NeZero b] {a : ZMod b} (ha : IsUnit a) :
    ‖jacobiChar b a‖ = 1 := by
  have hne : jacobiChar b a ≠ 0 := fun h => (jacobiChar_eq_zero_iff b a).mp h ha
  rcases jacobiChar_eq_zero_or_one_or_neg_one b a with h | h | h
  · exact absurd h hne
  · rw [h]; norm_num
  · rw [h]; norm_num

end

end Work.FIArea4
