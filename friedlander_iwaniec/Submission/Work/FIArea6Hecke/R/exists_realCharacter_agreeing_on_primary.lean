/-
# `Submission.Work.FIArea6Hecke.R.exists_realCharacter_agreeing_on_primary`

**Every character `χ` mod `4d` of `ℤ[i]` which is *real on the primary units* is the restriction,
to the primary elements, of a multiplicative real-valued function `χ'` on all of `ℤ[i]` with
`χ'(1) = 1` and `‖χ'‖ ≤ 1`.**

This is the elementary reduction used by `Work.FIArea6Hecke.R.Lam_one_ne_zero`: the Hecke
`L`-function only sees the values of `χ` on the *primary* elements (`heckeLam_eq_of_primary_agree`),
and the real (quadratic) case is handled by a completion argument which needs a character defined
on the whole ring and taking real values there.

The construction is the classical one.  Every `z ∈ ℤ[i]` of odd norm — equivalently every `z`
which is odd, i.e. `1 + i ∤ z` — is `u · w` for a unique unit `u` and a unique *primary* `w`
(`Commons.NumberTheory.GaussianInt.primary_associate_exists_unique`), and the primary elements
form a submonoid.  Hence `z ↦ primAssoc z` (the primary associate, on odd elements) is
multiplicative, and so is

  `χ'(z) = χ (primAssoc z)`  for `z` of odd norm,   `χ'(z) = 0`  otherwise.

Off the odd elements `χ'` vanishes, and the product of two odd elements is odd, so `χ'` is
multiplicative *on all of* `ℤ[i]` (a product involving an even element — in particular `0` — is
again even, and either `χ'` value is `0`).  On primary `z` we have `primAssoc z = z`, so `χ'`
agrees with `χ` there.  Finally `χ'` is real valued: `primAssoc z` is primary, so either it is a
unit mod `4d` and `hreal` applies, or `χ` vanishes on it by the strict character condition.

Nothing here uses `1 ≤ d` (the hypothesis is kept for compatibility with the caller).
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.LamOneNeZeroDefs
import Submission.Work.FIArea4.GaussMoebiusCore

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Work.FIPlan

noncomputable section

/-! ## The primary associate is multiplicative on the odd elements -/

/-- An element of odd norm is non-zero. -/
lemma ne_zero_of_odd_gnorm {z : GaussianInt} (h : Odd (gnorm z)) : z ≠ 0 := by
  intro hz
  rw [hz] at h
  obtain ⟨k, hk⟩ := h
  rw [Work.FIArea4.gnorm_zero] at hk
  omega

/-- **Uniqueness form of the primary associate**: any primary associate of `z` *is* `primAssoc z`.
This is the shape in which the unicty of the primary associate is used below. -/
lemma primAssoc_unique_of_odd {z y : GaussianInt} (hz : z ≠ 0) (hodd : Odd (gnorm z))
    (hy : Associated y z) (hyp : IsPrimary y) : y = Work.FIArea4.primAssoc z := by
  have huniq := (Classical.choose_spec (Work.FIArea4.existsUnique_primary_assoc hz hodd)).2
  rw [Work.FIArea4.primAssoc,
    dif_pos (show z ≠ 0 ∧ Odd (gnorm z) from ⟨hz, hodd⟩)]
  exact huniq y ⟨hy, hyp⟩

/-- **The primary associate is multiplicative on odd elements**: the product of primary elements
is primary, so `primAssoc` is a monoid homomorphism on the odd part of `ℤ[i]`. -/
lemma primAssoc_mul_odd {z w : GaussianInt} (hz : Odd (gnorm z)) (hw : Odd (gnorm w)) :
    Work.FIArea4.primAssoc (z * w) = Work.FIArea4.primAssoc z * Work.FIArea4.primAssoc w := by
  have hz0 := ne_zero_of_odd_gnorm hz
  have hw0 := ne_zero_of_odd_gnorm hw
  have hzw0 : z * w ≠ 0 := mul_ne_zero hz0 hw0
  have hzw : Odd (gnorm (z * w)) := by
    rw [Work.FIArea4.gnorm_mul]; exact hz.mul hw
  exact (primAssoc_unique_of_odd hzw0 hzw
    ((Work.FIArea4.primAssoc_associated hz0 hz).mul_mul
      (Work.FIArea4.primAssoc_associated hw0 hw))
    (Work.FIArea5.S16Hecke.isPrimary_mul (Work.FIArea4.primAssoc_primary hz0 hz)
      (Work.FIArea4.primAssoc_primary hw0 hw))).symm

/-! ## The real character on all of `ℤ[i]` -/

/-- The real character attached to `χ`: normalise to the primary associate on the odd elements and
extend by `0` off them. -/
def chiReal (chi : GaussianInt → ℂ) : GaussianInt → ℂ :=
  fun z => if Odd (gnorm z) then chi (Work.FIArea4.primAssoc z) else 0

lemma chiReal_of_odd {chi : GaussianInt → ℂ} {z : GaussianInt} (h : Odd (gnorm z)) :
    chiReal chi z = chi (Work.FIArea4.primAssoc z) := by
  unfold chiReal
  rw [if_pos h]

lemma chiReal_of_even {chi : GaussianInt → ℂ} {z : GaussianInt} (h : ¬ Odd (gnorm z)) :
    chiReal chi z = 0 := by
  unfold chiReal
  rw [if_neg h]

/-! ## Main theorem -/

theorem exists_realCharacter_agreeing_on_primary {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hreal : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z →
      Work.FIArea5.S16Hecke.IsUnitMod4d d z → chi z = star (chi z)) :
    ∃ chi' : GaussianInt → ℂ, chi' 1 = 1 ∧ (∀ z : GaussianInt, chi' z = star (chi' z)) ∧
      (∀ z w : GaussianInt, chi' (z * w) = chi' z * chi' w) ∧
      (∀ z : GaussianInt, ‖chi' z‖ ≤ 1) ∧
      (∀ z : GaussianInt, Work.FIPlan.IsPrimary z → chi z = chi' z) := by
  classical
  refine ⟨chiReal chi, ?_, ?_, ?_, ?_, ?_⟩
  · -- `χ'(1) = χ(1) = 1`
    have h1 : Odd (gnorm (1 : GaussianInt)) :=
      Work.FIArea5.S16Hecke.isPrimary_odd_gnorm Work.FIArea5.S16Hecke.isPrimary_one
    rw [chiReal_of_odd h1, Work.FIArea4.primAssoc_eq_self Work.FIArea5.S16Hecke.isPrimary_one]
    exact hchi.1.1
  · -- `χ'` is real valued: `primAssoc z` is primary, hence a unit mod `4d` (and `hreal` applies)
    -- or a zero of `χ`
    intro z
    by_cases h : Odd (gnorm z)
    · rw [chiReal_of_odd h]
      by_cases hu : Work.FIArea5.S16Hecke.IsUnitMod4d d (Work.FIArea4.primAssoc z)
      · exact hreal _ (Work.FIArea4.primAssoc_primary (ne_zero_of_odd_gnorm h) h) hu
      · rw [hchi.2 _ hu]; simp
    · rw [chiReal_of_even h]; simp
  · -- multiplicativity: the odd elements form a submonoid and everything else is killed
    intro z w
    by_cases hz : Odd (gnorm z)
    · by_cases hw : Odd (gnorm w)
      · have hzw : Odd (gnorm (z * w)) := by
          rw [Work.FIArea4.gnorm_mul]; exact hz.mul hw
        rw [chiReal_of_odd hzw, chiReal_of_odd hz, chiReal_of_odd hw, primAssoc_mul_odd hz hw]
        exact hchi.1.2.1 _ _
      · have hzw : ¬ Odd (gnorm (z * w)) := by
          rw [Work.FIArea4.gnorm_mul]
          intro hcon
          exact hw (Nat.odd_mul.mp hcon).2
        rw [chiReal_of_odd hz, chiReal_of_even hw, chiReal_of_even hzw, mul_zero]
    · have hzw : ¬ Odd (gnorm (z * w)) := by
        rw [Work.FIArea4.gnorm_mul]
        intro hcon
        exact hz (Nat.odd_mul.mp hcon).1
      rw [chiReal_of_even hz, chiReal_of_even hzw, zero_mul]
  · -- the bound `‖χ'‖ ≤ 1`
    intro z
    by_cases h : Odd (gnorm z)
    · rw [chiReal_of_odd h]; exact hchi.1.2.2.1 _
    · rw [chiReal_of_even h]; simp
  · -- agreement on the primary elements: `primAssoc z = z` there
    intro z hz
    have h : Odd (gnorm z) := Work.FIArea5.S16Hecke.isPrimary_odd_gnorm hz
    rw [chiReal_of_odd h, Work.FIArea4.primAssoc_eq_self hz]

end

end Work.FIArea6Hecke.R
