import Mathlib
import Submission.Work.Peluse.MajorArc.Defs

/-!
# Constants shared by the `U²`-inverse entry of the `Ulower` chain

This module only fixes the two numerical quantities that depend on the polynomial `P` in the
constant bookkeeping of `Work.Peluse.Ulower.ss_char_entry`:

* `coeffSum P = ∑_i |a_i|`, a bound for the coefficients of `P` (used to bound `polySup P N` by
  `coeffSum P · N ^ P.natDegree`), and
* `ssAmax P = 3 + 2 · coeffSum P`, the constant `A_P ≥ 1` with
  `max (dSup P Ns N / |c| + 1) D ≤ ssAmax P · Ns` whenever `Scaled Ns N P.natDegree` holds.

They are separated out so that the auxiliary lemmas of the entry can be stated without importing
the (still incomplete) target module. -/
set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- The sum of the absolute values of the coefficients of `P`.  For `N ≥ 1` it dominates
`polySup P N / N ^ P.natDegree`. -/
def coeffSum (P : Polynomial ℤ) : ℕ :=
  ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).natAbs

/-- The uniform constant `A_P = 3 + 2·coeffSum P` of the support-box bookkeeping. -/
def ssAmax (P : Polynomial ℤ) : ℕ := 3 + 2 * coeffSum P

/-- `coeffSum P` dominates each `|coeff i|`. -/
lemma coeff_natAbs_le_coeffSum (P : Polynomial ℤ) (i : ℕ) :
    (P.coeff i).natAbs ≤ coeffSum P := by
  rw [coeffSum]
  by_cases hi : i ≤ P.natDegree
  · exact Finset.single_le_sum (f := fun j => (P.coeff j).natAbs) (fun j _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  · have hzero : P.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_le hi)
    rw [hzero]
    simp

/-- `ssAmax P` is at least `3`. -/
lemma three_le_ssAmax (P : Polynomial ℤ) : 3 ≤ ssAmax P := by
  rw [ssAmax]
  omega

lemma ssAmax_pos (P : Polynomial ℤ) : 0 < ssAmax P := by
  have := three_le_ssAmax P
  omega

/-- **Support of a dilate.**  If `F` is supported in `[-L,L]`, `c ≠ 0` and `0 ≤ r < |c|`, then
`z ↦ F (c*z + r)` is supported in `[-max (L/|c| + 1) D, max (L/|c| + 1) D]` for every `D`: if
`|z| > L/|c| + 1` then `|c*z + r| ≥ |c|·|z| - r > L`. -/
lemma ss_support_dilate {c : ℤ} (hc : c ≠ 0) {D L : ℕ} (F : ℤ → ℂ)
    (hFs : Work.Peluse.SupportIn F L) (r : ℕ) (hr : r < c.natAbs) :
    Work.Peluse.SupportIn (fun z : ℤ => F (c * z + (r : ℤ))) (max (L / c.natAbs + 1) D) := by
  have hm : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  have hrle : r + 1 ≤ c.natAbs := hr
  intro z hz
  apply hFs
  -- `z.natAbs ≥ L/|c| + 2`
  have hz2 : L / c.natAbs + 2 ≤ z.natAbs := by omega
  -- lower bound for `(c * z + r).natAbs`
  have htri : (c * z).natAbs ≤ (c * z + (r : ℤ)).natAbs + r := by
    have h := Int.natAbs_sub_le (c * z + (r : ℤ)) (r : ℤ)
    rw [add_sub_cancel_right] at h
    simpa using h
  rw [Int.natAbs_mul] at htri
  -- `|c| * z.natAbs ≥ L + 1 + (|c| - 1)`... get `L + 1 ≤ |c| * z.natAbs - r`
  have hdiv : c.natAbs * (L / c.natAbs) + L % c.natAbs = L := Nat.div_add_mod L c.natAbs
  have hmod : L % c.natAbs + 1 ≤ c.natAbs := Nat.succ_le_of_lt (Nat.mod_lt L hm)
  have hmul : c.natAbs * (L / c.natAbs + 2) = c.natAbs * (L / c.natAbs) + 2 * c.natAbs := by ring
  have hkey : L + 1 + r ≤ c.natAbs * z.natAbs := by
    have h2 : c.natAbs * (L / c.natAbs + 2) ≤ c.natAbs * z.natAbs :=
      Nat.mul_le_mul_left _ hz2
    rw [hmul] at h2
    have hr' : r + 1 ≤ c.natAbs := hrle
    omega
  -- conclude
  have : L < (c * z + (r : ℤ)).natAbs := by omega
  simpa using this

/-- The character `Work.Peluse.ee (ξ * x)` written in the form used by the statement. -/
lemma ss_ee_eq_exp (ξ : ℝ) (x : ℤ) :
    Work.Peluse.ee (ξ * (x : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ)) := by
  rw [Work.Peluse.ee]
  congr 1
  push_cast
  ring

/-- Membership in the symmetric interval, in terms of `Int.natAbs`. -/
lemma symIcc_mem_iff {L : ℕ} {x : ℤ} : x ∈ Work.Peluse.symIcc L ↔ x.natAbs ≤ L := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (x.natAbs : ℤ) ≤ (L : ℤ) := by
      rw [Int.natCast_natAbs]
      exact abs_le.mpr ⟨h1, h2⟩
    exact_mod_cast h3
  · intro h
    have h3 : (x.natAbs : ℤ) ≤ (L : ℤ) := by exact_mod_cast h
    rw [Int.natCast_natAbs] at h3
    exact abs_le.mp h3

end

end Work.Peluse.Ulower
