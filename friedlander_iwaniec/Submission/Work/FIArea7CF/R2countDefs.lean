/-
# `Submission.Work.FIArea7CF.R2countDefs` — clash-free copy of `Submission.Work.FIArea7.R2countDefs`

Imports redirected to the `FIArea7CF` copies; renamed: mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.ACDefs

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The finset of Gaussian integers of norm exactly `n`, cut down to the box `gBox n`.
By definition this is the finset `r2count n` counts. -/
def Sz (n : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (n : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n)

lemma r2count_eq_Sz_card (n : ℕ) : r2count n = (Sz n).card := rfl

/-- Membership in the box, in coordinates. -/
lemma r2c_mem_gBox_iff {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ z.re ∈ Icc (-R) R ∧ z.im ∈ Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [Finset.mem_product] using hq
  · intro h
    exact ⟨(z.re, z.im), by simpa [Finset.mem_product] using h, rfl⟩

lemma mem_Sz_iff {n : ℕ} {z : GaussianInt} :
    z ∈ Sz n ↔ Work.FIPlan.gnorm z = n ∧ z ∈ Work.FIPlan.gBox (n : ℤ) := by
  rw [Sz, Finset.mem_filter]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

lemma gnorm_mul (a b : GaussianInt) :
    Work.FIPlan.gnorm (a * b) = Work.FIPlan.gnorm a * Work.FIPlan.gnorm b := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

lemma gnorm_star (a : GaussianInt) :
    Work.FIPlan.gnorm (star a) = Work.FIPlan.gnorm a := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_conj]

lemma gnorm_one : Work.FIPlan.gnorm (1 : GaussianInt) = 1 := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_one, Int.natAbs_one]

lemma gnorm_pow (a : GaussianInt) (i : ℕ) :
    Work.FIPlan.gnorm (a ^ i) = Work.FIPlan.gnorm a ^ i := by
  induction i with
  | zero => simpa using gnorm_one
  | succ i ih => rw [pow_succ, gnorm_mul, ih, pow_succ]

lemma gnorm_eq_zero_iff {z : GaussianInt} : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  rw [Work.FIPlan.gnorm, Int.natAbs_eq_zero]
  exact Zsqrtd.norm_eq_zero_iff (by norm_num) z

lemma gnorm_natCast (n : ℕ) : Work.FIPlan.gnorm ((n : ℕ) : GaussianInt) = n ^ 2 := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast, pow_two]

lemma mul_star_eq_gnorm (z : GaussianInt) :
    z * star z = ((Work.FIPlan.gnorm z : ℕ) : GaussianInt) := by
  have h : ((z.norm.natAbs : ℤ) : GaussianInt) = z * star z := by
    rw [Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num) z)]
    exact Zsqrtd.norm_eq_mul_conj z
  rw [← h, Int.cast_natCast]
  rfl

lemma re_natAbs_le_gnorm (z : GaussianInt) : z.re.natAbs ≤ Work.FIPlan.gnorm z := by
  have h := GaussianInt.natAbs_norm_eq z
  rw [Work.FIPlan.gnorm, h]
  exact le_trans (Nat.le_mul_self _) (Nat.le_add_right _ _)

lemma im_natAbs_le_gnorm (z : GaussianInt) : z.im.natAbs ≤ Work.FIPlan.gnorm z := by
  have h := GaussianInt.natAbs_norm_eq z
  rw [Work.FIPlan.gnorm, h]
  exact le_trans (Nat.le_mul_self _) (Nat.le_add_left _ _)

/-- A Gaussian integer of norm `n` lies in the box `gBox n`. -/
lemma mem_gBox_of_gnorm_eq {z : GaussianInt} {n : ℕ} (h : Work.FIPlan.gnorm z = n) :
    z ∈ Work.FIPlan.gBox (n : ℤ) := by
  rw [r2c_mem_gBox_iff]
  have hre : |z.re| ≤ (n : ℤ) := by
    have h1 : z.re.natAbs ≤ n := by rw [← h]; exact re_natAbs_le_gnorm z
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1
  have him : |z.im| ≤ (n : ℤ) := by
    have h1 : z.im.natAbs ≤ n := by rw [← h]; exact im_natAbs_le_gnorm z
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1
  exact ⟨by rw [Finset.mem_Icc]; exact abs_le.mp hre,
         by rw [Finset.mem_Icc]; exact abs_le.mp him⟩

lemma mem_Sz_of_gnorm_eq {z : GaussianInt} {n : ℕ} (h : Work.FIPlan.gnorm z = n) :
    z ∈ Sz n := by
  rw [mem_Sz_iff]
  exact ⟨h, mem_gBox_of_gnorm_eq h⟩

end

end Work.FIArea7
