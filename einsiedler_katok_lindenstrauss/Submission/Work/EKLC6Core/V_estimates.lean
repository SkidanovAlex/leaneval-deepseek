import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLComp.inv_mem_V
import Submission.Work.EKLRelCross.flower_balls
import Submission.Work.EKLC6Core.aeBall_V_inv

/-!
# Estimates on products of `V s`-small displacements

`V δ = {g : SL₃(ℝ) | ∀ i j, |g i j - 1 i j| < δ}` is the entrywise `δ`-neighbourhood of the
identity.  This file records the two group-law estimates needed downstream:

* `g ∈ V s`, `h ∈ V t` ⟹ `g * h ∈ V (s + t + 3 s t)` (the elementary "Maurer–Cartan" bound
  `(g-1)(h-1) + (g-1) + (h-1)` on the product);
* hence, for `0 < s ≤ 1/10`:
  * `a, b ∈ V s ⟹ a * b ∈ V (5 s)` (`s + s + 3 s² ≤ 5 s`),
  * `a, b ∈ V s ⟹ a * b⁻¹ ∈ V (14 s)`, `a⁻¹ * b ∈ V (14 s)`
    (using `b⁻¹ ∈ V (10 s)` from `Work.EKLComp.inv_mem_V`,
     since `s + 10 s + 30 s² ≤ 14 s`).
-/

namespace Work.EKLC6Core

open Work.EKLContract

/-- `V` is monotone in its radius. -/
private lemma V_mono' {δ δ' : ℝ} (h : δ ≤ δ') : V δ ⊆ V δ' :=
  fun _ hg i j => lt_of_lt_of_le (hg i j) h

/-- The first-order product estimate: if `g` is `s`-close to `1` and `h` is `t`-close to `1`,
then `g * h` is `(s + t + 3 s t)`-close to `1`.  The bound is the exact "Taylor expansion"

`g h - 1 = (g - 1)(h - 1) + (g - 1) + (h - 1)`,

whose three terms have entrywise sizes at most `3 s t`, `s`, `t`. -/
private lemma mul_mem_V_of {s t : ℝ} {g h : SL3}
    (hg : g ∈ V s) (hh : h ∈ V t) : g * h ∈ V (s + t + 3 * s * t) := by
  intro i j
  have hX : ∀ k l : Fin 3, |(toMat g - 1) k l| < s := by
    intro k l; rw [Matrix.sub_apply, Matrix.one_apply]; exact hg k l
  have hY : ∀ k l : Fin 3, |(toMat h - 1) k l| < t := by
    intro k l; rw [Matrix.sub_apply, Matrix.one_apply]; exact hh k l
  change |(toMat (g * h) - 1) i j| < s + t + 3 * s * t
  have key : (toMat (g * h) - 1) i j
      = ((toMat g - 1) * (toMat h - 1)) i j + (toMat g - 1) i j + (toMat h - 1) i j := by
    have h2 : toMat (g * h) - 1
        = (toMat g - 1) * (toMat h - 1) + (toMat g - 1) + (toMat h - 1) := by
      rw [toMat_mul]
      noncomm_ring
    rw [h2, Matrix.add_apply, Matrix.add_apply]
  rw [key]
  have hXY : |((toMat g - 1) * (toMat h - 1)) i j| ≤ 3 * s * t := by
    rw [Matrix.mul_apply]
    calc |∑ k, (toMat g - 1) i k * (toMat h - 1) k j|
        ≤ ∑ k, |(toMat g - 1) i k * (toMat h - 1) k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 3, s * t := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          exact le_of_lt (mul_lt_mul_of_nonneg (hX i k) (hY k j) (abs_nonneg _) (abs_nonneg _))
      _ = 3 * s * t := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num; ring
  have htri : |((toMat g - 1) * (toMat h - 1)) i j + (toMat g - 1) i j + (toMat h - 1) i j|
      ≤ |((toMat g - 1) * (toMat h - 1)) i j| + |(toMat g - 1) i j| + |(toMat h - 1) i j| := by
    have h1 := abs_add_le (((toMat g - 1) * (toMat h - 1)) i j + (toMat g - 1) i j)
      ((toMat h - 1) i j)
    have h2 := abs_add_le (((toMat g - 1) * (toMat h - 1)) i j) ((toMat g - 1) i j)
    linarith [abs_nonneg ((toMat g - 1) i j), abs_nonneg ((toMat h - 1) i j),
      abs_nonneg (((toMat g - 1) * (toMat h - 1)) i j)]
  linarith [htri, hXY, hX i j, hY i j]

/-- Inverse of a small displacement (radius `≤ 1`) is a displacement of radius `10 s`. -/
private lemma inv_mem_V' {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {g : SL3} (hg : g ∈ V s) :
    g⁻¹ ∈ V (10 * s) :=
  Work.EKLComp.inv_mem_V hs hs1 hg

theorem V_estimates {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/10) :
    (∀ a b : Work.EKLContract.SL3, a ∈ Work.EKLContract.V s → b ∈ Work.EKLContract.V s →
      a * b ∈ Work.EKLContract.V (5 * s)) ∧
    (∀ a b : Work.EKLContract.SL3, a ∈ Work.EKLContract.V s → b ∈ Work.EKLContract.V s →
      a * b⁻¹ ∈ Work.EKLContract.V (14 * s)) ∧
    (∀ a b : Work.EKLContract.SL3, a ∈ Work.EKLContract.V s → b ∈ Work.EKLContract.V s →
      a⁻¹ * b ∈ Work.EKLContract.V (14 * s)) := by
  have hsle1 : s ≤ 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro a b ha hb
    refine V_mono' ?_ (mul_mem_V_of ha hb)
    nlinarith [hs, hs1]
  · intro a b ha hb
    have hbinv : b⁻¹ ∈ V (10 * s) := inv_mem_V' hs hsle1 hb
    refine V_mono' ?_ (mul_mem_V_of ha hbinv)
    nlinarith [hs, hs1]
  · intro a b ha hb
    have hainv : a⁻¹ ∈ V (10 * s) := inv_mem_V' hs hsle1 ha
    refine V_mono' ?_ (mul_mem_V_of hainv hb)
    nlinarith [hs, hs1]

end Work.EKLC6Core
