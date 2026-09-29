import Mathlib
import Submission.Work.CNum.SmallBox
import Submission.Work.CNum.NrmSpec

/-!
# `Work.CNum.AbsMaxSpec` — specification of `absMax`

`absMax I = max |I.lo| |I.hi|` (in mantissas) is an upper bound of `|x|` for every `x ∈ I`, and
the "small box" side condition `Small` makes the mantissa level sum of squares of the two
coordinate widths of `a - b` fit in the `70`-step range of the mantissa square root.

* `absMax_mem` : `I.Mem x → |x| ≤ m2r (absMax I)`.
* `absMax_sub_small` : `Small a → Small b → (absMax (sub a.re b.re))² + (absMax (sub a.im b.im))²
  < 2^70`.
-/

namespace Work.CNum

open Work.ANum
open Work.ANum.Iv

/-! ## The real value of `absMax` -/

lemma m2r_natAbs (a : ℤ) : m2r (a.natAbs : ℤ) = |m2r a| := by
  have h1 : (((a.natAbs : ℤ)) : ℝ) = |(a : ℝ)| := by
    rw [← Int.cast_abs]; congr 1; exact (Int.abs_eq_natAbs a).symm
  simp only [m2r, h1, abs_div, abs_of_pos SC_posR]

/-- `m2r (absMax I) = max |m2r I.lo| |m2r I.hi|`. -/
lemma m2r_absMax (I : Iv) : m2r (absMax I) = max |m2r I.lo| |m2r I.hi| := by
  rw [show absMax I = max (I.lo.natAbs : ℤ) (I.hi.natAbs : ℤ) from rfl]
  rw [m2r_max]
  congr 1 <;> exact m2r_natAbs _

/-- `absMax I` bounds `|x|` on `I`. -/
lemma absMax_mem (I : Iv) (x : ℝ) (h : I.Mem x) : |x| ≤ m2r (absMax I) := by
  rw [m2r_absMax]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h1 : -|m2r I.lo| ≤ m2r I.lo := neg_abs_le _
    exact le_trans (le_trans (neg_le_neg (le_max_left _ _)) h1) h.1
  · exact le_trans h.2 (le_trans (le_abs_self _) (le_max_right _ _))

/-! ## The small-box arithmetic bound -/

/-- An integer bound on `absMax` gives the analogous `ℕ` bounds on the endpoints. -/
lemma natAbs_le_of_absMax_le {I : Iv} {c : ℕ} (h : absMax I ≤ (c : ℤ)) :
    I.lo.natAbs ≤ c ∧ I.hi.natAbs ≤ c := by
  have h' : max (I.lo.natAbs : ℤ) (I.hi.natAbs : ℤ) ≤ (c : ℤ) := h
  exact ⟨by exact_mod_cast (le_trans (le_max_left _ _) h'),
         by exact_mod_cast (le_trans (le_max_right _ _) h')⟩

/-- The mantissa width of the difference of two `Small` intervals is at most `2^33`. -/
lemma absMax_sub_le (I J : Iv) (hI : absMax I ≤ (2 : ℤ) ^ 32) (hJ : absMax J ≤ (2 : ℤ) ^ 32) :
    absMax (Iv.sub I J) ≤ (2 : ℤ) ^ 33 := by
  obtain ⟨hIlo, hIhi⟩ := natAbs_le_of_absMax_le hI
  obtain ⟨hJlo, hJhi⟩ := natAbs_le_of_absMax_le hJ
  have hlo : (I.lo - J.hi).natAbs ≤ (2 : ℕ) ^ 33 := by
    have h1 := Int.natAbs_sub_le I.lo J.hi
    have hab : I.lo.natAbs + J.hi.natAbs ≤ (2 : ℕ) ^ 32 + (2 : ℕ) ^ 32 := Nat.add_le_add hIlo hJhi
    have h2 : (2 : ℕ) ^ 32 + (2 : ℕ) ^ 32 = (2 : ℕ) ^ 33 := by norm_num
    omega
  have hhi : (I.hi - J.lo).natAbs ≤ (2 : ℕ) ^ 33 := by
    have h1 := Int.natAbs_sub_le I.hi J.lo
    have hab : I.hi.natAbs + J.lo.natAbs ≤ (2 : ℕ) ^ 32 + (2 : ℕ) ^ 32 := Nat.add_le_add hIhi hJlo
    have h2 : (2 : ℕ) ^ 32 + (2 : ℕ) ^ 32 = (2 : ℕ) ^ 33 := by norm_num
    omega
  show max ((I.lo - J.hi).natAbs : ℤ) ((I.hi - J.lo).natAbs : ℤ) ≤ (2 : ℤ) ^ 33
  have h2 : (((2 : ℕ) ^ 33 : ℕ) : ℤ) = (2 : ℤ) ^ 33 := by norm_num
  rw [← h2]
  exact max_le (by exact_mod_cast hlo) (by exact_mod_cast hhi)

/-- The `Small` side condition keeps the mantissa sum of squares within the `70`-step range. -/
lemma absMax_sub_small (a b : Cpx) (ha : Small a) (hb : Small b) :
    ((absMax (Iv.sub a.re b.re)) * (absMax (Iv.sub a.re b.re))
      + (absMax (Iv.sub a.im b.im)) * (absMax (Iv.sub a.im b.im))).toNat < 2 ^ 70 := by
  have hdx : absMax (Iv.sub a.re b.re) ≤ (2 : ℤ) ^ 33 := absMax_sub_le a.re b.re ha.1 hb.1
  have hdy : absMax (Iv.sub a.im b.im) ≤ (2 : ℤ) ^ 33 := absMax_sub_le a.im b.im ha.2 hb.2
  have hdx0 : 0 ≤ absMax (Iv.sub a.re b.re) := absMax_nonneg _
  have hdy0 : 0 ≤ absMax (Iv.sub a.im b.im) := absMax_nonneg _
  have hx34 : (absMax (Iv.sub a.re b.re)).natAbs ≤ (2 : ℕ) ^ 34 := by
    have h1 : ((absMax (Iv.sub a.re b.re)).natAbs : ℤ) ≤ (((2 : ℕ) ^ 34 : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg hdx0]
      have h2 : (((2 : ℕ) ^ 34 : ℕ) : ℤ) = (2 : ℤ) ^ 34 := by norm_num
      rw [h2]; linarith [(by norm_num : (2 : ℤ) ^ 33 ≤ (2 : ℤ) ^ 34)]
    exact_mod_cast h1
  have hy34 : (absMax (Iv.sub a.im b.im)).natAbs ≤ (2 : ℕ) ^ 34 := by
    have h1 : ((absMax (Iv.sub a.im b.im)).natAbs : ℤ) ≤ (((2 : ℕ) ^ 34 : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg hdy0]
      have h2 : (((2 : ℕ) ^ 34 : ℕ) : ℤ) = (2 : ℤ) ^ 34 := by norm_num
      rw [h2]; linarith [(by norm_num : (2 : ℤ) ^ 33 ≤ (2 : ℤ) ^ 34)]
    exact_mod_cast h1
  exact (natAbs_sq_add hx34 hy34).1

theorem AbsMaxSpec : (∀ (I : Work.ANum.Iv) (x : ℝ), I.Mem x → |x| ≤ Work.ANum.m2r (Work.CNum.absMax I)) ∧ (∀ (a b : Work.CNum.Cpx), Work.CNum.Small a → Work.CNum.Small b → ((Work.CNum.absMax (Work.ANum.Iv.sub a.re b.re)) * (Work.CNum.absMax (Work.ANum.Iv.sub a.re b.re)) + (Work.CNum.absMax (Work.ANum.Iv.sub a.im b.im)) * (Work.CNum.absMax (Work.ANum.Iv.sub a.im b.im))).toNat < 2 ^ 70) := by
  exact ⟨fun I x h => absMax_mem I x h, fun a b ha hb => absMax_sub_small a b ha hb⟩

end Work.CNum
