import Mathlib
import Submission.Work.KMTPlan.A6.sum_Ico_one_div_sq_le
import Submission.Work.KMTPlan.A6.sum_Icc_int_eq_sum_Ico_nat
import Submission.Work.KMTPlan.A6.sum_Icc_neg_eq_of_even

/-!
# The weak-type `ℓ¹` mass of the weight `r ∧ r⁻¹ (2π|p|)⁻²`

This file proves `Work.KMTPlan.A6.wt_tsum_le`: for `0 < r ≤ 1` the weight

  `w_r(p) = if p = 0 then r else min r (r⁻¹ / (2 π |p|)²)`   (`p : ℤ`)

is summable and `∑'_p w_r(p) ≤ 4`.

The weight is a plateau of height `r` and half-width `K = ⌈1/(2πr)⌉`, followed by a quadratic
tail.  The whole estimate is therefore a finite count (`≈ 1/π`) plus a telescoping/integral
bound for `∑ 1/p²` (`≈ 1/π`); the constant `4` has plenty of room.
-/

namespace Work.KMTPlan.A6

open Finset

noncomputable section

/-- The weight of `wt_tsum_le`, isolated as a definition. -/
def wtW (r : ℝ) (p : ℤ) : ℝ :=
  if p = 0 then r else min r (r⁻¹ / (2 * Real.pi * |(p : ℝ)|) ^ 2)

lemma wtW_nonneg {r : ℝ} (hr : 0 < r) (p : ℤ) : 0 ≤ wtW r p := by
  rw [wtW]; split_ifs with h
  · exact hr.le
  · exact le_min hr.le (by positivity)

lemma wtW_le_r (r : ℝ) (p : ℤ) : wtW r p ≤ r := by
  rw [wtW]; split_ifs with h
  · exact le_rfl
  · exact min_le_left _ _

lemma wtW_even (r : ℝ) (p : ℤ) : wtW r (-p) = wtW r p := by
  rw [wtW, wtW]
  rcases eq_or_ne p 0 with h | h
  · subst h; simp
  · rw [if_neg (neg_ne_zero.mpr h), if_neg h, Int.cast_neg, abs_neg]

/-- The elementary inequality `r⁻¹/(2π|x|)² ≤ r` for `|x| > 1/(2πr)`. -/
lemma inv_div_sq_le {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : 1 / (2 * Real.pi * r) < |x|) :
    r⁻¹ / (2 * Real.pi * |x|) ^ 2 ≤ r := by
  have hpos : 0 < 2 * Real.pi * r := by positivity
  have hxpos : 0 < |x| := lt_of_lt_of_le (by positivity) hx.le
  have h1 : 1 < 2 * Real.pi * r * |x| := by
    rw [div_lt_iff₀ hpos] at hx
    linarith [hx]
  have h2 : 1 ≤ (2 * Real.pi * r * |x|) ^ 2 := by
    have hz1 : 0 < 2 * Real.pi * r * |x| - 1 := by linarith
    have hz2 : 0 < 2 * Real.pi * r * |x| + 1 := by linarith
    nlinarith [mul_pos hz1 hz2]
  have hden : 0 < (2 * Real.pi * |x|) ^ 2 := by positivity
  rw [div_le_iff₀ hden, inv_le_iff_one_le_mul₀ hr]
  nlinarith [h2]

/-- On the far tail `wtW` is exactly the quadratic weight `r⁻¹/(4π²) · 1/p²`. -/
lemma wtW_eq_tail {r : ℝ} (hr : 0 < r) {p : ℤ} (hp : 1 / (2 * Real.pi * r) < |(p : ℝ)|) :
    wtW r p = r⁻¹ / (4 * Real.pi ^ 2) * (1 / (p : ℝ) ^ 2) := by
  have hne : p ≠ 0 := by
    intro h0
    rw [h0] at hp
    simp only [Int.cast_zero, abs_zero] at hp
    exact absurd hp (not_lt.mpr (by positivity))
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hne
  rw [wtW, if_neg hne, min_eq_right (inv_div_sq_le hr hp)]
  have hsq : (2 * Real.pi * |(p : ℝ)|) ^ 2 = 4 * Real.pi ^ 2 * (p : ℝ) ^ 2 := by
    rw [mul_pow, sq_abs]; ring
  rw [hsq]
  field_simp

/-! ### The tail sums -/

/-- The positive far tail of the weight is dominated by `r⁻¹/(4π²) · ∑ 1/p² ≤ r⁻¹/(4π²) · 1/K`. -/
lemma sum_Icc_wtW_tail {r : ℝ} (hr : 0 < r) {K M : ℕ}
    (hK : 1 / (2 * Real.pi * r) ≤ (K : ℝ)) :
    ∑ p ∈ Finset.Icc ((K : ℤ) + 1) (M : ℤ), wtW r p
      ≤ r⁻¹ / (4 * Real.pi ^ 2) * (1 / (K : ℝ)) := by
  have hK1 : 1 ≤ K := by
    have hpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le (by positivity) hK
    exact Nat.one_le_iff_ne_zero.mpr fun h => by rw [h] at hpos; norm_num at hpos
  have hpt : ∀ p ∈ Finset.Icc ((K : ℤ) + 1) (M : ℤ),
      wtW r p ≤ r⁻¹ / (4 * Real.pi ^ 2) * (1 / (p : ℝ) ^ 2) := by
    intro p hp
    rw [Finset.mem_Icc] at hp
    have h1 : ((K : ℤ) + 1 : ℤ) ≤ p := hp.1
    have h2 : ((K : ℝ) + 1) ≤ (p : ℝ) := by
      have : (((K : ℤ) + 1 : ℤ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
      simpa using this
    have h3 : 1 / (2 * Real.pi * r) < |(p : ℝ)| := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact (wtW_eq_tail hr h3).le
  calc ∑ p ∈ Finset.Icc ((K : ℤ) + 1) (M : ℤ), wtW r p
      ≤ ∑ p ∈ Finset.Icc ((K : ℤ) + 1) (M : ℤ),
          r⁻¹ / (4 * Real.pi ^ 2) * (1 / (p : ℝ) ^ 2) := Finset.sum_le_sum hpt
    _ = r⁻¹ / (4 * Real.pi ^ 2) *
          ∑ p ∈ Finset.Icc ((K : ℤ) + 1) (M : ℤ), (1 / (p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ r⁻¹ / (4 * Real.pi ^ 2) * (1 / (K : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [sum_Icc_int_eq_sum_Ico_nat (fun p : ℤ => (1 : ℝ) / ((p : ℝ) ^ 2)) K M]
        simpa using sum_Ico_one_div_sq_le K M hK1

/-- The negative far tail has the same bound, by the reflection symmetry of `wtW`. -/
lemma sum_Icc_wtW_negtail {r : ℝ} (hr : 0 < r) {K M : ℕ}
    (hK : 1 / (2 * Real.pi * r) ≤ (K : ℝ)) :
    ∑ p ∈ Finset.Icc (-(M : ℤ)) (-((K : ℤ) + 1)), wtW r p
      ≤ r⁻¹ / (4 * Real.pi ^ 2) * (1 / (K : ℝ)) := by
  rw [sum_Icc_neg_eq_of_even (wtW r) (wtW_even r) K M]
  exact sum_Icc_wtW_tail hr hK

/-! ### The plateau -/

/-- The plateau of the weight: at most `2K+1` terms, each of size at most `r`. -/
lemma sum_Icc_wtW_plateau {r : ℝ} (K : ℕ) :
    ∑ p ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), wtW r p ≤ r * ((2 * K + 1 : ℕ) : ℝ) := by
  calc ∑ p ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), wtW r p
      ≤ ∑ _p ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), r := Finset.sum_le_sum fun p _ => wtW_le_r r p
    _ = ((2 * K + 1 : ℕ) : ℝ) * r := by
        rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
        have hcard : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by omega
        rw [hcard, Int.toNat_natCast]
    _ = r * ((2 * K + 1 : ℕ) : ℝ) := by ring

/-! ### Splitting a symmetric window into plateau and two tails -/

lemma Icc_subset_three (K M : ℕ) :
    Finset.Icc (-(M : ℤ)) (M : ℤ) ⊆
      Finset.Icc (-(M : ℤ)) (-((K : ℤ) + 1)) ∪ Finset.Icc (-(K : ℤ)) (K : ℤ) ∪
        Finset.Icc ((K : ℤ) + 1) (M : ℤ) := by
  intro p hp
  rw [Finset.mem_Icc] at hp
  rw [Finset.mem_union, Finset.mem_union]
  by_cases h1 : p < -((K : ℤ))
  · left; left; rw [Finset.mem_Icc]; exact ⟨hp.1, by omega⟩
  · have h1' : -((K : ℤ)) ≤ p := not_lt.mp h1
    by_cases h2 : ((K : ℤ)) < p
    · right; rw [Finset.mem_Icc]; exact ⟨by omega, hp.2⟩
    · have h2' : p ≤ (K : ℤ) := not_lt.mp h2
      left; right; rw [Finset.mem_Icc]; exact ⟨h1', h2'⟩

lemma sum_union_le_sum {s t : Finset ℤ} {f : ℤ → ℝ} (h : ∀ i ∈ s ∪ t, 0 ≤ f i) :
    ∑ i ∈ s ∪ t, f i ≤ ∑ i ∈ s, f i + ∑ i ∈ t, f i := by
  rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff]
  have hsub : ∑ i ∈ t \ s, f i ≤ ∑ i ∈ t, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i hi _ => h i (Finset.mem_union_right s hi))
  linarith

/-- The symmetric-window bound: `∑_{|p| ≤ M} w_r(p) ≤ 4`. -/
theorem sum_Icc_wtW_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (M : ℕ) :
    ∑ p ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), wtW r p ≤ 4 := by
  set K := Nat.ceil (1 / (2 * Real.pi * r)) with hKdef
  have hKle : 1 / (2 * Real.pi * r) ≤ (K : ℝ) := by
    have h := Nat.le_ceil (1 / (2 * Real.pi * r))
    rwa [← hKdef] at h
  have hKlt : (K : ℝ) < 1 / (2 * Real.pi * r) + 1 := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 / (2 * Real.pi * r) by positivity)
    rwa [← hKdef] at h
  have hpi3 : 1 / Real.pi ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (le_of_lt Real.pi_gt_three)
  -- the plateau bound, in a form suitable for `linarith`
  have hArith : r * ((2 * K + 1 : ℕ) : ℝ) ≤ 1 / Real.pi + 3 * r := by
    have h2 : 2 * (1 / (2 * Real.pi * r)) = 1 / (Real.pi * r) := by field_simp
    have hKinv : 2 * (K : ℝ) + 1 < 1 / (Real.pi * r) + 3 := by linarith [hKlt, h2]
    have hcast : ((2 * K + 1 : ℕ) : ℝ) = 2 * (K : ℝ) + 1 := by push_cast; ring
    have hr3 : r * (1 / (Real.pi * r) + 3) = 1 / Real.pi + 3 * r := by field_simp
    have hmul := mul_lt_mul_of_pos_left hKinv hr
    rw [hr3] at hmul
    rw [hcast]
    linarith [hmul.le]
  -- the tail bound
  have htail : r⁻¹ / (4 * Real.pi ^ 2) * (1 / (K : ℝ)) ≤ 1 / (2 * Real.pi) := by
    have hKinv : 1 / (K : ℝ) ≤ 2 * Real.pi * r := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 / (2 * Real.pi * r) by positivity) hKle
      rwa [one_div_div, div_one] at h
    calc r⁻¹ / (4 * Real.pi ^ 2) * (1 / (K : ℝ))
        ≤ r⁻¹ / (4 * Real.pi ^ 2) * (2 * Real.pi * r) :=
          mul_le_mul_of_nonneg_left hKinv (by positivity)
      _ = 1 / (2 * Real.pi) := by field_simp; norm_num
  -- numeric conclusion
  have hA2 : 2 * (r⁻¹ / (4 * Real.pi ^ 2) * (1 / (K : ℝ))) ≤ 1 / Real.pi := by
    have h2 : (2 : ℝ) * (1 / (2 * Real.pi)) = 1 / Real.pi := by field_simp
    linarith [htail, h2]
  have hB2 : r * ((2 * K + 1 : ℕ) : ℝ) ≤ 1 / 3 + 3 := by linarith [hArith, hr1, hpi3]
  -- the three-piece split
  have hsplit : ∑ p ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), wtW r p
      ≤ (∑ p ∈ Finset.Icc (-(M : ℤ)) (-((K : ℤ) + 1)), wtW r p
            + ∑ p ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), wtW r p)
          + ∑ p ∈ Finset.Icc ((K : ℤ) + 1) (M : ℤ), wtW r p := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_three K M)
      (fun i _ _ => wtW_nonneg hr i)) ?_
    refine le_trans (sum_union_le_sum (s := Finset.Icc (-(M : ℤ)) (-((K : ℤ) + 1)) ∪
      Finset.Icc (-(K : ℤ)) (K : ℤ)) (t := Finset.Icc ((K : ℤ) + 1) (M : ℤ))
      (f := wtW r) (fun i _ => wtW_nonneg hr i)) ?_
    have hAB : ∑ i ∈ Finset.Icc (-(M : ℤ)) (-((K : ℤ) + 1)) ∪ Finset.Icc (-(K : ℤ)) (K : ℤ),
        wtW r i
        ≤ ∑ i ∈ Finset.Icc (-(M : ℤ)) (-((K : ℤ) + 1)), wtW r i
          + ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), wtW r i :=
      sum_union_le_sum (fun i _ => wtW_nonneg hr i)
    linarith [hAB]
  refine le_trans hsplit ?_
  have h1 := sum_Icc_wtW_negtail hr (M := M) hKle
  have h2 := sum_Icc_wtW_plateau (r := r) K
  have h3 := sum_Icc_wtW_tail hr (K := K) (M := M) hKle
  linarith [h1, h2, h3, hA2, hB2]

/-! ### From finite subsets of `ℤ` to symmetric windows -/

/-- For every finite set of integers, `∑_{p ∈ u} w_r(p) ≤ 4`. -/
theorem sum_finset_wtW_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (u : Finset ℤ) :
    ∑ p ∈ u, wtW r p ≤ 4 := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
    (fun i _ _ => wtW_nonneg hr i)) (sum_Icc_wtW_le r hr hr1 (u.sup fun q => q.natAbs))
  intro p hp
  rw [Finset.mem_Icc]
  have hle : p.natAbs ≤ u.sup fun q => q.natAbs := Finset.le_sup hp
  have h2 : |p| ≤ ((u.sup fun q => q.natAbs : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hle
  exact abs_le.mp h2

/-- **The weak-type `ℓ¹` mass of the weight**: summable, with total mass at most `4`. -/
theorem wt_tsum_le (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    Summable (fun p : ℤ =>
        if p = 0 then r else min r (r⁻¹ / (2 * Real.pi * |(p : ℝ)|) ^ 2))
      ∧ (∑' p : ℤ,
          (if p = 0 then r else min r (r⁻¹ / (2 * Real.pi * |(p : ℝ)|) ^ 2))) ≤ 4 := by
  have hnn : ∀ p : ℤ, 0 ≤ wtW r p := wtW_nonneg hr
  have hfin : ∀ u : Finset ℤ, ∑ p ∈ u, wtW r p ≤ 4 := sum_finset_wtW_le r hr hr1
  refine ⟨?_, ?_⟩
  · change Summable (fun p : ℤ => wtW r p)
    exact summable_of_sum_le hnn hfin
  · change (∑' p : ℤ, wtW r p) ≤ 4
    exact Real.tsum_le_of_sum_le hnn hfin

end

end Work.KMTPlan.A6
