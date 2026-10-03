import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs

namespace Work.KMTPlan.A6

/-- **The lacunary reciprocal sum is dominated by its smallest term.**

For a `Λ`-lacunary sequence `a : ℕ → ℝ≥0` with `Λ > 1` and `a n ≥ 1`, and any set `P` of indices
whose elements satisfy `a m ≤ a n`, the sum of the reciprocals of `a` over `P` is bounded by
`Λ / (Λ - 1)` times the reciprocal of the smallest term `a m`.

Indeed `a` is strictly increasing (`Λ * a n ≤ a (n + 1)` with `a n > 0` and `Λ > 1`), so `P`
contains only indices `n ≥ m`, and `Λ ^ (n - m) * a m ≤ a n` gives `(a n)⁻¹ ≤ (a m)⁻¹ * Λ ^ (-(n-m))`.
Summing the geometric series over `n ≥ m` gives the factor `∑_{k≥0} Λ ^ (-k) = Λ/(Λ-1)`. -/
theorem lacunarySumInv (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (P : ℕ → Prop)
    [DecidablePred P] {m : ℕ}
    (hm : ∀ n, P n → a m ≤ a n) :
    (∑' n : ℕ, if P n then (((a n : ℝ))⁻¹) else 0)
      ≤ (Λ : ℝ) / ((Λ : ℝ) - 1) * (((a m : ℝ))⁻¹) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by linarith
  -- the one-step growth, in `ℝ≥0`
  have hgr : ∀ n, Λ * a n ≤ a (n + 1) := by
    intro n
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    exact le_of_lt ((lt_div_iff₀ hpos).mp (ha n))
  -- `a` is strictly increasing
  have hstrict : ∀ n, a n < a (n + 1) := by
    intro n
    have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    have h1 : a n < Λ * a n := by
      calc a n = 1 * a n := (one_mul _).symm
        _ < Λ * a n := mul_lt_mul_of_pos_right hΛ hpos
    exact lt_of_lt_of_le h1 (hgr n)
  have hmono : StrictMono a := strictMono_nat_of_lt_succ hstrict
  have hle_m : ∀ n, P n → m ≤ n := by
    intro n hn
    by_contra h
    exact (not_lt_of_ge (hm n hn)) (hmono (not_le.mp h))
  have haposR : ∀ n, (0 : ℝ) < (a n : ℝ) := fun n => by
    have h := ha1 n
    exact_mod_cast (lt_of_lt_of_le zero_lt_one h)
  -- iterated growth: `Λ ^ k * a p ≤ a (p + k)`
  have hpow : ∀ p k, (Λ : ℝ) ^ k * (a p : ℝ) ≤ (a (p + k) : ℝ) := by
    intro p k
    induction k with
    | zero => simp
    | succ j ih =>
      have hstep : (Λ : ℝ) * (a (p + j) : ℝ) ≤ (a (p + j + 1) : ℝ) := by
        have h := hgr (p + j)
        have h' : ((Λ * a (p + j) : NNReal) : ℝ) ≤ ((a (p + j + 1) : NNReal) : ℝ) := by
          exact_mod_cast h
        simpa using h'
      calc (Λ : ℝ) ^ (j + 1) * (a p : ℝ)
          = (Λ : ℝ) * ((Λ : ℝ) ^ j * (a p : ℝ)) := by ring
        _ ≤ (Λ : ℝ) * (a (p + j) : ℝ) := mul_le_mul_of_nonneg_left ih hΛpos.le
        _ ≤ (a (p + j + 1) : ℝ) := hstep
  -- the pointwise bound on the terms
  have hterm : ∀ n, P n → ((a n : ℝ))⁻¹ ≤ ((a m : ℝ))⁻¹ * ((Λ : ℝ)⁻¹) ^ (n - m) := by
    intro n hn
    have hmn : m ≤ n := hle_m n hn
    have hgrowth : (Λ : ℝ) ^ (n - m) * (a m : ℝ) ≤ (a n : ℝ) := by
      have h := hpow m (n - m)
      rwa [Nat.add_sub_of_le hmn] at h
    have hinv : (Λ : ℝ) ^ (n - m) * ((Λ : ℝ)⁻¹) ^ (n - m) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hΛpos), one_pow]
    have h2 : (a m : ℝ) ≤ (a n : ℝ) * ((Λ : ℝ)⁻¹) ^ (n - m) := by
      calc (a m : ℝ) = 1 * (a m : ℝ) := (one_mul _).symm
        _ = ((Λ : ℝ) ^ (n - m) * ((Λ : ℝ)⁻¹) ^ (n - m)) * (a m : ℝ) := by rw [hinv]
        _ = ((Λ : ℝ) ^ (n - m) * (a m : ℝ)) * ((Λ : ℝ)⁻¹) ^ (n - m) := by ring
        _ ≤ (a n : ℝ) * ((Λ : ℝ)⁻¹) ^ (n - m) :=
            mul_le_mul_of_nonneg_right hgrowth (by positivity)
    have han : (0 : ℝ) < (a n : ℝ) := haposR n
    have h4 : (a m : ℝ) * ((a n : ℝ))⁻¹ ≤ ((Λ : ℝ)⁻¹) ^ (n - m) := by
      have h := mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr han.le)
      have h5 : (a n : ℝ) * ((Λ : ℝ)⁻¹) ^ (n - m) * ((a n : ℝ))⁻¹
          = ((Λ : ℝ)⁻¹) ^ (n - m) := by
        rw [mul_assoc, mul_comm (((Λ : ℝ)⁻¹) ^ (n - m)) ((a n : ℝ))⁻¹, ← mul_assoc,
          mul_inv_cancel₀ (ne_of_gt han), one_mul]
      rwa [h5] at h
    have h6 : ((a m : ℝ))⁻¹ * ((a m : ℝ) * ((a n : ℝ))⁻¹)
        ≤ ((a m : ℝ))⁻¹ * ((Λ : ℝ)⁻¹) ^ (n - m) :=
      mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr (haposR m).le)
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (haposR m)), one_mul] at h6
  -- comparison with the geometric majorant
  have hbd : ∀ n : ℕ,
      (if P n then ((a n : ℝ))⁻¹ else 0)
        ≤ (if m ≤ n then ((a m : ℝ))⁻¹ * ((Λ : ℝ)⁻¹) ^ (n - m) else 0) := by
    intro n
    by_cases hn : P n
    · have hmn : m ≤ n := hle_m n hn
      rw [if_pos hn, if_pos hmn]
      exact hterm n hn
    · rw [if_neg hn]
      by_cases hmn : m ≤ n
      · rw [if_pos hmn]
        exact mul_nonneg (inv_nonneg.mpr (haposR m).le)
          (pow_nonneg (inv_nonneg.mpr hΛpos.le) _)
      · rw [if_neg hmn]
  have hgeomnorm : ‖((Λ : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛpos)]
    exact inv_lt_one_of_one_lt₀ hΛR
  have hgeom : Summable (fun k : ℕ => ((Λ : ℝ)⁻¹) ^ k) :=
    summable_geometric_of_norm_lt_one hgeomnorm
  have heq : ∀ k : ℕ, (if m ≤ k + m then ((a m : ℝ))⁻¹ * ((Λ : ℝ)⁻¹) ^ (k + m - m) else 0)
      = ((a m : ℝ))⁻¹ * ((Λ : ℝ)⁻¹) ^ k := by
    intro k
    rw [if_pos (Nat.le_add_left m k), Nat.add_sub_cancel]
  have hsumd : Summable (fun n : ℕ =>
      if m ≤ n then ((a m : ℝ))⁻¹ * ((Λ : ℝ)⁻¹) ^ (n - m) else 0) := by
    refine (summable_nat_add_iff m).mp ?_
    exact Summable.congr (hgeom.mul_left ((a m : ℝ))⁻¹) (fun k => (heq k).symm)
  have hnonnegb : ∀ n : ℕ, (0 : ℝ) ≤ (if P n then ((a n : ℝ))⁻¹ else 0) := by
    intro n
    by_cases hn : P n
    · rw [if_pos hn]
      exact inv_nonneg.mpr (haposR n).le
    · rw [if_neg hn]
  have hsumb : Summable (fun n : ℕ => if P n then ((a n : ℝ))⁻¹ else 0) :=
    Summable.of_nonneg_of_le hnonnegb hbd hsumd
  have hmain : (∑' n : ℕ, (if P n then ((a n : ℝ))⁻¹ else 0))
      ≤ ∑' n : ℕ, (if m ≤ n then ((a m : ℝ))⁻¹ * ((Λ : ℝ)⁻¹) ^ (n - m) else 0) :=
    hsumb.tsum_le_tsum hbd hsumd
  -- the geometric majorant has the value `(a m)⁻¹ * (1 - Λ⁻¹)⁻¹`
  have hzero : (∑ i ∈ Finset.range m,
      (if m ≤ i then ((a m : ℝ))⁻¹ * ((Λ : ℝ)⁻¹) ^ (i - m) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_neg (not_le.mpr hi)]
  have hval : (∑' n : ℕ, (if m ≤ n then ((a m : ℝ))⁻¹ * ((Λ : ℝ)⁻¹) ^ (n - m) else 0))
      = ((a m : ℝ))⁻¹ * (1 - (Λ : ℝ)⁻¹)⁻¹ := by
    have hsplit := hsumd.sum_add_tsum_nat_add m
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
    rw [tsum_congr heq, tsum_mul_left, tsum_geometric_of_norm_lt_one hgeomnorm]
  have hfinal : (1 - (Λ : ℝ)⁻¹)⁻¹ = (Λ : ℝ) / ((Λ : ℝ) - 1) := by
    have h1 : (1 : ℝ) - (Λ : ℝ)⁻¹ = ((Λ : ℝ) - 1) / (Λ : ℝ) := by
      rw [sub_div, div_self (ne_of_gt hΛpos), one_div]
    rw [h1, inv_div]
  calc (∑' n : ℕ, (if P n then ((a n : ℝ))⁻¹ else 0))
      ≤ ∑' n : ℕ, (if m ≤ n then ((a m : ℝ))⁻¹ * ((Λ : ℝ)⁻¹) ^ (n - m) else 0) := hmain
    _ = ((a m : ℝ))⁻¹ * (1 - (Λ : ℝ)⁻¹)⁻¹ := hval
    _ = (Λ : ℝ) / ((Λ : ℝ) - 1) * ((a m : ℝ))⁻¹ := by rw [hfinal]; ring

end Work.KMTPlan.A6
