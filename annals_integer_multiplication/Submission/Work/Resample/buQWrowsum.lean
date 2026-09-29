import Mathlib
import Submission.Work.Resample.buQWdefs

/-!
# The row-sum estimate for the tabulated `B̃` weight table

`Work.Resample.buQWrowsum`: given the pointwise accuracy of the tabulated weights
`|buWt p α s t ℓ h / 2^p - egW s t α ℓ h| ≤ 4·2^{-p}` (`Work.Resample.buWtAcc`), the retained
window `h ∈ egHset (egM p α)` (that is `0 < |h| ≤ m`) carries total mass at most
`2^p/2 + 8m`, and every individual tabulated weight is bounded by `2^p + 4`.

The whole estimate is elementary.  The decay hypothesis `hdec` gives
`|egW s t α ℓ h| ≤ egWBnd α h ≤ 20^{-|h|}` (`buQWR_egWBnd_le_pow`, with `α ≥ 2`), so the total
mass of the true weights is at most the geometric sum `Σ_{h ∈ egHset m} 20^{-|h|} ≤ 2/19 ≤ 1/2`
(`egHset_geom_le`, by induction on `m` along the recursive decomposition of the window into the
previous window plus the pair `±(m+1)`).  The accuracy hypothesis transfers this estimate to the
tabulated weights with an additive loss of `4` per term
(`|buWt| ≤ 2^p|egW| + 4`) over the `2m` terms of the window.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

/-! ## The numerical bound on the Gaussian weight bound -/

/-- `e^{-π} ≤ 1/20`. -/
lemma buQWR_exp_neg_pi_le : Real.exp (-Real.pi) ≤ 1 / 20 := by
  have h : (20 : ℝ) ≤ Real.exp 3 := by
    have hh := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 9
    norm_num at hh
    linarith [hh]
  calc Real.exp (-Real.pi) ≤ Real.exp (-3 : ℝ) :=
        Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
    _ = 1 / Real.exp 3 := by rw [Real.exp_neg]; ring
    _ ≤ 1 / 20 := one_div_le_one_div_of_le (by norm_num) h

/-- For `h ≠ 0` the Gaussian weight bound `egWBnd α h` is at most `20^{-|h|}` (with `α ≥ 2`):
for `|h| = 1` this is `e^{-2π} = (e^{-π})^2 ≤ 20^{-1}`, and for `|h| ≥ 2` the exponent
`π α² |h| (|h|-1) ≥ 4π|h| ≥ π|h|` dominates. -/
lemma buQWR_egWBnd_le_pow (α : ℕ) (hα : 2 ≤ α) (h : ℤ) (hh : h ≠ 0) :
    egWBnd α h ≤ (1 / 20 : ℝ) ^ h.natAbs := by
  have hq : Real.exp (-Real.pi) ≤ 1 / 20 := buQWR_exp_neg_pi_le
  have hq0 : 0 ≤ Real.exp (-Real.pi) := Real.exp_nonneg _
  rw [egWBnd]
  by_cases h1 : h.natAbs = 1
  · rw [if_pos h1]
    have heq : Real.exp (-2 * Real.pi) = (Real.exp (-Real.pi)) ^ 2 := by
      rw [show -2 * Real.pi = ((2 : ℕ) : ℝ) * (-Real.pi) by push_cast; ring, Real.exp_nat_mul]
    calc Real.exp (-2 * Real.pi) = (Real.exp (-Real.pi)) ^ 2 := heq
      _ ≤ (1 / 20 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hq0 hq 2
      _ ≤ (1 / 20 : ℝ) ^ (1 : ℕ) := by norm_num
      _ = (1 / 20 : ℝ) ^ h.natAbs := by rw [h1]
  · rw [if_neg h1]
    have hk2 : 2 ≤ h.natAbs := by omega
    have hkR : (2 : ℝ) ≤ (h.natAbs : ℝ) := by exact_mod_cast hk2
    have hα2 : (1 : ℝ) ≤ (α : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα
      nlinarith
    have hkk : (h.natAbs : ℝ) ≤ (h.natAbs : ℝ) * ((h.natAbs : ℝ) - 1) := by nlinarith
    have hmul := mul_le_mul hα2 hkk (by positivity : (0 : ℝ) ≤ (h.natAbs : ℝ))
      (by positivity : (0 : ℝ) ≤ (α : ℝ) ^ 2)
    have hkey : (h.natAbs : ℝ) ≤ (α : ℝ) ^ 2 * ((h.natAbs : ℝ) * ((h.natAbs : ℝ) - 1)) := by
      simpa using hmul
    have harg : Real.pi * (h.natAbs : ℝ) ≤
        Real.pi * (α : ℝ) ^ 2 * ((h.natAbs : ℝ) * ((h.natAbs : ℝ) - 1)) := by
      have := mul_le_mul_of_nonneg_left hkey (le_of_lt Real.pi_pos)
      linarith
    have hexp : Real.exp (-(Real.pi * (α : ℝ) ^ 2 * ((h.natAbs : ℝ) * ((h.natAbs : ℝ) - 1))))
        ≤ Real.exp (-(Real.pi * (h.natAbs : ℝ))) := Real.exp_le_exp.mpr (by linarith)
    have hpow : Real.exp (-(Real.pi * (h.natAbs : ℝ))) = (Real.exp (-Real.pi)) ^ h.natAbs := by
      rw [show -(Real.pi * (h.natAbs : ℝ)) = ((h.natAbs : ℕ) : ℝ) * (-Real.pi) by
            push_cast; ring, Real.exp_nat_mul]
    calc Real.exp (-(Real.pi * (α : ℝ) ^ 2 * ((h.natAbs : ℝ) * ((h.natAbs : ℝ) - 1))))
        ≤ Real.exp (-(Real.pi * (h.natAbs : ℝ))) := hexp
      _ = (Real.exp (-Real.pi)) ^ h.natAbs := hpow
      _ ≤ (1 / 20 : ℝ) ^ h.natAbs := pow_le_pow_left₀ hq0 hq h.natAbs

/-- The retained window `egHset m = {h | 0 < |h| ≤ m}` has `2m` elements. -/
lemma buQWR_egHset_card (m : ℕ) : (egHset m).card = 2 * m := by
  have hmem : (0 : ℤ) ∈ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
    simp only [Finset.mem_Icc]
    constructor <;> omega
  rw [egHset, Finset.card_erase_of_mem hmem, Int.card_Icc]
  have hcast : ((m : ℤ) + 1 - (-(m : ℤ))).toNat = 2 * m + 1 := by
    have h : (m : ℤ) + 1 - (-(m : ℤ)) = ((2 * m + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]
  rw [hcast]
  omega

/-! ## The geometric sum over the retained window -/

/-- The window `egHset m` is the previous window together with the outermost pair `±(m+1)`. -/
private lemma egHset_succ (m : ℕ) :
    egHset (m + 1) =
      insert (((m + 1 : ℕ)) : ℤ) (insert (-(((m + 1 : ℕ)) : ℤ)) (egHset m)) := by
  ext h
  simp only [egHset, Finset.mem_insert, Finset.mem_erase, Finset.mem_Icc]
  omega

/-- Exact evaluation of the geometric sum over the window: `Σ_{h ∈ egHset m} q^{|h|}` is twice the
sum of `q^{k+1}` for `k < m`. -/
private lemma egHset_sum_eq (m : ℕ) (q : ℝ) :
    ∑ h ∈ egHset m, q ^ h.natAbs = 2 * ∑ k ∈ Finset.range m, q ^ (k + 1) := by
  induction m with
  | zero =>
      have h0 : egHset 0 = ∅ := by
        rw [egHset]
        simp only [Nat.cast_zero, neg_zero, Finset.Icc_self]
        exact (Finset.erase_eq_empty_iff ({0} : Finset ℤ) 0).mpr (Or.inr rfl)
      simp [h0]
  | succ m ih =>
      show ∑ h ∈ egHset (m + 1), q ^ h.natAbs = 2 * ∑ k ∈ Finset.range (m + 1), q ^ (k + 1)
      have hb : (-(((m + 1 : ℕ)) : ℤ)) ∉ egHset m := by
        simp only [egHset, Finset.mem_erase, Finset.mem_Icc]
        omega
      have ha : (((m + 1 : ℕ)) : ℤ) ∉ insert (-(((m + 1 : ℕ)) : ℤ)) (egHset m) := by
        simp only [Finset.mem_insert, egHset, Finset.mem_erase, Finset.mem_Icc]
        omega
      rw [egHset_succ m, Finset.sum_insert ha, Finset.sum_insert hb, ih,
        Finset.sum_range_succ, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_natCast]
      ring

/-- The truncated geometric sum: `(1 - q) Σ_{k<m} q^k ≤ 1 - q^m` for `q ≥ 0` (trivial for `m = 0`,
and `(1-q)(Σ + q^m) = (1-q)Σ + q^m - q^{m+1} ≤ 1 - q^m + q^m - q^{m+1}` in the step). -/
private lemma geom_range_le (m : ℕ) (q : ℝ) :
    (1 - q) * (∑ k ∈ Finset.range m, q ^ k) ≤ 1 - q ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hq : (1 - q) * q ^ m = q ^ m - q ^ (m + 1) := by
        rw [sub_mul, one_mul, ← pow_succ']
      rw [Finset.sum_range_succ, mul_add, hq]
      linarith

/-- `Σ_{h ∈ egHset m} q^{|h|} ≤ 2q/(1-q)` for `0 ≤ q ≤ 1/2`: each absolute value `k ∈ [1,m]` is
attained twice, so the sum is twice the truncated geometric sum of ratio `q`. -/
private lemma egHset_geom_le (m : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) :
    ∑ h ∈ egHset m, q ^ h.natAbs ≤ 2 * q / (1 - q) := by
  have hpos : 0 < 1 - q := by linarith
  have hshift : ∑ k ∈ Finset.range m, q ^ (k + 1) = q * (∑ k ∈ Finset.range m, q ^ k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ'])
  have hbound : ∑ k ∈ Finset.range m, q ^ k ≤ 1 / (1 - q) := by
    have h1 := geom_range_le m q
    rw [le_div_iff₀ hpos]
    linarith [h1, pow_nonneg hq0 m]
  calc ∑ h ∈ egHset m, q ^ h.natAbs
      = 2 * (q * (∑ k ∈ Finset.range m, q ^ k)) := by rw [egHset_sum_eq m q, hshift]
    _ ≤ 2 * (q * (1 / (1 - q))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound hq0) (by norm_num)
    _ = 2 * q / (1 - q) := by ring

/-! ## The row sum -/

theorem buQWrowsum (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (ℓ : ℤ)
    (hacc : ∀ h : ℤ, h ≠ 0 →
      |((Work.Resample.buWt p α s t ℓ h : ℝ) / (2:ℝ)^p - Work.Resample.egW s t α ℓ h)| ≤ 4 / (2:ℝ)^p)
    (hdec : ∀ h : ℤ, h ≠ 0 → |Work.Resample.egW s t α ℓ h| ≤ Work.Resample.egWBnd α h) :
    (∑ h ∈ Work.Resample.egHset (Work.Resample.egM p α), |(Work.Resample.buWt p α s t ℓ h : ℝ)|) ≤
      (2:ℝ)^p / 2 + 8 * (Work.Resample.egM p α : ℝ) ∧
    (∀ h : ℤ, h ≠ 0 → |(Work.Resample.buWt p α s t ℓ h : ℝ)| ≤ (2:ℝ)^p + 4) := by
  have h2p : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hq0 : (0 : ℝ) ≤ 1 / 20 := by norm_num
  have hq1 : (1 / 20 : ℝ) ≤ 1 / 2 := by norm_num
  -- pointwise decay of the true Gaussian weights, in geometric form
  have hWdec : ∀ h : ℤ, h ≠ 0 → |egW s t α ℓ h| ≤ (1 / 20 : ℝ) ^ h.natAbs :=
    fun h hh => le_trans (hdec h hh) (buQWR_egWBnd_le_pow α hα h hh)
  -- the total mass of the true weights over the window is at most `1/2`
  have hWsum : ∑ h ∈ egHset (egM p α), |egW s t α ℓ h| ≤ 1 / 2 := by
    have h1 : ∑ h ∈ egHset (egM p α), |egW s t α ℓ h| ≤
        ∑ h ∈ egHset (egM p α), (1 / 20 : ℝ) ^ h.natAbs :=
      Finset.sum_le_sum (fun h hh => hWdec h (Finset.mem_erase.mp hh).1)
    have h2 : ∑ h ∈ egHset (egM p α), (1 / 20 : ℝ) ^ h.natAbs ≤
        2 * (1 / 20 : ℝ) / (1 - 1 / 20) := egHset_geom_le (egM p α) (1 / 20) hq0 hq1
    have h3 : 2 * (1 / 20 : ℝ) / (1 - 1 / 20) ≤ 1 / 2 := by norm_num
    linarith
  -- pointwise comparison of the tabulated weight with `2^p` times the true weight
  have hcmp : ∀ h : ℤ, h ≠ 0 →
      |(buWt p α s t ℓ h : ℝ)| ≤ (2 : ℝ) ^ p * |egW s t α ℓ h| + 4 := by
    intro h hh
    have h1 := hacc h hh
    have h2 : |(buWt p α s t ℓ h : ℝ)| / (2 : ℝ) ^ p ≤
        |egW s t α ℓ h| + 4 / (2 : ℝ) ^ p := by
      have htri : |(buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p| ≤
          |(buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p - egW s t α ℓ h| + |egW s t α ℓ h| := by
        have := abs_add_le ((buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p - egW s t α ℓ h)
          (egW s t α ℓ h)
        rwa [show ((buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p - egW s t α ℓ h) + egW s t α ℓ h
              = (buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p by ring] at this
      have h3 : |(buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p| ≤
          4 / (2 : ℝ) ^ p + |egW s t α ℓ h| := by linarith
      calc |(buWt p α s t ℓ h : ℝ)| / (2 : ℝ) ^ p
          = |(buWt p α s t ℓ h : ℝ) / (2 : ℝ) ^ p| := by
            rw [abs_div, abs_of_pos h2p]
        _ ≤ 4 / (2 : ℝ) ^ p + |egW s t α ℓ h| := h3
        _ = |egW s t α ℓ h| + 4 / (2 : ℝ) ^ p := by ring
    have h4 : |(buWt p α s t ℓ h : ℝ)| ≤
        (|egW s t α ℓ h| + 4 / (2 : ℝ) ^ p) * (2 : ℝ) ^ p := (div_le_iff₀ h2p).mp h2
    calc |(buWt p α s t ℓ h : ℝ)|
        ≤ (|egW s t α ℓ h| + 4 / (2 : ℝ) ^ p) * (2 : ℝ) ^ p := h4
      _ = (2 : ℝ) ^ p * |egW s t α ℓ h| + 4 := by
          rw [add_mul, div_mul_cancel₀ _ (ne_of_gt h2p)]
          ring
  constructor
  · calc ∑ h ∈ egHset (egM p α), |(buWt p α s t ℓ h : ℝ)|
        ≤ ∑ h ∈ egHset (egM p α), ((2 : ℝ) ^ p * |egW s t α ℓ h| + 4) :=
          Finset.sum_le_sum (fun h hh => hcmp h (Finset.mem_erase.mp hh).1)
      _ = (2 : ℝ) ^ p * (∑ h ∈ egHset (egM p α), |egW s t α ℓ h|) +
            4 * ((egHset (egM p α)).card : ℝ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
      _ = (2 : ℝ) ^ p * (∑ h ∈ egHset (egM p α), |egW s t α ℓ h|) +
            4 * (2 * (egM p α : ℝ)) := by
          rw [buQWR_egHset_card]
          push_cast
          ring
      _ ≤ (2 : ℝ) ^ p / 2 + 8 * (egM p α : ℝ) := by
          have h5 : (2 : ℝ) ^ p * (∑ h ∈ egHset (egM p α), |egW s t α ℓ h|) ≤
              (2 : ℝ) ^ p * (1 / 2) := mul_le_mul_of_nonneg_left hWsum (le_of_lt h2p)
          linarith
  · intro h hh
    have h1 := hcmp h hh
    have h2 : |egW s t α ℓ h| ≤ (1 : ℝ) := by
      have h3 := hWdec h hh
      have h4 : (1 / 20 : ℝ) ^ h.natAbs ≤ (1 : ℝ) := pow_le_one₀ hq0 (by norm_num)
      linarith
    have h5 : (2 : ℝ) ^ p * |egW s t α ℓ h| ≤ (2 : ℝ) ^ p := by
      simpa using mul_le_mul_of_nonneg_left h2 (le_of_lt h2p)
    linarith

end Work.Resample
