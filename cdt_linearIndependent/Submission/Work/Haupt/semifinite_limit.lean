import Mathlib
import Submission.Work.Haupt.qp_defs

/-!
# The semi-finite limit

We show that the semi-finite sum `∑' n : ℤ, sfTerm q z m n` converges as `m → ∞`
to the "infinite" sum `∑' n : ℤ, qhalfInt q n * z ^ n`.

The proof uses the split `hsplit : ∑' n, sfTerm q z m n = Afun q z m + Bfun q z m`
from `semifinite_split`, computes the limit of the two pieces separately using
Tannery's theorem (`tendsto_tsum_of_dominated_convergence`), and identifies the sum of
the two limits with the `ℤ`-indexed series by the `ℕ`/`ℤ`-splitting lemma
`tsum_of_nat_of_neg_add_one`.
-/

set_option maxHeartbeats 1000000

open scoped BigOperators
open Filter Topology

namespace Work.Haupt

/-! ## Elementary norm and exponent facts -/

/-- `‖qhalf q n‖ = ‖q‖ ^ (n (n-1)/2)`. -/
lemma norm_qhalf (q : ℂ) (n : ℕ) : ‖qhalf q n‖ = ‖q‖ ^ (n * (n - 1) / 2) := by
  rw [qhalf, norm_prod]
  simp only [norm_pow]
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]

/-- `‖z ^ Int.negSucc k‖ = (‖z‖⁻¹) ^ (k+1)`. -/
lemma norm_zpow_negSucc (z : ℂ) (k : ℕ) : ‖z ^ (Int.negSucc k)‖ = (‖z‖⁻¹) ^ (k + 1) := by
  rw [norm_zpow, Int.negSucc_eq k, zpow_neg]
  have h : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, zpow_natCast, inv_pow]

/-- `q ^ ((m : ℤ) + 1) = q ^ (m + 1)`. -/
lemma zpow_int_add_one (q : ℂ) (m : ℕ) : q ^ ((m : ℤ) + 1) = q ^ (m + 1) := by
  have h : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, zpow_natCast]

lemma halfExp_succ (k : ℕ) : (k + 2) * (k + 2 - 1) / 2 = (k + 1) * (k + 2) / 2 := by
  rw [show k + 2 - 1 = k + 1 from by omega]
  exact congrArg (· / 2) (Nat.mul_comm (k + 2) (k + 1))

/-- **Super-geometric summability.**  For `0 ≤ r < 1` and `c ≥ 0`, the series
`∑_k r ^ (P k) * c ^ k` converges, provided `P k ≥ k (k-1)/2` (i.e. the exponent grows at
least quadratically). -/
theorem quad_summable (r c : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hc : 0 ≤ c) (P : ℕ → ℕ)
    (hP : ∀ k, k * (k - 1) / 2 ≤ P k) : Summable (fun k : ℕ => r ^ (P k) * c ^ k) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg hr0 (P k)) (pow_nonneg hc k))
    (fun k => mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hr0 hr1.le (hP k))
      (pow_nonneg hc k)) ?_
  have hgeom : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat hgeom ?_
  have hρ0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hρ1 : Real.sqrt r < 1 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hr1)
  have htend : Tendsto (fun k : ℕ => c * Real.sqrt r ^ (k - 1)) atTop (nhds 0) := by
    have hcomp := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
      (tendsto_sub_atTop_nat 1)
    have hc' : Tendsto (fun _ : ℕ => c) atTop (nhds c) := tendsto_const_nhds
    simpa using hc'.mul hcomp
  have hev : ∀ᶠ k : ℕ in atTop, c * Real.sqrt r ^ (k - 1) < 1 / 2 :=
    htend (IsOpen.mem_nhds isOpen_Iio (by norm_num : (0 : ℝ) ∈ Set.Iio (1 / 2)))
  rw [eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  rw [eventually_atTop]
  refine ⟨max K 2, fun k hk => ?_⟩
  have hkK : K ≤ k := le_trans (le_max_left K 2) hk
  have hK' : c * Real.sqrt r ^ (k - 1) < 1 / 2 := hK k hkK
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hr0 _) (pow_nonneg hc k))]
  have h2m : 2 * (k * (k - 1) / 2) = k * (k - 1) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))
  have hrp : r ^ (k * (k - 1) / 2) = Real.sqrt r ^ (k * (k - 1)) := by
    calc r ^ (k * (k - 1) / 2) = (Real.sqrt r ^ 2) ^ (k * (k - 1) / 2) := by
          rw [Real.sq_sqrt hr0]
      _ = Real.sqrt r ^ (2 * (k * (k - 1) / 2)) := by rw [← pow_mul]
      _ = Real.sqrt r ^ (k * (k - 1)) := by rw [h2m]
  rw [hrp]
  calc Real.sqrt r ^ (k * (k - 1)) * c ^ k
      = (c * Real.sqrt r ^ (k - 1)) ^ k := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm (k - 1) k]; ring
    _ ≤ ((1 : ℝ) / 2) ^ k :=
        pow_le_pow_left₀ (mul_nonneg hc (pow_nonneg hρ0 _)) (le_of_lt hK') k

/-! ## Pointwise limits of `qpNat` -/

/-- `qpNat (q ^ (m+1)) q n → 1` as `m → ∞`. -/
theorem tendsto_qpNat_succ (q : ℂ) (hq : ‖q‖ < 1) (n : ℕ) :
    Tendsto (fun m : ℕ => qpNat (q ^ (m + 1)) q n) atTop (nhds 1) := by
  have h0 : Tendsto (fun m : ℕ => q ^ (m + 1)) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using h
  have hprod : Tendsto (fun m : ℕ => ∏ j ∈ Finset.range n, (1 - q ^ (m + 1) * q ^ j))
      atTop (nhds (∏ j ∈ Finset.range n, (1 - (0 : ℂ) * q ^ j))) := by
    refine tendsto_finsetProd (s := Finset.range n)
      (f := fun j m => 1 - q ^ (m + 1) * q ^ j) (a := fun j => 1 - (0 : ℂ) * q ^ j)
      (fun j hj => ?_)
    have h1 : Tendsto (fun m : ℕ => q ^ (m + 1) * q ^ j) atTop (nhds 0) := by
      have hc : Tendsto (fun _ : ℕ => q ^ j) atTop (nhds (q ^ j)) := tendsto_const_nhds
      simpa using h0.mul hc
    have hc1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using hc1.sub h1
  have h1 : (∏ j ∈ Finset.range n, (1 - (0 : ℂ) * q ^ j)) = 1 := by simp
  rw [h1] at hprod
  simpa [qpNat] using hprod

/-- `qpNat (q ^ (m - k)) q n → 1` as `m → ∞`. -/
theorem tendsto_qpNat_sub (q : ℂ) (hq : ‖q‖ < 1) (k n : ℕ) :
    Tendsto (fun m : ℕ => qpNat (q ^ (m - k)) q n) atTop (nhds 1) := by
  have h0 : Tendsto (fun m : ℕ => q ^ (m - k)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).comp (tendsto_sub_atTop_nat k)
  have hprod : Tendsto (fun m : ℕ => ∏ j ∈ Finset.range n, (1 - q ^ (m - k) * q ^ j))
      atTop (nhds (∏ j ∈ Finset.range n, (1 - (0 : ℂ) * q ^ j))) := by
    refine tendsto_finsetProd (s := Finset.range n)
      (f := fun j m => 1 - q ^ (m - k) * q ^ j) (a := fun j => 1 - (0 : ℂ) * q ^ j)
      (fun j hj => ?_)
    have h1 : Tendsto (fun m : ℕ => q ^ (m - k) * q ^ j) atTop (nhds 0) := by
      have hc : Tendsto (fun _ : ℕ => q ^ j) atTop (nhds (q ^ j)) := tendsto_const_nhds
      simpa using h0.mul hc
    have hc1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1) := tendsto_const_nhds
    simpa using hc1.sub h1
  have h1 : (∏ j ∈ Finset.range n, (1 - (0 : ℂ) * q ^ j)) = 1 := by simp
  rw [h1] at hprod
  simpa [qpNat] using hprod

/-! ## Norm bounds for `qpNat` -/

/-- `(1 - ‖q‖)^n ≤ ‖qpNat (q ^ (m+1)) q n‖`. -/
theorem qpNat_norm_ge (q : ℂ) (hq : ‖q‖ < 1) (m n : ℕ) :
    (1 - ‖q‖) ^ n ≤ ‖qpNat (q ^ (m + 1)) q n‖ := by
  rw [qpNat, norm_prod]
  have hnn : 0 ≤ 1 - ‖q‖ := by linarith [norm_nonneg q, hq]
  calc (1 - ‖q‖) ^ n = ∏ j ∈ Finset.range n, (1 - ‖q‖) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ j ∈ Finset.range n, ‖1 - q ^ (m + 1) * q ^ j‖ := by
        refine Finset.prod_le_prod₀ (fun j hj => hnn) (fun j hj => ?_)
        have hj' : q ^ (m + 1) * q ^ j = q ^ (m + 1 + j) := by rw [← pow_add]
        rw [hj']
        have h1 : ‖q‖ ^ (m + 1 + j) ≤ ‖q‖ := by
          simpa using pow_le_pow_of_le_one (norm_nonneg q) hq.le (by omega : 1 ≤ m + 1 + j)
        have h2 : (1 : ℝ) ≤ ‖(1 : ℂ) - q ^ (m + 1 + j)‖ + ‖q‖ ^ (m + 1 + j) := by
          have h := norm_add_le ((1 : ℂ) - q ^ (m + 1 + j)) (q ^ (m + 1 + j))
          rw [sub_add_cancel, norm_one, norm_pow] at h
          exact h
        linarith

/-- `‖qpNat (q ^ (m - k)) q (k+1)‖ ≤ 2 ^ (k+1)` when `k < m`. -/
theorem qpNat_norm_le (q : ℂ) (hq : ‖q‖ < 1) (m k : ℕ) (h : k < m) :
    ‖qpNat (q ^ (m - k)) q (k + 1)‖ ≤ 2 ^ (k + 1) := by
  rw [qpNat, norm_prod]
  calc ∏ j ∈ Finset.range (k + 1), ‖1 - q ^ (m - k) * q ^ j‖
      ≤ ∏ j ∈ Finset.range (k + 1), 2 := by
        refine Finset.prod_le_prod₀ (fun j hj => norm_nonneg _) (fun j hj => ?_)
        have hj' : q ^ (m - k) * q ^ j = q ^ (m - k + j) := by rw [← pow_add]
        rw [hj']
        calc ‖1 - q ^ (m - k + j)‖ ≤ ‖(1 : ℂ)‖ + ‖q ^ (m - k + j)‖ := norm_sub_le _ _
          _ = 1 + ‖q‖ ^ (m - k + j) := by rw [norm_one, norm_pow]
          _ ≤ 2 := by
              have h1 : ‖q‖ ^ (m - k + j) ≤ 1 := pow_le_one₀ (norm_nonneg q) hq.le
              linarith
    _ = 2 ^ (k + 1) := by rw [Finset.prod_const, Finset.card_range]

/-! ## Reindexing `Bfun` -/

/-- `Bfun` as a sum over `Finset.range m`. -/
theorem Bfun_eq_sum_range (q z : ℂ) (m : ℕ) :
    Bfun q z m = ∑ k ∈ Finset.range m,
      qpNat (q ^ (m - k)) q (k + 1) * qhalf q (k + 2) * z ^ (Int.negSucc k) := by
  rw [Bfun]
  have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k < m := Finset.mem_range.mp hk
  have hkm : k ≤ m := le_of_lt hk'
  rw [show (1 : ℕ) + k = k + 1 from Nat.add_comm 1 k]
  have hexp : (m : ℤ) + 1 - ((k + 1 : ℕ) : ℤ) = ((m - k : ℕ) : ℤ) := by
    rw [Nat.cast_sub hkm]; push_cast; ring
  have hnk : k + 1 + 1 = k + 2 := by omega
  have hneg : -((k + 1 : ℕ) : ℤ) = Int.negSucc k := by
    rw [Int.negSucc_eq]; push_cast; ring
  simp only [hexp, hnk, hneg, zpow_natCast]

/-! ## Splitting a `ℤ`-indexed sum into its two halves -/

/-- `∑'_{n:ℤ} f n = ∑'_{n:ℕ} f n + ∑'_{n:ℕ} f (-n-1)` for `f n = qhalfInt q n * z ^ n`. -/
theorem tsum_int_half (q z : ℂ)
    (h1 : Summable (fun n : ℕ => qhalf q n * z ^ n))
    (h2 : Summable (fun k : ℕ => qhalf q (k + 2) * z ^ Int.negSucc k)) :
    (∑' n : ℤ, qhalfInt q n * z ^ n)
      = (∑' n : ℕ, qhalf q n * z ^ n)
        + (∑' k : ℕ, qhalf q (k + 2) * z ^ Int.negSucc k) := by
  have h1' : Summable (fun n : ℕ => (fun m : ℤ => qhalfInt q m * z ^ m) ((n : ℕ) : ℤ)) := by
    simpa [qhalfInt_natCast, zpow_natCast] using h1
  have h2' : Summable (fun n : ℕ => (fun m : ℤ => qhalfInt q m * z ^ m) (-((n : ℤ) + 1))) := by
    have he : (fun n : ℕ => (fun m : ℤ => qhalfInt q m * z ^ m) (-((n : ℤ) + 1)))
        = fun n : ℕ => qhalf q (n + 2) * z ^ Int.negSucc n := by
      funext n
      simp only [(Int.negSucc_eq n).symm, qhalfInt_negSucc]
    rw [he]; exact h2
  exact tsum_of_nat_of_neg_add_one (f := fun m : ℤ => qhalfInt q m * z ^ m) h1' h2'

/-! ## The two limits -/

/-- Summability of the dominating function for `Bfun`. -/
lemma summable_bfun {q z : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun k : ℕ => ‖q‖ ^ ((k + 1) * (k + 2) / 2) * (2 * ‖z‖⁻¹) ^ (k + 1)) := by
  refine Summable.congr ((quad_summable ‖q‖ (2 * ‖z‖⁻¹) (norm_nonneg q) hq (by positivity)
    (fun k => (k + 1) * (k + 2) / 2) (fun k =>
      Nat.div_le_div_right (le_trans (Nat.mul_le_mul_left k (Nat.sub_le k 1))
        (Nat.mul_le_mul (Nat.le_succ k) (by omega))))).mul_left (2 * ‖z‖⁻¹)) (fun k => ?_)
  rw [pow_succ]; ring

/-- `Afun q z m → ∑' n, qhalf q n * z ^ n`. -/
lemma tendsto_Afun {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    Tendsto (fun m : ℕ => Afun q z m) atTop (nhds (∑' n : ℕ, qhalf q n * z ^ n)) := by
  have hpos : (0 : ℝ) < 1 - ‖q‖ := by linarith [norm_nonneg q, hq]
  have hbase : Summable (fun n : ℕ =>
      ‖q‖ ^ (n * (n - 1) / 2) * ((1 + ‖z‖) * (1 - ‖q‖)⁻¹) ^ n) :=
    quad_summable ‖q‖ ((1 + ‖z‖) * (1 - ‖q‖)⁻¹) (norm_nonneg q) hq
      (mul_nonneg (by positivity) (inv_nonneg.mpr hpos.le))
      (fun n => n * (n - 1) / 2) (fun n => le_rfl)
  have hmain : Tendsto (fun m : ℕ => ∑' n : ℕ,
        qhalf q n * z ^ n * (qpNat (q ^ (m + 1)) q n)⁻¹)
      atTop (nhds (∑' n : ℕ, qhalf q n * z ^ n)) := by
    refine tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun m n => qhalf q n * z ^ n * (qpNat (q ^ (m + 1)) q n)⁻¹)
      (g := fun n => qhalf q n * z ^ n)
      (bound := fun n => ‖q‖ ^ (n * (n - 1) / 2) * ((1 + ‖z‖) * (1 - ‖q‖)⁻¹) ^ n)
      hbase ?_ ?_
    · intro n
      have h1 : Tendsto (fun m : ℕ => qpNat (q ^ (m + 1)) q n) atTop (nhds 1) :=
        tendsto_qpNat_succ q hq n
      have hc : Tendsto (fun _ : ℕ => qhalf q n * z ^ n) atTop (nhds (qhalf q n * z ^ n)) :=
        tendsto_const_nhds
      have h2 := hc.mul (h1.inv₀ one_ne_zero)
      simpa using h2
    · refine Eventually.of_forall (fun m n => ?_)
      have hL : ‖qhalf q n * z ^ n * (qpNat (q ^ (m + 1)) q n)⁻¹‖
          = ‖q‖ ^ (n * (n - 1) / 2) * ‖z‖ ^ n * (‖qpNat (q ^ (m + 1)) q n‖)⁻¹ := by
        simp only [norm_mul, norm_inv, norm_qhalf, norm_pow]
      rw [hL]
      have hDpos : 0 < (1 - ‖q‖) ^ n := pow_pos hpos n
      have hQ : (1 - ‖q‖) ^ n ≤ ‖qpNat (q ^ (m + 1)) q n‖ := qpNat_norm_ge q hq m n
      have hQpos : 0 < ‖qpNat (q ^ (m + 1)) q n‖ := lt_of_lt_of_le hDpos hQ
      have hA0 : 0 ≤ ‖q‖ ^ (n * (n - 1) / 2) := by positivity
      have hZ0 : 0 ≤ ‖z‖ ^ n := by positivity
      calc ‖q‖ ^ (n * (n - 1) / 2) * ‖z‖ ^ n * (‖qpNat (q ^ (m + 1)) q n‖)⁻¹
          ≤ ‖q‖ ^ (n * (n - 1) / 2) * ‖z‖ ^ n * (((1 - ‖q‖) ^ n))⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hA0 hZ0)
            exact (inv_le_inv₀ hQpos hDpos).mpr hQ
        _ = ‖q‖ ^ (n * (n - 1) / 2) * (‖z‖ * (1 - ‖q‖)⁻¹) ^ n := by
            rw [← inv_pow, mul_assoc, ← mul_pow]
        _ ≤ ‖q‖ ^ (n * (n - 1) / 2) * ((1 + ‖z‖) * (1 - ‖q‖)⁻¹) ^ n := by
            refine mul_le_mul_of_nonneg_left ?_ hA0
            refine pow_le_pow_left₀ (by positivity) ?_ n
            exact mul_le_mul_of_nonneg_right (by linarith [norm_nonneg z]) (by positivity)
  refine Tendsto.congr' (Eventually.of_forall (fun m => ?_)) hmain
  unfold Afun
  refine tsum_congr (fun n => ?_)
  rw [div_eq_mul_inv, zpow_int_add_one]

/-- `Bfun q z m → ∑' k, qhalf q (k+2) * z ^ (Int.negSucc k)`. -/
lemma tendsto_Bfun {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    Tendsto (fun m : ℕ => Bfun q z m) atTop
      (nhds (∑' k : ℕ, qhalf q (k + 2) * z ^ (Int.negSucc k))) := by
  have hmain : Tendsto (fun m : ℕ => ∑' k : ℕ, (if k < m then
        qpNat (q ^ (m - k)) q (k + 1) * qhalf q (k + 2) * z ^ (Int.negSucc k) else 0)) atTop
      (nhds (∑' k : ℕ, qhalf q (k + 2) * z ^ (Int.negSucc k))) := by
    refine tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun m k => if k < m then
        qpNat (q ^ (m - k)) q (k + 1) * qhalf q (k + 2) * z ^ (Int.negSucc k) else 0)
      (g := fun k => qhalf q (k + 2) * z ^ (Int.negSucc k))
      (bound := fun k => ‖q‖ ^ ((k + 1) * (k + 2) / 2) * (2 * ‖z‖⁻¹) ^ (k + 1))
      (summable_bfun hq) ?_ ?_
    · intro k
      have hpt : Tendsto (fun m : ℕ => qpNat (q ^ (m - k)) q (k + 1) * qhalf q (k + 2)
            * z ^ (Int.negSucc k)) atTop (nhds (1 * qhalf q (k + 2) * z ^ (Int.negSucc k))) := by
        have hc : Tendsto (fun _ : ℕ => qhalf q (k + 2)) atTop (nhds (qhalf q (k + 2))) :=
          tendsto_const_nhds
        have hd : Tendsto (fun _ : ℕ => z ^ (Int.negSucc k)) atTop
            (nhds (z ^ (Int.negSucc k))) := tendsto_const_nhds
        exact ((tendsto_qpNat_sub q hq k (k + 1)).mul hc).mul hd
      have hev : (fun m : ℕ => qpNat (q ^ (m - k)) q (k + 1) * qhalf q (k + 2)
            * z ^ (Int.negSucc k))
          =ᶠ[atTop] (fun m : ℕ => (if k < m then qpNat (q ^ (m - k)) q (k + 1)
            * qhalf q (k + 2) * z ^ (Int.negSucc k) else 0)) := by
        filter_upwards [eventually_ge_atTop (k + 1)] with m hm
        exact (if_pos (by omega)).symm
      have := Tendsto.congr' hev hpt
      simpa using this
    · refine Eventually.of_forall (fun m k => ?_)
      by_cases h : k < m
      · rw [if_pos h, norm_mul, norm_mul, norm_qhalf, norm_zpow_negSucc, halfExp_succ]
        have h1 : ‖qpNat (q ^ (m - k)) q (k + 1)‖ ≤ 2 ^ (k + 1) := qpNat_norm_le q hq m k h
        have hA0 : 0 ≤ ‖q‖ ^ ((k + 1) * (k + 2) / 2) := by positivity
        calc ‖qpNat (q ^ (m - k)) q (k + 1)‖ * ‖q‖ ^ ((k + 1) * (k + 2) / 2)
              * (‖z‖⁻¹) ^ (k + 1)
            ≤ 2 ^ (k + 1) * ‖q‖ ^ ((k + 1) * (k + 2) / 2) * (‖z‖⁻¹) ^ (k + 1) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hA0) (by positivity)
          _ = ‖q‖ ^ ((k + 1) * (k + 2) / 2) * (2 * ‖z‖⁻¹) ^ (k + 1) := by
              rw [mul_pow]; ring
      · rw [if_neg h, norm_zero]
        positivity
  refine Tendsto.congr' (Eventually.of_forall (fun m => ?_)) hmain
  show (∑' k : ℕ, (if k < m then qpNat (q ^ (m - k)) q (k + 1) * qhalf q (k + 2)
      * z ^ (Int.negSucc k) else 0)) = Bfun q z m
  rw [Bfun_eq_sum_range, tsum_eq_sum (s := Finset.range m) (fun k hk => by
    rw [Finset.mem_range] at hk; exact if_neg hk)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [if_pos (Finset.mem_range.mp hk)]

/-! ## The main theorem -/

theorem semifinite_limit {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0)
    (hsplit : ∀ m : ℕ, (∑' n : ℤ, sfTerm q z m n) = Afun q z m + Bfun q z m) :
    Filter.Tendsto (fun m : ℕ => (∑' n : ℤ, sfTerm q z m n)) Filter.atTop
      (nhds (∑' n : ℤ, qhalfInt q n * z ^ n)) := by
  have h1 : Summable (fun n : ℕ => qhalf q n * z ^ n) := by
    refine Summable.of_norm_bounded
      (quad_summable ‖q‖ ‖z‖ (norm_nonneg q) hq (norm_nonneg z)
        (fun n => n * (n - 1) / 2) (fun n => le_rfl)) (fun n => ?_)
    rw [norm_mul, norm_qhalf, norm_pow]
  have h2 : Summable (fun k : ℕ => qhalf q (k + 2) * z ^ Int.negSucc k) := by
    refine Summable.of_norm_bounded (summable_bfun (q := q) (z := z) hq) (fun k => ?_)
    rw [norm_mul, norm_qhalf, norm_zpow_negSucc, halfExp_succ]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith [inv_nonneg.mpr (norm_nonneg z)]) _)
      (by positivity)
  have hAB := (tendsto_Afun hq hz).add (tendsto_Bfun hq hz)
  rw [tsum_int_half q z h1 h2]
  refine Tendsto.congr' (Eventually.of_forall (fun m => ?_)) hAB
  exact (hsplit m).symm

end Work.Haupt
