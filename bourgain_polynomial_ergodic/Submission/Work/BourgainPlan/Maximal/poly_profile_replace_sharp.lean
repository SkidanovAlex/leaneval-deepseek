import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_sub_one_le
import Submission.Work.BourgainPlan.Maximal.polyProfile_decay_sharp

namespace Work.BourgainPlan.Maximal

/-!
# `ℓ¹`-summability of the profile replacement error along the dyadic scales

This file assembles the two analytic inputs of the profile-replacement estimate

* `polyProfile_sub_one_le` — the mean-value (plateau) bound at the origin,
  `‖polyProfile P N β - 1‖ ≤ 4π (∑_i |c_i|) |β| N^d`;
* `polyProfile_decay_sharp` — the van der Corput decay off the origin,
  `‖polyProfile P (2^k) β‖ ≤ C (|β| 2^{kd})^{-1/d}` for `|β| 2^{kd} ≥ 1`,

into the statement that the error made in replacing the profile `polyProfile P (2^k) β` by the
sharp indicator `1_{|β| 2^{kd} ≤ 1}` is summable over the dyadic scales, with a constant that is
uniform in the non-zero frequency `β`.

The combinatorial heart is a splitting of the `tsum` at the first dyadic scale `j` for which
`y j := |β| · polyDil P j > 1`:

* below `j` the indicator is `1` and the error is controlled by the mean-value bound, the head
  geometric sum `∑_{i<j} y i ≤ 2^d/(2^d-1) ≤ 2` (because `y (j-1) ≤ 1` and `y j = 2^d y (j-1)`);
* from `j` on the indicator is `0` and the error is controlled by the van der Corput decay, the
  tail `∑_{i≥j} (|β|2^{id})^{-1/d} = |β|^{-1/d} ∑_{i≥j} 2^{-i} ≤ 2 · y j^{-1/d} ≤ 2`
  (because `y j > 1`).
-/

open Filter Finset
open scoped BigOperators

set_option autoImplicit false

open Commons.Analysis.ExponentialSums

/-! ## Elementary facts about the dyadic dilation `polyDil P k = (2^k)^d` -/

/-- `|polyDil P k · β| = |β| · polyDil P k` (the dilation is positive). -/
private lemma abs_polyDil_mul (P : Polynomial ℤ) (β : ℝ) (k : ℕ) :
    |polyDil P k * β| = |β| * polyDil P k := by
  rw [abs_mul, abs_of_pos (polyDil_pos P k), mul_comm]

/-- `(polyDil P k)^{-1/d} = 2^{-k}`. -/
private lemma polyDil_rpow_neg_inv (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (k : ℕ) :
    (polyDil P k) ^ (-(1 / (P.natDegree : ℝ))) = (1 / 2 : ℝ) ^ k := by
  have hpos : (0:ℝ) < polyDil P k := polyDil_pos P k
  rw [Real.rpow_neg hpos.le]
  rw [powDil_rpow P.natDegree hd k]
  rw [show (1:ℝ)/2 = ((2:ℝ))⁻¹ by norm_num, ← inv_pow]

/-- `((2^k : ℕ) : ℝ)^d = polyDil P k` — the bridge between the hypothesis on the scale `N = 2^k`
of the mean-value bound and the dilation `polyDil`. -/
private lemma natCast_two_pow_pow_eq_polyDil (P : Polynomial ℤ) (k : ℕ) :
    ((2 ^ k : ℕ) : ℝ) ^ P.natDegree = polyDil P k := by
  rw [polyDil]; exact (powDil_eq_nat P.natDegree k).symm

/-- One dyadic step of the dilation: `polyDil P j = 2^d · polyDil P (j-1)` for `j ≥ 1`. -/
private lemma polyDil_eq_pred_mul (P : Polynomial ℤ) {j : ℕ} (hj : 1 ≤ j) :
    polyDil P j = polyDil P (j-1) * (2:ℝ)^P.natDegree := by
  have h : (2:ℝ)^j = (2:ℝ)^(j-1) * 2 := by
    conv_lhs => rw [show j = (j-1)+1 by omega]
    rw [pow_succ]
  calc polyDil P j = ((2:ℝ)^j) ^ P.natDegree := rfl
    _ = (((2:ℝ)^(j-1)) * 2) ^ P.natDegree := by rw [h]
    _ = ((2:ℝ)^(j-1)) ^ P.natDegree * (2:ℝ)^P.natDegree := mul_pow _ _ _
    _ = polyDil P (j-1) * (2:ℝ)^P.natDegree := rfl

/-! ## The assembly -/

/-- **Capstone.**  The mean-value bound at the plateau and the van der Corput decay off it imply
that the dyadic profile-replacement error is uniformly summable in the non-zero frequency.

`hhead M` is the plateau bound `‖polyProfile P N β - 1‖ ≤ M |β| N^d` for `N ≥ 1` and `hdec C1` is
the decay `‖polyProfile P (2^k) β‖ ≤ C1 (|β| polyDil P k)^{-1/d}` in the regime
`|β| polyDil P k ≥ 1`. -/
theorem poly_profile_replace_sharp_of_bounds (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (M : ℝ) (hM : 0 ≤ M)
    (hhead : ∀ N : ℕ, 1 ≤ N → ∀ β : ℝ,
      ‖polyProfile P N β - 1‖ ≤ M * (|β| * (N : ℝ) ^ P.natDegree))
    (C1 : ℝ) (hC1 : 0 < C1)
    (hdec : ∀ β : ℝ, β ≠ 0 → ∀ k : ℕ, 1 ≤ |β| * polyDil P k →
      ‖polyProfile P (2 ^ k) β‖ ≤ C1 * (|β| * polyDil P k) ^ (-(1 / (P.natDegree : ℝ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ≠ 0 → (∑' k : ℕ, polyErrVal P β k) ≤ C := by
  have hd1 : 1 ≤ P.natDegree := by omega
  refine ⟨2 * M + 2 * C1 + 1, by positivity, ?_⟩
  intro β hβ
  have hβpos : 0 < |β| := abs_pos.mpr hβ
  set y : ℕ → ℝ := fun k => |β| * polyDil P k with hydef
  have hyk : ∀ k, y k = |β| * polyDil P k := fun k => rfl
  have hypos : ∀ k, 0 < y k := fun k => by rw [hyk k]; exact mul_pos hβpos (polyDil_pos P k)
  have hymono : ∀ i j, i ≤ j → y i ≤ y j := fun i j hij => by
    rw [hyk i, hyk j]
    exact mul_le_mul_of_nonneg_left (powDil_mono P.natDegree hij) hβpos.le
  -- the first dyadic scale at which the sharp window closes
  have hex : ∃ k : ℕ, 1 < y k := by
    have htop : Tendsto (fun k : ℕ => (4:ℝ)^k * |β|) atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 4)).atTop_mul_const hβpos
    obtain ⟨k, hk⟩ := (htop.eventually (eventually_gt_atTop (1:ℝ))).exists
    refine ⟨k, lt_of_lt_of_le hk ?_⟩
    rw [hyk k]
    have h4 : (4:ℝ)^k ≤ polyDil P k := by
      rw [polyDil, powDil]
      calc (4:ℝ)^k = ((2:ℝ)^k)^2 := by
            rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul]; ring
        _ ≤ ((2:ℝ)^k)^P.natDegree :=
            pow_le_pow_right₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hd
    exact le_trans (le_of_eq (mul_comm _ _)) (mul_le_mul_of_nonneg_left h4 hβpos.le)
  set j : ℕ := Nat.find hex with hjdef
  have hjspec : 1 < y j := Nat.find_spec hex
  have hjmin : ∀ i, i < j → y i ≤ 1 := fun i hi => not_lt.mp (Nat.find_min hex hi)
  have hjge : ∀ i, j ≤ i → 1 < y i := fun i hi => lt_of_lt_of_le hjspec (hymono j i hi)
  have hcond_eq : ∀ k, |polyDil P k * β| = y k := fun k => by rw [abs_polyDil_mul]
  -- the pointwise two-piece bound for the error
  have hf_bound : ∀ k, polyErrVal P β k ≤ (if k < j then M * y k else 0)
      + C1 * |β| ^ (-(1/(P.natDegree:ℝ))) * (1/2)^k := by
    intro k
    have h2nn : 0 ≤ C1 * |β| ^ (-(1/(P.natDegree:ℝ))) * (1/2)^k :=
      mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg hβpos.le _)) (by positivity)
    rw [polyErrVal, hcond_eq k]
    rcases lt_or_ge k j with hk | hk
    · -- below the threshold: the window is present, use the mean-value bound
      rw [if_pos hk, if_pos (hjmin k hk)]
      have h1 : ‖polyProfile P (2^k) β - 1‖ ≤ M * y k := by
        have h := hhead (2^k) Nat.one_le_two_pow β
        rwa [natCast_two_pow_pow_eq_polyDil P k, ← hyk k] at h
      linarith
    · -- from the threshold on: the window is absent, use the decay
      rw [if_neg (not_lt.mpr hk), if_neg (not_le.mpr (hjge k hk)), sub_zero, zero_add]
      have h1 := hdec β hβ k (le_of_lt (hjge k hk))
      have h3 : (|β| * polyDil P k) ^ (-(1/(P.natDegree:ℝ)))
          = |β| ^ (-(1/(P.natDegree:ℝ))) * (1/2)^k := by
        rw [Real.mul_rpow hβpos.le (polyDil_pos P k).le, polyDil_rpow_neg_inv P hd1 k]
      rw [h3] at h1
      simpa [mul_assoc] using h1
  have hsumg : Summable (fun k : ℕ => (if k < j then M * y k else 0)
      + C1 * |β| ^ (-(1/(P.natDegree:ℝ))) * (1/2)^k) := by
    refine Summable.add ?_ ?_
    · refine summable_of_ne_finset_zero (s := Finset.range j) (fun k hk => ?_)
      rw [Finset.mem_range] at hk
      exact if_neg hk
    · exact (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
  have hsumf : Summable (fun k : ℕ => polyErrVal P β k) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hf_bound hsumg
  rw [← Summable.sum_add_tsum_nat_add j hsumf]
  -- the head: the geometric sum of the plateau
  have hfin : ∑ i ∈ Finset.range j, polyErrVal P β i ≤ 2 * M := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]; simp; linarith [hM]
    have h1 : ∑ i ∈ Finset.range j, polyErrVal P β i ≤ ∑ i ∈ Finset.range j, M * y i := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hij : i < j := Finset.mem_range.mp hi
      rw [polyErrVal, hcond_eq i, if_pos (hjmin i hij)]
      have h := hhead (2^i) Nat.one_le_two_pow β
      rwa [natCast_two_pow_pow_eq_polyDil P i, ← hyk i] at h
    rw [← Finset.mul_sum] at h1
    have hsumy : ∑ i ∈ Finset.range j, y i ≤ 2 := by
      have h2d : (4:ℝ) ≤ (2:ℝ)^P.natDegree := by
        calc (4:ℝ) = (2:ℝ)^2 := by norm_num
          _ ≤ (2:ℝ)^P.natDegree := pow_le_pow_right₀ (by norm_num) hd
      have hden : 0 < (2:ℝ)^P.natDegree - 1 := by linarith
      have hbase : ((2:ℝ)^P.natDegree) ≠ 1 := by linarith
      have hyi : ∀ i, y i = |β| * ((2:ℝ)^P.natDegree)^i := by
        intro i
        rw [hyk i, polyDil, powDil]
        congr 1
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      have hyj : ((2:ℝ)^P.natDegree)^j = polyDil P j := by
        rw [polyDil, powDil, ← pow_mul, ← pow_mul, Nat.mul_comm]
      have hyj2 : y j ≤ (2:ℝ)^P.natDegree := by
        have hprev := hjmin (j-1) (by omega)
        rw [hyk (j-1)] at hprev
        rw [hyk j, polyDil_eq_pred_mul P hpos]
        nlinarith [hprev, pow_pos (by norm_num : (0:ℝ) < 2) P.natDegree]
      calc ∑ i ∈ Finset.range j, y i
          = ∑ i ∈ Finset.range j, |β| * ((2:ℝ)^P.natDegree)^i :=
            Finset.sum_congr rfl (fun i _ => hyi i)
        _ = |β| * ∑ i ∈ Finset.range j, ((2:ℝ)^P.natDegree)^i := by rw [Finset.mul_sum]
        _ = |β| * ((((2:ℝ)^P.natDegree)^j - 1) / ((2:ℝ)^P.natDegree - 1)) := by
            rw [geom_sum_eq hbase j]
        _ ≤ |β| * (((2:ℝ)^P.natDegree)^j / ((2:ℝ)^P.natDegree - 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ hβpos.le
            exact div_le_div_of_nonneg_right
              (by linarith [pow_pos (by positivity : (0:ℝ) < (2:ℝ)^P.natDegree) j]) hden.le
        _ = y j / ((2:ℝ)^P.natDegree - 1) := by rw [hyj, ← mul_div_assoc, ← hyk j]
        _ ≤ (2:ℝ)^P.natDegree / ((2:ℝ)^P.natDegree - 1) :=
            div_le_div_of_nonneg_right hyj2 hden.le
        _ ≤ 2 := by
            rw [div_le_iff₀ hden]
            nlinarith [h2d]
    nlinarith [h1, hsumy, hM]
  -- the tail: the geometric sum of the decay
  have htail : ∑' i : ℕ, polyErrVal P β (i + j) ≤ 2 * C1 := by
    have hle : ∀ i : ℕ, polyErrVal P β (i + j)
        ≤ (C1 * |β| ^ (-(1/(P.natDegree:ℝ))) * (1/2)^j) * (1/2)^i := by
      intro i
      have hb := hf_bound (i + j)
      rw [if_neg (by omega : ¬ (i + j < j)), zero_add] at hb
      refine le_trans hb (le_of_eq ?_)
      rw [pow_add]
      ring
    have hsumg2 : Summable
        (fun i : ℕ => (C1 * |β| ^ (-(1/(P.natDegree:ℝ))) * (1/2)^j) * (1/2)^i) :=
      (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left _
    have hsumf2 : Summable (fun i : ℕ => polyErrVal P β (i + j)) :=
      hsumf.comp_injective (fun a b h => Nat.add_right_cancel h)
    have hcmp := Summable.tsum_le_tsum hle hsumf2 hsumg2
    have hval : (∑' i : ℕ, (C1 * |β| ^ (-(1/(P.natDegree:ℝ))) * (1/2)^j) * (1/2)^i)
        = 2 * (C1 * |β| ^ (-(1/(P.natDegree:ℝ))) * (1/2)^j) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)]
      ring
    rw [hval] at hcmp
    have hkey : |β| ^ (-(1/(P.natDegree:ℝ))) * (1/2)^j ≤ 1 := by
      have h1 : |β| ^ (-(1/(P.natDegree:ℝ))) * (1/2)^j = y j ^ (-(1/(P.natDegree:ℝ))) := by
        rw [← polyDil_rpow_neg_inv P hd1 j, ← Real.mul_rpow hβpos.le (polyDil_pos P j).le,
          ← hyk j]
      rw [h1, Real.rpow_neg (le_of_lt (hypos j)),
        inv_le_one₀ (Real.rpow_pos_of_pos (hypos j) _)]
      exact Real.one_le_rpow hjspec.le (by positivity)
    calc ∑' i : ℕ, polyErrVal P β (i + j)
        ≤ 2 * (C1 * |β| ^ (-(1/(P.natDegree:ℝ))) * (1/2)^j) := hcmp
      _ ≤ 2 * C1 := by nlinarith [hkey, hC1]
  linarith

/-- **The profile replacement is `ℓ¹` along the dyadic scales.**  There is `C > 0` such that for every non-zero frequency `β`, the sum over the dyadic scales of the error made in replacing the profile `polyProfile P (2^k) β` by the sharp indicator `1_{|N^d β| ≤ 1}` is bounded by `C`.

Route (mirror `Commons.Analysis.ExponentialSums.powProfile_replace_sharp_tsum_le`, `pure_power_kernel_maximal_l2.lean` lines ~1356-1543, replacing the pure-power decay by van der Corput for the general polynomial): write `Φ_N(β) = polyProfile P N β`.
* mean-value: `‖Φ_N(β) - 1‖ ≤ 2 * Real.pi * |β| * (∑_{i ≤ d} |P.coeff i|) * N^d` (bound the integrand by `|e^{iu}-1| ≤ |u|`);
* van der Corput: `Commons.Analysis.Oscillatory.van_der_corput_bound d hd` applied to `φ(s) = 2 * Real.pi * β * (toRealPoly P).eval (N * s)` on `[0,1]`, whose `d`-th derivative is the constant `2 * Real.pi * β * d! * P.leadingCoeff * N^d`, gives `‖Φ_N(β)‖ ≤ C * (|β| * N^d)^{-1/d}`;
* split the `tsum` at the first index `j` with `1 < |polyDil P j * β|`, bound the head by the geometric sum `∑_{k<j} |β| * 2^{kd} ≤ 2 * |β| * 2^{jd} ≤ 4`, and the tail by the geometric sum `∑_{k≥j} (|β| * 2^{kd})^{-1/d} ≤ 2 * |β|^{-1/d} * 2^{-j} ≤ 2 * (2^d)^{1/d}`. -/
theorem poly_profile_replace_sharp (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ≠ 0 →
      (∑' k : ℕ, polyErrVal P β k) ≤ C := by
  obtain ⟨C1, hC1pos, hdec⟩ := polyProfile_decay_sharp P hd
  refine poly_profile_replace_sharp_of_bounds P hd
    (4 * Real.pi * (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|))
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => abs_nonneg _))) ?_ C1 hC1pos hdec
  intro N hN β
  exact polyProfile_sub_one_le P N hN β

end Work.BourgainPlan.Maximal
