import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs
import Submission.Work.BourgainPlan.Maximal.poly_profile_replace_sharp

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators ENNReal

open Commons.Analysis.ExponentialSums

/-! ## Elementary facts about the dyadic dilation (reproved here: the copies in
`poly_profile_replace_sharp` are `private`) -/

/-- `(polyDil P k)^{-1/d} = 2^{-k}`. -/
private lemma polyErrDil_rpow_neg_inv (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (k : ℕ) :
    (polyDil P k) ^ (-(1 / (P.natDegree : ℝ))) = (1 / 2 : ℝ) ^ k := by
  have hpos : (0 : ℝ) < polyDil P k := polyDil_pos P k
  rw [Real.rpow_neg hpos.le]
  rw [powDil_rpow P.natDegree hd k]
  rw [show (1 : ℝ) / 2 = ((2 : ℝ))⁻¹ by norm_num, ← inv_pow]

/-- `((2^k : ℕ) : ℝ)^d = polyDil P k`. -/
private lemma polyErrNatCast_two_pow_pow_eq_polyDil (P : Polynomial ℤ) (k : ℕ) :
    ((2 ^ k : ℕ) : ℝ) ^ P.natDegree = polyDil P k := by
  rw [polyDil]; exact (powDil_eq_nat P.natDegree k).symm

/-- Arithmetic core of the geometric comparison: for `0 ≤ x ≤ 1` and `M ≤ C`,
`M x ≤ C x^{-1/d}`. -/
private lemma mul_le_const_mul_rpow_neg {d : ℕ} {M C x : ℝ} (hM : 0 ≤ M) (hMC : M ≤ C)
    (hd : 1 ≤ d) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    M * x ≤ C * x ^ (-(1 / (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hC0 : 0 ≤ C := hM.trans hMC
  rcases eq_or_lt_of_le hx0 with hx | hxpos
  · rw [← hx]
    rw [Real.zero_rpow (neg_ne_zero.mpr (one_div_ne_zero hdne))]
    simp
  · have h1 : x ^ (-(1 / (d : ℝ))) = (x ^ (1 / (d : ℝ)))⁻¹ := Real.rpow_neg hx0 _
    have h2 : x ^ (1 / (d : ℝ)) ≤ 1 :=
      Real.rpow_le_one hx0 hx1 (le_of_lt (one_div_pos.mpr hdR))
    have h3 : (1 : ℝ) ≤ x ^ (-(1 / (d : ℝ))) := by
      rw [h1, one_le_inv₀ (Real.rpow_pos_of_pos hxpos _)]
      exact h2
    calc M * x ≤ M * 1 := mul_le_mul_of_nonneg_left hx1 hM
      _ = M := mul_one M
      _ ≤ C := hMC
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * x ^ (-(1 / (d : ℝ))) := mul_le_mul_of_nonneg_left h3 hC0

/-- The profile error at frequency `0` vanishes. -/
private lemma polyErrVal_zero (P : Polynomial ℤ) (K : ℕ) : polyErrVal P 0 K = 0 := by
  unfold polyErrVal
  have h : |polyDil P K * (0 : ℝ)| ≤ 1 := by
    rw [mul_zero, abs_zero]; norm_num
  rw [if_pos h, polyProfile_zero, sub_self, norm_zero]

/-- **Geometric domination of the profile-replacement error.**  The error at scale `K` is bounded
by a geometric sequence with ratio `1/2`, uniformly in the frequency; the comparison constant is
`max M C₁` where `M` is the mean-value constant and `C₁` the van der Corput constant.

For `|β| · polyDil P K ≤ 1` the sharp window is present and the mean-value bound gives
`≤ M |β| polyDil P K ≤ max M C₁ · |β|^{-1/d} 2^{-K}`, while for `|β| · polyDil P K > 1` the window is
absent and the van der Corput decay gives the same envelope (since `(polyDil P K)^{-1/d} = 2^{-K}`). -/
private lemma polyErrVal_le_geom (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (K : ℕ),
      polyErrVal P β K ≤ C * |β| ^ (-(1 / (P.natDegree : ℝ))) * (1 / 2) ^ K := by
  have hd1 : 1 ≤ P.natDegree := by omega
  obtain ⟨C1, hC1pos, hdec⟩ := polyProfile_decay_sharp P hd
  set M : ℝ := 4 * Real.pi * (∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|)
    with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => abs_nonneg _))
  refine ⟨max M C1, lt_of_lt_of_le hC1pos (le_max_right _ _), ?_⟩
  intro β K
  set x : ℝ := |β| * polyDil P K with hxdef
  have hx0 : 0 ≤ x := by
    rw [hxdef]; exact mul_nonneg (abs_nonneg β) (le_of_lt (polyDil_pos P K))
  have hβabs : |polyDil P K * β| = x := by
    rw [abs_mul, abs_of_pos (polyDil_pos P K), hxdef]
    ring
  have hrpow : x ^ (-(1 / (P.natDegree : ℝ)))
      = |β| ^ (-(1 / (P.natDegree : ℝ))) * (1 / 2) ^ K := by
    rw [hxdef, Real.mul_rpow (abs_nonneg β) (polyDil_pos P K).le,
      polyErrDil_rpow_neg_inv P hd1 K]
  by_cases hx1 : x ≤ 1
  · -- the sharp window is present: use the mean-value bound
    have hwin : |polyDil P K * β| ≤ 1 := by rw [hβabs]; exact hx1
    have hE : polyErrVal P β K = ‖polyProfile P (2 ^ K) β - 1‖ := by
      unfold polyErrVal
      rw [if_pos hwin]
    have h1 : ‖polyProfile P (2 ^ K) β - 1‖ ≤ M * x := by
      have h := polyProfile_sub_one_le P (2 ^ K) Nat.one_le_two_pow β
      rw [polyErrNatCast_two_pow_pow_eq_polyDil P K] at h
      rw [hMdef, hxdef]
      exact h
    have h2 : M * x ≤ max M C1 * (|β| ^ (-(1 / (P.natDegree : ℝ))) * (1 / 2) ^ K) := by
      rw [← hrpow]
      exact mul_le_const_mul_rpow_neg hM0 (le_max_left _ _) hd1 hx0 hx1
    calc polyErrVal P β K = ‖polyProfile P (2 ^ K) β - 1‖ := hE
      _ ≤ M * x := h1
      _ ≤ max M C1 * (|β| ^ (-(1 / (P.natDegree : ℝ))) * (1 / 2) ^ K) := h2
      _ = max M C1 * |β| ^ (-(1 / (P.natDegree : ℝ))) * (1 / 2) ^ K := by ring
  · -- the sharp window is absent: use the van der Corput decay
    have hxgt : 1 < x := not_le.mp hx1
    have hβne : β ≠ 0 := by
      intro h
      rw [hxdef] at hxgt
      rw [h] at hxgt
      simp only [abs_zero, zero_mul] at hxgt
      exact absurd hxgt (by norm_num)
    have hwin : ¬ |polyDil P K * β| ≤ 1 := by rw [hβabs]; exact hx1
    have hE : polyErrVal P β K = ‖polyProfile P (2 ^ K) β‖ := by
      unfold polyErrVal
      rw [if_neg hwin, sub_zero]
    have h1 : ‖polyProfile P (2 ^ K) β‖ ≤ C1 * x ^ (-(1 / (P.natDegree : ℝ))) := by
      have h := hdec β hβne K (by rw [← hxdef]; exact le_of_lt hxgt)
      rwa [← hxdef] at h
    have h2 : C1 * x ^ (-(1 / (P.natDegree : ℝ)))
        ≤ max M C1 * (|β| ^ (-(1 / (P.natDegree : ℝ))) * (1 / 2) ^ K) := by
      rw [← hrpow]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hx0 _)
    calc polyErrVal P β K = ‖polyProfile P (2 ^ K) β‖ := hE
      _ ≤ C1 * x ^ (-(1 / (P.natDegree : ℝ))) := h1
      _ ≤ max M C1 * (|β| ^ (-(1 / (P.natDegree : ℝ))) * (1 / 2) ^ K) := h2
      _ = max M C1 * |β| ^ (-(1 / (P.natDegree : ℝ))) * (1 / 2) ^ K := by ring

/-- **The profile-replacement errors form a uniformly `ℓ¹`-in-scale family.**  There is `C > 0` such that for every arc index `(q,a,l)` and every frequency `θ`, the sum over the dyadic scales `K` of the (extended) profile errors `polyErrNorm P q a l K θ` is bounded by `ofReal C`.

Use `poly_profile_replace_sharp` (module `Submission.Work.BourgainPlan.Maximal.poly_profile_replace_sharp`) for the non-zero frequency case; for `β = 0` use `polyProfile_zero` and the fact that the sharp indicator is satisfied at `β = 0`.  Beware: the exposed statement of `poly_profile_replace_sharp` gives a *real* `tsum` bound, so you must also extract summability of `fun K => polyErrVal P β K` (e.g. from `poly_profile_replace_sharp_of_bounds`'s internal geometric bound, or by re-deriving the pointwise bound `polyErrVal P β K ≤ M * (1/2)^K * |β|^{-1/d}` from `polyProfile_decay_sharp` and `polyProfile_sub_one_le` in the companion modules of that file), and then use `ENNReal.ofReal_tsum_of_nonneg` and `ENNReal.ofReal_mul`. -/
theorem polyErrNorm_tsum_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) (l : ℤ) (θ : ℝ),
      (∑' K : ℕ, polyErrNorm P q a l K θ) ≤ ENNReal.ofReal C := by
  obtain ⟨Csh, hCshpos, hsh⟩ := poly_profile_replace_sharp P hd
  obtain ⟨Cg, _hCgpos, hgeom⟩ := polyErrVal_le_geom P hd
  refine ⟨max Csh Cg, lt_of_lt_of_le hCshpos (le_max_left _ _), ?_⟩
  intro q a l θ
  set β : ℝ := θ - (((a : ℝ) / (q : ℝ) + (l : ℝ)) / (P.leadingCoeff : ℝ)) with hβdef
  have hterm : ∀ K : ℕ, polyErrNorm P q a l K θ = ENNReal.ofReal (polyErrVal P β K) := by
    intro K
    rw [hβdef]
    rfl
  -- the real errors are summable, by the geometric domination
  have hsumm : Summable (fun K : ℕ => polyErrVal P β K) := by
    refine Summable.of_nonneg_of_le (fun K => norm_nonneg _) (fun K => ?_)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (Cg * |β| ^ (-(1 / (P.natDegree : ℝ)))))
    simpa [mul_assoc] using hgeom β K
  by_cases hβ : β = 0
  · -- the zero frequency: the error vanishes at every scale
    have hzero : ∀ K : ℕ, polyErrVal P β K = 0 := by
      intro K
      rw [hβ]
      exact polyErrVal_zero P K
    calc (∑' K : ℕ, polyErrNorm P q a l K θ)
        = ∑' K : ℕ, ENNReal.ofReal (polyErrVal P β K) := tsum_congr hterm
      _ = ∑' _K : ℕ, (0 : ℝ≥0∞) := by
          refine tsum_congr (fun K => ?_)
          rw [hzero K, ENNReal.ofReal_zero]
      _ = 0 := tsum_zero
      _ ≤ ENNReal.ofReal (max Csh Cg) := bot_le
  · calc (∑' K : ℕ, polyErrNorm P q a l K θ)
        = ∑' K : ℕ, ENNReal.ofReal (polyErrVal P β K) := tsum_congr hterm
      _ = ENNReal.ofReal (∑' K : ℕ, polyErrVal P β K) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun K => norm_nonneg _) hsumm).symm
      _ ≤ ENNReal.ofReal (max Csh Cg) :=
          ENNReal.ofReal_le_ofReal (le_trans (hsh β hβ) (le_max_left _ _))

end Work.BourgainPlan.Maximal
