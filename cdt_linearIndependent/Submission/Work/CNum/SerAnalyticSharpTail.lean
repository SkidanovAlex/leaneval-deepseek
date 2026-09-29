import Mathlib
import Submission.Work.CNum.SerUpDefs
import Submission.Work.CNum.CPlan
import Submission.Work.ANum.HLog
import Submission.Work.CNum.norm_pow_sub_pow_le_sharp

/-!
# `Work.CNum.SerAnalyticSharpTail` — the sharp-tail analytic bound behind `serUp`

Same statement as `Work.CNum.SerAnalyticSharp` (imported from the hauptmodul product formula
`log ‖h q‖ = log 256 + log ‖q‖ + ∑'ₙ 24 log ‖1 + qⁿ⁺¹‖` for `‖q‖ < 1`) but with the remainder of
the logarithmic series bounded by the **sharp** three-term estimate

  `log (1 + x) ≤ x - x²/2 + x³/3`   (`x = Rᴶ ≥ 0`)   instead of   `log (1 + x) ≤ x`,

so the geometric tail `R^{SERM+1}/(1-R)` is sharpened to

  `R^{SERM+1}/(1-R) - R^{2(SERM+1)}/(2(1-R²)) + R^{3(SERM+1)}/(3(1-R³))`.

The finite part is the same as in `SerAnalyticSharp`: the sharp telescoping bound
`‖wᴶ - q₀ᴶ‖ ≤ Rᴶ - cᴶ` (`Work.CNum.norm_pow_sub_pow_le_sharp`) gives, term by term,
`‖1 + wᴶ‖ ≤ ‖1 + q₀ᴶ‖ + (Rᴶ - cᴶ)`.
-/

namespace Work.CNum

open scoped BigOperators

/-- The cubic lower bound for the logarithm: `log (1 + x) ≤ x - x²/2 + x³/3` for `x ≥ 0`.
(The difference has derivative `x³/(1+x) ≥ 0` and vanishes at `0`.) -/
private lemma logOneAddLeCubic {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  have hHas : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - Real.log (1 + s))
        (t ^ 3 / (1 + t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      have h := (hasDerivAt_pow 2 t).div_const 2
      refine h.congr_deriv ?_
      rw [show 2 - 1 = 1 by norm_num, pow_one]; ring
    have h3 : HasDerivAt (fun s : ℝ => s ^ 3 / 3) (t ^ 2) t := by
      have h := (hasDerivAt_pow 3 t).div_const 3
      refine h.congr_deriv ?_
      rw [show 3 - 1 = 2 by norm_num]; ring
    have h4 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) ((1 + t)⁻¹) t := by
      have h : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t :=
        ((hasDerivAt_id t).const_add 1).log (by linarith : (1 : ℝ) + t ≠ 0)
      refine h.congr_deriv ?_
      rw [one_div]
    have htot : HasDerivAt (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - Real.log (1 + s))
        ((1 - t + t ^ 2) - (1 + t)⁻¹) t := ((h1.sub h2).add h3).sub h4
    refine htot.congr_deriv ?_
    have h1t : (1 : ℝ) + t ≠ 0 := by linarith
    field_simp
    ring
  have hmono : MonotoneOn (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - Real.log (1 + s))
      (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ ?_
      · refine ContinuousOn.add (ContinuousOn.sub continuousOn_id ?_) ?_
        · exact (continuousOn_id.pow 2).div_const 2
        · exact (continuousOn_id.pow 3).div_const 3
      · exact ContinuousOn.log (continuousOn_const.add continuousOn_id)
          (fun t ht => by have h1 : (0 : ℝ) ≤ t := ht; linarith)
    · intro t ht
      have ht0 : 0 < t := by rw [interior_Ici] at ht; exact ht
      exact (hHas t ht0).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 < t := by rw [interior_Ici] at ht; exact ht
      rw [(hHas t ht0).deriv]
      positivity
  have h := hmono (by simp : (0 : ℝ) ∈ Set.Ici 0) (by simpa using hx : x ∈ Set.Ici 0) hx
  have h0 : (fun s : ℝ => s - s ^ 2 / 2 + s ^ 3 / 3 - Real.log (1 + s)) 0 = 0 := by
    simp
  rw [h0] at h
  have h' : 0 ≤ x - x ^ 2 / 2 + x ^ 3 / 3 - Real.log (1 + x) := h
  linarith

/-- Reindex a sum over the exponents `1, …, M` as a sum over `0, …, M - 1`. -/
private lemma sum_range_succ_eq_sum_Icc (f : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ Finset.range M, f (n + 1)) = ∑ J ∈ Finset.Icc 1 M, f J := by
  have h1 : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := by
    simpa [Nat.succ_eq_add_one] using Finset.Ico_succ_right_eq_Icc (1 : ℕ) M
  rw [← h1, Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl (fun k _ => by rw [Nat.add_comm])

/-- Sharp geometric tail bound for the logarithmic series: for `‖q‖ ≤ R < 1`,

  `∑' j, log ‖1 + q^{j+K+1}‖ ≤ R^{K+1}/(1-R) - R^{2(K+1)}/(2(1-R²)) + R^{3(K+1)}/(3(1-R³))`. -/
private lemma logGeomSharpTailAux {q : ℂ} {R : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hq : ‖q‖ ≤ R) (K : ℕ) :
    ∑' j : ℕ, Real.log ‖(1 : ℂ) + q ^ (j + K + 1)‖ ≤
      R ^ (K + 1) / (1 - R)
        - (R ^ (2 * (K + 1)) / (2 * (1 - R ^ 2)) - R ^ (3 * (K + 1)) / (3 * (1 - R ^ 3))) := by
  have hR2 : R ^ 2 < 1 := pow_lt_one₀ hR0 hR1 (by norm_num : (2 : ℕ) ≠ 0)
  have hR3 : R ^ 3 < 1 := pow_lt_one₀ hR0 hR1 (by norm_num : (3 : ℕ) ≠ 0)
  -- pointwise sharp bound
  have hpoint : ∀ j : ℕ, Real.log ‖(1 : ℂ) + q ^ (j + K + 1)‖ ≤
      R ^ (j + K + 1) - R ^ (2 * (j + K + 1)) / 2 + R ^ (3 * (j + K + 1)) / 3 := by
    intro j
    have hgeo_le : R ^ (j + K + 1) ≤ R := by
      have h1 : 1 ≤ j + K + 1 := by omega
      calc R ^ (j + K + 1) ≤ R ^ 1 := pow_le_pow_of_le_one hR0 hR1.le h1
        _ = R := pow_one R
    have hRN1 : R ^ (j + K + 1) < 1 := lt_of_le_of_lt hgeo_le hR1
    have hqN : ‖q ^ (j + K + 1)‖ ≤ R ^ (j + K + 1) := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg q) hq _
    have hqN1 : ‖q ^ (j + K + 1)‖ < 1 := lt_of_le_of_lt hqN hRN1
    have hpos : 0 < ‖(1 : ℂ) + q ^ (j + K + 1)‖ := by
      have h := norm_add_le ((1 : ℂ) + q ^ (j + K + 1)) (-(q ^ (j + K + 1)))
      rw [show (1 : ℂ) + q ^ (j + K + 1) + -(q ^ (j + K + 1)) = 1 by ring,
        norm_one, norm_neg] at h
      linarith
    have hb : ‖(1 : ℂ) + q ^ (j + K + 1)‖ ≤ 1 + R ^ (j + K + 1) := by
      calc ‖(1 : ℂ) + q ^ (j + K + 1)‖ ≤ ‖(1 : ℂ)‖ + ‖q ^ (j + K + 1)‖ := norm_add_le _ _
        _ = 1 + ‖q ^ (j + K + 1)‖ := by simp
        _ ≤ 1 + R ^ (j + K + 1) := by linarith
    calc Real.log ‖(1 : ℂ) + q ^ (j + K + 1)‖
        ≤ Real.log (1 + R ^ (j + K + 1)) := Real.log_le_log hpos hb
      _ ≤ R ^ (j + K + 1) - (R ^ (j + K + 1)) ^ 2 / 2 + (R ^ (j + K + 1)) ^ 3 / 3 :=
          logOneAddLeCubic (pow_nonneg hR0 _)
      _ = R ^ (j + K + 1) - R ^ (2 * (j + K + 1)) / 2 + R ^ (3 * (j + K + 1)) / 3 := by
          have e2 : (R ^ (j + K + 1)) ^ 2 = R ^ (2 * (j + K + 1)) := by
            rw [← pow_mul, Nat.mul_comm (j + K + 1) 2]
          have e3 : (R ^ (j + K + 1)) ^ 3 = R ^ (3 * (j + K + 1)) := by
            rw [← pow_mul, Nat.mul_comm (j + K + 1) 3]
          rw [e2, e3]
  -- summability of the logarithmic series
  have hsumm_f : Summable (fun j : ℕ => Real.log ‖(1 : ℂ) + q ^ (j + K + 1)‖) := by
    have hgeo : Summable (fun j : ℕ => q ^ (j + K + 1)) := by
      have h2 : Summable (fun j : ℕ => q ^ (j + (K + 1))) :=
        (summable_nat_add_iff (K + 1)).2
          (summable_geometric_iff_norm_lt_one.mpr (lt_of_le_of_lt hq hR1))
      exact h2.congr (fun j => by rw [Nat.add_assoc])
    exact hgeo.norm.summable_log_norm_one_add
  -- the comparison series and its exact sum
  have hA : HasSum (fun j : ℕ => R ^ (j + K + 1)) (R ^ (K + 1) / (1 - R)) := by
    have h := (hasSum_geometric_of_lt_one hR0 hR1).mul_left (R ^ (K + 1))
    have hfun : (fun j : ℕ => R ^ (K + 1) * R ^ j) = fun j : ℕ => R ^ (j + K + 1) := by
      funext j; rw [← pow_add]; congr 1; omega
    rw [hfun] at h
    rwa [div_eq_mul_inv]
  have hB : HasSum (fun j : ℕ => R ^ (2 * (j + K + 1)) / 2)
      (R ^ (2 * (K + 1)) / (2 * (1 - R ^ 2))) := by
    have hgeo := hasSum_geometric_of_lt_one (sq_nonneg R) hR2
    have h := hgeo.mul_left ((R ^ 2) ^ (K + 1))
    have hfun : (fun j : ℕ => (R ^ 2) ^ (K + 1) * (R ^ 2) ^ j)
        = fun j : ℕ => R ^ (2 * (j + K + 1)) := by
      funext j; rw [← pow_add, ← pow_mul]; congr 1; omega
    rw [hfun] at h
    have h2 := h.div_const 2
    have hval : ((R ^ 2) ^ (K + 1) * (1 - R ^ 2)⁻¹) / 2
        = R ^ (2 * (K + 1)) / (2 * (1 - R ^ 2)) := by
      rw [pow_mul, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]; ring
    rwa [hval] at h2
  have hC : HasSum (fun j : ℕ => R ^ (3 * (j + K + 1)) / 3)
      (R ^ (3 * (K + 1)) / (3 * (1 - R ^ 3))) := by
    have hgeo := hasSum_geometric_of_lt_one (pow_nonneg hR0 3) hR3
    have h := hgeo.mul_left ((R ^ 3) ^ (K + 1))
    have hfun : (fun j : ℕ => (R ^ 3) ^ (K + 1) * (R ^ 3) ^ j)
        = fun j : ℕ => R ^ (3 * (j + K + 1)) := by
      funext j; rw [← pow_add, ← pow_mul]; congr 1; omega
    rw [hfun] at h
    have h3 := h.div_const 3
    have hval : ((R ^ 3) ^ (K + 1) * (1 - R ^ 3)⁻¹) / 3
        = R ^ (3 * (K + 1)) / (3 * (1 - R ^ 3)) := by
      rw [pow_mul, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]; ring
    rwa [hval] at h3
  have hsumm_c : Summable (fun j : ℕ =>
      R ^ (j + K + 1) - R ^ (2 * (j + K + 1)) / 2 + R ^ (3 * (j + K + 1)) / 3) :=
    ((hA.sub hB).add hC).summable
  calc ∑' j : ℕ, Real.log ‖(1 : ℂ) + q ^ (j + K + 1)‖
      ≤ ∑' j : ℕ, (R ^ (j + K + 1) - R ^ (2 * (j + K + 1)) / 2 + R ^ (3 * (j + K + 1)) / 3) :=
        hsumm_f.tsum_le_tsum hpoint hsumm_c
    _ = R ^ (K + 1) / (1 - R)
          - (R ^ (2 * (K + 1)) / (2 * (1 - R ^ 2)) - R ^ (3 * (K + 1)) / (3 * (1 - R ^ 3))) := by
        have hvalc : R ^ (K + 1) / (1 - R) - R ^ (2 * (K + 1)) / (2 * (1 - R ^ 2))
              + R ^ (3 * (K + 1)) / (3 * (1 - R ^ 3))
            = R ^ (K + 1) / (1 - R)
              - (R ^ (2 * (K + 1)) / (2 * (1 - R ^ 2))
                - R ^ (3 * (K + 1)) / (3 * (1 - R ^ 3))) := by ring
        rw [((hA.sub hB).add hC).tsum_eq, hvalc]

theorem SerAnalyticSharpTail {w q₀ : ℂ} {R c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hρc : ρ < c) (hq0 : ‖q₀‖ = c) (hw : ‖w‖ ≤ R) (hwq : ‖w - q₀‖ ≤ ρ) (hR : R = c + ρ) (hR1 : R < 1) : Real.log ‖Submission.CDTPlan.hauptH w‖ ≤ Real.log 256 + Real.log R + 24 * (∑ J ∈ Finset.Icc 1 Work.CNum.SERM, Real.log (‖(1 : ℂ) + q₀ ^ J‖ + (R ^ J - c ^ J))) + 24 * (R ^ (Work.CNum.SERM + 1) / (1 - R) - (R ^ (2 * (Work.CNum.SERM + 1)) / (2 * (1 - R ^ 2)) - R ^ (3 * (Work.CNum.SERM + 1)) / (3 * (1 - R ^ 3)))) := by
  have hρ0 : 0 ≤ ρ := hρ.le
  have hRpos : 0 < R := by rw [hR]; exact add_pos hc hρ
  have hwlt1 : ‖w‖ < 1 := lt_of_le_of_lt hw hR1
  -- `w` stays away from `0`: `‖w‖ ≥ c - ρ > 0`
  have hwpos : 0 < ‖w‖ := by
    have h : c ≤ ‖w‖ + ρ := by
      calc c = ‖q₀‖ := hq0.symm
        _ = ‖w + (q₀ - w)‖ := by rw [show w + (q₀ - w) = q₀ by ring]
        _ ≤ ‖w‖ + ‖q₀ - w‖ := norm_add_le _ _
        _ = ‖w‖ + ‖w - q₀‖ := by rw [norm_sub_rev]
        _ ≤ ‖w‖ + ρ := by linarith
    linarith
  -- the logarithm of the hauptmodul as an explicit convergent series
  have hlogid := Work.ANum.log_norm_hauptH_of_norm_lt_one (q := w) hwlt1 (norm_pos_iff.mp hwpos)
  rw [hlogid, tsum_mul_left]
  have hsumm : Summable (fun n : ℕ => Real.log ‖(1 : ℂ) + w ^ (n + 1)‖) := by
    have hgeo : Summable (fun n : ℕ => w ^ (n + 1)) :=
      (summable_nat_add_iff 1).2 (summable_geometric_iff_norm_lt_one.mpr hwlt1)
    have hgnorm : Summable (fun n : ℕ => ‖w ^ (n + 1)‖) := by
      simpa [norm_pow] using hgeo.norm
    exact hgnorm.summable_log_norm_one_add
  have hsplit := hsumm.sum_add_tsum_nat_add SERM
  -- termwise domination by `‖1 + q₀ᴶ‖ + (Rᴶ - cᴶ)`
  have hterm : ∀ n : ℕ, Real.log ‖(1 : ℂ) + w ^ (n + 1)‖ ≤
      Real.log (‖(1 : ℂ) + q₀ ^ (n + 1)‖ + (R ^ (n + 1) - c ^ (n + 1))) := by
    intro n
    have hnd : ‖w ^ (n + 1) - q₀ ^ (n + 1)‖ ≤ R ^ (n + 1) - c ^ (n + 1) := by
      simpa [hR] using norm_pow_sub_pow_le_sharp hρ0 hq0 hwq (n + 1)
    have hb : ‖(1 : ℂ) + w ^ (n + 1)‖ ≤
        ‖(1 : ℂ) + q₀ ^ (n + 1)‖ + (R ^ (n + 1) - c ^ (n + 1)) := by
      have h1 : (1 : ℂ) + w ^ (n + 1) =
          ((1 : ℂ) + q₀ ^ (n + 1)) + (w ^ (n + 1) - q₀ ^ (n + 1)) := by ring
      rw [h1]
      calc ‖((1 : ℂ) + q₀ ^ (n + 1)) + (w ^ (n + 1) - q₀ ^ (n + 1))‖
          ≤ ‖(1 : ℂ) + q₀ ^ (n + 1)‖ + ‖w ^ (n + 1) - q₀ ^ (n + 1)‖ := norm_add_le _ _
        _ ≤ ‖(1 : ℂ) + q₀ ^ (n + 1)‖ + (R ^ (n + 1) - c ^ (n + 1)) := by linarith
    have hp : 0 < ‖(1 : ℂ) + w ^ (n + 1)‖ := by
      have h2 : ‖w ^ (n + 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg w) hwlt1 (Nat.succ_ne_zero n)
      have h3 : (1 : ℝ) ≤ ‖(1 : ℂ) + w ^ (n + 1)‖ + ‖w ^ (n + 1)‖ := by
        have h := norm_add_le ((1 : ℂ) + w ^ (n + 1)) (-(w ^ (n + 1)))
        rw [show (1 : ℂ) + w ^ (n + 1) + -(w ^ (n + 1)) = 1 by ring, norm_one, norm_neg] at h
        linarith
      linarith
    exact Real.log_le_log hp hb
  -- the first `SERM` terms of the series
  have hfin : (∑ n ∈ Finset.range SERM, Real.log ‖(1 : ℂ) + w ^ (n + 1)‖) ≤
      ∑ J ∈ Finset.Icc 1 SERM, Real.log (‖(1 : ℂ) + q₀ ^ J‖ + (R ^ J - c ^ J)) := by
    calc (∑ n ∈ Finset.range SERM, Real.log ‖(1 : ℂ) + w ^ (n + 1)‖)
        ≤ ∑ n ∈ Finset.range SERM,
            Real.log (‖(1 : ℂ) + q₀ ^ (n + 1)‖ + (R ^ (n + 1) - c ^ (n + 1))) :=
          Finset.sum_le_sum (fun n _ => hterm n)
      _ = ∑ J ∈ Finset.Icc 1 SERM, Real.log (‖(1 : ℂ) + q₀ ^ J‖ + (R ^ J - c ^ J)) :=
          sum_range_succ_eq_sum_Icc
            (fun J => Real.log (‖(1 : ℂ) + q₀ ^ J‖ + (R ^ J - c ^ J))) SERM
  -- the sharp geometric tail of the series
  have htail : (∑' i : ℕ, Real.log ‖(1 : ℂ) + w ^ (i + SERM + 1)‖) ≤
      R ^ (SERM + 1) / (1 - R)
        - (R ^ (2 * (SERM + 1)) / (2 * (1 - R ^ 2))
            - R ^ (3 * (SERM + 1)) / (3 * (1 - R ^ 3))) :=
    logGeomSharpTailAux hRpos.le hR1 hw SERM
  have hkey : (∑' n : ℕ, Real.log ‖(1 : ℂ) + w ^ (n + 1)‖) ≤
      (∑ J ∈ Finset.Icc 1 SERM, Real.log (‖(1 : ℂ) + q₀ ^ J‖ + (R ^ J - c ^ J))) +
        (R ^ (SERM + 1) / (1 - R)
          - (R ^ (2 * (SERM + 1)) / (2 * (1 - R ^ 2))
              - R ^ (3 * (SERM + 1)) / (3 * (1 - R ^ 3)))) := by
    rw [← hsplit]
    exact add_le_add hfin htail
  have hlogw : Real.log ‖w‖ ≤ Real.log R := Real.log_le_log hwpos hw
  have hmul : 24 * (∑' n : ℕ, Real.log ‖(1 : ℂ) + w ^ (n + 1)‖) ≤
      24 * (∑ J ∈ Finset.Icc 1 SERM, Real.log (‖(1 : ℂ) + q₀ ^ J‖ + (R ^ J - c ^ J))) +
        24 * (R ^ (SERM + 1) / (1 - R)
          - (R ^ (2 * (SERM + 1)) / (2 * (1 - R ^ 2))
              - R ^ (3 * (SERM + 1)) / (3 * (1 - R ^ 3)))) := by
    have h24 := mul_le_mul_of_nonneg_left hkey (by norm_num : (0 : ℝ) ≤ 24)
    linarith [mul_add 24
      (∑ J ∈ Finset.Icc 1 SERM, Real.log (‖(1 : ℂ) + q₀ ^ J‖ + (R ^ J - c ^ J)))
      (R ^ (SERM + 1) / (1 - R)
        - (R ^ (2 * (SERM + 1)) / (2 * (1 - R ^ 2))
            - R ^ (3 * (SERM + 1)) / (3 * (1 - R ^ 3))))]
  linarith

end Work.CNum
