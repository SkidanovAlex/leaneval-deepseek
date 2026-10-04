import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Friedrichs-mollifier error estimate for the weighted `ℓ²` norm

Let `ρ : ℝ^ι → ℝ` be a cutoff with `ρ = 1` on the unit ball and `|ρ| ≤ 1` everywhere (the
profile of the Friedrichs mollifier `trunc ρ ε`), and let `ε ∈ (0,1]`.  For a coefficient
family `c` on `ℤ^ι` with finite `H^{s+1}` weighted norm we show

  `CSq s (trunc ρ ε c - c) ≤ 4 ε² CSq (s+1) c`.

The only point is that `trunc ρ ε c - c` is supported (frequency-wise) on the complement of
the unit ball scaled by `ε`: if `ρ (ε • k) ≠ 1` then `ε² Σ kᵢ² > 1`, hence

  `ε² ⟨k⟩² = ε² (1 + Σ kᵢ²) > 1`,

so that `⟨k⟩^{2s} ≤ ε² ⟨k⟩^{2s+2}` there.  Together with the crude bound
`|ρ (ε • k) - 1| ≤ 2` this gives the pointwise estimate, and summing over `k` the claim.
-/

namespace Work.Diff.STE

theorem CSq_trunc_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ1 : ∀ y : ι → ℝ, (∑ i, (y i) ^ 2) ≤ 1 → ρ y = 1)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (s : ℕ) (c : (ι → ℤ) → ℂ)
    (h : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + 1) * ‖c k‖ ^ 2)) :
    Work.Diff.STE.CSq s (fun k => Work.Diff.STE.trunc ρ ε c k - c k)
      ≤ 4 * ε ^ 2 * Work.Diff.STE.CSq (s + 1) c := by
  classical
  -- Pointwise control of the weight on the support of the multiplier's error.
  have hkey : ∀ k : ι → ℤ, ρ (ε • (fun i => (k i : ℝ))) ≠ 1 →
      wt k ^ s ≤ ε ^ 2 * wt k ^ (s + 1) := by
    intro k hk
    have hsum : 1 < ∑ i, ((ε • (fun i => (k i : ℝ))) i) ^ 2 := by
      by_contra hcon
      exact hk (hρ1 _ (not_lt.mp hcon))
    have hsumE : ∑ i, ((ε • (fun i => (k i : ℝ))) i) ^ 2
        = ε ^ 2 * ∑ i, ((k i : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; ring
    have hSnn : (0 : ℝ) ≤ ∑ i, ((k i : ℝ)) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
    have hwt : wt k = 1 + ∑ i, ((k i : ℝ)) ^ 2 := rfl
    have hgt : 1 < ε ^ 2 * wt k := by
      rw [hwt]
      have hsum2 : 1 < ε ^ 2 * ∑ i, ((k i : ℝ)) ^ 2 := hsumE ▸ hsum
      nlinarith [hsum2, hSnn, hε2]
    have hle1 : 1 ≤ ε ^ 2 * wt k := le_of_lt hgt
    have hpos : (0 : ℝ) ≤ wt k ^ s := pow_nonneg (le_of_lt (wt_pos k)) s
    calc wt k ^ s = wt k ^ s * 1 := (mul_one _).symm
      _ ≤ wt k ^ s * (ε ^ 2 * wt k) := mul_le_mul_of_nonneg_left hle1 hpos
      _ = ε ^ 2 * wt k ^ (s + 1) := by rw [pow_succ]; ring
  -- Pointwise estimate on the coefficients.
  have hpt : ∀ k : ι → ℤ, wt k ^ s * ‖trunc ρ ε c k - c k‖ ^ 2
      ≤ 4 * ε ^ 2 * (wt k ^ (s + 1) * ‖c k‖ ^ 2) := by
    intro k
    have hsub : trunc ρ ε c k - c k
        = (((ρ (ε • (fun i => (k i : ℝ))) - 1 : ℝ)) : ℂ) * c k := by
      rw [trunc, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    have hsq : ‖trunc ρ ε c k - c k‖ ^ 2
        = (ρ (ε • (fun i => (k i : ℝ))) - 1) ^ 2 * ‖c k‖ ^ 2 := by
      rw [hsub, norm_mul, mul_pow, Complex.sq_norm, Complex.normSq_ofReal]
      ring
    by_cases hk : ρ (ε • (fun i => (k i : ℝ))) = 1
    · have h0 : (ρ (ε • (fun i => (k i : ℝ))) - 1) ^ 2 = 0 := by rw [hk]; norm_num
      rw [hsq, h0, zero_mul, mul_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg ε))
        (mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) _) (sq_nonneg _))
    · have hkeyk := hkey k hk
      have h4 : (ρ (ε • (fun i => (k i : ℝ))) - 1) ^ 2 ≤ 4 := by
        have hb : |ρ (ε • (fun i => (k i : ℝ)))| ≤ 1 := by
          have := hρb (ε • (fun i => (k i : ℝ)))
          rwa [Real.norm_eq_abs] at this
        obtain ⟨hlo, hhi⟩ := abs_le.mp hb
        nlinarith
      rw [hsq]
      calc wt k ^ s * ((ρ (ε • (fun i => (k i : ℝ))) - 1) ^ 2 * ‖c k‖ ^ 2)
          ≤ wt k ^ s * (4 * ‖c k‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 (sq_nonneg _))
              (pow_nonneg (le_of_lt (wt_pos k)) s)
        _ ≤ (ε ^ 2 * wt k ^ (s + 1)) * (4 * ‖c k‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hkeyk (mul_nonneg (by norm_num) (sq_nonneg _))
        _ = 4 * ε ^ 2 * (wt k ^ (s + 1) * ‖c k‖ ^ 2) := by ring
  -- Summability and summation.
  have hGsum : Summable (fun k : ι → ℤ => 4 * ε ^ 2 * (wt k ^ (s + 1) * ‖c k‖ ^ 2)) :=
    h.mul_left (4 * ε ^ 2)
  have hgsum : Summable (fun k : ι → ℤ => wt k ^ s * ‖trunc ρ ε c k - c k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _)) hpt hGsum
  have hle := Summable.tsum_le_tsum hpt hgsum hGsum
  have hfinal : ∑' k : ι → ℤ, 4 * ε ^ 2 * (wt k ^ (s + 1) * ‖c k‖ ^ 2)
      = 4 * ε ^ 2 * CSq (s + 1) c := by
    rw [CSq, tsum_mul_left]
  have hCSq : CSq s (fun k => trunc ρ ε c k - c k)
      = ∑' k : ι → ℤ, wt k ^ s * ‖trunc ρ ε c k - c k‖ ^ 2 := rfl
  rw [hCSq]
  exact hle.trans (le_of_eq hfinal)

end Work.Diff.STE
