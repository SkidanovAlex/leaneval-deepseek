import Mathlib
import Submission.Work.KMTAreas.A4.denseMultiples_kern
import Submission.Work.KMTAreas.A4.amplifyDenseDefs

/-!
# The final arithmetic of Area A4 ("large Erdős–Turán sum forces a good rational approximation")

`Work.KMTAreas.A4.finalArithmetic` is the arithmetic endgame of the A4 chapter: if the
Erdős–Turán discrepancy sum
`∑_{q=1}^{Q-1} (1/q) · 1/(2 ‖q α‖)`
(`‖x‖ = nDist x` the distance of `x` to the nearest integer) is at least
`(π/2)·(c ρ - 2 δ - 1/Q)·(2N+1)` with `c ≥ 3/4`, `4δ ≤ ρ`, `7/ρ ≤ Q ≤ 8/ρ`, then `α` is within
`2^8/(ρ^2 (2N+1))` of a rational `a/q` with `q ≤ 8/ρ`.

The proof is a pigeonhole (maximum) argument followed by an explicit contrapositive estimate.

* From the hypotheses on `ρ, δ, c, Q` one gets `c ρ - 2 δ - 1/Q ≥ 3ρ/28`; hence the sum is
  `≥ (π/2)·(3ρ/28)·(2N+1) ≥ (9/56)·ρ·(2N+1)`.
* Let `q₀ ∈ [1,Q-1]` maximise the summand `g q = (1/q)·1/(2‖qα‖)`.  Since there are `Q-1`
  summands and `Q-1 ≤ 8/ρ`, `g q₀ ≥ (ρ/8)·(9/56)·ρ·(2N+1) = (9/448)·ρ²·(2N+1)`.
* Finally `g q₀ ≤ 1/(2 ‖q₀α‖)` (as `q₀ ≥ 1`), so `‖q₀α‖ ≤ 224/(9ρ²(2N+1))`; with
  `a = round (q₀ α)` and the identity `|α - a/q₀| = ‖q₀α‖/q₀` (`abs_sub_div_round`) this gives
  `|α - a/q₀| ≤ 224/(9ρ²(2N+1)) ≤ 2^8/(ρ²(2N+1))`.
-/

namespace Work.KMTAreas.A4

open scoped BigOperators

theorem finalArithmetic (Q N : ℕ) (hQ2 : 2 ≤ Q) (hN : 1 ≤ N) (α δ ρ c : ℝ) (hρ : 0 < ρ) (hδ : 0 < δ) (hρδ : 4 * δ ≤ ρ) (hc : 3/4 ≤ c) (hQlow : 7 / ρ ≤ (Q:ℝ)) (hQhigh : (Q:ℝ) ≤ 8 / ρ) (hbound : (c * ρ - 2 * δ - 1 / (Q:ℝ)) * (2 * (N:ℝ) + 1) ≤ (2 / Real.pi) * ∑ q ∈ Finset.Icc 1 (Q-1), (1 / (q:ℝ)) * (1 / (2 * nDist ((q:ℝ) * α)))) : ∃ q : ℕ, 1 ≤ q ∧ (q:ℝ) ≤ 8 / ρ ∧ ∃ a : ℤ, |α - (a:ℝ) / (q:ℝ)| ≤ 2^8 / (ρ^2 * (2 * (N:ℝ) + 1)) := by
  have hQpos : (0:ℝ) < (Q:ℝ) := by
    have h : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ2
    linarith
  have hDpos : (0:ℝ) < 2 * (N:ℝ) + 1 := by positivity
  -- (1) the coefficient is bounded below by `3ρ/28`
  have hQlow' : 7 ≤ (Q:ℝ) * ρ := (div_le_iff₀ hρ).mp hQlow
  have hinvQ : 1 / (Q:ℝ) ≤ ρ / 7 := by
    rw [div_le_iff₀ hQpos]
    nlinarith [hQlow']
  have hcoef : (3/28) * ρ ≤ c * ρ - 2 * δ - 1 / (Q:ℝ) := by
    have h1 : (3/4) * ρ ≤ c * ρ := by nlinarith [hc, hρ]
    have h2 : 2 * δ ≤ ρ / 2 := by linarith [hρδ]
    linarith
  -- (2) a term of maximal size
  have hsne : (Finset.Icc 1 (Q-1)).Nonempty := Finset.nonempty_Icc.mpr (by omega)
  obtain ⟨q0, hq0mem, hq0max⟩ :=
    Finset.exists_max_image (Finset.Icc 1 (Q-1))
      (fun q => (1 / (q:ℝ)) * (1 / (2 * nDist ((q:ℝ) * α)))) hsne
  have hq0low : 1 ≤ q0 := (Finset.mem_Icc.mp hq0mem).1
  have hq0hi : q0 ≤ Q - 1 := (Finset.mem_Icc.mp hq0mem).2
  have hq0pos : (0:ℝ) < (q0:ℝ) := by exact_mod_cast hq0low
  have hq0lowR : (1:ℝ) ≤ (q0:ℝ) := by exact_mod_cast hq0low
  set c0 : ℝ := (1 / (q0:ℝ)) * (1 / (2 * nDist ((q0:ℝ) * α))) with hc0
  have hc0nonneg : 0 ≤ c0 := by
    rw [hc0]
    have h1 : (0:ℝ) ≤ 1 / (2 * nDist ((q0:ℝ) * α)) := by
      apply div_nonneg (by norm_num)
      have := nDist_nonneg ((q0:ℝ) * α)
      linarith
    have h2 : (0:ℝ) ≤ 1 / (q0:ℝ) := le_of_lt (by positivity)
    exact mul_nonneg h2 h1
  -- the sum is at most `card * c0`
  have hsum_le : (∑ q ∈ Finset.Icc 1 (Q-1), (1 / (q:ℝ)) * (1 / (2 * nDist ((q:ℝ) * α)))) ≤ ((Finset.Icc 1 (Q-1)).card : ℝ) * c0 := by
    calc (∑ q ∈ Finset.Icc 1 (Q-1), (1 / (q:ℝ)) * (1 / (2 * nDist ((q:ℝ) * α))))
        ≤ ∑ q ∈ Finset.Icc 1 (Q-1), c0 := by
          apply Finset.sum_le_sum
          intro q hq
          exact hq0max q hq
      _ = ((Finset.Icc 1 (Q-1)).card : ℝ) * c0 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc 1 (Q-1)).card : ℝ) ≤ 8 / ρ := by
    have hcardeq : (Finset.Icc 1 (Q-1)).card = Q - 1 := by rw [Nat.card_Icc]; omega
    rw [hcardeq, Nat.cast_sub (by omega : 1 ≤ Q)]
    linarith [hQhigh]
  have hsum_le2 : (∑ q ∈ Finset.Icc 1 (Q-1), (1 / (q:ℝ)) * (1 / (2 * nDist ((q:ℝ) * α)))) ≤ (8 / ρ) * c0 :=
    hsum_le.trans (mul_le_mul_of_nonneg_right hcard hc0nonneg)
  -- (3) the sum is at least `(9/56) ρ (2N+1)`
  have hS_lb : (9/56) * ρ * (2 * (N:ℝ) + 1) ≤ (∑ q ∈ Finset.Icc 1 (Q-1), (1 / (q:ℝ)) * (1 / (2 * nDist ((q:ℝ) * α)))) := by
    have h1 : (3/28) * ρ * (2 * (N:ℝ) + 1) ≤ (2 / Real.pi) * (∑ q ∈ Finset.Icc 1 (Q-1), (1 / (q:ℝ)) * (1 / (2 * nDist ((q:ℝ) * α)))) := by
      have hh := mul_le_mul_of_nonneg_right hcoef (le_of_lt hDpos)
      linarith
    have hπ2 : (0:ℝ) < Real.pi / 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hπ2)
    have hpi : (Real.pi / 2) * (2 / Real.pi) = 1 := by field_simp
    have h3 : (Real.pi / 2) * ((2 / Real.pi) * (∑ q ∈ Finset.Icc 1 (Q-1), (1 / (q:ℝ)) * (1 / (2 * nDist ((q:ℝ) * α))))) = (∑ q ∈ Finset.Icc 1 (Q-1), (1 / (q:ℝ)) * (1 / (2 * nDist ((q:ℝ) * α)))) := by
      rw [← mul_assoc, hpi, one_mul]
    rw [h3] at h2
    have h4 : (9/56) * ρ * (2 * (N:ℝ) + 1) ≤ (Real.pi / 2) * ((3/28) * ρ * (2 * (N:ℝ) + 1)) := by
      have hρD : 0 < ρ * (2 * (N:ℝ) + 1) := mul_pos hρ hDpos
      nlinarith [Real.pi_gt_three, hρD]
    linarith
  -- (4) hence the maximal term is at least `(9/448) ρ² (2N+1)`
  have hρ8 : (0:ℝ) ≤ ρ / 8 := by positivity
  have hg0_lb : (9/448) * ρ^2 * (2 * (N:ℝ) + 1) ≤ c0 := by
    have h5 : (ρ / 8) * ((9/56) * ρ * (2 * (N:ℝ) + 1)) = (9/448) * ρ^2 * (2 * (N:ℝ) + 1) := by ring
    have h4 := mul_le_mul_of_nonneg_left hS_lb hρ8
    rw [h5] at h4
    have h6 := mul_le_mul_of_nonneg_left hsum_le2 hρ8
    have h7 : (ρ / 8) * ((8 / ρ) * c0) = c0 := by
      rw [← mul_assoc]
      have : (ρ/8) * (8/ρ) = 1 := by field_simp
      rw [this, one_mul]
    rw [h7] at h6
    linarith
  -- (5) convert the lower bound on `c0` into an upper bound for `‖q₀ α‖`
  have hd_nonneg : 0 ≤ nDist ((q0:ℝ) * α) := nDist_nonneg _
  have h2d_nonneg : (0:ℝ) ≤ 2 * nDist ((q0:ℝ) * α) := by linarith
  have hinv2d_nonneg : (0:ℝ) ≤ 1 / (2 * nDist ((q0:ℝ) * α)) := div_nonneg (by norm_num) h2d_nonneg
  have hq0inv_le : (1:ℝ) / (q0:ℝ) ≤ 1 := by
    have h : (1:ℝ)/(q0:ℝ) ≤ 1/1 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1) hq0lowR
    simpa using h
  have hf_le : c0 ≤ 1 / (2 * nDist ((q0:ℝ) * α)) := by
    have hh : (1 / (q0:ℝ)) * (1 / (2 * nDist ((q0:ℝ) * α))) ≤ 1 * (1 / (2 * nDist ((q0:ℝ) * α))) :=
      mul_le_mul_of_nonneg_right hq0inv_le hinv2d_nonneg
    rw [hc0]
    simpa using hh
  have hBpos : (0:ℝ) < (9/448) * ρ^2 * (2 * (N:ℝ) + 1) := by positivity
  have h2dpos : (0:ℝ) < 2 * nDist ((q0:ℝ) * α) := by
    have hlt : (0:ℝ) < 1 / (2 * nDist ((q0:ℝ) * α)) := lt_of_lt_of_le hBpos (hg0_lb.trans hf_le)
    have hh : (0:ℝ) < (2 * nDist ((q0:ℝ) * α))⁻¹ := by simpa [one_div] using hlt
    have := inv_pos.mp hh
    linarith
  have hmain : ((9/448) * ρ^2 * (2 * (N:ℝ) + 1)) * (2 * nDist ((q0:ℝ) * α)) ≤ 1 := by
    have hle := hg0_lb.trans hf_le
    have := (le_div_iff₀ h2dpos).mp hle
    simpa using this
  have hkey : ρ^2 * (2 * (N:ℝ) + 1) * nDist ((q0:ℝ) * α) ≤ 256 := by
    have h1 : (9/224) * (ρ^2 * (2 * (N:ℝ) + 1) * nDist ((q0:ℝ) * α)) ≤ 1 := by linarith [hmain]
    nlinarith [h1]
  -- (6) assemble
  refine ⟨q0, hq0low, ?_, round ((q0:ℝ) * α), ?_⟩
  · have : (q0:ℝ) ≤ (Q:ℝ) := by exact_mod_cast (by omega : q0 ≤ Q)
    linarith [hQhigh]
  · rw [abs_sub_div_round (β := α) (q := q0) hq0low]
    rw [div_le_div_iff₀ hq0pos (by positivity : (0:ℝ) < ρ^2 * (2 * (N:ℝ) + 1))]
    have h2q : (2:ℝ)^8 * (q0:ℝ) ≥ 256 := by
      have h256 : (2:ℝ)^8 = 256 := by norm_num
      rw [h256]
      nlinarith [hq0lowR]
    have hkey' : nDist ((q0:ℝ) * α) * (ρ ^ 2 * (2 * (N:ℝ) + 1)) ≤ 256 := by linarith [hkey]
    linarith [hkey', h2q]

end Work.KMTAreas.A4
