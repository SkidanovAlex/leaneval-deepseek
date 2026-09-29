import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17I.logP_radius_of_hloc
import Submission.Work.C17I.log_mul_add_not_identically_zero_on_lens
import Submission.Work.C17I.xsOf_ge_eight_ninths

namespace Work.C17I

noncomputable section

open scoped BigOperators Topology

/-- **Sharp coefficient bound for `logP` from the local structure at `x_s`.**

This is the sharp form of `Work.C17I.logP_radius_of_hloc`: the hypothesis `hloc` (a logarithmic
singularity of the analytic function `Pfun` at the cusp `x = xsOf m n`, with non-zero log-coefficient
`κ·y₁`, valid on the lens `ball(x, δ) ∩ ball(0, x)`) not only bounds the coefficients by `C·(6/5)^k`
but lets us *choose* the radius `ρ`: for the point `z₀` of the lens where the series does not
vanish (whose existence is the content of `log_mul_add_not_identically_zero_on_lens`), the terms of
the series tend to `0`, so `‖coeff k‖ · ‖z₀‖^k < 1` for `k ≥ K`, and since `z₀ ∈ ball(0, x)` we have
`ρ := ‖z₀‖ < x`, while `z₀ ∈ ball(x, δ)` gives `ρ > x - δ`.  Because `2δ ≤ 1 - x` and `δ > 0` we
have `x < 1`, hence `1/ρ > 1`, which handles the finitely many indices `k < K`.  So the coefficients
are bounded by `C·(1/ρ)^k` with `x - δ < ρ < x`. -/
theorem logP_coeff_bound_sharp (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) (ra rb rab r0 : ℤ)
    (κ : ℂ) (hκ : κ ≠ 0) (y1 : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : 2 * δ ≤ Work.C17.xsOf m n) (hδ2 : 2 * δ ≤ 1 - Work.C17.xsOf m n)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball ((Work.C17.xsOf m n : ℂ)) δ))
    (hy1ne : y1 ((Work.C17.xsOf m n : ℂ)) ≠ 0)
    (hh : ℂ → ℂ) (hhh : DifferentiableOn ℂ hh (Metric.ball ((Work.C17.xsOf m n : ℂ)) δ))
    (hloc : ∀ z ∈ Metric.ball ((Work.C17.xsOf m n : ℂ)) δ ∩ Metric.ball (0 : ℂ) (Work.C17.xsOf m n),
        Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 z
          = κ * y1 z * Complex.log (((Work.C17.xsOf m n : ℝ) : ℂ) - z) + hh z) :
    ∃ ρ : ℝ, Work.C17.xsOf m n - δ < ρ ∧ ρ < Work.C17.xsOf m n ∧
      ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
        ‖((PowerSeries.coeff k (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) : ℚ) : ℂ)‖
          ≤ C * (1 / ρ) ^ k := by
  -- The cusp `x = xsOf m n` and its basic numerical properties.
  set x : ℝ := Work.C17.xsOf m n with hxdef
  have hx89 : (8 : ℝ) / 9 ≤ x := by
    rw [hxdef]; exact xsOf_ge_eight_ninths m n hm hlt hgap
  have hxpos : 0 < x := by linarith
  -- `2δ ≤ 1 - x` with `δ > 0` forces `x < 1`.
  have hx1 : x < 1 := by linarith
  -- ## Step 1: `Pfun` does not vanish on the whole lens.
  have hnv : ∃ z0, z0 ∈ Metric.ball ((x : ℂ)) δ ∩ Metric.ball (0 : ℂ) x ∧
      Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 z0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine log_mul_add_not_identically_zero_on_lens hxpos hδ y1 hh hy1d hhh hy1ne κ hκ
      (fun z hz => ?_)
    have h1 := hloc z hz
    rw [hcon z hz] at h1
    exact h1.symm
  obtain ⟨z0, hz0mem, hz0ne⟩ := hnv
  have hz0δ : z0 ∈ Metric.ball ((x : ℂ)) δ := hz0mem.1
  have hz0b0 : z0 ∈ Metric.ball (0 : ℂ) x := hz0mem.2
  -- ## Step 2: the series is summable at `z₀`.
  have hsumm : Summable (fun k : ℕ => cofQ m n ra rb rab r0 k * z0 ^ k) := by
    by_contra hns
    refine hz0ne ?_
    rw [Work.C17.Pfun]
    exact tsum_eq_zero_of_not_summable hns
  -- ## Step 3: the sharp radius `ρ = ‖z₀‖` satisfies `x - δ < ρ < x`.
  have hz0lt : ‖z0‖ < x := by
    have h := hz0b0
    rw [Metric.mem_ball, dist_zero_right] at h
    exact h
  have hz0gt : x - δ < ‖z0‖ := by
    have h1 : ‖z0 - ((x : ℂ))‖ < δ := by
      rw [Metric.mem_ball, dist_eq_norm] at hz0δ; exact hz0δ
    have hxnorm : ‖((x : ℝ) : ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hxpos)]
    have h2 : ‖((x : ℝ) : ℂ)‖ - ‖z0 - ((x : ℂ))‖ ≤ ‖z0‖ := by
      have h := norm_sub_le z0 (z0 - ((x : ℂ)))
      have hz : z0 - (z0 - ((x : ℂ))) = ((x : ℂ)) := by ring
      rw [hz] at h
      linarith
    linarith
  have hz0pos : 0 < ‖z0‖ := by
    have h56 : (5 : ℝ) / 6 ≤ x - δ := by nlinarith [hδ2, hx89]
    linarith
  -- `‖z₀‖ < x < 1`, so `1/‖z₀‖ > 1`.
  have hz0le1 : ‖z0‖ ≤ 1 := by linarith
  have hinv1 : (1 : ℝ) ≤ 1 / ‖z0‖ := by
    rw [one_le_div hz0pos]; exact hz0le1
  -- ## Step 4: the terms of the series are eventually `< 1`.
  have htend : Filter.Tendsto (fun k : ℕ => cofQ m n ra rb rab r0 k * z0 ^ k) Filter.atTop (𝓝 0) :=
    hsumm.tendsto_atTop_zero
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (htend.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)))
  have hKb : ∀ k : ℕ, K ≤ k → ‖cofQ m n ra rb rab r0 k‖ * ‖z0‖ ^ k < 1 := by
    intro k hk
    have hmem := hK k hk
    simpa only [dist_zero_right, norm_mul, norm_pow] using hmem
  -- ## Step 5: assemble the constant `C`.
  set C : ℝ := 1 + ∑ k ∈ Finset.range K, ‖cofQ m n ra rb rab r0 k‖ with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCnneg : 0 ≤ C := le_of_lt hCpos
  have hC1 : (1 : ℝ) ≤ C := by
    rw [hCdef]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  refine ⟨‖z0‖, hz0gt, hz0lt, C, hCpos, fun k => ?_⟩
  change ‖cofQ m n ra rb rab r0 k‖ ≤ C * (1 / ‖z0‖) ^ k
  by_cases hk : k < K
  · -- finitely many small indices: `(1/ρ)^k ≥ 1`
    have hle : ‖cofQ m n ra rb rab r0 k‖ ≤ ∑ k ∈ Finset.range K, ‖cofQ m n ra rb rab r0 k‖ :=
      Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hk)
    have h1 : ‖cofQ m n ra rb rab r0 k‖ ≤ C := by rw [hCdef]; linarith
    have h2 : (1 : ℝ) ≤ (1 / ‖z0‖) ^ k := one_le_pow₀ hinv1
    calc ‖cofQ m n ra rb rab r0 k‖ ≤ C := h1
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * (1 / ‖z0‖) ^ k := mul_le_mul_of_nonneg_left h2 hCnneg
  · -- all large indices: `‖coeff‖ < (1/ρ)^k`
    have hkK : K ≤ k := not_lt.mp hk
    have hlt1 := hKb k hkK
    have hzp : 0 < ‖z0‖ ^ k := pow_pos hz0pos k
    have hb : ‖cofQ m n ra rb rab r0 k‖ < 1 / ‖z0‖ ^ k := (lt_div_iff₀ hzp).mpr hlt1
    have hb2 : 1 / ‖z0‖ ^ k = (1 / ‖z0‖) ^ k := by rw [div_pow, one_pow]
    have h4 : (1 / ‖z0‖) ^ k ≤ C * (1 / ‖z0‖) ^ k := by
      calc (1 / ‖z0‖) ^ k = 1 * (1 / ‖z0‖) ^ k := (one_mul _).symm
        _ ≤ C * (1 / ‖z0‖) ^ k := mul_le_mul_of_nonneg_right hC1 (by positivity)
    have h5 : ‖cofQ m n ra rb rab r0 k‖ < (1 / ‖z0‖) ^ k := by
      rw [hb2] at hb
      exact hb
    exact le_trans (le_of_lt h5) h4

end

end Work.C17I
