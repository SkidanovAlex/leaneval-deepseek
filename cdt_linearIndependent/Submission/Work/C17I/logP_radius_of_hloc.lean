import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17I.xsOf_ge_eight_ninths
import Submission.Work.C17I.log_mul_add_not_identically_zero_on_lens

namespace Work.C17I

noncomputable section

open scoped BigOperators Topology

/-- The `k`-th coefficient of `logP (aOf m) (aOf n) ra rb rab r0`, viewed as a complex number.
This is just an abbreviation for the (long) coefficient expression; it is definitionally equal
to it, so `change` can swap the two forms. -/
def cofQ (m n : ℕ) (ra rb rab r0 : ℤ) (k : ℕ) : ℂ :=
  ((PowerSeries.coeff k (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) : ℚ) : ℂ)

/-- Guidance from the requester (area C17, input for `Work.C17.relation_to_LC`).

# The coefficient bound for `logP` implied by the local structure at `x_s`

`Pfun a b ra rb rab r0 z = ∑' k, coeff_k(logP a b ra rb rab r0) · z^k` is defined as the `tsum`
(Lean's convention: `0` where the series is not summable).  The hypothesis `hloc` says that on the
lens `ball(x_s, δ) ∩ ball(0, x_s)` the function `Pfun` equals `κ · y₁ · log(x_s - ·) + hh` with
`κ ≠ 0`, `y₁, hh` holomorphic on `ball(x_s, δ)` and `y₁ x_s ≠ 0`.

The claim: the coefficients of `logP` are bounded by `C · (6/5)^k` — i.e. the series converges on a
disc that reaches well past `x_s - (1-x_s)/2`.

Reasoning (this is the whole content; it also shows why the hypothesis is not vacuous):
* If the `tsum` vanished at every point of the lens, then `κ y₁ log(x_s - ·) + hh ≡ 0` there, hence
  so is its derivative, and multiplying by `(x_s - z)` and letting `z = x_s - ε → x_s` (those points
  are in the lens for `0 < ε < min δ x_s`) yields `κ y₁ x_s = 0` using `ε · log ε → 0`, contradicting
  `hκ` and `hy1ne`.  (In the formalisation below the same conclusion is reached without
  differentiating, by dividing the vanishing identity by `Complex.log` and letting `ε → 0⁺`:
  the log diverges while `y₁` stays away from `0` and `hh` stays bounded.  This is
  `Work.C17I.log_mul_add_not_identically_zero_on_lens`.)
* So there is `z₀` in the lens with `Pfun z₀ ≠ 0`, i.e. the series is summable at `z₀`; its terms
  therefore tend to `0`, hence are bounded: `‖coeff_k logP‖ · ‖z₀‖^k ≤ M`.
* Finally `‖z₀‖ ≥ x_s - δ ≥ (3 x_s - 1)/2 ≥ 5/6`, because `z₀ ∈ ball(x_s, δ)`, `δ ≤ (1-x_s)/2`
  (from `2δ ≤ 1 - x_s`) and `x_s ≥ 8/9` (from the gap hypothesis, see
  `Work.C17I.xsOf_ge_eight_ninths`). -/
theorem logP_radius_of_hloc (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hlt : m < n)
    (hgap : 10 ^ 6 * ((m : ℤ) - n).natAbs ≤ n) (ra rb rab r0 : ℤ)
    (κ : ℂ) (hκ : κ ≠ 0) (y1 : ℂ → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : 2 * δ ≤ Work.C17.xsOf m n)
    (hδ2 : 2 * δ ≤ 1 - Work.C17.xsOf m n)
    (hy1d : DifferentiableOn ℂ y1 (Metric.ball ((Work.C17.xsOf m n : ℂ)) δ))
    (hy1ne : y1 ((Work.C17.xsOf m n : ℂ)) ≠ 0)
    (hh : ℂ → ℂ) (hhh : DifferentiableOn ℂ hh (Metric.ball ((Work.C17.xsOf m n : ℂ)) δ))
    (hloc : ∀ z ∈ Metric.ball ((Work.C17.xsOf m n : ℂ)) δ ∩ Metric.ball (0 : ℂ) (Work.C17.xsOf m n),
        Work.C17.Pfun (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0 z
          = κ * y1 z * Complex.log (((Work.C17.xsOf m n : ℝ) : ℂ) - z) + hh z) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDT.logP (Work.C17.aOf m) (Work.C17.aOf n) ra rb rab r0) : ℚ) : ℂ)‖
        ≤ C * (6 / 5 : ℝ) ^ k := by
  -- The cusp `x = xsOf m n`, together with the two numerical bounds we will use.
  set x : ℝ := Work.C17.xsOf m n with hxdef
  have hx89 : (8 : ℝ) / 9 ≤ x := by
    rw [hxdef]; exact xsOf_ge_eight_ninths m n hm hlt hgap
  have hxpos : 0 < x := by linarith
  have hxδ : (5 : ℝ) / 6 ≤ x - δ := by nlinarith [hδ2, hx89]
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
  -- ## Step 2: the series is summable at `z₀`.
  have hsumm : Summable (fun k : ℕ => cofQ m n ra rb rab r0 k * z0 ^ k) := by
    by_contra hns
    refine hz0ne ?_
    rw [Work.C17.Pfun]
    exact tsum_eq_zero_of_not_summable hns
  -- ## Step 3: `‖z₀‖ ≥ 5/6`.
  have hz0norm : (5 : ℝ) / 6 ≤ ‖z0‖ := by
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
  -- ## Step 4: the terms of the series are eventually `< 1`.
  have htend : Filter.Tendsto (fun k : ℕ => cofQ m n ra rb rab r0 k * z0 ^ k) Filter.atTop (𝓝 0) :=
    hsumm.tendsto_atTop_zero
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    (htend.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)))
  have hKb : ∀ k : ℕ, K ≤ k → ‖cofQ m n ra rb rab r0 k‖ * ‖z0‖ ^ k < 1 := by
    intro k hk
    have hmem := hK k hk
    simpa only [dist_zero_right, norm_mul, norm_pow] using hmem
  have hz0pos : 0 < ‖z0‖ := lt_of_lt_of_le (by norm_num) hz0norm
  have hinv : (1 : ℝ) / ‖z0‖ ≤ 6 / 5 := by
    rw [div_le_iff₀ hz0pos]; nlinarith [hz0norm]
  -- ## Step 5: assemble the constant `C`.
  set C : ℝ := 1 + ∑ k ∈ Finset.range K, ‖cofQ m n ra rb rab r0 k‖ with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCnneg : 0 ≤ C := le_of_lt hCpos
  refine ⟨C, hCpos, fun k => ?_⟩
  change ‖cofQ m n ra rb rab r0 k‖ ≤ C * (6 / 5 : ℝ) ^ k
  by_cases hk : k < K
  · -- finitely many small indices
    have hle : ‖cofQ m n ra rb rab r0 k‖ ≤ ∑ k ∈ Finset.range K, ‖cofQ m n ra rb rab r0 k‖ :=
      Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hk)
    have h1 : ‖cofQ m n ra rb rab r0 k‖ ≤ C := by rw [hCdef]; linarith
    have h2 : (1 : ℝ) ≤ (6 / 5 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    calc ‖cofQ m n ra rb rab r0 k‖ ≤ C := h1
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * (6 / 5 : ℝ) ^ k := mul_le_mul_of_nonneg_left h2 hCnneg
  · -- all large indices
    have hkK : K ≤ k := not_lt.mp hk
    have hlt1 := hKb k hkK
    have hzp : 0 < ‖z0‖ ^ k := pow_pos hz0pos k
    have hb : ‖cofQ m n ra rb rab r0 k‖ < 1 / ‖z0‖ ^ k := (lt_div_iff₀ hzp).mpr hlt1
    have hb2 : 1 / ‖z0‖ ^ k = (1 / ‖z0‖) ^ k := by rw [div_pow, one_pow]
    have h3 : (1 / ‖z0‖) ^ k ≤ (6 / 5 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hinv k
    have h4 : (6 / 5 : ℝ) ^ k ≤ C * (6 / 5 : ℝ) ^ k := by
      have h5 : (1 : ℝ) ≤ C := by
        rw [hCdef]
        exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg _))
      calc (6 / 5 : ℝ) ^ k = 1 * (6 / 5 : ℝ) ^ k := (one_mul _).symm
        _ ≤ C * (6 / 5 : ℝ) ^ k := mul_le_mul_of_nonneg_right h5 (by positivity)
    have h5 : ‖cofQ m n ra rb rab r0 k‖ < (6 / 5 : ℝ) ^ k := by
      rw [hb2] at hb
      exact lt_of_lt_of_le hb h3
    exact le_trans (le_of_lt h5) h4

end

end Work.C17I
