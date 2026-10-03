import Mathlib
import Submission.Work.FatouCH.twoSidedAux

namespace Work.FatouCH

open Metric Set Complex
open scoped Topology

/-- **Upper bound half of the two-sided Koebe estimate** (Shishikura Lemma A.2.4(i), first step).
`ρ > 0` is a Koebe-type constant for the unit disc: every `f` holomorphic and injective on `ball 0 1`
with `f 0 = 0`, `deriv f 0 = 1` omits no value of modulus `< ρ`.  For `Φ` holomorphic and injective
on `ball z₀ R` and `v` a near-translation (`‖v z - 1‖ < 1/4`) satisfying the Abel relation
`Φ (z + v z) = Φ z + 1` whenever both points lie in `ball z₀ R`, we have `‖deriv Φ z‖ ≤ 4 / (3 * ρ)`
on `ball z₀ (R - 2)`.

Suggested route (all tools in `Submission.Work.FatouCH.twoSidedAux`): normalise
`G u = (Φ (z + (3/4)u) - Φ z) / ((3/4) * deriv Φ z)` (`normedTransform Φ z (3/4)`), analytic and
injective on the unit disc with `G 0 = 0`, `deriv G 0 = 1`; use `deriv_ne_zero_of_differentiableOn_injOn_ball`
for `deriv Φ z ≠ 0`.  If `4/(3ρ) < ‖deriv Φ z‖` then `w₀ = 1/((3/4) * deriv Φ z)` has modulus `< ρ`,
so by `hkoebe` `w₀ = G u` for some `‖u‖ < 1`, giving `Φ (z + (3/4)u) = Φ z + 1 = Φ (z + v z)`
(`habel`; `z + v z ∈ ball z₀ R` since `‖v z‖ < 5/4`, `add_mem_ball_of_norm_lt`); injectivity forces
`(3/4)u = v z`, so `‖v z‖ < 3/4`, contradicting `norm_gt_three_quarters_of_norm_sub_one_lt`. -/
theorem derivNormLeOfAbel {ρ : ℝ} (hρ : 0 < ρ)
    (hkoebe : ∀ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
      Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
      ∀ w : ℂ, w ∉ f '' (Metric.ball (0 : ℂ) 1) → ρ ≤ ‖w‖)
    (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ)
    (hΦ : DifferentiableOn ℂ Φ (Metric.ball z₀ R)) (hinj : Set.InjOn Φ (Metric.ball z₀ R))
    (hv : DifferentiableOn ℂ v (Metric.ball z₀ R))
    (hnear : ∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4)
    (habel : ∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ (z + v z) = Φ z + 1) :
    ∀ z ∈ Metric.ball z₀ (R - 2), ‖deriv Φ z‖ ≤ 4 / (3 * ρ) := by
  intro z hz
  -- `z` lies in the larger ball on which `Φ` is holomorphic and injective.
  have hzR : z ∈ Metric.ball z₀ R := by
    rw [Metric.mem_ball] at hz ⊢
    linarith
  have hd : deriv Φ z ≠ 0 := deriv_ne_zero_of_differentiableOn_injOn_ball hΦ hinj hzR
  -- The normalisation `G` has all the hypotheses that `hkoebe` needs.
  have hs_norm : ‖((3 / 4 : ℂ))‖ ≤ 2 := by norm_num
  have hs_ne : ((3 / 4 : ℂ)) ≠ 0 := by norm_num
  have hne : (3 / 4 : ℂ) * deriv Φ z ≠ 0 := mul_ne_zero hs_ne hd
  have han : ∀ u ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ (normedTransform Φ z (3 / 4)) u :=
    normedTransform_analyticAt hΦ hz hs_norm
  have hinj' : Set.InjOn (normedTransform Φ z (3 / 4)) (Metric.ball (0 : ℂ) 1) :=
    normedTransform_injOn hinj hz hs_norm hs_ne hd
  have h0 : normedTransform Φ z (3 / 4) 0 = 0 := normedTransform_zero Φ z (3 / 4)
  have hd1 : deriv (normedTransform Φ z (3 / 4)) 0 = 1 :=
    normedTransform_deriv_zero hΦ hzR hne
  by_contra hcon
  rw [not_le] at hcon
  -- The modulus of the candidate omitted value.
  have h34 : ‖((3 / 4 : ℂ))‖ = 3 / 4 := by norm_num
  have hnorm_w₀ : ‖(1 : ℂ) / ((3 / 4 : ℂ) * deriv Φ z)‖ = 4 / (3 * ‖deriv Φ z‖) := by
    rw [norm_div, norm_one, norm_mul, h34]
    field_simp
  -- It is `< ρ`, hence cannot be omitted.
  have hw₀_lt : ‖(1 : ℂ) / ((3 / 4 : ℂ) * deriv Φ z)‖ < ρ := by
    rw [hnorm_w₀]
    have hDpos : (0 : ℝ) < ‖deriv Φ z‖ := by
      have : 0 < 4 / (3 * ρ) := by positivity
      linarith
    have h1 : 4 < 3 * ρ * ‖deriv Φ z‖ := by
      have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 3 * ρ)).mp hcon
      linarith
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 3 * ‖deriv Φ z‖)]
    nlinarith
  have hw₀_mem : (1 : ℂ) / ((3 / 4 : ℂ) * deriv Φ z)
      ∈ normedTransform Φ z (3 / 4) '' Metric.ball (0 : ℂ) 1 := by
    by_contra hnot
    have hle := hkoebe (normedTransform Φ z (3 / 4)) han hinj' h0 hd1 _ hnot
    linarith
  obtain ⟨u, hu, hGu⟩ := hw₀_mem
  have hu1 : ‖u‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hu
  -- Both `z + (3/4)u` and `z + v z` lie in `ball z₀ R`.
  have hzsu : z + (3 / 4 : ℂ) * u ∈ Metric.ball z₀ R :=
    add_mul_mem_ball_of_norm_le hz hs_norm hu1
  have hvz_mem : z + v z ∈ Metric.ball z₀ R := by
    refine add_mem_ball_of_norm_lt (c := 2) hz ?_
    have h1 : ‖v z‖ ≤ ‖v z - 1‖ + ‖(1 : ℂ)‖ := by
      calc ‖v z‖ = ‖(v z - 1) + 1‖ := by ring_nf
        _ ≤ ‖v z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at h1
    have := hnear z hzR
    linarith
  -- The Abel relation together with `G u = w₀` forces `Φ (z + (3/4)u) = Φ z + 1`.
  have hPhi_u : Φ (z + (3 / 4 : ℂ) * u) = Φ z + 1 := by
    have h1 : (Φ (z + (3 / 4 : ℂ) * u) - Φ z) / ((3 / 4 : ℂ) * deriv Φ z)
        = 1 / ((3 / 4 : ℂ) * deriv Φ z) := by
      simpa [normedTransform] using hGu
    have h2 : Φ (z + (3 / 4 : ℂ) * u) - Φ z = 1 := by
      have h := congrArg (fun y : ℂ => y * ((3 / 4 : ℂ) * deriv Φ z)) h1
      rwa [div_mul_cancel₀ _ hne, div_mul_cancel₀ _ hne] at h
    rw [sub_eq_iff_eq_add] at h2
    simpa [add_comm] using h2
  -- Injectivity pins down `(3/4)u = v z`, contradicting `‖v z‖ > 3/4`.
  have hEq : z + (3 / 4 : ℂ) * u = z + v z := by
    refine hinj hzsu hvz_mem ?_
    rw [hPhi_u, habel z hzR hvz_mem]
  have hsu : (3 / 4 : ℂ) * u = v z := add_left_cancel hEq
  have hlt : ‖v z‖ < 3 / 4 := by
    calc ‖v z‖ = ‖(3 / 4 : ℂ) * u‖ := by rw [← hsu]
      _ = ‖(3 / 4 : ℂ)‖ * ‖u‖ := norm_mul _ _
      _ = 3 / 4 * ‖u‖ := by rw [h34]
      _ < 3 / 4 := by nlinarith
  have hgt : 3 / 4 < ‖v z‖ := norm_gt_three_quarters_of_norm_sub_one_lt (hnear z hzR)
  linarith

end Work.FatouCH
