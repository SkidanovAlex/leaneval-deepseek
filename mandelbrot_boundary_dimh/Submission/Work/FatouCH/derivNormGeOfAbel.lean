import Mathlib
import Submission.Work.FatouCH.twoSidedAux
import Submission.Unif.Commons.Analysis.Complex.Koebe.growth_bound

namespace Work.FatouCH

/-- **Lower bound half of the two-sided Koebe estimate** (Shishikura Lemma A.2.4(i), first step).
`ρ > 0` is a Koebe-type constant for the unit disc: every `f` holomorphic and injective on `ball 0 1`
with `f 0 = 0`, `deriv f 0 = 1` omits no value of modulus `< ρ`.  For `Φ` holomorphic and injective
on `ball z₀ R` and `v` a near-translation (`‖v z - 1‖ < 1/4`) satisfying the Abel relation
`Φ (z + v z) = Φ z + 1` whenever both points lie in `ball z₀ R`, we have
`1 / (2 * ((13/3) ^ (1/ρ) - 1)) ≤ ‖deriv Φ z‖` on `ball z₀ (R - 2)`.

Suggested route: add `import Submission.Unif.Commons.Analysis.Complex.Koebe.growth_bound` and apply
`Commons.Analysis.Complex.Koebe.growth_bound` with `c = ρ` to
`G u = (Φ (z + 2u) - Φ z) / (2 * deriv Φ z)` (`normedTransform Φ z 2`), which is analytic and
injective on the unit disc with `G 0 = 0`, `deriv G 0 = 1` (tools in
`Submission.Work.FatouCH.twoSidedAux`, plus `deriv_ne_zero_of_differentiableOn_injOn_ball`).  The
growth bound gives `‖G u‖ + 1 ≤ ((1 + ‖u‖)/(1 - ‖u‖)) ^ (1/ρ)`; at `u = v z / 2` one has
`G u = 1/(2 * deriv Φ z)` by the Abel relation, and `‖u‖ < 5/8` (`norm_div_two_lt_five_eighths`), so
`((1 + ‖u‖)/(1 - ‖u‖)) ^ (1/ρ) ≤ (13/3) ^ (1/ρ)` (`rpow_one_add_div_one_sub_le`); since
`deriv Φ z ≠ 0` this rearranges to the claimed bound. -/
theorem derivNormGeOfAbel {ρ : ℝ} (hρ : 0 < ρ)
    (hkoebe : ∀ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ f z) →
      Set.InjOn f (Metric.ball (0 : ℂ) 1) → f 0 = 0 → deriv f 0 = 1 →
      ∀ w : ℂ, w ∉ f '' (Metric.ball (0 : ℂ) 1) → ρ ≤ ‖w‖)
    (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ)
    (hΦ : DifferentiableOn ℂ Φ (Metric.ball z₀ R)) (hinj : Set.InjOn Φ (Metric.ball z₀ R))
    (hv : DifferentiableOn ℂ v (Metric.ball z₀ R))
    (hnear : ∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4)
    (habel : ∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ (z + v z) = Φ z + 1) :
    ∀ z ∈ Metric.ball z₀ (R - 2), 1 / (2 * ((13 / 3) ^ (1 / ρ) - 1)) ≤ ‖deriv Φ z‖ := by
  intro z hz
  have _hv := hv -- differentiability of `v` is not needed for this half of the estimate
  -- the point `z` lies in the larger ball and `Φ' z ≠ 0` by injectivity
  have hzR : z ∈ Metric.ball z₀ R := Metric.ball_subset_ball (by linarith : R - 2 ≤ R) hz
  have hd : deriv Φ z ≠ 0 :=
    deriv_ne_zero_of_differentiableOn_injOn_ball hΦ hinj hzR
  have hs2 : ‖(2 : ℂ)‖ ≤ 2 := by norm_num
  have hsne : (2 : ℂ) ≠ 0 := by norm_num
  -- the normalised rescaling, univalent on the unit disc with `0 ↦ 0`, derivative `1` at `0`
  set G : ℂ → ℂ := normedTransform Φ z 2 with hGdef
  have hGana : ∀ u ∈ Metric.ball (0 : ℂ) 1, AnalyticAt ℂ G u := by
    intro u hu
    rw [hGdef]
    exact normedTransform_analyticAt hΦ hz hs2 u hu
  have hGinj : Set.InjOn G (Metric.ball (0 : ℂ) 1) := by
    rw [hGdef]
    exact normedTransform_injOn hinj hz hs2 hsne hd
  have hG0 : G 0 = 0 := by rw [hGdef]; exact normedTransform_zero Φ z 2
  have hG1 : deriv G 0 = 1 := by
    rw [hGdef]
    exact normedTransform_deriv_zero hΦ hzR (mul_ne_zero hsne hd)
  -- the growth bound for `G`
  have hgrowth := Commons.Analysis.Complex.Koebe.growth_bound hρ hkoebe hGana hGinj hG0 hG1
  -- evaluate at `u = v z / 2`, which lies well inside the unit disc
  have hnearz : ‖v z - 1‖ < 1 / 4 := hnear z hzR
  have htz : ‖v z / 2‖ < 5 / 8 := norm_div_two_lt_five_eighths hnearz
  have humem : v z / 2 ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; linarith
  have hgu := hgrowth (v z / 2) humem
  have hvz_norm : ‖v z‖ < 2 := by
    have h1 : ‖v z‖ ≤ ‖v z - 1‖ + ‖(1 : ℂ)‖ := by
      calc ‖v z‖ = ‖(v z - 1) + 1‖ := by ring_nf
        _ ≤ ‖v z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at h1
    linarith
  have hvzmem : z + v z ∈ Metric.ball z₀ R := add_mem_ball_of_norm_lt hz hvz_norm
  have habelz : Φ (z + v z) = Φ z + 1 := habel z hzR hvzmem
  have hGval : G (v z / 2) = 1 / (2 * deriv Φ z) := by
    rw [hGdef, normedTransform_apply]
    have h2 : (2 : ℂ) * (v z / 2) = v z := by ring
    rw [h2, habelz, add_sub_cancel_left]
  rw [hGval] at hgu
  -- simplify the modulus of the value and compare the growth expression with its bound
  set D : ℝ := ‖deriv Φ z‖ with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact norm_pos_iff.mpr hd
  have hnorm : ‖(1 : ℂ) / (2 * deriv Φ z)‖ = 1 / (2 * D) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
  rw [hnorm] at hgu
  set L : ℝ := (13 / 3 : ℝ) ^ (1 / ρ) with hLdef
  have hLgt : 1 < L := by
    rw [hLdef]; exact Real.one_lt_rpow (by norm_num) (by positivity)
  have hmono : ((1 + ‖v z / 2‖) / (1 - ‖v z / 2‖)) ^ (1 / ρ) ≤ L := by
    rw [hLdef]
    exact rpow_one_add_div_one_sub_le hρ (norm_nonneg _) (le_of_lt htz)
  have hLb : 1 / (2 * D) + 1 ≤ L := le_trans hgu hmono
  -- rearrange `1/(2D) + 1 ≤ L` into `1/(2(L-1)) ≤ D`
  have hDge : 1 / (2 * (L - 1)) ≤ D := by
    have h1 : 1 / (2 * D) ≤ L - 1 := by linarith
    have h2 : 1 ≤ D * (2 * (L - 1)) := by
      have h3 := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * D)).mp h1
      nlinarith [h3]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (L - 1))]
    exact h2
  simpa [hDdef, hLdef] using hDge

end Work.FatouCH
