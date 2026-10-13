import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.Spaces.SinMinBounds
import Submission.Work.FTS.H2.mixed_sin_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the angular slice `(D_z^j D_θ^i f)² · sin(2θ)^{-γ}`

The mixed slot of the `H^k`-norm of the paper carries the singular angular weight
`thGam α θ = sin(2θ)^{-γ}`, `γ = gam α = 1 + α/10 ≥ 1`.  The weight alone is *not*
integrable on `Iθ = [0,π/2]` (it is not even bounded), but the extra vanishing of the
mixed derivative at the two angular endpoints saves the day: for `i ≥ 1` the operator
`D_θ = sin(2θ)∂_θ` carries an explicit factor `sin(2θ)`, so

  `|D_z^j D_θ^i f (z,θ)| ≤ C · sin(2θ)`  for all `θ ∈ Iθ`

(`Work.FTS.H2.mixed_sin_bound`).  Consequently the integrand is dominated by
`C² · sin(2θ)^{2-γ}` with `2 - γ > 0`, which is integrable on `Iθ`
(`Work.FTS.EllipticEst.integrableOn_sin_two_rpow`).  Only the almost-everywhere
measurability needs care, since the integrand is not continuous at the endpoints; it is
continuous on the co-null open interval `(0,π/2)` where `sin(2θ) > 0`.
-/

namespace Work.FTS.EllipticEst.RPFresh

open scoped Real Topology
open MeasureTheory Set Filter

/-- The angular slice `θ ↦ h z θ` of a function which is smooth (in the analytic sense)
on an open neighbourhood of the closed quadrant is continuous on `Iθ`, for every
`z ∈ Iz`. -/
theorem continuousOn_slice_mixed_of_smoothNbhd {h : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothNbhd h) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContinuousOn (fun θ => h z θ) Work.Spaces.Iθ := by
  have h1 : ContinuousOn (Function.uncurry h) Work.Spaces.nbhU := hsm.continuousOn
  have h2 : ContinuousOn (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ :=
    (continuous_const.prodMk continuous_id).continuousOn
  have h3 : Set.MapsTo (fun θ : ℝ => (z, θ)) Work.Spaces.Iθ Work.Spaces.nbhU :=
    fun θ hθ => Work.Spaces.mem_nbhU hz hθ
  have h4 := h1.comp h2 h3
  convert h4 using 1
  ext θ
  rfl

/-- The angular weight `thGam α θ = sin(2θ)^{-γ}` is continuous on the *open* interval
`(0,π/2)`, where `sin(2θ) > 0` and hence the `rpow` branch is the smooth one. -/
theorem continuousOn_thGam_Ioo (α : ℝ) :
    ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thGam α θ) (Set.Ioo 0 (Real.pi / 2)) := by
  change ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
    (Set.Ioo 0 (Real.pi / 2))
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  exact hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.EllipticEst.sin_two_pos hθ)))

/-- The open interval `(0,π/2)` and the closed interval `Iθ` carry the same restriction of
Lebesgue measure, since they differ by the two null points `0` and `π/2`. -/
theorem restrict_Ioo_eq_restrict_Iθ_RPFresh :
    MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict Work.Spaces.Iθ :=
  MeasureTheory.Measure.restrict_congr_set
    (by rw [Work.Spaces.Iθ]; exact MeasureTheory.Ioo_ae_eq_Icc)

/-- On `Iθ`, where `0 ≤ sin(2θ) ≤ 1`, the product `sin(2θ)² · sin(2θ)^{-γ}` collapses to
`sin(2θ)^{2-γ}`. -/
theorem sin_sq_mul_thGam_eq {α : ℝ} (hγ : Work.Spaces.gam α ≠ 2) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thGam α θ
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  have hrew : (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ 2 := Real.rpow_natCast _ 2
  rw [← hrew]
  change (Real.sin (2 * θ)) ^ (2 : ℝ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) = _
  rw [← Real.rpow_add' hs (by intro hc; exact hγ (by linarith))]
  ring_nf

/-- **Integrability of the mixed angular slice.**  For `f` smooth on an open neighbourhood
of the closed quadrant, `0 < α ≤ 1`, `j : ℕ` arbitrary and `i ≥ 1`, the slice
`θ ↦ (D_z^j D_θ^i f)(z,θ)² · sin(2θ)^{-γ}` is integrable on `Iθ`, for every `z ≥ 0`.

The hypothesis `1 ≤ i` is essential: the factor `sin(2θ)` produced by `D_θ` is what makes
the integrand integrable against the weight `sin(2θ)^{-γ}` with `γ ≥ 1`. -/
theorem slice_mixed_integrable {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f) (α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (j i : ℕ) (hi : 1 ≤ i) :
    ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.mixed j i f z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ := by
  intro z hz
  -- the vanishing of the mixed derivative at the angular boundary
  obtain ⟨C, _hC0, hCb⟩ := Work.FTS.H2.mixed_sin_bound f hsm z hz j i hi
  -- `γ = 1 + α/10 ∈ [1, 11/10]`, so `2 - γ > 0`
  have hγ2 : Work.Spaces.gam α < 2 := by
    have hα0 : (0 : ℝ) < α := hα
    rw [Work.Spaces.gam]; linarith [hα0, hα1]
  have hγ : Work.Spaces.gam α ≠ 2 := ne_of_lt hγ2
  have hp : 0 ≤ 2 - Work.Spaces.gam α := by linarith
  -- the dominating integrable function `C² sin(2θ)^{2-γ}`
  have hdom : MeasureTheory.IntegrableOn
      (fun θ : ℝ => C ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    (Work.FTS.EllipticEst.integrableOn_sin_two_rpow hp).1.const_mul (C ^ 2)
  -- continuity on the open interval, hence a.e. strong measurability
  have hcont1 : ContinuousOn (fun θ => (Work.Spaces.mixed j i f z θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (((continuousOn_slice_mixed_of_smoothNbhd (Work.Spaces.smoothNbhd_mixed hsm j i) hz).mono
      (Set.Ioo_subset_Icc_self)).pow 2)
  have hcont : ContinuousOn
      (fun θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    hcont1.mul (continuousOn_thGam_Ioo α)
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [← restrict_Ioo_eq_restrict_Iθ_RPFresh]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  -- `|mixed| ≤ C sin(2θ)`, so `mixed² ≤ C² sin(2θ)²`
  have hmix : (Work.Spaces.mixed j i f z θ) ^ 2 ≤ C ^ 2 * (Real.sin (2 * θ)) ^ 2 := by
    have h1 : |Work.Spaces.mixed j i f z θ| ≤ C * Real.sin (2 * θ) := hCb θ hθ
    calc (Work.Spaces.mixed j i f z θ) ^ 2 = |Work.Spaces.mixed j i f z θ| ^ 2 := by
          rw [sq_abs]
      _ ≤ (C * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = C ^ 2 * (Real.sin (2 * θ)) ^ 2 := by ring
  have hσ : 0 ≤ Work.FTS.EllipticEst.thGam α θ := Work.FTS.EllipticEst.thGam_nonneg hθ
  have hnn : 0 ≤ (Work.Spaces.mixed j i f z θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ :=
    mul_nonneg (sq_nonneg _) hσ
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc (Work.Spaces.mixed j i f z θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
      ≤ (C ^ 2 * (Real.sin (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thGam α θ :=
        mul_le_mul_of_nonneg_right hmix hσ
    _ = C ^ 2 * ((Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thGam α θ) := by ring
    _ = C ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
        rw [sin_sq_mul_thGam_eq hγ hθ]

end Work.FTS.EllipticEst.RPFresh
