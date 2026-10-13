/-
# Integrability of the `L₁₂`-density from `ℋ⁴_α` plus a.e. strong measurability

`L12dens F s = ∫_θ K θ · F s θ / s` is the density of the `L₁₂`-functional.  For data
`F ∈ ℋ⁴_α` (i.e. `HkMem α 4 F`: every angular slice of the integrand `HkIntegrand α 4 F` is
integrable on `Iθ`, and its `θ`-integral is integrable in `z` on `Iz`), the Cauchy–Schwarz
factorisation of `cc.abs_L12dens_le` gives the pointwise domination

  `|L12dens F s| ≤ Wlam s · (BK · √(∫_θ HkIntegrand α 4 F s θ))`,   `Wlam s = s/(1+s)²`,

whose majorant is integrable on `(0,∞)`: `Wlam ∈ L²((0,∞))` and
`s ↦ ∫_θ HkIntegrand α 4 F s θ ∈ L¹((0,∞))`, so AM–GM in the radial variable closes.

The only ingredient not supplied by `HkMem` is the a.e. strong measurability of the density
itself — for a datum smooth on the open quadrant it comes from joint continuity of the
integrand (`cc.aesm_L12dens_of_SmoothOpen`); here it is simply an explicit hypothesis, which
is exactly what the consumers of this lemma have at hand.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.GalBasis.cc.integral_abs_L12dens_le
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux3

/-- **The `L₁₂`-density of an `ℋ⁴_α`-datum is integrable on `(0,∞)`**, as soon as it is a.e.
strongly measurable there.

Route.  `HkMem α 4 F` gives `IntegrableOn (fun s => ∫_θ HkIntegrand α 4 F s θ) (Ioi 0)`
(the two sets `Ioi 0` and `Iz = Ici 0` differ by the null set `{0}`), hence, writing
`A s = √(∫_θ HkIntegrand α 4 F s θ)`, also `IntegrableOn (fun s => A s ^ 2) (Ioi 0)`.
Together with `Wlam ∈ L²` (`Work.Elliptic.psi_sq_integrable_aux`), AM–GM
`Wlam s · A s ≤ Wlam s ^ 2 + A s ^ 2` makes `s ↦ BK · (Wlam s · A s)` integrable, and the
pointwise domination `cc.abs_L12dens_le` with the assumed `hmeas` gives the conclusion by
`Integrable.mono'`. -/
theorem integrableOn_L12dens_of_aem {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 F)
    (hmeas : MeasureTheory.AEStronglyMeasurable (Work.Construction.L12dens F)
      (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0) := by
  set H : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 F s θ with hH
  set A : ℝ → ℝ := fun s => Real.sqrt (H s) with hA
  -- the angular marginal `H` is nonnegative and integrable on `(0,∞)`
  have hHnn : ∀ s, 0 ≤ H s :=
    fun s => integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 F s θ
  have hH_int : IntegrableOn H (Set.Ioi 0) :=
    hmem.2.mono_set Set.Ioi_subset_Ici_self
  -- its square root `A` is a.e. strongly measurable, with `A² = H`
  have hA_aesm : AEStronglyMeasurable A (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hH_int.aestronglyMeasurable
  have hA2_int : IntegrableOn (fun s => A s ^ 2) (Set.Ioi 0) :=
    hH_int.congr (Eventually.of_forall fun s => (Real.sq_sqrt (hHnn s)).symm)
  -- the radial weight `Wlam` is square-integrable on `(0,∞)`
  have hWlam_aesm : AEStronglyMeasurable Work.FTS.GalBasis.cc.Wlam
      (volume.restrict (Set.Ioi 0)) := by
    have hc : ContinuousOn (fun s : ℝ => s / (1 + s) ^ 2) (Set.Ioi 0) := by
      refine ContinuousOn.div continuousOn_id ?_ ?_
      · exact (continuousOn_const.add continuousOn_id).pow 2
      · intro s hs
        have h1 : (0 : ℝ) < 1 + s := by linarith [Set.mem_Ioi.mp hs]
        exact pow_ne_zero 2 (ne_of_gt h1)
    exact (show ContinuousOn Work.FTS.GalBasis.cc.Wlam (Set.Ioi 0) from hc).aestronglyMeasurable
      measurableSet_Ioi
  have hWlam2_int : IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s ^ 2) (Set.Ioi 0) := by
    simpa only [Work.FTS.GalBasis.cc.Wlam] using Work.Elliptic.psi_sq_integrable_aux
  -- AM–GM: `Wlam · A` is integrable
  have hWlamA_int : IntegrableOn (fun s => Work.FTS.GalBasis.cc.Wlam s * A s) (Set.Ioi 0) := by
    refine (hWlam2_int.add hA2_int).mono' (hWlam_aesm.mul hA_aesm) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with s hs
    have h1 : 0 ≤ Work.FTS.GalBasis.cc.Wlam s := Work.FTS.GalBasis.cc.Wlam_nonneg hs.le
    have h2 : 0 ≤ A s := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2), Pi.add_apply]
    nlinarith [sq_nonneg (Work.FTS.GalBasis.cc.Wlam s - A s)]
  -- the pointwise domination of the density
  refine (hWlamA_int.const_mul Work.FTS.GalBasis.cc.BK).mono' hmeas ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun s hs => ?_
  have hb := Work.FTS.GalBasis.cc.abs_L12dens_le α F hmem hs
  calc |Work.Construction.L12dens F s|
      ≤ Work.FTS.GalBasis.cc.Wlam s * (Work.FTS.GalBasis.cc.BK * A s) := by
        simpa only [hA, hH] using hb
    _ = Work.FTS.GalBasis.cc.BK * (Work.FTS.GalBasis.cc.Wlam s * A s) := by ring

end Work.FTS.StrongEps.E5Aux3
