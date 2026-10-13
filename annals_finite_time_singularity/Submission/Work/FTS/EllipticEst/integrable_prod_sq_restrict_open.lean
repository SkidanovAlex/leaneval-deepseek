/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of a single weighted `D_z`-slot on a half-open interval of the radial axis

For `F` smooth on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen F`) and `F ∈ ℋ^k`
(`Work.Spaces.HkMem α k F`), and for every `i ≤ k`, the *uncurried* squared weighted summand
`(r,θ) ↦ (D_z^i F r θ · w(r)/sin(2θ)^{η/2})²` is integrable for the product measure
`(volume|_{(a,b]}) × (volume|_{Iθ})`, for every `a ≥ 0` and every `b`.

The point of the lemma is the endpoint `a = 0`: `Ioc 0 b = (0,b]` contains the points
`r → 0⁺` at which the radial weight `w(r) = (1+r)²/r²` blows up, and the lemma still holds
because the `ℋ^k`-membership is exactly what controls it.  The angular slice is integrable at
every `r ∈ Iz` (`Work.FTS.EllipticEst.integrableOn_zSummand`) and the iterated integral is
dominated on `Iz` by `z ↦ ∫_θ HkIntegrand α k F z θ`, which is integrable in `z` by
hypothesis; so the singularity at `r = 0` never has to be stripped, and `Ioc a b ⊆ Iz`
transfers the result to the requested measure.

PROOF.  `Work.Spaces.integrable_prod_of_iterated` (Tonelli for a nonnegative function)
applied to `μ = volume|(a,b]`, `ν = volume|Iθ`.  The four inputs are:

* nonnegativity: a square;
* a.e. strong measurability: the summand is continuous on the open quadrant, which exhausts
  the closed quadrant up to null sets (`Work.Spaces.aesm_of_continuousOn_Qd`); the measure on
  the box is the restriction of the measure on `Iz ×ˢ Iθ` (`Measure.prod_restrict` plus
  monotonicity of `Measure.restrict`), so `AEStronglyMeasurable.mono_measure` descends it;
* the angular slices: `Work.FTS.EllipticEst.integrableOn_zSummand` at every `r ∈ (a,b]`;
* the iterated integral: `integrableOn_slice_Iz` below.  This is the argument of
  `Work.FTS.EllipticEst.integrableOn_slice_l2`, which yields integrability on `Icc a b`
  only for `a > 0`; here it is run once on the whole half-line `Iz`, from which both cases
  `a = 0` and `a > 0` follow by monotonicity of the restricted measure.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.integrable_prod_of_iterated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 800000

/-- On the whole half-line `Iz` the iterated angular integral of a single weighted `D_z`-slot
of an `ℋ^k`-function is integrable: it is measurable by Fubini for Bochner integrals
(`AEStronglyMeasurable.integral_prod_right'`, the joint integrand being a.e. strongly
measurable by continuity on the open quadrant) and pointwise dominated by the iterated
integral of `HkIntegrand`, which is integrable by `hmem.2` (`sq_le_HkIntegrand_z`). -/
theorem integrableOn_slice_Iz (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (i : ℕ) (hi : i ≤ k) :
    MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter i F s θ * (Work.Spaces.w s
        / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Work.Spaces.Iz := by
  -- a.e. strong measurability of the uncurried squared summand for `(dz)|_{Iz} × (dθ)|_{Iθ}`
  have hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i F p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_summand i)).pow 2
  -- Fubini for Bochner integrals: integrate out `θ` to get measurability in `s`
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i F s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hjoint.integral_prod_right'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa only using h
  -- domination by the iterated integral of the full `ℋ^k`-integrand
  refine hmem.2.mono' haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict
    (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with s hs
  rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
  exact MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => sq_nonneg _)
    (hmem.1 s hs)
    (MeasureTheory.ae_restrict_of_forall_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ _ => Work.Spaces.sq_le_HkIntegrand_z α k F s θ i hi))

theorem integrable_prod_sq_restrict_open (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (i : ℕ) (hi : i ≤ k) {a b : ℝ} (ha : 0 ≤ a) :
    MeasureTheory.Integrable
      (Function.uncurry (fun r θ : ℝ => (Work.Spaces.DzIter i F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- `Ioc a b ⊆ Iz` because `a ≥ 0`.
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iz := fun r hr =>
    Set.mem_Ici.mpr (le_of_lt (lt_of_le_of_lt ha hr.1))
  have hbox : Set.Ioc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ :=
    Set.prod_mono hsub subset_rfl
  -- The measure on the box is the restriction of the measure on the closed quadrant.
  have hmono : (MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      ≤ (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_mono hbox le_rfl
  -- a.e. strong measurability on the box, by monotonicity of the restricted measure.
  have hAE : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun r θ : ℝ => (Work.Spaces.DzIter i F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    ((Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_summand i)).pow 2).mono_measure
      hmono
  -- The angular slices are integrable at every `r ∈ (a,b]`.
  have hslice : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
      MeasureTheory.Integrable (fun θ : ℝ => (Work.Spaces.DzIter i F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with r hr
    exact integrableOn_zSummand α k hF hmem i hi (hsub hr)
  -- The iterated integral is integrable on `(a,b]` by the half-line version.
  have houter : MeasureTheory.Integrable
      (fun r : ℝ => ∫ θ, (Work.Spaces.DzIter i F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (integrableOn_slice_Iz α k hF hmem i hi).mono_set hsub
  exact (Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun r θ : ℝ => (Work.Spaces.DzIter i F r θ
      * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun r θ => sq_nonneg _) hAE hslice houter).1

end Work.FTS.EllipticEst
