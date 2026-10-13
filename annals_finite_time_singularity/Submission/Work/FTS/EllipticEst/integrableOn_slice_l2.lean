/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the weighted `L²`-slice of an `ℋ^k` function on a compact interval

For `F` smooth on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`) and `F ∈ ℋ^k`
(`Work.Spaces.HkMem α k F`), and for every `i ≤ k`, the angular `L²`-slice

  `s ↦ ∫_θ (D_z^i F s θ · w(s) / sin(2θ)^{η/2})²`

is integrable on every compact interval `[a,b]` with `0 < a`.  In fact the proof
establishes the stronger statement that it is integrable on all of `Iz = [0,∞)`.

This is the "finite" ingredient of the `L²`-theory of the elliptic estimates: it turns
the pointwise domination of a single weighted `D_z`-summand by the full `ℋ^k`-integrand
(`Work.Spaces.sq_le_HkIntegrand_z`) into an honest integrability statement on the
`s`-line.  The two halves are

* measurability: the uncurried squared summand is continuous on the open quadrant, the
  product `(dz)|_{Iz} × (dθ)|_{Iθ}` differs from the planar Lebesgue measure on the
  closed quadrant by a null set (`Work.Spaces.aesm_of_continuousOn_Qd`), and Fubini for
  Bochner integrals (`AEStronglyMeasurable.integral_prod_right'`) integrates out `θ`;
* domination: the `θ`-integral of the squared summand is pointwise bounded by the
  `θ`-integral of `HkIntegrand α k F`, which is integrable in `z` by hypothesis.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter
open scoped Real Topology

theorem integrableOn_slice_l2 (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (i : ℕ) (hi : i ≤ k) :
    ∀ a b : ℝ, 0 < a → a < b → MeasureTheory.IntegrableOn (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter i F s θ * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (Set.Icc a b) := by
  intro a b ha hab
  -- The uncurried squared summand is a.e. strongly measurable for the product measure
  -- `(dz)|_{Iz} × (dθ)|_{Iθ}`: it is continuous on the open quadrant, which exhausts the
  -- closed quadrant up to a null set.
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.DzIter i F p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ (hF.continuousOn_summand i)).pow 2
  -- Integrating out `θ` (Fubini for Bochner integrals) gives the measurability of the
  -- angular `L²`-slice in `s`.
  have haesm : AEStronglyMeasurable
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i F s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := hjoint.integral_prod_right'
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    simpa only using h
  -- Domination: the `θ`-integral of the squared summand is pointwise bounded by the
  -- `θ`-integral of the full `ℋ^k`-integrand, which is integrable in `z` by hypothesis.
  have hInt : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter i F s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz := by
    refine hmem.2.mono' haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (show MeasurableSet Work.Spaces.Iz from measurableSet_Ici)] with s hs
    rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)]
    exact MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
      (hmem.1 s hs)
      (MeasureTheory.ae_restrict_of_forall_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
        fun θ _ => Work.Spaces.sq_le_HkIntegrand_z α k F s θ i hi)
  -- `[a,b] ⊆ Iz` because `0 < a`.
  exact hInt.mono_set fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)

end Work.FTS.EllipticEst
