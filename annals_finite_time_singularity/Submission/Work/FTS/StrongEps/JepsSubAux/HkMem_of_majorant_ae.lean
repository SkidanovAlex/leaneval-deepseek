import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.JepsHkMem.AuxMeas
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.JepsSubAux

set_option autoImplicit false

/-- `ℋ^k`-membership by an a.e. domination, with the measurability of the integrand supplied by
continuity on the open quadrant `Quad = (0,∞) × (0,π/2)` (which is conull for the product of the
two restricted measures).  This is `Work.FTS.LocData.HkMem_of_majorant` with the *everywhere*
pointwise domination weakened to an a.e. one; the continuity hypothesis is what supplies both the
slicewise and the joint a.e. strong measurability of the integrand.

Declare it in namespace `Work.FTS.StrongEps.JepsSubAux` (full name
`Work.FTS.StrongEps.JepsSubAux.HkMem_of_majorant_ae`).

Route: (i) at `z = 0` the integrand vanishes identically (`Work.Spaces.w 0 = 0`, resp. the mixed
slots carry `Work.Spaces.Wt α 0 θ = 0`), so the slice is integrable outright (there is a ready-made
`Work.FTS.LocData.HkIntegrand_zero_fst`);
(ii) for `z > 0` the slice `θ ↦ HkIntegrand α k h z θ` is continuous on `Ioo 0 (π/2)` (compose
`hcont` with `θ ↦ (z,θ)`), hence a.e. strongly measurable for `volume.restrict Iθ` — use
`Work.FTS.StrongEps.JepsHkMem.restrict_Iθ_eq` to replace the closed interval by the open one —
and `Integrable.mono'` against the slice of `M` closes it;
(iii) the joint function is a.e. strongly measurable for
`(volume.restrict Iz).prod (volume.restrict Iθ)` by `hcont` and the conull-ness of `Quad`
(`Work.FTS.StrongEps.JepsHkMem.ae_mem_Quad_prod`), so Fubini's measurability
(`AEStronglyMeasurable.integral_prod_right'`) gives the a.e. strong measurability of the
slice-integral, and `Integrable.mono'` against `z ↦ ∫_θ M z θ` (using `integral_mono_of_nonneg`
slicewise) closes the second conjunct. -/
theorem HkMem_of_majorant_ae (α : ℝ) (k : ℕ) {h M : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k h q.1 q.2)
      Work.FTS.StrongEps.Quad)
    (hMslice : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => M z θ) Work.Spaces.Iθ)
    (hMz : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, M z θ) Work.Spaces.Iz)
    (hle : ∀ z ∈ Work.Spaces.Iz,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α k h z θ ≤ M z θ) :
    Work.Spaces.HkMem α k h := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2) :=
    MeasureTheory.Ioo_ae_eq_Icc
  constructor
  · -- Step 1: the `θ`-slices of the integrand are integrable on `Iθ`.
    intro z hz
    show IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k h z θ) (Set.Icc 0 (π / 2))
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · -- `z = 0`: the integrand vanishes identically
      subst h0
      refine IntegrableOn.congr_fun integrableOn_zero (fun θ _ => ?_) measurableSet_Icc
      exact (Work.FTS.LocData.HkIntegrand_zero_fst α k h θ).symm
    · -- `z > 0`: continuity of the slice on the open interval, then `mono'` against `M`
      have haesm : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.HkIntegrand α k h z θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        rw [Work.FTS.StrongEps.JepsHkMem.restrict_Iθ_eq]
        exact (Work.FTS.LocData.continuousOn_slice_theta
          (G := Work.Spaces.HkIntegrand α k h) hcont hz0
            ).aestronglyMeasurable measurableSet_Ioo
      refine MeasureTheory.Integrable.mono' (hMslice z hz) haesm ?_
      filter_upwards [hle z hz] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k h z θ)]
      exact hθ
  · -- Step 2: the `z`-integral of the slices is integrable on `Iz`.
    have hprod : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k h p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [Work.FTS.StrongEps.JepsHkMem.restrict_Iz_eq,
        Work.FTS.StrongEps.JepsHkMem.restrict_Iθ_eq,
        MeasureTheory.Measure.prod_restrict,
        ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
      exact hcont.aestronglyMeasurable
        (Work.FTS.StrongEps.isOpen_Quad.measurableSet)
    have h1 : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hprod.integral_prod_right'
    refine MeasureTheory.Integrable.mono' hMz h1 ?_
    filter_upwards [ae_restrict_mem (s := Work.Spaces.Iz) measurableSet_Ici] with z hz
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k h z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k h z θ))
      (hMslice z hz) (hle z hz)

end Work.FTS.StrongEps.JepsSubAux
