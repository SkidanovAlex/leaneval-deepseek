import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.ClassC.VopGen.Gate
import Submission.Work.FTS.ClassC.VopGen.CoreSplit
import Submission.Work.FTS.EllipticEst.Prop.mixedSlotInterpEta
import Submission.Work.FTS.EllipticEst.Prop.aslotTwoShift
import Submission.Work.FTS.ClassC.VopGen.hkMem_pth2_Dz_AofGen
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoBnds
import Submission.Work.FTS.EllipticEst.remov.bPairDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassC.VopGen.muSliceAgmonPointwise
import Submission.Work.FTS.ClassC.VopGen.HkMem_zero_slice_mu

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.ClassC.VopGen.sliceAgmonAofGen` — the a.e.-slicewise Agmon inequality for
`f = D_z (z²∂_z²Ψ)`

This module proves the "slice half" `SliceAgmonStmt` of the level-`2` core inequality
(`VopGen/CoreSplit.lean`): for every datum of the weak class `TT.EllWeakPos α 2 F Ψ` with
`0 < α ≤ 1/4`, for almost every `z > 0`,

  `∫_θ (∂_θ D_zA)² σ ≤ -∫_θ D_zA · ∂_θ²(D_zA) · σ`,   `σ = sin(2θ)^{2-γ(α)}`, `A = z²∂_z²Ψ`.

## The reduction

The `z`-variable is *parametrised away*: for each `z > 0` the angular slice
`f := θ ↦ D_zA(z,θ)` satisfies the pointwise Agmon inequality
`Work.FTS.ClassC.VopGen.muSliceAgmonPointwise`, whose three hypotheses are

* `ContDiffOn ℝ 2 f (Ioo 0 (π/2))` — the slice of the `C^∞`-function `D_zA` on the open quadrant
  (`SmoothOpen.curry_θ`);
* the two vanishing endpoint traces of `f` — a.e. `z`, this is
  `Prop.aof_tendsto_zero` (`D_zA = z ∂_z A`);
* the `σ`-weighted integrability of the second derivative `∂_θ²(D_zA)` — this is the
  `ℋ⁰`-honesty `VopGen.hkMem_pth2_Dz_AofGen` (the `∂_θ²`-slot of the level-`2` weak class)
  together with the weight transfer `VopGen.HkMem_zero_slice_mu`, which converts the level-`0`
  integrand `(∂_θ²(D_zA))² w² sin(2θ)^{-η}` of `ℋ⁰` into the slicewise
  `(∂_θ²(D_zA))² sin(2θ)^{2-γ}`.

The `∀ᵐ z` of the statement is taken with respect to `volume.restrict Iz` (`Iz = [0,∞)`); the
statement is proved a.e. on `Ioi 0` (where the traces live) and transported along the a.e.
equality `Ioi 0 =ᵐ Ici 0`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.ClassC.VopGen

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The a.e.-slicewise angular Agmon inequality** for `f = D_z(z²∂_z²Ψ)`. -/
theorem sliceAgmonAofGen : Work.FTS.ClassC.VopGen.SliceAgmonStmt := by
  intro α F Ψ hα hα4 h
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hA : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.H2W.Aof Ψ) :=
    Work.FTS.EllipticEst.Prop.aofSmoothOpen hΨ
  have hg : Work.Spaces.HkMem α 0
      (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ))) :=
    Work.FTS.ClassC.VopGen.hkMem_pth2_Dz_AofGen h
  have hsmg : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ))) :=
    (hA.Dz).pth.pth
  have htr := Work.FTS.EllipticEst.Prop.aof_tendsto_zero hα hα4 h
  -- the slicewise inequality, a.e. on `Ioi 0`
  have key : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ)) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ -(∫ θ in Work.Spaces.Iθ,
            Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ
              * (Work.Spaces.pthIter 2 (Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ))) z θ
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) := by
    filter_upwards [htr, MeasureTheory.ae_restrict_mem (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi]
      with z htz hz
    have hzpos : 0 < z := hz
    -- the slice is `C²` on the open angle interval
    have hcd : ContDiffOn ℝ 2
        (fun θ : ℝ => Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      ((hA.Dz).curry_θ hzpos).of_le (by simp [Work.Stability.smoothOrder])
    -- the `σ`-weighted `L²`-integrability of `∂_θ²` of the slice
    have hDμ : MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (deriv (fun θ' : ℝ => Work.Spaces.Dz (Work.FTS.EllipticEst.H2W.Aof Ψ) z θ')) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 := Work.FTS.ClassC.VopGen.HkMem_zero_slice_mu (α := α) hα hα4 hsmg hg z hzpos
      exact MeasureTheory.IntegrableOn.congr_set_ae h1 (by
        rw [Work.Spaces.Iθ]
        exact MeasureTheory.Ioo_ae_eq_Icc)
    exact Work.FTS.ClassC.VopGen.muSliceAgmonPointwise (α := α) hα hα4 hcd htz.1 htz.2 hDμ
  -- transport `Ioi 0` to `Iz = Ici 0` (they differ by the null set `{0}`)
  have hIoi : (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl, ← hIoi]
  exact key

end Work.FTS.ClassC.VopGen
