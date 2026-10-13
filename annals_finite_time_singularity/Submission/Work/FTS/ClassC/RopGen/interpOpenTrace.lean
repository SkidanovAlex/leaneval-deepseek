import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.PkgK5.K5c.TraceOpen
import Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllSol.EllPkgAux.mollAdm
import Submission.Work.EllipticEst.Core.i0Aux.interpS_theta
import Submission.Work.FTS.ClassC.RopGen.Trace.mollDom
import Submission.Work.FTS.ClassC.RopGen.Trace.mollFatou
import Submission.Work.FTS.ClassC.RopGen.sliceSecNonposBochner
import Submission.Work.FTS.ClassC.RopGen.sliceAgmonEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.RopGen

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false

/-!
# `interpOpenTrace` — the assembly

Target (statement unchanged, see below): `∃ C, 0 < C ∧ InterpOpenTrace C`, i.e. the trace-class
single-function interpolation estimate of Elgindi's §7.

## The route: mollification transfer from the proved strip-class estimate

`InterpOpenTrace C` is proved by transferring the **proved** strip-class estimate
`Work.EllipticEst.Core.i0Aux.interpS_theta` (`= ∃ C, 0 < C ∧ InterpStrip C`) along the
*approximant*

  `Φ := zmoll G δ ε`  (the logarithmic-radial mollification of the doubly-odd-extension angular
                        mollification `thMoll`),

with `δ, ε ∈ (0, 1/2]`.  The datum `G` is recovered by lower semicontinuity (Fatou) on the left,
whereas the right-hand side is dominated:

```
α² ∫ mixIntS G
  ≤ α² (∫ mixIntS Φ + η)                        -- `Trace.mollFatou`   (η > 0 arbitrary)
  ≤ C₀ (α⁴ ∫ ddIntS Φ + ∫ ttIntS Φ + α² ∫ dIntS Φ)   -- `interpS_theta` at Φ (strip class)
  ≤ C₀ K (α⁴ ∫ ddIntS G + ∫ ttIntS G + α² ∫ dIntS G) -- `Trace.mollDom`   (dominations)
```
and `η → 0` gives `InterpOpenTrace (C₀ * K)`.

The two analytic pieces of the transfer are proved in the sibling modules
`Submission/Work/FTS/ClassC/RopGen/Trace/mollDom.lean` (the dominations of the four functionals
of `Φ`, together with the four outer integrabilities) and
`Submission/Work/FTS/ClassC/RopGen/Trace/mollFatou.lean` (the `+η` Fatou step); both are proved
in the `Work.FTS.ClassC.RopGen.Trace` namespace.  This file contains the (short) assembly, and
additionally two 1-D angular lemmas (`pairNonpos`, `sliceBound`) that record the slicewise
Agmon/completing-squares input used by the independent `AgmonIbpCut` route of the chapter.
-/

/-- **The sign of the pairing, for the slices of a datum.**  For `G` smooth on the open quadrant
and `z > 0`, if the slice `θ ↦ D_zG z θ` has vanishing one-sided limits at `0` and `π/2`, then

  `∫_θ σ θ · (D_zG z θ · ∂_θ²(D_zG) z θ) ≤ 0`.

This is `sliceSecNonposBochner` applied to the slice, and it is the 1-D input that makes the
honesty set `H = {z | ∫_θ σ (∂_θ D_zG)² < ∞}` harmless in the pointwise Agmon estimates (on
`H^c` the Bochner integral above is `0`, so the inequality still holds). -/
theorem pairNonpos {G : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen G) {z : ℝ}
    (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hπ : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
      * (Work.Spaces.Dz G z θ
        * Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ)) ≤ 0 := by
  have hcd : ContDiffOn ℝ 2 (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.Dz.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have h := Work.FTS.ClassC.RopGen.sliceSecNonposBochner
    (f := fun θ : ℝ => Work.Spaces.Dz G z θ) hcd h0 hπ
  simpa only [Work.FTS.EllipticEst.thEta, Work.Spaces.pth] using h

/-- **The slice Agmon bound for a datum** (the `θ`-IBP + sharp Hardy in the form needed by the
pointwise route): with `ψ = D_zG`,

  `∫_θ thEta θ · (∂_θψ(z,θ))² ≤ ((1+η)/(1−η)) · (2η ∫_θ thEta θ · ψ(z,θ)² − ∫_θ thEta θ · (ψ(z,θ)·∂_θ²ψ(z,θ)))`.

Here `hF` is the *honesty* of the left-hand slice and `hPair` the integrability of the pairing. -/
theorem sliceBound {G : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen G) {z : ℝ}
    (hz : 0 < z)
    (h0 : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hπ : Filter.Tendsto (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hF : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
      * (Work.Spaces.pth (Work.Spaces.Dz G) z θ) ^ 2) Work.Spaces.Iθ)
    (hZ : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
      * (Work.Spaces.Dz G z θ) ^ 2) Work.Spaces.Iθ)
    (hPair : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
      * (Work.Spaces.Dz G z θ
        * Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ)) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
        * (Work.Spaces.pth (Work.Spaces.Dz G) z θ) ^ 2)
      ≤ ((1 + Work.Spaces.eta) / (1 - Work.Spaces.eta))
        * (2 * Work.Spaces.eta
            * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
                * (Work.Spaces.Dz G z θ) ^ 2)
          - (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.thEta θ
              * (Work.Spaces.Dz G z θ
                * Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ))) := by
  have hcd : ContDiffOn ℝ 2 (fun θ : ℝ => Work.Spaces.Dz G z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.Dz.curry_θ hz).of_le (by simp [Work.Stability.smoothOrder])
  have h := Work.FTS.ClassC.RopGen.sliceAgmonEta
    (f := fun θ : ℝ => Work.Spaces.Dz G z θ) hcd h0 hπ
    (by simpa only [Work.FTS.EllipticEst.thEta, Work.Spaces.pth] using hF)
    (by simpa only [Work.FTS.EllipticEst.thEta] using hZ)
    (by simpa only [Work.FTS.EllipticEst.thEta, Work.Spaces.pth] using hPair)
  simpa only [Work.FTS.EllipticEst.thEta, Work.Spaces.pth] using h

end

end Work.FTS.ClassC.RopGen

namespace Work.FTS.ClassC.RopGen

/-- **The trace-class single-function interpolation estimate exists.**

Proved by the mollification transfer from the proved strip-class estimate `interpS_theta`:
the strip estimate is applied to the approximant `Φ = zmoll G δ ε` (which is strip-admissible by
the proved `mollAdm`), its right-hand side is dominated by that of the datum (`Trace.mollDom`)
and its left-hand side dominates the datum's up to `η > 0` (`Trace.mollFatou`); `η → 0` closes
the argument. -/
theorem interpOpenTrace : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.PkgK5.K5c.InterpOpenTrace C := by
  obtain ⟨C₀, hC₀, hstrip⟩ := Work.EllipticEst.Core.i0Aux.interpS_theta
  obtain ⟨K, hK, hdom⟩ := Work.FTS.ClassC.RopGen.Trace.mollDom
  refine ⟨C₀ * K, by positivity, ?_⟩
  intro α G hα hα14 hsm h0 hpi htr0 htrpi hdz0 hdzpi hsh hmi hdd htt hd
  have htr : Work.FTS.EllSol.EllPkgAux.TraceClass G :=
    ⟨hsm, h0, hpi, htr0, htrpi, hdz0, hdzpi, hsh⟩
  have hfour : Work.FTS.EllSol.EllPkgAux.FourInts G := ⟨hmi, hdd, htt, hd⟩
  -- the four functionals of the approximant are honest
  have hfin : ∀ (δ ε : ℝ), Work.FTS.EllSol.EllPkgAux.Params δ ε →
      MeasureTheory.IntegrableOn
        (fun z : ℝ =>
          Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        Work.Spaces.Iz :=
    fun δ ε hp => (hdom G htr hfour δ ε hp).2.2.2.1
  have hfat := Work.FTS.ClassC.RopGen.Trace.mollFatou G htr hfour hfin
  set R : ℝ := α ^ 4 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
    + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
    + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z) with hR
  have key : ∀ η : ℝ, 0 < η →
      α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        ≤ C₀ * K * R + α ^ 2 * η := by
    intro η hη
    obtain ⟨δ, ε, hp, hle⟩ := hfat η hη
    obtain ⟨hd1, ht1, hz1, hmΦ, hdΦ, htΦ, hzΦ⟩ := hdom G htr hfour δ ε hp
    obtain ⟨hsmΦ, hv0, hvπ⟩ := Work.FTS.EllSol.EllPkgAux.mollAdm G htr hfour δ ε hp
    have hstripΦ := hstrip α (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) hα hα14 hsmΦ hv0 hvπ
      hmΦ hdΦ htΦ hzΦ
    have hα2 : 0 ≤ α ^ 2 := sq_nonneg α
    have hα4 : 0 ≤ α ^ 4 := by positivity
    have hC0 : 0 ≤ C₀ := le_of_lt hC₀
    set M := ∫ z in Work.Spaces.Iz,
      Work.EllipticEst.Core.mixIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z with hM
    have e1 : α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        ≤ α ^ 2 * (M + η) := by
      rw [hM]
      exact mul_le_mul_of_nonneg_left hle hα2
    have e2 : α ^ 2 * (M + η) = α ^ 2 * M + α ^ 2 * η := by ring
    have e3 : α ^ 2 * M ≤ C₀ * (α ^ 4 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.ddIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        + (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.ttIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        + α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.dIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)) := by
      rw [hM]; exact hstripΦ
    have e4 : C₀ * (α ^ 4 * (∫ z in Work.Spaces.Iz,
          Work.EllipticEst.Core.ddIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        + (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.ttIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z)
        + α ^ 2 * (∫ z in Work.Spaces.Iz,
            Work.EllipticEst.Core.dIntS (Work.FTS.EllSol.PkgK5.K5c.zmoll G δ ε) z))
        ≤ C₀ * (α ^ 4 * (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
            + (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
            + α ^ 2 * (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z)) := by
      refine mul_le_mul_of_nonneg_left ?_ hC0
      refine add_le_add (add_le_add ?_ ?_) ?_
      · exact mul_le_mul_of_nonneg_left hd1 hα4
      · exact ht1
      · exact mul_le_mul_of_nonneg_left hz1 hα2
    have e5 : C₀ * (α ^ 4 * (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ddIntS G z)
          + (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
          + α ^ 2 * (K * ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z))
        = C₀ * K * R := by
      rw [hR]; ring
    have h3 : α ^ 2 * M ≤ C₀ * K * R := le_trans e3 (le_trans e4 (le_of_eq e5))
    calc α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        ≤ α ^ 2 * (M + η) := e1
      _ = α ^ 2 * M + α ^ 2 * η := e2
      _ ≤ C₀ * K * R + α ^ 2 * η := by linarith [h3]
  have hfinal : α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
      ≤ C₀ * K * R := by
    by_contra hcon
    push_neg at hcon
    have hα2pos : 0 < α ^ 2 := by positivity
    have hpos : 0 < (α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        - C₀ * K * R) / (2 * α ^ 2) := by positivity
    have hk := key _ hpos
    have hsplit : α ^ 2 * ((α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
        - C₀ * K * R) / (2 * α ^ 2))
        = (α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS G z)
          - C₀ * K * R) / 2 := by
      field_simp
    rw [hsplit] at hk
    linarith [hk]
  have hRK : C₀ * K * R = C₀ * K * (α ^ 4 * (∫ z in Work.Spaces.Iz,
        Work.EllipticEst.Core.ddIntS G z)
      + (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.ttIntS G z)
      + α ^ 2 * (∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.dIntS G z)) := by rw [hR]
  rw [hRK] at hfinal
  exact hfinal

end Work.FTS.ClassC.RopGen
