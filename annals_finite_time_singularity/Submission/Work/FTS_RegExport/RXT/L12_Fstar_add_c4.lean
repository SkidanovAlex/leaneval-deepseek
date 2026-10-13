/-
# Additivity of `L₁₂` over `F_* + u`, with the `C^4`-hypothesis on the datum

`Work.Construction.L12 g z = ∫_z^∞ ∫_0^{π/2} K(θ) g(s,θ)/s dθ ds` (`K(θ) = 3 sin θ cos²θ`) is an
*integral* in the profile `g`, so it is additive as soon as the two angular integrals and the
radial ones exist.

This is the `C^4`-scoped version of `Work.FTS.StrongEps.blocks.L12_Fstar_add_open` (which assumes
the full `SmoothOpen u`, i.e. `C^∞` on the open quadrant).  The proof of the latter never used
more than *continuity* on the open quadrant for the a.e. strong measurability of the angular
slices and of the densities, and that continuity is all the `_of_continuousOn` certificates need:

* `Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn` — the angular slice
  `θ ↦ K θ u s θ / s` is integrable on `Iθ` for every `s > 0`, from
  `ContinuousOn (uncurry u) Q0` and `HkMem α 4 u`;
* `Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn` — the density
  `s ↦ ∫_θ K θ u s θ / s` is integrable on `(0,∞)`, from the same two hypotheses;
* `Work.Stability.integrableOn_slice_Fstar` (needs `0 < α`) and
  `Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn` (needs `α ≤ 1`) are the
  corresponding statements for the reference profile `F_*`;
* `Work.FTS.LocData.L12_add_mul` then assembles the additivity from these four certificates.

The `C^4`-hypothesis enters only through `ContDiffOn.continuousOn`; no derivative of `u` is used,
so the same argument works for any `ContDiffOn ℝ n (uncurry u) Q0` with `n ≥ 0`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn
import Submission.Work.Stability.L12Add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

/-- **Additivity of `L₁₂` over `F_* + u`** at every `z ≥ 0`, for a datum that is `C^4` on the open
quadrant and lies in `ℋ⁴`. -/
theorem L12_Fstar_add_c4 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ 4 (Function.uncurry u) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 u) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + u z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 u z := by
  -- `C^4` on the open quadrant gives continuity there, which is all the certificates use
  have hcont : ContinuousOn (Function.uncurry u) Work.FTS.EllipticEst.Q0 := hu.continuousOn
  -- the angular slice of `u`: `s > z ≥ 0`, so `s > 0` and the `HkMem`-Cauchy–Schwarz applies
  have hslice : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * u s θ / s) Work.Spaces.Iθ :=
    fun s hs =>
      Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn hcont hmem s
        (lt_of_le_of_lt hz hs)
  -- the density of `u`: integrable on `(0,∞)`, hence on the smaller `(z,∞)` since `z ≥ 0`
  have hdens : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K u) (Set.Ioi z) :=
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn hcont hmem).mono_set
      (Set.Ioi_subset_Ioi hz)
  exact (Work.FTS.LocData.L12_add_mul (c := 0) (z := z)
    (a := Work.Construction.Fstar α) (b := u)
    (fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s)
    hslice
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 z hz)
    hdens).1

end Work.FTS_RegExport.RXT
