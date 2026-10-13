/-
# Additivity of `L₁₂` on `F_* + u`, for a datum of the **open** smooth class

`Work.Construction.L12 g z = ∫_z^∞ ∫_0^{π/2} K(θ) g(s,θ)/s dθ ds` (`K(θ) = 3 sin θ cos²θ`) is an
*integral* in the profile `g`, so it is additive in the sense of the Bochner integral as soon as
the relevant integrals exist.

This is the `SmoothOpen`-scoped version of `Work.FTS.GalFields.Tail.L12_Fstar_add` (which assumes
the stronger `SmoothQuad`): nothing in the proof used the extra smoothness near `z = -1`, only the
joint continuity on the open quadrant `Q0 = (0,∞) × (0,π/2)` (for the a.e. strong measurability of
the slices and of the densities) and `HkMem α 4 u` (for the weighted `L¹`-bounds).  The route is
unchanged:

* `Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem` gives, for every `s > 0`, the
  integrability on `Iθ` of the angular slice `θ ↦ K θ u s θ / s`;
* `Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem` gives the integrability on
  `(0,∞)` of the `L₁₂`-density of `u`, restricted here to `(z,∞) ⊆ (0,∞)` (as `z ≥ 0`);
* `Work.Stability.integrableOn_slice_Fstar` (uses `0 < α`) and
  `Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn` (uses `α ≤ 1`) are the
  corresponding statements for the reference profile `F_*`;
* `Work.FTS.LocData.L12_add_mul` then assembles the additivity from these four certificates.

No boundary behaviour of `u` is used and `z = 0` is allowed.
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalFields.Tail.L12_Fstar_add
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.blocks

/-- **Additivity of `L₁₂` over `F_* + u`** at every `z ≥ 0`, for a datum of the open smooth class
(`SmoothOpen` + `ℋ⁴`).  The `SmoothOpen`-scoped companion of
`Work.FTS.GalFields.Tail.L12_Fstar_add`. -/
theorem L12_Fstar_add_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u : ℝ → ℝ → ℝ}
    (huS : Work.FTS.EllipticEst.SmoothOpen u) (hu4 : Work.Spaces.HkMem α 4 u) {z : ℝ}
    (hz : 0 ≤ z) :
    Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + u z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 u z := by
  -- the angular slice of `u`: `s > z ≥ 0`, so `s > 0` and the `HkMem`-Cauchy–Schwarz applies
  have hslice : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * u s θ / s) Work.Spaces.Iθ :=
    fun s hs =>
      Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem huS hu4
        (lt_of_le_of_lt hz hs)
  -- the density of `u`: integrable on `(0,∞)`, hence on the smaller `(z,∞)` since `z ≥ 0`
  have hdens : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K u) (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem huS hu4).mono_set
      (fun s hs => lt_of_le_of_lt hz hs)
  exact (Work.FTS.LocData.L12_add_mul (c := 0) (z := z)
    (a := Work.Construction.Fstar α) (b := u)
    (fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s)
    hslice
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 z hz)
    hdens).1

end Work.FTS.StrongEps.blocks
