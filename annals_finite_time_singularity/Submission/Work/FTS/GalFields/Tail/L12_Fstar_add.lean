/-
# Additivity of `L₁₂` on `F_* + u`

`Work.Construction.L12 g z = ∫_z^∞ ∫_0^{π/2} K(θ) g(s,θ)/s dθ ds` (`K(θ) = 3 sin θ cos²θ`) is an
*integral* in the profile `g`, hence additive; unconditionally the Bochner integral is additive
only on integrable functions, so the proof spends the honesty of the datum
(`SmoothQuad u` for the a.e. measurability, `HkMem α 4 u` for the weighted `L¹`-bounds) to produce
the four integrability certificates that `Work.FTS.LocData.L12_add_mul` asks for:

* the angular slice of the reference profile, `θ ↦ K θ F_*(s,θ)/s`, continuous on the compact
  `Iθ` (`Work.Stability.integrableOn_slice_Fstar`) — this is where `0 < α` is used;
* the angular slice of `u`, `θ ↦ K θ u(s,θ)/s` for `s > z ≥ 0`
  (`Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`, Cauchy–Schwarz against
  `HkIntegrand α 4 u s ·`);
* the two densities on `(z,∞)`: that of `F_*` is the elementary `α·2/(1+s)²`
  (`Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn`, for every `z ≥ 0`), and that
  of `u` (`Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem`), restricted from
  `(0,∞)` to `(z,∞)`.

The only conversion needed is `SmoothQuad u → SmoothOpen u` (the open quadrant `(0,∞) × (0,π/2)`
sits inside the strip `(-1,∞) × (0,π/2)` of `SmoothQuad`).  No boundary behaviour of `u` is used,
and `z = 0` is allowed: for `s ∈ (z,∞)` the a.e. strong measurability arguments of the open
class only need `s > 0`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Construction.Defs
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.Stability.L12Add
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.Tail

set_option autoImplicit false

/-- **Linearity of `L₁₂` over `F_* + u`**, at every `z ≥ 0`, for a datum of the localised-data
class (`SmoothQuad` + `ℋ⁴`).  This is `Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar`
(`0 < z`, datum of the open class) re-scoped to the hypotheses of this chapter. -/
theorem L12_Fstar_add {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u : ℝ → ℝ → ℝ}
    (huS : Work.FTS.LocData.SmoothQuad u) (hu4 : Work.Spaces.HkMem α 4 u)
    {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + u z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 u z := by
  -- `SmoothQuad` is `C^∞` on the strip `(-1,∞) × (0,π/2)`, which contains the open quadrant
  -- `Q0 = (0,∞) × (0,π/2)` on which `SmoothOpen` is stated.
  have huS' : Work.FTS.EllipticEst.SmoothOpen u :=
    huS.mono (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) (le_refl _))
  -- the angular slice of `u`: `s > z ≥ 0`, so `s > 0` and the `HkMem`-Cauchy–Schwarz applies
  have hslice : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * u s θ / s) Work.Spaces.Iθ :=
    fun s hs =>
      Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem huS' hu4
        (lt_of_le_of_lt hz hs)
  -- the density of `u`: integrable on `(0,∞)`, hence on the smaller `(z,∞)` since `z ≥ 0`
  have hdens : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K u) (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem huS' hu4).mono_set
      (fun s hs => lt_of_le_of_lt hz hs)
  exact (Work.FTS.LocData.L12_add_mul (c := 0) (z := z)
    (a := Work.Construction.Fstar α) (b := u)
    (fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s)
    hslice
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 z hz)
    hdens).1

end Work.FTS.GalFields.Tail
