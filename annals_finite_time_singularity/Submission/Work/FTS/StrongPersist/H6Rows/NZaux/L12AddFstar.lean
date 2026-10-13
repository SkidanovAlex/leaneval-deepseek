import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.Stability.L12Add
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.Nonlinear.Pieces.L12FK_add_ge0
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsL12add
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.NZaux

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Linearity of `L₁₂` over `F_* + f` at level `ℋ⁴`.**

`Work.Construction.L12 g z = ∫_z^∞ ∫_0^{π/2} K(θ) g(s,θ)/s dθ ds` is an integral, so it is
additive in the profile; unconditionally the Bochner integral is additive only on integrable
functions, so the proof spends the honesty of the datum (`SmoothOpen f`, `HkMem α 4 f`) to
produce the four integrability certificates required by `Work.FTS.LocData.L12_add_mul`:

* the angular slice of the reference profile, `θ ↦ K θ F_*(s,θ)/s`, continuous on the compact
  `Iθ` (`Work.Stability.integrableOn_slice_Fstar`);
* the angular slice of `f`, `θ ↦ K θ f(s,θ)/s`, for `s > z > 0`
  (`Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`);
* the two densities on `(z,∞)`: that of `F_*` is the elementary `α·2/(1+s)²`
  (`Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn`), and that of `f`
  (`Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem`), restricted from `(0,∞)`
  to `(z,∞)`.

No boundary behaviour of `f` is used: the statement is a purely measure-theoretic consequence
of `SmoothOpen` and `HkMem α 4`. -/
theorem L12AddFstar {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z : ℝ, 0 < z → Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z := by
  intro z hz
  have hslice_f : ∀ s ∈ Set.Ioi z, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * f s θ / s) Work.Spaces.Iθ :=
    fun s hs =>
      Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hso hmem
        (lt_of_lt_of_le hz hs.le)
  have hdens_f : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi z) :=
    (Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hso hmem).mono_set
      (fun s hs => lt_of_lt_of_le hz hs.le)
  exact (Work.FTS.LocData.L12_add_mul (c := 0) (z := z)
    (a := Work.Construction.Fstar α) (b := f)
    (fun s _ => Work.Stability.integrableOn_slice_Fstar α hα s)
    hslice_f
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα hα1 z hz.le)
    hdens_f).1

end Work.FTS.StrongPersist.H6Rows.NZaux
