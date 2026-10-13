/-
# `L3RhsL12add` — additivity of `L₁₂` over `F = F_* + f`

The operator of the modulation chapter,

  `L₁₂(F)(z) = ∫_z^∞ ∫_0^{π/2} K(θ) F(s,θ)/s dθ ds`   (`K(θ) = 3 sin θ cos² θ`),

is an *integral*, hence additive in the profile:

  `L₁₂(F_* + f)(z) = L₁₂(F_*)(z) + L₁₂(f)(z)`   for `z > 0`.

Unconditionally the Bochner integral is only additive on integrable functions, so the proof
spends the honesty of the datum `f` (`H6Adm α f` ⟹ `SmoothOpen f` and `HkMem α 6 f`) to
produce the four integrability certificates required by `Work.FTS.LocData.L12_add_mul`:

* the angular slice of the reference profile, `θ ↦ K θ F_*(s,θ)/s` — it is continuous on the
  compact `Iθ` (`Work.Stability.integrableOn_slice_Fstar`);
* the angular slice of `f`, `θ ↦ K θ f(s,θ)/s`, for `s > z > 0`
  (`cc.integrableOn_slice_of_SmoothOpen_HkMem`, at level `4` reached from `ℋ⁶` by the monotonicity
  of `HkMem` `Work.FTS.OpenPkg.HkMem_mono_open`);
* the two densities on `(z,∞)`: `L₁₂`-density of `F_*` is the elementary `α·2/(1+s)²`
  (`Pieces.L12dens_Fstar_integrableOn`), and that of `f`
  (`cc.integrableOn_L12dens_of_SmoothOpen_HkMem`) restricted from `(0,∞)` to `(z,∞)`.

No boundary behaviour of `f` (`VanishTheta`, `axis`, `l12`) is used: the statement is a purely
measure-theoretic consequence of the honest `ℋ⁶`-regularity field of the class.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.Stability.L12Add
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.LocData.L12_add_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false

theorem L3RhsL12add : ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.StrongPersist.H6Adm α f → ∀ z : ℝ, 0 < z →
    Work.Construction.L12 (Work.Construction.Ftot α f) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z := by
  intro α hα f hf z hz
  obtain ⟨hα0, hα1⟩ := hα
  -- the honest fields of the class
  have hSO : Work.FTS.EllipticEst.SmoothOpen f := hf.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO 4 (by norm_num) hf.reg.2
  -- linearity of the integral operator on the four integrability certificates
  have hadd := (Work.FTS.LocData.L12_add_mul (c := 0) (z := z)
    (a := Work.Construction.Fstar α) (b := f)
    (fun s _ => Work.Stability.integrableOn_slice_Fstar α hα0 s)
    (fun s hs =>
      Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hSO hmem4
        (lt_of_lt_of_le hz hs.le))
    (Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_Fstar_integrableOn hα0 hα1 z hz.le)
    ((Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hSO hmem4).mono_set
      (fun s hs => lt_of_lt_of_le hz hs.le))).1
  -- `Ftot α f` is definitionally `fun z θ => F_* z θ + f z θ`
  change Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z
  exact hadd

end Work.FTS.StrongPersist.L3Rhs
