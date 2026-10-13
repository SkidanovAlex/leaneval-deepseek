import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.FTS.FireFix.PhysFields
import Submission.Work.FTS.FireFix.VortEqLocal
import Submission.Work.FTS.FireFix.Clauses.psiField_contDiffAt_two

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `C¹` clause for the (negated) physical vorticity

`Work.FTS.FireFix.Clauses.negPhysOmega_contDiffAt_one`: the (negated) physical vorticity
`ω := −physOmega α A B g C` is, at every `t ∈ (0, C.T)` and every `x ∈ Uax`, of class `C¹`.

## The mathematical content

Off the axis and off the plane, the (negated) physical vorticity *is* the curl of the velocity
(`hcurl`), and the velocity is the stream-function field `psiField (Φ · t)` of the profile (`hid`,
valid on the open set `Uax`).  So `ω(·,t) = ∇× (psiField (Φ · t))` near `x`, and the vorticity of
a `C²` field is `C¹` (`contDiffAt_vorticity_one`).  The `C²`-ness of `psiField (Φ · t)` off the axis
is `Clauses.psiField_contDiffAt_two`, which needs `Φ(·,·,t)` to be `C³` at `(radial x, axial x)`
(the hypothesis `hΨ`); both `radial x > 0` and `axial x ≠ 0` hold on `Uax`, since
`Uax = {x₂ ≠ 0} ∩ {x₀² + x₁² ≠ 0}`.

## The two helper lemmas

* `curlOf` — the curl `∇× L = ∑ᵢ eᵢ ×₃ (L eᵢ)` of a *continuous linear map* `L : ℝ³ →L[ℝ] ℝ³`,
  i.e. the `FiniteTimeSingularity.vorticity` expression with the derivative already taken (this is
  `Work.SolutionDelivery.Measurable.curlOf`, re-declared in the namespace of this file so that the
  module only needs the `FireFix` imports);
* `contDiff_curlOf` — `curlOf` is `C¹` (indeed linear and continuous): a finite sum of
  compositions of the continuous linear maps `L ↦ L (e i)`, the cross product with the fixed
  vector `e i`, and `WithLp.toLp 2`.  This is the only ingredient the `C¹`-clause needs about the
  vorticity besides the local unfolding `vorticity u y = curlOf (fderiv ℝ u y)`;
* `contDiffAt_vorticity_one` — consequently the vorticity of a `C²` field is `C¹`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open FiniteTimeSingularity Set
open scoped Matrix Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace Work.FTS.FireFix.Clauses

/-- The curl (vorticity) of a continuous linear map `ℝ³ →L[ℝ] ℝ³`, in exactly the form in which
the curl of a differentiable field appears in `FiniteTimeSingularity.vorticity`:
`∇×L = ∑ᵢ eᵢ ×₃ (L eᵢ)`. -/
noncomputable def curlOf (L : ℝ³ →L[ℝ] ℝ³) : ℝ³ :=
  WithLp.toLp 2 (∑ i, FiniteTimeSingularity.e i ⨯₃ (L (FiniteTimeSingularity.e i)))

/-- The vorticity expression is smooth as a function of the derivative: it is a finite sum of
compositions of continuous linear maps, hence smooth (we only need `C¹`). -/
theorem contDiff_curlOf : ContDiff ℝ 1 curlOf := by
  unfold curlOf
  have hsum : ContDiff ℝ 1 (fun L : ℝ³ →L[ℝ] ℝ³ =>
      ∑ i, crossProduct (WithLp.ofLp (FiniteTimeSingularity.e i))
        (WithLp.ofLp (L (FiniteTimeSingularity.e i)))) := by
    refine ContDiff.sum (fun i _ => ?_)
    have h1 : ContDiff ℝ 1 (fun L : ℝ³ →L[ℝ] ℝ³ =>
        L (FiniteTimeSingularity.e i)) :=
      ContDiff.clm_apply contDiff_id contDiff_const
    have h2 : ContDiff ℝ 1 (fun L : ℝ³ →L[ℝ] ℝ³ =>
        WithLp.ofLp (L (FiniteTimeSingularity.e i))) :=
      (EuclideanSpace.equiv (Fin 3) ℝ).contDiff.comp h1
    have h3 : ContDiff ℝ 1 (fun w : Fin 3 → ℝ =>
        crossProduct (WithLp.ofLp (FiniteTimeSingularity.e i)) w) :=
      (LinearMap.toContinuousLinearMap
        (crossProduct (WithLp.ofLp (FiniteTimeSingularity.e i)))).contDiff
    exact h3.comp h2
  have htoLp : ContDiff ℝ 1 (WithLp.toLp 2 : (Fin 3 → ℝ) → ℝ³) :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff
  exact htoLp.comp hsum

/-- **The vorticity of a `C²` field is `C¹`.**  Unfolding the definition of the vorticity, it is
the fixed smooth function `curlOf` evaluated at the derivative `fderiv ℝ u`, which is `C¹` when
`u` is `C²`. -/
theorem contDiffAt_vorticity_one {u : ℝ³ → ℝ³} {x : ℝ³} (hu : ContDiffAt ℝ 2 u x) :
    ContDiffAt ℝ 1 (fun y => FiniteTimeSingularity.vorticity u y) x := by
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right (m := 1) (by norm_num)
  have hcurl : ContDiffAt ℝ 1 curlOf (fderiv ℝ u x) := contDiff_curlOf.contDiffAt
  have hmain : ContDiffAt ℝ 1 (fun y => curlOf (fderiv ℝ u y)) x := hcurl.comp x hfd
  refine hmain.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  rfl

/-- **The `C¹` clause of the (negated) physical vorticity.**

For `t ∈ (0, C.T)` and `x ∈ Uax` the (negated) physical vorticity `y ↦ −physOmega α A B g C y t`
is `C¹` at `x`.

Indeed, by `hcurl` it is the curl of the velocity, and by `hid` the velocity agrees, on the open
set `Uax` (which contains a neighbourhood of `x`), with the stream-function field
`psiField (Φ · t)`; that field is `C²` off the axis by `psiField_contDiffAt_two`, and the curl of a
`C²` field is `C¹`. -/
theorem negPhysOmega_contDiffAt_one {α : ℝ} {A B : ℝ → ℝ} {g Φ : ℝ → ℝ → ℝ → ℝ}
    {C : Work.FTS.Physical.PhysClock}
    (hid : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Work.FTS.PressureOn.Uax,
      Work.FTS.Physical.physVel (fun x s => - Work.FTS.Physical.physOmega α A B g C x s) x t
        = Work.Cyl.psiField (fun r z => Φ r z t) x)
    (hΨ : ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      ContDiffAt ℝ 3 (fun p : ℝ × ℝ => Φ p.1 p.2 t) (r, z))
    (hcurl : ∀ t ∈ Set.Ico (0 : ℝ) C.T, ∀ x : EuclideanSpace ℝ (Fin 3),
      FiniteTimeSingularity.vorticity
        (fun y => Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega α A B g C x s) y t) x
        = - Work.FTS.Physical.physOmega α A B g C x t) :
    ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Work.FTS.PressureOn.Uax,
      ContDiffAt ℝ 1 (fun y : EuclideanSpace ℝ (Fin 3) =>
        - Work.FTS.Physical.physOmega α A B g C y t) x := by
  intro t ht x hx
  -- on `Uax` the radius is positive and the height is non-zero
  have hrad : 0 < Work.Cyl.radial x := by
    rcases eq_or_lt_of_le (Work.Cyl.radial_nonneg x) with h | h
    · exfalso
      have h01 := (Work.Cyl.radial_eq_zero_iff x).mp h.symm
      exact hx.2 (by rw [h01.1, h01.2]; norm_num)
    · exact h
  have hax : Work.Cyl.axial x ≠ 0 := hx.1
  -- the stream-function field `psiField (Φ · t)` is `C²` at `x`, hence its curl is `C¹`
  have h3 : ContDiffAt ℝ 3 (fun p : ℝ × ℝ => Φ p.1 p.2 t)
      (Work.Cyl.radial x, Work.Cyl.axial x) :=
    hΨ t ht (Work.Cyl.radial x) (Work.Cyl.axial x) hrad hax
  have h2 : ContDiffAt ℝ 2 (fun y : ℝ³ => Work.Cyl.psiField (fun r z => Φ r z t) y) x :=
    psiField_contDiffAt_two (ψ := fun r z => Φ r z t) hrad h3
  have h1 : ContDiffAt ℝ 1 (fun y : ℝ³ => FiniteTimeSingularity.vorticity
      (fun z : ℝ³ => Work.Cyl.psiField (fun r z => Φ r z t) z) y) x :=
    contDiffAt_vorticity_one h2
  -- `ω = ∇× u` and `u = psiField (Φ · t)` near `x`, so `ω = ∇×(psiField (Φ · t))` near `x`
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Work.FTS.PressureOn.isOpen_Uax.mem_nhds hx] with y hy
  have hev : (fun z : ℝ³ => Work.Cyl.psiField (fun r z => Φ r z t) z)
      =ᶠ[𝓝 y] (fun z : ℝ³ => Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega α A B g C x s) z t) := by
    filter_upwards [Work.FTS.PressureOn.isOpen_Uax.mem_nhds hy] with z hz
    exact (hid t ht z hz).symm
  have hfd : fderiv ℝ (fun z : ℝ³ => Work.Cyl.psiField (fun r z => Φ r z t) z) y
      = fderiv ℝ (fun z : ℝ³ => Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega α A B g C x s) z t) y :=
    hev.fderiv_eq
  have hcurly := hcurl t (Set.Ioo_subset_Ico_self ht) y
  rw [← hcurly]
  simp only [FiniteTimeSingularity.vorticity, hfd]

end Work.FTS.FireFix.Clauses
