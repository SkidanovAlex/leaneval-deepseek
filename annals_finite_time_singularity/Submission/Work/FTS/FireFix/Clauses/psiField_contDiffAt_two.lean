import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.FireFix.Defs
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `psiField ψ` is `C²` off the axis when `ψ` is `C³`

The stream-function velocity field `Work.Cyl.psiField ψ` is built from the polar data
`(ρ, x₃) ↦ (ψ, ∂_rψ, ∂_zψ)` of the two-variable stream function.  This module proves that the
composition stays as smooth as the data allows off the axis: if `ψ` is `C³` at
`(radial x, axial x)` and `radial x > 0`, then `psiField ψ` is `C²` at `x`.

The two ingredients are

* `contDiffAt_radial` — `x ↦ radial x = √(x₀² + x₁²)` is `C²` at `x` when `radial x > 0`
  (a neighbourhood of `x` lies in `radSq > 0`, where `√` is smooth);
* `contDiffAt_pdZ_uncurry`, `contDiffAt_pdR_uncurry` — the partial derivatives
  `(r,z) ↦ pdZ ψ r z`, `(r,z) ↦ pdR ψ r z` are `C²` at `(r,z)` as soon as `ψ` is `C³` there.
  Indeed both are the first derivative `fderiv ℝ (uncurry ψ)` evaluated in a fixed direction
  `(0,1)` resp. `(1,0)` (`Work.Cyl.fderiv_prod_apply_snd`, `Work.Cyl.fderiv_prod_apply_fst`), and
  `fderiv` of a `C³` function is `C²`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.FTS.FireFix.Clauses

/-- The axial partial derivative `(r,z) ↦ ∂_zψ(r,z)` of a `C³` stream function is `C²`. -/
theorem contDiffAt_pdZ_uncurry {ψ : ℝ → ℝ → ℝ} {r z : ℝ}
    (hψ : ContDiffAt ℝ 3 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Work.Cyl.pdZ ψ p.1 p.2) (r, z) := by
  -- `ψ` is differentiable on a neighbourhood of `(r,z)`
  have hev : ∀ᶠ p : ℝ × ℝ in nhds (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  -- `fderiv ℝ ψ` is `C²` at `(r,z)`
  have hfd : ContDiffAt ℝ 2 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 2) (by norm_num)
  -- evaluating it in the fixed direction `(0,1)` preserves smoothness
  have hΦ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (0, 1)) (r, z) :=
    hfd.clm_apply contDiffAt_const
  -- and on a neighbourhood it agrees with `∂_zψ`
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (Work.Cyl.fderiv_prod_apply_snd ψ p.1 p.2 hp).symm

/-- The radial partial derivative `(r,z) ↦ ∂_rψ(r,z)` of a `C³` stream function is `C²`. -/
theorem contDiffAt_pdR_uncurry {ψ : ℝ → ℝ → ℝ} {r z : ℝ}
    (hψ : ContDiffAt ℝ 3 (fun p : ℝ × ℝ => ψ p.1 p.2) (r, z)) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Work.Cyl.pdR ψ p.1 p.2) (r, z) := by
  have hev : ∀ᶠ p : ℝ × ℝ in nhds (r, z),
      DifferentiableAt ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p :=
    (hψ.eventually (by norm_num)).mono fun p hp => hp.differentiableAt (by norm_num)
  have hfd : ContDiffAt ℝ 2 (fderiv ℝ (fun p : ℝ × ℝ => ψ p.1 p.2)) (r, z) :=
    hψ.fderiv_right (m := 2) (by norm_num)
  have hΦ : ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => ψ q.1 q.2) p) (1, 0)) (r, z) :=
    hfd.clm_apply contDiffAt_const
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [hev] with p hp
  exact (Work.Cyl.fderiv_prod_apply_fst ψ p.1 p.2 hp).symm

/-- `x ↦ radial x = √(x₀² + x₁²)` is `C²` at `x` provided `radial x > 0`. -/
theorem contDiffAt_radial_two {x : EuclideanSpace ℝ (Fin 3)}
    (hx : 0 < Work.Cyl.radial x) :
    ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => Work.Cyl.radial y) x := by
  have hsq : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => Work.Cyl.radSq y) x := by
    show ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => y 0 ^ 2 + y 1 ^ 2) x
    fun_prop
  have hpos : 0 < Work.Cyl.radSq x := Real.sqrt_pos.mp hx
  exact (Real.contDiffAt_sqrt (ne_of_gt hpos)).comp x hsq

theorem psiField_contDiffAt_two {ψ : ℝ → ℝ → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hx : 0 < Work.Cyl.radial x)
    (hψ : ContDiffAt ℝ 3 (fun p : ℝ × ℝ => ψ p.1 p.2) (Work.Cyl.radial x, Work.Cyl.axial x)) :
    ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => Work.Cyl.psiField ψ y) x := by
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hx
  -- the polar data are `C²` at `x`
  have hrad := contDiffAt_radial_two hx
  have hax : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => Work.Cyl.axial y) x := by
    show ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => y 2) x
    fun_prop
  have hP : ContDiffAt ℝ 2
      (fun y : EuclideanSpace ℝ (Fin 3) => (Work.Cyl.radial y, Work.Cyl.axial y)) x :=
    hrad.prodMk hax
  -- the profile data are `C²` at `(radial x, axial x)`
  have hpdZ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Work.Cyl.pdZ ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := contDiffAt_pdZ_uncurry hψ
  have hpdR : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Work.Cyl.pdR ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := contDiffAt_pdR_uncurry hψ
  have hψ2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2)
      (Work.Cyl.radial x, Work.Cyl.axial x) := hψ.of_le (by norm_num)
  have hpdZc : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hpdZ.comp x hP using 1
    ext y; rfl
  have hpdRc : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hpdR.comp x hP using 1
    ext y; rfl
  have hψc : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x := by
    convert hψ2.comp x hP using 1
    ext y; rfl
  -- the two components of `cylField`, as functions of `x`
  have hA : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y) x :=
    hpdZc.div hrad hrne
  have hB : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      -(ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
        - Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) x :=
    (hψc.div hrad hrne).neg.sub hpdRc
  have hrv : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => Work.Cyl.radialVec y) x := by
    rw [show Work.Cyl.radialVec = fun y : EuclideanSpace ℝ (Fin 3) =>
        (y 0) • Work.Cyl.e0 + (y 1) • Work.Cyl.e1 from by
      funext y; ext i; fin_cases i <;>
        simp [Work.Cyl.radialVec, Work.Cyl.e0, Work.Cyl.e1, FiniteTimeSingularity.e]]
    fun_prop
  have hmain : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) =>
      (Work.Cyl.pdZ ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
          • Work.Cyl.radialVec y
        + (-(ψ (Work.Cyl.radial y) (Work.Cyl.axial y) / Work.Cyl.radial y)
            - Work.Cyl.pdR ψ (Work.Cyl.radial y) (Work.Cyl.axial y)) • Work.Cyl.eZ) x :=
    (hA.smul hrv).add (hB.smul (contDiffAt_const (c := Work.Cyl.eZ)))
  refine hmain.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  simp only [Work.Cyl.psiField, Work.Cyl.cylField]

end Work.FTS.FireFix.Clauses
