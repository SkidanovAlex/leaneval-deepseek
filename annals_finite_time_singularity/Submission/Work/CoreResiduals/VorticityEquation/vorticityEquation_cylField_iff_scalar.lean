import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.CoreResiduals.Defs
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.FieldDeriv
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.Frame
import Submission.Work.LWP.Defs
import Submission.Work.CoreResiduals.VorticityEquation.fderiv_eTheta
import Submission.Work.CoreResiduals.VorticityEquation.fderiv_cylField_angularVec
import Submission.Work.CoreResiduals.VorticityEquation.fderiv_comp_radial_axial

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Work.Cyl
open FiniteTimeSingularity

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.CoreResiduals.VorticityEquation

theorem deriv_smul_const_eucl {n : ℕ} (c : ℝ → ℝ) (f : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    deriv (fun s => c s • f) t = deriv c t • f := by
  by_cases hf : f = 0
  · subst hf; simp
  · by_cases hc : DifferentiableAt ℝ c t
    · exact deriv_smul_const hc f
    · have hnorm : ‖f‖ ^ 2 ≠ 0 := by
        have : (0:ℝ) < ‖f‖ := norm_pos_iff.mpr hf
        positivity
      have hg : ¬ DifferentiableAt ℝ (fun s => c s • f) t := by
        intro h
        apply hc
        let T : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := (‖f‖ ^ 2)⁻¹ • innerSL ℝ f
        have hcomp : DifferentiableAt ℝ (fun s => T (c s • f)) t :=
          (T.differentiableAt).comp t h
        have heq : (fun s => T (c s • f)) = c := by
          funext s
          simp only [T, smul_apply, smul_eq_mul, innerSL_apply_apply,
            real_inner_smul_right, real_inner_self_eq_norm_sq, mul_comm]
          field_simp
        rwa [heq] at hcomp
      rw [deriv_zero_of_not_differentiableAt hc, deriv_zero_of_not_differentiableAt hg,
        zero_smul]

lemma differentiableAt_angularVec (x : R3) : DifferentiableAt ℝ (fun y : R3 => angularVec y) x := by
  have h0 : DifferentiableAt ℝ (fun y : R3 => y 0) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x 0).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y : R3 => y 1) x :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x 1).differentiableAt
  have hfun : (fun y : R3 => angularVec y) = fun y : R3 => (-y 1) • e0 + (y 0) • e1 := by
    funext y
    apply ext_coord <;> simp [angularVec, e0, e1, FiniteTimeSingularity.e]
  rw [hfun]
  exact ((h1.neg.smul_const e0).add (h0.smul_const e1))

lemma fderiv_eTheta_cylField_eq_zero (ur uz : ℝ → ℝ → ℝ) (x : R3) (hr : 0 < radial x) :
    fderiv ℝ (fun y : R3 => eTheta y) x (cylField ur uz x) = 0 := by
  rw [fderiv_eTheta x (cylField ur uz x) hr]
  set v : R3 := cylField ur uz x with hv
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hv0 : v 0 = ur (radial x) (axial x) * x 0 / radial x := by rw [hv]; exact cylField_zero ur uz x
  have hv1 : v 1 = ur (radial x) (axial x) * x 1 / radial x := by rw [hv]; exact cylField_one ur uz x
  have hsq : x 0 ^ 2 + x 1 ^ 2 = radial x ^ 2 := (radial_sq x).symm
  have hdot : x 0 * v 0 + x 1 * v 1 = ur (radial x) (axial x) * radial x := by
    rw [hv0, hv1]; field_simp; rw [hsq]
  have hang : angularVec v = (ur (radial x) (axial x) / radial x) • angularVec x := by
    apply ext_coord
    · simp only [angularVec_apply_zero, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, hv1]; ring
    · simp only [angularVec_apply_one, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, hv0]; ring
    · simp only [angularVec_apply_two, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_zero]
  rw [hdot, hang, smul_smul, ← add_smul]
  have : -(ur (radial x) (axial x) * radial x) / radial x ^ 3
      + (radial x)⁻¹ * (ur (radial x) (axial x) / radial x) = 0 := by
    field_simp; ring
  rw [this, zero_smul]

lemma fderiv_cylField_eTheta (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (huz : DiffAt2 uz (radial x) (axial x))
    (hr : 0 < radial x) :
    fderiv ℝ (cylField ur uz) x (eTheta x) = redR ur (radial x) (axial x) • eTheta x := by
  have h3 := fderiv_cylField_angularVec ur uz x hur huz hr
  have he : eTheta x = (radial x)⁻¹ • angularVec x := by simp only [eTheta, one_div]
  rw [he, map_smul, h3]
  simp only [smul_smul]
  congr 1
  ring

lemma timeDeriv_swirl {W : ℝ → ℝ → ℝ → ℝ} (x : R3) (t : ℝ) :
    timeDeriv (fun x t => W (radial x) (axial x) t • eTheta x) x t
      = deriv (fun s : ℝ => W (radial x) (axial x) s) t • eTheta x := by
  simp only [timeDeriv]
  exact deriv_smul_const_eucl (fun s => W (radial x) (axial x) s) (eTheta x) t

lemma directionalDeriv_swirl_cylField {ur uz W : ℝ → ℝ → ℝ → ℝ}
    (hW : ∀ t r z : ℝ, 0 < r → DiffAt2 (fun r z => W r z t) r z)
    (x : R3) (t : ℝ) (hr : 0 < radial x) :
    directionalDeriv
        (fun x t => W (radial x) (axial x) t • eTheta x)
        (fun x t => cylField (fun r z => ur r z t) (fun r z => uz r z t) x) x t
      = (ur (radial x) (axial x) t * pdR (fun r' z' => W r' z' t) (radial x) (axial x)
          + uz (radial x) (axial x) t * pdZ (fun r' z' => W r' z' t) (radial x) (axial x))
        • eTheta x := by
  rw [directionalDeriv]
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hG : DiffAt2 (fun r z => W r z t) (radial x) (axial x) := hW t (radial x) (axial x) hr
  have hrad : DifferentiableAt ℝ radial x := differentiableAt_radial x hrne
  have hax : DifferentiableAt ℝ axial x := differentiableAt_axial x
  have hΦ : DifferentiableAt ℝ (fun y : R3 => (radial y, axial y)) x := hrad.prodMk hax
  have hc : DifferentiableAt ℝ (fun y : R3 => W (radial y) (axial y) t) x :=
    DifferentiableAt.comp (g := fun p : ℝ × ℝ => W p.1 p.2 t) x hG hΦ
  have hf : DifferentiableAt ℝ (fun y : R3 => eTheta y) x := by
    have h1 : DifferentiableAt ℝ (fun y : R3 => (radial y)⁻¹) x := hrad.inv hrne
    have h2 : DifferentiableAt ℝ (fun y : R3 => angularVec y) x := differentiableAt_angularVec x
    have h := h1.smul h2
    convert h using 1
    funext y
    simp [eTheta, one_div]
  rw [fderiv_fun_smul hc hf]
  rw [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply]
  rw [fderiv_eTheta_cylField_eq_zero (fun r z => ur r z t) (fun r z => uz r z t) x hr]
  rw [fderiv_comp_radial_axial (fun r z => W r z t) x
        (cylField (fun r z => ur r z t) (fun r z => uz r z t) x) hG hr]
  have hsq : x 0 ^ 2 + x 1 ^ 2 = radial x ^ 2 := (radial_sq x).symm
  have hv0 : (cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 0
      = ur (radial x) (axial x) t * x 0 / radial x := cylField_zero _ _ x
  have hv1 : (cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 1
      = ur (radial x) (axial x) t * x 1 / radial x := cylField_one _ _ x
  have hdot' : x 0 * (cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 0
      + x 1 * (cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 1
      = ur (radial x) (axial x) t * radial x := by
    rw [hv0, hv1]; field_simp; rw [hsq]
  have hdot : (x 0 * (cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 0
      + x 1 * (cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 1) / radial x
      = ur (radial x) (axial x) t := by
    rw [hdot']; field_simp
  rw [hdot, cylField_two]
  simp only [smul_zero, zero_add]
  congr 1
  ring

lemma directionalDeriv_cylField_swirl {ur uz W : ℝ → ℝ → ℝ → ℝ}
    (hu : ∀ t r z : ℝ, 0 < r →
      DiffAt2 (fun r z => ur r z t) r z ∧ DiffAt2 (fun r z => uz r z t) r z)
    (x : R3) (t : ℝ) (hr : 0 < radial x) :
    directionalDeriv
        (fun x t => cylField (fun r z => ur r z t) (fun r z => uz r z t) x)
        (fun x t => W (radial x) (axial x) t • eTheta x) x t
      = (W (radial x) (axial x) t * (ur (radial x) (axial x) t / radial x)) • eTheta x := by
  rw [directionalDeriv]
  rw [map_smul, fderiv_cylField_eTheta (fun r z => ur r z t) (fun r z => uz r z t) x
        (hu t (radial x) (axial x) hr).1 (hu t (radial x) (axial x) hr).2 hr]
  simp only [smul_smul, redR]

/-! ## axis helper -/

lemma fderiv_apply_eZ_eq_zero {F : R3 → R3} {x : R3} (hF : ∀ s : ℝ, F (x + s • eZ) = 0) :
    fderiv ℝ F x eZ = 0 := by
  by_cases hd : DifferentiableAt ℝ F x
  · rw [fderiv_apply_eq_deriv_line F x eZ hd]
    have : (fun s : ℝ => F (x + s • eZ)) = fun _ => 0 := by funext s; exact hF s
    rw [this]; simp
  · rw [fderiv_zero_of_not_differentiableAt hd]; simp

/-! ## the corner facts at (r,0,z) -/

lemma radial_mk3 (r z : ℝ) (hr : 0 < r) : radial (!₂[r, 0, z] : R3) = r := by
  have h1 : (!₂[r, 0, z] : R3) 0 = r := by simp
  have h2 : (!₂[r, 0, z] : R3) 1 = 0 := by simp
  rw [radial, radSq, h1, h2, show (0:ℝ) ^ 2 = 0 by norm_num, add_zero]
  exact Real.sqrt_sq hr.le

lemma axial_mk3 (r z : ℝ) : axial (!₂[r, 0, z] : R3) = z := by
  simp [axial]

lemma eTheta_mk3 (r z : ℝ) (hr : 0 < r) : eTheta (!₂[r, 0, z] : R3) = e1 := by
  rw [eTheta, radial_mk3 r z hr]
  apply ext_coord
  · simp [angularVec, e1, FiniteTimeSingularity.e]
  · simp [angularVec, e1, FiniteTimeSingularity.e]
    field_simp
  · simp [angularVec, e1, FiniteTimeSingularity.e]

/-! ## the main theorem -/

/-- **The scalar (meridian) reduction of the `ℝ³` vorticity equation** — the spatial half of the
dictionary that residual R1 needs.

For a no-swirl axisymmetric velocity `u(x,t) = cylField (ur · t) (uz · t) x` (radial component `ur`,
axial component `uz`, as functions of `(r,z,t)`) and a swirl vorticity
`ω(x,t) = W(radial x, axial x, t)·eTheta x`, the `ℝ³` vorticity equation
`∂ₜω + (u·∇)ω = (ω·∇)u` is equivalent to the *scalar* equation

  `∂ₜW + ur·∂_rW + uz·∂_zW = (ur/r)·W`   on `r > 0`,

given the differentiability of `W(·,·,t)` and of `ur(·,·,t)`, `uz(·,·,t)` in `(r,z)` off the axis
(the `DiffAt2` hypotheses; without them the chain rule is unavailable and the equivalence fails, as
both reviews noted with explicit counterexamples).  The `e_r`- and `e_z`-components of the equation
are identically zero (`∂ₜω = (∂ₜW)·e_θ`, `(u·∇)ω = (ur ∂_rW + uz ∂_zW)·e_θ + W·(u·∇)e_θ` with
`(u·∇)e_θ = 0` since the only non-vanishing derivative of `e_θ` is along `e_φ` and `u` has no swirl
component, and `(ω·∇)u = W·(1/r)∂_φ u = (W·ur/r)·e_θ`), and on the axis the equation is automatic
since `eTheta` vanishes there.

Instantiating `ur = pdZ ψ`, `uz = -(ψ/r) - pdR ψ` gives the stream-function case (`psiField ψ`), and
the chain rule `(ρ,θ) → (R = ρ^α, θ) → (z = R/μ̄, θ)` converts the scalar equation into
`Work.Stability.SelfSimEulerS`/`DynEq`, i.e. the profile-level form of R1.  The remaining ingredient
of R1 is the identification of the stream function with the elliptic inverse of `ω`
(`Work.Elliptic.bslOp`, `Work.Construction.StatEqPhi`). -/
theorem vorticityEquation_cylField_iff_scalar {ur uz : ℝ → ℝ → ℝ → ℝ} {W : ℝ → ℝ → ℝ → ℝ}
    (hW : ∀ t r z : ℝ, 0 < r → Work.Cyl.DiffAt2 (fun r z => W r z t) r z)
    (hu : ∀ t r z : ℝ, 0 < r →
      Work.Cyl.DiffAt2 (fun r z => ur r z t) r z ∧ Work.Cyl.DiffAt2 (fun r z => uz r z t) r z) :
    Work.LWP.VorticityEquation
        (fun x t => Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x)
        (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
      ↔ (∀ r z t : ℝ, 0 < r →
            deriv (fun s : ℝ => W r z s) t
              + ur r z t * Work.Cyl.pdR (fun r' z' => W r' z' t) r z
              + uz r z t * Work.Cyl.pdZ (fun r' z' => W r' z' t) r z
              = (ur r z t / r) * W r z t) := by
  constructor
  · intro hVE r z t hr
    have hradX : radial (!₂[r, 0, z] : R3) = r := radial_mk3 r z hr
    have haxX : axial (!₂[r, 0, z] : R3) = z := axial_mk3 r z
    have heX : eTheta (!₂[r, 0, z] : R3) = e1 := eTheta_mk3 r z hr
    have hrX : 0 < radial (!₂[r, 0, z] : R3) := by rw [hradX]; exact hr
    have h := hVE (!₂[r, 0, z] : R3) t
    rw [timeDeriv_swirl (W := W) (!₂[r, 0, z] : R3) t,
        directionalDeriv_swirl_cylField (W := W) hW (!₂[r, 0, z] : R3) t hrX,
        directionalDeriv_cylField_swirl (W := W) hu (!₂[r, 0, z] : R3) t hrX] at h
    rw [hradX, haxX, heX] at h
    rw [← add_smul] at h
    have h2 := congrArg (fun v : R3 => v 1) h
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, e1_apply_one, mul_one] at h2
    rw [add_assoc]
    rw [h2]
    ring
  · intro hsc x t
    by_cases hr : 0 < radial x
    · rw [timeDeriv_swirl (W := W) x t,
          directionalDeriv_swirl_cylField (W := W) hW x t hr,
          directionalDeriv_cylField_swirl (W := W) hu x t hr, ← add_smul]
      congr 1
      rw [← add_assoc]
      rw [hsc (radial x) (axial x) t hr]
      ring
    · have hr0 : radial x = 0 := le_antisymm (not_lt.mp hr) (radial_nonneg x)
      have hx01 : x 0 = 0 ∧ x 1 = 0 := (radial_eq_zero_iff x).mp hr0
      have hradVec : radialVec x = 0 := by
        apply ext_coord <;> simp [radialVec, hx01.1, hx01.2]
      have he0 : eTheta x = 0 := by simp [eTheta, hr0]
      have hu0 : cylField (fun r z => ur r z t) (fun r z => uz r z t) x
          = uz (radial x) (axial x) t • eZ := by
        show (ur (radial x) (axial x) t / radial x) • radialVec x
            + uz (radial x) (axial x) t • eZ = _
        rw [hradVec, smul_zero, zero_add]
      have hT1 : timeDeriv (fun x t => W (radial x) (axial x) t • eTheta x) x t = 0 := by
        rw [timeDeriv_swirl (W := W) x t, he0, smul_zero]
      have hT3 : directionalDeriv
            (fun x t => cylField (fun r z => ur r z t) (fun r z => uz r z t) x)
            (fun x t => W (radial x) (axial x) t • eTheta x) x t = 0 := by
        rw [directionalDeriv]
        have h0 : W (radial x) (axial x) t • eTheta x = 0 := by rw [he0, smul_zero]
        rw [h0]; simp
      have hT2 : directionalDeriv
            (fun x t => W (radial x) (axial x) t • eTheta x)
            (fun x t => cylField (fun r z => ur r z t) (fun r z => uz r z t) x) x t = 0 := by
        rw [directionalDeriv, hu0, map_smul]
        have hz : (fderiv ℝ (fun y : R3 => W (radial y) (axial y) t • eTheta y) x) eZ = 0 :=
          fderiv_apply_eZ_eq_zero (F := fun y : R3 => W (radial y) (axial y) t • eTheta y)
            (by intro s
                have hrs : radial (x + s • eZ) = 0 := by rw [radial_add_smul_eZ, hr0]
                simp [eTheta, hrs])
        rw [hz, smul_zero]
      rw [hT1, hT2, hT3]
      simp


end Work.CoreResiduals.VorticityEquation
