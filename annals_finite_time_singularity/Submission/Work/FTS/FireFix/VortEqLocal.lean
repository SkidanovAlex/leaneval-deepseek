/-
# `Work.FTS.FireFix.VortEqLocal` — the local (pointwise) vorticity equation on `Uax`

This is the third of the four changes of design §5 item 7: the physical vorticity equation is
available only *on the open set* `Uax` (the complement of the axis and of the plane — a null set)
and only for `t ∈ (0, C.T)`, because the meridian form of the fake-time equation
(`Work.FTS.MeridianDyn.MeridianEqOn`, design §1) is only assumed there.  The delivered route
(`Work.FTS.Physical.vorticityEquation_of_meridian`) produces the *global* `VorticityEquation` from a
global `MeridianEq`; here we need the *pointwise* version.

## Contents

* `directionalDeriv_swirl_cylField_at`, `directionalDeriv_cylField_swirl_at` — the two pointwise
  directional-derivative identities of `Work.CoreResiduals.VorticityEquation` (their global
  counterparts are stated with `∀ t r z` hypotheses; the proofs are pointwise verbatim);
* `vorticityEquation_at` — the pointwise scalar reduction: if the meridian residual vanishes at
  `(radial x, axial x, t)` and the meridian pair is differentiable there, then the `ℝ³` vorticity
  equation holds at `(x,t)` for the stream-function velocity and the swirl vorticity;
* `vorticityEquationOn_of_meridianEqOn` — the same for the data of the reconstruction: from
  `MeridianEqOn W ψ T`, `DiffAt2` of `W(·,·,t)` and `ContDiffAt ℝ 2` of `ψ(·,·,t)` off the axis and
  the plane, the pointwise vorticity equation holds at every `x ∈ Uax` and `t ∈ (0,T)`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.FireFix.PhysFields
import Submission.Work.CoreResiduals.VorticityEquation.vorticityEquation_cylField_iff_scalar
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.Physical.Meridian

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.FireFix

/-- **The pointwise `(u·∇)ω` identity** for a swirl vorticity and a no-swirl velocity field.  This
is `Work.CoreResiduals.VorticityEquation.directionalDeriv_swirl_cylField` with the `DiffAt2`
hypothesis required only at the point `(radial x, axial x)` (its proof only uses it there). -/
theorem directionalDeriv_swirl_cylField_at {ur uz W : ℝ → ℝ → ℝ → ℝ} {x : R3} {t : ℝ}
    (hW : Work.Cyl.DiffAt2 (fun r z => W r z t) (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    directionalDeriv
        (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
        (fun x t => Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) x t
      = (ur (Work.Cyl.radial x) (Work.Cyl.axial x) t
            * Work.Cyl.pdR (fun r' z' => W r' z' t) (Work.Cyl.radial x) (Work.Cyl.axial x)
          + uz (Work.Cyl.radial x) (Work.Cyl.axial x) t
            * Work.Cyl.pdZ (fun r' z' => W r' z' t) (Work.Cyl.radial x) (Work.Cyl.axial x))
        • Work.Cyl.eTheta x := by
  rw [directionalDeriv]
  have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
  have hG : Work.Cyl.DiffAt2 (fun r z => W r z t) (Work.Cyl.radial x) (Work.Cyl.axial x) := hW
  have hrad : DifferentiableAt ℝ Work.Cyl.radial x := Work.Cyl.differentiableAt_radial x hrne
  have hax : DifferentiableAt ℝ Work.Cyl.axial x := Work.Cyl.differentiableAt_axial x
  have hΦ : DifferentiableAt ℝ (fun y : R3 => (Work.Cyl.radial y, Work.Cyl.axial y)) x :=
    hrad.prodMk hax
  have hc : DifferentiableAt ℝ (fun y : R3 => W (Work.Cyl.radial y) (Work.Cyl.axial y) t) x :=
    DifferentiableAt.comp (g := fun p : ℝ × ℝ => W p.1 p.2 t) x hG hΦ
  have hf : DifferentiableAt ℝ (fun y : R3 => Work.Cyl.eTheta y) x := by
    have h1 : DifferentiableAt ℝ (fun y : R3 => (Work.Cyl.radial y)⁻¹) x := hrad.inv hrne
    have h2 : DifferentiableAt ℝ (fun y : R3 => Work.Cyl.angularVec y) x :=
      Work.CoreResiduals.VorticityEquation.differentiableAt_angularVec x
    have h := h1.smul h2
    convert h using 1
    funext y
    simp [Work.Cyl.eTheta, one_div]
  rw [fderiv_fun_smul hc hf]
  rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [Work.CoreResiduals.VorticityEquation.fderiv_eTheta_cylField_eq_zero
    (fun r z => ur r z t) (fun r z => uz r z t) x hr]
  rw [Work.CoreResiduals.VorticityEquation.fderiv_comp_radial_axial (fun r z => W r z t) x
        (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) hG hr]
  have hsq : x 0 ^ 2 + x 1 ^ 2 = Work.Cyl.radial x ^ 2 := (Work.Cyl.radial_sq x).symm
  have hv0 : (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 0
      = ur (Work.Cyl.radial x) (Work.Cyl.axial x) t * x 0 / Work.Cyl.radial x :=
    Work.Cyl.cylField_zero _ _ x
  have hv1 : (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 1
      = ur (Work.Cyl.radial x) (Work.Cyl.axial x) t * x 1 / Work.Cyl.radial x :=
    Work.Cyl.cylField_one _ _ x
  have hdot' : x 0 * (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 0
      + x 1 * (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 1
      = ur (Work.Cyl.radial x) (Work.Cyl.axial x) t * Work.Cyl.radial x := by
    rw [hv0, hv1]; field_simp; rw [hsq]
  have hdot : (x 0 * (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 0
      + x 1 * (Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x) 1) / Work.Cyl.radial x
      = ur (Work.Cyl.radial x) (Work.Cyl.axial x) t := by
    rw [hdot']; field_simp
  rw [hdot, Work.Cyl.cylField_two]
  simp only [smul_zero, zero_add]
  congr 1
  ring

/-- **The pointwise `(ω·∇)u` identity**; pointwise version of
`Work.CoreResiduals.VorticityEquation.directionalDeriv_cylField_swirl`. -/
theorem directionalDeriv_cylField_swirl_at {ur uz W : ℝ → ℝ → ℝ → ℝ} {x : R3} {t : ℝ}
    (hu : Work.Cyl.DiffAt2 (fun r z => ur r z t) (Work.Cyl.radial x) (Work.Cyl.axial x) ∧
      Work.Cyl.DiffAt2 (fun r z => uz r z t) (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hr : 0 < Work.Cyl.radial x) :
    directionalDeriv
        (fun x t => Work.Cyl.cylField (fun r z => ur r z t) (fun r z => uz r z t) x)
        (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
      = (W (Work.Cyl.radial x) (Work.Cyl.axial x) t
          * (ur (Work.Cyl.radial x) (Work.Cyl.axial x) t / Work.Cyl.radial x)) • Work.Cyl.eTheta x := by
  rw [directionalDeriv]
  rw [map_smul, Work.CoreResiduals.VorticityEquation.fderiv_cylField_eTheta
        (fun r z => ur r z t) (fun r z => uz r z t) x hu.1 hu.2 hr]
  simp only [smul_smul, Work.Cyl.redR]

/-- **The pointwise scalar reduction of the `ℝ³` vorticity equation.**  If the meridian residual of
`(W, ψ)` vanishes at `(radial x, axial x, t)` and the meridian pair is differentiable there, then
the `ℝ³` vorticity equation holds at `(x,t)` for the stream-function velocity
`psiField (ψ · t)` and the swirl vorticity `W(radial x, axial x, t) • e_θ(x)`. -/
theorem vorticityEquation_at {W ψ : ℝ → ℝ → ℝ → ℝ} {x : R3} {t : ℝ}
    (hr : 0 < Work.Cyl.radial x)
    (hW : Work.Cyl.DiffAt2 (fun r z => W r z t) (Work.Cyl.radial x) (Work.Cyl.axial x))
    (hψC : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2 t)
      (Work.Cyl.radial x, Work.Cyl.axial x))
    (hres : Work.CoreResiduals.meridianResid W ψ (Work.Cyl.radial x) (Work.Cyl.axial x) t = 0) :
    timeDeriv (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
      + directionalDeriv (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
          (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x) x t
      = directionalDeriv (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x)
          (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t := by
  have hψd : DifferentiableAt ℝ (fun p : ℝ × ℝ => ψ p.1 p.2 t)
      (Work.Cyl.radial x, Work.Cyl.axial x) := hψC.differentiableAt (by norm_num)
  have hu1 : Work.Cyl.DiffAt2 (fun r z => Work.Cyl.pdZ (fun r' z' => ψ r' z' t) r z)
      (Work.Cyl.radial x) (Work.Cyl.axial x) :=
    Work.Cyl.differentiableAt_pdZ (fun r' z' => ψ r' z' t) _ _ hψC
  have hu2 : Work.Cyl.DiffAt2
      (fun r z => -(ψ r z t / r) - Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z)
      (Work.Cyl.radial x) (Work.Cyl.axial x) := by
    have hrne : Work.Cyl.radial x ≠ 0 := ne_of_gt hr
    have h1 : Work.Cyl.DiffAt2 (fun r z => Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z)
        (Work.Cyl.radial x) (Work.Cyl.axial x) :=
      Work.Cyl.differentiableAt_pdR (fun r' z' => ψ r' z' t) _ _ hψC
    have h2 : DifferentiableAt ℝ
        (fun p : ℝ × ℝ => ψ p.1 p.2 t * (p.1)⁻¹) (Work.Cyl.radial x, Work.Cyl.axial x) :=
      hψd.mul (differentiableAt_fst.inv (by simpa using hrne))
    exact h2.neg.sub h1
  have hpsi : (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x)
      = fun x t => Work.Cyl.cylField (fun r z => Work.Cyl.pdZ (fun r' z' => ψ r' z' t) r z)
          (fun r z => -(ψ r z t / r) - Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z) x := by
    funext y s
    simp only [Work.Cyl.psiField]
  rw [hpsi]
  rw [Work.CoreResiduals.VorticityEquation.timeDeriv_swirl (W := W) x t,
    directionalDeriv_swirl_cylField_at (W := W) (ur := fun r z t => Work.Cyl.pdZ
      (fun r' z' => ψ r' z' t) r z)
      (uz := fun r z t => -(ψ r z t / r) - Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z) hW hr,
    directionalDeriv_cylField_swirl_at (W := W) (ur := fun r z t => Work.Cyl.pdZ
      (fun r' z' => ψ r' z' t) r z)
      (uz := fun r z t => -(ψ r z t / r) - Work.Cyl.pdR (fun r' z' => ψ r' z' t) r z)
      ⟨hu1, hu2⟩ hr, ← add_smul]
  congr 1
  rw [← add_assoc]
  simp only [Work.CoreResiduals.meridianResid] at hres
  linarith

/-- **Transport of the pointwise vorticity equation along a change of the pair `(u,ω)`.**  If the
velocity fields agree near `x` and the vorticity fields agree identically, the equation transfers
(both `timeDeriv` and `directionalDeriv` only see the pointwise values). -/
theorem vorticityEquation_transfer {u v ω η : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (huv : (fun y => u y t) =ᶠ[𝓝 x] (fun y => v y t)) (hωη : ω = η)
    (h : timeDeriv η x t + directionalDeriv η v x t = directionalDeriv v η x t) :
    timeDeriv ω x t + directionalDeriv ω u x t = directionalDeriv u ω x t := by
  have h1 : timeDeriv ω x t = timeDeriv η x t := by rw [hωη]
  have h2 : directionalDeriv ω u x t = directionalDeriv η v x t := by
    show fderiv ℝ (fun y => ω y t) x (u x t) = fderiv ℝ (fun y => η y t) x (v x t)
    rw [show (fun y => ω y t) = (fun y => η y t) from by funext y; rw [hωη],
      huv.eq_of_nhds]
  have h3 : directionalDeriv u ω x t = directionalDeriv v η x t := by
    show fderiv ℝ (fun y => u y t) x (ω x t) = fderiv ℝ (fun y => v y t) x (η x t)
    rw [huv.fderiv_eq, show ω x t = η x t from by rw [hωη]]
  rw [h1, h2, h3]
  exact h

/-- **The pointwise vorticity equation of the reconstruction.**  From the meridian equation on the
window `(0,T)` (`Work.FTS.MeridianDyn.MeridianEqOn`) and the two differentiability clauses of the
design (`hW`, `hΨ`), the `ℝ³` vorticity equation holds at every `x ∈ Uax` and every `t ∈ (0,T)`. -/
theorem vorticityEquationOn_of_meridianEqOn {W ψ : ℝ → ℝ → ℝ → ℝ} {T : ℝ}
    (hmer : Work.FTS.MeridianDyn.MeridianEqOn W ψ T)
    (hW : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      Work.Cyl.DiffAt2 (fun r z => W r z t) r z)
    (hΨ : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ r z : ℝ, 0 < r → z ≠ 0 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => ψ p.1 p.2 t) (r, z)) :
    ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x ∈ Work.FTS.PressureOn.Uax,
      timeDeriv (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t
        + directionalDeriv
            (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x)
            (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x) x t
        = directionalDeriv (fun x t => Work.Cyl.psiField (fun r z => ψ r z t) x)
            (fun x t => W (Work.Cyl.radial x) (Work.Cyl.axial x) t • Work.Cyl.eTheta x) x t := by
  intro t ht x hx
  have hr : 0 < Work.Cyl.radial x := by
    rcases eq_or_lt_of_le (Work.Cyl.radial_nonneg x) with h | h
    · exfalso
      have h01 : x 0 = 0 ∧ x 1 = 0 := (Work.Cyl.radial_eq_zero_iff x).mp h.symm
      exact hx.2 (by rw [h01.1, h01.2]; norm_num)
    · exact h
  exact vorticityEquation_at (hr := hr) (hW := hW t ht _ _ hr hx.1)
    (hψC := hΨ t ht _ _ hr hx.1) (hres := hmer _ _ t hr hx.1 ht)

end Work.FTS.FireFix
