import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.omega_facts
import Submission.Work.Spaces.c_bounds
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false

/-! ## The three factorisations of the reference profile `F_*`

With `β = pExp α = 3α`, `Γ(θ) = Gam β θ = (sin θ cos²θ)^α`, `c = c β` and
`F̂ = FM.Fstar = 2z/(1+z)²`, the reference profile is

  `F_* = β·(Γ/c)·F̂ = (β/c)·Γ·F̂`

and its two first-order derivatives factor as

* `D_z F_* = (β/c)·Γ·(z F̂')`,  `z F̂'(z) = 2z(1-z)/(1+z)³`;
* `sin(2θ)·∂_θF_* = (β/c)·Γ·((2β/3)·c2m θ·F̂)`,  `c2m θ = cos 2θ - sin²θ`.

The second is the statement `∂_θΓ = Γ·2α·c2m θ/sin 2θ` (`Work.FTS_RegExport.RXT.hasDerivAt_Gamma`,
which is stated for `Work.FTS.Regularity.Gamma α = Gam (pExp α)`) times the factor `2β/3 = 2α`.
Multiplying by `sin 2θ` clears the angular singularity at the two endpoints of the identity; the
identity itself is used only on the open interval `(0, π/2)` where `sin 2θ ≠ 0`. -/

/-- `F_*(pExp α) = (β/c)·Γ·F̂` with `β = pExp α`. -/
private lemma Fs_coeff (α z θ : ℝ) :
    Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ * Work.FM.Fstar z := by
  simp only [Work.Construction.Fstar]
  ring

/-- `D_z F_* = (β/c)·Γ·(2z(1-z)/(1+z)³)`. -/
private lemma Dz_Fs_coeff {α z θ : ℝ} (hz : 0 < z) :
    Work.Spaces.Dz (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * (2 * z * (1 - z) / (1 + z) ^ 3) := by
  have hslice : (fun z' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ)
      = fun z' => (Work.FTS.Regularity.pExp α
            * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp α))) * Work.FM.Fstar z' := by
    funext z'; simp only [Work.Construction.Fstar]
  have hd : DifferentiableAt ℝ Work.FM.Fstar z :=
    (Work.FM.hasDerivAt_Fstar z (by linarith)).differentiableAt
  rw [Work.Spaces.Dz, Work.Spaces.pz, hslice, deriv_const_mul _ hd,
    Work.FM.deriv_Fstar z (by linarith)]
  ring

/-- `sin(2θ)·∂_θF_* = (β/c)·Γ·((2β/3)·c2m θ·F̂)`. -/
private lemma sin_pth_Fs_coeff {α z θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Real.sin (2 * θ) * Work.Spaces.pth
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * ((2 * Work.FTS.Regularity.pExp α / 3) * Work.Construction.c2m θ
            * (2 * z / (1 + z) ^ 2)) := by
  have hGam : HasDerivAt (fun θ' : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ')
      (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ))) θ := by
    have h := Work.FTS_RegExport.RXT.hasDerivAt_Gamma α θ hθ0 hθ1
    have hfun : (fun θ' : ℝ => Work.FTS.Regularity.Gamma α θ')
        = fun θ' => Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ' := by
      funext θ'; exact Work.FTS.Regularity.Gamma_eq_Gam α θ'
    rwa [hfun, Work.FTS.Regularity.Gamma_eq_Gam α θ] at h
  have hslice : (fun θ' : ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ')
      = fun θ' => (Work.FTS.Regularity.pExp α * Work.FM.Fstar z
            / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ' := by
    funext θ'; simp only [Work.Construction.Fstar]; ring
  have hpth : Work.Spaces.pth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      = (Work.FTS.Regularity.pExp α * Work.FM.Fstar z
            / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ))) := by
    rw [Work.Spaces.pth, hslice, deriv_const_mul _ hGam.differentiableAt, hGam.deriv]
  rw [hpth]
  have hs : Real.sin (2 * θ) ≠ 0 := by
    apply ne_of_gt
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ1, Real.pi_pos])
  have h2 : 2 * Work.FTS.Regularity.pExp α / 3 = 2 * α := by
    simp only [Work.FTS.Regularity.pExp]; ring
  rw [h2]
  calc Real.sin (2 * θ) * ((Work.FTS.Regularity.pExp α * Work.FM.Fstar z
          / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ))))
      = (Work.FTS.Regularity.pExp α * Work.FM.Fstar z
          / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * (Real.sin (2 * θ) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ)))) := by ring
    _ = (Work.FTS.Regularity.pExp α * Work.FM.Fstar z
          / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          * (2 * α * Work.Construction.c2m θ)) := by
        rw [show Real.sin (2 * θ) * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ)))
            = Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
              * (Real.sin (2 * θ) * (2 * α * Work.Construction.c2m θ
                / Real.sin (2 * θ))) by ring,
          mul_div_cancel₀ _ hs]
    _ = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
        * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
        * (2 * α * Work.Construction.c2m θ * (2 * z / (1 + z) ^ 2)) := by
        simp only [Work.FM.Fstar]; ring

/-- **The reduced form of the forcing.**  With `β = pExp α`, `Γ = Gam (pExp α)`, `c = Spaces.c β`,
`F_* = Fstar β = β(Γ/c)·(2z/(1+z)²)`, the forcing
`Σ = VR·D_zF_* + Vθ7·∂_θF_* + cR·F_*` equals `(β/c)·Γ` times the explicit combination
`VR·(z·F̂') + bR·((2β/3)c2m·F̂) + cR·F̂` of the three coefficients, where `zF̂' = 2z(1-z)/(1+z)³`
and `F̂ = 2z/(1+z)²`: this uses `D_zF_* = (β/c)·Γ·zF̂'` and
`∂_θF_* = (β/c)·Γ·(2β/3)c2m·F̂/sin 2θ` together with `Vθ7 = sin 2θ·bR`. -/
theorem SigR_eq_reduced {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} :
    ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.RegExportIface.RXT.SigR α Φs E g σ z θ
        = (Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          * (Work.FTS.RegExportIface.RXT.VR α Φs E g z θ σ * (2 * z * (1 - z) / (1 + z) ^ 3)
            + Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
              * ((2 * Work.FTS.Regularity.pExp α / 3) * Work.Construction.c2m θ
                * (2 * z / (1 + z) ^ 2))
            + Work.FTS.RegExportIface.RXT.cR α Φs E g z θ σ * (2 * z / (1 + z) ^ 2)) := by
  intro σ hσ z θ hz hθ0 hθ1
  -- the angular weight is nonzero on the open interval, so `bR = Vθ7/sin 2θ` inverts
  have hs : Real.sin (2 * θ) ≠ 0 := by
    apply ne_of_gt
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ1, Real.pi_pos])
  have hU : Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ
      = Real.sin (2 * θ) * Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ := by
    show Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ
      = Real.sin (2 * θ) * (Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ / Real.sin (2 * θ))
    rw [mul_div_cancel₀ _ hs]
  -- the `∂_θF_*`-slot in terms of `bR`
  have hmid : Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) z θ σ
      * Work.Spaces.pth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
      = Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
        * ((Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
          * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          * ((2 * Work.FTS.Regularity.pExp α / 3) * Work.Construction.c2m θ
            * (2 * z / (1 + z) ^ 2))) := by
    rw [hU]
    calc (Real.sin (2 * θ) * Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ)
          * Work.Spaces.pth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
        = Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
          * (Real.sin (2 * θ) * Work.Spaces.pth
              (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ) := by ring
      _ = Work.FTS.RegExportIface.RXT.bR α Φs E g z θ σ
          * ((Work.FTS.Regularity.pExp α / Work.Spaces.c (Work.FTS.Regularity.pExp α))
            * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
            * ((2 * Work.FTS.Regularity.pExp α / 3) * Work.Construction.c2m θ
              * (2 * z / (1 + z) ^ 2))) := by
          rw [sin_pth_Fs_coeff hθ0 hθ1]
  rw [Work.FTS.RegExportIface.RXT.SigR, Dz_Fs_coeff hz, Fs_coeff, hmid]
  simp only [Work.FM.Fstar]
  ring

end Work.FTS_RegExport.RXT.SysAux
