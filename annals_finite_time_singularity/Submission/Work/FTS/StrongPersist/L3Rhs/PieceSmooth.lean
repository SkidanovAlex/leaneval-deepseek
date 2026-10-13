import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.NRow11
import Submission.Work.FTS.NonlinRows.NRow15T2
import Submission.Work.FTS.NonlinRows.NRow19T2
import Submission.Work.FTS.Nonlinear.Open.Row23
import Submission.Work.FTS.Nonlinear.Open.Row26

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
set_option linter.unusedVariables false

/-! ## Elementary smoothness of the explicit angular and radial factors

The five summands of `NSsSum` are built out of the following factors, each of which is `C^∞` on
the open quadrant `(0,∞) × (0,π/2)` for elementary reasons:

* the angular factors `s2 θ = sin 2θ` and `sin²θ`;
* the radial factor `FK (F_*) z = α·2z/(1+z)²` (`Work.FTS.Nonlinear.FstarPkg.FK_Fstar`);
* the profile `F_* = α(Γ/c)·2z/(1+z)²` (`Work.FTS.LocData.SmoothQuad_Fstar`);
* the star residual `Φ̃_* = Φ_* - Θ_*(α)` (`Work.FTS.NonlinRows.smoothOpen_PhiTs`),
  and the coefficient fields `ℛ(Φ̃_*)`, `𝒰(Φ̃_*)`, `𝒱(Φ̃_*)` built from it. -/

/-- `s2 θ = sin(2θ)` is `C^∞` on the open quadrant. -/
theorem smoothOpen_s2 :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) := by
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo 0 (π / 2)) :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have h2 := Work.FTS.NonlinRows.smoothOpen_theta_only (a := fun θ : ℝ => Real.sin (2 * θ)) h
  simpa only [Work.Construction.s2] using h2

/-- `sin²θ` is `C^∞` on the open quadrant. -/
theorem smoothOpen_sin_sq :
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.sin θ ^ 2) := by
  refine Work.FTS.NonlinRows.smoothOpen_theta_only (a := fun θ : ℝ => Real.sin θ ^ 2) ?_
  have h : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin θ)
      (Set.Ioo 0 (π / 2)) := Real.contDiff_sin.contDiffOn
  simpa only [Pi.pow_apply] using h.pow 2

/-- **`FK (F_*)` is a `C^∞` radial function.**  By `FK_Fstar` it is the explicit function
`z ↦ α·2z/(1+z)²`, which is smooth on `(0,∞)` (indeed on `(-1,∞)`). -/
theorem smoothOpen_FK_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) := by
  have hrad : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => 2 * z / (1 + z) ^ 2) := by
    refine Work.FTS.NonlinRows.smoothOpen_z_only (r := fun z : ℝ => 2 * z / (1 + z) ^ 2) ?_
    exact ContDiffOn.div (contDiffOn_const.mul contDiffOn_id)
      ((contDiffOn_const.add contDiffOn_id).pow 2) (fun z hz => by
        have h1 : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
        positivity)
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (f := fun z (_ : ℝ) => α * (2 * z / (1 + z) ^ 2))
    (Work.FTS.NonlinRows.smoothOpen_const_mul α hrad) ?_
  intro z _ _ _ _
  exact (Work.FTS.Nonlinear.FstarPkg.FK_Fstar (α := α) (z := z) hα hα1).symm

/-- **Smoothness of the five `ss` pieces**: for `0 < α ≤ 1` and star data
`StarPkgo2 α Cs Φs`, each of the five summands of
`Work.FTS.StrongPersist.L3Rhs.NSsSum α Φs` is `C^∞` on the open quadrant `Q0` (all finite
orders, i.e. `Work.FTS.EllipticEst.SmoothOpen`), the profile-only pieces `N4ss α`, `N5ss α`
being independent of the star data.

The three star pieces reduce to `StarPkgo.smooth : SmoothOpen Φs` together with the explicit
smoothness of `Theta α (Fstar α)`, `Work.Spaces.c α`, `Work.Spaces.Gam α`, `s2`, `FK (Fstar α)`
and `Work.Spaces.pz`-slices of those.  The two profile pieces are products `a θ * r z` of an
angular-only and a radial-only `C^∞` function on `(0,π/2)` resp. `(0,∞)`; the angular factors are
`D_θ`-iterates of `sin²θ · Γ`, whose smoothness is `row23_smoothOpen_dthU_Gam`, and the radial
factor is `Work.Spaces.hKer`-based (`row23_contDiffOn_hKer`,
`Work.FTS.NonlinRows.smoothOpen_radial`).  This bundle is a tool for the `ℋ³`-norm assembly of
`L3RhsNssBlock` (`HkNorm_add_le`, `HkMem_mono_open`, and the `ContDiffOn ℝ 3` conjunct all need
it), not an estimate. -/
theorem PieceSmooth : ∀ α ∈ Set.Ioc 0 1, ∀ (Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N1ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N3ss α Φs) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N4ss α) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N5ss α) := by
  intro α hαIoc Cs Φs hs
  obtain ⟨hα, hα1⟩ : 0 < α ∧ α ≤ 1 := hαIoc
  have hsO : Work.FTS.VocabO.StarPkgo α Cs Φs := hs.toStarPkgo
  -- the star residual, the profile, and the angular moment
  have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hsO
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hFK : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    smoothOpen_FK_Fstar hα hα1
  -- the three coefficient fields
  have hRop : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hPhi
  have hUop : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Uop_PhiTs hα hα1 hsO
  have hVop : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Vop hPhi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `N₁^{**} = 2 ℛ(Φ̃_*) F_*`
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (f := fun z θ => 2 * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Construction.Fstar α z θ))
      (Work.FTS.NonlinRows.smoothOpen_const_mul 2
        (Work.FTS.NonlinRows.smoothOpen_mul hRop hF)) ?_
    intro z θ _ _ _
    simp only [Work.FTS.Nonlin.N1ss]
    ring
  · -- `N₂^{**} = -2 𝒰(Φ̃_*) ∂_θF_*`
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (f := fun z θ => -2 * (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ))
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-2)
        (Work.FTS.NonlinRows.smoothOpen_mul hUop hF.pth)) ?_
    intro z θ _ _ _
    simp only [Work.FTS.Nonlin.N2ss]
    ring
  · -- `N₃^{**} = -2α 𝒱(Φ̃_*) D_zF_*`
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (f := fun z θ => (-2 * α) * (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ))
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-2 * α)
        (Work.FTS.NonlinRows.smoothOpen_mul hVop hF.Dz)) ?_
    intro z θ _ _ _
    simp only [Work.FTS.Nonlin.N3ss]
    ring
  · -- `N₄^{**} = -(1/2) sin 2θ · FK(F_*) · ∂_θF_*`
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (f := fun z θ => (-(1 / 2)) * ((Work.Construction.s2 θ
        * Work.Construction.FK (Work.Construction.Fstar α) z)
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ))
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-(1 / 2))
        (Work.FTS.NonlinRows.smoothOpen_mul
          (Work.FTS.NonlinRows.smoothOpen_mul smoothOpen_s2 hFK) hF.pth)) ?_
    intro z θ _ _ _
    simp only [Work.FTS.Nonlin.N4ss]
    ring
  · -- `N₅^{**} = -sin²θ · FK(F_*) · F_*`
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (f := fun z θ => (-1) * ((Real.sin θ ^ 2
        * Work.Construction.FK (Work.Construction.Fstar α) z)
          * Work.Construction.Fstar α z θ))
      (Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
        (Work.FTS.NonlinRows.smoothOpen_mul
          (Work.FTS.NonlinRows.smoothOpen_mul smoothOpen_sin_sq hFK) hF)) ?_
    intro z θ _ _ _
    simp only [Work.FTS.Nonlin.N5ss]
    ring

end Work.FTS.StrongPersist.L3Rhs
