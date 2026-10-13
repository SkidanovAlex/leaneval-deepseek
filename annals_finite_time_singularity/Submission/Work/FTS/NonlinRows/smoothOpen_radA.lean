import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row11Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/- Open-quadrant infrastructure for the primed star rows (`N1ss = 2ℛ(Φ̃_*)F_*`, row 11, and
row 10's `2ℛ(Φ̃_*)g`): the radial factor `radA = ℛ(Φ̃_*)·z/(1+z)²` of `N1ss = (2Bv(θ))·radA` is
`C^∞` on the open quadrant from `StarPkgo.smooth`, and the weighted factor relevant to
`StarPkg.R`/`StarPkgo.R` is `(z+1)³/z²·radA = ((z+1)/z)·ℛ(Φ̃_*)`.

This is the `SmoothOpen` counterpart of the pair `smoothQuad_radA` / `weighted_eq_Rv` of
`Submission/Work/FTS/Nonlinear/Pieces/RNPV2/row11.lean` (`SmoothQuad` class).  The smoothness part
uses `L12 (Fstar α) z = 2α/(1+z)` (`FstarPkg/L12_Fstar_eq_of_gt_neg_one`, hence `0 < α ≤ 1`), so
that `Theta α (Fstar α) = sin(2θ)/(2(1+z))` is smooth on the open quadrant, and the identity part is
the pointwise `field_simp`/`ring` computation of `weighted_eq_Rv`. -/

/-! ## The two auxiliary `SmoothOpen` facts

The open-quadrant analogues of `smoothQuad_Theta_Fstar` and `smoothQuad_Rop` of
`Submission/Work/FTS/Nonlinear/Pieces/RNP/N1ss_smoothQuad.lean` (which are stated for the
*analytic* class `LocData.SmoothQuad`, unusable here since `SmoothOpen` is only `C^∞` on the
open quadrant). -/

/-- **`Θ_*(α) = Θ α (F_*)` is `C^∞` on the open quadrant.**  By the profile identity
`L₁₂(F_*)(z) = 2α/(1+z)` (valid for every `z > -1`, hence on `Q0`) it is the explicit function
`(z,θ) ↦ sin(2θ)/(2(1+z))`, smooth on `Q0` because `1 + z > 0` there. -/
theorem smoothOpen_Theta_Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) := by
  have hsmooth : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => Real.sin (2 * θ) / (2 * (1 + z))) := by
    change ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1)))
      Work.FTS.EllipticEst.Q0
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * (1 + p.1)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, 2 * (1 + p.1) ≠ 0 := by
      intro p hp
      have hp1 : (0 : ℝ) < 1 + p.1 := by
        have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
        linarith
      positivity
    exact hnum.div hden hne
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl hsmooth ?_
  intro z θ hz0 hθ0 hθ1
  have hz : -1 < z := by linarith
  have hα0 : α ≠ 0 := ne_of_gt hα
  have h1z : (1 + z : ℝ) ≠ 0 := by positivity
  show Real.sin (2 * θ) / (2 * (1 + z))
      = Work.Construction.Theta α (Work.Construction.Fstar α) z θ
  simp only [Work.Construction.Theta, Work.Construction.s2]
  rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hz]
  field_simp
  ring

/-- **The operator `ℛ` preserves `C^∞`-smoothness on the open quadrant.**  The only point to
check is that the division by `cos θ` is legitimate there (`cos θ > 0` for `0 < θ < π/2`); all
the remaining factors are `sin θ`, `cos θ`, `z`, the datum `Ψ` and its two first derivatives
(`SmoothOpen.pz`, `SmoothOpen.pth`). -/
theorem smoothOpen_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ψ) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (Work.Construction.Rop α Ψ)) Work.FTS.EllipticEst.Q0
  have hΨ' : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ)
      Work.FTS.EllipticEst.Q0 := hΨ
  have hpz : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.pz hΨ
  have hpth : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.SmoothOpen.pth hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul hsin).mul hΨ'
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const.mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p)
      Work.FTS.EllipticEst.Q0 :=
    hcos.mul hpth
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) Work.FTS.EllipticEst.Q0 :=
    (h1.add h2).add h3
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  refine (hnum.div hcos hne).congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-- **`Φ̃_* = Φ_* - Θ_*(α)` is `C^∞` on the open quadrant**, from `StarPkgo.smooth` and
`smoothOpen_Theta_Fstar`. -/
theorem smoothOpen_PhiTs {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) := by
  have hTheta : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Theta α (Work.Construction.Fstar α)) :=
    smoothOpen_Theta_Fstar hα hα1
  have hmain : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl hs.smooth hTheta
  refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl (f := fun z θ : ℝ =>
    Φs z θ - Work.Construction.Theta α (Work.Construction.Fstar α) z θ) hmain ?_
  intro z θ _ _ _
  rfl

/-- The rational factor `z/(1+z)²` of `radA` is `C^∞` on the open quadrant. -/
theorem smoothOpen_rat_z :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z) ^ 2) := by
  change ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1)
      Work.FTS.EllipticEst.Q0 := contDiffOn_fst
  have hden : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (1 + p.1) ^ 2) Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.add contDiffOn_fst).pow 2
  have hne : ∀ p ∈ Work.FTS.EllipticEst.Q0, (1 + p.1) ^ 2 ≠ 0 := by
    intro p hp
    have hp1 : (0 : ℝ) < 1 + p.1 := by
      have := (Work.FTS.EllipticEst.mem_Q0.mp hp).1
      linarith
    positivity
  exact hnum.div hden hne

theorem smoothOpen_radA {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * z / (1 + z) ^ 2) ∧
    (fun z θ => (z + 1) ^ 3 / z ^ 2
        * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * z / (1 + z) ^ 2))
      = (fun z θ => (z + 1) / z
          * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) := by
  constructor
  · have hPhi : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
      smoothOpen_PhiTs hα hα1 hs
    have hRop : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) := smoothOpen_Rop hPhi
    have hrat : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z) ^ 2) :=
      smoothOpen_rat_z
    have hprod : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ : ℝ => Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          * (z / (1 + z) ^ 2)) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hRop hrat
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl (f := fun z θ : ℝ =>
      Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * (z / (1 + z) ^ 2)) hprod ?_
    intro z θ _ _ _
    rw [mul_div_assoc']
  · funext z θ
    show (z + 1) ^ 3 / z ^ 2
          * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ * z / (1 + z) ^ 2)
        = (z + 1) / z * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
    rcases eq_or_ne z 0 with rfl | hz
    · norm_num
    · rcases eq_or_ne (1 + z) 0 with h1 | h1
      · have hz1 : z = -1 := by linarith
        rw [hz1]
        norm_num
      · field_simp
        ring

end Work.FTS.NonlinRows
