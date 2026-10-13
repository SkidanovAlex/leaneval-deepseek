import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row11Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP

set_option autoImplicit false

/-- The open quadrant of `SmoothPos`: `z > 0`, `0 < θ < π/2`. -/
private abbrev Sp : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)

private theorem isOpen_Sp : IsOpen Sp := isOpen_Ioi.prod isOpen_Ioo

private theorem cos_ne_zero_Sp : ∀ p ∈ Sp, Real.cos p.2 ≠ 0 := by
  intro p hp
  have h := Set.mem_Ioo.mp hp.2
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1, Real.pi_pos], h.2⟩)

/-- `ℛ` preserves smoothness on the open quadrant `Sp`: the only point is that the division by
`cos θ` is legitimate there (it is strictly positive on `(0,π/2)`). -/
private theorem contDiffOn_Rop_Sp {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Ψ) Sp) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.Rop α Ψ)) Sp := by
  have hpz := Work.FTS.LocData.contDiffOn_pz isOpen_Sp hΨ
  have hpth := Work.FTS.LocData.contDiffOn_pth isOpen_Sp hΨ
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin p.2) Sp :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hcos : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2) Sp :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p) Sp :=
    (contDiffOn_const.mul hsin).mul hΨ
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p) Sp :=
    ((contDiffOn_const.mul hsin).mul contDiffOn_fst).mul hpz
  have h3 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) Sp :=
    hcos.mul hpth
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => 2 * Real.sin p.2 * Function.uncurry Ψ p
        + α * Real.sin p.2 * p.1 * Function.uncurry (Work.Spaces.pz Ψ) p
        + Real.cos p.2 * Function.uncurry (Work.Spaces.pth Ψ) p) Sp :=
    (h1.add h2).add h3
  refine (hnum.div hcos (fun p hp => cos_ne_zero_Sp p hp)).congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

/-- `Θ_*(α) = (1/(4α)) sin(2θ) L₁₂(F_*)` is smooth on `Sp`, because the profile identity
`L₁₂(F_*)(z) = 2α/(1+z)` (valid for `z > -1`) turns it into the explicit
`sin(2θ)/(2(1+z))`. -/
private theorem contDiffOn_Theta_Fstar_Sp {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.Theta α (Work.Construction.Fstar α))) Sp := by
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => Real.sin (2 * p.2) / (2 * (1 + p.1))) Sp := by
    have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Sp :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have hden : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => 2 * (1 + p.1)) Sp :=
      contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst)
    have hne : ∀ p ∈ Sp, 2 * (1 + p.1) ≠ 0 := by
      intro p hp
      have hp1 : (0 : ℝ) < 1 + p.1 := by
        have := Set.mem_Ioi.mp hp.1; linarith
      positivity
    exact hnum.div hden hne
  refine hsmooth.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hz : -1 < z := by have := Set.mem_Ioi.mp hp.1; linarith
  simp only [Function.uncurry, Work.Construction.Theta, Work.Construction.s2]
  rw [Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hz]
  field_simp
  ring

/-- `Φ̃_* = Φ_s - Θ_*(α)` is smooth on `Sp` whenever `Φ_s` is. -/
private theorem contDiffOn_PhiTil_Sp {α : ℝ} {Φs : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hΦ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Φs) Sp) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) Sp := by
  have hθ := contDiffOn_Theta_Fstar_Sp (α := α) hα hα1
  refine (hΦ.sub hθ).congr ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  rfl

theorem Rv_smooth {α Cs : ℝ} {Φs : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (h : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    Work.FTS.Nonlinear.Pieces.RNP.SmoothPos (fun z θ => 2 * Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs z θ) ∧
    (∀ z ∈ Set.Ici (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ContDiffAt ℝ 4 (fun θ' => 2 * Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs z θ') θ) := by
  have hΦ : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry Φs) Sp :=
    h.smooth.mono (fun p hp => ⟨Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hp.1]), hp.2⟩)
  have hΨ : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)) Sp :=
    contDiffOn_PhiTil_Sp (α := α) hα hα1 hΦ
  have hR : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Construction.Rop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs))) Sp :=
    contDiffOn_Rop_Sp hΨ
  have hnum : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => (2 * (p.1 + 1)) / p.1) Sp := by
    refine ContDiffOn.div ?_ ?_ ?_
    · exact (contDiffOn_const.mul (contDiffOn_fst.add contDiffOn_const))
    · exact contDiffOn_fst
    · intro p hp; exact ne_of_gt (Set.mem_Ioi.mp hp.1)
  have hP : Work.FTS.Nonlinear.Pieces.RNP.SmoothPos
      (fun z θ => 2 * Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs z θ) := by
    show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => 2 * Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs z θ)) Sp
    refine (hnum.mul hR).congr ?_
    intro p _
    obtain ⟨z, θ⟩ := p
    show 2 * Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs z θ
      = ((2 * (z + 1)) / z) * Work.Construction.Rop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
    simp only [Work.FTS.Nonlinear.Pieces.RNP.Rv]
    ring
  refine ⟨hP, ?_⟩
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have hconst : (fun θ' : ℝ => 2 * Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs 0 θ')
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ'
      simp [Work.FTS.Nonlinear.Pieces.RNP.Rv]
    rw [hconst]
    exact contDiffAt_const
  · have hAt : ContDiffAt ℝ Work.Stability.smoothOrder
        (Function.uncurry (fun z θ => 2 * Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs z θ))
        (z, θ) :=
      hP.contDiffAt (isOpen_Sp.mem_nhds ⟨hzpos, hθ⟩)
    have hslice : ContDiffAt ℝ Work.Stability.smoothOrder
        (fun θ' : ℝ => Function.uncurry
          (fun z θ => 2 * Work.FTS.Nonlinear.Pieces.RNP.Rv α Φs z θ) (z, θ')) θ :=
      hAt.comp θ (contDiffAt_const.prodMk contDiffAt_id)
    exact hslice.of_le (by simp [Work.Stability.smoothOrder])

end Work.FTS.Nonlinear.Pieces.RNP
