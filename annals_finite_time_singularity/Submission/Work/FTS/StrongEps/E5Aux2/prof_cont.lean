import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.E5Aux2.MuHGlue
import Submission.Work.FTS.StrongEps.E5Aux2.continuousOn_uncurry_transport
import Submission.Work.FTS.StrongEps.E5Aux2.prof_cont_ops
import Submission.Work.FTS.StrongEps.E5Aux2.prof_cont_moments
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Continuity of the elliptic-correction block `N` from `C¹` data

`N α F Φ` is an algebraic combination of the profile `F = F_* + w`, of its two moments
`z ↦ L₁₂(F)(z)` and `z ↦ FK(F)(z)`, and of the three transported coefficients
`ℛ(Φ̃)`, `𝒰(Φ̃)`, `𝒱(Φ̃)` of the residual stream function `Φ̃ = Φ - (1/(4α)) sin(2θ) L₁₂(F)`.

The contrast with `smoothOpen_N_gen` (`FTS/StrongEps/smoothOpen_dynRHS.lean`) is that the
stream function `Φ` is only *`C¹`* on the open quadrant — the case of the `ε`-scheme's limit
object — so the three coefficients are only continuous, not smooth.  Everything else is
smooth, and the only `Φ`-input is that `Φ̃` is `C¹` on the open quadrant (a `C¹` difference),
whose continuity feeds the coefficient lemma `prof_cont_ops`. -/

/-- **`N α F Φ` is continuous on the open quadrant from `C¹` data on `Φ`.** -/
theorem continuousOn_N_gen {α : ℝ} {F Φ : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hL12F : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 F z))
    (hFK : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK F z))
    (hΦ : ContDiffOn ℝ 1 (Function.uncurry Φ) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry (Work.Construction.N α F Φ))
      Work.FTS.EllipticEst.Q0 := by
  -- the singular part `Θ = (1/(4α)) sin(2θ) L₁₂(F)` is smooth
  have hTheta : ContDiffOn ℝ 1
      (Function.uncurry (Work.Construction.Theta α F)) Work.FTS.EllipticEst.Q0 := by
    have hs2 : Work.FTS.EllipticEst.SmoothOpen
        (fun _ (θ : ℝ) => Real.sin (2 * θ)) := Work.FTS.GalFields.RHS.smoothOpen_sin_two
    have h := (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hs2 hL12F)).forall 1
    refine h.congr ?_
    intro p hp
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.Construction.Theta, Work.Construction.s2]
    ring
  -- the residual `Φ̃ = Φ - Θ` is `C¹`, hence continuous
  have hPsi_c1 : ContDiffOn ℝ 1
      (Function.uncurry (Work.Construction.PhiTil α F Φ)) Work.FTS.EllipticEst.Q0 := by
    refine (hΦ.sub hTheta).congr ?_
    intro p hp
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry_apply_pair, Work.Construction.PhiTil]
  -- the three transported coefficients
  obtain ⟨hR, hU, hV⟩ := prof_cont_ops (α := α) hPsi_c1
  have hFc : ContinuousOn (Function.uncurry F) Work.FTS.EllipticEst.Q0 := hF.continuousOn
  have hpthF : ContinuousOn (Function.uncurry (Work.Spaces.pth F))
      Work.FTS.EllipticEst.Q0 := hF.pth.continuousOn
  have hDzF : ContinuousOn (Function.uncurry (Work.Spaces.Dz F))
      Work.FTS.EllipticEst.Q0 := hF.Dz.continuousOn
  have hFKc : ContinuousOn (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK F z))
      Work.FTS.EllipticEst.Q0 := hFK.continuousOn
  have hs2c : ContinuousOn (Function.uncurry (fun _ (θ : ℝ) => Work.Construction.s2 θ))
      Work.FTS.EllipticEst.Q0 := Work.FTS.GalFields.RHS.smoothOpen_sin_two.continuousOn
  have hsin2c : ContinuousOn (Function.uncurry (fun _ (θ : ℝ) => Real.sin θ ^ 2))
      Work.FTS.EllipticEst.Q0 := Work.FTS.GalFields.RHS.smoothOpen_sin_sq.continuousOn
  have t1 : ContinuousOn (fun p : ℝ × ℝ => 2 * Work.Construction.Rop α
      (Work.Construction.PhiTil α F Φ) p.1 p.2 * F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (continuousOn_const.mul hR).mul hFc
  have t2 : ContinuousOn (fun p : ℝ × ℝ => 2 * Work.Construction.Uop α
      (Work.Construction.PhiTil α F Φ) p.1 p.2 * Work.Spaces.pth F p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (continuousOn_const.mul hU).mul hpthF
  have t3 : ContinuousOn (fun p : ℝ × ℝ => 2 * α * Work.Construction.Vop
      (Work.Construction.PhiTil α F Φ) p.1 p.2 * Work.Spaces.Dz F p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_const (c := (2 : ℝ) * α)).mul hV).mul hDzF
  have t4 : ContinuousOn (fun p : ℝ × ℝ => (1 / 2) * Work.Construction.s2 p.2
      * Work.Construction.FK F p.1 * Work.Spaces.pth F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((continuousOn_const.mul hs2c).mul hFKc).mul hpthF
  have t5 : ContinuousOn (fun p : ℝ × ℝ => Real.sin p.2 ^ 2 * Work.Construction.FK F p.1
      * F p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    (hsin2c.mul hFKc).mul hFc
  have key : ContinuousOn (fun p : ℝ × ℝ =>
      2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) p.1 p.2 * F p.1 p.2
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) p.1 p.2
          * Work.Spaces.pth F p.1 p.2
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φ) p.1 p.2
          * Work.Spaces.Dz F p.1 p.2
        - (1 / 2) * Work.Construction.s2 p.2 * Work.Construction.FK F p.1
          * Work.Spaces.pth F p.1 p.2
        - Real.sin p.2 ^ 2 * Work.Construction.FK F p.1 * F p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    (((t1.sub t2).sub t3).sub t4).sub t5
  refine key.congr ?_
  intro p hp
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry_apply_pair, Work.Construction.N]

/-! ## The target -/

/-- **The three right-hand-side blocks of the `ε`-scheme are jointly continuous on the open
quadrant**, for a profile `w` of the class `ClassC α` and a stream function `Φ` which is only
`C¹` on the open quadrant.

* `N₀ α (F_* + w) w` is smooth: `SmoothN0` with the `C^∞`-radial moment
  `z ↦ L₁₂(w)(z)` supplied by the class alone (`smoothOpen_L12_radial_classC`);
* `N α (F_* + w) Φ` is only continuous, because `Φ` is: `continuousOn_N_gen`, whose
  `Φ`-input is the `C¹`-difference `Φ̃ = Φ - (1/(4α)) sin(2θ) L₁₂(F_* + w)`;
* `Transport w = 3 D_θw/(1+z)` is continuous: `continuousOn_uncurry_transport`. -/
theorem prof_cont {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {w Φ : ℝ → ℝ → ℝ}
    (hw : Work.FTS.ClassC.ClassC α w)
    (hΦ : ContDiffOn ℝ 1 (Function.uncurry Φ) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (Function.uncurry
        (Work.Construction.N0 α (Work.Construction.Ftot α w) w)) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry
        (Work.Construction.N α (Work.Construction.Ftot α w) Φ)) Work.FTS.EllipticEst.Q0 ∧
    ContinuousOn (Function.uncurry (Work.Coercivity.Transport w)) Work.FTS.EllipticEst.Q0 := by
  obtain ⟨hL12w, hFKw⟩ := prof_cont_moments hα hα1 hw
  have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftot α w) :=
    Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)) hw.reg
  refine ⟨?_, ?_, ?_⟩
  · exact (Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hw.reg
      (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw)).continuousOn
  · exact continuousOn_N_gen hF hL12w hFKw hΦ
  · exact continuousOn_uncurry_transport hw.reg

end

end Work.FTS.StrongEps.E5Aux2
