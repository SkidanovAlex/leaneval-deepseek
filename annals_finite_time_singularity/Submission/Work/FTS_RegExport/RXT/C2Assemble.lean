import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.StrongEps.HkMem_of_tendsto
import Submission.Work.FTS_FinalLeaves.psiCan_C3_proved

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.C2Assemble` — elementary smoothness of the transport coefficients

The pointwise (in `(z,θ) ∈ Q0`) assembly steps of S4 (`coeff_C2`): once the stream function
`slice (psiR α Φs E (tauExt g)) τ` is `C³` on the open quadrant and the two radial functions
`L₁₂(F(τ))`, `𝔽K(F(τ))` are `C²`/`C³` on `(0,∞)`, the three coefficients `Vz7`, `Vθ7`, `cs7`
of `(E)` are `C²` there.

Nothing here uses the elliptic theory: these are the `ContDiffOn`-calculus lemmas.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## `sin 2θ`, `cos θ` and `tan` on the open quadrant -/

theorem sin_two_pos_Q0 {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.2.1]) (by linarith [h.2.2, Real.pi_pos])

theorem cos_pos_Q0 {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.2.1, Real.pi_pos], by linarith [h.2.2, Real.pi_pos]⟩

theorem contDiffOn_tan_Q0 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.tan p.2)
    Work.FTS.EllipticEst.Q0 := by
  have hsin : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    Real.contDiff_sin.comp_contDiffOn contDiff_snd.contDiffOn
  have hcos : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    Real.contDiff_cos.comp_contDiffOn contDiff_snd.contDiffOn
  refine (hsin.div hcos (fun p hp => ne_of_gt (cos_pos_Q0 hp))).congr ?_
  intro p _
  exact Real.tan_eq_sin_div_cos p.2

/-! ## The partial derivatives lower the order -/

theorem contDiffOn_uncurry_pz {F : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz F)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongEps.contDiffOn_uncurry_pz_fin Work.FTS.EllipticEst.isOpen_Q0 h

theorem contDiffOn_uncurry_pth {F : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth F)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin Work.FTS.EllipticEst.isOpen_Q0 h

/-- `C³` is in particular `C²`. -/
theorem cd2_of_cd3 {F : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 3 (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
  h.of_le (by norm_num)

/-! ## The coefficients `Uop`, `Vop`, `Rop` of an open-quadrant-`C³` stream function -/

theorem contDiffOn_uncurry_Uop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Uop α Ψ)) Work.FTS.EllipticEst.Q0 := by
  have hpz : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Ψ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pz hΨ
  have h2 := cd2_of_cd3 hΨ
  have h3 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => α * p.1 * Work.Spaces.pz Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const (c := α)).mul contDiffOn_fst).mul hpz
  refine (((contDiffOn_const (c := (-3 : ℝ))).mul h2).sub h3).congr ?_
  intro p _
  simp only [Function.uncurry, Work.Construction.Uop]

theorem contDiffOn_uncurry_Vop {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop Ψ)) Work.FTS.EllipticEst.Q0 := by
  have hpth : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pth hΨ
  have h2 := cd2_of_cd3 hΨ
  exact hpth.sub (contDiffOn_tan_Q0.mul h2)

theorem contDiffOn_uncurry_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Rop α Ψ)) Work.FTS.EllipticEst.Q0 := by
  have hpz : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Ψ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pz hΨ
  have hpth : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pth hΨ
  have h2 := cd2_of_cd3 hΨ
  have hsin : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    Real.contDiff_sin.comp_contDiffOn contDiff_snd.contDiffOn
  have hcos : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    Real.contDiff_cos.comp_contDiffOn contDiff_snd.contDiffOn
  have hn : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      (2 * Real.sin p.2 * Ψ p.1 p.2 + α * Real.sin p.2 * p.1 * Work.Spaces.pz Ψ p.1 p.2
        + Real.cos p.2 * Work.Spaces.pth Ψ p.1 p.2)) Work.FTS.EllipticEst.Q0 :=
    ((((contDiffOn_const (c := (2 : ℝ))).mul hsin).mul h2).add
      ((((contDiffOn_const (c := α)).mul hsin).mul contDiffOn_fst).mul hpz)).add
        (hcos.mul hpth)
  refine (hn.div hcos (fun p hp => ne_of_gt (cos_pos_Q0 hp))).congr ?_
  intro p _
  simp only [Pi.div_apply, Function.uncurry, Work.Construction.Rop]

/-! ## Division by `sin (2θ)` and radial/angular products -/

theorem contDiffOn_uncurry_div_sin_two {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 2 (Function.uncurry (fun z θ => F z θ / Real.sin (2 * θ)))
      Work.FTS.EllipticEst.Q0 := by
  have hsin : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hF.div hsin (fun p hp => ne_of_gt (sin_two_pos_Q0 hp))

/-- `(z,θ) ↦ c * a z` is `C²` on `Q0` when `a` is `C²` on `(0,∞)`. -/
theorem contDiffOn_two_const_mul_fst {c : ℝ} {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ 2 a (Set.Ioi 0)) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => c * a p.1) Work.FTS.EllipticEst.Q0 :=
  (contDiffOn_const (c := c)).mul (ha.comp contDiffOn_fst (fun p hp => hp.1))

/-- `(z,θ) ↦ a z * b θ` is `C²` on `Q0`. -/
theorem contDiffOn_two_mul_snd {a : ℝ → ℝ} {b : ℝ → ℝ}
    (ha : ContDiffOn ℝ 2 a (Set.Ioi 0)) (hb : ContDiffOn ℝ 2 b (Set.Ioo 0 (π / 2))) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => a p.1 * b p.2) Work.FTS.EllipticEst.Q0 :=
  (ha.comp contDiffOn_fst (fun p hp => hp.1)).mul
    (hb.comp contDiffOn_snd (fun p hp => hp.2))

end Work.FTS_RegExport.RXT
