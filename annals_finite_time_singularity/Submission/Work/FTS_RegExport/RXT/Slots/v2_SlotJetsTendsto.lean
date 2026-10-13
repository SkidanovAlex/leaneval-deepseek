import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXT.C2Assemble
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Defs
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.tendsto_EJet

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Slots

open scoped Real Topology
open Set Filter
open Work.FTS_RegExport.RXT.Slots.JetCalc

/-- The three coefficient triples, and the congruence of the operators with the combination. -/
theorem v2_SlotJetsTendsto {α : ℝ} {Ξ : ℕ → ℝ → ℝ → ℝ} {Ξlim : ℝ → ℝ → ℝ}
    (hΞ : ∀ n : ℕ, ContDiffOn ℝ 3 (Function.uncurry (Ξ n)) Work.FTS.EllipticEst.Q0)
    (hΞlim : ContDiffOn ℝ 3 (Function.uncurry Ξlim) Work.FTS.EllipticEst.Q0)
    (hconv : ∀ (b a : ℕ), a + b ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed b a (Ξ n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed b a Ξlim z θ))) :
    ∀ (j i : ℕ), j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
            (fun z θ => Work.Construction.Rop α (Ξ n) z θ) z θ) Filter.atTop
          (nhds (Work.Spaces.mixed j i (fun z θ => Work.Construction.Rop α Ξlim z θ) z θ)) ∧
        Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
            (fun z θ => Work.Construction.Vop (Ξ n) z θ) z θ) Filter.atTop
          (nhds (Work.Spaces.mixed j i (fun z θ => Work.Construction.Vop Ξlim z θ) z θ)) ∧
        Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i
            (fun z θ => Work.Construction.Uop α (Ξ n) z θ / Real.sin (2 * θ)) z θ) Filter.atTop
          (nhds (Work.Spaces.mixed j i
            (fun z θ => Work.Construction.Uop α Ξlim z θ / Real.sin (2 * θ)) z θ))) := by
  intro j i hji z θ hz hθ hθ2
  have hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩
  have htan : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.tan p.2) Work.FTS.EllipticEst.Q0 :=
    JetCalc.contDiffOn_tan_quad
  -- the Rop coefficients
  have haR : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (fun θ => 2 * Real.tan θ) p.2)
      Work.FTS.EllipticEst.Q0 := by
    show ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (2 : ℝ) * Real.tan p.2) Work.FTS.EllipticEst.Q0
    exact (contDiffOn_const (c := (2 : ℝ))).mul htan
  have hbR : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (fun θ => α * Real.tan θ) p.2)
      Work.FTS.EllipticEst.Q0 := by
    show ContDiffOn ℝ 2 (fun p : ℝ × ℝ => α * Real.tan p.2) Work.FTS.EllipticEst.Q0
    exact (contDiffOn_const (c := α)).mul htan
  have hcR : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (fun _ : ℝ => (1 : ℝ)) p.2)
      Work.FTS.EllipticEst.Q0 := by
    show ContDiffOn ℝ 2 (fun _ : ℝ × ℝ => (1 : ℝ)) Work.FTS.EllipticEst.Q0
    exact contDiffOn_const
  -- the coordinate congruence for `ℛ`
  have ropEq : ∀ X : ℝ → ℝ → ℝ, ContDiffOn ℝ 3 (Function.uncurry X) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i (fun z θ => Work.Construction.Rop α X z θ) z θ
        = EJet (fun θ => 2 * Real.tan θ) (fun θ => α * Real.tan θ) (fun _ => 1) j i X z θ := by
    intro X hX
    have hcong : Set.EqOn (Function.uncurry (fun z θ => Work.Construction.Rop α X z θ))
        (Function.uncurry (combo (fun θ => 2 * Real.tan θ) (fun θ => α * Real.tan θ)
          (fun _ => 1) X)) Work.FTS.EllipticEst.Q0 := by
      intro p hp'
      obtain ⟨z', θ'⟩ := p
      have hcos : Real.cos θ' ≠ 0 := ne_of_gt (JetCalc.cos_pos_quad hp')
      simp only [Function.uncurry, combo, Work.Construction.Rop, Work.Spaces.Dz, Work.Spaces.pz,
        Work.Spaces.pth, Real.tan_eq_sin_div_cos]
      field_simp
      try ring
    exact (JetCalc.mixed_congr_eqOn hcong j i hp).trans
      (JetCalc.mixed_combo_pt hji hX haR hbR hcR z θ hp)
  -- the Vop coefficients
  have haV : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (fun θ => -Real.tan θ) p.2)
      Work.FTS.EllipticEst.Q0 := by
    show ContDiffOn ℝ 2 (fun p : ℝ × ℝ => -Real.tan p.2) Work.FTS.EllipticEst.Q0
    exact htan.neg
  have hbV : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (fun _ : ℝ => (0 : ℝ)) p.2)
      Work.FTS.EllipticEst.Q0 := by
    show ContDiffOn ℝ 2 (fun _ : ℝ × ℝ => (0 : ℝ)) Work.FTS.EllipticEst.Q0
    exact contDiffOn_const
  have vopEq : ∀ X : ℝ → ℝ → ℝ, ContDiffOn ℝ 3 (Function.uncurry X) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i (fun z θ => Work.Construction.Vop X z θ) z θ
        = EJet (fun θ => -Real.tan θ) (fun _ => 0) (fun _ => 1) j i X z θ := by
    intro X hX
    have hcong : Set.EqOn (Function.uncurry (fun z θ => Work.Construction.Vop X z θ))
        (Function.uncurry (combo (fun θ => -Real.tan θ) (fun _ => 0) (fun _ => 1) X))
        Work.FTS.EllipticEst.Q0 := by
      intro p hp'
      obtain ⟨z', θ'⟩ := p
      simp only [Function.uncurry, combo, Work.Construction.Vop, Work.Spaces.Dz, Work.Spaces.pz,
        Work.Spaces.pth]
      ring
    exact (JetCalc.mixed_congr_eqOn hcong j i hp).trans
      (JetCalc.mixed_combo_pt hji hX haV hbV hcR z θ hp)
  -- the Uop coefficients
  have haU : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (fun θ => -3 / Real.sin (2 * θ)) p.2)
      Work.FTS.EllipticEst.Q0 := by
    show ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (-3 : ℝ) / Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0
    have h1 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (-3 : ℝ)) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const
    have h2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    show ContDiffOn ℝ 2 ((fun p : ℝ × ℝ => (-3 : ℝ)) / (fun p : ℝ × ℝ => Real.sin (2 * p.2)))
      Work.FTS.EllipticEst.Q0
    exact h1.div h2 (fun p hp' => ne_of_gt (JetCalc.sin_two_pos_quad hp'))
  have hbU : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (fun θ => -α / Real.sin (2 * θ)) p.2)
      Work.FTS.EllipticEst.Q0 := by
    show ContDiffOn ℝ 2 (fun p : ℝ × ℝ => -α / Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0
    have h1 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => -α) Work.FTS.EllipticEst.Q0 :=
      contDiffOn_const
    have h2 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Work.FTS.EllipticEst.Q0 :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    show ContDiffOn ℝ 2 ((fun p : ℝ × ℝ => -α) / (fun p : ℝ × ℝ => Real.sin (2 * p.2)))
      Work.FTS.EllipticEst.Q0
    exact h1.div h2 (fun p hp' => ne_of_gt (JetCalc.sin_two_pos_quad hp'))
  have uopEq : ∀ X : ℝ → ℝ → ℝ, ContDiffOn ℝ 3 (Function.uncurry X) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed j i (fun z θ => Work.Construction.Uop α X z θ / Real.sin (2 * θ)) z θ
        = EJet (fun θ => -3 / Real.sin (2 * θ)) (fun θ => -α / Real.sin (2 * θ)) (fun _ => 0)
            j i X z θ := by
    intro X hX
    have hcong : Set.EqOn
        (Function.uncurry (fun z θ => Work.Construction.Uop α X z θ / Real.sin (2 * θ)))
        (Function.uncurry (combo (fun θ => -3 / Real.sin (2 * θ))
          (fun θ => -α / Real.sin (2 * θ)) (fun _ => 0) X)) Work.FTS.EllipticEst.Q0 := by
      intro p hp'
      obtain ⟨z', θ'⟩ := p
      have hs : Real.sin (2 * θ') ≠ 0 := ne_of_gt (JetCalc.sin_two_pos_quad hp')
      simp only [Function.uncurry, combo, Work.Construction.Uop, Work.Spaces.Dz, Work.Spaces.pz,
        Work.Spaces.pth]
      field_simp
      try ring
    exact (JetCalc.mixed_congr_eqOn hcong j i hp).trans
      (JetCalc.mixed_combo_pt hji hX haU hbU hbV z θ hp)
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun n : ℕ => Work.Spaces.mixed j i
          (fun z θ => Work.Construction.Rop α (Ξ n) z θ) z θ)
        = fun n : ℕ => EJet (fun θ => 2 * Real.tan θ) (fun θ => α * Real.tan θ) (fun _ => 1)
            j i (Ξ n) z θ from funext (fun n => ropEq (Ξ n) (hΞ n)),
      show Work.Spaces.mixed j i (fun z θ => Work.Construction.Rop α Ξlim z θ) z θ
        = EJet (fun θ => 2 * Real.tan θ) (fun θ => α * Real.tan θ) (fun _ => 1) j i Ξlim z θ
        from ropEq Ξlim hΞlim]
    exact JetCalc.tendsto_EJet hconv _ _ _ hji z θ hz hθ hθ2
  · rw [show (fun n : ℕ => Work.Spaces.mixed j i
          (fun z θ => Work.Construction.Vop (Ξ n) z θ) z θ)
        = fun n : ℕ => EJet (fun θ => -Real.tan θ) (fun _ => 0) (fun _ => 1)
            j i (Ξ n) z θ from funext (fun n => vopEq (Ξ n) (hΞ n)),
      show Work.Spaces.mixed j i (fun z θ => Work.Construction.Vop Ξlim z θ) z θ
        = EJet (fun θ => -Real.tan θ) (fun _ => 0) (fun _ => 1) j i Ξlim z θ
        from vopEq Ξlim hΞlim]
    exact JetCalc.tendsto_EJet hconv _ _ _ hji z θ hz hθ hθ2
  · rw [show (fun n : ℕ => Work.Spaces.mixed j i
          (fun z θ => Work.Construction.Uop α (Ξ n) z θ / Real.sin (2 * θ)) z θ)
        = fun n : ℕ => EJet (fun θ => -3 / Real.sin (2 * θ)) (fun θ => -α / Real.sin (2 * θ))
            (fun _ => 0) j i (Ξ n) z θ from funext (fun n => uopEq (Ξ n) (hΞ n)),
      show Work.Spaces.mixed j i
          (fun z θ => Work.Construction.Uop α Ξlim z θ / Real.sin (2 * θ)) z θ
        = EJet (fun θ => -3 / Real.sin (2 * θ)) (fun θ => -α / Real.sin (2 * θ))
            (fun _ => 0) j i Ξlim z θ from uopEq Ξlim hΞlim]
    exact JetCalc.tendsto_EJet hconv _ _ _ hji z θ hz hθ hθ2

end Work.FTS_RegExport.RXT.Slots
