import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.FTS_RegExport.RXT.st1_fb_theta
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS_RegExport.RXA2w.lim_mixed_weighted_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXA2w

theorem lim_mixed_weighted_proved {αG C₀ : ℝ} (hα : 0 < αG) (hα1 : αG ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ|
          ≤ C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  obtain ⟨gn, B, L, hC, -, hjet, -⟩ := hA T hT
  -- the constant `C₀ * αG ^ 2` is nonnegative (it dominates `Xn` at any slot)
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn αG (Work.FTS.Galerkin.slice (gn 0) 0) :=
    Work.Spaces.HkNorm_nonneg αG 4 _
  have hC0sq : 0 ≤ C₀ * αG ^ 2 := le_trans hX0 (hC 0 0 hT0).2.1
  refine ⟨Cw * (C₀ * αG ^ 2), mul_nonneg hCw0 hC0sq, ?_⟩
  intro τ hτ b a hab z θ hz hθ0 hθ1
  have hw0 : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
  -- the existential constant does not depend on `n`: the class-`C` bound transfers slotwise
  have hbound : ∀ n : ℕ,
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (C₀ * αG ^ 2) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    intro n
    have hcls : Work.FTS.ClassC.ClassC αG (Work.FTS.Galerkin.slice (gn n) τ) := (hC n τ hτ).1
    have h4 : ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice (gn n) τ))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hcls.reg 4
    have hmem : Work.Spaces.HkMem αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.OpenPkg.HkMem_mono_open hcls.reg 4 (by norm_num) hcls.mem
    have htr : Work.FTS.Nonlin.BdryTraces αG 4 (Work.FTS.Galerkin.slice (gn n) τ) :=
      Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcls.tr
    have h1 := hCw _ h4 hmem htr b a hab z θ hz hθ0 hθ1
    have h2 : Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) ≤ C₀ * αG ^ 2 :=
      (hC n τ hτ).2.1
    calc |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Work.Spaces.HkNorm αG 4 (Work.FTS.Galerkin.slice (gn n) τ) := h1
      _ ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (C₀ * αG ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hCw0 hw0)
      _ = Cw * (C₀ * αG ^ 2) * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  exact le_of_tendsto ((hjet τ hτ b a (by omega) z θ hzθ).abs)
    (Filter.Eventually.of_forall hbound)

end Work.FTS_RegExport.RXA2w
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.r7Init =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR7

open scoped Real Topology NNReal
open Set Filter

set_option autoImplicit false

/-- **RX-R7, the `hInit` field.** The full profile of the R7 block at the sanitised
right-Taylor family (`Prof α g = profFull α (extG (gS α (tauExt g)))`) vanishes at `τ = 0`
beyond some radius `Lz7 > 0`, namely (via `hdat`) beyond the `z`-support of the localised datum
`locG6 (pExp α) L β`.

Route: `hdat` at `τ = 0`; `gS` and `tauExt` are inert at `z > 0`, `0 ≤ θ ≤ π/2`, `τ = 0`
(`gS`, `tauExt_of_nonneg`, `extG_of_pos`); `locG6 (pExp α) L β = locData - F_*` with
`locData = F_* · chi(z/L) + β · hLoc` and `hLoc α = bumpZ · Γ`, and `profFull = F_* + extG(·)`
reduces the profile at `τ = 0` to `F_* · chi(z/L) + β · bumpZ(z) · Γ(θ)` which vanishes for
`z > max (2L) (7/4)` (`Stability.chi_eq_zero` with `|z/L| ≥ 2`, `LocData.bumpZ_eq_zero_of_ge`).
`Lz7 := max (2L) (7/4)` works since `1 ≤ L` gives `Lz7 > 0`. -/
theorem r7Init {α : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ) :
    ∃ Lz7 : ℝ, 0 < Lz7 ∧ ∀ z θ, Lz7 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_RegExport.RXR7.Prof α g z θ 0 = 0 := by
  obtain ⟨L, β, hL1, hdat⟩ := hdat
  refine ⟨max (2 * L) (7 / 4), lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro z θ hz hθ0 hθ1
  have hLpos : 0 < L := by linarith
  have hz2L : 2 * L < z := lt_of_le_of_lt (le_max_left _ _) hz
  have hz74 : 7 / 4 < z := lt_of_le_of_lt (le_max_right _ _) hz
  have hz0 : 0 < z := by linarith
  -- the sanitiser and the right-Taylor extension are inert at `τ = 0`
  have hgr : GR α g z θ 0 = g z θ 0 := by
    have h1 : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ 0
        = Work.FTS.FinalV2.tauExt g z θ 0 := by
      simp only [Work.FTS.FinalV2.gS, hz0, hθ0.le, hθ1.le, and_self, ↓reduceIte]
    rw [GR, h1, Work.FTS.FinalV2.tauExt_of_nonneg g (le_refl (0 : ℝ))]
  have hextG : Work.FTS.RegPkgGal.extG (GR α g) z θ 0 = g z θ 0 := by
    rw [Work.FTS.RegPkgGal.extG_of_pos hz0 (le_refl (0 : ℝ)), hgr]
  -- the profile at `τ = 0` is `F_* + g(0)`
  have hprof : Prof α g z θ 0 = Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
      + g z θ 0 := by
    simp only [Prof, Work.FTS.Regularity.profFull_apply, hextG]
  -- the two cut-offs vanish beyond `z > max (2L) (7/4)`
  have hchi : Work.Stability.chi (z / L) = 0 := by
    refine Work.Stability.chi_eq_zero ?_
    rw [abs_of_nonneg (div_nonneg hz0.le hLpos.le)]
    rw [le_div_iff₀ hLpos]
    linarith
  have hbump : Work.FTS.LocData.bumpZ z = 0 :=
    Work.FTS.LocDataExt.bumpZ_eq_zero_of_ge hz74.le
  rw [hprof, hdat z θ, Work.FTS.LocData6.locG6_eq, Work.FTS.LocData.locG_apply,
    Work.FTS.LocData.locData_apply, Work.FTS.LocData.hLoc_apply, hchi, hbump]
  ring

end Work.FTS_RegExport.RXR7
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Slots.v2_SlotJetsTendsto =====
section

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
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.st1_angle =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

/-- The `α`-Hölder modulus of `g̃` in `θ`. -/
theorem st1_hhθ {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S)
    (hK0 : 0 ≤ K)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∃ Lθ : ℝ, 0 ≤ Lθ ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
        |GG α g z θ τ - GG α g z θ' τ| ≤ Lθ * |θ - θ'| ^ α := by
  have hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hmin.vanish τ hτ z hz
  obtain ⟨L, hL0, hL⟩ := theta_modulus_uniform_fb (α := α) (C := K) (K := K) hα hα13 hK0 hK0
  refine ⟨L, hL0, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    rw [GG_of_nonpos α le_rfl, GG_of_nonpos α le_rfl, sub_zero, abs_zero]
    exact mul_nonneg hL0 (Real.rpow_nonneg (abs_nonneg _) _)
  · exact hL (u := fun x => GG α g z x τ)
      (u' := fun x => Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z x)
      (fun x hx =>
        (Work.FTS.RegPkgGal.R4b.hasDerivAt_sliceTh isOpen_Ioi isOpen_Ioo
          ((hmin.c4 τ hτ.1).of_le (by norm_num)) hzpos hx).congr_of_eventuallyEq (by
            filter_upwards [isOpen_Ioo.mem_nhds hx] with x' hx'
            exact GG_of_mem α hτ.1 hzpos ⟨hx'.1.le, hx'.2.le⟩))
      (fun x hx => by
        have hxI : x ∈ Work.Spaces.Iθ := ⟨hx.1.le, hx.2.le⟩
        have hsin : 0 < Real.sin (2 * x) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
        have h2 := hw (2 : Fin 6) τ hτ z x hzpos hx.1 hx.2
        norm_num [Work.FTS.RegExportIface.RXT.idx] at h2
        have hDth : Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z x
            = Real.sin (2 * x) * Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z x := rfl
        have hkey : |Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z x| * Real.sin (2 * x)
            ≤ K * Work.FTS.Regularity.Gamma α x := by
          calc |Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z x| * Real.sin (2 * x)
              = |Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z x| := by
                rw [hDth, abs_mul, abs_of_pos hsin]; ring
            _ ≤ K * Work.FTS.RegExportIface.ω α z x := h2
            _ ≤ K * Work.FTS.Regularity.Gamma α x :=
                mul_le_mul_of_nonneg_left (omega_le_Gamma α z x hzpos.le hxI) hK0
        have hfin : |Work.Spaces.pth (Work.FTS.Galerkin.slice g τ) z x|
            ≤ K * Work.FTS.Regularity.Gamma α x / Real.sin (2 * x) :=
          (le_div_iff₀ hsin).mpr hkey
        simpa only [mul_div_assoc] using hfin)
      (fun x hx => by
        rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
        · subst hx0
          rw [GG_eq_zero_left α hτ.1 hzpos hv, Gamma_zero_left hα, mul_zero, abs_zero]
        · rcases eq_or_lt_of_le hx.2 with hxπ | hxlt
          · subst hxπ
            rw [GG_eq_zero_right α hτ.1 hzpos hv, Gamma_zero_right hα, mul_zero, abs_zero]
          · rw [GG_of_mem α hτ.1 hzpos hx]
            have h0 := hw (0 : Fin 6) τ hτ z x hzpos hxpos hxlt
            norm_num [Work.FTS.RegExportIface.RXT.idx] at h0
            calc |Work.FTS.Galerkin.slice g τ z x|
                = |Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z x| := rfl
              _ ≤ K * Work.FTS.RegExportIface.ω α z x := h0
              _ ≤ K * Work.FTS.Regularity.Gamma α x :=
                  mul_le_mul_of_nonneg_left (omega_le_Gamma α z x hzpos.le hx) hK0)
      θ hθ θ' hθ'

/-- The `α`-Hölder modulus of `∂_z g̃` in `θ`. -/
theorem st1_hhθp {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S)
    (hK0 : 0 ≤ K)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∃ Nθ : ℝ, 0 ≤ Nθ ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ, ∀ θ' ∈ Work.Spaces.Iθ,
        |Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z θ
          - Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z θ'| ≤ Nθ * |θ - θ'| ^ α := by
  have hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hmin.vanish τ hτ z hz
  obtain ⟨L, hL0, hL⟩ := theta_modulus_uniform_fb (α := α) (C := K) (K := K) hα hα13 hK0 hK0
  refine ⟨L, hL0, ?_⟩
  intro τ hτ z hz θ hθ θ' hθ'
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    have hz0' : ∀ x : ℝ, Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) 0 x = 0 :=
      fun x => by
        show deriv (fun z' => GG α g z' x τ) 0 = 0
        exact deriv_eq_zero_of_eq_zero_of_nonpos (fun y hy => GG_of_nonpos α hy)
    rw [hz0' θ, hz0' θ', sub_zero, abs_zero]
    exact mul_nonneg hL0 (Real.rpow_nonneg (abs_nonneg _) _)
  · exact hL (u := fun x => Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z x)
      (u' := fun x => Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x)
      (fun x hx =>
        (Work.FTS.EllipticEst.TT.step2Ae.hasDerivAt_pz_theta
          (((hmin.c4 τ hτ.1).contDiffAt
            ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds (show (z, x) ∈ Set.Ioi (0:ℝ) ×ˢ
              Set.Ioo (0:ℝ) (π / 2) from ⟨hzpos, hx.1, hx.2⟩))).of_le
              (by norm_num))).congr_of_eventuallyEq (by
          filter_upwards [isOpen_Ioo.mem_nhds hx] with x' hx'
          exact pz_GG_eq α hτ.1 hzpos ⟨hx'.1.le, hx'.2.le⟩))
      (fun x hx => by
        have hxI : x ∈ Work.Spaces.Iθ := ⟨hx.1.le, hx.2.le⟩
        have hsin : 0 < Real.sin (2 * x) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2])
        have h4 := hw (4 : Fin 6) τ hτ z x hzpos hx.1 hx.2
        norm_num [Work.FTS.RegExportIface.RXT.idx] at h4
        have hid : Work.Spaces.mixed 1 1 (Work.FTS.Galerkin.slice g τ) z x
            = z * (Real.sin (2 * x)
                * Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x) :=
          mixed_one_one_eq _ z x
        -- `|∂_θ∂_zg| · sin 2θ ≤ KΓ`, then divide by `sin 2θ`
        have hkey : (|Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
              * Real.sin (2 * x)) * z ≤ K * Work.FTS.RegExportIface.ω α z x := by
          have h1 : (|Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
                * Real.sin (2 * x)) * z
              = |Work.Spaces.mixed 1 1 (Work.FTS.Galerkin.slice g τ) z x| := by
            rw [hid]
            simp only [abs_mul, abs_of_pos hzpos, abs_of_pos hsin]
            ring
          rw [h1]; exact h4
        have h5 : |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
              * Real.sin (2 * x)
            ≤ K * (Work.FTS.RegExportIface.ω α z x / z) := by
          have h7 : |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
                * Real.sin (2 * x)
              ≤ K * Work.FTS.RegExportIface.ω α z x / z := (le_div_iff₀ hzpos).mpr hkey
          rwa [mul_div_assoc] at h7
        have hfin : |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
              * Real.sin (2 * x) ≤ K * Work.FTS.Regularity.Gamma α x :=
          le_trans h5 (mul_le_mul_of_nonneg_left
            (omega_div_z_le_Gamma α z x hzpos.le hxI) hK0)
        have hres : |Work.Spaces.pz (Work.Spaces.pth (Work.FTS.Galerkin.slice g τ)) z x|
            ≤ K * Work.FTS.Regularity.Gamma α x / Real.sin (2 * x) :=
          (le_div_iff₀ hsin).mpr hfin
        simpa only [mul_div_assoc] using hres)
      (fun x hx => by
        rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
        · subst hx0
          rw [pz_GG_eq_zero_left α hτ.1 hzpos hv, Gamma_zero_left hα, mul_zero, abs_zero]
        · rcases eq_or_lt_of_le hx.2 with hxπ | hxlt
          · subst hxπ
            rw [pz_GG_eq_zero_right α hτ.1 hzpos hv, Gamma_zero_right hα, mul_zero, abs_zero]
          · rw [pz_GG_eq α hτ.1 hzpos hx]
            have h1 := hw (1 : Fin 6) τ hτ z x hzpos hxpos hxlt
            norm_num [Work.FTS.RegExportIface.RXT.idx] at h1
            have hkey : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x| * z
                ≤ K * Work.FTS.RegExportIface.ω α z x := by
              have h2 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x| * z
                  = |Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z x| := by
                show |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x| * z
                  = |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x|
                rw [abs_mul, abs_of_pos hzpos]; ring
              rw [h2]; exact h1
            have h4 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x|
                ≤ K * (Work.FTS.RegExportIface.ω α z x / z) := by
              have h5 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x|
                  ≤ K * Work.FTS.RegExportIface.ω α z x / z := (le_div_iff₀ hzpos).mpr hkey
              rwa [mul_div_assoc] at h5
            calc |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z x|
                ≤ K * (Work.FTS.RegExportIface.ω α z x / z) := h4
              _ ≤ K * Work.FTS.Regularity.Gamma α x :=
                  mul_le_mul_of_nonneg_left (omega_div_z_le_Gamma α z x hzpos.le hx) hK0)
      θ hθ θ' hθ'

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.st1_stdata =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

/-- The `Γ`-vanishing of the angular derivative of `g̃`. -/
theorem st1_dthvan {α : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∃ Cθ : ℝ, 0 ≤ Cθ ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ := by
  refine ⟨|K|, abs_nonneg K, ?_⟩
  intro τ hτ z θ hz hθ
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · -- `z = 0`: the `GG`-slice at `z = 0` is identically zero
    subst hz0
    have hfun : (fun θ' : ℝ => GG α g 0 θ' τ) = fun _ => (0:ℝ) :=
      funext (fun θ' => GG_of_nonpos α le_rfl)
    have hD0 : Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) 0 θ = 0 := by
      show Real.sin (2 * θ) * deriv (fun θ' => GG α g 0 θ' τ) θ = 0
      rw [hfun, deriv_const, mul_zero]
    rw [hD0, abs_zero]
    simp
  · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
    · -- `θ = 0`
      subst hθ0
      have hD0 : Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) z 0 = 0 := by
        show Real.sin (2 * (0:ℝ)) * deriv (fun θ' => GG α g z θ' τ) 0 = 0
        rw [mul_zero, Real.sin_zero, zero_mul]
      rw [hD0, abs_zero, Gamma_zero_left hα]
      simp
    · rcases eq_or_lt_of_le hθ.2 with hθπ | hθlt
      · -- `θ = π/2`
        subst hθπ
        have hD0 : Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) z (π / 2) = 0 := by
          show Real.sin (2 * (π / 2)) * deriv (fun θ' => GG α g z θ' τ) (π / 2) = 0
          rw [show Real.sin (2 * (π / 2)) = 0 by
            rw [show 2 * (π / 2) = π by ring, Real.sin_pi], zero_mul]
        rw [hD0, abs_zero, Gamma_zero_right hα]
        simp
      · -- interior: the `(0,1)`-slot
        have hD : Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) z θ
            = Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ := by
          rw [Dth_GG_eq α hτ.1 hzpos hθpos hθlt]
          rfl
        rw [hD]
        have h2 := hw (2 : Fin 6) τ hτ z θ hzpos hθpos hθlt
        norm_num [Work.FTS.RegExportIface.RXT.idx] at h2
        calc |Work.Spaces.mixed 0 1 (Work.FTS.Galerkin.slice g τ) z θ|
            ≤ K * Work.FTS.RegExportIface.ω α z θ := h2
          _ ≤ |K| * Work.FTS.RegExportIface.ω α z θ :=
              mul_le_mul_of_nonneg_right (le_abs_self K) (omega_nonneg_of α z θ hzpos.le hθ)
          _ ≤ |K| * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) :=
              mul_le_mul_of_nonneg_left (omega_le_zsq_mul_Gamma α z θ hzpos.le hθ) (abs_nonneg K)
          _ = |K| * z ^ 2 * Work.FTS.Regularity.Gamma α θ := by ring

/-- The Taylor data at `z = 0`. -/
theorem st1_quad {α : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g) (hS : 0 < S)
    (hK0 : 0 ≤ K)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    ∃ Kq Q : ℝ, 0 ≤ Kq ∧ 0 ≤ Q ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |GG α g z θ τ| ≤ Kq * z ^ 2) ∧
        ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
          |Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z θ| ≤ Q * z := by
  have hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0 :=
    fun τ hτ z hz => hmin.vanish τ hτ z hz
  refine ⟨|K|, |K|, abs_nonneg K, abs_nonneg K, ?_⟩
  intro τ hτ θ hθ
  refine ⟨?_, ?_⟩
  · intro z hz hz2
    rcases eq_or_lt_of_le hz with hz0 | hzpos
    · subst hz0
      rw [GG_of_nonpos α le_rfl, abs_zero]
      positivity
    · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
      · subst hθ0
        rw [GG_eq_zero_left α hτ.1 hzpos hv, abs_zero]
        positivity
      · rcases eq_or_lt_of_le hθ.2 with hθπ | hθlt
        · subst hθπ
          rw [GG_eq_zero_right α hτ.1 hzpos hv, abs_zero]
          positivity
        · rw [GG_of_mem α hτ.1 hzpos hθ]
          have h0 := hw (0 : Fin 6) τ hτ z θ hzpos hθpos hθlt
          norm_num [Work.FTS.RegExportIface.RXT.idx] at h0
          have hΓ1 : Work.FTS.Regularity.Gamma α θ ≤ 1 :=
            Work.ConstructionInstance.Gamma_le_one hα.le hθ
          have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
            Work.ConstructionInstance.Gamma_nonneg hθ
          calc |Work.FTS.Galerkin.slice g τ z θ|
              = |Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g τ) z θ| := rfl
            _ ≤ K * Work.FTS.RegExportIface.ω α z θ := h0
            _ ≤ |K| * Work.FTS.RegExportIface.ω α z θ :=
                mul_le_mul_of_nonneg_right (le_abs_self K) (omega_nonneg_of α z θ hzpos.le hθ)
            _ ≤ |K| * (z ^ 2 * Work.FTS.Regularity.Gamma α θ) :=
                mul_le_mul_of_nonneg_left (omega_le_zsq_mul_Gamma α z θ hzpos.le hθ)
                  (abs_nonneg K)
            _ ≤ |K| * z ^ 2 := by
                have h := mul_le_mul_of_nonneg_left hΓ1 (mul_nonneg (abs_nonneg K) (sq_nonneg z))
                simpa only [mul_assoc, mul_one] using h
  · intro z hz hz2
    rcases eq_or_lt_of_le hz with hz0 | hzpos
    · subst hz0
      have h0 : Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) 0 θ = 0 := by
        show deriv (fun z' => GG α g z' θ τ) 0 = 0
        exact deriv_eq_zero_of_eq_zero_of_nonpos (fun y hy => GG_of_nonpos α hy)
      rw [h0, abs_zero]
      positivity
    · rcases eq_or_lt_of_le hθ.1 with hθ0 | hθpos
      · subst hθ0
        rw [pz_GG_eq_zero_left α hτ.1 hzpos hv, abs_zero]
        positivity
      · rcases eq_or_lt_of_le hθ.2 with hθπ | hθlt
        · subst hθπ
          rw [pz_GG_eq_zero_right α hτ.1 hzpos hv, abs_zero]
          positivity
        · rw [pz_GG_eq α hτ.1 hzpos hθ]
          have h1 := hw (1 : Fin 6) τ hτ z θ hzpos hθpos hθlt
          norm_num [Work.FTS.RegExportIface.RXT.idx] at h1
          have hΓ1 : Work.FTS.Regularity.Gamma α θ ≤ 1 :=
            Work.ConstructionInstance.Gamma_le_one hα.le hθ
          have hΓ0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
            Work.ConstructionInstance.Gamma_nonneg hθ
          have hkey : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ| * z
              ≤ K * Work.FTS.RegExportIface.ω α z θ := by
            have h2 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ| * z
                = |Work.Spaces.mixed 1 0 (Work.FTS.Galerkin.slice g τ) z θ| := by
              show |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ| * z
                = |z * Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
              rw [abs_mul, abs_of_pos hzpos]; ring
            rw [h2]; exact h1
          have h4 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
              ≤ K * (Work.FTS.RegExportIface.ω α z θ / z) := by
            have h5 : |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
                ≤ K * Work.FTS.RegExportIface.ω α z θ / z := (le_div_iff₀ hzpos).mpr hkey
            rwa [mul_div_assoc] at h5
          have h6 : K * (Work.FTS.RegExportIface.ω α z θ / z)
              ≤ K * (z * Work.FTS.Regularity.Gamma α θ) :=
            mul_le_mul_of_nonneg_left (omega_div_z_le_z_mul_Gamma α z θ hzpos.le hθ) hK0
          calc |Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ|
              ≤ K * (Work.FTS.RegExportIface.ω α z θ / z) := h4
            _ ≤ K * (z * Work.FTS.Regularity.Gamma α θ) := h6
            _ ≤ |K| * z := by
                have hA : K * (z * Work.FTS.Regularity.Gamma α θ) ≤ K * z :=
                  mul_le_mul_of_nonneg_left
                    (by simpa using mul_le_mul_of_nonneg_left hΓ1 hzpos.le) hK0
                have hB : K * z ≤ |K| * z := mul_le_mul_of_nonneg_right (le_abs_self K) hzpos.le
                linarith

end Work.FTS_RegExport.RXT
end
end
