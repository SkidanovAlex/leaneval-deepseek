import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB1.psiP_diff
import Submission.Work.FTS_StreamBdry.SB1.psiP_Vop_bnd
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.psiP_D3_le
import Submission.Work.FTS_StreamBdry.SB3.pth_DzIter_le
import Submission.Work.FTS_StreamBdry.SB3.law_psiP
import Submission.Work.FTS_StreamBdry.SB3.P2Aux.AsmSupport
import Submission.Work.FTS_StreamBdry.SB5.PthIter2Reproved
import Submission.Work.FTS_StreamBdry.SB25.sb5_compare
import Submission.Work.FTS_StreamBdry.SB25.bslOp_eq_s2_Lgs
import Submission.Work.FTS_StreamBdry.SB25.bslOp_dilate
import Submission.Work.FTS_StreamBdry.SB25.bslOp_lincombQd
import Submission.Work.FTS_StreamBdry.SB25.dq1_facts
import Submission.Work.FTS_StreamBdry.SB25.dq2_facts
import Submission.Work.FTS_StreamBdry.SB5Aux.unif_decay_ratio_proved

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB5.Prep` — elementary facts, dilations and the `bslOp`-harmonicity of the difference quotients.
-/

namespace Work.FTS_StreamBdry.SB5

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false

noncomputable section




/-! ## §1 Elementary facts about `s2` and the quadrant -/

theorem isOpen_Qd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

theorem continuous_s2 : Continuous Work.Construction.s2 := by
  rw [show Work.Construction.s2 = fun θ : ℝ => Real.sin (2 * θ) from
    funext fun θ => Work.Construction.s2_eq θ]
  fun_prop

theorem s2_zero : Work.Construction.s2 0 = 0 := by
  rw [Work.Construction.s2_eq]; simp

theorem s2_pi_div_two : Work.Construction.s2 (π / 2) = 0 := by
  rw [Work.Construction.s2_eq]
  have h : 2 * (π / 2) = π := by ring
  rw [h, Real.sin_pi]

theorem tendsto_s2_zero_right : Tendsto Work.Construction.s2 (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h : Tendsto Work.Construction.s2 (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h' := continuous_s2.tendsto (0 : ℝ)
    rwa [s2_zero] at h'
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_s2_zero_left : Tendsto Work.Construction.s2 (𝓝[<] (π / 2)) (𝓝 0) := by
  have h : Tendsto Work.Construction.s2 (𝓝 (π / 2 : ℝ)) (𝓝 0) := by
    have h' := continuous_s2.tendsto (π / 2 : ℝ)
    rwa [s2_pi_div_two] at h'
  exact h.mono_left nhdsWithin_le_nhds

/-- **Endpoint vanishing from a `sin 2θ` bound.**  If `|Q z θ| ≤ M sin 2θ` on the quadrant then
the `θ`-slice of `Q` at a fixed `z > 0` vanishes at both ends. -/
theorem tendsto_zero_endpoints_of_abs_le_s2 {Q : ℝ → ℝ → ℝ} {M z : ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Q z θ| ≤ M * Work.Construction.s2 θ)
    (hz : 0 < z) :
    Tendsto (fun θ => Q z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun θ => Q z θ) (𝓝[<] (π / 2)) (𝓝 0) := by
  have hlt : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < π / 2 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)] with θ hθ _
    exact hθ
  have hgt : ∀ᶠ θ in 𝓝[<] (π / 2), (0 : ℝ) < θ := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Ioi_mem_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)] with θ hθ _
    exact hθ
  have hb : Tendsto (fun θ => M * Work.Construction.s2 θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_s2_zero_right.const_mul M
  have hb' : Tendsto (fun θ => M * Work.Construction.s2 θ) (𝓝[<] (π / 2)) (𝓝 0) := by
    simpa using tendsto_s2_zero_left.const_mul M
  constructor
  · refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin, hlt] with θ hθ hθ2
    rw [Real.norm_eq_abs]
    exact h z θ (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθ, hθ2⟩)
  · refine squeeze_zero_norm' ?_ hb'
    filter_upwards [self_mem_nhdsWithin, hgt] with θ hθ hθ2
    rw [Real.norm_eq_abs]
    exact h z θ (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθ2, hθ⟩)

/-- Continuity on `Ici L` of a slice `z ↦ Q z θ` of a `C¹` function on the quadrant. -/
theorem continuousOn_slice_of_contDiffOn {Q : ℝ → ℝ → ℝ} {L θ : ℝ} (hL : 0 < L)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hQ : ContDiffOn ℝ 1 (Function.uncurry Q) Work.Construction.Qd) :
    ContinuousOn (fun z => Q z θ) (Ici L) := by
  intro z hz
  have hmem : (z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨lt_of_lt_of_le hL hz, hθ.1, hθ.2⟩
  have hd : DifferentiableAt ℝ (Function.uncurry Q) (z, θ) :=
    (hQ.contDiffAt (isOpen_Qd.mem_nhds hmem)).differentiableAt (by norm_num)
  exact (Work.Spaces.differentiableAt_curry_left hd).continuousAt.continuousWithinAt

/-! ## §2 Dilation, difference quotients, and their smoothness -/

/-- A dilation of the first variable preserves `ContDiffOn` on the quadrant (it maps the
quadrant into itself when the factor is positive). -/
theorem contDiffOn_dilate {P : ℝ → ℝ → ℝ} {c : ℝ} (hc : 0 < c) {n : WithTop ℕ∞}
    (h : ContDiffOn ℝ n (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => P (c * z) θ)) Work.Construction.Qd := by
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (c * p.1, p.2)) Work.Construction.Qd
      Work.Construction.Qd := by
    intro p hp
    rw [Work.FTS_StreamBdry.mem_Qd] at hp ⊢
    exact ⟨mul_pos hc hp.1, hp.2⟩
  have hf : ContDiffOn ℝ n (fun p : ℝ × ℝ => (c * p.1, p.2)) Work.Construction.Qd := by
    fun_prop
  have hcomp := h.comp hf hmaps
  convert hcomp using 1
  funext p
  rfl

/-- Pointwise version of `contDiffOn_dilate`. -/
theorem contDiffAt_dilate {P : ℝ → ℝ → ℝ} {c z θ : ℝ} {n : ℕ}
    (h : ContDiffAt ℝ (n : WithTop ℕ∞) (Function.uncurry P) (c * z, θ)) :
    ContDiffAt ℝ (n : WithTop ℕ∞) (Function.uncurry (fun z θ => P (c * z) θ)) (z, θ) := by
  have hf : ContDiffAt ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => (c * p.1, p.2)) (z, θ) := by
    fun_prop
  have hcomp := h.comp (z, θ) hf
  convert hcomp using 1
  funext p
  rfl

/-- Multiplying a `ContDiffOn` function by a constant (in the `curry`-form). -/
theorem contDiffOn_const_mul_field {A : ℝ → ℝ → ℝ} {a : ℝ} {n : WithTop ℕ∞}
    (hA : ContDiffOn ℝ n (Function.uncurry A) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => a * A z θ)) Work.Construction.Qd := by
  refine (hA.const_smul a).congr ?_
  intro p hp
  dsimp only [Function.uncurry, Pi.smul_apply]
  rw [smul_eq_mul]

/-- Multiplying a `ContDiffAt` function by a constant (in the `curry`-form). -/
theorem contDiffAt_const_mul_field {A : ℝ → ℝ → ℝ} {a z θ : ℝ}
    (hA : ContDiffAt ℝ 2 (Function.uncurry A) (z, θ)) :
    ContDiffAt ℝ 2 (Function.uncurry (fun z θ => a * A z θ)) (z, θ) := by
  refine (hA.const_smul a).congr_of_eventuallyEq ?_
  filter_upwards with p
  dsimp only [Function.uncurry, Pi.smul_apply]
  rw [smul_eq_mul]

/-- The first logarithmic difference quotient of `P` at step `h`. -/
def dilDiff (P : ℝ → ℝ → ℝ) (h : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (P (Real.exp h * z) θ - P z θ) / h

/-- The second logarithmic difference quotient of `P` at step `h`. -/
def dilDiff2 (P : ℝ → ℝ → ℝ) (h : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (P (Real.exp (2 * h) * z) θ - 2 * P (Real.exp h * z) θ + P z θ) / h ^ 2

theorem contDiffOn_dilDiff {P : ℝ → ℝ → ℝ} {h : ℝ} {n : WithTop ℕ∞}
    (hP : ContDiffOn ℝ n (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (dilDiff P h)) Work.Construction.Qd := by
  have hA : ContDiffOn ℝ n (Function.uncurry (fun z θ => P (Real.exp h * z) θ))
      Work.Construction.Qd := contDiffOn_dilate (Real.exp_pos h) hP
  have hsub : ContDiffOn ℝ n (Function.uncurry (fun z θ => P (Real.exp h * z) θ)
      - Function.uncurry P) Work.Construction.Qd := hA.sub hP
  refine (hsub.div_const h).congr ?_
  intro p hp
  simp only [Function.uncurry, Pi.sub_apply, dilDiff]

theorem contDiffOn_dilDiff2 {P : ℝ → ℝ → ℝ} {h : ℝ} {n : WithTop ℕ∞}
    (hP : ContDiffOn ℝ n (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (dilDiff2 P h)) Work.Construction.Qd := by
  have hA2 : ContDiffOn ℝ n (Function.uncurry (fun z θ => P (Real.exp (2 * h) * z) θ))
      Work.Construction.Qd := contDiffOn_dilate (Real.exp_pos (2 * h)) hP
  have hA1 : ContDiffOn ℝ n (Function.uncurry (fun z θ => P (Real.exp h * z) θ))
      Work.Construction.Qd := contDiffOn_dilate (Real.exp_pos h) hP
  have hc : ContDiffOn ℝ n (Function.uncurry (fun z θ => (2 : ℝ) * P (Real.exp h * z) θ))
      Work.Construction.Qd := contDiffOn_const_mul_field (a := (2 : ℝ)) hA1
  have hmain : ContDiffOn ℝ n (Function.uncurry (fun z θ =>
      P (Real.exp (2 * h) * z) θ - 2 * P (Real.exp h * z) θ + P z θ))
      Work.Construction.Qd := by
    refine ((hA2.sub hc).add hP).congr ?_
    intro p hp
    dsimp only [Function.uncurry, Pi.sub_apply, Pi.add_apply]
  refine (hmain.div_const (h ^ 2)).congr ?_
  intro p hp
  dsimp only [Function.uncurry, dilDiff2]

/-! ## §3 `bslOp` of the difference quotients -/

/-- The three-term linearity of `bslOp` at a point of the quadrant. -/
theorem bslOp_lin3 {α a b c : ℝ} {A B C : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hQd : (z, θ) ∈ Work.Construction.Qd)
    (hA : ContDiffAt ℝ 2 (Function.uncurry A) (z, θ))
    (hB : ContDiffAt ℝ 2 (Function.uncurry B) (z, θ))
    (hC : ContDiffAt ℝ 2 (Function.uncurry C) (z, θ)) :
    Work.Elliptic.bslOp α (fun z θ => a * A z θ + b * B z θ + c * C z θ) z θ
      = a * Work.Elliptic.bslOp α A z θ + b * Work.Elliptic.bslOp α B z θ
        + c * Work.Elliptic.bslOp α C z θ := by
  have hAB : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => a * A z θ + b * B z θ)) (z, θ) := by
    have h1 : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => a * A z θ)) (z, θ) :=
      contDiffAt_const_mul_field (a := a) hA
    have h2 : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => b * B z θ)) (z, θ) :=
      contDiffAt_const_mul_field (a := b) hB
    refine (h1.add h2).congr_of_eventuallyEq ?_
    filter_upwards with p
    dsimp only [Function.uncurry, Pi.add_apply]
  have h1 := Work.FTS_StreamBdry.SB25.bslOp_lincombQd α a b A B z θ hQd hA hB
  have h2 := Work.FTS_StreamBdry.SB25.bslOp_lincombQd α 1 c
    (fun z θ => a * A z θ + b * B z θ) C z θ hQd hAB hC
  have hc : Work.Elliptic.bslOp α (fun z θ => a * A z θ + b * B z θ + c * C z θ) z θ
      = Work.Elliptic.bslOp α (fun z θ =>
          1 * (fun z θ => a * A z θ + b * B z θ) z θ + c * C z θ) z θ := by
    apply Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq
    filter_upwards with q
    ring
  rw [hc, h2, h1]
  ring

/-- `bslOp` of the first difference quotient vanishes above `z = L`. -/
theorem bslOp_dilDiff_eq_zero {α L : ℝ} (hL : 0 < L) {P F : ℝ → ℝ → ℝ}
    (hP3 : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd)
    (hbsl : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Elliptic.bslOp α P z θ = F z θ)
    (hF0 : ∀ z θ, L ≤ z → θ ∈ Work.Spaces.Iθ → F z θ = 0)
    {h : ℝ} (hh : 0 < h) {z θ : ℝ} (hz : L < z) (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    Work.Elliptic.bslOp α (dilDiff P h) z θ = 0 := by
  have hz0 : 0 < z := lt_trans hL hz
  have hV : IsOpen Work.Construction.Qd := isOpen_Qd
  have hexp1 : 1 ≤ Real.exp h := Real.one_le_exp (le_of_lt hh)
  have hQd : (z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz0, hθ.1, hθ.2⟩
  have hmemA : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr
      ⟨mul_pos (lt_of_lt_of_le one_pos hexp1) hz0, hθ.1, hθ.2⟩
  have hA2 : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => P (Real.exp h * z) θ)) (z, θ) :=
    contDiffAt_dilate ((hP3.contDiffAt (hV.mem_nhds hmemA)).of_le (by norm_num))
  have hB2 : ContDiffAt ℝ 2 (Function.uncurry P) (z, θ) :=
    (hP3.contDiffAt (hV.mem_nhds hQd)).of_le (by norm_num)
  have hlin := Work.FTS_StreamBdry.SB25.bslOp_lincombQd α (1 / h) (-(1 / h))
    (fun z θ => P (Real.exp h * z) θ) P z θ hQd hA2 hB2
  have hdil := Work.FTS_StreamBdry.SB25.bslOp_dilate α (Real.exp h) P z θ
  have hcongr : Work.Elliptic.bslOp α (dilDiff P h) z θ
      = Work.Elliptic.bslOp α
          (fun z θ => (1 / h) * P (Real.exp h * z) θ + (-(1 / h)) * P z θ) z θ := by
    apply Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq
    filter_upwards with q
    simp only [dilDiff]
    ring
  have hA0 : Work.Elliptic.bslOp α (fun z θ => P (Real.exp h * z) θ) z θ = 0 := by
    rw [hdil, hbsl _ _ hmemA]
    exact hF0 _ _ (le_trans (le_of_lt hz)
      (le_mul_of_one_le_left (le_of_lt hz0) hexp1)) (Work.FTS_StreamBdry.Qd_theta_Iθ hmemA)
  have hB0 : Work.Elliptic.bslOp α P z θ = 0 := by
    rw [hbsl _ _ hQd]
    exact hF0 _ _ (le_of_lt hz) (Work.FTS_StreamBdry.Qd_theta_Iθ hQd)
  rw [hcongr, hlin, hA0, hB0, mul_zero, neg_mul, mul_zero, neg_zero, add_zero]

/-- `bslOp` of the second difference quotient vanishes above `z = L`. -/
theorem bslOp_dilDiff2_eq_zero {α L : ℝ} (hL : 0 < L) {P F : ℝ → ℝ → ℝ}
    (hP3 : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd)
    (hbsl : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Elliptic.bslOp α P z θ = F z θ)
    (hF0 : ∀ z θ, L ≤ z → θ ∈ Work.Spaces.Iθ → F z θ = 0)
    {h : ℝ} (hh : 0 < h) {z θ : ℝ} (hz : L < z) (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    Work.Elliptic.bslOp α (dilDiff2 P h) z θ = 0 := by
  have hz0 : 0 < z := lt_trans hL hz
  have hV : IsOpen Work.Construction.Qd := isOpen_Qd
  have h1 : (1 : ℝ) ≤ Real.exp h := Real.one_le_exp (le_of_lt hh)
  have h2 : (1 : ℝ) ≤ Real.exp (2 * h) := Real.one_le_exp (by positivity)
  have hQd : (z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz0, hθ.1, hθ.2⟩
  have hm2 : (Real.exp (2 * h) * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (lt_of_lt_of_le one_pos h2) hz0, hθ.1, hθ.2⟩
  have hm1 : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (lt_of_lt_of_le one_pos h1) hz0, hθ.1, hθ.2⟩
  have hA2 : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => P (Real.exp (2 * h) * z) θ)) (z, θ) :=
    contDiffAt_dilate ((hP3.contDiffAt (hV.mem_nhds hm2)).of_le (by norm_num))
  have hA1 : ContDiffAt ℝ 2 (Function.uncurry (fun z θ => P (Real.exp h * z) θ)) (z, θ) :=
    contDiffAt_dilate ((hP3.contDiffAt (hV.mem_nhds hm1)).of_le (by norm_num))
  have hB2 : ContDiffAt ℝ 2 (Function.uncurry P) (z, θ) :=
    (hP3.contDiffAt (hV.mem_nhds hQd)).of_le (by norm_num)
  have hlin := bslOp_lin3 (α := α) (a := 1 / h ^ 2) (b := -(2 / h ^ 2)) (c := 1 / h ^ 2)
    (A := fun z θ => P (Real.exp (2 * h) * z) θ) (B := fun z θ => P (Real.exp h * z) θ)
    (C := P) hQd hA2 hA1 hB2
  have hcongr : Work.Elliptic.bslOp α (dilDiff2 P h) z θ
      = Work.Elliptic.bslOp α (fun z θ => (1 / h ^ 2) * P (Real.exp (2 * h) * z) θ
          + (-(2 / h ^ 2)) * P (Real.exp h * z) θ + (1 / h ^ 2) * P z θ) z θ := by
    apply Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq
    filter_upwards with q
    simp only [dilDiff2]
    ring
  have hA20 : Work.Elliptic.bslOp α (fun z θ => P (Real.exp (2 * h) * z) θ) z θ = 0 := by
    rw [Work.FTS_StreamBdry.SB25.bslOp_dilate α (Real.exp (2 * h)) P z θ, hbsl _ _ hm2]
    exact hF0 _ _ (le_trans (le_of_lt hz)
      (le_mul_of_one_le_left (le_of_lt hz0) h2)) (Work.FTS_StreamBdry.Qd_theta_Iθ hm2)
  have hA10 : Work.Elliptic.bslOp α (fun z θ => P (Real.exp h * z) θ) z θ = 0 := by
    rw [Work.FTS_StreamBdry.SB25.bslOp_dilate α (Real.exp h) P z θ, hbsl _ _ hm1]
    exact hF0 _ _ (le_trans (le_of_lt hz)
      (le_mul_of_one_le_left (le_of_lt hz0) h1)) (Work.FTS_StreamBdry.Qd_theta_Iθ hm1)
  have hB0 : Work.Elliptic.bslOp α P z θ = 0 := by
    rw [hbsl _ _ hQd]
    exact hF0 _ _ (le_of_lt hz) (Work.FTS_StreamBdry.Qd_theta_Iθ hQd)
  rw [hcongr, hlin, hA20, hA10, hB0]
  ring


end

end Work.FTS_StreamBdry.SB5
