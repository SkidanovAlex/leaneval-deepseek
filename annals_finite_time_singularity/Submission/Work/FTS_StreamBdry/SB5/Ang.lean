import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
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
import Submission.Work.FTS_StreamBdry.SB5.Prep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB5.Ang` — angular derivatives, bounds and decay of the dilate difference quotients.
-/

namespace Work.FTS_StreamBdry.SB5

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## §4 The angular derivatives of the difference quotients -/

theorem pth_dilDiff {P : ℝ → ℝ → ℝ} {h z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun θ' => P (Real.exp h * z) θ') θ)
    (hB : DifferentiableAt ℝ (fun θ' => P z θ') θ) :
    Work.Spaces.pth (dilDiff P h) z θ
      = (Work.Spaces.pth P (Real.exp h * z) θ - Work.Spaces.pth P z θ) / h := by
  show deriv (fun θ' => (P (Real.exp h * z) θ' - P z θ') / h) θ = _
  rw [deriv_div_const,
    show (fun θ' => P (Real.exp h * z) θ' - P z θ')
      = (fun θ' => P (Real.exp h * z) θ') - (fun θ' => P z θ') from rfl,
    deriv_sub hA hB]
  simp only [Work.Spaces.pth]

theorem pth_dilDiff2 {P : ℝ → ℝ → ℝ} {h z θ : ℝ}
    (hA : DifferentiableAt ℝ (fun θ' => P (Real.exp (2 * h) * z) θ') θ)
    (hB : DifferentiableAt ℝ (fun θ' => P (Real.exp h * z) θ') θ)
    (hC : DifferentiableAt ℝ (fun θ' => P z θ') θ) :
    Work.Spaces.pth (dilDiff2 P h) z θ
      = (Work.Spaces.pth P (Real.exp (2 * h) * z) θ - 2 * Work.Spaces.pth P (Real.exp h * z) θ
          + Work.Spaces.pth P z θ) / h ^ 2 := by
  show deriv (fun θ' => (P (Real.exp (2 * h) * z) θ' - 2 * P (Real.exp h * z) θ' + P z θ') / h ^ 2)
    θ = _
  rw [deriv_div_const,
    show (fun θ' => P (Real.exp (2 * h) * z) θ' - 2 * P (Real.exp h * z) θ' + P z θ')
      = ((fun θ' => P (Real.exp (2 * h) * z) θ') - (fun θ' => 2 * P (Real.exp h * z) θ'))
        + (fun θ' => P z θ') from rfl,
    deriv_add (hA.sub (hB.const_mul 2)) hC, deriv_sub hA (hB.const_mul 2),
    deriv_const_mul_field]
  simp only [Work.Spaces.pth]

theorem pthIter2_dilDiff {P : ℝ → ℝ → ℝ} {h z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hPd : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry P) (z', θ'))
    (hPd2 : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth P)) (z', θ')) :
    Work.Spaces.pthIter 2 (dilDiff P h) z θ
      = (Work.Spaces.pthIter 2 P (Real.exp h * z) θ - Work.Spaces.pthIter 2 P z θ) / h := by
  have hmem : ∀ θ' ∈ Ioo (0 : ℝ) (π / 2), (z, θ') ∈ Work.Construction.Qd := fun θ' hθ' =>
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθ'.1, hθ'.2⟩
  have hev : (fun θ' => Work.Spaces.pth (dilDiff P h) z θ')
      =ᶠ[𝓝 θ] (fun θ' => (Work.Spaces.pth P (Real.exp h * z) θ'
        - Work.Spaces.pth P z θ') / h) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact pth_dilDiff
      (Work.Spaces.differentiableAt_curry_right (hPd (Real.exp h * z) θ'
        (Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz, hθ'.1, hθ'.2⟩)))
      (Work.Spaces.differentiableAt_curry_right (hPd z θ' (hmem θ' hθ')))
  rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  show deriv (fun θ' => Work.Spaces.pth (dilDiff P h) z θ') θ = _
  rw [hev.deriv_eq]
  show deriv (fun θ' => (Work.Spaces.pth P (Real.exp h * z) θ'
    - Work.Spaces.pth P z θ') / h) θ = _
  rw [deriv_div_const,
    show (fun θ' => Work.Spaces.pth P (Real.exp h * z) θ' - Work.Spaces.pth P z θ')
      = (fun θ' => Work.Spaces.pth P (Real.exp h * z) θ')
        - (fun θ' => Work.Spaces.pth P z θ') from rfl,
    deriv_sub
      (Work.Spaces.differentiableAt_curry_right (hPd2 (Real.exp h * z) θ
        (Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz, hθ.1, hθ.2⟩)))
      (Work.Spaces.differentiableAt_curry_right (hPd2 z θ (hmem θ hθ)))]
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]

theorem pthIter2_dilDiff2 {P : ℝ → ℝ → ℝ} {h z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hPd : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry P) (z', θ'))
    (hPd2 : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth P)) (z', θ')) :
    Work.Spaces.pthIter 2 (dilDiff2 P h) z θ
      = (Work.Spaces.pthIter 2 P (Real.exp (2 * h) * z) θ
          - 2 * Work.Spaces.pthIter 2 P (Real.exp h * z) θ
          + Work.Spaces.pthIter 2 P z θ) / h ^ 2 := by
  have hmem : ∀ θ' ∈ Ioo (0 : ℝ) (π / 2), (z, θ') ∈ Work.Construction.Qd := fun θ' hθ' =>
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθ'.1, hθ'.2⟩
  have hev : (fun θ' => Work.Spaces.pth (dilDiff2 P h) z θ')
      =ᶠ[𝓝 θ] (fun θ' => (Work.Spaces.pth P (Real.exp (2 * h) * z) θ'
          - 2 * Work.Spaces.pth P (Real.exp h * z) θ' + Work.Spaces.pth P z θ') / h ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact pth_dilDiff2
      (Work.Spaces.differentiableAt_curry_right (hPd (Real.exp (2 * h) * z) θ'
        (Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos (2 * h)) hz, hθ'.1, hθ'.2⟩)))
      (Work.Spaces.differentiableAt_curry_right (hPd (Real.exp h * z) θ'
        (Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz, hθ'.1, hθ'.2⟩)))
      (Work.Spaces.differentiableAt_curry_right (hPd z θ' (hmem θ' hθ')))
  rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  show deriv (fun θ' => Work.Spaces.pth (dilDiff2 P h) z θ') θ = _
  rw [hev.deriv_eq]
  show deriv (fun θ' => (Work.Spaces.pth P (Real.exp (2 * h) * z) θ'
    - 2 * Work.Spaces.pth P (Real.exp h * z) θ' + Work.Spaces.pth P z θ') / h ^ 2) θ = _
  have ha : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth P (Real.exp (2 * h) * z) θ') θ :=
    Work.Spaces.differentiableAt_curry_right (hPd2 (Real.exp (2 * h) * z) θ
      (Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos (2 * h)) hz, hθ.1, hθ.2⟩))
  have hb : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth P (Real.exp h * z) θ') θ :=
    Work.Spaces.differentiableAt_curry_right (hPd2 (Real.exp h * z) θ
      (Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz, hθ.1, hθ.2⟩))
  have hc : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth P z θ') θ :=
    Work.Spaces.differentiableAt_curry_right (hPd2 z θ (hmem θ hθ))
  rw [deriv_div_const,
    show (fun θ' => Work.Spaces.pth P (Real.exp (2 * h) * z) θ'
        - 2 * Work.Spaces.pth P (Real.exp h * z) θ' + Work.Spaces.pth P z θ')
      = ((fun θ' => Work.Spaces.pth P (Real.exp (2 * h) * z) θ')
          - (fun θ' => 2 * Work.Spaces.pth P (Real.exp h * z) θ'))
        + (fun θ' => Work.Spaces.pth P z θ') from rfl,
    deriv_add (ha.sub (hb.const_mul 2)) hc, deriv_sub ha (hb.const_mul 2),
    deriv_const_mul_field]
  rw [show deriv (Work.Spaces.pth P (Real.exp (2 * h) * z)) θ
        = Work.Spaces.pthIter 2 P (Real.exp (2 * h) * z) θ from rfl,
      show deriv (Work.Spaces.pth P (Real.exp h * z)) θ
        = Work.Spaces.pthIter 2 P (Real.exp h * z) θ from rfl,
      show deriv (Work.Spaces.pth P z) θ = Work.Spaces.pthIter 2 P z θ from rfl]

/-- `dilDiff` of a `C³` function is `C²`. -/
theorem contDiffOn_dilDiff_three {P : ℝ → ℝ → ℝ} {h : ℝ}
    (hP : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (dilDiff P h)) Work.Construction.Qd :=
  contDiffOn_dilDiff (h := h) (n := 2) (hP.of_le (by norm_num))

/-- `dilDiff2` of a `C³` function is `C²`. -/
theorem contDiffOn_dilDiff2_three {P : ℝ → ℝ → ℝ} {h : ℝ}
    (hP : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ 2 (Function.uncurry (dilDiff2 P h)) Work.Construction.Qd :=
  contDiffOn_dilDiff2 (h := h) (n := 2) (hP.of_le (by norm_num))

/-! ## §5 Bounds on the difference quotients -/

/-- A pointwise `sin 2θ` bound on `P` gives one on the first difference quotient. -/
theorem abs_dilDiff_le_s2 {P : ℝ → ℝ → ℝ} {M h z θ : ℝ} (hh : 0 < h)
    (hP : ∀ w θ, (w, θ) ∈ Work.Construction.Qd → |P w θ| ≤ M * Work.Construction.s2 θ)
    (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    |dilDiff P h z θ| ≤ (2 * M / h) * Work.Construction.s2 θ := by
  obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
  have hm : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz0, hθ1, hθ2⟩
  have h1 := hP (Real.exp h * z) θ hm
  have h2 := hP z θ hzθ
  have hmain : |P (Real.exp h * z) θ - P z θ| ≤ 2 * M * Work.Construction.s2 θ := by
    calc |P (Real.exp h * z) θ - P z θ| ≤ |P (Real.exp h * z) θ| + |P z θ| := abs_sub _ _
      _ ≤ M * Work.Construction.s2 θ + M * Work.Construction.s2 θ := add_le_add h1 h2
      _ = 2 * M * Work.Construction.s2 θ := by ring
  rw [dilDiff, abs_div, abs_of_pos hh]
  calc |P (Real.exp h * z) θ - P z θ| / h ≤ (2 * M * Work.Construction.s2 θ) / h :=
        div_le_div_of_nonneg_right hmain (le_of_lt hh)
    _ = (2 * M / h) * Work.Construction.s2 θ := by ring

/-- The same for the second difference quotient. -/
theorem abs_dilDiff2_le_s2 {P : ℝ → ℝ → ℝ} {M h z θ : ℝ} (hh : 0 < h)
    (hP : ∀ w θ, (w, θ) ∈ Work.Construction.Qd → |P w θ| ≤ M * Work.Construction.s2 θ)
    (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    |dilDiff2 P h z θ| ≤ (4 * M / h ^ 2) * Work.Construction.s2 θ := by
  obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
  have hm2 : (Real.exp (2 * h) * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos (2 * h)) hz0, hθ1, hθ2⟩
  have hm1 : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz0, hθ1, hθ2⟩
  have h1 := hP (Real.exp (2 * h) * z) θ hm2
  have h2 := hP (Real.exp h * z) θ hm1
  have h3 := hP z θ hzθ
  have hb : |2 * P (Real.exp h * z) θ| ≤ 2 * (M * Work.Construction.s2 θ) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have hmain : |P (Real.exp (2 * h) * z) θ - 2 * P (Real.exp h * z) θ + P z θ|
      ≤ 4 * M * Work.Construction.s2 θ := by
    calc |P (Real.exp (2 * h) * z) θ - 2 * P (Real.exp h * z) θ + P z θ|
        ≤ |P (Real.exp (2 * h) * z) θ - 2 * P (Real.exp h * z) θ| + |P z θ| := abs_add_le _ _
      _ ≤ (|P (Real.exp (2 * h) * z) θ| + |2 * P (Real.exp h * z) θ|) + |P z θ| :=
          add_le_add (abs_sub _ _) le_rfl
      _ ≤ (M * Work.Construction.s2 θ + 2 * (M * Work.Construction.s2 θ))
            + M * Work.Construction.s2 θ := add_le_add (add_le_add h1 hb) h3
      _ = 4 * M * Work.Construction.s2 θ := by ring
  have hh2 : 0 < h ^ 2 := by positivity
  rw [dilDiff2, abs_div, abs_of_pos hh2]
  calc |P (Real.exp (2 * h) * z) θ - 2 * P (Real.exp h * z) θ + P z θ| / h ^ 2
      ≤ (4 * M * Work.Construction.s2 θ) / h ^ 2 :=
        div_le_div_of_nonneg_right hmain (le_of_lt hh2)
    _ = (4 * M / h ^ 2) * Work.Construction.s2 θ := by ring

/-- The `θ`-derivative bound for the first difference quotient. -/
theorem abs_pth_dilDiff_le {P : ℝ → ℝ → ℝ} {h K : ℝ} (hh : 0 < h)
    (hK : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pth P z θ| ≤ K)
    (hPd : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry P) (z', θ'))
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    |Work.Spaces.pth (dilDiff P h) z θ| ≤ 2 * K / h := by
  obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
  have hm : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz0, hθ1, hθ2⟩
  have hmain : |Work.Spaces.pth P (Real.exp h * z) θ - Work.Spaces.pth P z θ| ≤ 2 * K := by
    calc |Work.Spaces.pth P (Real.exp h * z) θ - Work.Spaces.pth P z θ|
        ≤ |Work.Spaces.pth P (Real.exp h * z) θ| + |Work.Spaces.pth P z θ| := abs_sub _ _
      _ ≤ K + K := add_le_add (hK _ _ hm) (hK _ _ hzθ)
      _ = 2 * K := by ring
  rw [pth_dilDiff
      (Work.Spaces.differentiableAt_curry_right (hPd (Real.exp h * z) θ hm))
      (Work.Spaces.differentiableAt_curry_right (hPd z θ hzθ)),
    abs_div, abs_of_pos hh]
  calc |Work.Spaces.pth P (Real.exp h * z) θ - Work.Spaces.pth P z θ| / h
      ≤ (2 * K) / h := div_le_div_of_nonneg_right hmain (le_of_lt hh)
    _ = 2 * K / h := rfl

/-- The second `θ`-derivative bound for the first difference quotient. -/
theorem abs_pthIter2_dilDiff_le {P : ℝ → ℝ → ℝ} {h K : ℝ} (hh : 0 < h)
    (hK : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pthIter 2 P z θ| ≤ K)
    (hPd : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry P) (z', θ'))
    (hPd2 : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth P)) (z', θ'))
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    |Work.Spaces.pthIter 2 (dilDiff P h) z θ| ≤ 2 * K / h := by
  obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
  have hm : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz0, hθ1, hθ2⟩
  have hmain : |Work.Spaces.pthIter 2 P (Real.exp h * z) θ - Work.Spaces.pthIter 2 P z θ|
      ≤ 2 * K := by
    calc |Work.Spaces.pthIter 2 P (Real.exp h * z) θ - Work.Spaces.pthIter 2 P z θ|
        ≤ |Work.Spaces.pthIter 2 P (Real.exp h * z) θ| + |Work.Spaces.pthIter 2 P z θ| :=
          abs_sub _ _
      _ ≤ K + K := add_le_add (hK _ _ hm) (hK _ _ hzθ)
      _ = 2 * K := by ring
  rw [pthIter2_dilDiff hz0 ⟨hθ1, hθ2⟩ hPd hPd2, abs_div, abs_of_pos hh]
  calc |Work.Spaces.pthIter 2 P (Real.exp h * z) θ - Work.Spaces.pthIter 2 P z θ| / h
      ≤ (2 * K) / h := div_le_div_of_nonneg_right hmain (le_of_lt hh)
    _ = 2 * K / h := rfl

/-- The `θ`-derivative bound for the second difference quotient. -/
theorem abs_pth_dilDiff2_le {P : ℝ → ℝ → ℝ} {h K : ℝ} (hh : 0 < h)
    (hK : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pth P z θ| ≤ K)
    (hPd : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry P) (z', θ'))
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    |Work.Spaces.pth (dilDiff2 P h) z θ| ≤ 4 * K / h ^ 2 := by
  obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
  have hm2 : (Real.exp (2 * h) * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos (2 * h)) hz0, hθ1, hθ2⟩
  have hm1 : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz0, hθ1, hθ2⟩
  have hb : |2 * Work.Spaces.pth P (Real.exp h * z) θ| ≤ 2 * K := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (hK _ _ hm1) (by norm_num)
  have hmain : |Work.Spaces.pth P (Real.exp (2 * h) * z) θ
      - 2 * Work.Spaces.pth P (Real.exp h * z) θ + Work.Spaces.pth P z θ| ≤ 4 * K := by
    calc |Work.Spaces.pth P (Real.exp (2 * h) * z) θ
          - 2 * Work.Spaces.pth P (Real.exp h * z) θ + Work.Spaces.pth P z θ|
        ≤ |Work.Spaces.pth P (Real.exp (2 * h) * z) θ
            - 2 * Work.Spaces.pth P (Real.exp h * z) θ| + |Work.Spaces.pth P z θ| :=
          abs_add_le _ _
      _ ≤ (|Work.Spaces.pth P (Real.exp (2 * h) * z) θ|
            + |2 * Work.Spaces.pth P (Real.exp h * z) θ|) + |Work.Spaces.pth P z θ| :=
          add_le_add (abs_sub _ _) le_rfl
      _ ≤ (K + 2 * K) + K := add_le_add (add_le_add (hK _ _ hm2) hb) (hK _ _ hzθ)
      _ = 4 * K := by ring
  have hh2 : 0 < h ^ 2 := by positivity
  rw [pth_dilDiff2
      (Work.Spaces.differentiableAt_curry_right (hPd (Real.exp (2 * h) * z) θ hm2))
      (Work.Spaces.differentiableAt_curry_right (hPd (Real.exp h * z) θ hm1))
      (Work.Spaces.differentiableAt_curry_right (hPd z θ hzθ)),
    abs_div, abs_of_pos hh2]
  calc |Work.Spaces.pth P (Real.exp (2 * h) * z) θ - 2 * Work.Spaces.pth P (Real.exp h * z) θ
        + Work.Spaces.pth P z θ| / h ^ 2
      ≤ (4 * K) / h ^ 2 := div_le_div_of_nonneg_right hmain (le_of_lt hh2)
    _ = 4 * K / h ^ 2 := rfl

/-- The second `θ`-derivative bound for the second difference quotient. -/
theorem abs_pthIter2_dilDiff2_le {P : ℝ → ℝ → ℝ} {h K : ℝ} (hh : 0 < h)
    (hK : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pthIter 2 P z θ| ≤ K)
    (hPd : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry P) (z', θ'))
    (hPd2 : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth P)) (z', θ'))
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.Construction.Qd) :
    |Work.Spaces.pthIter 2 (dilDiff2 P h) z θ| ≤ 4 * K / h ^ 2 := by
  obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
  have hm2 : (Real.exp (2 * h) * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos (2 * h)) hz0, hθ1, hθ2⟩
  have hm1 : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz0, hθ1, hθ2⟩
  have hb : |2 * Work.Spaces.pthIter 2 P (Real.exp h * z) θ| ≤ 2 * K := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (hK _ _ hm1) (by norm_num)
  have hmain : |Work.Spaces.pthIter 2 P (Real.exp (2 * h) * z) θ
      - 2 * Work.Spaces.pthIter 2 P (Real.exp h * z) θ + Work.Spaces.pthIter 2 P z θ|
      ≤ 4 * K := by
    calc |Work.Spaces.pthIter 2 P (Real.exp (2 * h) * z) θ
          - 2 * Work.Spaces.pthIter 2 P (Real.exp h * z) θ + Work.Spaces.pthIter 2 P z θ|
        ≤ |Work.Spaces.pthIter 2 P (Real.exp (2 * h) * z) θ
            - 2 * Work.Spaces.pthIter 2 P (Real.exp h * z) θ|
          + |Work.Spaces.pthIter 2 P z θ| := abs_add_le _ _
      _ ≤ (|Work.Spaces.pthIter 2 P (Real.exp (2 * h) * z) θ|
            + |2 * Work.Spaces.pthIter 2 P (Real.exp h * z) θ|)
          + |Work.Spaces.pthIter 2 P z θ| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ (K + 2 * K) + K := add_le_add (add_le_add (hK _ _ hm2) hb) (hK _ _ hzθ)
      _ = 4 * K := by ring
  have hh2 : 0 < h ^ 2 := by positivity
  rw [pthIter2_dilDiff2 hz0 ⟨hθ1, hθ2⟩ hPd hPd2, abs_div, abs_of_pos hh2]
  calc |Work.Spaces.pthIter 2 P (Real.exp (2 * h) * z) θ
        - 2 * Work.Spaces.pthIter 2 P (Real.exp h * z) θ + Work.Spaces.pthIter 2 P z θ| / h ^ 2
      ≤ (4 * K) / h ^ 2 := div_le_div_of_nonneg_right hmain (le_of_lt hh2)
    _ = 4 * K / h ^ 2 := rfl

/-! ## §6 Decay in `z` of the difference quotients -/

/-- At a fixed `θ`, the first difference quotient of `P` inherits the decay of `P` in `z`. -/
theorem tendsto_dilDiff_atTop {P : ℝ → ℝ → ℝ} {h θ : ℝ} (hh : 0 < h)
    (hdec : Tendsto (fun z => P z θ) atTop (𝓝 0)) :
    Tendsto (fun z => dilDiff P h z θ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ => P (Real.exp h * z) θ) atTop (𝓝 0) :=
    hdec.comp (Filter.Tendsto.const_mul_atTop (Real.exp_pos h) Filter.tendsto_id)
  have h2 : Tendsto (fun z : ℝ => P (Real.exp h * z) θ - P z θ) atTop (𝓝 (0 - 0)) :=
    h1.sub hdec
  have h3 := h2.div_const h
  simpa only [dilDiff, sub_self, zero_div] using h3

/-- At a fixed `θ`, the second difference quotient of `P` inherits the decay of `P` in `z`. -/
theorem tendsto_dilDiff2_atTop {P : ℝ → ℝ → ℝ} {h θ : ℝ} (hh : 0 < h)
    (hdec : Tendsto (fun z => P z θ) atTop (𝓝 0)) :
    Tendsto (fun z => dilDiff2 P h z θ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ => P (Real.exp (2 * h) * z) θ) atTop (𝓝 0) :=
    hdec.comp (Filter.Tendsto.const_mul_atTop (Real.exp_pos (2 * h)) Filter.tendsto_id)
  have h2 : Tendsto (fun z : ℝ => P (Real.exp h * z) θ) atTop (𝓝 0) :=
    hdec.comp (Filter.Tendsto.const_mul_atTop (Real.exp_pos h) Filter.tendsto_id)
  have h3 : Tendsto (fun z : ℝ => P (Real.exp (2 * h) * z) θ - 2 * P (Real.exp h * z) θ
      + P z θ) atTop (𝓝 (0 - 2 * 0 + 0)) := (h1.sub (h2.const_mul 2)).add hdec
  have h4 := h3.div_const (h ^ 2)
  simpa only [dilDiff2, sub_self, mul_zero, zero_add, zero_div] using h4

/-- Wrapper around the E5 lemma: uniform decay in `θ` out of pointwise decay, `θ`-derivative
bounds and vanishing at the two ends. -/
theorem uniform_decay_of_data {Q : ℝ → ℝ → ℝ} {K : ℝ}
    (hdiff : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun θ' => Q z θ') θ ∧
        DifferentiableAt ℝ (fun θ' => Work.Spaces.pth Q z θ') θ)
    (h1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pth Q z θ| ≤ K)
    (h2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pthIter 2 Q z θ| ≤ K)
    (hend : ∀ z, 0 < z → Tendsto (fun θ => Q z θ) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun θ => Q z θ) (𝓝[<] (π / 2)) (𝓝 0))
    (hdec : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), Tendsto (fun z => Q z θ) atTop (𝓝 0)) :
    ∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) →
      |Q z θ| ≤ ε * Work.Construction.s2 θ :=
  Work.FTS_StreamBdry.SB5Aux.unif_decay_ratio_proved Q K hdiff h1 h2 hend hdec

/-! ## §7 The pointwise `θ`-differentiability of the difference quotients -/

theorem differentiableAt_pth_dilDiff {P : ℝ → ℝ → ℝ} {h z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hPd : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry P) (z', θ'))
    (hPd2 : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth P)) (z', θ')) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.pth (dilDiff P h) z θ') θ := by
  have hmem : (z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩
  have hm : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz, hθ.1, hθ.2⟩
  have hev : (fun θ' => Work.Spaces.pth (dilDiff P h) z θ')
      =ᶠ[𝓝 θ] (fun θ' => (Work.Spaces.pth P (Real.exp h * z) θ'
        - Work.Spaces.pth P z θ') / h) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact pth_dilDiff
      (Work.Spaces.differentiableAt_curry_right (hPd (Real.exp h * z) θ'
        (Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz, hθ'.1, hθ'.2⟩)))
      (Work.Spaces.differentiableAt_curry_right (hPd z θ'
        (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθ'.1, hθ'.2⟩)))
  refine hev.differentiableAt_iff.mpr ?_
  exact ((Work.Spaces.differentiableAt_curry_right (hPd2 (Real.exp h * z) θ hm)).sub
    (Work.Spaces.differentiableAt_curry_right (hPd2 z θ hmem))).div_const h

theorem differentiableAt_pth_dilDiff2 {P : ℝ → ℝ → ℝ} {h z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hPd : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry P) (z', θ'))
    (hPd2 : ∀ z' θ', (z', θ') ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth P)) (z', θ')) :
    DifferentiableAt ℝ (fun θ' => Work.Spaces.pth (dilDiff2 P h) z θ') θ := by
  have hmem : (z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθ.1, hθ.2⟩
  have hm2 : (Real.exp (2 * h) * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos (2 * h)) hz, hθ.1, hθ.2⟩
  have hm1 : (Real.exp h * z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz, hθ.1, hθ.2⟩
  have hev : (fun θ' => Work.Spaces.pth (dilDiff2 P h) z θ')
      =ᶠ[𝓝 θ] (fun θ' => (Work.Spaces.pth P (Real.exp (2 * h) * z) θ'
          - 2 * Work.Spaces.pth P (Real.exp h * z) θ' + Work.Spaces.pth P z θ') / h ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact pth_dilDiff2
      (Work.Spaces.differentiableAt_curry_right (hPd (Real.exp (2 * h) * z) θ'
        (Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos (2 * h)) hz, hθ'.1, hθ'.2⟩)))
      (Work.Spaces.differentiableAt_curry_right (hPd (Real.exp h * z) θ'
        (Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos (Real.exp_pos h) hz, hθ'.1, hθ'.2⟩)))
      (Work.Spaces.differentiableAt_curry_right (hPd z θ'
        (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθ'.1, hθ'.2⟩)))
  refine hev.differentiableAt_iff.mpr ?_
  exact (((Work.Spaces.differentiableAt_curry_right (hPd2 (Real.exp (2 * h) * z) θ hm2)).sub
    ((Work.Spaces.differentiableAt_curry_right (hPd2 (Real.exp h * z) θ hm1)).const_mul 2)).add
    (Work.Spaces.differentiableAt_curry_right (hPd2 z θ hmem))).div_const (h ^ 2)

/-! ## §8 Slice continuity of the `D_z`-iterates -/

theorem contDiffOn_DzIter_one {P : ℝ → ℝ → ℝ} {n : ℕ}
    (hP : ContDiffOn ℝ (n + 1) (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter 1 P)) Work.Construction.Qd := by
  have h := Work.FTS_StreamBdry.SB3.P2Aux.Dz_smooth_of (V := Work.Construction.Qd) isOpen_Qd
    (n := n) (Q := P) hP
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h

theorem contDiffOn_DzIter_two {P : ℝ → ℝ → ℝ} {n : ℕ}
    (hP : ContDiffOn ℝ (n + 2) (Function.uncurry P) Work.Construction.Qd) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter 2 P)) Work.Construction.Qd := by
  have hP' : ContDiffOn ℝ (((n + 1 : ℕ) : WithTop ℕ∞) + 1) (Function.uncurry P)
      Work.Construction.Qd := hP.of_le (le_of_eq (by push_cast; ring))
  have h1 : ContDiffOn ℝ (n + 1) (Function.uncurry (Work.Spaces.DzIter 1 P))
      Work.Construction.Qd := contDiffOn_DzIter_one (P := P) (n := n + 1) hP'
  exact contDiffOn_DzIter_one (P := Work.Spaces.DzIter 1 P) (n := n) h1
