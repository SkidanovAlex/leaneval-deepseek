import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
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
import Submission.Work.FTS_StreamBdry.SB5.Ang

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB5.Core` — the core decay lemma `sb5_decay_core` and the `psiP` `θ`-bounds.
-/

namespace Work.FTS_StreamBdry.SB5

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false

noncomputable section

/-! ## §9 The core decay lemma -/

/-- **Core decay.**  If `P` is the `U`-slot part with source `F` supported in `z < L`, with the
`D_z`-bounds `|D_z^j P| ≤ M sin 2θ` (`j ≤ 2`), the `θ`-bounds `|∂_θP|, |∂_θ²P| ≤ K` and the
pointwise decay `P z θ → 0` (`z → ∞`) at every fixed `θ ∈ (0,π/2)`, then
`|D_z^j P z θ| ≤ M sin 2θ (L/z)^{4/α}` for `z ≥ L`, `j ≤ 2`. -/
theorem sb5_decay_core {α M L K : ℝ} (hα : 0 < α) (hL : 0 < L) {P F : ℝ → ℝ → ℝ}
    (hP3 : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd)
    (hbsl : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Elliptic.bslOp α P z θ = F z θ)
    (hF0 : ∀ z θ, L ≤ z → θ ∈ Work.Spaces.Iθ → F z θ = 0)
    (hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j P z θ| ≤ M * Work.Construction.s2 θ)
    (hK1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pth P z θ| ≤ K)
    (hK2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.pthIter 2 P z θ| ≤ K)
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => P z θ) atTop (𝓝 0))
    (hbar : Work.FTS.StreamBdryIface.SB5Barrier) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j P z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hαk_eq : α * (4 / α) = 4 := by field_simp
  have hαk : 0 < α * (4 / α) := by rw [hαk_eq]; norm_num
  have hαk5 : α * (4 / α) < 5 := by rw [hαk_eq]; norm_num
  have hV : IsOpen Work.Construction.Qd := isOpen_Qd
  have hPd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry P) (z, θ) := fun z θ hzθ =>
    (hP3.contDiffAt (hV.mem_nhds hzθ)).differentiableAt (by norm_num)
  have hPth : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth P)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.contDiffOn_uncurry_pth_qd (n := 2)
      (show ContDiffOn ℝ ((2 : WithTop ℕ∞) + 1) (Function.uncurry P)
        Work.Construction.Qd from hP3)
  have hPd2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pth P)) (z, θ) := fun z θ hzθ =>
    (hPth.contDiffAt (hV.mem_nhds hzθ)).differentiableAt (by norm_num)
  have hsquare : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun θ' => P z θ') θ ∧
        DifferentiableAt ℝ (fun θ' => Work.Spaces.pth P z θ') θ := fun z θ hzθ =>
    ⟨Work.Spaces.differentiableAt_curry_right (hPd z θ hzθ),
      Work.Spaces.differentiableAt_curry_right (hPd2 z θ hzθ)⟩
  -- the `sb5_compare` mechanism, with the four variable hypotheses supplied per function
  have hcompare : ∀ (Q : ℝ → ℝ → ℝ) (Mb : ℝ),
      ContDiffOn ℝ 2 (Function.uncurry Q) Work.Construction.Qd →
      (∀ z θ, L < z → θ ∈ Ioo (0 : ℝ) (π / 2) → Work.Elliptic.bslOp α Q z θ = 0) →
      (∀ z θ, L ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) → |Q z θ| ≤ Mb * Work.Construction.s2 θ) →
      (∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo (0 : ℝ) (π / 2) →
        |Q z θ| ≤ ε * Work.Construction.s2 θ) →
      ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
        |Q z θ| ≤ Mb * Work.Construction.s2 θ * (L / z) ^ (4 / α) :=
    fun Q Mb hC2 hbslQ hbdQ hdecQ z θ hzθ hLz =>
      Work.FTS_StreamBdry.SB25.sb5_compare α (4 / α) L Mb Q hα hL hαk hαk5 hbar hC2 hbslQ
        hbdQ hdecQ z θ hLz (Work.FTS_StreamBdry.mem_Qd.mp hzθ).2
  -- ## j = 0
  have hj0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      |P z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
    intro z θ hzθ hLz
    obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
    exact hcompare P M (hP3.of_le (by norm_num))
      (fun z θ hz hθ => by
        have hmem : (z, θ) ∈ Work.Construction.Qd :=
          Work.FTS_StreamBdry.mem_Qd.mpr ⟨lt_trans hL hz, hθ.1, hθ.2⟩
        rw [hbsl z θ hmem]
        exact hF0 z θ (le_of_lt hz) (Work.FTS_StreamBdry.Qd_theta_Iθ hmem))
      (fun z θ hz hθ =>
        hDz z θ (Work.FTS_StreamBdry.mem_Qd.mpr ⟨lt_of_lt_of_le hL hz, hθ.1, hθ.2⟩)
          0 (by norm_num))
      (fun ε hε => uniform_decay_of_data hsquare hK1 hK2
        (fun z hz => tendsto_zero_endpoints_of_abs_le_s2
          (fun z θ hzθ => hDz z θ hzθ 0 (by norm_num)) hz)
        (fun θ hθ => hdec θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) ε hε)
      z θ hzθ hLz
  -- ## j = 1
  have hj1 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      |Work.Spaces.DzIter 1 P z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
    intro z θ hzθ hLz
    obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
    have hdecθ : Tendsto (fun z => P z θ) atTop (𝓝 0) := hdec θ ⟨le_of_lt hθ1, le_of_lt hθ2⟩
    rcases eq_or_lt_of_le hLz with hzL | hzLt
    · rw [hzL, div_self (ne_of_gt hz0), Real.one_rpow, mul_one]
      exact hDz z θ hzθ 1 (by norm_num)
    · have hconv : Tendsto (fun h' : ℝ => dilDiff P h' z θ) (𝓝[>] (0 : ℝ))
          (𝓝 (Work.Spaces.DzIter 1 P z θ)) := by
        have hdq := Work.FTS_StreamBdry.SB25.dq1_facts (fun z' => P z' θ) L
          (M * Work.Construction.s2 θ) hL
          (fun z' hz' => Work.Spaces.differentiableAt_curry_left
            (hPd z' θ (Work.FTS_StreamBdry.mem_Qd.mpr
              ⟨lt_of_lt_of_le hL hz', hθ1, hθ2⟩)))
          (fun z' hz' => by
            have h := hDz z' θ (Work.FTS_StreamBdry.mem_Qd.mpr
              ⟨lt_of_lt_of_le hL hz', hθ1, hθ2⟩) 1 (by norm_num)
            simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
              Work.Spaces.pz] using h)
        simpa only [dilDiff, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
          Work.Spaces.pz] using hdq.2 z hzLt
      have hbound : ∀ᶠ h' in 𝓝[>] (0 : ℝ),
          |dilDiff P h' z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
        filter_upwards [self_mem_nhdsWithin] with h' hh'
        exact hcompare (dilDiff P h') M (contDiffOn_dilDiff_three (h := h') hP3)
          (fun z' θ' hz' hθ' => bslOp_dilDiff_eq_zero hL hP3 hbsl hF0 hh' hz' hθ')
          (fun z' θ' hz' hθ' => by
            have h := (Work.FTS_StreamBdry.SB25.dq1_facts (fun z'' => P z'' θ') L
              (M * Work.Construction.s2 θ') hL
              (fun z'' hz'' => Work.Spaces.differentiableAt_curry_left
                (hPd z'' θ' (Work.FTS_StreamBdry.mem_Qd.mpr
                  ⟨lt_of_lt_of_le hL hz'', hθ'.1, hθ'.2⟩)))
              (fun z'' hz'' => by
                have h2 := hDz z'' θ' (Work.FTS_StreamBdry.mem_Qd.mpr
                  ⟨lt_of_lt_of_le hL hz'', hθ'.1, hθ'.2⟩) 1 (by norm_num)
                simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
                  Work.Spaces.pz] using h2)).1 h' hh' z' hz'
            simpa only [dilDiff] using h)
          (fun ε hε => uniform_decay_of_data
            (fun z' θ' hzθ' => ⟨
              Work.Spaces.differentiableAt_curry_right
                (((contDiffOn_dilDiff_three (h := h') hP3).contDiffAt
                  (hV.mem_nhds hzθ')).differentiableAt (by norm_num)),
              differentiableAt_pth_dilDiff (Work.FTS_StreamBdry.mem_Qd.mp hzθ').1
                ⟨(Work.FTS_StreamBdry.mem_Qd.mp hzθ').2.1,
                  (Work.FTS_StreamBdry.mem_Qd.mp hzθ').2.2⟩ hPd hPd2⟩)
            (fun z' θ' hzθ' => abs_pth_dilDiff_le hh' hK1 hPd hzθ')
            (fun z' θ' hzθ' => abs_pthIter2_dilDiff_le hh' hK2 hPd hPd2 hzθ')
            (fun z' hz' => tendsto_zero_endpoints_of_abs_le_s2
              (fun a b hab => abs_dilDiff_le_s2 hh'
                (fun w θ hw => hDz w θ hw 0 (by norm_num)) hab) hz')
            (fun θ' hθ' => tendsto_dilDiff_atTop hh'
              (hdec θ' ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩))
            ε hε)
          z θ hzθ hLz
      exact le_of_tendsto hconv.abs hbound
  -- ## j = 2
  have hj2 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      |Work.Spaces.DzIter 2 P z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
    intro z θ hzθ hLz
    obtain ⟨hz0, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
    rcases eq_or_lt_of_le hLz with hzL | hzLt
    · rw [hzL, div_self (ne_of_gt hz0), Real.one_rpow, mul_one]
      exact hDz z θ hzθ 2 (by norm_num)
    · have h1sm : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DzIter 1 P))
          Work.Construction.Qd := contDiffOn_DzIter_one (n := 2) hP3
      have h2sm : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter 2 P))
          Work.Construction.Qd := contDiffOn_DzIter_two (n := 1) hP3
      have hcont2 : ∀ θ' ∈ Ioo (0 : ℝ) (π / 2),
          ContinuousOn (fun z'' => Work.Spaces.DzIter 2 P z'' θ') (Ici L) :=
        fun θ' hθ' => continuousOn_slice_of_contDiffOn hL hθ' h2sm
      have hconv : Tendsto (fun h' : ℝ => dilDiff2 P h' z θ) (𝓝[>] (0 : ℝ))
          (𝓝 (Work.Spaces.DzIter 2 P z θ)) := by
        have hdq := Work.FTS_StreamBdry.SB25.dq2_facts (fun z' => P z' θ) L
          (M * Work.Construction.s2 θ) hL
          (fun z' hz' => by
            refine ⟨Work.Spaces.differentiableAt_curry_left
              (hPd z' θ (Work.FTS_StreamBdry.mem_Qd.mpr
                ⟨lt_of_lt_of_le hL hz', hθ1, hθ2⟩)), ?_⟩
            exact Work.Spaces.differentiableAt_curry_left
              ((h1sm.contDiffAt (hV.mem_nhds (Work.FTS_StreamBdry.mem_Qd.mpr
                ⟨lt_of_lt_of_le hL hz', hθ1, hθ2⟩))).differentiableAt (by norm_num)))
          (fun z' hz' => hcont2 θ ⟨hθ1, hθ2⟩ z' hz')
          (fun z' hz' => by
            have h := hDz z' θ (Work.FTS_StreamBdry.mem_Qd.mpr
              ⟨lt_of_lt_of_le hL hz', hθ1, hθ2⟩) 2 (by norm_num)
            simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
              Work.Spaces.pz] using h)
        simpa only [dilDiff2, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
          Work.Spaces.pz] using hdq.2 z hzLt
      have hbound : ∀ᶠ h' in 𝓝[>] (0 : ℝ),
          |dilDiff2 P h' z θ| ≤ M * Work.Construction.s2 θ * (L / z) ^ (4 / α) := by
        filter_upwards [self_mem_nhdsWithin] with h' hh'
        refine hcompare (dilDiff2 P h') M (contDiffOn_dilDiff2_three (h := h') hP3)
          (fun z' θ' hz' hθ' => bslOp_dilDiff2_eq_zero hL hP3 hbsl hF0 hh' hz' hθ')
          (fun z' θ' hz' hθ' => by
            have h := (Work.FTS_StreamBdry.SB25.dq2_facts (fun z'' => P z'' θ') L
              (M * Work.Construction.s2 θ') hL
              (fun z'' hz'' => by
                refine ⟨Work.Spaces.differentiableAt_curry_left
                  (hPd z'' θ' (Work.FTS_StreamBdry.mem_Qd.mpr
                    ⟨lt_of_lt_of_le hL hz'', hθ'.1, hθ'.2⟩)), ?_⟩
                exact Work.Spaces.differentiableAt_curry_left
                  ((h1sm.contDiffAt (hV.mem_nhds (Work.FTS_StreamBdry.mem_Qd.mpr
                    ⟨lt_of_lt_of_le hL hz'', hθ'.1, hθ'.2⟩))).differentiableAt (by norm_num)))
              (fun z'' hz'' => hcont2 θ' hθ' z'' hz'')
              (fun z'' hz'' => by
                have h2 := hDz z'' θ' (Work.FTS_StreamBdry.mem_Qd.mpr
                  ⟨lt_of_lt_of_le hL hz'', hθ'.1, hθ'.2⟩) 2 (by norm_num)
                simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
                  Work.Spaces.pz] using h2)).1 h' hh' z' hz'
            simpa only [dilDiff2] using h)
          (fun ε hε => uniform_decay_of_data
            (fun z' θ' hzθ' => ⟨
              Work.Spaces.differentiableAt_curry_right
                (((contDiffOn_dilDiff2_three (h := h') hP3).contDiffAt
                  (hV.mem_nhds hzθ')).differentiableAt (by norm_num)),
              differentiableAt_pth_dilDiff2 (Work.FTS_StreamBdry.mem_Qd.mp hzθ').1
                ⟨(Work.FTS_StreamBdry.mem_Qd.mp hzθ').2.1,
                  (Work.FTS_StreamBdry.mem_Qd.mp hzθ').2.2⟩ hPd hPd2⟩)
            (fun z' θ' hzθ' => abs_pth_dilDiff2_le hh' hK1 hPd hzθ')
            (fun z' θ' hzθ' => abs_pthIter2_dilDiff2_le hh' hK2 hPd hPd2 hzθ')
            (fun z' hz' => tendsto_zero_endpoints_of_abs_le_s2
              (fun a b hab => abs_dilDiff2_le_s2 hh'
                (fun w θ hw => hDz w θ hw 0 (by norm_num)) hab) hz')
            (fun θ' hθ' => tendsto_dilDiff2_atTop hh'
              (hdec θ' ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩))
            ε hε)
          z θ hzθ hLz
      exact le_of_tendsto hconv.abs hbound
  -- ## assembly
  intro z θ hzθ hLz j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact hj0 z θ hzθ hLz
  · exact hj1 z θ hzθ hLz
  · exact hj2 z θ hzθ hLz

/-! ## §10 The `θ`-bounds and the pointwise decay for `psiP` -/

/-- `|∂_θ psiP| ≤ 3M`: `∂_θP = V(Ψ) + tan θ·P` and `V` cannot see the gauge mode. -/
theorem abs_pth_psiP_le {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ| ≤ 3 * M := by
  intro z θ hzθ
  have hV := Work.FTS_StreamBdry.SB3.Vop_psiP_eq hαG h3 hslot z θ hzθ
  have hpth : Work.Spaces.pth (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
      = Work.Construction.Vop Ψ z θ
        + Real.tan θ * Work.FTS.StreamBdryIface.psiP αG Ψ z θ := by
    rw [Work.Construction.Vop] at hV
    linarith
  have h1 : |Work.Construction.Vop Ψ z θ| ≤ M :=
    Work.FTS_StreamBdry.SlotBd.V_le hslot hzθ (j := 0) (by norm_num)
  have h2 : |Real.tan θ * Work.FTS.StreamBdryIface.psiP αG Ψ z θ| ≤ 2 * M := by
    have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hzθ)
    have hs2 : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Qd hzθ
    have hkey : Real.tan θ * Work.FTS.StreamBdryIface.psiP αG Ψ z θ
        = (Real.tan θ * Work.Construction.s2 θ)
          * (Work.FTS.StreamBdryIface.psiP αG Ψ z θ / Work.Construction.s2 θ) := by
      field_simp
    have hsin : |2 * Real.sin θ ^ 2| ≤ 2 := by
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sin θ ^ 2)]
      nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
    have hdiv : |Work.FTS.StreamBdryIface.psiP αG Ψ z θ / Work.Construction.s2 θ| ≤ M := by
      rw [abs_div, abs_of_pos hs2, div_le_iff₀ hs2]
      exact Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot z θ hzθ 0 (by norm_num)
    rw [hkey, abs_mul, Work.FTS_StreamBdry.tan_mul_s2 hcos]
    exact mul_le_mul hsin hdiv (abs_nonneg _) (by norm_num)
  rw [hpth]
  calc |Work.Construction.Vop Ψ z θ
        + Real.tan θ * Work.FTS.StreamBdryIface.psiP αG Ψ z θ|
      ≤ |Work.Construction.Vop Ψ z θ|
        + |Real.tan θ * Work.FTS.StreamBdryIface.psiP αG Ψ z θ| := abs_add_le _ _
    _ ≤ M + 2 * M := add_le_add h1 h2
    _ ≤ 3 * M := by linarith

/-- The `U`-slot part of a solution decays pointwise in `z` at every fixed `θ`. -/
theorem tendsto_psiP_atTop {αG M : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Tendsto (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z θ) atTop (𝓝 0) := by
  intro θ hθ
  by_cases hθ0 : θ = 0
  · subst hθ0
    have hone : (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z 0) = fun _ => (0 : ℝ) := by
      funext z
      rw [Work.FTS_StreamBdry.psiP_eq_Iint, s2_zero]
      ring
    rw [hone]
    exact tendsto_const_nhds
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
    by_cases hθπ : θ = π / 2
    · subst hθπ
      have hone : (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z (π / 2)) = fun _ => (0 : ℝ) := by
        funext z
        rw [Work.FTS_StreamBdry.psiP_eq_Iint, s2_pi_div_two]
        ring
      rw [hone]
      exact tendsto_const_nhds
    · have hθlt : θ < π / 2 := lt_of_le_of_ne hθ.2 hθπ
      obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M) hαG h3
        hslot (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
        (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
        (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
      have heq : (fun z => Work.FTS.StreamBdryIface.psiP αG Ψ z θ)
          =ᶠ[atTop] (fun z => Ψ z θ
            - κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        have h := hκ z θ (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz, hθpos, hθlt⟩)
        linarith
      have h1 : Tendsto (fun z => Ψ z θ) atTop (𝓝 0) := hsol.2.2.2 θ ⟨hθ.1, hθ.2⟩
      have h2 : Tendsto (fun z => κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) atTop
          (𝓝 0) := by
        have hg : Tendsto (fun z : ℝ => z ^ (-(3 / αG))) atTop (𝓝 0) :=
          tendsto_rpow_neg_atTop (by positivity)
        have h3' := hg.const_mul (κ / Real.cos θ)
        simpa only [Work.FTS.StreamBdryIface.gaugeMode, div_eq_mul_inv, mul_comm, mul_left_comm,
          mul_assoc, zero_mul, mul_zero] using h3'
      have h0 : Tendsto (fun z => Ψ z θ
          - κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) atTop (𝓝 (0 - 0)) := h1.sub h2
      refine Tendsto.congr' heq.symm ?_
      simpa using h0


end

end Work.FTS_StreamBdry.SB5
