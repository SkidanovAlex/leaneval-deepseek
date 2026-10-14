import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound2
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.FTS_StreamBdry.SB6.uprime_le
import Submission.Work.FTS_StreamBdry.SBpsiP.DzJ_crux
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.sb2_dthDV_proved
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.psiP_edge_axis =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.psiP_edge_axis` — leaf B6 of the SB2/SB5 plan

The edge limits of `P := psiP αG Ψ` at `θ = π/2`: with `V := Vop`, `D := Dz`,

* `P`, `∂_zP`, `∂_z²P`, `∂_θ²P → 0` as `(z,θ) → (z₀, π/2)` inside the open quadrant;
* `∂_θP` and the mixed second partials have limits;

all uniformly in `z` near a fixed `z₀ > 0`.

The two edge traces used by the argument are produced separately:

* `SB25Aux3.trace_Vop_psiP` — the trace `Vb` of `V(P)` at `θ = π/2`, at rate
  `K_V = (αG²+5αG+6)M + Mf` (`lip_edge_trace` applied to `V(P)`, whose `θ`-derivative is bounded
  by the law `law_psiP`);
* `SB25Aux3.trace_DzVop_psiP` — the trace `DVb` of `D_z(V(P))` at `θ = π/2`, at rate `|K'|`
  (the `K'` supplied by the statement; `SB2.sb2_dthDV` is what produces it downstream).

The assembly is `SB25Aux4.psiP_edge_axis_aux`, whose parts are
`SB25Aux4.psiP_edge_axis_zero123` (the three vanishing `z`-derivative limits),
`SB25Aux4.psiP_edge_axis_pthth` (`∂_θ²P → 0`), `SB25Aux4.psiP_edge_axis_pth` (the limit of
`∂_θP`) and `SB25Aux4.psiP_edge_axis_mixed` (the mixed second partials).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP)

set_option autoImplicit false

theorem psiP_edge_axis {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ} :
    Work.FTS_StreamBdry.SB25.PsiPEdgeAxis αG M L Mf F Ψ := by
  intro hsol h3 hslot hsrc hK'
  obtain ⟨K', hK'b⟩ := hK'
  obtain ⟨Vb, hVbc, hVb⟩ :=
    Work.FTS_StreamBdry.SB25Aux3.trace_Vop_psiP (αG := αG) (M := M) (L := L) (Mf := Mf)
      hαG hsol h3 hslot hsrc
  obtain ⟨DVb, hDVbc, hDVb⟩ :=
    Work.FTS_StreamBdry.SB25Aux3.trace_DzVop_psiP (αG := αG) (M := M) hαG h3 hslot hK'b
  exact Work.FTS_StreamBdry.SB25Aux4.psiP_edge_axis_aux (αG := αG) (M := M) (L := L)
    (Mf := Mf) (K' := K') hαG hsol h3 hslot hsrc hK'b Vb hVbc hVb DVb hDVbc hDVb

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB5.Ang =====
section

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
end
end Work.FTS_StreamBdry.SB5
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.Vop_far =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.Vop_far` — decay of the `V`-slot in the far field

`V(P) = ∂_θP - tan θ·P` does *not* satisfy `bslOp V(P) = 0`, so its decay cannot be obtained from
the maximum principle directly.  Instead: the law in `D`-form gives
`∂_θV(P) = -(α²D_z²P + 5αD_zP + 6P) - F`, which decays like `z^{-4/αG}` above `L`
(`Vop_deriv_le`).  Since also `(P cos θ)' = cos θ·V(P)`, the value of `V(P)` at `θ = π/4` is pinned
down to `O(z^{-4/αG})` by integrating against `cos` up to `θ = π/2`, where `P(z,π/2)cos(π/2) = 0`
gives a vanishing boundary term; the `θ`-Lipschitz bound on `V(P)` (also from the law) then
propagates this to every `θ ∈ (0,π/2)`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

theorem psiP_Vop_far {αG M L Mf Kf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hKf : 0 ≤ Kf)
    (hfar : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ Kf * Work.Construction.s2 θ * (L / z) ^ (4 / αG)) :
    ∃ K : ℝ, 0 < K ∧ ∀ z θ, (z, θ) ∈ Work.Construction.Qd → L ≤ z →
      |Work.Construction.Vop (psiP αG Ψ) z θ| ≤ K * (L / z) ^ (4 / αG) := by
  have hL : 0 < L := hF.2.2.2.2.1
  have hM : 0 ≤ M := M_nonneg hslot
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hPth1 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (psiP αG Ψ)))
      Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.contDiffOn_uncurry_pth_qd hP2
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hsm : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
  have hδ : 0 < 1 - Real.sin (Real.pi / 4) := by
    rw [hsm]
    have h2 : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]; norm_num
    linarith
  set Cflow : ℝ := (αG ^ 2 + 5 * |αG| + 6) * Kf with hCflow
  have hCnonneg : 0 ≤ αG ^ 2 + 5 * |αG| + 6 := by positivity
  have hCflow0 : 0 ≤ Cflow := by
    rw [hCflow]; exact mul_nonneg hCnonneg hKf
  -- the pinning-down constant at `π/4` and the final constant
  set K₀ : ℝ := (Cflow * (Real.pi / 2) ^ 2 + Kf * Real.cos (Real.pi / 4))
      / (1 - Real.sin (Real.pi / 4)) + Cflow * (Real.pi / 2) + 1 with hK0
  have hcm0 : 0 ≤ Real.cos (Real.pi / 4) :=
    le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have hnum0 : 0 ≤ Cflow * (Real.pi / 2) ^ 2 + Kf * Real.cos (Real.pi / 4) := by
    have h1 : 0 ≤ Cflow * (Real.pi / 2) ^ 2 := by positivity
    have h2 : 0 ≤ Kf * Real.cos (Real.pi / 4) := mul_nonneg hKf hcm0
    linarith
  have hK0pos : 0 < K₀ := by
    rw [hK0]
    have h1 : 0 ≤ (Cflow * (Real.pi / 2) ^ 2 + Kf * Real.cos (Real.pi / 4))
        / (1 - Real.sin (Real.pi / 4)) := div_nonneg hnum0 (le_of_lt hδ)
    have h2 : 0 ≤ Cflow * (Real.pi / 2) := by positivity
    linarith
  refine ⟨K₀, hK0pos, ?_⟩
  intro z θ hmem hzL
  have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hmem
  set r : ℝ := (L / z) ^ (4 / αG) with hr
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact Real.rpow_nonneg (div_nonneg (le_of_lt hL) (le_of_lt hzpos)) _
  set g : ℝ → ℝ := fun t => Work.Spaces.pth (psiP αG Ψ) z t
    - Real.tan t * psiP αG Ψ z t with hg
  have hgVop : ∀ t : ℝ, g t = Work.Construction.Vop (psiP αG Ψ) z t := by
    intro t; rw [hg]; rfl
  have hVopg : ∀ t : ℝ, Work.Construction.Vop (psiP αG Ψ) z t = g t := fun t => (hgVop t).symm
  -- differentiability of the `θ`-slice of `V(psiP)`
  have hgdiff : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ g t := by
    intro t ht
    have hmemt : (z, t) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, ht.1, ht.2⟩
    have h1 : DifferentiableAt ℝ (fun s => Work.Spaces.pth (psiP αG Ψ) z s) t :=
      Work.Spaces.differentiableAt_curry_right
        ((hPth1.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmemt))
    have hPz : DifferentiableAt ℝ (fun s => psiP αG Ψ z s) t :=
      Work.Spaces.differentiableAt_curry_right
        ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmemt))
    have hcost : Real.cos t ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩)
    have h2 : DifferentiableAt ℝ (fun s => Real.tan s * psiP αG Ψ z s) t :=
      (Real.differentiableAt_tan.mpr hcost).mul hPz
    have h3 : DifferentiableAt ℝ (fun s => Work.Spaces.pth (psiP αG Ψ) z s
        - Real.tan s * psiP αG Ψ z s) t := h1.sub h2
    rw [hg]
    exact h3
  -- the derivative bound on the slice (transported from `Vop_deriv_le`)
  have hD : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv g t| ≤ Cflow * r * Work.Construction.s2 t := by
    intro t ht
    have hmemt : (z, t) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, ht.1, ht.2⟩
    have hV := Vop_deriv_le hαG hsol h3 hslot hF hKf hfar z t hmemt hzL
    have heq : deriv g t = deriv (fun s => Work.Construction.Vop (psiP αG Ψ) z s) t := by
      rw [hg]; rfl
    rw [heq, hCflow, hr]
    exact hV
  -- the `θ`-Lipschitz bound on the slice
  have hglip : ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ → θ₂ < Real.pi / 2 →
      |g θ₂ - g θ₁| ≤ Cflow * r * (θ₂ - θ₁) := by
    intro θ₁ θ₂ h1 h2 h3
    have hs : Set.Icc θ₁ θ₂ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun x hx => ⟨lt_of_lt_of_le h1 hx.1, lt_of_le_of_lt hx.2 h3⟩
    have hdiff : ∀ x ∈ Set.Icc θ₁ θ₂, DifferentiableAt ℝ g x := fun x hx => hgdiff x (hs hx)
    have hb : ∀ x ∈ Set.Icc θ₁ θ₂, ‖deriv g x‖ ≤ Cflow * r := by
      intro x hx
      rw [Real.norm_eq_abs]
      have hs2le : Work.Construction.s2 x ≤ 1 := by
        rw [Work.Construction.s2_eq]; exact Real.sin_le_one _
      calc |deriv g x| ≤ Cflow * r * Work.Construction.s2 x := hD x (hs hx)
        _ ≤ Cflow * r * 1 := mul_le_mul_of_nonneg_left hs2le (mul_nonneg hCflow0 hr0)
        _ = Cflow * r := by ring
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := Set.Icc θ₁ θ₂)
      hdiff hb (convex_Icc θ₁ θ₂) ⟨le_rfl, h2⟩ ⟨h2, le_rfl⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ₂ - θ₁)] at hmvt
    exact hmvt
  -- the derivative of `Φ t = psiP(z,t) cos t - g(π/4) sin t`
  have hPhiDiff : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => psiP αG Ψ z t * Real.cos t - g (Real.pi / 4) * Real.sin t)
        (Real.cos x * (g x - g (Real.pi / 4))) x := by
    intro x hx
    have hmemx : (z, x) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, hx.1, hx.2⟩
    have hcost : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩)
    have hPz : HasDerivAt (fun t : ℝ => psiP αG Ψ z t) (Work.Spaces.pth (psiP αG Ψ) z x) x := by
      simpa only [Work.Spaces.pth] using (Work.Spaces.differentiableAt_curry_right
        ((hP2.differentiableOn (by norm_num)).differentiableAt (hQd.mem_nhds hmemx))).hasDerivAt
    have hmul : HasDerivAt (fun t : ℝ => psiP αG Ψ z t * Real.cos t)
        (Work.Spaces.pth (psiP αG Ψ) z x * Real.cos x
          + psiP αG Ψ z x * (-Real.sin x)) x := hPz.mul (Real.hasDerivAt_cos x)
    have hsin : HasDerivAt (fun t : ℝ => g (Real.pi / 4) * Real.sin t)
        (g (Real.pi / 4) * Real.cos x) x :=
      (Real.hasDerivAt_sin x).const_mul (g (Real.pi / 4))
    have htot : HasDerivAt
        (fun t : ℝ => psiP αG Ψ z t * Real.cos t - g (Real.pi / 4) * Real.sin t)
        (Work.Spaces.pth (psiP αG Ψ) z x * Real.cos x + psiP αG Ψ z x * (-Real.sin x)
          - g (Real.pi / 4) * Real.cos x) x := hmul.sub hsin
    refine htot.congr_deriv ?_
    have hgx : g x = Work.Spaces.pth (psiP αG Ψ) z x - Real.tan x * psiP αG Ψ z x := by
      rw [hg]
    rw [hgx, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  -- the mean value bound on `Φ` over `[π/4, θ']`
  have hMVT : ∀ θ' : ℝ, Real.pi / 4 < θ' → θ' < Real.pi / 2 →
      |psiP αG Ψ z θ' * Real.cos θ' - g (Real.pi / 4) * Real.sin θ'
        - (psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)
            - g (Real.pi / 4) * Real.sin (Real.pi / 4))| ≤ Cflow * r * (Real.pi / 2) ^ 2 := by
    intro θ' h1 h2
    have hs : Set.Icc (Real.pi / 4) θ' ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun x hx => ⟨by linarith [Real.pi_pos, hx.1], lt_of_le_of_lt hx.2 h2⟩
    have hfdiff : ∀ x ∈ Set.Icc (Real.pi / 4) θ',
        DifferentiableAt ℝ (fun t : ℝ => psiP αG Ψ z t * Real.cos t
          - g (Real.pi / 4) * Real.sin t) x :=
      fun x hx => (hPhiDiff x (hs hx)).differentiableAt
    have hfb : ∀ x ∈ Set.Icc (Real.pi / 4) θ',
        ‖deriv (fun t : ℝ => psiP αG Ψ z t * Real.cos t
          - g (Real.pi / 4) * Real.sin t) x‖ ≤ Cflow * r * (Real.pi / 2) := by
      intro x hx
      rw [Real.norm_eq_abs, (hPhiDiff x (hs hx)).deriv]
      have hgl := hglip (Real.pi / 4) x (by linarith [Real.pi_pos]) hx.1 (hs hx).2
      have hdiff : |g x - g (Real.pi / 4)| ≤ Cflow * r * (Real.pi / 2) := by
        refine hgl.trans ?_
        exact mul_le_mul_of_nonneg_left (by linarith [(hs hx).2]) (mul_nonneg hCflow0 hr0)
      rw [abs_mul]
      calc |Real.cos x| * |g x - g (Real.pi / 4)|
          ≤ 1 * (Cflow * r * (Real.pi / 2)) :=
            mul_le_mul (Real.abs_cos_le_one x) hdiff (abs_nonneg _) (by norm_num)
        _ = Cflow * r * (Real.pi / 2) := by ring
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun t : ℝ => psiP αG Ψ z t * Real.cos t - g (Real.pi / 4) * Real.sin t)
      (s := Set.Icc (Real.pi / 4) θ') hfdiff hfb (convex_Icc (Real.pi / 4) θ')
      ⟨le_rfl, le_of_lt h1⟩ ⟨le_of_lt h1, le_rfl⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ θ' - Real.pi / 4)] at hmvt
    refine hmvt.trans ?_
    calc Cflow * r * (Real.pi / 2) * (θ' - Real.pi / 4)
        ≤ Cflow * r * (Real.pi / 2) * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_left (by linarith [h2]) (by positivity)
      _ = Cflow * r * (Real.pi / 2) ^ 2 := by ring
  -- the limit of `Φ` at `π/2`
  have hPlim : Filter.Tendsto (fun t => psiP αG Ψ z t * Real.cos t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hb : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        |psiP αG Ψ z t| ≤ M * Work.Construction.s2 t :=
      fun t ht => Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot z t
        (Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, ht.1, ht.2⟩) 0 (by norm_num)
    have hP0 : Filter.Tendsto (fun t => psiP αG Ψ z t)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      tendsto_zero_of_abs_le_s2_right hM hb
    have h2 : Filter.Tendsto (fun t => |psiP αG Ψ z t * Real.cos t|)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall (fun t => abs_nonneg _)) ?_ (by simpa using hP0.abs)
      filter_upwards with t
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one t)
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using h2)
  have hSinlim : Filter.Tendsto (fun t : ℝ => Real.sin t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 1) := by
    have hle : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) ≤ nhds (Real.pi / 2) :=
      nhdsWithin_le_nhds
    have h := (Real.continuous_sin.tendsto (Real.pi / 2)).mono_left hle
    have h1 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    simpa only [h1] using h
  have hPhilim : Filter.Tendsto
      (fun t => psiP αG Ψ z t * Real.cos t - g (Real.pi / 4) * Real.sin t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (0 - g (Real.pi / 4) * 1)) :=
    hPlim.sub (hSinlim.const_mul _)
  have hev : ∀ᶠ t in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
      |psiP αG Ψ z t * Real.cos t - g (Real.pi / 4) * Real.sin t
        - (psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)
            - g (Real.pi / 4) * Real.sin (Real.pi / 4))| ≤ Cflow * r * (Real.pi / 2) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2))]
      with t ht1 ht2
    exact hMVT t ht2 ht1
  have hpin : |-(g (Real.pi / 4)) - (psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)
      - g (Real.pi / 4) * Real.sin (Real.pi / 4))| ≤ Cflow * r * (Real.pi / 2) ^ 2 := by
    have hsub : Filter.Tendsto
        (fun t => (psiP αG Ψ z t * Real.cos t - g (Real.pi / 4) * Real.sin t)
          - (psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)
              - g (Real.pi / 4) * Real.sin (Real.pi / 4)))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds ((0 - g (Real.pi / 4) * 1) - (psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)
          - g (Real.pi / 4) * Real.sin (Real.pi / 4)))) :=
      hPhilim.sub tendsto_const_nhds
    have h := le_of_tendsto hsub.abs hev
    have hlim : (0 - g (Real.pi / 4) * 1) = -(g (Real.pi / 4)) := by ring
    rwa [hlim] at h
  -- rewrite the pin in the convenient form
  have hpin' : |g (Real.pi / 4) * (1 - Real.sin (Real.pi / 4))
      + psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)| ≤ Cflow * r * (Real.pi / 2) ^ 2 := by
    have heq : -(g (Real.pi / 4)) - (psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)
        - g (Real.pi / 4) * Real.sin (Real.pi / 4))
        = -(g (Real.pi / 4) * (1 - Real.sin (Real.pi / 4))
            + psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)) := by ring
    rw [heq, abs_neg] at hpin
    exact hpin
  -- the bound on `|psiP(z,π/4)|`
  have hP4 : |psiP αG Ψ z (Real.pi / 4)| * Real.cos (Real.pi / 4)
      ≤ Kf * r * Real.cos (Real.pi / 4) := by
    have h4 : (z, Real.pi / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, by linarith [Real.pi_pos],
        by linarith [Real.pi_pos]⟩
    have h := hfar z (Real.pi / 4) h4 hzL 0 (by norm_num)
    have hs2 : Work.Construction.s2 (Real.pi / 4) = 1 := by
      rw [Work.Construction.s2_eq,
        show 2 * (Real.pi / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
    rw [hs2, mul_one] at h
    have hcpos : 0 < Real.cos (Real.pi / 4) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    calc |psiP αG Ψ z (Real.pi / 4)| * Real.cos (Real.pi / 4)
        ≤ (Kf * r) * Real.cos (Real.pi / 4) :=
          mul_le_mul_of_nonneg_right h (le_of_lt hcpos)
      _ = Kf * r * Real.cos (Real.pi / 4) := by ring
  have hP4' : |psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)|
      ≤ Kf * r * Real.cos (Real.pi / 4) := by
    rw [abs_mul, abs_of_nonneg (le_of_lt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩))]
    exact hP4
  -- the pinned value of `|g(π/4)|`
  have ha : |g (Real.pi / 4)| ≤ ((Cflow * (Real.pi / 2) ^ 2 + Kf * Real.cos (Real.pi / 4))
      / (1 - Real.sin (Real.pi / 4))) * r := by
    have h1 : |g (Real.pi / 4) * (1 - Real.sin (Real.pi / 4))| ≤ Cflow * r * (Real.pi / 2) ^ 2
        + Kf * r * Real.cos (Real.pi / 4) := by
      have heq : g (Real.pi / 4) * (1 - Real.sin (Real.pi / 4))
          = (g (Real.pi / 4) * (1 - Real.sin (Real.pi / 4))
              + psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4))
            - psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4) := by ring
      calc |g (Real.pi / 4) * (1 - Real.sin (Real.pi / 4))|
          = |(g (Real.pi / 4) * (1 - Real.sin (Real.pi / 4))
              + psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4))
            - psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)| := congrArg abs heq
        _ ≤ |g (Real.pi / 4) * (1 - Real.sin (Real.pi / 4))
              + psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)|
            + |psiP αG Ψ z (Real.pi / 4) * Real.cos (Real.pi / 4)| := abs_sub _ _
        _ ≤ Cflow * r * (Real.pi / 2) ^ 2 + Kf * r * Real.cos (Real.pi / 4) :=
            add_le_add hpin' hP4'
    rw [abs_mul, abs_of_nonneg (le_of_lt hδ)] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    have hsum : Cflow * r * (Real.pi / 2) ^ 2 + Kf * r * Real.cos (Real.pi / 4)
        = (Cflow * (Real.pi / 2) ^ 2 + Kf * Real.cos (Real.pi / 4)) * r := by ring
    linarith [h1, hsum]
  -- propagate to every `θ ∈ (0,π/2)`
  have hmem4 : (z, Real.pi / 4) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨hzpos, by linarith [Real.pi_pos],
      by linarith [Real.pi_pos]⟩
  have hgap : ∀ θ₁ θ₂ : ℝ, θ₁ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      θ₂ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → |g θ₁ - g θ₂| ≤ Cflow * r * (Real.pi / 2) := by
    intro θ₁ θ₂ h1 h2
    rcases le_total θ₁ θ₂ with hle | hle
    · rw [abs_sub_comm]
      refine (hglip θ₁ θ₂ h1.1 hle h2.2).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith [h1.1, h2.2]) (mul_nonneg hCflow0 hr0)
    · refine (hglip θ₂ θ₁ h2.1 hle h1.2).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith [h2.1, h1.2]) (mul_nonneg hCflow0 hr0)
  have hfinal : |g θ| ≤ K₀ * r := by
    have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      Work.FTS_StreamBdry.Qd_theta_mem hmem
    have h4mem : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hsplit : |g θ| = |(g θ - g (Real.pi / 4)) + g (Real.pi / 4)| := by
      rw [sub_add_cancel]
    rw [hsplit]
    calc |(g θ - g (Real.pi / 4)) + g (Real.pi / 4)|
        ≤ |g θ - g (Real.pi / 4)| + |g (Real.pi / 4)| := abs_add_le _ _
      _ ≤ Cflow * r * (Real.pi / 2)
            + ((Cflow * (Real.pi / 2) ^ 2 + Kf * Real.cos (Real.pi / 4))
                / (1 - Real.sin (Real.pi / 4))) * r :=
          add_le_add (hgap θ (Real.pi / 4) hθmem h4mem) ha
      _ ≤ K₀ * r := by
          rw [hK0]
          have h1 : 0 ≤ (Cflow * (Real.pi / 2) ^ 2 + Kf * Real.cos (Real.pi / 4))
              / (1 - Real.sin (Real.pi / 4)) := div_nonneg hnum0 (le_of_lt hδ)
          have h2 : 0 ≤ Cflow * (Real.pi / 2) := by positivity
          have h3 : 0 ≤ Cflow * (Real.pi / 2) * r := mul_nonneg h2 hr0
          nlinarith [hr0, h1, h2, h3]
  rw [hVopg θ]
  exact hfinal

end Work.FTS_StreamBdry.SB6
end
end
