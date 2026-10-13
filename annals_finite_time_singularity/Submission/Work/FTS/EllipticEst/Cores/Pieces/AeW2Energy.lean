import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemUD
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD
import Submission.Work.FTS.EllipticEst.H2W.AeW.aeTruncWHon
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeCutErr
import Submission.Work.FTS.EllipticEst.weight_algebra_fts
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeGapSlices
import Submission.Work.FTS.EllipticEst.H2W.AeLeftClean
import Submission.Work.FTS.EllipticEst.H2W.Ae.AeSliceRightTendsto
import Submission.Work.FTS.EllipticEst.AngAWeak.aeEnergyWAux
import Submission.Work.FTS.EllipticEst.Dispatch.aeLeftLimitD
import Submission.Work.FTS.EllipticEst.Honest.HR2.Defs
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyTruncIneq2
import Submission.Work.FTS.EllipticEst.AngAWeak.AeEnergyMain
import Submission.Work.FTS.EllipticEst.Cores.Pieces.AeW2SliceBundle

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Pieces

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# `AeW2Energy` — the plain-`w²` angular energy of the a.e. class

The estimate `∫_z ∫_θ (∂_θu)² w(z)² ≤ C (|G|²_{ℋ⁰} + α² |D_z u|²_{ℋ⁰})` for a datum
`AeData α u G` of the almost-everywhere class of the level-`0` elliptic estimate of
T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
Euler equations on `ℝ³`*, Annals of Math. **194** (2021) (Step 1 of Proposition `prop:H2`).

The proof runs the proved truncated radial energy *identity*
`Work.FTS.EllipticEst.H2W.AeW.aeTruncWHon` for the cut-off family `cut n` and then passes to
the limit `n → ∞`.
-/

/-! ## Elementary radial weight facts on a compact sub-interval of `(0,∞)` -/

/-- On `[δ,R] ⊆ (0,∞)` each of the three derived radial weights is dominated by `C·w²`, and so
are `z²w²` and `zw²` (`w² ≥ 1` on the half-line, and the five quotients are continuous on the
compact interval). -/
theorem exists_weight_bound {δ R : ℝ} (hδ : 0 < δ) (hδR : δ ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Icc δ R,
      |deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z| ≤ C * (Work.Spaces.w z) ^ 2 ∧
      |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z| ≤ C * (Work.Spaces.w z) ^ 2 ∧
      |deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z|
        ≤ C * (Work.Spaces.w z) ^ 2 ∧
      z ^ 2 * (Work.Spaces.w z) ^ 2 ≤ C * (Work.Spaces.w z) ^ 2 ∧
      z * (Work.Spaces.w z) ^ 2 ≤ C * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨hsq2, hsq1, hd2, hd1, hdd2, -, -, -, -, -, -⟩ := weight_algebra_fts
  have hne : ∀ z ∈ Set.Icc δ R, z ≠ 0 := fun z hz =>
    ne_of_gt (lt_of_lt_of_le hδ hz.1)
  have hcont1 : ContinuousOn (fun z : ℝ => 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3) (Set.Icc δ R) := by
    refine ContinuousOn.div ?_ (by fun_prop) (fun z hz => pow_ne_zero 3 (hne z hz))
    fun_prop
  have hcont2 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4)
      (Set.Icc δ R) := by
    refine ContinuousOn.div ?_ (by fun_prop) (fun z hz => pow_ne_zero 4 (hne z hz))
    fun_prop
  have hcont3 : ContinuousOn (fun z : ℝ => (z - 3) * (1 + z) ^ 3 / z ^ 4) (Set.Icc δ R) := by
    refine ContinuousOn.div ?_ (by fun_prop) (fun z hz => pow_ne_zero 4 (hne z hz))
    fun_prop
  have hcont4 : ContinuousOn (fun z : ℝ => (1 + z) ^ 4 / z ^ 2) (Set.Icc δ R) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) (fun z hz => pow_ne_zero 2 (hne z hz))
  have hcont5 : ContinuousOn (fun z : ℝ => (1 + z) ^ 4 / z ^ 3) (Set.Icc δ R) :=
    ContinuousOn.div (by fun_prop) (by fun_prop) (fun z hz => pow_ne_zero 3 (hne z hz))
  obtain ⟨C1, hC1⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont1
  obtain ⟨C2, hC2⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont2
  obtain ⟨C3, hC3⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont3
  obtain ⟨C4, hC4⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont4
  obtain ⟨C5, hC5⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcont5
  refine ⟨|C1| + |C2| + |C3| + |C4| + |C5| + 1, by positivity, fun z hz => ?_⟩
  have hz0 : (0:ℝ) < z := lt_of_lt_of_le hδ hz.1
  have hw1 : 1 ≤ (Work.Spaces.w z) ^ 2 := by
    have h := Work.FTS.EllipticEst.Dispatch.one_le_w_D (lt_of_lt_of_le hδ hz.1)
    nlinarith
  have hCnn : (0:ℝ) ≤ |C1| + |C2| + |C3| + |C4| + |C5| + 1 := by positivity
  have key : ∀ {F : ℝ → ℝ} {C0 : ℝ}, (∀ z ∈ Set.Icc δ R, |F z| ≤ C0) →
      C0 ≤ |C1| + |C2| + |C3| + |C4| + |C5| + 1 →
      |F z| ≤ (|C1| + |C2| + |C3| + |C4| + |C5| + 1) * (Work.Spaces.w z) ^ 2 := by
    intro F C0 hF hle
    calc |F z| ≤ C0 := hF z hz
      _ ≤ |C1| + |C2| + |C3| + |C4| + |C5| + 1 := hle
      _ = (|C1| + |C2| + |C3| + |C4| + |C5| + 1) * 1 := by ring
      _ ≤ (|C1| + |C2| + |C3| + |C4| + |C5| + 1) * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_left hw1 hCnn
  have keynn : ∀ {F : ℝ → ℝ} {C0 : ℝ}, 0 ≤ F z → (∀ z ∈ Set.Icc δ R, |F z| ≤ C0) →
      C0 ≤ |C1| + |C2| + |C3| + |C4| + |C5| + 1 →
      F z ≤ (|C1| + |C2| + |C3| + |C4| + |C5| + 1) * (Work.Spaces.w z) ^ 2 := by
    intro F C0 hFnn hF hle
    rw [← abs_of_nonneg hFnn]
    exact key hF hle
  have hb : ∀ {F : ℝ → ℝ} {D : ℝ}, (∀ y ∈ Set.Icc δ R, ‖F y‖ ≤ D) →
      ∀ y ∈ Set.Icc δ R, |F y| ≤ |D| := by
    intro F D hD y hy
    have h1 := hD y hy
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self D]
  have h1 : |deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z|
      ≤ (|C1| + |C2| + |C3| + |C4| + |C5| + 1) * (Work.Spaces.w z) ^ 2 := by
    rw [hd1 z (hne z hz)]
    exact key (F := fun y : ℝ => (y - 3) * (1 + y) ^ 3 / y ^ 4) (C0 := |C3|)
      (hb hC3) (by linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C4, abs_nonneg C5])
  have h2 : |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
      ≤ (|C1| + |C2| + |C3| + |C4| + |C5| + 1) * (Work.Spaces.w z) ^ 2 := by
    rw [hd2 z (hne z hz)]
    exact key (F := fun y : ℝ => 2 * (y - 1) * (1 + y) ^ 3 / y ^ 3) (C0 := |C1|)
      (hb hC1) (by linarith [abs_nonneg C2, abs_nonneg C3, abs_nonneg C4, abs_nonneg C5])
  have h3 : |deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z|
      ≤ (|C1| + |C2| + |C3| + |C4| + |C5| + 1) * (Work.Spaces.w z) ^ 2 := by
    rw [hdd2 z (hne z hz)]
    exact key (F := fun y : ℝ => (1 + y) ^ 2 * (2 * y ^ 2 - 4 * y + 6) / y ^ 4) (C0 := |C2|)
      (hb hC2) (by linarith [abs_nonneg C1, abs_nonneg C3, abs_nonneg C4, abs_nonneg C5])
  have h4 : z ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (|C1| + |C2| + |C3| + |C4| + |C5| + 1) * (Work.Spaces.w z) ^ 2 := by
    rw [hsq2 z (hne z hz)]
    have hnn : (0:ℝ) ≤ (1 + z) ^ 4 / z ^ 2 := div_nonneg (by positivity) (sq_nonneg z)
    exact keynn (F := fun y : ℝ => (1 + y) ^ 4 / y ^ 2) (C0 := |C4|) hnn
      (hb hC4) (by linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C5])
  have h5 : z * (Work.Spaces.w z) ^ 2
      ≤ (|C1| + |C2| + |C3| + |C4| + |C5| + 1) * (Work.Spaces.w z) ^ 2 := by
    rw [hsq1 z (hne z hz)]
    have hnn : (0:ℝ) ≤ (1 + z) ^ 4 / z ^ 3 :=
      div_nonneg (by positivity) (pow_nonneg (le_of_lt hz0) 3)
    exact keynn (F := fun y : ℝ => (1 + y) ^ 4 / y ^ 3) (C0 := |C5|) hnn
      (hb hC5) (by linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4])
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ## The domination of the truncation error integrands on the support of the cut-off -/

/-- If `χ` is `C²`, compactly supported and vanishes near `0`, then the two error integrands of
the truncated energy identity are dominated by `C·w²`. -/
theorem exists_cut_bound {χ : ℝ → ℝ} (hχsm : ContDiff ℝ 2 χ) (hcpt : HasCompactSupport χ)
    (hχ0 : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → χ z = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ,
      (2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
        + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) ≤ C * (Work.Spaces.w z) ^ 2 ∧
      |deriv χ z| * (z * (Work.Spaces.w z) ^ 2) ≤ C * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨δ, hδpos, hχδ⟩ := hχ0
  obtain ⟨R0, hR0⟩ := hcpt.isCompact.isBounded.exists_norm_le
  set R : ℝ := max R0 δ + 1 with hRdef
  have hRpos : 0 < R := by
    have : (0:ℝ) ≤ max R0 δ := le_trans (le_of_lt hδpos) (le_max_right _ _)
    rw [hRdef]; linarith
  have hRge : R0 ≤ R := by
    have : R0 ≤ max R0 δ := le_max_left _ _
    rw [hRdef]; linarith
  have hδR : δ ≤ R := by
    have : δ ≤ max R0 δ := le_max_right _ _
    rw [hRdef]; linarith
  obtain ⟨Cw, hCwpos, hCw⟩ := exists_weight_bound hδpos hδR
  have hc1 : ContinuousOn (deriv χ) (Set.Icc δ R) :=
    ((hχsm.contDiffOn.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).continuousOn).mono
      (fun z hz => lt_of_lt_of_le hδpos hz.1)
  have hc2 : ContinuousOn (deriv (deriv χ)) (Set.Icc δ R) :=
    (((hχsm.contDiffOn.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).deriv_of_isOpen
      isOpen_Ioi (m := 0) (by norm_num)).continuousOn).mono
      (fun z hz => lt_of_lt_of_le hδpos hz.1)
  obtain ⟨K1, hK1⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨K2, hK2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  refine ⟨2 * |K1| * Cw + |K2| * Cw + |K1| * Cw + 1, by positivity, fun z => ?_⟩
  have hCpos : (0:ℝ) < 2 * |K1| * Cw + |K2| * Cw + |K1| * Cw + 1 := by positivity
  have hWnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hK1nn : (0:ℝ) ≤ |K1| := abs_nonneg K1
  have hK2nn : (0:ℝ) ≤ |K2| := abs_nonneg K2
  by_cases hzI : z ∈ Set.Icc δ R
  · have hzpos : 0 < z := lt_of_lt_of_le hδpos hzI.1
    obtain ⟨hzg1, hzg2, hzg3, hzg4, hzg5⟩ := hCw z hzI
    have hK1z : |deriv χ z| ≤ |K1| := by
      have h := hK1 z hzI; rw [Real.norm_eq_abs] at h; linarith [le_abs_self K1]
    have hK2z : |deriv (deriv χ) z| ≤ |K2| := by
      have h := hK2 z hzI; rw [Real.norm_eq_abs] at h; linarith [le_abs_self K2]
    have hb1 : 2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
        ≤ 2 * |K1| * (Cw * (Work.Spaces.w z) ^ 2) := by
      have hm : |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
          ≤ |K1| * (Cw * (Work.Spaces.w z) ^ 2) :=
        mul_le_mul hK1z hzg2 (abs_nonneg _) hK1nn
      calc 2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
          = 2 * (|deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|) := by ring
        _ ≤ 2 * (|K1| * (Cw * (Work.Spaces.w z) ^ 2)) :=
            mul_le_mul_of_nonneg_left hm (by norm_num)
        _ = 2 * |K1| * (Cw * (Work.Spaces.w z) ^ 2) := by ring
    have hb2 : |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ |K2| * (Cw * (Work.Spaces.w z) ^ 2) :=
      mul_le_mul hK2z hzg4 (by positivity) hK2nn
    have hb3 : |deriv χ z| * (z * (Work.Spaces.w z) ^ 2)
        ≤ |K1| * (Cw * (Work.Spaces.w z) ^ 2) :=
      mul_le_mul hK1z hzg5 (by positivity) hK1nn
    constructor
    · calc 2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
            + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
          ≤ 2 * |K1| * (Cw * (Work.Spaces.w z) ^ 2) + |K2| * (Cw * (Work.Spaces.w z) ^ 2) :=
            add_le_add hb1 hb2
        _ = (2 * |K1| * Cw + |K2| * Cw) * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ (2 * |K1| * Cw + |K2| * Cw + |K1| * Cw + 1) * (Work.Spaces.w z) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ hWnn
            linarith [mul_nonneg hK1nn hCwpos.le]
    · calc |deriv χ z| * (z * (Work.Spaces.w z) ^ 2)
          ≤ |K1| * (Cw * (Work.Spaces.w z) ^ 2) := hb3
        _ = (|K1| * Cw) * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ (2 * |K1| * Cw + |K2| * Cw + |K1| * Cw + 1) * (Work.Spaces.w z) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ hWnn
            linarith [mul_nonneg hK1nn hCwpos.le, mul_nonneg hK2nn hCwpos.le]
  · have hzout : z < δ ∨ R < z := by
      rcases lt_or_ge z δ with h | h
      · exact Or.inl h
      · right
        by_contra hcon
        exact hzI ⟨h, le_of_not_gt hcon⟩
    have hzeronear : χ =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
      rcases hzout with hlt | hgt
      · filter_upwards [isOpen_Iio.mem_nhds hlt] with w hw
        exact hχδ w (le_of_lt hw)
      · have hzR : R0 < |z| := by
          rw [abs_of_pos (lt_trans hRpos hgt)]; exact lt_of_le_of_lt hRge hgt
        have hznot : z ∉ tsupport χ := fun h => absurd (hR0 z h) (not_le.mpr hzR)
        have hopen : IsOpen (tsupport χ)ᶜ := (isClosed_tsupport χ).isOpen_compl
        filter_upwards [hopen.mem_nhds hznot] with w hw
        exact image_eq_zero_of_notMem_tsupport hw
    have hd1 : deriv χ z = 0 := by
      have h := hzeronear.deriv_eq
      simpa using h
    have hd2 : deriv (deriv χ) z = 0 := by
      have hev : deriv χ =ᶠ[𝓝 z] (fun _ : ℝ => (0:ℝ)) := by
        have h : deriv χ =ᶠ[𝓝 z] deriv (fun _ : ℝ => (0:ℝ)) := hzeronear.deriv
        rw [show deriv (fun _ : ℝ => (0:ℝ)) = fun _ : ℝ => (0:ℝ) from
          funext (fun x => deriv_const x 0)] at h
        exact h
      have h := hev.deriv_eq
      simpa using h
    rw [hd1, hd2]
    constructor
    · simp only [abs_zero, mul_zero, zero_mul, add_zero]
      exact mul_nonneg hCpos.le hWnn
    · simp only [abs_zero, zero_mul]
      exact mul_nonneg hCpos.le hWnn

/-! ## Two elementary slice-integrability transfer lemmas -/

/-- The junk-friendly monotonicity of the integral over an arbitrary measurable set: it suffices
that the dominating function is nonnegative and integrable. -/
theorem setIntegral_le_of_ae_le_of_nonneg' {s : Set ℝ} (hs : MeasurableSet s) {f g : ℝ → ℝ}
    (hle : f ≤ᵐ[MeasureTheory.volume.restrict s] g)
    (hg0 : 0 ≤ᵐ[MeasureTheory.volume.restrict s] g)
    (hg : MeasureTheory.IntegrableOn g s) :
    (∫ x in s, f x) ≤ ∫ x in s, g x := by
  by_cases hf : MeasureTheory.Integrable f (MeasureTheory.volume.restrict s)
  · exact MeasureTheory.integral_mono_ae hf hg hle
  · rw [MeasureTheory.integral_undef hf]
    exact MeasureTheory.integral_nonneg_of_ae hg0

/-- On the open angular interval the plain square of a slice is dominated by its `σ`-weighted
square (`σ = sin(2θ)^{-η} ≥ 1`). -/
theorem integral_sq_le_integral_sq_sEta (f : ℝ → ℝ)
    (hint : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  refine setIntegral_le_of_ae_le_of_nonneg' measurableSet_Icc ?_ ?_ hint
  · filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ'] with θ hθ
    simpa using mul_le_mul_of_nonneg_left
      (Work.FTS.EllipticEst.Dispatch.one_le_sEta_D hθ) (sq_nonneg (f θ))
  · filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ'] with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (le_trans zero_le_one (Work.FTS.EllipticEst.Dispatch.one_le_sEta_D hθ))

/-- The `w²z²`-weighted first radial energy of `z ∂_z u` is dominated by its `ℋ⁰`-norm. -/
theorem integrableOn_wSq_zsq_sgP {α : ℝ} {u : ℝ → ℝ → ℝ}
    (hmg : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z)
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz,
          (Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z)
        ≤ Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ) := by
  obtain ⟨hint, hval⟩ :=
    Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta (α := α)
      (f := fun z θ => z * Work.Spaces.pz u z θ) hmg
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z
        ≤ (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ) := by
    filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
        = z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z := by
      rw [show (fun θ : ℝ => (z * Work.Spaces.pz u z θ) ^ 2)
          = fun θ : ℝ => z ^ 2 * (Work.Spaces.pz u z θ) ^ 2 from
        funext (fun θ => by ring)]
      rw [MeasureTheory.integral_const_mul]
      rfl
    have h2 : (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ :=
      integral_sq_le_integral_sq_sEta (fun θ => z * Work.Spaces.pz u z θ)
        (Work.FTS.EllipticEst.AngAWeak.integrableOn_slice_sq_mul_sEta hmg (le_of_lt hz) hz)
    calc (Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z
        = (Work.Spaces.w z) ^ 2 * (z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z) := by ring
      _ = (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2) := by rw [h1]
      _ ≤ (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hg0 : ∀ z : ℝ, 0 ≤ (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) := fun z =>
    mul_nonneg (sq_nonneg _)
      (MeasureTheory.integral_nonneg_of_ae (by
        filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ'] with θ hθ
        exact mul_nonneg (sq_nonneg _)
          (le_trans zero_le_one (Work.FTS.EllipticEst.Dispatch.one_le_sEta_D hθ))))
  have hL0 : ∀ z : ℝ, 0 ≤ (Work.Spaces.w z) ^ 2 * z ^ 2
      * Work.FTS.EllipticEst.AngAWeak.sgP u z := fun z =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
  refine ⟨?_, ?_⟩
  · refine MeasureTheory.Integrable.mono' hint haesm ?_
    filter_upwards [hpt] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (hL0 z)]
    exact hz
  · refine le_trans (Work.FTS.EllipticEst.Honest.setIntegral_le_of_ae_le_of_nonneg hpt
      (Filter.Eventually.of_forall hg0) hint) ?_
    rw [hval]

/-! ## The truncated `w²`-weighted energy inequality -/

theorem sgU_nonneg' (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ Work.FTS.EllipticEst.AngAWeak.sgU u z :=
  MeasureTheory.integral_nonneg fun θ => sq_nonneg _

theorem sgY_nonneg' (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ Work.FTS.EllipticEst.AngAWeak.sgY u z :=
  MeasureTheory.integral_nonneg fun θ => sq_nonneg _

theorem sgP_nonneg' (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ Work.FTS.EllipticEst.AngAWeak.sgP u z :=
  MeasureTheory.integral_nonneg fun θ => sq_nonneg _

/-- **The truncated `w²`-weighted energy inequality** of Step 1 of `prop:H2` in the
almost-everywhere class, for an admissible radial cut-off `χ` (this is the shape of
`Work.FTS.EllipticEst.Cores.Pieces.AeGradRho.AeCutEnergyProp`, with the angular profile `sgU u`
as the dominating function). -/
theorem cut_ineq (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (χ : ℝ → ℝ) (hχsm : ContDiff ℝ 2 χ) (hcpt : HasCompactSupport χ)
    (hχ0 : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → χ z = 0)
    (hχnn : ∀ z : ℝ, 0 ≤ χ z) (hχ1 : ∀ z : ℝ, χ z ≤ 1)
    (hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.bslOp α u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pzIter 2 u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => Work.Spaces.pz u z θ * u z θ)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)
            Work.Spaces.Iθ
      ∧ MeasureTheory.IntegrableOn (fun θ => (u z θ) ^ 2) Work.Spaces.Iθ)
    (hIntY : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z)
        Work.Spaces.Iz) :
    α ^ 2 * (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2 * z ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgP u z)
      + (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgY u z)
    ≤ (1 / 2) * (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      + (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
          * (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
              * Work.FTS.EllipticEst.AngAWeak.sgU u z)
      + ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
            (2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
              + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
              * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz, |deriv χ z|
              * (z * (Work.Spaces.w z) ^ 2) * Work.FTS.EllipticEst.AngAWeak.sgU u z)) := by
  obtain ⟨hα, hα4, heq, hd0, hdπ, hsm, hmemG, hmemRad2, hmemAng2, hmomU, hmomG⟩ := h
  have hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G :=
    ⟨hα, hα4, heq, hd0, hdπ, hsm, hmemG, hmemRad2, hmemAng2, hmomU, hmomG⟩
  have hmu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hAe
  have hmg : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hAe
  have hWnn : ∀ z : ℝ, 0 ≤ (Work.Spaces.w z) ^ 2 := fun z => sq_nonneg _
  have hsUnn : ∀ z : ℝ, 0 ≤ Work.FTS.EllipticEst.AngAWeak.sgU u z := sgU_nonneg' u
  have hsYnn : ∀ z : ℝ, 0 ≤ Work.FTS.EllipticEst.AngAWeak.sgY u z := sgY_nonneg' u
  have hsPnn : ∀ z : ℝ, 0 ≤ Work.FTS.EllipticEst.AngAWeak.sgP u z := sgP_nonneg' u
  have hFgnn : ∀ z : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ := fun z =>
    MeasureTheory.integral_nonneg_of_ae (by
      filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ'] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (le_trans zero_le_one (Work.FTS.EllipticEst.Dispatch.one_le_sEta_D hθ)))
  -- a.e. statements can be transferred from `(0,∞)` to `Iz`
  have hIz : (MeasureTheory.volume.restrict Work.Spaces.Iz : MeasureTheory.Measure ℝ)
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  -- ### the scalar integrals
  set A : ℝ := ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2 * z ^ 2
      * Work.FTS.EllipticEst.AngAWeak.sgP u z with hA
  set B : ℝ := ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
      * Work.FTS.EllipticEst.AngAWeak.sgY u z with hB
  set M : ℝ := ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
      * Work.FTS.EllipticEst.AngAWeak.sgU u z with hM
  set SM : ℝ := ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
      * Work.FTS.EllipticEst.AngAWeak.sgM u z with hSM
  set G2 : ℝ := ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) with hG2
  set Src : ℝ := ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ) with hSrc
  set W2 : ℝ := ∫ z in Work.Spaces.Iz,
      deriv (deriv (fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y ^ 2)) z
        * Work.FTS.EllipticEst.AngAWeak.sgU u z with hW2
  set W1 : ℝ := ∫ z in Work.Spaces.Iz,
      deriv (fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y) z
        * Work.FTS.EllipticEst.AngAWeak.sgU u z with hW1
  set E1 : ℝ := ∫ z in Work.Spaces.Iz, (2 * |deriv χ z|
      * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
      + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
      * Work.FTS.EllipticEst.AngAWeak.sgU u z with hE1
  set E2 : ℝ := ∫ z in Work.Spaces.Iz, |deriv χ z| * (z * (Work.Spaces.w z) ^ 2)
      * Work.FTS.EllipticEst.AngAWeak.sgU u z with hE2
  -- ### the truncated energy identity
  obtain ⟨δχ, hδχpos, hδχ⟩ := hχ0
  have hε' : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Set.Icc (0:ℝ) ε, χ z = 0 :=
    ⟨δχ, hδχpos, fun z hz => hδχ z hz.2⟩
  have hid := Work.FTS.EllipticEst.H2W.AeW.aeTruncWHon α u G hAe hsm hmu hmg χ hχsm hcpt hε'
    hslice
  have hstep1 : (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ))
      = ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ) := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ici ?_
    filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz_vol] with z hz hzI
    have hinner : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α u z θ * u z θ)
        = ∫ θ in Work.Spaces.Iθ, G z θ * u z θ := by
      refine MeasureTheory.setIntegral_congr_ae measurableSet_Icc ?_
      filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_of_mem_Iθ_vol] with θ hθ hθI
      rw [heq z (hz hzI) θ (hθ hθI).1 (hθ hθI).2]
    rw [hinner]
  have hstep2 : (∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2))
      = ∫ z in Work.Spaces.Iz, χ z * (Work.Spaces.w z) ^ 2 * z ^ 2
        * Work.FTS.EllipticEst.AngAWeak.sgP u z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    have hinner : (∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2)
        = z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z := by
      rw [show (fun θ : ℝ => (z * Work.Spaces.pz u z θ) ^ 2)
          = fun θ : ℝ => z ^ 2 * (Work.Spaces.pz u z θ) ^ 2 from
        funext (fun θ => by ring)]
      rw [MeasureTheory.integral_const_mul]
      rfl
    rw [hinner]
    ring
  have hid' : α ^ 2 * A + SM = Src + (α ^ 2 / 2) * W2 - ((α * (5 + α)) / 2) * W1 := by
    rw [hA, hSM, hSrc, hW2, hW1]
    have h1 := hid
    rw [hstep1, hstep2] at h1
    simp only [Work.FTS.EllipticEst.AngAWeak.sgM, Work.FTS.EllipticEst.AngAWeak.sgP,
      Work.FTS.EllipticEst.AngAWeak.sgU] at h1 ⊢
    linarith [h1]
  -- ### measurability
  have hcont1 : Continuous (deriv χ) := by
    rw [← continuousOn_univ]
    exact (hχsm.contDiffOn.deriv_of_isOpen isOpen_univ (m := 1) (by norm_num)).continuousOn
  have hcont2 : Continuous (deriv (deriv χ)) := by
    rw [← continuousOn_univ]
    exact ((hχsm.contDiffOn.deriv_of_isOpen isOpen_univ (m := 1) (by norm_num)).deriv_of_isOpen
      isOpen_univ (m := 0) (by norm_num)).continuousOn
  have hmeas_chi : Measurable χ := hχsm.continuous.measurable
  have hmeasw : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) :=
    Work.FTS.EllipticEst.AngAWeak.AeMain.w_sq_measurable'
  have hmeas_dv2 : Measurable (fun z : ℝ => 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3) := by fun_prop
  have hdv2 : (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z : ℝ => 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3) := by
    filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
    exact weight_algebra_fts.2.2.1 z (ne_of_gt hz)
  have haesm_dv2 : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmeas_dv2.aestronglyMeasurable.congr hdv2.symm
  have haesm_sU : MeasureTheory.AEStronglyMeasurable
      (Work.FTS.EllipticEst.AngAWeak.sgU u)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    change MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
    exact Work.FTS.EllipticEst.AngAWeak.AeMain.P_aesm hAe
  have hmeas_chiW : Measurable (fun z : ℝ => χ z * (Work.Spaces.w z) ^ 2) :=
    hmeas_chi.mul hmeasw
  -- ### integrability of the weighted profiles
  have hIU : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z)
      Work.Spaces.Iz :=
    (Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sgU hAe hmu).1
  have hIG : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      Work.Spaces.Iz :=
    (Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta (α := α) (f := G) hmemG).1
  have hIP : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z)
      Work.Spaces.Iz :=
    (integrableOn_wSq_zsq_sgP (α := α) hmg
      (by simpa only [Work.FTS.EllipticEst.AngAWeak.sgP] using
        Work.FTS.EllipticEst.AngAWeak.aesm_wSq_zsq_sgP hAe)).1
  have hIdB : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.dBnd α u G z)
      Work.Spaces.Iz :=
    Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_dBnd hAe hmu hmg
  obtain ⟨Cχ, hCχpos, hCχ⟩ := exists_cut_bound hχsm hcpt ⟨δχ, hδχpos, hδχ⟩
  -- the truncated weights
  have haesm_WU : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hIU.aestronglyMeasurable
  have haesm_WY : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hIntY.aestronglyMeasurable
  have haesm_WF : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hIG.aestronglyMeasurable
  have haesm_WM : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgM u z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.EllipticEst.AngAWeak.aesm_wSq_sgM hAe
  have chi_le_one : ∀ z : ℝ, χ z * (Work.Spaces.w z) ^ 2 ≤ 1 * (Work.Spaces.w z) ^ 2 :=
    fun z => mul_le_mul_of_nonneg_right (hχ1 z) (hWnn z)
  have hIchiU : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hIU ?_ ?_
    · refine ((hmeas_chi.aestronglyMeasurable).mul haesm_WU).congr
        (Filter.Eventually.of_forall fun z => by simp only [Pi.mul_apply]; ring)
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hχnn z) (hWnn z))
        (hsUnn z))]
      calc χ z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z
          = (χ z * (Work.Spaces.w z) ^ 2) * Work.FTS.EllipticEst.AngAWeak.sgU u z := rfl
        _ ≤ (1 * (Work.Spaces.w z) ^ 2) * Work.FTS.EllipticEst.AngAWeak.sgU u z :=
            mul_le_mul_of_nonneg_right (chi_le_one z) (hsUnn z)
        _ = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z := by ring
  have hIchiY : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hIntY ?_ ?_
    · refine ((hmeas_chi.aestronglyMeasurable).mul haesm_WY).congr
        (Filter.Eventually.of_forall fun z => by simp only [Pi.mul_apply]; ring)
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hχnn z) (hWnn z))
        (hsYnn z))]
      calc χ z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z
          = (χ z * (Work.Spaces.w z) ^ 2) * Work.FTS.EllipticEst.AngAWeak.sgY u z := rfl
        _ ≤ (1 * (Work.Spaces.w z) ^ 2) * Work.FTS.EllipticEst.AngAWeak.sgY u z :=
            mul_le_mul_of_nonneg_right (chi_le_one z) (hsYnn z)
        _ = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z := by ring
  have hIchiF : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hIG ?_ ?_
    · refine ((hmeas_chi.aestronglyMeasurable).mul haesm_WF).congr
        (Filter.Eventually.of_forall fun z => by simp only [Pi.mul_apply]; ring)
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hχnn z) (hWnn z))
        (hFgnn z))]
      calc χ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          = (χ z * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := rfl
        _ ≤ (1 * (Work.Spaces.w z) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :=
            mul_le_mul_of_nonneg_right (chi_le_one z) (hFgnn z)
        _ = (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring
  have hIsgM : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgM u z)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hIdB ?_ ?_
    · refine ((hmeas_chi.aestronglyMeasurable).mul haesm_WM).congr
        (Filter.Eventually.of_forall fun z => by simp only [Pi.mul_apply]; ring)
    · filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hzpos
      have hb := Work.FTS.EllipticEst.AngAWeak.abs_sgM_le hAe hmu hmg hzpos
      rw [Real.norm_eq_abs]
      have habs : |χ z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgM u z|
          = χ z * ((Work.Spaces.w z) ^ 2
              * |Work.FTS.EllipticEst.AngAWeak.sgM u z|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hχnn z), abs_of_nonneg (hWnn z)]; ring
      rw [habs]
      calc χ z * ((Work.Spaces.w z) ^ 2 * |Work.FTS.EllipticEst.AngAWeak.sgM u z|)
          ≤ 1 * ((Work.Spaces.w z) ^ 2 * |Work.FTS.EllipticEst.AngAWeak.sgM u z|) :=
            mul_le_mul_of_nonneg_right (hχ1 z)
              (mul_nonneg (hWnn z) (abs_nonneg _))
        _ = (Work.Spaces.w z) ^ 2 * |Work.FTS.EllipticEst.AngAWeak.sgM u z| := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.dBnd α u G z :=
            mul_le_mul_of_nonneg_left hb (hWnn z)
  have hIe1 : MeasureTheory.IntegrableOn (fun z => (2 * |deriv χ z|
        * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
        + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
        * Work.FTS.EllipticEst.AngAWeak.sgU u z) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' (hIU.const_mul Cχ) ?_ ?_
    · have heq : (fun z => 2 * |deriv χ z|
            * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
              + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          (fun z => 2 * |deriv χ z| * |2 * (z - 1) * (1 + z) ^ 3 / z ^ 3|
              + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) := by
        filter_upwards [hdv2] with z hz
        rw [hz]
      have hmeas1 : Measurable (fun z => 2 * |deriv χ z| * |2 * (z - 1) * (1 + z) ^ 3 / z ^ 3|
            + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)) :=
        Measurable.add
          (Measurable.mul (measurable_const.mul hcont1.measurable.abs) hmeas_dv2.abs)
          (Measurable.mul hcont2.measurable.abs ((measurable_id.pow_const 2).mul hmeasw))
      refine ((hmeas1.aestronglyMeasurable).mul haesm_sU).congr ?_
      filter_upwards [heq] with z hz
      rw [hz]
      simp only [Pi.mul_apply]
    · filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
      have h1 : 0 ≤ 2 * |deriv χ z|
          * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
            + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 (hsUnn z))]
      calc (2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
              + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * Work.FTS.EllipticEst.AngAWeak.sgU u z
          ≤ (Cχ * (Work.Spaces.w z) ^ 2) * Work.FTS.EllipticEst.AngAWeak.sgU u z :=
            mul_le_mul_of_nonneg_right (hCχ z).1 (hsUnn z)
        _ = Cχ * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by ring
  have hIe2 : MeasureTheory.IntegrableOn (fun z => |deriv χ z| * (z * (Work.Spaces.w z) ^ 2)
        * Work.FTS.EllipticEst.AngAWeak.sgU u z) Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' (hIU.const_mul Cχ) ?_ ?_
    · have hmeas1 : Measurable (fun z => |deriv χ z| * (z * (Work.Spaces.w z) ^ 2)) :=
        (hcont1.measurable.abs).mul (measurable_id.mul hmeasw)
      exact (hmeas1.aestronglyMeasurable).mul haesm_sU
    · filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
      have h1 : 0 ≤ |deriv χ z| * (z * (Work.Spaces.w z) ^ 2) :=
        mul_nonneg (abs_nonneg _) (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 (hsUnn z))]
      calc |deriv χ z| * (z * (Work.Spaces.w z) ^ 2) * Work.FTS.EllipticEst.AngAWeak.sgU u z
          ≤ (Cχ * (Work.Spaces.w z) ^ 2) * Work.FTS.EllipticEst.AngAWeak.sgU u z :=
            mul_le_mul_of_nonneg_right (hCχ z).2 (hsUnn z)
        _ = Cχ * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by ring
  -- a.e. pointwise facts
  have hL0 := Work.FTS.EllipticEst.Dispatch.aeLeftLimitD α u G hAe
  have hC := Work.FTS.EllipticEst.H2W.AeProof.ae_continuousOn_slice hAe hL0
  have hgap0 := Work.FTS.EllipticEst.AngAWeak.ae_gap_self hAe hC
  have hpt_gap : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Work.FTS.EllipticEst.AngAWeak.sgY u z
        ≤ Work.FTS.EllipticEst.AngAWeak.sgM u z
          + 6 * Work.FTS.EllipticEst.AngAWeak.sgU u z := by
    rw [hIz]
    filter_upwards [hgap0] with z hz
    exact hz.2
  have hpt_src : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, G z θ * u z θ)
        ≤ (1 / 2) * ((∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            + Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
    filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
    have hb := Work.FTS.EllipticEst.AngAWeak.abs_sgI_le hAe hmu hz
    have hIeq : Work.FTS.EllipticEst.AngAWeak.sgI G u z
        = ∫ θ in Work.Spaces.Iθ, G z θ * u z θ := rfl
    rw [hIeq] at hb
    exact le_trans (le_abs_self _) hb
  have hpt_w2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      -(6 * χ z * (Work.Spaces.w z) ^ 2
        + 2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
        + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
        ≤ deriv (deriv (fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y ^ 2)) z := by
    filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
    have htw := Work.FTS.EllipticEst.Honest.TruncCutDerivTwo χ hχsm z hz
    rw [htw]
    have h0 : 0 ≤ deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z :=
      weight_algebra_fts.2.2.2.2.2.2.2.1 z hz
    have h1 : -|deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ deriv (deriv χ) z * (z ^ 2 * (Work.Spaces.w z) ^ 2) :=
      mul_le_mul_of_nonneg_right (neg_abs_le _) (by positivity)
    have h2 : -2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
        ≤ 2 * deriv χ z * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z := by
      have h := neg_abs_le (deriv χ z * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z)
      rw [abs_mul] at h
      nlinarith [h]
    have h3 : 0 ≤ χ z * deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z :=
      mul_nonneg (hχnn z) h0
    have h4 : 0 ≤ 6 * χ z * (Work.Spaces.w z) ^ 2 := by
      have := hχnn z; have := hWnn z; nlinarith
    linarith [h1, h2, h3, h4]
  have hpt_w1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |deriv (fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y) z|
        ≤ |deriv χ z| * (z * (Work.Spaces.w z) ^ 2)
          + 3 * (χ z * (Work.Spaces.w z) ^ 2) := by
    filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
    have htw := Work.FTS.EllipticEst.Honest.TruncCutDerivOne χ hχsm z hz
    rw [htw]
    have h3 : |deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z|
        ≤ 3 * (Work.Spaces.w z) ^ 2 :=
      Work.FTS.EllipticEst.Honest.deriv_zwSq_abs_le z hz
    have hzWnn : 0 ≤ z * (Work.Spaces.w z) ^ 2 := by positivity
    calc |deriv χ z * (z * (Work.Spaces.w z) ^ 2)
            + χ z * deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z|
        ≤ |deriv χ z * (z * (Work.Spaces.w z) ^ 2)|
            + |χ z * deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z| := abs_add_le _ _
      _ = |deriv χ z| * (z * (Work.Spaces.w z) ^ 2)
            + χ z * |deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hχnn z),
            abs_of_nonneg (le_of_lt hz), abs_of_nonneg (hWnn z)]
      _ ≤ |deriv χ z| * (z * (Work.Spaces.w z) ^ 2) + χ z * (3 * (Work.Spaces.w z) ^ 2) := by
          have h5 := mul_le_mul_of_nonneg_left h3 (hχnn z)
          linarith [h5]
      _ = |deriv χ z| * (z * (Work.Spaces.w z) ^ 2) + 3 * (χ z * (Work.Spaces.w z) ^ 2) := by
          ring
  have hpt_w2b : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      deriv (deriv (fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y ^ 2)) z
        ≤ 6 * χ z * (Work.Spaces.w z) ^ 2
          + 2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
          + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) := by
    filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
    have htw := Work.FTS.EllipticEst.Honest.TruncCutDerivTwo χ hχsm z hz
    rw [htw]
    have h0 : deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z
        ≤ 6 * (Work.Spaces.w z) ^ 2 := weight_algebra_fts.2.2.2.2.2.1 z hz
    have h1 : deriv (deriv χ) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h2 : 2 * deriv χ z * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z
        ≤ 2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z| := by
      have hh := le_abs_self (deriv χ z
        * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z)
      rw [abs_mul] at hh
      linarith [hh]
    have h3 : χ z * deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z
        ≤ χ z * (6 * (Work.Spaces.w z) ^ 2) := mul_le_mul_of_nonneg_left h0 (hχnn z)
    linarith [h1, h2, h3]
  -- ### the four comparisons
  have hcmp_M : B ≤ SM + 6 * M := by
    rw [hB, hM, hSM]
    have hle : (fun z => χ z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => χ z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgM u z
          + 6 * (χ z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z)) := by
      filter_upwards [hpt_gap] with z hz
      have h1 : χ z * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z
          ≤ χ z * (Work.Spaces.w z) ^ 2
            * (Work.FTS.EllipticEst.AngAWeak.sgM u z
              + 6 * Work.FTS.EllipticEst.AngAWeak.sgU u z) :=
        mul_le_mul_of_nonneg_left hz (mul_nonneg (hχnn z) (hWnn z))
      linarith [h1]
    have hmain := MeasureTheory.integral_mono_ae hIchiY
      (hIsgM.add (hIchiU.const_mul 6)) hle
    simp only [Pi.add_apply] at hmain
    rw [MeasureTheory.integral_add hIsgM (hIchiU.const_mul 6)] at hmain
    rw [MeasureTheory.integral_const_mul] at hmain
    linarith [hmain]
  have hcmp_W2 : (α ^ 2 / 2) * W2 ≤ 3 * α ^ 2 * M + (α ^ 2 / 2) * E1 := by
    rw [hW2, hM, hE1]
    set A2 : ℝ → ℝ := fun z => 2 * |deriv χ z|
      * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
      + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) with hA2
    have hA2' : MeasureTheory.IntegrableOn
        (fun z => A2 z * Work.FTS.EllipticEst.AngAWeak.sgU u z) Work.Spaces.Iz := by
      rw [show A2 = fun z => 2 * |deriv χ z|
          * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
          + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) from hA2]
      exact hIe1
    have h6 : MeasureTheory.IntegrableOn
        (fun z => 6 * (χ z * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)) Work.Spaces.Iz :=
      hIchiU.const_mul 6
    have hG : MeasureTheory.IntegrableOn (fun z => 6 * (χ z * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        + A2 z * Work.FTS.EllipticEst.AngAWeak.sgU u z) Work.Spaces.Iz := h6.add hA2'
    have hA2nn : ∀ z : ℝ, 0 ≤ A2 z := by
      intro z; rw [hA2]; positivity
    have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        deriv (deriv (fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y ^ 2)) z
          * Work.FTS.EllipticEst.AngAWeak.sgU u z
          ≤ 6 * (χ z * (Work.Spaces.w z) ^ 2
              * Work.FTS.EllipticEst.AngAWeak.sgU u z)
            + A2 z * Work.FTS.EllipticEst.AngAWeak.sgU u z := by
      filter_upwards [hpt_w2b] with z hz
      have hz' : deriv (deriv (fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y ^ 2)) z
          ≤ 6 * χ z * (Work.Spaces.w z) ^ 2 + A2 z := by
        have h := hz
        rw [hA2]
        linarith [h]
      have h1 := mul_le_mul_of_nonneg_right hz' (hsUnn z)
      linarith [h1]
    have hGnn : ∀ z : ℝ, 0 ≤ 6 * (χ z * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        + A2 z * Work.FTS.EllipticEst.AngAWeak.sgU u z := by
      intro z
      have h1 := hχnn z; have h2 := hWnn z; have h3 := hsUnn z; have h4 := hA2nn z
      nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) h3, mul_nonneg h4 h3]
    have h1 := Work.FTS.EllipticEst.Honest.setIntegral_le_of_ae_le_of_nonneg hle
      (Filter.Eventually.of_forall hGnn) hG
    rw [MeasureTheory.integral_add h6 hA2'] at h1
    rw [MeasureTheory.integral_const_mul] at h1
    have h2 : (∫ z in Work.Spaces.Iz, A2 z * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        = (∫ z in Work.Spaces.Iz, (2 * |deriv χ z|
            * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
            + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
      rw [show A2 = fun z => 2 * |deriv χ z|
          * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
          + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) from hA2]
    rw [h2] at h1
    have hc : (0:ℝ) ≤ α ^ 2 / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hc]
  have hcmp_W1 : -((α * (5 + α)) / 2) * W1
      ≤ (3 * α * (5 + α) / 2) * M + (α * (5 + α) / 2) * E2 := by
    rw [hW1, hM, hE2]
    set B2 : ℝ → ℝ := fun z => 3 * (χ z * (Work.Spaces.w z) ^ 2)
      + |deriv χ z| * (z * (Work.Spaces.w z) ^ 2) with hB2
    have h3 : MeasureTheory.IntegrableOn
        (fun z => 3 * (χ z * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)) Work.Spaces.Iz :=
      hIchiU.const_mul 3
    have hG : MeasureTheory.IntegrableOn (fun z => 3 * (χ z * (Work.Spaces.w z) ^ 2
        * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        + |deriv χ z| * (z * (Work.Spaces.w z) ^ 2)
          * Work.FTS.EllipticEst.AngAWeak.sgU u z) Work.Spaces.Iz := h3.add hIe2
    have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        -(3 * (χ z * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)
          + |deriv χ z| * (z * (Work.Spaces.w z) ^ 2)
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)
          ≤ deriv (fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y) z
            * Work.FTS.EllipticEst.AngAWeak.sgU u z := by
      filter_upwards [hpt_w1] with z hz
      have h1 : -(|deriv χ z| * (z * (Work.Spaces.w z) ^ 2)
            + 3 * (χ z * (Work.Spaces.w z) ^ 2))
          ≤ deriv (fun y : ℝ => χ y * (Work.Spaces.w y) ^ 2 * y) z := (abs_le.mp hz).1
      have h2 := mul_le_mul_of_nonneg_right h1 (hsUnn z)
      linarith [h2]
    have h1 := Work.FTS.EllipticEst.Honest.neg_setIntegral_le_of_ae_le hle
      (by
        filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
        have h1 := hχnn z; have h2 := hWnn z; have h3 := hsUnn z
        have h4 : (0:ℝ) ≤ z := le_of_lt hz
        nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) h3,
          mul_nonneg (mul_nonneg (abs_nonneg (deriv χ z)) (mul_nonneg h4 h2)) h3]) hG
    rw [MeasureTheory.integral_add h3 hIe2] at h1
    rw [MeasureTheory.integral_const_mul] at h1
    have hc : (0:ℝ) ≤ α * (5 + α) / 2 := by nlinarith [hα, hα4]
    nlinarith [mul_le_mul_of_nonneg_left h1 hc]
  have hcmp_src : Src ≤ (1 / 2) * G2 + (1 / 2) * M := by
    rw [hSrc, hG2, hM]
    have hle : (fun z => χ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, G z θ * u z θ))
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => (1 / 2) * (χ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          + (1 / 2) * (χ z * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)) := by
      filter_upwards [hpt_src] with z hz
      have h1 := mul_le_mul_of_nonneg_left hz (mul_nonneg (hχnn z) (hWnn z))
      ring_nf at h1 ⊢
      linarith [h1]
    have hG : MeasureTheory.IntegrableOn
        (fun z => (1 / 2) * (χ z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
          + (1 / 2) * (χ z * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)) Work.Spaces.Iz :=
      (hIchiF.const_mul (1 / 2)).add (hIchiU.const_mul (1 / 2))
    have hGnn : ∀ z : ℝ, 0 ≤ (1 / 2) * (χ z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        + (1 / 2) * (χ z * (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
      intro z
      have h1 := hχnn z; have h2 := hWnn z
      nlinarith [hFgnn z, hsUnn z, mul_nonneg h1 h2,
        mul_nonneg (mul_nonneg h1 h2) (hFgnn z), mul_nonneg (mul_nonneg h1 h2) (hsUnn z)]
    have h1 := Work.FTS.EllipticEst.Honest.setIntegral_le_of_ae_le_of_nonneg hle
      (Filter.Eventually.of_forall hGnn) hG
    rw [MeasureTheory.integral_add (hIchiF.const_mul (1 / 2)) (hIchiU.const_mul (1 / 2))] at h1
    rw [MeasureTheory.integral_const_mul] at h1
    rw [MeasureTheory.integral_const_mul] at h1
    linarith [h1]
  -- ### assembly
  have hmain1 : α ^ 2 * A + B ≤ α ^ 2 * A + SM + 6 * M := by linarith [hcmp_M]
  have hmain2 : α ^ 2 * A + SM
      ≤ (1 / 2) * G2 + (1 / 2) * M + (3 * α ^ 2 * M + (α ^ 2 / 2) * E1)
        + ((3 * α * (5 + α) / 2) * M + (α * (5 + α) / 2) * E2) := by
    linarith [hid', hcmp_W2, hcmp_W1, hcmp_src]
  linarith [hmain1, hmain2]

/-- A function is integrable after multiplication by a bounded measurable weight. -/
theorem integrableOn_mul_of_bounded {f χ : ℝ → ℝ} (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    (hmeas : Measurable χ) (hf : MeasureTheory.IntegrableOn f Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun z => χ z * f z) Work.Spaces.Iz := by
  refine MeasureTheory.Integrable.mono' hf.norm
    ((hmeas.aestronglyMeasurable.mul hf.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun z => by simp only [Pi.mul_apply])) ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hχ0 z)]
  exact mul_le_of_le_one_left (abs_nonneg _) (hχ1 z)

theorem AeW2Energy : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pth u z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ C * (Work.Spaces.HkSq α 0 G
            + α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by
  refine ⟨144 / 11, by norm_num, fun α u G h => ?_⟩
  obtain ⟨hα, hα4, heq, hd0, hdπ, hsm, hmemG, hmemRad2, hmemAng2, hmomU, hmomG⟩ := h
  have hAe : Work.FTS.EllipticEst.H2W.Ae.AeData α u G :=
    ⟨hα, hα4, heq, hd0, hdπ, hsm, hmemG, hmemRad2, hmemAng2, hmomU, hmomG⟩
  have hsUnn : ∀ z : ℝ, 0 ≤ Work.FTS.EllipticEst.AngAWeak.sgU u z := sgU_nonneg' u
  have hsYnn : ∀ z : ℝ, 0 ≤ Work.FTS.EllipticEst.AngAWeak.sgY u z := sgY_nonneg' u
  have hsPnn : ∀ z : ℝ, 0 ≤ Work.FTS.EllipticEst.AngAWeak.sgP u z := sgP_nonneg' u
  have hWnn : ∀ z : ℝ, 0 ≤ (Work.Spaces.w z) ^ 2 := fun z => sq_nonneg _
  -- the left hand side is the `w²`-weighted angular energy
  have hLHS : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pth u z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgY u z := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    rw [MeasureTheory.integral_mul_const, mul_comm]
    rfl
  rw [hLHS]
  by_cases hIntY : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z)
      Work.Spaces.Iz
  · -- ### the honest case
    have hmu : Work.Spaces.HkMem α 0 u := Work.FTS.EllipticEst.Dispatch.hkMem_uM α u G hAe
    have hmg : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ) :=
      Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hAe
    have hslice := Work.FTS.EllipticEst.Cores.Pieces.AeW2SliceBundle α u G hAe
    have hIU : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        Work.Spaces.Iz :=
      (Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sgU hAe hmu).1
    have hIGval : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        = Work.Spaces.HkSq α 0 G :=
      (Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta (α := α) (f := G)
        hmemG).2
    have hIP : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z)
        Work.Spaces.Iz :=
      (integrableOn_wSq_zsq_sgP (α := α) hmg
        (by simpa only [Work.FTS.EllipticEst.AngAWeak.sgP] using
          Work.FTS.EllipticEst.AngAWeak.aesm_wSq_zsq_sgP hAe)).1
    have hL0 := Work.FTS.EllipticEst.Dispatch.aeLeftLimitD α u G hAe
    have hC := Work.FTS.EllipticEst.H2W.AeProof.ae_continuousOn_slice hAe hL0
    have hgap0 := Work.FTS.EllipticEst.AngAWeak.ae_gap_self hAe hC
    have hIz : (MeasureTheory.volume.restrict Work.Spaces.Iz : MeasureTheory.Measure ℝ)
        = MeasureTheory.volume.restrict (Set.Ioi 0) := by
      rw [Work.Spaces.Iz]
      exact MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
    have hgap : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        9 * Work.FTS.EllipticEst.AngAWeak.sgU u z
          ≤ Work.FTS.EllipticEst.AngAWeak.sgY u z := by
      rw [hIz]
      filter_upwards [hgap0] with z hz
      exact hz.1
    -- the two functionals
    let Y : ℝ → ℝ := fun z => α ^ 2 * ((Work.Spaces.w z) ^ 2 * z ^ 2
        * Work.FTS.EllipticEst.AngAWeak.sgP u z)
      + ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z)
    let Z : ℝ → ℝ := fun z => (1 / 2) * ((Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      + (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
        * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z)
    let Bd : ℕ → ℝ := fun n => (1 / 2) * (∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      + (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α)) * (∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)
      + ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz, (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
            * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
              * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
            |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)
              * Work.FTS.EllipticEst.AngAWeak.sgU u z))
    have hYint : MeasureTheory.IntegrableOn Y Work.Spaces.Iz := by
      have h1 : MeasureTheory.IntegrableOn
          (fun z => α ^ 2 * ((Work.Spaces.w z) ^ 2 * z ^ 2
              * Work.FTS.EllipticEst.AngAWeak.sgP u z)) Work.Spaces.Iz := hIP.const_mul (α ^ 2)
      exact (h1.add hIntY).congr (Filter.Eventually.of_forall fun z => by
        simp only [Y, Pi.add_apply])
    have hZint : MeasureTheory.IntegrableOn Z Work.Spaces.Iz := by
      have h1 : MeasureTheory.IntegrableOn (fun z => (1 / 2) * ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
          Work.Spaces.Iz :=
        (Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta (α := α) (f := G)
          hmemG).1.const_mul (1 / 2)
      have h2 : MeasureTheory.IntegrableOn (fun z => (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
            * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z))
          Work.Spaces.Iz := hIU.const_mul _
      exact (h1.add h2).congr (Filter.Eventually.of_forall fun z => by
        simp only [Z, Pi.add_apply])
    have hYnn : ∀ z : ℝ, 0 ≤ Y z := by
      intro z
      have h1 := hsPnn z; have h2 := hsYnn z; have h3 := hWnn z
      have h4 : 0 ≤ z ^ 2 := sq_nonneg z
      have h5 : 0 ≤ α ^ 2 := sq_nonneg α
      simp only [Y]
      nlinarith [mul_nonneg h5 (mul_nonneg (mul_nonneg h3 h4) h1),
        mul_nonneg h3 h2]
    have hZnn : ∀ z : ℝ, 0 ≤ Z z := by
      intro z
      have h1 := hsUnn z; have h2 := hWnn z
      have h3 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.integral_nonneg_of_ae (by
          filter_upwards [Work.FTS.EllipticEst.Honest.ae_mem_Ioo_Iθ'] with θ hθ
          exact mul_nonneg (sq_nonneg _)
            (le_trans zero_le_one (Work.FTS.EllipticEst.Dispatch.one_le_sEta_D hθ)))
      have h4 : 0 ≤ 13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α) := by nlinarith [hα, hα4]
      simp only [Z]
      exact add_nonneg (mul_nonneg (by norm_num) (mul_nonneg h2 h3))
        (mul_nonneg h4 (mul_nonneg h2 h1))
    have hYasm : MeasureTheory.AEStronglyMeasurable Y
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := hYint.aestronglyMeasurable
    -- the truncated inequalities
    have hcutadm : ∀ n : ℕ,
        Work.FTS.EllipticEst.Honest.HR2.Admissible (Work.FTS.EllipticEst.cut n) :=
      Work.FTS.EllipticEst.Honest.HR2.cut_admissible
    have hcutmeas : ∀ n : ℕ, Measurable (Work.FTS.EllipticEst.cut n) := fun n =>
      ((hcutadm n).1).continuous.measurable
    have hbound : ∀ n : ℕ, (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Y z)
        ≤ Bd n := by
      intro n
      have hp : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * z ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgP u z) Work.Spaces.Iz := hIP
      have hchiP : MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
          * ((Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z))
          Work.Spaces.Iz :=
        integrableOn_mul_of_bounded (hcutadm n).2.2.1 (hcutadm n).2.2.2.1 (hcutmeas n) hp
      have hchiY : MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.cut n z
          * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z)) Work.Spaces.Iz :=
        integrableOn_mul_of_bounded (hcutadm n).2.2.1 (hcutadm n).2.2.2.1 (hcutmeas n) hIntY
      have hmain := cut_ineq α u G hAe (Work.FTS.EllipticEst.cut n) (hcutadm n).1
        (hcutadm n).2.1 (hcutadm n).2.2.2.2 (hcutadm n).2.2.1 (hcutadm n).2.2.2.1 hslice hIntY
      have hf1 : MeasureTheory.IntegrableOn (fun z => α ^ 2 * (Work.FTS.EllipticEst.cut n z
          * (Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z))
          Work.Spaces.Iz := by
        have h := integrableOn_mul_of_bounded (hcutadm n).2.2.1 (hcutadm n).2.2.2.1 (hcutmeas n)
          (hIP.const_mul (α ^ 2))
        exact h.congr (Filter.Eventually.of_forall fun z => by
          simp only [Pi.mul_apply]; ring)
      have hsplitY : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Y z)
          = α ^ 2 * (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z
                * (Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z)
            + (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z
                * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgY u z) := by
        have hcongr : (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.cut n z * Y z)
            = ∫ z in Work.Spaces.Iz, α ^ 2 * (Work.FTS.EllipticEst.cut n z
                  * (Work.Spaces.w z) ^ 2 * z ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgP u z)
              + Work.FTS.EllipticEst.cut n z * ((Work.Spaces.w z) ^ 2
                * Work.FTS.EllipticEst.AngAWeak.sgY u z) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
          simp only [Y]
          ring
        rw [hcongr]
        rw [MeasureTheory.integral_add hf1 hchiY]
        rw [MeasureTheory.integral_const_mul]
        congr 1
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
        ring
      rw [hsplitY]
      simpa only [Bd] using hmain
    -- the limiting family
    have hWlim : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z) Filter.atTop (nhds 1) := by
      filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
      exact Work.FTS.EllipticEst.Honest.HR2.cut_tendsto_one hz
    have hA0 : (0:ℝ) ≤ ∫ z in Work.Spaces.Iz, Z z :=
      MeasureTheory.integral_nonneg fun z => hZnn z
    have hWint : ∀ n : ℕ, MeasureTheory.IntegrableOn
        (fun z => Work.FTS.EllipticEst.cut n z * Y z) Work.Spaces.Iz := fun n =>
      integrableOn_mul_of_bounded ((hcutadm n).2.2.1) ((hcutadm n).2.2.2.1) (hcutmeas n) hYint
    have h1 : Filter.Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        Filter.atTop (nhds (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun z => |(Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)|)
        (fun n => ?_) ?_ (fun n => ?_) ?_
      · refine ((hcutmeas n).aestronglyMeasurable.mul
          ((Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta (α := α) (f := G)
            hmemG).1.aestronglyMeasurable)).congr
          (Filter.Eventually.of_forall fun z => by simp only [Pi.mul_apply]; ring)
      · exact (Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta (α := α) (f := G)
          hmemG).1.abs
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
        have hWz : (0:ℝ) ≤ (Work.Spaces.w z) ^ 2 := hWnn z
        have h1c := (hcutadm n).2.2.1 z
        have h2c := (hcutadm n).2.2.2.1 z
        have hFnn : (0:ℝ) ≤ |∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ| :=
          abs_nonneg _
        rw [Real.norm_eq_abs]
        have hsplit : |Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
              * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)|
            = Work.FTS.EllipticEst.cut n z * ((Work.Spaces.w z) ^ 2
                * |∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg h1c, abs_of_nonneg hWz]
          ring
        rw [hsplit, abs_mul, abs_of_nonneg hWz]
        nlinarith [hFnn, hWz, h1c, h2c, mul_nonneg hWz hFnn]
      · filter_upwards [hWlim] with z hz
        have h := hz.mul_const ((Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
        simpa only [one_mul, mul_assoc] using h
    have h2 : Filter.Tendsto (fun n : ℕ => ∫ z in Work.Spaces.Iz,
          Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        Filter.atTop (nhds (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgU u z)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun z => |(Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z|)
        (fun n => ?_) ?_ (fun n => ?_) ?_
      · refine ((hcutmeas n).aestronglyMeasurable.mul hIU.aestronglyMeasurable).congr
          (Filter.Eventually.of_forall fun z => by simp only [Pi.mul_apply]; ring)
      · exact hIU.abs
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with z hz
        have hWz : (0:ℝ) ≤ (Work.Spaces.w z) ^ 2 := hWnn z
        have h1c := (hcutadm n).2.2.1 z
        have h2c := (hcutadm n).2.2.2.1 z
        have hUnn : (0:ℝ) ≤ Work.FTS.EllipticEst.AngAWeak.sgU u z := hsUnn z
        rw [Real.norm_eq_abs]
        have hsplit : |Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2
              * Work.FTS.EllipticEst.AngAWeak.sgU u z|
            = Work.FTS.EllipticEst.cut n z
                * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
          rw [abs_mul, abs_mul, abs_of_nonneg h1c, abs_of_nonneg hWz, abs_of_nonneg hUnn]
          ring
        rw [hsplit, abs_mul, abs_of_nonneg hWz, abs_of_nonneg hUnn]
        nlinarith [hUnn, hWz, h1c, h2c, mul_nonneg hWz hUnn]
      · filter_upwards [hWlim] with z hz
        have h := hz.mul_const ((Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        simpa only [one_mul, mul_assoc] using h
    have hsgU : MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) Work.Spaces.Iz := by
      refine MeasureTheory.Integrable.mono' hIU
        (Work.FTS.EllipticEst.AngAWeak.AeMain.P_aesm hAe) ?_
      filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
      have h1 : (0:ℝ) ≤ ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 := hsUnn z
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact le_mul_of_one_le_left h1 (by
        have h := Work.FTS.EllipticEst.Dispatch.one_le_w_D hz
        nlinarith)
    have herr := Work.FTS.EllipticEst.H2W.AeProof.AeCutErr
      (Work.FTS.EllipticEst.AngAWeak.sgU u) hsUnn
      (Work.FTS.EllipticEst.AngAWeak.AeMain.P_aesm hAe) hsgU hIU
    have hXnn : ∀ n : ℕ, 0 ≤ (∫ z in Work.Spaces.Iz, (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
          * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
          + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
          * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
      intro n
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards with z
      exact mul_nonneg (by positivity) (hsUnn z)
    have hYnn2 : ∀ n : ℕ, 0 ≤ (∫ z in Work.Spaces.Iz,
          |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)
            * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
      intro n
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [Work.FTS.EllipticEst.Honest.ae_pos_of_mem_Iz] with z hz
      exact mul_nonneg (mul_nonneg (abs_nonneg _) (by
        exact mul_nonneg (le_of_lt hz) (hWnn z))) (hsUnn z)
    have h3 : Filter.Tendsto (fun n : ℕ => (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
          (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
            * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
              * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
            |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)
              * Work.FTS.EllipticEst.AngAWeak.sgU u z))
        Filter.atTop (nhds 0) := by
      have hc1 : (0:ℝ) ≤ α ^ 2 / 2 := by positivity
      have hc2 : (0:ℝ) ≤ α * (5 + α) / 2 := by nlinarith [hα, hα4]
      have hCmax : (0:ℝ) ≤ max (α ^ 2 / 2) (α * (5 + α) / 2) :=
        le_max_of_le_left hc1
      refine squeeze_zero (fun n => add_nonneg (mul_nonneg hc1 (hXnn n))
          (mul_nonneg hc2 (hYnn2 n))) (fun n => ?_)
        (by
          have := herr.const_mul (max (α ^ 2 / 2) (α * (5 + α) / 2))
          simpa using this)
      have hxm := hXnn n
      have hym := hYnn2 n
      have hb1 : α ^ 2 / 2 * (∫ z in Work.Spaces.Iz, (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
            * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
            + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)
          ≤ max (α ^ 2 / 2) (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
            (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
              + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2))
              * Work.FTS.EllipticEst.AngAWeak.sgU u z) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hxm
      have hb2 : α * (5 + α) / 2 * (∫ z in Work.Spaces.Iz,
            |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)
              * Work.FTS.EllipticEst.AngAWeak.sgU u z)
          ≤ max (α ^ 2 / 2) (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
            |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2)
              * Work.FTS.EllipticEst.AngAWeak.sgU u z) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hym
      nlinarith [hb1, hb2]
    have hconv : Filter.Tendsto Bd Filter.atTop (nhds (∫ z in Work.Spaces.Iz, Z z)) := by
      have hZval : (∫ z in Work.Spaces.Iz, Z z)
          = (1 / 2) * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
                * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
            + (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
              * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
                * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
        have hsplit : (∫ z in Work.Spaces.Iz, Z z)
            = (∫ z in Work.Spaces.Iz, (1 / 2) * ((Work.Spaces.w z) ^ 2
                  * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
              + (∫ z in Work.Spaces.Iz, (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
                  * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z)) := by
          have hcongr : (∫ z in Work.Spaces.Iz, Z z)
              = ∫ z in Work.Spaces.Iz, (1 / 2) * ((Work.Spaces.w z) ^ 2
                    * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
                + (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
                  * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
            simp only [Z]
          rw [hcongr, MeasureTheory.integral_add
            ((Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta (α := α) (f := G)
              hmemG).1.const_mul (1 / 2)) (hIU.const_mul _)]
        rw [hsplit, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [hZval]
      simpa only [Bd, add_zero] using ((h1.const_mul (1 / 2)).add
        (h2.const_mul (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α)))).add h3
    obtain ⟨hYint', hYle⟩ := Work.FTS.EllipticEst.AngAWeak.integral_le_of_cutoff_tendsto
      hA0 hYnn hYasm (fun n z => (hcutadm n).2.2.1 z) hWlim hconv hWint hbound
    -- ### the arithmetic
    have hZval : (∫ z in Work.Spaces.Iz, Z z)
        = (1 / 2) * Work.Spaces.HkSq α 0 G
          + (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
            * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
              * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
      have hsplit : (∫ z in Work.Spaces.Iz, Z z)
          = (1 / 2) * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
                * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
            + (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
              * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
                * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
        have hcongr : (∫ z in Work.Spaces.Iz, Z z)
            = ∫ z in Work.Spaces.Iz, (1 / 2) * ((Work.Spaces.w z) ^ 2
                  * (∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
                + (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
                  * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
          simp only [Z]
        rw [hcongr, MeasureTheory.integral_add
          ((Work.FTS.EllipticEst.AngAWeak.integrableOn_wSq_sliceSq_sEta (α := α) (f := G)
            hmemG).1.const_mul (1 / 2)) (hIU.const_mul _)]
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [hsplit, hIGval]
    have hYge : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgY u z) ≤ ∫ z in Work.Spaces.Iz, Y z :=
      Work.FTS.EllipticEst.Honest.setIntegral_le_of_ae_le_of_nonneg
        (Filter.Eventually.of_forall fun z => by
          simp only [Y]
          have h1 := hsPnn z
          have h2 : (0:ℝ) ≤ α ^ 2 := sq_nonneg α
          have h3 : (0:ℝ) ≤ z ^ 2 := sq_nonneg z
          have h4 : (0:ℝ) ≤ (Work.Spaces.w z) ^ 2 := hWnn z
          nlinarith [mul_nonneg h2 (mul_nonneg (mul_nonneg h4 h3) h1)])
        (Filter.Eventually.of_forall hYnn) hYint
    have h9 : 9 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgY u z := by
      have hmono := MeasureTheory.integral_mono_ae (hIU.const_mul 9) hIntY
        (by
          filter_upwards [hgap] with z hz
          have hw := hWnn z
          nlinarith [hz, hw])
      rw [MeasureTheory.integral_const_mul] at hmono
      exact hmono
    have hMle : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        ≤ (1 / 9) * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgY u z) := by linarith [h9]
    have hKle : 13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α) ≤ 277 / 32 := by
      nlinarith [hα, hα4]
    have hstep1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgY u z)
        ≤ (1 / 2) * Work.Spaces.HkSq α 0 G
          + (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
            * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
              * Work.FTS.EllipticEst.AngAWeak.sgU u z) := by
      calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgY u z) ≤ ∫ z in Work.Spaces.Iz, Y z := hYge
        _ ≤ ∫ z in Work.Spaces.Iz, Z z := hYle
        _ = _ := hZval
    have hstep2 : (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α))
          * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgU u z)
        ≤ ((13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α)) / 9)
          * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgY u z) := by
      have hc : (0:ℝ) ≤ 13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α) := by nlinarith [hα, hα4]
      nlinarith [hMle, hc]
    have hK9 : (11:ℝ) / 288 ≤ 1 - (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α)) / 9 := by
      nlinarith [hKle]
    have hstep3 : (1 - (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α)) / 9)
          * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgY u z)
        ≤ (1 / 2) * Work.Spaces.HkSq α 0 G := by linarith [hstep1, hstep2]
    have hfin : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * Work.FTS.EllipticEst.AngAWeak.sgY u z)
        ≤ (144 / 11) * Work.Spaces.HkSq α 0 G := by
      have hpos : (0:ℝ) < 1 - (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α)) / 9 := by
        nlinarith [hK9]
      have h2 : (1 / 2) * Work.Spaces.HkSq α 0 G
            / (1 - (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α)) / 9)
          ≤ (144 / 11) * Work.Spaces.HkSq α 0 G := by
        rw [div_le_iff₀ hpos]
        have hH := Work.Spaces.HkSq_nonneg α 0 G
        nlinarith [hK9, hH]
      calc (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * Work.FTS.EllipticEst.AngAWeak.sgY u z)
          = (1 - (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α)) / 9)
              * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
                * Work.FTS.EllipticEst.AngAWeak.sgY u z)
              / (1 - (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α)) / 9) := by
            rw [mul_div_cancel_left₀ _ (ne_of_gt hpos)]
        _ ≤ ((1 / 2) * Work.Spaces.HkSq α 0 G)
              / (1 - (13 / 2 + 3 * α ^ 2 + (3 / 2) * α * (5 + α)) / 9) :=
            div_le_div_of_nonneg_right hstep3 (le_of_lt hpos)
        _ ≤ _ := h2
    refine le_trans hfin ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 144 / 11)
    exact le_add_of_nonneg_right
      (mul_nonneg (sq_nonneg α) (Work.Spaces.HkSq_nonneg _ _ _))
  · -- ### the junk case
    rw [MeasureTheory.integral_undef hIntY]
    have h1 : 0 ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
    have h2 : 0 ≤ α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
      mul_nonneg (sq_nonneg α) (Work.Spaces.HkSq_nonneg _ _ _)
    nlinarith [h1, h2]

end Work.FTS.EllipticEst.Cores.Pieces