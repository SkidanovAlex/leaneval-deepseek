import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.KMinus_slash_cusp_ball
import Submission.Work.Asymptotics.MFix.KMinusCuspBall
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.ZAtomsThird.first_order
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Residues.KMinusClear_T
import Submission.Work.Residues.KMinusCuspDefs

set_option maxHeartbeats 4000000

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

noncomputable section

open Work.Kernels

/-! ## Two elementary tools

1. A continuous function on `ℍ` is bounded on any closed box `{a ≤ Re ≤ b, c ≤ Im ≤ d}` with
   `c > 0` (compactness).
2. A holomorphic function on `ℍ` which is periodic with positive period and bounded at `i∞` is
   bounded on every half plane `{a ≤ Im}` (`Work.Rigidity.bounded_on_lt_im_of_periodic`).  We
   also record the (easy) bridge between the `vadd`-form and the `ofComplex`-form of periodicity.
-/

lemma exists_bound_box {f : ℍ → ℂ} (hf : Continuous f) {a b c d : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℍ, a ≤ w.re → w.re ≤ b → c ≤ w.im → w.im ≤ d → ‖f w‖ ≤ C := by
  have hTcomp : IsCompact {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d} := by
    have hcl : IsClosed {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d} := by
      have h1 : IsClosed {w : ℂ | a ≤ w.re} := isClosed_le continuous_const Complex.continuous_re
      have h2 : IsClosed {w : ℂ | w.re ≤ b} := isClosed_le Complex.continuous_re continuous_const
      have h3 : IsClosed {w : ℂ | c ≤ w.im} := isClosed_le continuous_const Complex.continuous_im
      have h4 : IsClosed {w : ℂ | w.im ≤ d} := isClosed_le Complex.continuous_im continuous_const
      have hset : {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d}
          = {w : ℂ | a ≤ w.re} ∩ {w : ℂ | w.re ≤ b} ∩ {w : ℂ | c ≤ w.im}
            ∩ {w : ℂ | w.im ≤ d} := by
        ext w; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
      rw [hset]; exact ((h1.inter h2).inter h3).inter h4
    have hbdd : Bornology.IsBounded {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d} := by
      refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ))
        (r := |a| + |b| + |c| + |d| + 1)) ?_
      intro w hw
      obtain ⟨ha, hb, hc', hd⟩ := hw
      rw [Metric.mem_closedBall, dist_zero_right]
      have hre : |w.re| ≤ |a| + |b| :=
        le_trans (abs_le_max_abs_abs ha hb) (by
          rcases le_total |a| |b| with h | h
          · rw [max_eq_right h]; linarith [abs_nonneg a]
          · rw [max_eq_left h]; linarith [abs_nonneg b])
      have him : |w.im| ≤ |c| + |d| :=
        le_trans (abs_le_max_abs_abs hc' hd) (by
          rcases le_total |c| |d| with h | h
          · rw [max_eq_right h]; linarith [abs_nonneg c]
          · rw [max_eq_left h]; linarith [abs_nonneg d])
      have hre2 : w.re ^ 2 ≤ (|a| + |b|) ^ 2 := by
        have h := abs_le.mp hre
        nlinarith [h.1, h.2, abs_nonneg a, abs_nonneg b]
      have him2 : w.im ^ 2 ≤ (|c| + |d|) ^ 2 := by
        have h := abs_le.mp him
        nlinarith [h.1, h.2, abs_nonneg c, abs_nonneg d]
      have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have hR : (0 : ℝ) ≤ |a| + |b| + |c| + |d| + 1 := by positivity
      have h2 : ‖w‖ ^ 2 ≤ (|a| + |b| + |c| + |d| + 1) ^ 2 := by
        nlinarith [hsq, hre2, him2, abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg d]
      calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
        _ ≤ Real.sqrt ((|a| + |b| + |c| + |d| + 1) ^ 2) := Real.sqrt_le_sqrt h2
        _ = |a| + |b| + |c| + |d| + 1 := Real.sqrt_sq hR
    exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hcl, hbdd⟩
  have himg : ((↑) : ℍ → ℂ) ''
      (((↑) : ℍ → ℂ) ⁻¹' {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d})
      = {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d} := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hw
      exact ⟨⟨w, lt_of_lt_of_le hc hw.2.2.1⟩, hw, rfl⟩
  have hK : IsCompact
      (((↑) : ℍ → ℂ) ⁻¹' {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d}) := by
    rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff, himg]
    exact hTcomp
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun w ha hb hc' hd => ?_⟩
  exact le_trans (hC w ⟨ha, hb, hc', hd⟩) (le_max_left _ _)

/-- Bridge from the `vadd`-form of periodicity to the `ofComplex`-form used by
`Work.Rigidity.bounded_on_lt_im_of_periodic`. -/
lemma periodic_comp_ofComplex_of_vadd {F : ℍ → ℂ} {h : ℝ} (_hh : 0 < h)
    (hper : ∀ τ : ℍ, F (h +ᵥ τ) = F τ) :
    Function.Periodic (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) h := by
  intro w
  rcases lt_or_ge (0 : ℝ) w.im with hw | hw
  · have hw' : 0 < (w + (h : ℂ)).im := by
      rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hw
    have h1 : (UpperHalfPlane.ofComplex (w + (h : ℂ)) : ℍ)
        = h +ᵥ (UpperHalfPlane.ofComplex w : ℍ) := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw', UpperHalfPlane.ofComplex_apply_of_im_pos hw]
      apply UpperHalfPlane.ext
      rw [UpperHalfPlane.coe_vadd]
      push_cast
      ring
    show F (UpperHalfPlane.ofComplex (w + (h : ℂ))) = F (UpperHalfPlane.ofComplex w)
    rw [h1, hper]
  · have hw' : (w + (h : ℂ)).im ≤ 0 := by
      rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hw
    show F (UpperHalfPlane.ofComplex (w + (h : ℂ))) = F (UpperHalfPlane.ofComplex w)
    rw [UpperHalfPlane.ofComplex_apply_of_im_nonpos hw',
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw]

/-- A holomorphic function on `ℍ` with positive period `h`, bounded at `i∞`, is bounded on
`{Im ≥ a}` for every `a > 0`. -/
lemma bdd_of_periodic_vadd {F : ℍ → ℂ} {h a : ℝ} (hh : 0 < h) (ha : 0 < a)
    (hper : ∀ τ : ℍ, F (h +ᵥ τ) = F τ) (hfhol : MDiff F)
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) :
    ∃ M : ℝ, ∀ τ : ℍ, a ≤ τ.im → ‖F τ‖ ≤ M :=
  Work.Rigidity.bounded_on_lt_im_of_periodic hh ha
    (periodic_comp_ofComplex_of_vadd hh hper) hfhol hbdd

/-! ## The `z`-estimates on `{Im z ≥ 1/3}`

The atoms are `2`-periodic in `Re` (`U`, `W`, `V` and `𝓛_S` change sign under `z ↦ z+1`), so
`Work.Rigidity.bounded_on_lt_im_of_periodic` gives boundedness on `{Im ≥ 1/3}`; combined with the
cusp decay for `Im ≥ 1` this yields the rates `O(1)` for `U`, `W`, `E₄`, `E₆`, `E₁₀`, `E₁₄` and
`O(e^{-π Im})` for `V`, `𝓛_S`.
-/

private lemma vadd_two (τ : ℍ) : (2 : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd]
  push_cast
  ring

private lemma isBoundedAtImInfty_of_bound {F : ℍ → ℂ} {C H : ℝ}
    (h : ∀ τ : ℍ, H ≤ τ.im → ‖F τ‖ ≤ C) : UpperHalfPlane.IsBoundedAtImInfty F :=
  UpperHalfPlane.isBoundedAtImInfty_iff.mpr ⟨C, H, h⟩

private lemma bdd_third_of_period_two {F : ℍ → ℂ} (hper : ∀ τ : ℍ, F ((2 : ℝ) +ᵥ τ) = F τ)
    (hfhol : MDiff F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ : ℍ, (1 : ℝ) / 3 ≤ τ.im → ‖F τ‖ ≤ M := by
  obtain ⟨M, hM⟩ := bdd_of_periodic_vadd (show (0 : ℝ) < 2 by norm_num)
    (show (0 : ℝ) < 1 / 3 by norm_num) hper hfhol hbdd
  exact ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun τ hτ => le_trans (hM τ hτ) (le_max_left _ _)⟩

private lemma decay_third_of {F : ℍ → ℂ} {C M : ℝ} (hC : 0 < C) (hM : 0 < M)
    (h1 : ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-(Real.pi * τ.im)))
    (h2 : ∀ τ : ℍ, (1 : ℝ) / 3 ≤ τ.im → ‖F τ‖ ≤ M) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ τ : ℍ, (1 : ℝ) / 3 ≤ τ.im →
      ‖F τ‖ ≤ C' * Real.exp (-(Real.pi * τ.im)) := by
  refine ⟨max C (M * Real.exp Real.pi) + 1, by positivity, fun τ hτ => ?_⟩
  rcases lt_or_ge (1 : ℝ) τ.im with h | h
  · refine le_trans (h1 τ h.le) (mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _))
    linarith [le_max_left C (M * Real.exp Real.pi)]
  · have hE : Real.exp (-(Real.pi * τ.im)) * Real.exp Real.pi = Real.exp (Real.pi * (1 - τ.im)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hge : (1 : ℝ) ≤ Real.exp (-(Real.pi * τ.im)) * Real.exp Real.pi := by
      rw [hE]; exact Real.one_le_exp (by nlinarith [Real.pi_pos, h])
    have hle : M ≤ M * (Real.exp (-(Real.pi * τ.im)) * Real.exp Real.pi) := by
      nlinarith [hM.le, hge]
    calc ‖F τ‖ ≤ M := h2 τ hτ
      _ ≤ M * (Real.exp (-(Real.pi * τ.im)) * Real.exp Real.pi) := hle
      _ = M * Real.exp Real.pi * Real.exp (-(Real.pi * τ.im)) := by ring
      _ ≤ (max C (M * Real.exp Real.pi) + 1) * Real.exp (-(Real.pi * τ.im)) :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_right C (M * Real.exp Real.pi)])
            (Real.exp_nonneg _)

private lemma UFun_bdd_cusp_ab : UpperHalfPlane.IsBoundedAtImInfty UFun := by
  obtain ⟨C, hC, h⟩ := Work.Residues.UFun_decay
  refine isBoundedAtImInfty_of_bound (H := 1) (C := C + 1) fun τ hτ => ?_
  have h1 : Real.exp (-(Real.pi * τ.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hτ])
  have h2 := h τ hτ
  have h3 : C * Real.exp (-(Real.pi * τ.im)) ≤ C := by nlinarith [hC.le, h1]
  have h4 := norm_add_le (UFun τ - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at h4
  linarith

private lemma WFun_bdd_cusp_ab : UpperHalfPlane.IsBoundedAtImInfty WFun := by
  obtain ⟨C, hC, h⟩ := Work.Residues.WFun_decay
  refine isBoundedAtImInfty_of_bound (H := 1) (C := C + 1) fun τ hτ => ?_
  have h1 : Real.exp (-(Real.pi * τ.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hτ])
  have h2 := h τ hτ
  have h3 : C * Real.exp (-(Real.pi * τ.im)) ≤ C := by nlinarith [hC.le, h1]
  have h4 := norm_add_le (WFun τ - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at h4
  linarith

private lemma VFun_bdd_cusp_ab : UpperHalfPlane.IsBoundedAtImInfty VFun := by
  obtain ⟨C, hC, h⟩ := Work.Residues.VFun_decay
  refine isBoundedAtImInfty_of_bound (H := 1) (C := C + 1) fun τ hτ => ?_
  have h1 : Real.exp (-(Real.pi * τ.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hτ])
  have h2 := h τ hτ
  have h3 : C * Real.exp (-(Real.pi * τ.im)) ≤ C := by nlinarith [hC.le, h1]
  linarith

private lemma LS_bdd_cusp_ab (ℓ : Work.Kernels.LogLambdaData) :
    UpperHalfPlane.IsBoundedAtImInfty ℓ.L_S := by
  obtain ⟨C, hC, h⟩ := (Work.Residues.LogLambdaBound ℓ).2
  refine isBoundedAtImInfty_of_bound (H := 1) (C := C + 1) fun τ hτ => ?_
  have h1 : Real.exp (-(Real.pi * τ.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hτ])
  have h2 := h τ hτ
  have h3 : C * Real.exp (-(Real.pi * τ.im)) ≤ C := by nlinarith [hC.le, h1]
  linarith

private lemma UFun_bdd_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im → ‖UFun z‖ ≤ C :=
  bdd_third_of_period_two (fun τ => by rw [vadd_two, KernelFacts.UFun_vadd_one, KernelFacts.WFun_vadd_one])
    (show MDiff UFun from (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.pow 4).1) UFun_bdd_cusp_ab

private lemma WFun_bdd_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im → ‖WFun z‖ ≤ C :=
  bdd_third_of_period_two (fun τ => by rw [vadd_two, KernelFacts.WFun_vadd_one, KernelFacts.UFun_vadd_one])
    (show MDiff WFun from (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.pow 4).1) WFun_bdd_cusp_ab

private lemma VFun_bdd_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im → ‖VFun z‖ ≤ C :=
  bdd_third_of_period_two (fun τ => by rw [vadd_two, KernelFacts.VFun_vadd_one, KernelFacts.VFun_vadd_one, neg_neg])
    (show MDiff VFun from (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.pow 4).1) VFun_bdd_cusp_ab

private lemma LS_bdd_third (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im → ‖ℓ.L_S z‖ ≤ C :=
  bdd_third_of_period_two (fun τ => by rw [vadd_two, KernelFacts.L_S_vadd_one ℓ, KernelFacts.L_S_vadd_one ℓ, neg_neg])
    ℓ.holo_S (LS_bdd_cusp_ab ℓ)

private lemma VFun_decay_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im →
    ‖VFun z‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨C, hC, h⟩ := Work.Residues.VFun_decay
  obtain ⟨M, hM, hM'⟩ := VFun_bdd_third
  exact decay_third_of hC hM h hM'

private lemma LS_decay_third (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im →
      ‖ℓ.L_S z‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨C, hC, h⟩ := (Work.Residues.LogLambdaBound ℓ).2
  obtain ⟨M, hM, hM'⟩ := LS_bdd_third ℓ
  exact decay_third_of hC hM h hM'

/-- `‖q(z)‖ = e^{-2π Im z}`. -/
private lemma norm_qParam (z : ℍ) :
    ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * z.im)) := norm_qParamFun z

private lemma E4Fun_bdd_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im → ‖E4Fun z‖ ≤ C := by
  obtain ⟨C, hC, -, h4, -⟩ := ZAtomsThird.first_order
  refine ⟨C + 1, by positivity, fun z hz => ?_⟩
  have hq : ‖Work.Kernels.qParamFun z‖ ≤ 1 := le_trans (norm_qParam_le_third hz) (by norm_num)
  have h1 := h4 z hz
  have h2 : ‖E4Fun z - 1‖ ≤ C := by
    calc ‖E4Fun z - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖ := h1
      _ ≤ C * 1 := by nlinarith [hq, hC.le]
      _ = C := by ring
  have h3 : E4Fun z = (E4Fun z - 1) + 1 := by ring
  rw [h3]
  have h4 := norm_add_le (E4Fun z - 1) (1 : ℂ)
  rw [norm_one] at h4
  linarith

private lemma E6Fun_bdd_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im → ‖E6Fun z‖ ≤ C := by
  obtain ⟨C, hC, -, -, h6, -⟩ := ZAtomsThird.first_order
  refine ⟨C + 1, by positivity, fun z hz => ?_⟩
  have hq : ‖Work.Kernels.qParamFun z‖ ≤ 1 := le_trans (norm_qParam_le_third hz) (by norm_num)
  have h1 := h6 z hz
  have h2 : ‖E6Fun z - 1‖ ≤ C := by
    calc ‖E6Fun z - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖ := h1
      _ ≤ C * 1 := by nlinarith [hq, hC.le]
      _ = C := by ring
  have h3 : E6Fun z = (E6Fun z - 1) + 1 := by ring
  rw [h3]
  have h4 := norm_add_le (E6Fun z - 1) (1 : ℂ)
  rw [norm_one] at h4
  linarith

private lemma DeltaFun_lower_third :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im →
      c * Real.exp (-(2 * Real.pi * z.im)) ≤ ‖DeltaFun z‖ := by
  obtain ⟨c, hc, h⟩ := delta_lower_third
  exact ⟨c, hc, fun z hz => by rw [← norm_qParam z]; exact h z hz⟩

private lemma DeltaFun_upper_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im →
      ‖DeltaFun z‖ ≤ C * Real.exp (-(2 * Real.pi * z.im)) := by
  obtain ⟨C, hC, h⟩ := delta_upper_third
  exact ⟨C, hC, fun z hz => by rw [← norm_qParam z]; exact h z hz⟩

/-! ## The `τ`-estimates on the funnel `τ ∈ 𝒟`, `Im τ ≥ 1/2` -/

private lemma bdd_half_of_period_two {F : ℍ → ℂ} (hper : ∀ τ : ℍ, F ((2 : ℝ) +ᵥ τ) = F τ)
    (hfhol : MDiff F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ : ℍ, (1 : ℝ) / 2 ≤ τ.im → ‖F τ‖ ≤ M := by
  obtain ⟨M, hM⟩ := bdd_of_periodic_vadd (show (0 : ℝ) < 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) hper hfhol hbdd
  exact ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _),
    fun τ hτ => le_trans (hM τ hτ) (le_max_left _ _)⟩

private lemma decay_of_bdd_and_decay {F : ℍ → ℂ} {a C M : ℝ} (hC : 0 < C) (hM : 0 < M)
    (h1 : ∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-(Real.pi * τ.im)))
    (h2 : ∀ τ : ℍ, a ≤ τ.im → ‖F τ‖ ≤ M) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ τ : ℍ, a ≤ τ.im → ‖F τ‖ ≤ C' * Real.exp (-(Real.pi * τ.im)) := by
  refine ⟨max C (M * Real.exp Real.pi) + 1, by positivity, fun τ hτ => ?_⟩
  rcases lt_or_ge (1 : ℝ) τ.im with h | h
  · refine le_trans (h1 τ h.le) (mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _))
    linarith [le_max_left C (M * Real.exp Real.pi)]
  · have hE : Real.exp (-(Real.pi * τ.im)) * Real.exp Real.pi = Real.exp (Real.pi * (1 - τ.im)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hge : (1 : ℝ) ≤ Real.exp (-(Real.pi * τ.im)) * Real.exp Real.pi := by
      rw [hE]; exact Real.one_le_exp (by nlinarith [Real.pi_pos, h])
    have hle : M ≤ M * (Real.exp (-(Real.pi * τ.im)) * Real.exp Real.pi) := by
      nlinarith [hM.le, hge]
    calc ‖F τ‖ ≤ M := h2 τ hτ
      _ ≤ M * (Real.exp (-(Real.pi * τ.im)) * Real.exp Real.pi) := hle
      _ = M * Real.exp Real.pi * Real.exp (-(Real.pi * τ.im)) := by ring
      _ ≤ (max C (M * Real.exp Real.pi) + 1) * Real.exp (-(Real.pi * τ.im)) :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_right C (M * Real.exp Real.pi)])
            (Real.exp_nonneg _)

/-- `U`, `W` are bounded on `{Im ≥ 1/2}`. -/
private lemma UFun_bdd_half : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (1 : ℝ) / 2 ≤ τ.im → ‖UFun τ‖ ≤ C :=
  bdd_half_of_period_two (fun τ => by rw [vadd_two, KernelFacts.UFun_vadd_one, KernelFacts.WFun_vadd_one])
    (show MDiff UFun from (Work.Kernels.ClassicalFacts.theta00Fun_mem_InP.pow 4).1) UFun_bdd_cusp_ab

private lemma WFun_bdd_half : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (1 : ℝ) / 2 ≤ τ.im → ‖WFun τ‖ ≤ C :=
  bdd_half_of_period_two (fun τ => by rw [vadd_two, KernelFacts.WFun_vadd_one, KernelFacts.UFun_vadd_one])
    (show MDiff WFun from (Work.Kernels.ClassicalFacts.theta01Fun_mem_InP.pow 4).1) WFun_bdd_cusp_ab

private lemma VFun_decay_half : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (1 : ℝ) / 2 ≤ τ.im →
    ‖VFun τ‖ ≤ C * Real.exp (-(Real.pi * τ.im)) := by
  obtain ⟨M, hM, hM'⟩ := bdd_half_of_period_two
    (fun τ => by rw [vadd_two, KernelFacts.VFun_vadd_one, KernelFacts.VFun_vadd_one, neg_neg])
    (show MDiff VFun from (Work.Kernels.ClassicalFacts.theta10Fun_mem_InP.pow 4).1) VFun_bdd_cusp_ab
  obtain ⟨C, hC, h⟩ := Work.Residues.VFun_decay
  exact decay_of_bdd_and_decay hC hM h hM'

private lemma LS_decay_half (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (1 : ℝ) / 2 ≤ τ.im →
      ‖ℓ.L_S τ‖ ≤ C * Real.exp (-(Real.pi * τ.im)) := by
  obtain ⟨M, hM, hM'⟩ := bdd_half_of_period_two
    (fun τ => by rw [vadd_two, KernelFacts.L_S_vadd_one ℓ, KernelFacts.L_S_vadd_one ℓ, neg_neg])
    ℓ.holo_S (LS_bdd_cusp_ab ℓ)
  obtain ⟨C, hC, h⟩ := (Work.Residues.LogLambdaBound ℓ).2
  exact decay_of_bdd_and_decay hC hM h hM'

/-- `𝓛` has at most linear growth on the funnel. -/
private lemma L_bdd_half (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ DomainD → (1 : ℝ) / 2 ≤ τ.im →
      ‖ℓ.L τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) := by
  obtain ⟨C₁, hC₁, h₁⟩ := (Work.Residues.LogLambdaBound ℓ).1
  obtain ⟨C₂, hC₂, h₂⟩ := exists_bound_box (f := fun τ : ℍ => ℓ.L τ) ℓ.holo.continuous
    (a := -1) (b := 1) (c := 1 / 2) (d := 1) (by norm_num)
  refine ⟨max (C₁ + Real.pi) C₂ + 1, by positivity, fun τ hτ hτim => ?_⟩
  rcases lt_or_ge (1 : ℝ) τ.im with h | h
  · -- large imaginary part: `𝓛 = πiτ + O(1)`
    have h₃ := h₁ τ h.le
    have hπ : ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ = Real.pi * ‖(τ : ℂ)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one]
      congr 1
      rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hsplit : ℓ.L τ = (ℓ.L τ - (Real.pi : ℂ) * Complex.I * (τ : ℂ))
        + (Real.pi : ℂ) * Complex.I * (τ : ℂ) := by ring
    rw [hsplit]
    calc ‖(ℓ.L τ - (Real.pi : ℂ) * Complex.I * (τ : ℂ))
          + (Real.pi : ℂ) * Complex.I * (τ : ℂ)‖
        ≤ ‖ℓ.L τ - (Real.pi : ℂ) * Complex.I * (τ : ℂ)‖
          + ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ := norm_add_le _ _
      _ ≤ C₁ + Real.pi * ‖(τ : ℂ)‖ := by rw [hπ]; linarith
      _ ≤ (C₁ + Real.pi) * (1 + ‖(τ : ℂ)‖) := by
          nlinarith [norm_nonneg (τ : ℂ), hC₁.le, Real.pi_pos]
      _ ≤ (max (C₁ + Real.pi) C₂ + 1) * (1 + ‖(τ : ℂ)‖) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith [le_max_left (C₁ + Real.pi) C₂]
  · -- bounded region
    have hre := (mem_DomainD.mp hτ).1
    have hre' := (mem_DomainD.mp hτ).2.1
    have h₃ : ‖ℓ.L τ‖ ≤ C₂ := h₂ τ (by linarith) (le_of_lt hre') hτim (by linarith)
    have h4 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
      have := norm_nonneg (τ : ℂ); linarith
    have h5 : C₂ ≤ C₂ * (1 + ‖(τ : ℂ)‖) := by nlinarith [hC₂, norm_nonneg (τ : ℂ), h4]
    have h6 : C₂ * (1 + ‖(τ : ℂ)‖) ≤ (max (C₁ + Real.pi) C₂ + 1) * (1 + ‖(τ : ℂ)‖) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith [le_max_right (C₁ + Real.pi) C₂]
    linarith

private lemma E4Fun_bdd_half : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (1 : ℝ) / 2 ≤ τ.im → ‖E4Fun τ‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := E4Fun_bdd_third
  exact ⟨C, hC, fun τ hτ => h τ (by linarith)⟩

private lemma psi2_bdd_half (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ DomainD → (1 : ℝ) / 2 ≤ τ.im →
      ‖psi2 ℓ τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) := by
  obtain ⟨CU, hCU, hU⟩ := UFun_bdd_half
  obtain ⟨CW, hCW, hW⟩ := WFun_bdd_half
  obtain ⟨CV, hCV, hV⟩ := VFun_decay_half
  obtain ⟨CL, hCL, hL⟩ := L_bdd_half ℓ
  obtain ⟨CS, hCS, hS⟩ := LS_decay_half ℓ
  refine ⟨CL * (CU + CW) + CS * (CU + CV) + 1, by positivity, fun τ hτ hτim => ?_⟩
  have hxm : (xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ = -(UFun τ + VFun τ) :=
    congr_fun Work.Residues.XiSlashS.1 τ
  have h₁ : ‖xi2Fun τ‖ ≤ CU + CW := by
    have h : xi2Fun τ = UFun τ + WFun τ := rfl
    rw [h]; exact le_trans (norm_add_le _ _) (add_le_add (hU τ hτim) (hW τ hτim))
  have h₂ : ‖(xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ‖ ≤ CU + CV := by
    rw [hxm, norm_neg]
    refine le_trans (norm_add_le _ _) ?_
    have hVe : ‖VFun τ‖ ≤ CV := by
      have h1 := hV τ hτim
      have h2 : Real.exp (-(Real.pi * τ.im)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, τ.im_pos])
      calc ‖VFun τ‖ ≤ CV * Real.exp (-(Real.pi * τ.im)) := h1
        _ ≤ CV * 1 := by nlinarith [hCV.le, h2]
        _ = CV := by ring
    linarith [hU τ hτim, hVe]
  have hS1 : ‖ℓ.L_S τ‖ ≤ CS := by
    have h1 := hS τ hτim
    have h2 : Real.exp (-(Real.pi * τ.im)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, τ.im_pos])
    calc ‖ℓ.L_S τ‖ ≤ CS * Real.exp (-(Real.pi * τ.im)) := h1
      _ ≤ CS * 1 := by nlinarith [hCS.le, h2]
      _ = CS := by ring
  have hmain : psi2 ℓ τ = xi2Fun τ * ℓ.L τ + (xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
  rw [hmain]
  have h3 : ‖xi2Fun τ * ℓ.L τ‖ ≤ (CU + CW) * (CL * (1 + ‖(τ : ℂ)‖)) := by
    rw [norm_mul]
    exact mul_le_mul h₁ (hL τ hτ hτim) (norm_nonneg _) (by positivity)
  have h4 : ‖(xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ‖ ≤ (CU + CV) * CS := by
    rw [norm_mul]
    exact mul_le_mul h₂ hS1 (norm_nonneg _) (by positivity)
  have h5 : (CU + CV) * CS ≤ (CU + CV) * CS * (1 + ‖(τ : ℂ)‖) := by
    have h6 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
      have := norm_nonneg (τ : ℂ); linarith
    nlinarith [h6, mul_nonneg (by positivity : (0:ℝ) ≤ CU + CV) hCS.le]
  calc ‖xi2Fun τ * ℓ.L τ + (xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ‖
      ≤ ‖xi2Fun τ * ℓ.L τ‖ + ‖(xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ‖ := norm_add_le _ _
    _ ≤ (CU + CW) * (CL * (1 + ‖(τ : ℂ)‖)) + (CU + CV) * CS := add_le_add h3 h4
    _ ≤ (CL * (CU + CW) + CS * (CU + CV) + 1) * (1 + ‖(τ : ℂ)‖) := by
        nlinarith [h5, norm_nonneg (τ : ℂ), hCL.le, hCS.le, hCU.le, hCW.le, hCV.le]

private lemma psi4_bdd_half (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ DomainD → (1 : ℝ) / 2 ≤ τ.im →
      ‖psi4 ℓ τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) := by
  obtain ⟨CU, hCU, hU⟩ := UFun_bdd_half
  obtain ⟨CW, hCW, hW⟩ := WFun_bdd_half
  obtain ⟨CV, hCV, hV⟩ := VFun_decay_half
  obtain ⟨CL, hCL, hL⟩ := L_bdd_half ℓ
  obtain ⟨CS, hCS, hS⟩ := LS_decay_half ℓ
  have hCV1 : 0 < CV := hCV
  refine ⟨CL * (CU ^ 2 + CW ^ 2 + 2 * CV ^ 2) + CS * (CU ^ 2 + CV ^ 2 + 2 * CW ^ 2) + 1,
    by positivity, fun τ hτ hτim => ?_⟩
  have hxm : (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ
      = UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2 := congr_fun Work.Residues.XiSlashS.2 τ
  have hV1 : ‖VFun τ‖ ≤ CV := by
    have h1 := hV τ hτim
    have h2 : Real.exp (-(Real.pi * τ.im)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, τ.im_pos])
    calc ‖VFun τ‖ ≤ CV * Real.exp (-(Real.pi * τ.im)) := h1
      _ ≤ CV * 1 := by nlinarith [hCV.le, h2]
      _ = CV := by ring
  have h₁ : ‖xi4Fun τ‖ ≤ CU ^ 2 + CW ^ 2 + 2 * CV ^ 2 := by
    have h : xi4Fun τ = UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2 := rfl
    rw [h]
    have h2 : ‖UFun τ ^ 2‖ ≤ CU ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hU τ hτim) 2
    have h3 : ‖WFun τ ^ 2‖ ≤ CW ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hW τ hτim) 2
    have h4 : ‖(2 : ℂ) * VFun τ ^ 2‖ ≤ 2 * CV ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hV1 2) (by norm_num)
    have h5 := norm_sub_le (UFun τ ^ 2 + WFun τ ^ 2) (2 * VFun τ ^ 2)
    have h6 : ‖UFun τ ^ 2 + WFun τ ^ 2‖ ≤ CU ^ 2 + CW ^ 2 :=
      le_trans (norm_add_le _ _) (add_le_add h2 h3)
    linarith
  have h₂ : ‖(xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ‖
      ≤ CU ^ 2 + CV ^ 2 + 2 * CW ^ 2 := by
    rw [hxm]
    have h2 : ‖UFun τ ^ 2‖ ≤ CU ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hU τ hτim) 2
    have h3 : ‖VFun τ ^ 2‖ ≤ CV ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hV1 2
    have h4 : ‖(2 : ℂ) * WFun τ ^ 2‖ ≤ 2 * CW ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hW τ hτim) 2) (by norm_num)
    have h5 := norm_sub_le (UFun τ ^ 2 + VFun τ ^ 2) (2 * WFun τ ^ 2)
    have h6 : ‖UFun τ ^ 2 + VFun τ ^ 2‖ ≤ CU ^ 2 + CV ^ 2 :=
      le_trans (norm_add_le _ _) (add_le_add h2 h3)
    linarith
  have hS1 : ‖ℓ.L_S τ‖ ≤ CS := by
    have h1 := hS τ hτim
    have h2 : Real.exp (-(Real.pi * τ.im)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, τ.im_pos])
    calc ‖ℓ.L_S τ‖ ≤ CS * Real.exp (-(Real.pi * τ.im)) := h1
      _ ≤ CS * 1 := by nlinarith [hCS.le, h2]
      _ = CS := by ring
  have hmain : psi4 ℓ τ = xi4Fun τ * ℓ.L τ + (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ := rfl
  rw [hmain]
  have h3 : ‖xi4Fun τ * ℓ.L τ‖ ≤ (CU ^ 2 + CW ^ 2 + 2 * CV ^ 2) * (CL * (1 + ‖(τ : ℂ)‖)) := by
    rw [norm_mul]
    exact mul_le_mul h₁ (hL τ hτ hτim) (norm_nonneg _) (by positivity)
  have h4 : ‖(xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ‖ ≤ (CU ^ 2 + CV ^ 2 + 2 * CW ^ 2) * CS := by
    rw [norm_mul]
    exact mul_le_mul h₂ hS1 (norm_nonneg _) (by positivity)
  have h5 : (CU ^ 2 + CV ^ 2 + 2 * CW ^ 2) * CS
      ≤ (CU ^ 2 + CV ^ 2 + 2 * CW ^ 2) * CS * (1 + ‖(τ : ℂ)‖) := by
    have h6 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
      have := norm_nonneg (τ : ℂ); linarith
    nlinarith [h6, mul_nonneg (by positivity : (0:ℝ) ≤ CU ^ 2 + CV ^ 2 + 2 * CW ^ 2) hCS.le]
  calc ‖xi4Fun τ * ℓ.L τ + (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ‖
      ≤ ‖xi4Fun τ * ℓ.L τ‖ + ‖(xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * ℓ.L_S τ‖ := norm_add_le _ _
    _ ≤ (CU ^ 2 + CW ^ 2 + 2 * CV ^ 2) * (CL * (1 + ‖(τ : ℂ)‖))
          + (CU ^ 2 + CV ^ 2 + 2 * CW ^ 2) * CS := add_le_add h3 h4
    _ ≤ (CL * (CU ^ 2 + CW ^ 2 + 2 * CV ^ 2) + CS * (CU ^ 2 + CV ^ 2 + 2 * CW ^ 2) + 1)
          * (1 + ‖(τ : ℂ)‖) := by
        nlinarith [h5, norm_nonneg (τ : ℂ), hCL.le, hCS.le, hCU.le, hCW.le, hCV1.le]

/-! ## The key cancellation for `E₆ψ₂ - E₄ψ₄`

Writing `ψ₂ = ξ₂𝓛 + (ξ₂|S)𝓛_S` and `ψ₄ = ξ₄𝓛 + (ξ₄|S)𝓛_S`, the combination
`E₆ψ₂ - E₄ψ₄ = Θ𝓛 + Θ'𝓛_S` has coefficients

  `Θ = E₆ξ₂ - E₄ξ₄ = -(9/2) U W V²`,   `Θ' = E₆(ξ₂|S) - E₄(ξ₄|S) = -(9/2) U W² V`,

which vanish at the cusp: `Θ` is `O(e^{-2π Im})` and `Θ'` is `O(e^{-π Im})`.  Since `𝓛` grows at
most linearly and `𝓛_S = O(e^{-π Im})`, the combination is `O((1+‖τ‖) e^{-2π Im})`.
-/

private lemma nmul2 {a b : ℂ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a * b‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) hA

private lemma nmul3 {a b c : ℂ} {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) : ‖a * b * c‖ ≤ A * B * C := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hA) hc (norm_nonneg _) (mul_nonneg hA hB)

private lemma nmul4 {a b c d : ℂ} {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) :
    ‖a * b * c * d‖ ≤ A * B * C * D := by
  have h3 := nmul3 (a := a) (b := b) (c := c) hA hB hC ha hb hc
  rw [norm_mul]
  exact mul_le_mul h3 hd (norm_nonneg _) (by positivity)

private lemma theta_identity_one (τ : ℍ) :
    E6Fun τ * (UFun τ + WFun τ) - E4Fun τ * (UFun τ ^ 2 + WFun τ ^ 2 - 2 * VFun τ ^ 2)
      = -(9 / 2 : ℂ) * (UFun τ * WFun τ * VFun τ ^ 2) := by
  rw [Work.Residues.KMinusT_E4Fun_eq_theta τ, Work.Residues.KMinusT_E6Fun_eq_theta τ,
    Work.Kernels.TildeFacts.theta_quartic τ]
  ring

private lemma theta_identity_two (τ : ℍ) :
    E6Fun τ * (-(UFun τ + VFun τ)) - E4Fun τ * (UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2)
      = -(9 / 2 : ℂ) * (UFun τ * WFun τ ^ 2 * VFun τ) := by
  rw [Work.Residues.KMinusT_E4Fun_eq_theta τ, Work.Residues.KMinusT_E6Fun_eq_theta τ,
    Work.Kernels.TildeFacts.theta_quartic τ]
  ring

private lemma key_identity (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    E6Fun τ * psi2 ℓ τ - E4Fun τ * psi4 ℓ τ
      = (-(9 / 2 : ℂ) * (UFun τ * WFun τ * VFun τ ^ 2)) * ℓ.L τ
        + (-(9 / 2 : ℂ) * (UFun τ * WFun τ ^ 2 * VFun τ)) * ℓ.L_S τ := by
  have h1 := theta_identity_one τ
  have h2 := theta_identity_two τ
  simp only [psi2, psi4]
  rw [congr_fun Work.Residues.XiSlashS.1 τ, congr_fun Work.Residues.XiSlashS.2 τ]
  linear_combination (ℓ.L τ) * h1 + (ℓ.L_S τ) * h2

private lemma funnel_key (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ τ : ℍ, τ ∈ DomainD → (1 : ℝ) / 2 ≤ τ.im →
      ‖E6Fun τ * psi2 ℓ τ - E4Fun τ * psi4 ℓ τ‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
  obtain ⟨CU, hCU, hU⟩ := UFun_bdd_half
  obtain ⟨CW, hCW, hW⟩ := WFun_bdd_half
  obtain ⟨CV, hCV, hV⟩ := VFun_decay_half
  obtain ⟨CL, hCL, hL⟩ := L_bdd_half ℓ
  obtain ⟨CS, hCS, hS⟩ := LS_decay_half ℓ
  refine ⟨2 * ((9 / 2) * CU * CW * CV ^ 2 * CL + (9 / 2) * CU * CW ^ 2 * CV * CS) + 1, 1,
    by positivity, by norm_num, fun τ hτ hτim => ?_⟩
  rw [key_identity ℓ τ, Real.rpow_one]
  set t : ℝ := Real.exp (-(Real.pi * τ.im)) with ht
  have htpos : 0 < t := Real.exp_pos _
  have hVt : ‖VFun τ‖ ≤ CV * t := hV τ hτim
  have hUt : ‖UFun τ‖ ≤ CU := hU τ hτim
  have hWt : ‖WFun τ‖ ≤ CW := hW τ hτim
  have hLt : ‖ℓ.L τ‖ ≤ CL * (1 + ‖(τ : ℂ)‖) := hL τ hτ hτim
  have hSt : ‖ℓ.L_S τ‖ ≤ CS * t := hS τ hτim
  have hexp : Real.exp (-(2 * Real.pi * τ.im)) = t * t := by
    rw [ht, ← Real.exp_add]
    congr 1
    ring
  have hX : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
    have := norm_nonneg (τ : ℂ); linarith
  have hX1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
    have := norm_nonneg (τ : ℂ); linarith
  -- the two coefficients
  have hV2 : ‖VFun τ ^ 2‖ ≤ (CV * t) ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hVt 2
  have hV1 : ‖VFun τ‖ ≤ CV * t := hVt
  have hCWt : ‖WFun τ ^ 2‖ ≤ CW ^ 2 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hWt 2
  have hA1 : ‖UFun τ * WFun τ * VFun τ ^ 2‖ ≤ CU * CW * (CV * t) ^ 2 :=
    nmul3 (by positivity) (by positivity) (by positivity) hUt hWt hV2
  have hA2 : ‖UFun τ * WFun τ ^ 2 * VFun τ‖ ≤ CU * CW ^ 2 * (CV * t) :=
    nmul3 (by positivity) (by positivity) (by positivity) hUt hCWt hV1
  have hB1 : ‖-(9 / 2 : ℂ) * (UFun τ * WFun τ * VFun τ ^ 2)‖ ≤ (9 / 2) * (CU * CW * (CV * t) ^ 2) := by
    rw [norm_mul, norm_neg, show ‖(9 / 2 : ℂ)‖ = 9 / 2 by norm_num]
    exact mul_le_mul_of_nonneg_left hA1 (by norm_num)
  have hB2 : ‖-(9 / 2 : ℂ) * (UFun τ * WFun τ ^ 2 * VFun τ)‖ ≤ (9 / 2) * (CU * CW ^ 2 * (CV * t)) := by
    rw [norm_mul, norm_neg, show ‖(9 / 2 : ℂ)‖ = 9 / 2 by norm_num]
    exact mul_le_mul_of_nonneg_left hA2 (by norm_num)
  -- the two products with `𝓛`, `𝓛_S`
  have hK1 : (0 : ℝ) ≤ (9 / 2) * CU * CW * CV ^ 2 * CL := by positivity
  have hK2 : (0 : ℝ) ≤ (9 / 2) * CU * CW ^ 2 * CV * CS := by positivity
  have e1 : ‖(-(9 / 2 : ℂ) * (UFun τ * WFun τ * VFun τ ^ 2)) * ℓ.L τ‖
      ≤ ((9 / 2) * CU * CW * CV ^ 2 * CL + (9 / 2) * CU * CW ^ 2 * CV * CS)
        * (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * τ.im)) := by
    have h1 := nmul2 (by positivity) (by positivity) hB1 hLt
    rw [hexp]
    have heq : (9 / 2) * (CU * CW * (CV * t) ^ 2) * (CL * (1 + ‖(τ : ℂ)‖))
        = ((9 / 2) * CU * CW * CV ^ 2 * CL) * (1 + ‖(τ : ℂ)‖) * (t * t) := by ring
    rw [heq] at h1
    refine le_trans h1 ?_
    have h2 : ((9 / 2) * CU * CW * CV ^ 2 * CL) ≤
        ((9 / 2) * CU * CW * CV ^ 2 * CL + (9 / 2) * CU * CW ^ 2 * CV * CS) := by linarith
    have h3 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) * (t * t) := by positivity
    nlinarith [h2, h3]
  have e2 : ‖(-(9 / 2 : ℂ) * (UFun τ * WFun τ ^ 2 * VFun τ)) * ℓ.L_S τ‖
      ≤ ((9 / 2) * CU * CW * CV ^ 2 * CL + (9 / 2) * CU * CW ^ 2 * CV * CS)
        * (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * τ.im)) := by
    have h1 := nmul2 (by positivity) (by positivity) hB2 hSt
    rw [hexp]
    have heq : (9 / 2) * (CU * CW ^ 2 * (CV * t)) * (CS * t)
        = ((9 / 2) * CU * CW ^ 2 * CV * CS) * (t * t) := by ring
    rw [heq] at h1
    refine le_trans h1 ?_
    have h2 : ((9 / 2) * CU * CW ^ 2 * CV * CS) ≤
        ((9 / 2) * CU * CW * CV ^ 2 * CL + (9 / 2) * CU * CW ^ 2 * CV * CS) := by linarith
    have h4 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) * (t * t) := by positivity
    have h5 : ((9 / 2) * CU * CW ^ 2 * CV * CS) * (t * t) ≤
        ((9 / 2) * CU * CW * CV ^ 2 * CL + (9 / 2) * CU * CW ^ 2 * CV * CS)
          * (1 + ‖(τ : ℂ)‖) * (t * t) := by
      have h6 : ((9 / 2) * CU * CW ^ 2 * CV * CS) * (t * t)
          ≤ (((9 / 2) * CU * CW * CV ^ 2 * CL + (9 / 2) * CU * CW ^ 2 * CV * CS) * (t * t)) * (1 + ‖(τ : ℂ)‖) := by
        have h7 : ((9 / 2) * CU * CW ^ 2 * CV * CS) * (t * t)
            ≤ ((9 / 2) * CU * CW * CV ^ 2 * CL + (9 / 2) * CU * CW ^ 2 * CV * CS) * (t * t) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
        nlinarith [h7, hX1, mul_nonneg (by positivity : (0:ℝ) ≤ (9/2) * CU * CW * CV ^ 2 * CL + (9/2) * CU * CW ^ 2 * CV * CS) (by positivity : (0:ℝ) ≤ t * t)]
      calc ((9 / 2) * CU * CW ^ 2 * CV * CS) * (t * t)
          ≤ (((9 / 2) * CU * CW * CV ^ 2 * CL + (9 / 2) * CU * CW ^ 2 * CV * CS) * (t * t)) * (1 + ‖(τ : ℂ)‖) := h6
        _ = ((9 / 2) * CU * CW * CV ^ 2 * CL + (9 / 2) * CU * CW ^ 2 * CV * CS)
              * (1 + ‖(τ : ℂ)‖) * (t * t) := by ring
    linarith [h1, h5]
  -- assembly
  have hsum := norm_add_le ((-(9 / 2 : ℂ) * (UFun τ * WFun τ * VFun τ ^ 2)) * ℓ.L τ)
    ((-(9 / 2 : ℂ) * (UFun τ * WFun τ ^ 2 * VFun τ)) * ℓ.L_S τ)
  have hfin : ‖(-(9 / 2 : ℂ) * (UFun τ * WFun τ * VFun τ ^ 2)) * ℓ.L τ
        + (-(9 / 2 : ℂ) * (UFun τ * WFun τ ^ 2 * VFun τ)) * ℓ.L_S τ‖
      ≤ (2 * ((9 / 2) * CU * CW * CV ^ 2 * CL + (9 / 2) * CU * CW ^ 2 * CV * CS) + 1)
        * (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * τ.im)) := by
    have hK : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
    have h6 := e1
    have h7 := e2
    nlinarith [hsum, h6, h7, hK,
      mul_nonneg (by linarith : (0:ℝ) ≤ (9/2) * CU * CW * CV ^ 2 * CL + (9/2) * CU * CW ^ 2 * CV * CS) hK]
  refine le_trans hfin le_rfl

/-! ## The `z`-error atoms

For the `d = 24` assembly we need the two "error" combinations of `Ncusp`:
`fk(2)·E² - 1`, `fk(-2)·E² - 1`, `j·E² - 1` (bounded on `{Im ≥ 1/3}`, and `O(‖E‖²)` near the
cusp) together with `𝓛_S + 16E`, `V - 16E`, `U² - W² - 32E` (bounded on `{Im ≥ 1/3}`, and
`O(‖E‖³)` near the cusp).  Here `E = Ecusp z = Ept z`, `‖E‖ = e^{-π Im z}`.
-/

private lemma tpar_eq_norm_Ecusp (z : ℍ) : Work.Residues.tpar z = ‖Ecusp z‖ := by
  rw [norm_Ecusp, Work.Residues.tpar]

private lemma norm_qParam_eq_Ecusp_sq (z : ℍ) :
    ‖qParamFun z‖ = ‖Ecusp z‖ ^ 2 := by
  rw [norm_qParam, norm_Ecusp, sq, ← Real.exp_add]
  congr 1
  ring

/-- `‖A / D · E² - 1‖ ≤ M/c + 1` when `‖A‖ ≤ M` and `c‖E‖² ≤ ‖D‖`. -/
private lemma err_bound_sq {A D E : ℂ} {M c : ℝ} (hc : 0 < c) (hM : 0 ≤ M) (hE0 : 0 < ‖E‖)
    (hA : ‖A‖ ≤ M) (hD : c * ‖E‖ ^ 2 ≤ ‖D‖) : ‖A / D * E ^ 2 - 1‖ ≤ M / c + 1 := by
  have hDpos : 0 < ‖D‖ := lt_of_lt_of_le (mul_pos hc (pow_pos hE0 2)) hD
  have hDne : D ≠ 0 := norm_pos_iff.mp hDpos
  have hfac : A / D * E ^ 2 - 1 = (A * E ^ 2 - D) / D := by
    rw [div_mul_eq_mul_div]
    field_simp
  rw [hfac, norm_div]
  have hnum : ‖A * E ^ 2 - D‖ ≤ M * ‖E‖ ^ 2 + ‖D‖ := by
    have h1 := norm_sub_le (A * E ^ 2) D
    have h2 : ‖A * E ^ 2‖ ≤ M * ‖E‖ ^ 2 := by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right hA (by positivity)
    linarith
  have h1 : ‖A * E ^ 2 - D‖ / ‖D‖ ≤ (M * ‖E‖ ^ 2 + ‖D‖) / ‖D‖ :=
    div_le_div_of_nonneg_right hnum hDpos.le
  have h2 : M * ‖E‖ ^ 2 / ‖D‖ ≤ M / c := by
    rw [div_le_div_iff₀ hDpos hc]
    nlinarith [hD, hM, hc.le, pow_pos hE0 2]
  have h3 : (M * ‖E‖ ^ 2 + ‖D‖) / ‖D‖ = M * ‖E‖ ^ 2 / ‖D‖ + 1 := by
    field_simp
  linarith

private lemma z_errors_crude (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im →
      ‖fk 2 z * Ecusp z ^ 2 - 1‖ ≤ C ∧
      ‖fk (-2) z * Ecusp z ^ 2 - 1‖ ≤ C ∧
      ‖jInvariantFun z * Ecusp z ^ 2 - 1‖ ≤ C ∧
      ‖ℓ.L_S z + 16 * Ecusp z‖ ≤ C ∧
      ‖VFun z - 16 * Ecusp z‖ ≤ C ∧
      ‖UFun z ^ 2 - WFun z ^ 2 - 32 * Ecusp z‖ ≤ C := by
  obtain ⟨c, hc, hΔl⟩ := delta_lower_third
  obtain ⟨C4, hC4, hE4⟩ := E4Fun_bdd_third
  obtain ⟨C6, hC6, hE6⟩ := E6Fun_bdd_third
  obtain ⟨CU, hCU, hU⟩ := UFun_bdd_third
  obtain ⟨CW, hCW, hW⟩ := WFun_bdd_third
  obtain ⟨CV, hCV, hV⟩ := VFun_bdd_third
  obtain ⟨CS, hCS, hS⟩ := LS_bdd_third ℓ
  refine ⟨(C4 ^ 2 * C6 / c + 1) + (C4 * C6 / c + 1) + (C4 ^ 3 / c + 1) + (CS + 16)
    + (CV + 16) + (CU ^ 2 + CW ^ 2 + 32) + 1, by positivity, fun z hz => ?_⟩
  have hEpos : 0 < ‖Ecusp z‖ := by rw [norm_Ecusp]; exact Real.exp_pos _
  have hDz : c * ‖Ecusp z‖ ^ 2 ≤ ‖DeltaFun z‖ := by
    have h1 := hΔl z (by linarith)
    rwa [norm_qParam_eq_Ecusp_sq z] at h1
  have ht1 : ‖Ecusp z‖ ≤ 1 := by
    rw [norm_Ecusp, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hE14 : ‖E14Fun z‖ ≤ C4 ^ 2 * C6 := by
    have h : E14Fun z = E4Fun z ^ 2 * E6Fun z := rfl
    rw [h, norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hE4 z hz) 2) (hE6 z hz)
      (norm_nonneg _) (by positivity)
  have hE10 : ‖E10Fun z‖ ≤ C4 * C6 := by
    have h : E10Fun z = E4Fun z * E6Fun z := rfl
    rw [h, norm_mul]
    exact mul_le_mul (hE4 z hz) (hE6 z hz) (norm_nonneg _) hC4.le
  have hE43 : ‖E4Fun z ^ 3‖ ≤ C4 ^ 3 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hE4 z hz) 3
  have hA1 : ‖fk 2 z * Ecusp z ^ 2 - 1‖ ≤ C4 ^ 2 * C6 / c + 1 := by
    have hsplit : fk 2 z * Ecusp z ^ 2 - 1 = E14Fun z / DeltaFun z * Ecusp z ^ 2 - 1 := by
      rw [show fk 2 z = E14Fun z / DeltaFun z by simp [Work.Kernels.fk]]
    rw [hsplit]
    exact err_bound_sq hc (by positivity) hEpos hE14 hDz
  have hA2 : ‖fk (-2) z * Ecusp z ^ 2 - 1‖ ≤ C4 * C6 / c + 1 := by
    have hsplit : fk (-2) z * Ecusp z ^ 2 - 1 = E10Fun z / DeltaFun z * Ecusp z ^ 2 - 1 := by
      rw [show fk (-2) z = E10Fun z / DeltaFun z by simp [Work.Kernels.fk]]
    rw [hsplit]
    exact err_bound_sq hc (by positivity) hEpos hE10 hDz
  have hA3 : ‖jInvariantFun z * Ecusp z ^ 2 - 1‖ ≤ C4 ^ 3 / c + 1 := by
    have hsplit : jInvariantFun z * Ecusp z ^ 2 - 1
        = E4Fun z ^ 3 / DeltaFun z * Ecusp z ^ 2 - 1 := by
      rw [show jInvariantFun z = E4Fun z ^ 3 / DeltaFun z from rfl]
    rw [hsplit]
    exact err_bound_sq hc (by positivity) hEpos hE43 hDz
  have hA4 : ‖ℓ.L_S z + 16 * Ecusp z‖ ≤ CS + 16 := by
    have h := norm_add_le (ℓ.L_S z) (16 * Ecusp z)
    have h2 : ‖(16 : ℂ) * Ecusp z‖ = 16 * ‖Ecusp z‖ := by rw [norm_mul, Complex.norm_ofNat]
    rw [h2] at h
    have h3 : 16 * ‖Ecusp z‖ ≤ 16 := by linarith
    linarith [hS z hz, h3]
  have hA5 : ‖VFun z - 16 * Ecusp z‖ ≤ CV + 16 := by
    have h := norm_sub_le (VFun z) (16 * Ecusp z)
    have h2 : ‖(16 : ℂ) * Ecusp z‖ = 16 * ‖Ecusp z‖ := by rw [norm_mul, Complex.norm_ofNat]
    rw [h2] at h
    have h3 : 16 * ‖Ecusp z‖ ≤ 16 := by linarith
    linarith [hV z hz, h3]
  have hA6 : ‖UFun z ^ 2 - WFun z ^ 2 - 32 * Ecusp z‖ ≤ CU ^ 2 + CW ^ 2 + 32 := by
    have h1 := norm_sub_le (UFun z ^ 2 - WFun z ^ 2) (32 * Ecusp z)
    have h2 : ‖(32 : ℂ) * Ecusp z‖ = 32 * ‖Ecusp z‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h3 : ‖UFun z ^ 2 - WFun z ^ 2‖ ≤ CU ^ 2 + CW ^ 2 := by
      have h4 : ‖UFun z ^ 2‖ ≤ CU ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hU z hz) 2
      have h5 : ‖WFun z ^ 2‖ ≤ CW ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hW z hz) 2
      linarith [norm_sub_le (UFun z ^ 2) (WFun z ^ 2)]
    rw [h2] at h1
    have h6 : 32 * ‖Ecusp z‖ ≤ 32 := by linarith
    linarith [h1, h3, h6]
  have hC0 : 0 ≤ C4 ^ 2 * C6 / c + 1 := by positivity
  have hC1 : 0 ≤ C4 * C6 / c + 1 := by positivity
  have hC2 : 0 ≤ C4 ^ 3 / c + 1 := by positivity
  have hC3 : 0 ≤ CS + 16 := by linarith
  have hC4' : 0 ≤ CV + 16 := by linarith
  have hC5 : 0 ≤ CU ^ 2 + CW ^ 2 + 32 := by positivity
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-! ## The cusp regime of the error atoms (`‖E‖²`, `‖E‖³` rates) -/

private lemma cusp_fk2 : ∃ H C : ℝ, 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖fk 2 z * Ecusp z ^ 2 - 1‖ ≤ C * ‖Ecusp z‖ ^ 2 := by
  obtain ⟨H, C, hC, h⟩ := cuspEst_fk_two_mul_Ept_sq
  exact ⟨H, C, hC, fun z hz => by
    have h1 := h z hz
    rw [← norm_Ecusp_tpar z] at h1
    exact h1⟩

private lemma cusp_fkneg2 : ∃ H C : ℝ, 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖fk (-2) z * Ecusp z ^ 2 - 1‖ ≤ C * ‖Ecusp z‖ ^ 2 := by
  obtain ⟨H, C, hC, h⟩ := cuspEst_fk_neg_two_mul_Ept_sq
  exact ⟨H, C, hC, fun z hz => by
    have h1 := h z hz
    rw [← norm_Ecusp_tpar z] at h1
    exact h1⟩

private lemma cusp_jz : ∃ H C : ℝ, 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖jInvariantFun z * Ecusp z ^ 2 - 1‖ ≤ C * ‖Ecusp z‖ ^ 2 := by
  obtain ⟨H, C, hC, h⟩ := cuspEst_Ept_sq_mul_jInvariantFun_sub_one
  exact ⟨H, C, hC, fun z hz => by
    have h1 := h z hz
    rw [← norm_Ecusp_tpar z] at h1
    have heq : ‖jInvariantFun z * Ecusp z ^ 2 - 1‖
        = ‖Work.Residues.Ept z ^ 2 * jInvariantFun z - 1‖ := by
      congr 1
      rw [Ecusp_eq_Ept z]
      ring
    rw [heq]
    exact h1⟩

private lemma cusp_LS (ℓ : Work.Kernels.LogLambdaData) : ∃ H C : ℝ, 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖ℓ.L_S z + 16 * Ecusp z‖ ≤ C * ‖Ecusp z‖ ^ 3 := by
  obtain ⟨H, C, hC, h⟩ := cuspEst_LS_add_16E ℓ
  exact ⟨H, C, hC, fun z hz => by
    have h1 := h z hz
    rw [← norm_Ecusp_tpar z] at h1
    exact h1⟩

private lemma cusp_V : ∃ H C : ℝ, 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖VFun z - 16 * Ecusp z‖ ≤ C * ‖Ecusp z‖ ^ 3 := by
  obtain ⟨H, C, hC, h⟩ := cuspEst_VFun_sub_16E
  exact ⟨H, C, hC, fun z hz => by
    have h1 := h z hz
    rw [← norm_Ecusp_tpar z] at h1
    exact h1⟩

private lemma cusp_UW : ∃ H C : ℝ, 0 < C ∧ ∀ z : ℍ, H ≤ z.im →
    ‖UFun z ^ 2 - WFun z ^ 2 - 32 * Ecusp z‖ ≤ C * ‖Ecusp z‖ ^ 3 := by
  obtain ⟨H, C, hC, h⟩ := cuspEst_UFun_sq_sub_WFun_sq_sub_32E
  exact ⟨H, C, hC, fun z hz => by
    have h1 := h z hz
    rw [← norm_Ecusp_tpar z] at h1
    exact h1⟩

/-! ## The `τ`-coefficients of the expansions -/

private lemma Alpha8_0 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : Alpha ℓ 8 0 τ = E4Fun τ := by
  simp [Alpha, psiVec, vlen, Work.Kernels.fk]

private lemma Alpha8_1 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 8 1 τ = psi2 ℓ τ * (E14Fun τ / DeltaFun τ) := by
  simp [Alpha, psiVec, vlen, Work.Kernels.fk]

private lemma Alpha8_2 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : Alpha ℓ 8 2 τ = psi4 ℓ τ := by
  simp [Alpha, psiVec, vlen, Work.Kernels.fk]

private lemma Alpha24_0 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : Alpha ℓ 24 0 τ = DeltaFun τ := by
  simp [Alpha, psiVec, vlen, Work.Kernels.fk]

private lemma Alpha24_1 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 24 1 τ = psi2 ℓ τ * E10Fun τ := by
  simp [Alpha, psiVec, vlen, Work.Kernels.fk]

private lemma Alpha24_2 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 24 2 τ = psi4 ℓ τ * E4Fun τ ^ 2 := by
  simp [Alpha, psiVec, vlen, Work.Kernels.fk]

/-- The `d = 8` coefficient combination `α₁ - α₂j`, which is `(E₄²/Δ)(E₆ψ₂ - E₄ψ₄)`. -/
private lemma Alpha8_comb (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 8 1 τ - Alpha ℓ 8 2 τ * jInvariantFun τ
      = E4Fun τ ^ 2 / DeltaFun τ * (E6Fun τ * psi2 ℓ τ - E4Fun τ * psi4 ℓ τ) := by
  rw [Alpha8_1, Alpha8_2]
  have hD : DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  simp only [jInvariantFun, E14Fun, E10Fun, Work.Kernels.E14Fun]
  field_simp

/-- The `d = 24` coefficient combination `α₁ - α₂`, which is `E₄(E₆ψ₂ - E₄ψ₄)`. -/
private lemma Alpha24_comb (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ
      = E4Fun τ * (E6Fun τ * psi2 ℓ τ - E4Fun τ * psi4 ℓ τ) := by
  rw [Alpha24_1, Alpha24_2]
  ring

/-- `‖Δ τ‖ ≥ c e^{-2π Im τ}` on the funnel. -/
private lemma Delta_lower_half :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℍ, (1 : ℝ) / 2 ≤ τ.im →
      c * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖DeltaFun τ‖ :=
  let ⟨c, hc, h⟩ := DeltaFun_lower_third
  ⟨c, hc, fun τ hτ => h τ (by linarith)⟩

/-- `‖Δ τ‖⁻¹ ≤ C e^{2π Im τ}` on the funnel. -/
private lemma Delta_inv_half :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (1 : ℝ) / 2 ≤ τ.im →
      ‖DeltaFun τ‖⁻¹ ≤ C * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨c, hc, h⟩ := Delta_lower_half
  refine ⟨1 / c + 1, by positivity, fun τ hτ => ?_⟩
  have h2 := h τ hτ
  have hpos : 0 < c * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
  have hDpos : 0 < ‖DeltaFun τ‖ := lt_of_lt_of_le hpos h2
  have hinv : ‖DeltaFun τ‖⁻¹ ≤ (c * Real.exp (-(2 * Real.pi * τ.im)))⁻¹ :=
    (inv_le_inv₀ hDpos hpos).mpr h2
  have he : (0 : ℝ) < Real.exp (2 * Real.pi * τ.im) := Real.exp_pos _
  have h4 : c⁻¹ ≤ 1 / c + 1 := by
    rw [one_div]
    have : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr hc.le
    linarith
  calc ‖DeltaFun τ‖⁻¹ ≤ (c * Real.exp (-(2 * Real.pi * τ.im)))⁻¹ := hinv
    _ = Real.exp (2 * Real.pi * τ.im) * c⁻¹ := by
        rw [mul_inv, Real.exp_neg, inv_inv]
        ring
    _ ≤ (1 / c + 1) * Real.exp (2 * Real.pi * τ.im) := by
        calc Real.exp (2 * Real.pi * τ.im) * c⁻¹
            ≤ Real.exp (2 * Real.pi * τ.im) * (1 / c + 1) :=
              mul_le_mul_of_nonneg_left h4 he.le
          _ = (1 / c + 1) * Real.exp (2 * Real.pi * τ.im) := by ring

/-- `‖j τ‖ ≤ C e^{2π Im τ}` on the funnel. -/
private lemma jInvariantFun_grow_half :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, (1 : ℝ) / 2 ≤ τ.im →
      ‖jInvariantFun τ‖ ≤ C * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨C4, hC4, hE4⟩ := E4Fun_bdd_half
  obtain ⟨Cinv, hCinv, hinv⟩ := Delta_inv_half
  refine ⟨C4 ^ 3 * Cinv + 1, by positivity, fun τ hτ => ?_⟩
  have h : jInvariantFun τ = E4Fun τ ^ 3 / DeltaFun τ := rfl
  rw [h, norm_div, norm_pow]
  have hnum : ‖E4Fun τ‖ ^ 3 ≤ C4 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (hE4 τ hτ) 3
  have h1 : ‖E4Fun τ‖ ^ 3 / ‖DeltaFun τ‖
      ≤ C4 ^ 3 * (Cinv * Real.exp (2 * Real.pi * τ.im)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hnum (hinv τ hτ) (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
  refine le_trans h1 ?_
  nlinarith [Real.exp_pos (2 * Real.pi * τ.im), hC4.le, hCinv.le]

/-! ## The `d = 8` assembly -/

private lemma Ncusp_bound_eight (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ (τ z : ℍ), τ ∈ DomainD → (1 : ℝ) / 2 ≤ τ.im →
      (1 : ℝ) / 3 ≤ z.im →
      ‖Ncusp ℓ 8 τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨C4, hC4, hE4⟩ := E4Fun_bdd_half
  obtain ⟨C4z, hC4z, hE4z⟩ := E4Fun_bdd_third
  obtain ⟨C6z, hC6z, hE6z⟩ := E6Fun_bdd_third
  obtain ⟨CUz, hCUz, hUz⟩ := UFun_bdd_third
  obtain ⟨CWz, hCWz, hWz⟩ := WFun_bdd_third
  obtain ⟨CVz, hCVz, hVz⟩ := VFun_decay_third
  obtain ⟨CLSz, hCLSz, hLSz⟩ := LS_decay_third ℓ
  obtain ⟨Cs4, hCs4, hpsi4⟩ := psi4_bdd_half ℓ
  obtain ⟨Cinv, hCinv, hinv⟩ := Delta_inv_half
  obtain ⟨K, Ak, hK, hAk, hkey⟩ := funnel_key ℓ
  set A : ℝ := max Ak 1 with hA
  have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right Ak 1)
  have hAkA : Ak ≤ A := le_max_left Ak 1
  have h1A : (1 : ℝ) ≤ A := le_max_right Ak 1
  set Kc : ℝ := 3456 * C4 * (C4z * C6z) * CLSz + 1728 * Cs4 * (C4z ^ 2 * CVz)
      + (K * (C4 ^ 2 * Cinv)) * (C4z ^ 2 * CVz + C6z * (CUz + CWz) * CVz) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  refine ⟨(‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc + 1) * (1 + Kc) + 1, A,
    by positivity, hA0, fun τ z hτ hτ2 hz => ?_⟩
  have hM1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
    have := norm_nonneg (τ : ℂ); linarith
  have hMz : (0 : ℝ) < 1 + ‖(τ : ℂ)‖ := by
    have := norm_nonneg (τ : ℂ); linarith
  have hMz0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := hMz.le
  have hexp : (0 : ℝ) < Real.exp (-(Real.pi * z.im)) := Real.exp_pos _
  have hE1 : fk (ulen 8 0) z = E4Fun z * E6Fun z := by rw [ulen8_zero, fk_ten_eq]
  have hE2 : fk (ulen 8 1) z = E4Fun z ^ 2 := by rw [ulen8_one, fk_eight_eq]
  have hE3 : fk (ulen 8 2) z = E6Fun z := by rw [ulen8_two, fk_six_eq]
  -- the three `z`-factors
  have hT0 : ‖fk (ulen 8 0) z * ℓ.L_S z‖ ≤ C4z * C6z * (CLSz * Real.exp (-(Real.pi * z.im))) := by
    rw [hE1]
    exact nmul3 hC4z.le hC6z.le (by positivity) (hE4z z hz) (hE6z z hz) (hLSz z hz)
  have hT1 : ‖-(fk (ulen 8 1) z * VFun z)‖ ≤ C4z ^ 2 * (CVz * Real.exp (-(Real.pi * z.im))) := by
    rw [norm_neg, hE2]
    exact nmul2 (pow_nonneg hC4z.le 2) (by positivity)
      (by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hE4z z hz) 2) (hVz z hz)
  have hT12 : ‖-(fk (ulen 8 1) z * VFun z) - fk (ulen 8 2) z * (UFun z ^ 2 - WFun z ^ 2)‖
      ≤ (C4z ^ 2 + C6z * (CUz + CWz)) * (CVz * Real.exp (-(Real.pi * z.im))) := by
    have h3 : UFun z ^ 2 - WFun z ^ 2 = VFun z * (UFun z + WFun z) := by
      have hq := Work.Kernels.TildeFacts.theta_quartic z
      rw [hq]; ring
    have h4 : ‖UFun z + WFun z‖ ≤ CUz + CWz :=
      le_trans (norm_add_le _ _) (add_le_add (hUz z hz) (hWz z hz))
    have hA : ‖fk (ulen 8 1) z * VFun z‖ ≤ C4z ^ 2 * (CVz * Real.exp (-(Real.pi * z.im))) := by
      rw [hE2]
      exact nmul2 (pow_nonneg hC4z.le 2) (by positivity)
        (by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hE4z z hz) 2) (hVz z hz)
    have hB : ‖fk (ulen 8 2) z * (UFun z ^ 2 - WFun z ^ 2)‖
        ≤ C6z * ((CUz + CWz) * (CVz * Real.exp (-(Real.pi * z.im)))) := by
      rw [hE3, h3]
      have hinner : ‖VFun z * (UFun z + WFun z)‖
          ≤ CVz * Real.exp (-(Real.pi * z.im)) * (CUz + CWz) :=
        nmul2 (by positivity) (add_nonneg hCUz.le hCWz.le) (hVz z hz) h4
      calc ‖E6Fun z * (VFun z * (UFun z + WFun z))‖
          ≤ C6z * (CVz * Real.exp (-(Real.pi * z.im)) * (CUz + CWz)) :=
            nmul2 hC6z.le (by positivity) (hE6z z hz) hinner
        _ = C6z * ((CUz + CWz) * (CVz * Real.exp (-(Real.pi * z.im)))) := by ring
    calc ‖-(fk (ulen 8 1) z * VFun z) - fk (ulen 8 2) z * (UFun z ^ 2 - WFun z ^ 2)‖
        ≤ ‖-(fk (ulen 8 1) z * VFun z)‖ + ‖fk (ulen 8 2) z * (UFun z ^ 2 - WFun z ^ 2)‖ :=
          norm_sub_le _ _
      _ = ‖fk (ulen 8 1) z * VFun z‖ + ‖fk (ulen 8 2) z * (UFun z ^ 2 - WFun z ^ 2)‖ := by
          rw [norm_neg]
      _ ≤ C4z ^ 2 * (CVz * Real.exp (-(Real.pi * z.im)))
          + C6z * ((CUz + CWz) * (CVz * Real.exp (-(Real.pi * z.im)))) := add_le_add hA hB
      _ = (C4z ^ 2 + C6z * (CUz + CWz)) * (CVz * Real.exp (-(Real.pi * z.im))) := by ring
  -- `τ`-side coefficients
  have hA0c : ‖Alpha ℓ 8 0 τ‖ ≤ C4 := by
    rw [Alpha8_0]; exact hE4 τ hτ2
  have hA2c : ‖Alpha ℓ 8 2 τ‖ ≤ Cs4 * (1 + ‖(τ : ℂ)‖) := by
    rw [Alpha8_2]; exact hpsi4 τ hτ hτ2
  have hA12c : ‖Alpha ℓ 8 1 τ - Alpha ℓ 8 2 τ * jInvariantFun τ‖
      ≤ K * (C4 ^ 2 * Cinv) * (1 + ‖(τ : ℂ)‖) ^ Ak := by
    rw [Alpha8_comb]
    have h1 : ‖E4Fun τ ^ 2 / DeltaFun τ‖ ≤ C4 ^ 2 * (Cinv * Real.exp (2 * Real.pi * τ.im)) := by
      rw [div_eq_mul_inv]
      exact nmul2 (pow_nonneg hC4.le 2) (by positivity)
        (by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hE4 τ hτ2) 2)
        (by rw [norm_inv]; exact hinv τ hτ2)
    have h2 := hkey τ hτ hτ2
    have h3 : ‖E4Fun τ ^ 2 / DeltaFun τ * (E6Fun τ * psi2 ℓ τ - E4Fun τ * psi4 ℓ τ)‖
        ≤ (C4 ^ 2 * (Cinv * Real.exp (2 * Real.pi * τ.im)))
          * (K * (1 + ‖(τ : ℂ)‖) ^ Ak * Real.exp (-(2 * Real.pi * τ.im))) := by
      rw [norm_mul]
      exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    refine le_trans h3 (le_of_eq ?_)
    have he : Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * τ.im)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc (C4 ^ 2 * (Cinv * Real.exp (2 * Real.pi * τ.im)))
          * (K * (1 + ‖(τ : ℂ)‖) ^ Ak * Real.exp (-(2 * Real.pi * τ.im)))
        = K * (C4 ^ 2 * Cinv) * (1 + ‖(τ : ℂ)‖) ^ Ak
            * (Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * τ.im))) := by ring
      _ = K * (C4 ^ 2 * Cinv) * (1 + ‖(τ : ℂ)‖) ^ Ak := by rw [he, mul_one]
  -- rewrite `T8`
  have hT8 : T8 ℓ τ z = -(3456 : ℂ) * Alpha ℓ 8 0 τ * (fk (ulen 8 0) z * ℓ.L_S z)
      + (1728 : ℂ) * Alpha ℓ 8 2 τ * (-(fk (ulen 8 1) z * VFun z))
      + (Alpha ℓ 8 1 τ - Alpha ℓ 8 2 τ * jInvariantFun τ)
        * (-(fk (ulen 8 1) z * VFun z) - fk (ulen 8 2) z * (UFun z ^ 2 - WFun z ^ 2)) := by
    simp only [T8]
    ring
  have hp : (1 + ‖(τ : ℂ)‖) ^ Ak ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
    Real.rpow_le_rpow_of_exponent_le hM1 hAkA
  have hp1 : (1 + ‖(τ : ℂ)‖) ^ (1 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
    Real.rpow_le_rpow_of_exponent_le hM1 h1A
  have hpA : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.rpow_nonneg hMz0 A
  have hp1' : ((1 : ℝ) + ‖(τ : ℂ)‖) ^ (1 : ℝ) = 1 + ‖(τ : ℂ)‖ := Real.rpow_one _
  have hb1 : ‖-(3456 : ℂ) * Alpha ℓ 8 0 τ * (fk (ulen 8 0) z * ℓ.L_S z)‖
      ≤ 3456 * C4 * (C4z * C6z) * CLSz * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
    have hneg : -(3456 : ℂ) * Alpha ℓ 8 0 τ = -((3456 : ℂ) * Alpha ℓ 8 0 τ) := by ring
    have hb : ‖-(3456 : ℂ) * Alpha ℓ 8 0 τ‖ ≤ 3456 * C4 := by
      rw [hneg, norm_neg, norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hA0c (by norm_num)
    have h := nmul2 (by positivity) (by positivity) hb hT0
    have h5 : (1 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.one_le_rpow hM1 hA0
    have hK0 : (0 : ℝ) ≤ 3456 * C4 * (C4z * C6z) * CLSz * Real.exp (-(Real.pi * z.im)) := by
      positivity
    have hstep : 3456 * C4 * (C4z * C6z) * CLSz * Real.exp (-(Real.pi * z.im)) * 1
        ≤ 3456 * C4 * (C4z * C6z) * CLSz * Real.exp (-(Real.pi * z.im))
          * (1 + ‖(τ : ℂ)‖) ^ A :=
      mul_le_mul_of_nonneg_left h5 hK0
    refine le_trans h ?_
    calc (3456 * C4) * (C4z * C6z * (CLSz * Real.exp (-(Real.pi * z.im))))
        = 3456 * C4 * (C4z * C6z) * CLSz * Real.exp (-(Real.pi * z.im)) := by ring
      _ = 3456 * C4 * (C4z * C6z) * CLSz * Real.exp (-(Real.pi * z.im)) * 1 := by ring
      _ ≤ 3456 * C4 * (C4z * C6z) * CLSz * Real.exp (-(Real.pi * z.im))
            * (1 + ‖(τ : ℂ)‖) ^ A := hstep
      _ = 3456 * C4 * (C4z * C6z) * CLSz * (1 + ‖(τ : ℂ)‖) ^ A
            * Real.exp (-(Real.pi * z.im)) := by ring
  have hb2 : ‖(1728 : ℂ) * Alpha ℓ 8 2 τ * (-(fk (ulen 8 1) z * VFun z))‖
      ≤ 1728 * Cs4 * (C4z ^ 2 * CVz) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
    have hb : ‖(1728 : ℂ) * Alpha ℓ 8 2 τ‖ ≤ 1728 * (Cs4 * (1 + ‖(τ : ℂ)‖)) := by
      rw [norm_mul, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left hA2c (by norm_num)
    have h := nmul2 (by positivity) (by positivity) hb hT1
    refine le_trans h ?_
    have hx : (1728 * (Cs4 * (1 + ‖(τ : ℂ)‖)))
          * (C4z ^ 2 * (CVz * Real.exp (-(Real.pi * z.im))))
        = 1728 * Cs4 * (C4z ^ 2 * CVz) * (1 + ‖(τ : ℂ)‖) * Real.exp (-(Real.pi * z.im)) := by ring
    rw [hx]
    have h1 : 1728 * Cs4 * (C4z ^ 2 * CVz) * (1 + ‖(τ : ℂ)‖)
        ≤ 1728 * Cs4 * (C4z ^ 2 * CVz) * (1 + ‖(τ : ℂ)‖) ^ A := by
      nth_rewrite 1 [← hp1']
      exact mul_le_mul_of_nonneg_left hp1 (by positivity)
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hb3 : ‖(Alpha ℓ 8 1 τ - Alpha ℓ 8 2 τ * jInvariantFun τ)
        * (-(fk (ulen 8 1) z * VFun z) - fk (ulen 8 2) z * (UFun z ^ 2 - WFun z ^ 2))‖
      ≤ (K * (C4 ^ 2 * Cinv)) * (C4z ^ 2 * CVz + C6z * (CUz + CWz) * CVz)
        * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
    have h := nmul2 (by positivity) (by positivity) hA12c hT12
    refine le_trans h ?_
    have h8 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by positivity
    have h9 : K * (C4 ^ 2 * Cinv) * ((C4z ^ 2 + C6z * (CUz + CWz)) * CVz)
        ≤ K * (C4 ^ 2 * Cinv) * (C4z ^ 2 * CVz + C6z * (CUz + CWz) * CVz) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      nlinarith [hC4z.le, hC6z.le, hCUz.le, hCWz.le, hCVz.le]
    have hstep1 : K * (C4 ^ 2 * Cinv) * (1 + ‖(τ : ℂ)‖) ^ Ak
          * ((C4z ^ 2 + C6z * (CUz + CWz)) * (CVz * Real.exp (-(Real.pi * z.im))))
        ≤ K * (C4 ^ 2 * Cinv) * ((C4z ^ 2 + C6z * (CUz + CWz)) * CVz)
          * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))) := by
      have hfac : K * (C4 ^ 2 * Cinv) * (1 + ‖(τ : ℂ)‖) ^ Ak
            * ((C4z ^ 2 + C6z * (CUz + CWz)) * (CVz * Real.exp (-(Real.pi * z.im))))
          = (K * (C4 ^ 2 * Cinv) * ((C4z ^ 2 + C6z * (CUz + CWz)) * CVz))
            * ((1 + ‖(τ : ℂ)‖) ^ Ak * Real.exp (-(Real.pi * z.im))) := by ring
      rw [hfac]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hexp.le) (by positivity)
    have hstep2 : K * (C4 ^ 2 * Cinv) * ((C4z ^ 2 + C6z * (CUz + CWz)) * CVz)
          * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)))
        ≤ K * (C4 ^ 2 * Cinv) * (C4z ^ 2 * CVz + C6z * (CUz + CWz) * CVz)
          * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
      have hfac : K * (C4 ^ 2 * Cinv) * (C4z ^ 2 * CVz + C6z * (CUz + CWz) * CVz)
            * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))
          = (K * (C4 ^ 2 * Cinv) * (C4z ^ 2 * CVz + C6z * (CUz + CWz) * CVz))
            * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))) := by ring
      rw [hfac]
      exact mul_le_mul_of_nonneg_right h9 h8
    exact le_trans hstep1 hstep2
  -- assemble the bound for `T8`
  have hmain : ‖T8 ℓ τ z‖ ≤ Kc * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))) := by
    have hassoc : -(3456 : ℂ) * Alpha ℓ 8 0 τ * (fk (ulen 8 0) z * ℓ.L_S z)
        + (1728 : ℂ) * Alpha ℓ 8 2 τ * (-(fk (ulen 8 1) z * VFun z))
        + (Alpha ℓ 8 1 τ - Alpha ℓ 8 2 τ * jInvariantFun τ)
          * (-(fk (ulen 8 1) z * VFun z) - fk (ulen 8 2) z * (UFun z ^ 2 - WFun z ^ 2))
        = (-(3456 : ℂ) * Alpha ℓ 8 0 τ * (fk (ulen 8 0) z * ℓ.L_S z)
            + (1728 : ℂ) * Alpha ℓ 8 2 τ * (-(fk (ulen 8 1) z * VFun z)))
          + (Alpha ℓ 8 1 τ - Alpha ℓ 8 2 τ * jInvariantFun τ)
            * (-(fk (ulen 8 1) z * VFun z) - fk (ulen 8 2) z * (UFun z ^ 2 - WFun z ^ 2)) := by
      ring
    have hexpand : (3456 * C4 * (C4z * C6z) * CLSz + 1728 * Cs4 * (C4z ^ 2 * CVz)
        + (K * (C4 ^ 2 * Cinv)) * (C4z ^ 2 * CVz + C6z * (CUz + CWz) * CVz))
        * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)))
        = 3456 * C4 * (C4z * C6z) * CLSz * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))
          + 1728 * Cs4 * (C4z ^ 2 * CVz) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))
          + (K * (C4 ^ 2 * Cinv)) * (C4z ^ 2 * CVz + C6z * (CUz + CWz) * CVz)
            * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by ring
    rw [hT8, hKc, hassoc, hexpand]
    have h12 := norm_add_le (-(3456 : ℂ) * Alpha ℓ 8 0 τ * (fk (ulen 8 0) z * ℓ.L_S z))
      ((1728 : ℂ) * Alpha ℓ 8 2 τ * (-(fk (ulen 8 1) z * VFun z)))
    have hsplit := norm_add_le (-(3456 : ℂ) * Alpha ℓ 8 0 τ * (fk (ulen 8 0) z * ℓ.L_S z)
        + (1728 : ℂ) * Alpha ℓ 8 2 τ * (-(fk (ulen 8 1) z * VFun z)))
      ((Alpha ℓ 8 1 τ - Alpha ℓ 8 2 τ * jInvariantFun τ)
        * (-(fk (ulen 8 1) z * VFun z) - fk (ulen 8 2) z * (UFun z ^ 2 - WFun z ^ 2)))
    linarith [hsplit, h12, hb1, hb2, hb3]
  have hNc : Ncusp ℓ 8 τ z = (2 * c1728 * (Real.pi : ℂ))⁻¹ * T8 ℓ τ z :=
    Ncusp_eight_expansion ℓ τ z
  rw [hNc, norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left hmain (norm_nonneg _)) ?_
  have hM0 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.rpow_nonneg hMz0 A
  have he0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * z.im)) := hexp.le
  have hME : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := mul_nonneg hM0 he0
  have hkey2 : ‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc
      ≤ (‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc + 1) * (1 + Kc) := by
    have h1 : (0 : ℝ) ≤ ‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc := by positivity
    nlinarith [h1, hKc0]
  calc ‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖
        * (Kc * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))))
      = (‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc)
        * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))) := by ring
    _ ≤ ((‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc + 1) * (1 + Kc))
          * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))) :=
        mul_le_mul_of_nonneg_right hkey2 hME
    _ ≤ ((‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc + 1) * (1 + Kc) + 1)
          * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
        have h4 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) :=
          mul_nonneg hM0 he0
        have h5 : ((‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc + 1) * (1 + Kc))
            * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)))
            ≤ ((‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc + 1) * (1 + Kc) + 1)
              * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))) :=
          mul_le_mul_of_nonneg_right (by linarith) h4
        calc ((‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc + 1) * (1 + Kc))
              * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)))
            ≤ ((‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc + 1) * (1 + Kc) + 1)
              * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))) := h5
          _ = ((‖(2 * c1728 * (Real.pi : ℂ))⁻¹‖ * Kc + 1) * (1 + Kc) + 1)
              * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by ring

/-- `‖Δ z‖⁻¹ ≤ C e^{2π Im z}` for `Im z ≥ 1/3`. -/
private lemma Delta_inv_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im →
      ‖DeltaFun z‖⁻¹ ≤ C * Real.exp (2 * Real.pi * z.im) := by
  obtain ⟨c, hc, h⟩ := DeltaFun_lower_third
  refine ⟨1 / c + 1, by positivity, fun z hz => ?_⟩
  have h2 := h z hz
  have hpos : 0 < c * Real.exp (-(2 * Real.pi * z.im)) := by positivity
  have hDpos : 0 < ‖DeltaFun z‖ := lt_of_lt_of_le hpos h2
  have hinv : ‖DeltaFun z‖⁻¹ ≤ (c * Real.exp (-(2 * Real.pi * z.im)))⁻¹ :=
    (inv_le_inv₀ hDpos hpos).mpr h2
  have he : (0 : ℝ) < Real.exp (2 * Real.pi * z.im) := Real.exp_pos _
  have h4 : c⁻¹ ≤ 1 / c + 1 := by
    rw [one_div]
    have : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr hc.le
    linarith
  calc ‖DeltaFun z‖⁻¹ ≤ (c * Real.exp (-(2 * Real.pi * z.im)))⁻¹ := hinv
    _ = Real.exp (2 * Real.pi * z.im) * c⁻¹ := by
        rw [mul_inv, Real.exp_neg, inv_inv]
        ring
    _ ≤ (1 / c + 1) * Real.exp (2 * Real.pi * z.im) := by
        calc Real.exp (2 * Real.pi * z.im) * c⁻¹
            ≤ Real.exp (2 * Real.pi * z.im) * (1 / c + 1) :=
              mul_le_mul_of_nonneg_left h4 he.le
          _ = (1 / c + 1) * Real.exp (2 * Real.pi * z.im) := by ring

/-- `‖j z‖ ≤ C e^{2π Im z}` for `Im z ≥ 1/3`. -/
private lemma jInvariantFun_grow_third :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im →
      ‖jInvariantFun z‖ ≤ C * Real.exp (2 * Real.pi * z.im) := by
  obtain ⟨C4z, hC4z, hE4z⟩ := E4Fun_bdd_third
  obtain ⟨Cinv, hCinv, hinv⟩ := Delta_inv_third
  refine ⟨C4z ^ 3 * Cinv + 1, by positivity, fun z hz => ?_⟩
  have h : jInvariantFun z = E4Fun z ^ 3 / DeltaFun z := rfl
  rw [h]
  have hgoal : ‖E4Fun z ^ 3 / DeltaFun z‖ = ‖E4Fun z‖ ^ 3 * (‖DeltaFun z‖)⁻¹ := by
    rw [norm_div, norm_pow, div_eq_mul_inv]
  rw [hgoal]
  have hnum : ‖E4Fun z‖ ^ 3 ≤ C4z ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (hE4z z hz) 3
  have h1 : ‖E4Fun z‖ ^ 3 * (‖DeltaFun z‖)⁻¹
      ≤ C4z ^ 3 * (Cinv * Real.exp (2 * Real.pi * z.im)) := by
    exact mul_le_mul hnum (hinv z hz) (by positivity) (by positivity)
  refine le_trans h1 ?_
  nlinarith [Real.exp_pos (2 * Real.pi * z.im), hC4z.le, hCinv.le]

/-- `‖𝓛_S z‖ ≤ C` for `Im z ≥ 1/3`. -/
private lemma LS_bdd_nonneg (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im → ‖ℓ.L_S z‖ ≤ C :=
  LS_bdd_third ℓ

/-! ## The `d = 24` assembly: the crude regime -/

/-- On `{1/3 ≤ Im z ≤ H}` the `z`-factor `fk(2)·𝓛_S` is bounded. -/
private lemma fk2_LS_bound_H (ℓ : Work.Kernels.LogLambdaData) (H : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im → z.im ≤ H →
      ‖fk 2 z * ℓ.L_S z‖ ≤ C := by
  obtain ⟨C4z, hC4z, hE4z⟩ := E4Fun_bdd_third
  obtain ⟨C6z, hC6z, hE6z⟩ := E6Fun_bdd_third
  obtain ⟨CLSz, hCLSz, hLSz⟩ := LS_decay_third ℓ
  obtain ⟨Cinv, hCinv, hinv⟩ := Delta_inv_third
  refine ⟨C4z ^ 2 * C6z * Cinv * Real.exp (2 * Real.pi * H) * CLSz + 1,
    by positivity, fun z hz hzH => ?_⟩
  have hfk : fk 2 z = E14Fun z / DeltaFun z := by simp [Work.Kernels.fk]
  have hE14 : ‖E14Fun z‖ ≤ C4z ^ 2 * C6z := by
    have h : E14Fun z = E4Fun z ^ 2 * E6Fun z := rfl
    rw [h, norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hE4z z hz) 2) (hE6z z hz)
      (norm_nonneg _) (by positivity)
  have hLSu : ‖ℓ.L_S z‖ ≤ CLSz := by
    refine le_trans (hLSz z hz) ?_
    have he1 : Real.exp (-(Real.pi * z.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, z.im_pos]
    nlinarith [he1, hCLSz.le]
  have h1 : ‖fk 2 z * ℓ.L_S z‖
      ≤ (C4z ^ 2 * C6z) * (Cinv * Real.exp (2 * Real.pi * z.im)) * CLSz := by
    rw [hfk, div_eq_mul_inv]
    refine nmul3 (by positivity) (by positivity) (by positivity) hE14 ?_ hLSu
    rw [norm_inv]
    exact hinv z hz
  refine le_trans h1 ?_
  have h2 : Real.exp (2 * Real.pi * z.im) ≤ Real.exp (2 * Real.pi * H) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hzH])
  have h3 : (C4z ^ 2 * C6z) * (Cinv * Real.exp (2 * Real.pi * z.im)) * CLSz
      ≤ (C4z ^ 2 * C6z) * (Cinv * Real.exp (2 * Real.pi * H)) * CLSz := by
    refine mul_le_mul_of_nonneg_right ?_ hCLSz.le
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hCinv.le) (by positivity)
  refine le_trans h3 ?_
  nlinarith [hC4z.le, hC6z.le, hCinv.le, hCLSz.le, Real.exp_pos (2 * Real.pi * H)]

/-- On `{1/3 ≤ Im z ≤ H}` the `z`-factor `fk(-2)·(U² - W²)` is bounded. -/
private lemma fkm2_UW_bound_H (H : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, (1 : ℝ) / 3 ≤ z.im → z.im ≤ H →
      ‖fk (-2) z * (UFun z ^ 2 - WFun z ^ 2)‖ ≤ C := by
  obtain ⟨C4z, hC4z, hE4z⟩ := E4Fun_bdd_third
  obtain ⟨C6z, hC6z, hE6z⟩ := E6Fun_bdd_third
  obtain ⟨CUz, hCUz, hUz⟩ := UFun_bdd_third
  obtain ⟨CWz, hCWz, hWz⟩ := WFun_bdd_third
  obtain ⟨CVz, hCVz, hVz⟩ := VFun_decay_third
  obtain ⟨Cinv, hCinv, hinv⟩ := Delta_inv_third
  refine ⟨C4z * C6z * Cinv * Real.exp (2 * Real.pi * H) * (CVz * (CUz + CWz)) + 1,
    by positivity, fun z hz hzH => ?_⟩
  have hfk : fk (-2) z = E10Fun z / DeltaFun z := by simp [Work.Kernels.fk]
  have hE10 : ‖E10Fun z‖ ≤ C4z * C6z := by
    have h : E10Fun z = E4Fun z * E6Fun z := rfl
    rw [h, norm_mul]
    exact mul_le_mul (hE4z z hz) (hE6z z hz) (norm_nonneg _) hC4z.le
  have h3 : UFun z ^ 2 - WFun z ^ 2 = VFun z * (UFun z + WFun z) := by
    have hq := Work.Kernels.TildeFacts.theta_quartic z
    rw [hq]; ring
  have h4 : ‖UFun z + WFun z‖ ≤ CUz + CWz :=
    le_trans (norm_add_le _ _) (add_le_add (hUz z hz) (hWz z hz))
  have hVu : ‖VFun z‖ ≤ CVz := by
    refine le_trans (hVz z hz) ?_
    have he1 : Real.exp (-(Real.pi * z.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, z.im_pos]
    nlinarith [he1, hCVz.le]
  have h5 : ‖VFun z * (UFun z + WFun z)‖ ≤ CVz * (CUz + CWz) :=
    nmul2 (by positivity) (add_nonneg hCUz.le hCWz.le) hVu h4
  have h1 : ‖fk (-2) z * (UFun z ^ 2 - WFun z ^ 2)‖
      ≤ (C4z * C6z) * (Cinv * Real.exp (2 * Real.pi * z.im)) * (CVz * (CUz + CWz)) := by
    rw [hfk, h3, div_eq_mul_inv]
    refine nmul3 (by positivity) (by positivity) (by positivity) hE10 ?_ h5
    rw [norm_inv]
    exact hinv z hz
  refine le_trans h1 ?_
  have h2 : Real.exp (2 * Real.pi * z.im) ≤ Real.exp (2 * Real.pi * H) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hzH])
  have h3 : (C4z * C6z) * (Cinv * Real.exp (2 * Real.pi * z.im)) * (CVz * (CUz + CWz))
      ≤ (C4z * C6z) * (Cinv * Real.exp (2 * Real.pi * H)) * (CVz * (CUz + CWz)) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hCinv.le) (by positivity)
  refine le_trans h3 ?_
  nlinarith [hC4z.le, hC6z.le, hCinv.le, mul_nonneg hCVz.le (add_nonneg hCUz.le hCWz.le),
    Real.exp_pos (2 * Real.pi * H)]

/-- The `d = 24` kernel `T₂₄` is `O((1+‖τ‖)^A e^{-π Im z})` for `Im z ≤ H`. -/
private lemma T24_crude (ℓ : Work.Kernels.LogLambdaData) (H : ℝ) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ (τ z : ℍ), τ ∈ DomainD → (1 : ℝ) / 2 ≤ τ.im →
      (1 : ℝ) / 3 ≤ z.im → z.im ≤ H →
      ‖T24 ℓ τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨Cf2, hCf2, hfk2⟩ := fk2_LS_bound_H ℓ H
  obtain ⟨Cfm, hCfm, hfm⟩ := fkm2_UW_bound_H H
  obtain ⟨CVz, hCVz, hVz⟩ := VFun_bdd_third
  obtain ⟨C4, hC4, hE4⟩ := E4Fun_bdd_half
  obtain ⟨C6, hC6, hE6⟩ := E6Fun_bdd_third
  obtain ⟨Cs4, hCs4, hpsi4⟩ := psi4_bdd_half ℓ
  obtain ⟨Cj, hCj, hjτ⟩ := jInvariantFun_grow_half
  obtain ⟨Cjz, hCjz, hjz⟩ := jInvariantFun_grow_third
  obtain ⟨K, Ak, hK, hAk, hkey⟩ := funnel_key ℓ
  obtain ⟨Cd, hCd, hΔu⟩ := DeltaFun_upper_third
  set A : ℝ := max Ak 1 with hA
  have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right Ak 1)
  have hAkA : Ak ≤ A := le_max_left Ak 1
  have h1A : (1 : ℝ) ≤ A := le_max_right Ak 1
  refine ⟨(3456 * Cd * Cf2 + (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
      + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
      + 1728 * (Cs4 * C4 ^ 2)) * CVz + C4 * K * Cfm + 1) * Real.exp (Real.pi * H) + 1,
    A, by positivity, hA0, ?_⟩
  intro τ z hτ hτ2 hz hzH
  have hM1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
    have := norm_nonneg (τ : ℂ); linarith
  have hM0 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.rpow_nonneg (by positivity) A
  have hMA : (1 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.one_le_rpow hM1 hA0
  have hexp : (0 : ℝ) < Real.exp (-(Real.pi * z.im)) := Real.exp_pos _
  have hjt : ‖jInvariantFun τ‖ ≤ Cj * Real.exp (2 * Real.pi * τ.im) := hjτ τ hτ2
  have hjzH : ‖jInvariantFun z‖ ≤ Cjz * Real.exp (2 * Real.pi * H) := by
    refine le_trans (hjz z hz) ?_
    have h2 : Real.exp (2 * Real.pi * z.im) ≤ Real.exp (2 * Real.pi * H) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hzH])
    nlinarith [h2, Real.exp_pos (2 * Real.pi * z.im), hCjz.le]
  have hL1 : ‖Alpha ℓ 24 0 τ‖ ≤ Cd * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [Alpha24_0]
    exact hΔu τ (by linarith)
  have hL2 : ‖Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ‖
      ≤ C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [Alpha24_comb]
    have h2 := hkey τ hτ hτ2
    have h3 : ‖E4Fun τ * (E6Fun τ * psi2 ℓ τ - E4Fun τ * psi4 ℓ τ)‖
        ≤ C4 * (K * (1 + ‖(τ : ℂ)‖) ^ Ak * Real.exp (-(2 * Real.pi * τ.im))) :=
      nmul2 hC4.le (by positivity) (hE4 τ hτ2) h2
    refine le_trans h3 ?_
    have hp : (1 + ‖(τ : ℂ)‖) ^ Ak ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
      Real.rpow_le_rpow_of_exponent_le hM1 hAkA
    have h0 : (0 : ℝ) ≤ C4 * K * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
    nlinarith [hp, h0, mul_le_mul_of_nonneg_left hp h0]
  have hL3 : ‖Alpha ℓ 24 2 τ‖ ≤ Cs4 * C4 ^ 2 * (1 + ‖(τ : ℂ)‖) ^ A := by
    rw [Alpha24_2]
    have h1 := hpsi4 τ hτ hτ2
    have h4 : ‖E4Fun τ ^ 2‖ ≤ C4 ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hE4 τ hτ2) 2
    have h3 : ‖psi4 ℓ τ * E4Fun τ ^ 2‖ ≤ (Cs4 * (1 + ‖(τ : ℂ)‖)) * C4 ^ 2 :=
      nmul2 (by positivity) (by positivity) h1 h4
    refine le_trans h3 ?_
    have h5 : (1 + ‖(τ : ℂ)‖) ≤ (1 + ‖(τ : ℂ)‖) ^ A := by
      have h7 : (1 + ‖(τ : ℂ)‖) ^ (1 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
        Real.rpow_le_rpow_of_exponent_le hM1 h1A
      rwa [Real.rpow_one] at h7
    calc (Cs4 * (1 + ‖(τ : ℂ)‖)) * C4 ^ 2 = (Cs4 * C4 ^ 2) * (1 + ‖(τ : ℂ)‖) := by ring
      _ ≤ (Cs4 * C4 ^ 2) * (1 + ‖(τ : ℂ)‖) ^ A := mul_le_mul_of_nonneg_left h5 (by positivity)
  -- the coefficient of `VFun z`
  have hE2 : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) = 1 := by
    rw [← Real.exp_add]; simp
  have ht : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
  have hJdiff : ‖jInvariantFun τ - jInvariantFun z‖
      ≤ Cj * Real.exp (2 * Real.pi * τ.im) + Cjz * Real.exp (2 * Real.pi * H) :=
    le_trans (norm_sub_le _ _) (add_le_add hjt hjzH)
  have hc1 : ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * (jInvariantFun τ - jInvariantFun z)‖
      ≤ 3456 * Cd * Cj + 3456 * Cd * Cjz * Real.exp (2 * Real.pi * H) := by
    have hneg : ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ‖
        ≤ 3456 * (Cd * Real.exp (-(2 * Real.pi * τ.im))) := by
      rw [norm_mul]
      have h4 : ‖(-3456 : ℂ)‖ = 3456 := by norm_num
      rw [h4]
      exact mul_le_mul_of_nonneg_left hL1 (by norm_num)
    have h2 := nmul2 (by positivity) (by positivity) hneg hJdiff
    refine le_trans h2 ?_
    calc 3456 * (Cd * Real.exp (-(2 * Real.pi * τ.im)))
          * (Cj * Real.exp (2 * Real.pi * τ.im) + Cjz * Real.exp (2 * Real.pi * H))
        = 3456 * Cd * Cj * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im))
          + 3456 * Cd * Cjz * Real.exp (2 * Real.pi * H)
            * Real.exp (-(2 * Real.pi * τ.im)) := by ring
      _ ≤ 3456 * Cd * Cj * 1 + 3456 * Cd * Cjz * Real.exp (2 * Real.pi * H) * 1 := by
          rw [hE2]
          have h5 : (0 : ℝ) ≤ 3456 * Cd * Cj := by positivity
          have h6 : (0 : ℝ) ≤ 3456 * Cd * Cjz * Real.exp (2 * Real.pi * H) := by positivity
          nlinarith [ht, h5, h6]
      _ = 3456 * Cd * Cj + 3456 * Cd * Cjz * Real.exp (2 * Real.pi * H) := by ring
  have hc2 : ‖(2 : ℂ) * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * (jInvariantFun τ - jInvariantFun z)‖
      ≤ 2 * C4 * K * Cj * (1 + ‖(τ : ℂ)‖) ^ A
        + 2 * C4 * K * Cjz * Real.exp (2 * Real.pi * H) * (1 + ‖(τ : ℂ)‖) ^ A := by
    have h2 : ‖(2 : ℂ) * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)‖
        ≤ 2 * (C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) := by
      rw [norm_mul]
      have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h4]
      exact mul_le_mul_of_nonneg_left hL2 (by norm_num)
    have h3 := nmul2 (by positivity) (by positivity) h2 hJdiff
    refine le_trans h3 ?_
    calc 2 * (C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)))
          * (Cj * Real.exp (2 * Real.pi * τ.im) + Cjz * Real.exp (2 * Real.pi * H))
        = 2 * C4 * K * Cj * (1 + ‖(τ : ℂ)‖) ^ A
            * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im))
          + 2 * C4 * K * Cjz * Real.exp (2 * Real.pi * H) * (1 + ‖(τ : ℂ)‖) ^ A
            * Real.exp (-(2 * Real.pi * τ.im)) := by ring
      _ ≤ 2 * C4 * K * Cj * (1 + ‖(τ : ℂ)‖) ^ A * 1
          + 2 * C4 * K * Cjz * Real.exp (2 * Real.pi * H) * (1 + ‖(τ : ℂ)‖) ^ A * 1 := by
          rw [hE2]
          have h5 : (0 : ℝ) ≤ 2 * C4 * K * Cj * (1 + ‖(τ : ℂ)‖) ^ A := by positivity
          have h6 : (0 : ℝ) ≤ 2 * C4 * K * Cjz * Real.exp (2 * Real.pi * H)
              * (1 + ‖(τ : ℂ)‖) ^ A := by positivity
          nlinarith [ht, h5, h6]
      _ = 2 * C4 * K * Cj * (1 + ‖(τ : ℂ)‖) ^ A
          + 2 * C4 * K * Cjz * Real.exp (2 * Real.pi * H) * (1 + ‖(τ : ℂ)‖) ^ A := by ring
  have hc3 : ‖(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ
        + 1728 * Alpha ℓ 24 2 τ‖
      ≤ C4 * K * Cj * (1 + ‖(τ : ℂ)‖) ^ A
        + 1728 * (Cs4 * C4 ^ 2) * (1 + ‖(τ : ℂ)‖) ^ A := by
    have h5 : ‖(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ‖
        ≤ C4 * K * Cj * (1 + ‖(τ : ℂ)‖) ^ A := by
      have h6 := nmul2 (by positivity) (by positivity) hL2 hjt
      refine le_trans h6 ?_
      rw [show C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))
            * (Cj * Real.exp (2 * Real.pi * τ.im))
          = C4 * K * Cj * (1 + ‖(τ : ℂ)‖) ^ A
            * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im)) by ring,
        hE2, mul_one]
    have h7 : ‖(1728 : ℂ) * Alpha ℓ 24 2 τ‖
        ≤ 1728 * (Cs4 * C4 ^ 2) * (1 + ‖(τ : ℂ)‖) ^ A := by
      rw [norm_mul]
      have h4 : ‖(1728 : ℂ)‖ = 1728 := by norm_num
      rw [h4]
      have h8 : 1728 * ‖Alpha ℓ 24 2 τ‖ ≤ 1728 * (Cs4 * C4 ^ 2 * (1 + ‖(τ : ℂ)‖) ^ A) :=
        mul_le_mul_of_nonneg_left hL3 (by norm_num)
      linarith [h8]
    linarith [norm_add_le ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ)
      ((1728 : ℂ) * Alpha ℓ 24 2 τ), h5, h7,
      norm_nonneg ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ),
      norm_nonneg ((1728 : ℂ) * Alpha ℓ 24 2 τ)]
  have hCtot : ‖((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
        * (jInvariantFun τ - jInvariantFun z)
      + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ)‖
      ≤ (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
          + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
          + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A := by
    have hcoef : ((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
          * (jInvariantFun τ - jInvariantFun z)
        + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ)
        = (-3456 : ℂ) * Alpha ℓ 24 0 τ * (jInvariantFun τ - jInvariantFun z)
          + (2 : ℂ) * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * (jInvariantFun τ - jInvariantFun z)
          + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) := by
      ring
    rw [hcoef]
    have hsum := norm_add_le (((-3456 : ℂ) * Alpha ℓ 24 0 τ * (jInvariantFun τ - jInvariantFun z))
        + (2 : ℂ) * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * (jInvariantFun τ - jInvariantFun z))
      ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ)
    have hsum2 := norm_add_le ((-3456 : ℂ) * Alpha ℓ 24 0 τ * (jInvariantFun τ - jInvariantFun z))
      ((2 : ℂ) * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * (jInvariantFun τ - jInvariantFun z))
    have hK1 : (0 : ℝ) ≤ 3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
        + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
        + 1728 * (Cs4 * C4 ^ 2) := by positivity
    have heH : (0 : ℝ) ≤ Real.exp (2 * Real.pi * H) := (Real.exp_pos _).le
    nlinarith [hc1, hc2, hc3, hsum, hsum2, hMA, hM0, heH, hK1,
      hCd.le, hCj.le, hCjz.le, hC4.le, hK.le, hCs4.le,
      norm_nonneg ((-3456 : ℂ) * Alpha ℓ 24 0 τ * (jInvariantFun τ - jInvariantFun z)),
      norm_nonneg ((2 : ℂ) * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * (jInvariantFun τ - jInvariantFun z))]
  -- the three terms of `T24`
  have hT24 : T24 ℓ τ z = -(3456 : ℂ) * Alpha ℓ 24 0 τ * fk 2 z * ℓ.L_S z
      - (((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
            * (jInvariantFun τ - jInvariantFun z)
          + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ
              + 1728 * Alpha ℓ 24 2 τ)) * VFun z
      + (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * fk (-2) z * (UFun z ^ 2 - WFun z ^ 2) := by
    simp only [T24]
  have hterm1 : ‖-(3456 : ℂ) * Alpha ℓ 24 0 τ * fk 2 z * ℓ.L_S z‖
      ≤ 3456 * Cd * Cf2 * (1 + ‖(τ : ℂ)‖) ^ A := by
    have h1 : ‖-(3456 : ℂ) * Alpha ℓ 24 0 τ‖
        ≤ 3456 * (Cd * Real.exp (-(2 * Real.pi * τ.im))) := by
      rw [show -(3456 : ℂ) * Alpha ℓ 24 0 τ = -((3456 : ℂ) * Alpha ℓ 24 0 τ) by ring, norm_neg,
        norm_mul]
      have h4 : ‖(3456 : ℂ)‖ = 3456 := by norm_num
      rw [h4]
      exact mul_le_mul_of_nonneg_left hL1 (by norm_num)
    have h3 : ‖-(3456 : ℂ) * Alpha ℓ 24 0 τ * fk 2 z * ℓ.L_S z‖
        = ‖-(3456 : ℂ) * Alpha ℓ 24 0 τ * (fk 2 z * ℓ.L_S z)‖ := by ring_nf
    rw [h3]
    have h2 := nmul2 (by positivity) (by positivity) h1 (hfk2 z hz hzH)
    refine le_trans h2 ?_
    have ht : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
    have hbound : Real.exp (-(2 * Real.pi * τ.im)) ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
      le_trans ht hMA
    rw [show 3456 * (Cd * Real.exp (-(2 * Real.pi * τ.im))) * Cf2
        = 3456 * Cd * Cf2 * Real.exp (-(2 * Real.pi * τ.im)) by ring]
    exact mul_le_mul_of_nonneg_left hbound (by positivity)
  have hterm2 : ‖((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
          * (jInvariantFun τ - jInvariantFun z)
        + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ)‖
        * ‖VFun z‖
      ≤ (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
          + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
          + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A * CVz := by
    have hK1 : (0 : ℝ) ≤ 3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
        + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
        + 1728 * (Cs4 * C4 ^ 2) := by positivity
    have hK1A : (0 : ℝ) ≤ (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
        + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
        + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A :=
      mul_nonneg hK1 hM0
    calc ‖((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
            * (jInvariantFun τ - jInvariantFun z)
          + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ)‖
          * ‖VFun z‖
        ≤ ((3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
            + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
            + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A) * CVz :=
          mul_le_mul hCtot (hVz z hz) (norm_nonneg _) hK1A
      _ = (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
            + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
            + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A * CVz := by ring
  have hterm3 : ‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * fk (-2) z * (UFun z ^ 2 - WFun z ^ 2)‖
      ≤ C4 * K * Cfm * (1 + ‖(τ : ℂ)‖) ^ A := by
    have h1 : ‖Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ‖
        ≤ C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
      rw [show Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ = -(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) by ring,
        norm_neg]
      exact hL2
    have h3 : ‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * fk (-2) z * (UFun z ^ 2 - WFun z ^ 2)‖
        = ‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * (fk (-2) z * (UFun z ^ 2 - WFun z ^ 2))‖ := by
      ring_nf
    rw [h3]
    have h2 := nmul2 (by positivity) (by positivity) h1 (hfm z hz hzH)
    refine le_trans h2 ?_
    have ht : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
    have hmain : C4 * K * Cfm * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))
        ≤ C4 * K * Cfm * (1 + ‖(τ : ℂ)‖) ^ A := by
      calc C4 * K * Cfm * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))
          = (C4 * K * Cfm * (1 + ‖(τ : ℂ)‖) ^ A) * Real.exp (-(2 * Real.pi * τ.im)) := by ring
        _ ≤ (C4 * K * Cfm * (1 + ‖(τ : ℂ)‖) ^ A) * 1 :=
            mul_le_mul_of_nonneg_left ht (by positivity)
        _ = C4 * K * Cfm * (1 + ‖(τ : ℂ)‖) ^ A := by ring
    rw [show C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) * Cfm
        = C4 * K * Cfm * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) by ring]
    exact hmain
  rw [hT24]
  have hsplit2 := norm_sub_le (-(3456 : ℂ) * Alpha ℓ 24 0 τ * fk 2 z * ℓ.L_S z)
    ((((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
        * (jInvariantFun τ - jInvariantFun z)
      + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ))
      * VFun z)
  have hsplit3 := norm_add_le (-(3456 : ℂ) * Alpha ℓ 24 0 τ * fk 2 z * ℓ.L_S z
      - (((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
          * (jInvariantFun τ - jInvariantFun z)
        + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ))
        * VFun z)
    ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * fk (-2) z * (UFun z ^ 2 - WFun z ^ 2))
  have hb2' : ‖(((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
        * (jInvariantFun τ - jInvariantFun z)
      + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ))
      * VFun z‖
      ≤ (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
          + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
          + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A * CVz := by
    rw [norm_mul]
    exact hterm2
  have hfin : ‖-(3456 : ℂ) * Alpha ℓ 24 0 τ * fk 2 z * ℓ.L_S z
      - (((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
          * (jInvariantFun τ - jInvariantFun z)
        + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ))
        * VFun z
      + (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * fk (-2) z * (UFun z ^ 2 - WFun z ^ 2)‖
      ≤ 3456 * Cd * Cf2 * (1 + ‖(τ : ℂ)‖) ^ A
        + (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
          + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
          + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A * CVz
        + C4 * K * Cfm * (1 + ‖(τ : ℂ)‖) ^ A := by
    have hnorm2 : ‖(((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
          * (jInvariantFun τ - jInvariantFun z)
        + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ))
        * VFun z‖
        = ‖((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
            * (jInvariantFun τ - jInvariantFun z)
          + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ)‖
          * ‖VFun z‖ := norm_mul _ _
    linarith [hsplit3, hsplit2, hterm1, hb2', hterm3, hnorm2,
      norm_nonneg (-(3456 : ℂ) * Alpha ℓ 24 0 τ * fk 2 z * ℓ.L_S z),
      norm_nonneg ((((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
        * (jInvariantFun τ - jInvariantFun z)
      + ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ))
      * VFun z)]
  refine le_trans hfin ?_
  have hK1 : (0 : ℝ) ≤ 3456 * Cd * Cf2 + (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
      + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
      + 1728 * (Cs4 * C4 ^ 2)) * CVz + C4 * K * Cfm := by positivity
  have hKe : (1 : ℝ) ≤ Real.exp (Real.pi * H) * Real.exp (-(Real.pi * z.im)) := by
    rw [← Real.exp_add]
    rw [Real.one_le_exp_iff]
    nlinarith [Real.pi_pos, hz, hzH]
  calc 3456 * Cd * Cf2 * (1 + ‖(τ : ℂ)‖) ^ A
        + (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
          + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
          + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A * CVz
        + C4 * K * Cfm * (1 + ‖(τ : ℂ)‖) ^ A
      = (3456 * Cd * Cf2 + (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
          + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
          + 1728 * (Cs4 * C4 ^ 2)) * CVz + C4 * K * Cfm) * (1 + ‖(τ : ℂ)‖) ^ A := by ring
    _ ≤ ((3456 * Cd * Cf2 + (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
          + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
          + 1728 * (Cs4 * C4 ^ 2)) * CVz + C4 * K * Cfm + 1) * Real.exp (Real.pi * H) + 1)
        * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
        have h4 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := hM0
        have h5 : (0 : ℝ) ≤ Real.exp (-(Real.pi * z.im)) := hexp.le
        have h7 : (0 : ℝ) ≤ Real.exp (Real.pi * H) := (Real.exp_pos _).le
        have hbase : (0 : ℝ) ≤ 3456 * Cd * Cf2 + (3456 * Cd * (Cj + Cjz * Real.exp (2 * Real.pi * H))
            + 3 * (C4 * K * Cj) + 2 * (C4 * K * Cjz * Real.exp (2 * Real.pi * H))
            + 1728 * (Cs4 * C4 ^ 2)) * CVz + C4 * K * Cfm := hK1
        nlinarith [h4, h5, h7, hbase, hKe, mul_nonneg h4 h5,
          mul_nonneg (mul_nonneg h4 h5) h7,
          mul_le_mul_of_nonneg_right hKe h4]

/-! ## Products of at most four factors -/

private lemma prod2_le (a : ℂ) (A : ℝ) (ha : ‖a‖ ≤ A) (b : ℂ) (B : ℝ) (hb : ‖b‖ ≤ B) :
    ‖a * b‖ ≤ A * B := by
  have hA : 0 ≤ A := le_trans (norm_nonneg a) ha
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg b) hA

private lemma prod3_le (a : ℂ) (A : ℝ) (ha : ‖a‖ ≤ A) (b : ℂ) (B : ℝ) (hb : ‖b‖ ≤ B)
    (c : ℂ) (C : ℝ) (hc : ‖c‖ ≤ C) : ‖a * b * c‖ ≤ A * B * C := by
  have hA : 0 ≤ A := le_trans (norm_nonneg a) ha
  have hB : 0 ≤ B := le_trans (norm_nonneg b) hb
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul ha hb (norm_nonneg b) hA) hc (norm_nonneg c) (mul_nonneg hA hB)

private lemma prod4_le (a : ℂ) (A : ℝ) (ha : ‖a‖ ≤ A) (b : ℂ) (B : ℝ) (hb : ‖b‖ ≤ B)
    (c : ℂ) (C : ℝ) (hc : ‖c‖ ≤ C) (d : ℂ) (Dd : ℝ) (hd : ‖d‖ ≤ Dd) :
    ‖a * b * c * d‖ ≤ A * B * C * Dd := by
  have hA : 0 ≤ A := le_trans (norm_nonneg a) ha
  have hB : 0 ≤ B := le_trans (norm_nonneg b) hb
  have hC : 0 ≤ C := le_trans (norm_nonneg c) hc
  have h3 : ‖a * b * c‖ ≤ A * B * C := prod3_le a A ha b B hb c C hc
  rw [norm_mul]
  exact mul_le_mul h3 hd (norm_nonneg d) (mul_nonneg (mul_nonneg hA hB) hC)

/-! ## The `d = 24` cusp bound for `T₂₄` -/

private lemma T24_cusp (ℓ : Work.Kernels.LogLambdaData) :
    ∃ H C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (τ z : ℍ), τ ∈ DomainD → (1 : ℝ) / 2 ≤ τ.im → H ≤ z.im →
        ‖T24 ℓ τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨Ha, Ca, hCa, ha⟩ := cusp_fk2
  obtain ⟨Hb, Cb, hCb, hb⟩ := cusp_jz
  obtain ⟨He, Ce, hCe, he⟩ := cusp_fkneg2
  obtain ⟨Hu, Cu, hCu, hu⟩ := cusp_LS ℓ
  obtain ⟨Hv, Cv, hCv, hv⟩ := cusp_V
  obtain ⟨Hw, Cw, hCw, hw⟩ := cusp_UW
  obtain ⟨C4, hC4, hE4⟩ := E4Fun_bdd_half
  obtain ⟨Cs4, hCs4, hpsi4⟩ := psi4_bdd_half ℓ
  obtain ⟨Cj, hCj, hjτ0⟩ := jInvariantFun_grow_half
  obtain ⟨K, Ak, hK, hAk, hkey⟩ := funnel_key ℓ
  obtain ⟨Cd, hCd, hΔu⟩ := DeltaFun_upper_third
  set A : ℝ := max Ak 1 with hA
  have hA0 : 0 ≤ A := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right Ak 1)
  have hAkA : Ak ≤ A := le_max_left Ak 1
  have h1A : (1 : ℝ) ≤ A := le_max_right Ak 1
  set H : ℝ := max (max (max (max (max (max Ha Hb) He) Hu) Hv) Hw) (1 / 3) with hH
  have hHa : Ha ≤ H := by rw [hH]; simp only [le_max_iff, le_refl, true_or, or_true]
  have hHb : Hb ≤ H := by rw [hH]; simp only [le_max_iff, le_refl, true_or, or_true]
  have hHe : He ≤ H := by rw [hH]; simp only [le_max_iff, le_refl, true_or, or_true]
  have hHu : Hu ≤ H := by rw [hH]; simp only [le_max_iff, le_refl, true_or, or_true]
  have hHv : Hv ≤ H := by rw [hH]; simp only [le_max_iff, le_refl, true_or, or_true]
  have hHw : Hw ≤ H := by rw [hH]; simp only [le_max_iff, le_refl, true_or, or_true]
  set CON : ℝ := (55296 * Cd * Ca) + ((16 * (3456 * Cd + 2 * (C4 * K)) * Cj) + ((16 * (3456 * Cd + 2 * (C4 * K)) * Cb) + ((32 * (C4 * K) * Ce) + ((3456 * Cd * Cu) + ((3456 * Cd * Cu * Ca) + (((3456 * Cd + 2 * (C4 * K)) * Cv) + (((3456 * Cd + 2 * (C4 * K)) * Cv * Cj) + (((3456 * Cd + 2 * (C4 * K)) * Cv * Cb) + ((16 * (C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2))) + (((C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * Cv) + ((C4 * K * Cw) + ((C4 * K * Cw * Ce))))))))))))) with hCON
  have hCON0 : 0 < CON := by rw [hCON]; positivity
  refine ⟨H, CON, A, hCON0, hA0, ?_⟩
  intro τ z hτ hτ2 hzH
  have hM1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
    have := norm_nonneg (τ : ℂ); linarith
  have hbase : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith [norm_nonneg (τ : ℂ)]
  have hMt0 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.rpow_nonneg hbase A
  have hMt1 : (1 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.one_le_rpow hM1 hA0
  have hM1A : (1 + ‖(τ : ℂ)‖) ≤ (1 + ‖(τ : ℂ)‖) ^ A := by
    have h := Real.rpow_le_rpow_of_exponent_le hM1 h1A
    rwa [Real.rpow_one] at h
  have hpAk : (1 + ‖(τ : ℂ)‖) ^ Ak ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
    Real.rpow_le_rpow_of_exponent_le hM1 hAkA
  have hEjpos : (0 : ℝ) < Real.exp (-(2 * Real.pi * τ.im)) := Real.exp_pos _
  have hEjle : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
  have hExpmul : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) = 1 := by
    rw [← Real.exp_add, show -(2 * Real.pi * τ.im) + 2 * Real.pi * τ.im = 0 by ring, Real.exp_zero]
  have hE0 : (0 : ℝ) ≤ ‖Ecusp z‖ := norm_nonneg _
  have hEpos : (0 : ℝ) < ‖Ecusp z‖ := by
    rw [norm_Ecusp]; exact Real.exp_pos _
  have hEle : ‖Ecusp z‖ ≤ 1 := by
    rw [norm_Ecusp, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, z.im_pos]
  have hE2le : ‖Ecusp z‖ ^ 2 ≤ 1 := pow_le_one₀ hE0 hEle
  have hEjE2le : Real.exp (-(2 * Real.pi * τ.im)) * ‖Ecusp z‖ ^ 2 ≤ 1 :=
    mul_le_one₀ hEjle (by positivity) hE2le
  have hEjEj2le : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) ≤ 1 :=
    le_of_eq hExpmul
  have hEjEj2E2le : Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) * ‖Ecusp z‖ ^ 2 ≤ 1 := by
    rw [hExpmul, one_mul]; exact hE2le
  have h16 : ‖(16 : ℂ)‖ = 16 := by norm_num
  have h32 : ‖(32 : ℂ)‖ = 32 := by norm_num
  have h55296 : ‖(55296 : ℂ)‖ = 55296 := by norm_num
  have h3456 : ‖(3456 : ℂ)‖ = 3456 := by norm_num
  have hτ0 : ‖Alpha ℓ 24 0 τ‖ ≤ Cd * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
    have h := hΔu τ (by linarith [hτ2] : (1 : ℝ) / 3 ≤ τ.im)
    have h1 : Cd * Real.exp (-(2 * Real.pi * τ.im)) ≤ Cd * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) :=
      le_trans (le_mul_of_one_le_right (by positivity) hMt1) (le_of_eq (by ring))
    calc ‖Alpha ℓ 24 0 τ‖ = ‖DeltaFun τ‖ := by rw [Alpha24_0]
      _ ≤ Cd * Real.exp (-(2 * Real.pi * τ.im)) := h
      _ ≤ Cd * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := h1
  have hτ12 : ‖Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ‖ ≤ C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [Alpha24_comb]
    have h1 := hE4 τ hτ2
    have h2 := hkey τ hτ hτ2
    have h3 : ‖E4Fun τ * (E6Fun τ * psi2 ℓ τ - E4Fun τ * psi4 ℓ τ)‖
        ≤ C4 * (K * (1 + ‖(τ : ℂ)‖) ^ Ak * Real.exp (-(2 * Real.pi * τ.im))) :=
      nmul2 hC4.le (by positivity) h1 h2
    refine le_trans h3 ?_
    have h4 : C4 * (K * (1 + ‖(τ : ℂ)‖) ^ Ak * Real.exp (-(2 * Real.pi * τ.im)))
        ≤ C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) :=
      le_trans (le_of_eq (by ring)) (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpAk (by positivity)) hEjpos.le)
    exact h4
  have hτ21 : ‖Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ‖ ≤ C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [show Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ = -(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) by ring, norm_neg]
    exact hτ12
  have hα2 : ‖Alpha ℓ 24 2 τ‖ ≤ Cs4 * C4 ^ 2 * (1 + ‖(τ : ℂ)‖) ^ A := by
    rw [Alpha24_2]
    have hE4sq : ‖E4Fun τ ^ 2‖ ≤ C4 ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hE4 τ hτ2) 2
    have h := nmul2 (by positivity) (by positivity) (hpsi4 τ hτ hτ2) hE4sq
    have hmid : (Cs4 * (1 + ‖(τ : ℂ)‖)) * C4 ^ 2 ≤ Cs4 * C4 ^ 2 * (1 + ‖(τ : ℂ)‖) ^ A := by
      have hstep : (Cs4 * (1 + ‖(τ : ℂ)‖)) * C4 ^ 2 = Cs4 * C4 ^ 2 * (1 + ‖(τ : ℂ)‖) := by ring
      rw [hstep]
      exact mul_le_mul_of_nonneg_left hM1A (by positivity)
    exact le_trans h hmid
  have hjτz : ‖jInvariantFun τ‖ ≤ Cj * Real.exp (2 * Real.pi * τ.im) := hjτ0 τ hτ2
  have hτco : ‖-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)‖ ≤ (3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
    have h1 : ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ‖ ≤ 3456 * Cd * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
      rw [norm_mul, (by norm_num : ‖(-3456 : ℂ)‖ = 3456)]
      exact le_trans (mul_le_mul_of_nonneg_left hτ0 (by norm_num)) (le_of_eq (by ring))
    have h2 : ‖(2 : ℂ) * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)‖ ≤ 2 * C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
      rw [norm_mul, (by norm_num : ‖(2 : ℂ)‖ = 2)]
      exact le_trans (mul_le_mul_of_nonneg_left hτ12 (by norm_num)) (le_of_eq (by ring))
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add h1 h2) (le_of_eq (by ring)))
  have hτnco : ‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ))‖ ≤ (3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [norm_neg]; exact hτco
  have hτjc : ‖(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ‖ ≤ (C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A := by
    have hj1 : ‖(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ‖ ≤ C4 * K * Cj * (1 + ‖(τ : ℂ)‖) ^ A := by
      have h := nmul2 (by positivity) (by positivity) hτ12 hjτz
      have hstep : (C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Cj * Real.exp (2 * Real.pi * τ.im))
          = C4 * K * Cj * (1 + ‖(τ : ℂ)‖) ^ A := by
        rw [show (C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Cj * Real.exp (2 * Real.pi * τ.im))
            = C4 * K * Cj * (1 + ‖(τ : ℂ)‖) ^ A * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im)) by ring]
        rw [hExpmul, mul_one]
      exact le_trans h (le_of_eq hstep)
    have hj2 : ‖(1728 : ℂ) * Alpha ℓ 24 2 τ‖ ≤ 1728 * (Cs4 * C4 ^ 2) * (1 + ‖(τ : ℂ)‖) ^ A := by
      rw [norm_mul, (by norm_num : ‖(1728 : ℂ)‖ = 1728)]
      exact le_trans (mul_le_mul_of_nonneg_left hα2 (by norm_num)) (le_of_eq (by ring))
    refine le_trans (norm_add_le _ _) (le_trans (add_le_add hj1 hj2) (le_of_eq (by ring)))
  have hτnjc : ‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ)‖ ≤ (C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A := by
    rw [norm_neg]; exact hτjc
  have hzA : ‖eA τ z‖ ≤ Ca * ‖Ecusp z‖ ^ 2 := by
    have h := ha z (le_trans hHa hzH)
    have heq : eA τ z = fk 2 z * Ecusp z ^ 2 - 1 := by simp only [eA, Ecusp_eq_Ept]
    rw [heq]; exact h
  have hzE : ‖eE τ z‖ ≤ Ce * ‖Ecusp z‖ ^ 2 := by
    have h := he z (le_trans hHe hzH)
    have heq : eE τ z = fk (-2) z * Ecusp z ^ 2 - 1 := by simp only [eE, Ecusp_eq_Ept]
    rw [heq]; exact h
  have hzU : ‖eU ℓ z‖ ≤ Cu * ‖Ecusp z‖ ^ 3 := by
    have h := hu z (le_trans hHu hzH)
    have heq : eU ℓ z = ℓ.L_S z + 16 * Ecusp z := by simp only [eU, Ecusp_eq_Ept]
    rw [heq]; exact h
  have hzV : ‖eV z‖ ≤ Cv * ‖Ecusp z‖ ^ 3 := by
    have h := hv z (le_trans hHv hzH)
    have heq : eV z = VFun z - 16 * Ecusp z := by simp only [eV, Ecusp_eq_Ept]
    rw [heq]; exact h
  have hzW : ‖eW z‖ ≤ Cw * ‖Ecusp z‖ ^ 3 := by
    have h := hw z (le_trans hHw hzH)
    have heq : eW z = UFun z ^ 2 - WFun z ^ 2 - 32 * Ecusp z := by simp only [eW, Ecusp_eq_Ept]
    rw [heq]; exact h
  have hzJ : ‖jInvariantFun z * Ecusp z ^ 2 - 1‖ ≤ Cb * ‖Ecusp z‖ ^ 2 :=
    hb z (le_trans hHb hzH)
  have hE3b : ‖Ecusp z ^ 3‖ ≤ ‖Ecusp z‖ ^ 3 := by rw [norm_pow]
  have hE2b : ‖Ecusp z ^ 2‖ ≤ ‖Ecusp z‖ ^ 2 := by rw [norm_pow]
  have hLHS : T24 ℓ τ z * Ecusp z ^ 2
      = -(3456 * Alpha ℓ 24 0 τ) * (1 + eA τ z) * (-16 * Ecusp z + eU ℓ z)
        - (-3456 * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ) * (-1 + eB τ z)
          * (16 * Ecusp z + eV z)
        - ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ)
          * (16 * Ecusp z ^ 3 + eV z * Ecusp z ^ 2)
        + (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * (1 + eE τ z) * (32 * Ecusp z + eW z) := by
    simp only [T24, eA, eB, eE, eU, eV, eW, Ecusp_eq_Ept]
    ring
  have hcanc := T24_cancellation (Alpha ℓ 24 0 τ) (Alpha ℓ 24 1 τ) (Alpha ℓ 24 2 τ)
    (jInvariantFun τ) (Ecusp z) (eA τ z) (eB τ z) (eE τ z) (eU ℓ z) (eV z) (eW z)
  have hRHS_form : T24 ℓ τ z * Ecusp z ^ 2 = 55296 * Alpha ℓ 24 0 τ * eA τ z * Ecusp z + ((-16 : ℂ) * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * jInvariantFun τ * Ecusp z ^ 3 + (16 * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * (jInvariantFun z * Ecusp z ^ 2 - 1) * Ecusp z + (32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z + (-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2 + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1) + ((-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z)))))))))))) := by
    rw [hLHS, hcanc]
    simp only [eB, Ecusp_eq_Ept]
    ring
  have hP1 : ‖55296 * Alpha ℓ 24 0 τ * eA τ z * Ecusp z‖ ≤ 55296 * Cd * Ca * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod4_le (55296 : ℂ) 55296 (le_of_eq (by norm_num : ‖(55296 : ℂ)‖ = 55296)) (Alpha ℓ 24 0 τ) (Cd * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) hτ0 (eA τ z) (Ca * ‖Ecusp z‖ ^ 2) hzA (Ecusp z) ‖Ecusp z‖ (le_refl _)
    exact le_trans h (le_trans (le_of_eq (by ring : 55296 * (Cd * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Ca * ‖Ecusp z‖ ^ 2) * ‖Ecusp z‖ = (55296 * Cd * Ca * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (Real.exp (-(2 * Real.pi * τ.im))))) (mul_le_of_le_one_right (by positivity) (hEjle)))
  have hP2 : ‖(-16 : ℂ) * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * jInvariantFun τ * Ecusp z ^ 3‖ ≤ 16 * (3456 * Cd + 2 * (C4 * K)) * Cj * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod4_le (-16 : ℂ) 16 (le_of_eq (by norm_num : ‖(-16 : ℂ)‖ = 16)) (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) ((3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) hτco (jInvariantFun τ) (Cj * Real.exp (2 * Real.pi * τ.im)) hjτz (Ecusp z ^ 3) (‖Ecusp z‖ ^ 3) hE3b
    exact le_trans h (le_trans (le_of_eq (by ring : 16 * ((3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Cj * Real.exp (2 * Real.pi * τ.im)) * ‖Ecusp z‖ ^ 3 = (16 * (3456 * Cd + 2 * (C4 * K)) * Cj * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im)))) (mul_le_of_le_one_right (by positivity) (hEjEj2le)))
  have hP3 : ‖16 * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * (jInvariantFun z * Ecusp z ^ 2 - 1) * Ecusp z‖ ≤ 16 * (3456 * Cd + 2 * (C4 * K)) * Cb * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod4_le (16 : ℂ) 16 (le_of_eq (by norm_num : ‖(16 : ℂ)‖ = 16)) (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) ((3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) hτco (jInvariantFun z * Ecusp z ^ 2 - 1) (Cb * ‖Ecusp z‖ ^ 2) hzJ (Ecusp z) ‖Ecusp z‖ (le_refl _)
    exact le_trans h (le_trans (le_of_eq (by ring : 16 * ((3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Cb * ‖Ecusp z‖ ^ 2) * ‖Ecusp z‖ = (16 * (3456 * Cd + 2 * (C4 * K)) * Cb * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (Real.exp (-(2 * Real.pi * τ.im))))) (mul_le_of_le_one_right (by positivity) (hEjle)))
  have hP4 : ‖32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z‖ ≤ 32 * (C4 * K) * Ce * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod4_le (32 : ℂ) 32 (le_of_eq (by norm_num : ‖(32 : ℂ)‖ = 32)) (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) (C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) hτ21 (eE τ z) (Ce * ‖Ecusp z‖ ^ 2) hzE (Ecusp z) ‖Ecusp z‖ (le_refl _)
    exact le_trans h (le_trans (le_of_eq (by ring : 32 * (C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Ce * ‖Ecusp z‖ ^ 2) * ‖Ecusp z‖ = (32 * (C4 * K) * Ce * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (Real.exp (-(2 * Real.pi * τ.im))))) (mul_le_of_le_one_right (by positivity) (hEjle)))
  have hP5 : ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z‖ ≤ 3456 * Cd * Cu * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod3_le (-3456 : ℂ) 3456 (le_of_eq (by norm_num : ‖(-3456 : ℂ)‖ = 3456)) (Alpha ℓ 24 0 τ) (Cd * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) hτ0 (eU ℓ z) (Cu * ‖Ecusp z‖ ^ 3) hzU
    exact le_trans h (le_trans (le_of_eq (by ring : 3456 * (Cd * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Cu * ‖Ecusp z‖ ^ 3) = (3456 * Cd * Cu * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (Real.exp (-(2 * Real.pi * τ.im))))) (mul_le_of_le_one_right (by positivity) (hEjle)))
  have hP6 : ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z‖ ≤ 3456 * Cd * Cu * Ca * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod4_le (-3456 : ℂ) 3456 (le_of_eq (by norm_num : ‖(-3456 : ℂ)‖ = 3456)) (Alpha ℓ 24 0 τ) (Cd * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) hτ0 (eU ℓ z) (Cu * ‖Ecusp z‖ ^ 3) hzU (eA τ z) (Ca * ‖Ecusp z‖ ^ 2) hzA
    exact le_trans h (le_trans (le_of_eq (by ring : 3456 * (Cd * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Cu * ‖Ecusp z‖ ^ 3) * (Ca * ‖Ecusp z‖ ^ 2) = (3456 * Cd * Cu * Ca * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (Real.exp (-(2 * Real.pi * τ.im)) * ‖Ecusp z‖ ^ 2))) (mul_le_of_le_one_right (by positivity) (hEjE2le)))
  have hP7 : ‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z‖ ≤ (3456 * Cd + 2 * (C4 * K)) * Cv * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod2_le (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) ((3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) hτco (eV z) (Cv * ‖Ecusp z‖ ^ 3) hzV
    exact le_trans h (le_trans (le_of_eq (by ring : ((3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Cv * ‖Ecusp z‖ ^ 3) = ((3456 * Cd + 2 * (C4 * K)) * Cv * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (Real.exp (-(2 * Real.pi * τ.im))))) (mul_le_of_le_one_right (by positivity) (hEjle)))
  have hP8 : ‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2‖ ≤ (3456 * Cd + 2 * (C4 * K)) * Cv * Cj * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod4_le (-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ))) ((3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) hτnco (eV z) (Cv * ‖Ecusp z‖ ^ 3) hzV (jInvariantFun τ) (Cj * Real.exp (2 * Real.pi * τ.im)) hjτz (Ecusp z ^ 2) (‖Ecusp z‖ ^ 2) hE2b
    exact le_trans h (le_trans (le_of_eq (by ring : ((3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Cv * ‖Ecusp z‖ ^ 3) * (Cj * Real.exp (2 * Real.pi * τ.im)) * ‖Ecusp z‖ ^ 2 = ((3456 * Cd + 2 * (C4 * K)) * Cv * Cj * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (2 * Real.pi * τ.im) * ‖Ecusp z‖ ^ 2))) (mul_le_of_le_one_right (by positivity) (hEjEj2E2le)))
  have hP9 : ‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ ≤ (3456 * Cd + 2 * (C4 * K)) * Cv * Cb * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod3_le (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) ((3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) hτco (eV z) (Cv * ‖Ecusp z‖ ^ 3) hzV (jInvariantFun z * Ecusp z ^ 2 - 1) (Cb * ‖Ecusp z‖ ^ 2) hzJ
    exact le_trans h (le_trans (le_of_eq (by ring : ((3456 * Cd + 2 * (C4 * K)) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Cv * ‖Ecusp z‖ ^ 3) * (Cb * ‖Ecusp z‖ ^ 2) = ((3456 * Cd + 2 * (C4 * K)) * Cv * Cb * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (Real.exp (-(2 * Real.pi * τ.im)) * ‖Ecusp z‖ ^ 2))) (mul_le_of_le_one_right (by positivity) (hEjE2le)))
  have hP10 : ‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ ≤ 16 * (C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod3_le (-16 : ℂ) 16 (le_of_eq (by norm_num : ‖(-16 : ℂ)‖ = 16)) ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) ((C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A) hτjc (Ecusp z ^ 3) (‖Ecusp z‖ ^ 3) hE3b
    exact le_trans h (le_trans (le_of_eq (by ring : 16 * ((C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A) * ‖Ecusp z‖ ^ 3 = (16 * (C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * 1)) (mul_le_of_le_one_right (by positivity) (le_refl 1)))
  have hP11 : ‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ ≤ (C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * Cv * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod3_le (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ)) ((C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A) hτnjc (eV z) (Cv * ‖Ecusp z‖ ^ 3) hzV (Ecusp z ^ 2) (‖Ecusp z‖ ^ 2) hE2b
    exact le_trans h (le_trans (le_of_eq (by ring : ((C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A) * (Cv * ‖Ecusp z‖ ^ 3) * ‖Ecusp z‖ ^ 2 = ((C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * Cv * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (‖Ecusp z‖ ^ 2))) (mul_le_of_le_one_right (by positivity) (hE2le)))
  have hP12 : ‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ ≤ C4 * K * Cw * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod2_le (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) (C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) hτ21 (eW z) (Cw * ‖Ecusp z‖ ^ 3) hzW
    exact le_trans h (le_trans (le_of_eq (by ring : (C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Cw * ‖Ecusp z‖ ^ 3) = (C4 * K * Cw * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (Real.exp (-(2 * Real.pi * τ.im))))) (mul_le_of_le_one_right (by positivity) (hEjle)))
  have hP13 : ‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖ ≤ C4 * K * Cw * Ce * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    have h := prod3_le (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) (C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) hτ21 (eW z) (Cw * ‖Ecusp z‖ ^ 3) hzW (eE τ z) (Ce * ‖Ecusp z‖ ^ 2) hzE
    exact le_trans h (le_trans (le_of_eq (by ring : (C4 * K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(2 * Real.pi * τ.im))) * (Cw * ‖Ecusp z‖ ^ 3) * (Ce * ‖Ecusp z‖ ^ 2) = (C4 * K * Cw * Ce * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) * (Real.exp (-(2 * Real.pi * τ.im)) * ‖Ecusp z‖ ^ 2))) (mul_le_of_le_one_right (by positivity) (hEjE2le)))
  have htrisum13 : ‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖ ≤ ‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖ := le_refl _
  have htrisum12 : ‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z)‖ ≤ ‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum13)
  have htrisum11 : ‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z))‖ ≤ ‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖)) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum12)
  have htrisum10 : ‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z)))‖ ≤ ‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖))) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum11)
  have htrisum9 : ‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1) + ((-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z))))‖ ≤ ‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ + (‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖)))) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum10)
  have htrisum8 : ‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2 + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1) + ((-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z)))))‖ ≤ ‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ + (‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖))))) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum9)
  have htrisum7 : ‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z + (-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2 + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1) + ((-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z))))))‖ ≤ ‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z‖ + (‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ + (‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖)))))) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum8)
  have htrisum6 : ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z + (-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2 + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1) + ((-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z)))))))‖ ≤ ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z‖ + (‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ + (‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖))))))) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum7)
  have htrisum5 : ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z + (-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2 + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1) + ((-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z))))))))‖ ≤ ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z‖ + (‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ + (‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖)))))))) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum6)
  have htrisum4 : ‖32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z + (-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2 + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1) + ((-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z)))))))))‖ ≤ ‖32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z‖ + (‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ + (‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖))))))))) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum5)
  have htrisum3 : ‖16 * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * (jInvariantFun z * Ecusp z ^ 2 - 1) * Ecusp z + (32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z + (-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2 + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1) + ((-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z))))))))))‖ ≤ ‖16 * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * (jInvariantFun z * Ecusp z ^ 2 - 1) * Ecusp z‖ + (‖32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z‖ + (‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ + (‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖)))))))))) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum4)
  have htrisum2 : ‖(-16 : ℂ) * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * jInvariantFun τ * Ecusp z ^ 3 + (16 * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * (jInvariantFun z * Ecusp z ^ 2 - 1) * Ecusp z + (32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z + (-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2 + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1) + ((-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z)))))))))))‖ ≤ ‖(-16 : ℂ) * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * jInvariantFun τ * Ecusp z ^ 3‖ + (‖16 * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * (jInvariantFun z * Ecusp z ^ 2 - 1) * Ecusp z‖ + (‖32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z‖ + (‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ + (‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖))))))))))) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum3)
  have htrisum1 : ‖55296 * Alpha ℓ 24 0 τ * eA τ z * Ecusp z + ((-16 : ℂ) * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * jInvariantFun τ * Ecusp z ^ 3 + (16 * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * (jInvariantFun z * Ecusp z ^ 2 - 1) * Ecusp z + (32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z + (-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2 + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1) + ((-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z))))))))))))‖ ≤ ‖55296 * Alpha ℓ 24 0 τ * eA τ z * Ecusp z‖ + (‖(-16 : ℂ) * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * jInvariantFun τ * Ecusp z ^ 3‖ + (‖16 * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * (jInvariantFun z * Ecusp z ^ 2 - 1) * Ecusp z‖ + (‖32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z‖ + (‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ + (‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖)))))))))))) :=
    le_trans (norm_add_le _ _) (add_le_add (le_refl _) htrisum2)
  have htri : ‖55296 * Alpha ℓ 24 0 τ * eA τ z * Ecusp z + ((-16 : ℂ) * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * jInvariantFun τ * Ecusp z ^ 3 + (16 * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * (jInvariantFun z * Ecusp z ^ 2 - 1) * Ecusp z + (32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z + ((-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z + (-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2 + ((-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1) + ((-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3 + (-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2 + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z + ((Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z))))))))))))‖ ≤ ‖55296 * Alpha ℓ 24 0 τ * eA τ z * Ecusp z‖ + (‖(-16 : ℂ) * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * jInvariantFun τ * Ecusp z ^ 3‖ + (‖16 * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * (jInvariantFun z * Ecusp z ^ 2 - 1) * Ecusp z‖ + (‖32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z‖ + (‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ + (‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖)))))))))))) := htrisum1
  have hsum : ‖55296 * Alpha ℓ 24 0 τ * eA τ z * Ecusp z‖ + (‖(-16 : ℂ) * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * jInvariantFun τ * Ecusp z ^ 3‖ + (‖16 * (-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * (jInvariantFun z * Ecusp z ^ 2 - 1) * Ecusp z‖ + (‖32 * (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eE τ z * Ecusp z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z‖ + (‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * eU ℓ z * eA τ z‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z‖ + (‖-(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * jInvariantFun τ * Ecusp z ^ 2‖ + (‖(-3456 * Alpha ℓ 24 0 τ + 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)) * eV z * (jInvariantFun z * Ecusp z ^ 2 - 1)‖ + (‖(-16 : ℂ) * ((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * Ecusp z ^ 3‖ + (‖-((Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * jInvariantFun τ + 1728 * Alpha ℓ 24 2 τ) * eV z * Ecusp z ^ 2‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z‖ + (‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * eW z * eE τ z‖)))))))))))) ≤ (55296 * Cd * Ca * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((16 * (3456 * Cd + 2 * (C4 * K)) * Cj * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((16 * (3456 * Cd + 2 * (C4 * K)) * Cb * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((32 * (C4 * K) * Ce * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((3456 * Cd * Cu * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((3456 * Cd * Cu * Ca * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + (((3456 * Cd + 2 * (C4 * K)) * Cv * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + (((3456 * Cd + 2 * (C4 * K)) * Cv * Cj * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + (((3456 * Cd + 2 * (C4 * K)) * Cv * Cb * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((16 * (C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + (((C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * Cv * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((C4 * K * Cw * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((C4 * K * Cw * Ce * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3))))))))))))) :=
    (add_le_add hP1 (add_le_add hP2 (add_le_add hP3 (add_le_add hP4 (add_le_add hP5 (add_le_add hP6 (add_le_add hP7 (add_le_add hP8 (add_le_add hP9 (add_le_add hP10 (add_le_add hP11 (add_le_add hP12 hP13))))))))))))
  have hCONS : (55296 * Cd * Ca * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((16 * (3456 * Cd + 2 * (C4 * K)) * Cj * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((16 * (3456 * Cd + 2 * (C4 * K)) * Cb * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((32 * (C4 * K) * Ce * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((3456 * Cd * Cu * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((3456 * Cd * Cu * Ca * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + (((3456 * Cd + 2 * (C4 * K)) * Cv * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + (((3456 * Cd + 2 * (C4 * K)) * Cv * Cj * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + (((3456 * Cd + 2 * (C4 * K)) * Cv * Cb * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((16 * (C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + (((C4 * K * Cj + 1728 * (Cs4 * C4 ^ 2)) * Cv * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((C4 * K * Cw * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3) + ((C4 * K * Cw * Ce * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3))))))))))))) = CON * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
    rw [hCON]; ring
  have hmain : ‖T24 ℓ τ z‖ ≤ CON * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ := by
    have hpos : 0 < ‖Ecusp z‖ ^ 2 := pow_pos hEpos 2
    have h4 : ‖T24 ℓ τ z * Ecusp z ^ 2‖ ≤ CON * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3 := by
      rw [hRHS_form]
      exact le_trans (le_trans htri hsum) (le_of_eq hCONS)
    rw [norm_mul, norm_pow] at h4
    have h5 : ‖T24 ℓ τ z‖ * ‖Ecusp z‖ ^ 2
        ≤ (CON * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖) * ‖Ecusp z‖ ^ 2 := by
      rwa [show CON * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖ ^ 3
            = (CON * (1 + ‖(τ : ℂ)‖) ^ A * ‖Ecusp z‖) * ‖Ecusp z‖ ^ 2 from by ring] at h4
    exact le_of_mul_le_mul_right h5 hpos
  rw [← norm_Ecusp z]
  exact hmain
/-! ## The `Ncusp` bound for `d = 24` -/

private lemma Ncusp_bound_twentyfour (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (τ z : ℍ), τ ∈ DomainD → (1 : ℝ) / 2 ≤ τ.im → (1 : ℝ) / 3 ≤ z.im →
        ‖Ncusp ℓ 24 τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨H, C1, A1, hC1, hA1, hb1⟩ := T24_cusp ℓ
  obtain ⟨C2, A2, hC2, hA2, hb2⟩ := T24_crude ℓ H
  set A : ℝ := max A1 A2 with hAs
  set K : ℝ := max C1 C2 with hKs
  set Dc : ℝ := ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ with hDc
  have hA0 : 0 ≤ A := le_trans hA1 (le_max_left A1 A2)
  have hK0 : 0 < K := by rw [hKs]; exact lt_of_lt_of_le hC1 (le_max_left C1 C2)
  have hDc0 : (0 : ℝ) ≤ Dc := by rw [hDc]; positivity
  have hCpos : 0 < Dc * K + 1 := by
    have := mul_nonneg hDc0 hK0.le
    linarith
  refine ⟨Dc * K + 1, A, hCpos, hA0, ?_⟩
  intro τ z hτ hτ2 hz3
  have hM1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
    have := norm_nonneg (τ : ℂ); linarith
  have hMt0 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
    Real.rpow_nonneg (by linarith [norm_nonneg (τ : ℂ)]) A
  have hnn : (0 : ℝ) ≤ Real.exp (-(Real.pi * z.im)) := (Real.exp_pos _).le
  have hineq : ‖T24 ℓ τ z‖ ≤ K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
    have hp1 : (1 + ‖(τ : ℂ)‖) ^ A1 ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
      Real.rpow_le_rpow_of_exponent_le hM1 (le_max_left A1 A2)
    have hp2 : (1 + ‖(τ : ℂ)‖) ^ A2 ≤ (1 + ‖(τ : ℂ)‖) ^ A :=
      Real.rpow_le_rpow_of_exponent_le hM1 (le_max_right A1 A2)
    have hC1K : C1 ≤ K := le_max_left C1 C2
    have hC2K : C2 ≤ K := le_max_right C1 C2
    rcases le_or_gt H z.im with hzH | hzH
    · have h := hb1 τ z hτ hτ2 hzH
      refine le_trans h (le_trans (le_of_eq (by ring : C1 * (1 + ‖(τ : ℂ)‖) ^ A1 * Real.exp (-(Real.pi * z.im)) = (C1 * (1 + ‖(τ : ℂ)‖) ^ A1) * Real.exp (-(Real.pi * z.im)))) ?_)
      exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1K (by positivity)) hnn)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp1 hK0.le) hnn)
    · have hzH' : z.im ≤ H := le_of_lt hzH
      have h := hb2 τ z hτ hτ2 hz3 hzH'
      refine le_trans h (le_trans (le_of_eq (by ring : C2 * (1 + ‖(τ : ℂ)‖) ^ A2 * Real.exp (-(Real.pi * z.im)) = (C2 * (1 + ‖(τ : ℂ)‖) ^ A2) * Real.exp (-(Real.pi * z.im)))) ?_)
      exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2K (by positivity)) hnn)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hK0.le) hnn)
  rw [Ncusp_twentyfour_expansion ℓ τ z, norm_mul]
  refine le_trans (mul_le_mul_of_nonneg_left hineq (norm_nonneg _)) ?_
  have h0 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) :=
    mul_nonneg hMt0 hnn
  have hstep : Dc * K * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)))
      ≤ (Dc * K + 1) * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))) :=
    mul_le_mul_of_nonneg_right (by linarith) h0
  rw [hDc] at hstep
  have e1 : ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (K * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)))
      = ‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * K * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))) := by ring
  have e2 : (‖(2 * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * K + 1) * ((1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)))
      = (Dc * K + 1) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im)) := by
    rw [hDc]; ring
  exact le_trans (le_of_eq e1) (le_trans hstep (le_of_eq e2))

/-! ## The half-region slash bound for `K_-` -/

theorem KMinus_slash_bound_half (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (τ z : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD → (1 : ℝ) / 2 ≤ τ.im → 1 / 3 ≤ z.im →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
        ‖(z : ℂ) ^ ((d : ℤ) / 2 - 2) * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨C8, A8, hC8, hA8, hb8⟩ := Ncusp_bound_eight ℓ
  obtain ⟨C24, A24, hC24, hA24, hb24⟩ := Ncusp_bound_twentyfour ℓ
  have hCpos : 0 < max C8 C24 + 1 := by
    have := le_max_left C8 C24; linarith
  refine ⟨max C8 C24 + 1, max A8 A24, hCpos, le_trans hA8 (le_max_left A8 A24), ?_⟩
  intro τ z hτ hτ2 hz hne
  have hM1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
    have := norm_nonneg (τ : ℂ); linarith
  have hnn : (0 : ℝ) ≤ Real.exp (-(Real.pi * z.im)) := (Real.exp_pos _).le
  have hN : ‖Ncusp ℓ d τ z‖
      ≤ (max C8 C24 + 1) * (1 + ‖(τ : ℂ)‖) ^ (max A8 A24) * Real.exp (-(Real.pi * z.im)) := by
    have hp8 : (1 + ‖(τ : ℂ)‖) ^ A8 ≤ (1 + ‖(τ : ℂ)‖) ^ (max A8 A24) :=
      Real.rpow_le_rpow_of_exponent_le hM1 (le_max_left A8 A24)
    have hp24 : (1 + ‖(τ : ℂ)‖) ^ A24 ≤ (1 + ‖(τ : ℂ)‖) ^ (max A8 A24) :=
      Real.rpow_le_rpow_of_exponent_le hM1 (le_max_right A8 A24)
    have hc8 : C8 ≤ max C8 C24 + 1 := by have := le_max_left C8 C24; linarith
    have hc24 : C24 ≤ max C8 C24 + 1 := by have := le_max_right C8 C24; linarith
    rcases hd with rfl | rfl
    · have h := hb8 τ z hτ hτ2 hz
      refine le_trans h (le_trans (le_of_eq (by ring : C8 * (1 + ‖(τ : ℂ)‖) ^ A8 * Real.exp (-(Real.pi * z.im)) = (C8 * (1 + ‖(τ : ℂ)‖) ^ A8) * Real.exp (-(Real.pi * z.im)))) ?_)
      exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc8 (by positivity)) hnn)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp8 (by positivity)) hnn)
    · have h := hb24 τ z hτ hτ2 hz
      refine le_trans h (le_trans (le_of_eq (by ring : C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * Real.exp (-(Real.pi * z.im)) = (C24 * (1 + ‖(τ : ℂ)‖) ^ A24) * Real.exp (-(Real.pi * z.im)))) ?_)
      exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc24 (by positivity)) hnn)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp24 (by positivity)) hnn)
  have hD : Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
  have hkey : (z : ℂ) ^ ((d : ℤ) / 2 - 2) * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)
      = Ncusp ℓ d τ z
        / (Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) := by
    rw [show ((d : ℤ) / 2 - 2) = -(2 - (d : ℤ) / 2) by ring, Ncusp_ident ℓ d hd τ z hne]
    exact (mul_div_cancel_left₀ _ hD).symm
  rw [hkey, norm_div]
  exact div_le_div_of_nonneg_right hN (norm_nonneg _)

end

end Work.Asymptotics
