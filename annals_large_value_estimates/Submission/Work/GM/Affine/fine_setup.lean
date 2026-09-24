import Mathlib
import Submission.GM.Interfaces
import Submission.Work.GM.Affine.setup

/-!
# GM §9, the fine case: setup

Vocabulary for the proof of GM Proposition 9.1 in the fine range `M ≤ T^4`
(paper §9, Lemma 9.2 + the downward induction).
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The `m₁`-range `M₁ < |m₁| ≤ 2 M₁`. -/
def R1 (M₁ : ℝ) : Finset ℤ :=
  (Finset.Icc (-⌊2 * M₁⌋) ⌊2 * M₁⌋).filter (fun m => M₁ < |(m : ℝ)|)

/-- The `m₂`-range `M₂ < m₂ ≤ 2 M₂`. -/
def R2 (M₂ : ℝ) : Finset ℤ :=
  (Finset.Icc (1 : ℤ) ⌊2 * M₂⌋).filter (fun m => M₂ < (m : ℝ))

/-- The `m₃`-range `|m₃| ≤ K M₃`. -/
def R3 (K M₃ : ℝ) : Finset ℤ := Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋

/-- The `m₃`-range enlarged to contain the support of `psi1 K (·/M₃)`. -/
def R3ext (K M₃ : ℝ) : Finset ℤ := Finset.Icc (-⌈(K + 1) * M₃⌉) ⌈(K + 1) * M₃⌉

lemma affineSum_eq (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    Submission.GM.affineSum K M₁ M₂ M₃ f u
      = ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3 K M₃,
          f (((m₁ : ℝ) * u + m₃) / m₂) := rfl

/-- The smooth bump `ψ₁` majorising `[-K,K]` and supported in `[-K-1,K+1]`. -/
def psi1 (K x : ℝ) : ℝ :=
  Real.smoothTransition (K + 1 - x) * Real.smoothTransition (K + 1 + x)

lemma psi1_contDiff (K : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (psi1 K) := by
  unfold psi1
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id))

lemma psi1_nonneg (K x : ℝ) : 0 ≤ psi1 K x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma psi1_le_one (K x : ℝ) : psi1 K x ≤ 1 := by
  unfold psi1
  calc Real.smoothTransition (K + 1 - x) * Real.smoothTransition (K + 1 + x)
      ≤ 1 * 1 := mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _) zero_le_one
    _ = 1 := mul_one 1

lemma psi1_eq_one {K x : ℝ} (hx : |x| ≤ K) : psi1 K x = 1 := by
  have h1 : Real.smoothTransition (K + 1 - x) = 1 := by
    rw [Real.smoothTransition.eq_one_iff_one_le]
    rw [abs_le] at hx; linarith [hx.2]
  have h2 : Real.smoothTransition (K + 1 + x) = 1 := by
    rw [Real.smoothTransition.eq_one_iff_one_le]
    rw [abs_le] at hx; linarith [hx.1]
  unfold psi1
  rw [h1, h2, one_mul]

lemma psi1_eq_zero {K x : ℝ} (hx : K + 1 ≤ |x|) : psi1 K x = 0 := by
  unfold psi1
  rcases le_or_gt 0 x with h | h
  · have h1 : |x| = x := abs_of_nonneg h
    rw [h1] at hx
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : K + 1 - x ≤ 0), zero_mul]
  · have h1 : |x| = -x := abs_of_neg h
    rw [h1] at hx
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : K + 1 + x ≤ 0), mul_zero]

lemma abs_div_le_of_mem_R3 {K M₃ : ℝ} (hK : 0 ≤ K) (hM₃ : 0 < M₃) {m : ℤ}
    (hm : m ∈ R3 K M₃) : |(m : ℝ) / M₃| ≤ K := by
  rw [R3, Finset.mem_Icc] at hm
  have h1 : (m : ℝ) ≤ K * M₃ := by
    have : (m : ℝ) ≤ (⌊K * M₃⌋ : ℤ) := by exact_mod_cast hm.2
    exact this.trans (Int.floor_le _)
  have h2 : -(K * M₃) ≤ (m : ℝ) := by
    have : ((-⌊K * M₃⌋ : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
    push_cast at this
    linarith [Int.floor_le (K * M₃)]
  rw [abs_div, abs_of_pos hM₃, div_le_iff₀ hM₃, abs_le]
  exact ⟨by linarith, by linarith⟩

lemma R3_subset_R3ext {K M₃ : ℝ} (hK : 0 ≤ K) (hM₃ : 0 < M₃) :
    R3 K M₃ ⊆ R3ext K M₃ := by
  intro m hm
  rw [R3, Finset.mem_Icc] at hm
  rw [R3ext, Finset.mem_Icc]
  have hle : K * M₃ ≤ (K + 1) * M₃ := by nlinarith
  constructor
  · have h1 : ((-⌊K * M₃⌋ : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
    push_cast at h1
    have h2 : -(K * M₃) ≤ (m : ℝ) := by linarith [Int.floor_le (K * M₃)]
    have h3 : -(((⌈(K + 1) * M₃⌉ : ℤ)) : ℝ) ≤ (m : ℝ) := by
      push_cast
      linarith [Int.le_ceil ((K + 1) * M₃), hle]
    exact_mod_cast h3
  · have h1 : ((m : ℝ)) ≤ (⌊K * M₃⌋ : ℤ) := by exact_mod_cast hm.2
    have h2 : (m : ℝ) ≤ K * M₃ := by
      have h := Int.floor_le (K * M₃); push_cast at h1 ⊢; linarith
    have h3 : (m : ℝ) ≤ ((⌈(K + 1) * M₃⌉ : ℤ) : ℝ) := by
      push_cast
      linarith [Int.le_ceil ((K + 1) * M₃), hle]
    exact_mod_cast h3

/-- GM's majorant `g` of the affine sum: the `m₃`-sum, weighted by the bump `ψ₁`. -/
def gSum (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
    psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + m₃) / m₂)

/-- The affine sum is dominated pointwise by the smoothed majorant `g`. -/
theorem affineSum_le_gSum {K M₁ M₂ M₃ : ℝ} (hK : 0 ≤ K) (hM₃ : 0 < M₃)
    {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (u : ℝ) :
    Submission.GM.affineSum K M₁ M₂ M₃ f u ≤ gSum K M₁ M₂ M₃ f u := by
  rw [affineSum_eq]
  apply Finset.sum_le_sum
  intro m₁ _
  apply Finset.sum_le_sum
  intro m₂ _
  have hcongr : ∑ m₃ ∈ R3 K M₃, f (((m₁ : ℝ) * u + m₃) / m₂)
      = ∑ m₃ ∈ R3 K M₃,
          psi1 K ((m₃ : ℝ) / M₃) * f (((m₁ : ℝ) * u + m₃) / m₂) := by
    refine Finset.sum_congr rfl fun m₃ hm₃ => ?_
    rw [psi1_eq_one]
    · ring
    · exact abs_div_le_of_mem_R3 hK hM₃ hm₃
  rw [hcongr]
  apply Finset.sum_le_sum_of_subset_of_nonneg (R3_subset_R3ext hK hM₃)
  intro m₃ _ _
  exact mul_nonneg (psi1_nonneg _ _) (hf _)

/-- The (complex) Fourier transform of the bump `ψ₁ = psi1 K`. -/
def psi1hat (K : ℝ) (y : ℝ) : ℂ :=
  𝓕 (fun t : ℝ => ((psi1 K t : ℝ) : ℂ)) y

/-- The (complex) Fourier transform of GM's majorant `g = gSum K M₁ M₂ M₃ f`. -/
def ghat (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  𝓕 (fun u : ℝ => ((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) ξ

/-- The smoothing kernel `ψ` of Lemma 9.2. -/
def psiBump : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The smoothing kernel as a function: smooth, non-negative, `∫ψ = 1`, supported in `[-1,1]`,
and `≥ 1` on `[-1/8,1/8]`. -/
def psiSmooth : ℝ → ℝ := psiBump.normed volume

lemma psiSmooth_nonneg (x : ℝ) : 0 ≤ psiSmooth x :=
  ContDiffBump.nonneg_normed (f := psiBump) (μ := volume) x

lemma psiSmooth_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) psiSmooth :=
  ContDiffBump.contDiff_normed (f := psiBump) (μ := volume) (n := ⊤)

lemma psiSmooth_integral : ∫ x, psiSmooth x = 1 :=
  ContDiffBump.integral_normed (f := psiBump) (μ := volume)

lemma psiSmooth_support {x : ℝ} (hx : psiSmooth x ≠ 0) : x ∈ Set.Icc (-1 : ℝ) 1 := by
  have h : x ∈ Function.support (psiBump.normed volume) := by
    rw [Function.mem_support]
    exact hx
  rw [ContDiffBump.support_normed_eq] at h
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at h
  have hr : psiBump.rOut = 1 / 4 := rfl
  rw [abs_lt] at h
  rw [Set.mem_Icc]
  constructor <;> linarith [h.1, h.2, hr]

lemma psiBump_integral_le : ∫ x, (psiBump : ℝ → ℝ) x ∂volume ≤ 1 := by
  have hle : ∀ x, psiBump x ≤ (Metric.ball (0:ℝ) psiBump.rOut).indicator (fun _ => (1:ℝ)) x := by
    intro x
    rcases em (x ∈ Metric.ball (0:ℝ) psiBump.rOut) with hx | hx
    · rw [Set.indicator_of_mem hx]; exact ContDiffBump.le_one (f := psiBump) (x := x)
    · rw [Set.indicator_of_notMem hx]
      have h0 : x ∉ Function.support (psiBump : ℝ → ℝ) := by
        rw [ContDiffBump.support_eq]; exact hx
      rw [Function.mem_support] at h0
      exact le_of_eq (Classical.not_not.mp h0)
  have hint : Integrable ((Metric.ball (0:ℝ) psiBump.rOut).indicator (fun _ => (1:ℝ)) : ℝ → ℝ)
      volume := by
    rw [integrable_indicator_iff measurableSet_ball]
    exact integrableOn_const (s := Metric.ball (0:ℝ) psiBump.rOut)
  calc ∫ x, (psiBump : ℝ → ℝ) x ∂volume
      ≤ ∫ x, (Metric.ball (0:ℝ) psiBump.rOut).indicator (fun _ => (1:ℝ)) x ∂volume :=
        integral_mono (ContDiffBump.integrable (f := psiBump) (μ := volume)) hint
          (fun x => hle x)
    _ = volume.real (Metric.ball (0:ℝ) psiBump.rOut) :=
        MeasureTheory.integral_indicator_one (μ := volume) measurableSet_ball
    _ = 1 / 2 := by
        rw [MeasureTheory.measureReal_def, Real.volume_ball,
          show psiBump.rOut = 1 / 4 from rfl,
          ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2 * (1/4))]
        norm_num
    _ ≤ 1 := by norm_num

lemma psiSmooth_ge_one {x : ℝ} (hx : x ∈ Metric.closedBall (0:ℝ) (1/8)) : 1 ≤ psiSmooth x := by
  have h1 : psiBump x = 1 := ContDiffBump.one_of_mem_closedBall (f := psiBump) hx
  have h2 : 0 < ∫ x, psiBump x ∂volume := ContDiffBump.integral_pos (f := psiBump) (μ := volume)
  have h3 : ∫ x, psiBump x ∂volume ≤ 1 := psiBump_integral_le
  rw [psiSmooth, ContDiffBump.normed_def, h1, one_div, one_le_inv₀ h2]
  exact h3

end

end Work.GM.Affine
