/-
# Cusp asymptotics of the Eisenstein series on the imaginary axis

The second boundary point of the CKMRV contour integral is the cusp `t → 0` on the imaginary
axis, where the CKMRV kernel is built out of the classical modular forms evaluated at `it`
(`Work.Kernels.Kernels`, Section 4.4 of the paper).  Each `SL(2,ℤ)`-modular form of weight `k`
satisfies `f(-1/τ) = τ^k f(τ)`, so its value at `it` for `t → 0` is that of `i/t` for
`t → ∞` times `t^{-k}`; since the `E_k` tend to `1` at `i∞` this gives the two-sided bounds

  `‖E_k(it)‖ ≍ t^{-k}`   (`t → 0`).

These are the building blocks of the cusp analysis (CKMRV Lemma 4.12 and the contour shift of
Section 5), complementing `Work.Asymptotics.DeltaFun_imagAxis_atZero`
(`‖Δ(it)‖ ≍ t^{-12} e^{-2π/t}`) and `Work.Asymptotics.jInvariantFun_imagAxis_atZero`
(`‖j(it)‖ ≳ e^{2π/t}`).
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero
import Submission.Work.Modular.E4_tendsto_atImInfty
import Submission.Work.Modular.E6_qExpansion_coeff
import Submission.Work.Modular.E2_tendsto_atImInfty
import Submission.Work.Modular.E2_S_smul

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix Filter
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- `E₄` is comparable to `1` near the cusp `i∞`. -/
private theorem E4Fun_comparable_atImInfty :
    ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → (1 / 2 : ℝ) ≤ ‖E4Fun τ‖ ∧ ‖E4Fun τ‖ ≤ 3 / 2 := by
  have hE := Work.Modular.E4_tendsto_atImInfty.eventually
    (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨A, -, hA⟩ := UpperHalfPlane.atImInfty_basis.eventually_iff.mp hE
  refine ⟨A, fun τ hτ => ?_⟩
  have h1 : E4Fun τ ∈ Metric.ball (1 : ℂ) (1 / 2) := hA (by simpa using hτ)
  rw [Metric.mem_ball, Complex.dist_eq] at h1
  have h2 : |‖E4Fun τ‖ - ‖(1 : ℂ)‖| ≤ ‖E4Fun τ - 1‖ := abs_norm_sub_norm_le _ _
  rw [norm_one] at h2
  have h3 : |‖E4Fun τ‖ - 1| < 1 / 2 := lt_of_le_of_lt h2 h1
  rw [abs_lt] at h3
  constructor <;> linarith [h3.1, h3.2]

/-- **The cusp asymptotics of `E₄` at `t → 0`.**  `‖E₄(it)‖` is comparable to `t^{-4}`. -/
theorem E4Fun_imagAxis_atZero :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧
      ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
        c * (t ^ 4)⁻¹ ≤ ‖E4Fun (imagAxis t ht)‖ ∧
        ‖E4Fun (imagAxis t ht)‖ ≤ C * (t ^ 4)⁻¹ := by
  obtain ⟨A, hA⟩ := E4Fun_comparable_atImInfty
  refine ⟨1 / 2, 3 / 2, (max A 1)⁻¹, by norm_num, by norm_num, inv_pos.mpr (by positivity), ?_⟩
  intro t ht htT
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  have hmax : max A 1 ≤ t⁻¹ := (le_inv_comm₀ (by positivity : (0:ℝ) < max A 1) ht).mpr htT
  have him : (imagAxis t⁻¹ hs).im = t⁻¹ := by simp [imagAxis]
  have hA' : A ≤ (imagAxis t⁻¹ hs).im := by
    rw [him]; exact le_trans (le_max_left _ _) hmax
  obtain ⟨hlo, hhi⟩ := hA (imagAxis t⁻¹ hs) hA'
  -- the modular transformation law `E₄(S • it) = (it)^4 E₄(it)`
  have hS : E4Fun (imagAxis t⁻¹ hs) = ((imagAxis t ht : ℍ) : ℂ) ^ 4 * E4Fun (imagAxis t ht) := by
    rw [← imagAxis_smul_S t ht]
    exact KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_E4_slash_S (imagAxis t ht)
  have hn : ‖((imagAxis t ht : ℍ) : ℂ) ^ 4‖ = t ^ 4 := by
    rw [norm_pow]
    have : ‖((imagAxis t ht : ℍ) : ℂ)‖ = t := by
      simp [imagAxis, abs_of_pos ht]
    rw [this]
  have ht4 : (0 : ℝ) < t ^ 4 := pow_pos ht 4
  have hnorm : ‖E4Fun (imagAxis t⁻¹ hs)‖ = t ^ 4 * ‖E4Fun (imagAxis t ht)‖ := by
    rw [hS, norm_mul, hn]
  have hne : (t ^ 4) ≠ 0 := ne_of_gt ht4
  constructor
  · have h2 : (1 / 2 : ℝ) ≤ t ^ 4 * ‖E4Fun (imagAxis t ht)‖ := by
      rw [← hnorm]; exact hlo
    have h3 : (t ^ 4)⁻¹ * (1 / 2) ≤ (t ^ 4)⁻¹ * (t ^ 4 * ‖E4Fun (imagAxis t ht)‖) :=
      mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ht4.le)
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at h3
    calc (1 / 2 : ℝ) * (t ^ 4)⁻¹ = (t ^ 4)⁻¹ * (1 / 2) := by ring
      _ ≤ ‖E4Fun (imagAxis t ht)‖ := h3
  · have h2 : t ^ 4 * ‖E4Fun (imagAxis t ht)‖ ≤ 3 / 2 := by
      rw [← hnorm]; exact hhi
    have h3 : (t ^ 4)⁻¹ * (t ^ 4 * ‖E4Fun (imagAxis t ht)‖) ≤ (t ^ 4)⁻¹ * (3 / 2) :=
      mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ht4.le)
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at h3
    calc ‖E4Fun (imagAxis t ht)‖ ≤ (t ^ 4)⁻¹ * (3 / 2) := h3
      _ = (3 / 2 : ℝ) * (t ^ 4)⁻¹ := by ring

/-- `E₆` tends to its constant term `1` at the cusp `i∞` (mirroring the proof of
`Work.Modular.E4_tendsto_atImInfty`). -/
private theorem E6Fun_tendsto_atImInfty :
    Filter.Tendsto E6Fun UpperHalfPlane.atImInfty (𝓝 (1 : ℂ)) := by
  have hperi : Function.Periodic (Work.Modular.E6 ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL
  have hanalytic : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 Work.Modular.E6) 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hperi
      (ModularForm.holo' ModularForm.E₆) (ModularFormClass.bdd_at_infty ModularForm.E₆)
  have hcomp : Filter.Tendsto
      (fun τ : ℍ ↦ UpperHalfPlane.cuspFunction 1 Work.Modular.E6
        (Function.Periodic.qParam 1 (τ : ℂ)))
      UpperHalfPlane.atImInfty (𝓝 (UpperHalfPlane.cuspFunction 1 Work.Modular.E6 0)) :=
    hanalytic.continuousAt.tendsto.comp (UpperHalfPlane.qParam_tendsto_atImInfty one_pos)
  have hfeq : (fun τ : ℍ ↦ UpperHalfPlane.cuspFunction 1 Work.Modular.E6
      (Function.Periodic.qParam 1 (τ : ℂ))) = Work.Modular.E6 := by
    funext τ
    exact UpperHalfPlane.eq_cuspFunction τ one_ne_zero hperi
  rw [hfeq] at hcomp
  have hval : UpperHalfPlane.cuspFunction 1 Work.Modular.E6 0 = 1 := by
    rw [UpperHalfPlane.cuspFunction_apply_zero one_pos hanalytic hperi,
      ← UpperHalfPlane.qExpansion_coeff_zero one_pos hanalytic hperi]
    simpa using Work.Modular.E6_qExpansion_coeff 0
  rwa [hval] at hcomp

/-- `E₆` is comparable to `1` near the cusp `i∞`. -/
private theorem E6Fun_comparable_atImInfty :
    ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → (1 / 2 : ℝ) ≤ ‖E6Fun τ‖ ∧ ‖E6Fun τ‖ ≤ 3 / 2 := by
  have hE := E6Fun_tendsto_atImInfty.eventually
    (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨A, -, hA⟩ := UpperHalfPlane.atImInfty_basis.eventually_iff.mp hE
  refine ⟨A, fun τ hτ => ?_⟩
  have h1 : E6Fun τ ∈ Metric.ball (1 : ℂ) (1 / 2) := hA (by simpa using hτ)
  rw [Metric.mem_ball, Complex.dist_eq] at h1
  have h2 : |‖E6Fun τ‖ - ‖(1 : ℂ)‖| ≤ ‖E6Fun τ - 1‖ := abs_norm_sub_norm_le _ _
  rw [norm_one] at h2
  have h3 : |‖E6Fun τ‖ - 1| < 1 / 2 := lt_of_le_of_lt h2 h1
  rw [abs_lt] at h3
  constructor <;> linarith [h3.1, h3.2]

/-- **The cusp asymptotics of `E₆` at `t → 0`.**  `‖E₆(it)‖` is comparable to `t^{-6}`. -/
theorem E6Fun_imagAxis_atZero :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧
      ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
        c * (t ^ 6)⁻¹ ≤ ‖E6Fun (imagAxis t ht)‖ ∧
        ‖E6Fun (imagAxis t ht)‖ ≤ C * (t ^ 6)⁻¹ := by
  obtain ⟨A, hA⟩ := E6Fun_comparable_atImInfty
  refine ⟨1 / 2, 3 / 2, (max A 1)⁻¹, by norm_num, by norm_num, inv_pos.mpr (by positivity), ?_⟩
  intro t ht htT
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  have hmax : max A 1 ≤ t⁻¹ := (le_inv_comm₀ (by positivity : (0:ℝ) < max A 1) ht).mpr htT
  have him : (imagAxis t⁻¹ hs).im = t⁻¹ := by simp [imagAxis]
  have hA' : A ≤ (imagAxis t⁻¹ hs).im := by
    rw [him]; exact le_trans (le_max_left _ _) hmax
  obtain ⟨hlo, hhi⟩ := hA (imagAxis t⁻¹ hs) hA'
  have hS : E6Fun (imagAxis t⁻¹ hs) = ((imagAxis t ht : ℍ) : ℂ) ^ 6 * E6Fun (imagAxis t ht) := by
    rw [← imagAxis_smul_S t ht]
    exact KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_E6_slash_S (imagAxis t ht)
  have hn : ‖((imagAxis t ht : ℍ) : ℂ) ^ 6‖ = t ^ 6 := by
    rw [norm_pow]
    have : ‖((imagAxis t ht : ℍ) : ℂ)‖ = t := by simp [imagAxis, abs_of_pos ht]
    rw [this]
  have ht6 : (0 : ℝ) < t ^ 6 := pow_pos ht 6
  have hnorm : ‖E6Fun (imagAxis t⁻¹ hs)‖ = t ^ 6 * ‖E6Fun (imagAxis t ht)‖ := by
    rw [hS, norm_mul, hn]
  have hne : (t ^ 6) ≠ 0 := ne_of_gt ht6
  constructor
  · have h2 : (1 / 2 : ℝ) ≤ t ^ 6 * ‖E6Fun (imagAxis t ht)‖ := by
      rw [← hnorm]; exact hlo
    have h3 : (t ^ 6)⁻¹ * (1 / 2) ≤ (t ^ 6)⁻¹ * (t ^ 6 * ‖E6Fun (imagAxis t ht)‖) :=
      mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ht6.le)
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at h3
    calc (1 / 2 : ℝ) * (t ^ 6)⁻¹ = (t ^ 6)⁻¹ * (1 / 2) := by ring
      _ ≤ ‖E6Fun (imagAxis t ht)‖ := h3
  · have h2 : t ^ 6 * ‖E6Fun (imagAxis t ht)‖ ≤ 3 / 2 := by
      rw [← hnorm]; exact hhi
    have h3 : (t ^ 6)⁻¹ * (t ^ 6 * ‖E6Fun (imagAxis t ht)‖) ≤ (t ^ 6)⁻¹ * (3 / 2) :=
      mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr ht6.le)
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul] at h3
    calc ‖E6Fun (imagAxis t ht)‖ ≤ (t ^ 6)⁻¹ * (3 / 2) := h3
      _ = (3 / 2 : ℝ) * (t ^ 6)⁻¹ := by ring

/-- **The cusp asymptotics of `E₈ = E₄²` at `t → 0`.** -/
theorem E8Fun_imagAxis_atZero :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧
      ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
        c * (t ^ 8)⁻¹ ≤ ‖E8Fun (imagAxis t ht)‖ ∧
        ‖E8Fun (imagAxis t ht)‖ ≤ C * (t ^ 8)⁻¹ := by
  obtain ⟨c, C, T, hc, hC, hT, h⟩ := E4Fun_imagAxis_atZero
  refine ⟨c ^ 2, C ^ 2, T, by positivity, by positivity, hT, fun t ht htT => ?_⟩
  obtain ⟨hlo, hhi⟩ := h (t := t) ht htT
  have ht4 : (0 : ℝ) < t ^ 4 := pow_pos ht 4
  have hn : ‖E8Fun (imagAxis t ht)‖ = ‖E4Fun (imagAxis t ht)‖ ^ 2 := by
    simp only [E8Fun, norm_pow]
  have hpow : t ^ 8 = (t ^ 4) ^ 2 := by ring
  rw [hn, hpow]
  constructor
  · have h1 : (c * (t ^ 4)⁻¹) ^ 2 ≤ ‖E4Fun (imagAxis t ht)‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hc.le (inv_nonneg.mpr ht4.le)) hlo 2
    rwa [mul_pow, inv_pow] at h1
  · have h1 : (‖E4Fun (imagAxis t ht)‖) ^ 2 ≤ (C * (t ^ 4)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hhi 2
    rwa [mul_pow, inv_pow] at h1

/-- **The cusp asymptotics of `E₁₀ = E₄E₆` at `t → 0`.** -/
theorem E10Fun_imagAxis_atZero :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧
      ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
        c * (t ^ 10)⁻¹ ≤ ‖E10Fun (imagAxis t ht)‖ ∧
        ‖E10Fun (imagAxis t ht)‖ ≤ C * (t ^ 10)⁻¹ := by
  obtain ⟨c4, C4, T4, hc4, hC4, hT4, h4⟩ := E4Fun_imagAxis_atZero
  obtain ⟨c6, C6, T6, hc6, hC6, hT6, h6⟩ := E6Fun_imagAxis_atZero
  refine ⟨c4 * c6, C4 * C6, min T4 T6, by positivity, by positivity, lt_min hT4 hT6,
    fun t ht htT => ?_⟩
  have h4' := h4 (t := t) ht (le_trans htT (min_le_left _ _))
  have h6' := h6 (t := t) ht (le_trans htT (min_le_right _ _))
  have h4pos : (0 : ℝ) < t ^ 4 := pow_pos ht 4
  have h6pos : (0 : ℝ) < t ^ 6 := pow_pos ht 6
  have hn : ‖E10Fun (imagAxis t ht)‖ = ‖E4Fun (imagAxis t ht)‖ * ‖E6Fun (imagAxis t ht)‖ := by
    simp only [E10Fun, norm_mul]
  have hpow : t ^ 10 = t ^ 4 * t ^ 6 := by ring
  rw [hn]
  constructor
  · have h6p : (0 : ℝ) ≤ c6 * (t ^ 6)⁻¹ := mul_nonneg hc6.le (inv_nonneg.mpr h6pos.le)
    have h4n : (0 : ℝ) ≤ ‖E4Fun (imagAxis t ht)‖ := norm_nonneg _
    have h := mul_le_mul h4'.1 h6'.1 h6p h4n
    have heq : c4 * c6 * (t ^ 10)⁻¹ = (c4 * (t ^ 4)⁻¹) * (c6 * (t ^ 6)⁻¹) := by
      rw [hpow, mul_inv]; ring
    rw [heq]; exact h
  · have h6p : (0 : ℝ) ≤ ‖E6Fun (imagAxis t ht)‖ := norm_nonneg _
    have h4n : (0 : ℝ) ≤ C4 * (t ^ 4)⁻¹ := mul_nonneg hC4.le (inv_nonneg.mpr h4pos.le)
    have h := mul_le_mul h4'.2 h6'.2 h6p h4n
    have heq : (C4 * (t ^ 4)⁻¹) * (C6 * (t ^ 6)⁻¹) = C4 * C6 * (t ^ 10)⁻¹ := by
      rw [hpow, mul_inv]; ring
    rw [heq] at h; exact h

/-- **The cusp asymptotics of `E₁₄ = E₄²E₆` at `t → 0`.** -/
theorem E14Fun_imagAxis_atZero :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧
      ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
        c * (t ^ 14)⁻¹ ≤ ‖E14Fun (imagAxis t ht)‖ ∧
        ‖E14Fun (imagAxis t ht)‖ ≤ C * (t ^ 14)⁻¹ := by
  obtain ⟨c8, C8, T8, hc8, hC8, hT8, h8⟩ := E8Fun_imagAxis_atZero
  obtain ⟨c6, C6, T6, hc6, hC6, hT6, h6⟩ := E6Fun_imagAxis_atZero
  refine ⟨c8 * c6, C8 * C6, min T8 T6, by positivity, by positivity, lt_min hT8 hT6,
    fun t ht htT => ?_⟩
  have h8' := h8 (t := t) ht (le_trans htT (min_le_left _ _))
  have h6' := h6 (t := t) ht (le_trans htT (min_le_right _ _))
  have h8pos : (0 : ℝ) < t ^ 8 := pow_pos ht 8
  have h6pos : (0 : ℝ) < t ^ 6 := pow_pos ht 6
  have hn : ‖E14Fun (imagAxis t ht)‖
      = ‖E8Fun (imagAxis t ht)‖ * ‖E6Fun (imagAxis t ht)‖ := by
    simp only [E14Fun, E8Fun, norm_mul, norm_pow]
  have hpow : t ^ 14 = t ^ 8 * t ^ 6 := by ring
  rw [hn]
  constructor
  · have h6p : (0 : ℝ) ≤ c6 * (t ^ 6)⁻¹ := mul_nonneg hc6.le (inv_nonneg.mpr h6pos.le)
    have h8n : (0 : ℝ) ≤ ‖E8Fun (imagAxis t ht)‖ := norm_nonneg _
    have h := mul_le_mul h8'.1 h6'.1 h6p h8n
    have heq : c8 * c6 * (t ^ 14)⁻¹ = (c8 * (t ^ 8)⁻¹) * (c6 * (t ^ 6)⁻¹) := by
      rw [hpow, mul_inv]; ring
    rw [heq]; exact h
  · have h6p : (0 : ℝ) ≤ ‖E6Fun (imagAxis t ht)‖ := norm_nonneg _
    have h8n : (0 : ℝ) ≤ C8 * (t ^ 8)⁻¹ := mul_nonneg hC8.le (inv_nonneg.mpr h8pos.le)
    have h := mul_le_mul h8'.2 h6'.2 h6p h8n
    have heq : (C8 * (t ^ 8)⁻¹) * (C6 * (t ^ 6)⁻¹) = C8 * C6 * (t ^ 14)⁻¹ := by
      rw [hpow, mul_inv]; ring
    rw [heq] at h; exact h

/-- `E₂` is comparable to `1` near the cusp `i∞`. -/
private theorem E2Fun_comparable_atImInfty :
    ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → (1 / 2 : ℝ) ≤ ‖E2Fun τ‖ ∧ ‖E2Fun τ‖ ≤ 3 / 2 := by
  have hE := Work.Modular.E2_tendsto_atImInfty.eventually
    (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨A, -, hA⟩ := UpperHalfPlane.atImInfty_basis.eventually_iff.mp hE
  refine ⟨A, fun τ hτ => ?_⟩
  have h1 : E2Fun τ ∈ Metric.ball (1 : ℂ) (1 / 2) := hA (by simpa using hτ)
  rw [Metric.mem_ball, Complex.dist_eq] at h1
  have h2 : |‖E2Fun τ‖ - ‖(1 : ℂ)‖| ≤ ‖E2Fun τ - 1‖ := abs_norm_sub_norm_le _ _
  rw [norm_one] at h2
  have h3 : |‖E2Fun τ‖ - 1| < 1 / 2 := lt_of_le_of_lt h2 h1
  rw [abs_lt] at h3
  constructor <;> linarith [h3.1, h3.2]

/-- **The cusp asymptotics of `E₂` at `t → 0`.**  `‖E₂(it)‖` is comparable to `t^{-2}`; this is
the quasimodular input to the kernel, whose `S`-defect is the constant `-6i/π` in
`Work.Modular.E2_S_smul`. -/
theorem E2Fun_imagAxis_atZero :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧
      ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
        c * (t ^ 2)⁻¹ ≤ ‖E2Fun (imagAxis t ht)‖ ∧
        ‖E2Fun (imagAxis t ht)‖ ≤ C * (t ^ 2)⁻¹ := by
  obtain ⟨A, hA⟩ := E2Fun_comparable_atImInfty
  refine ⟨1 / 4, 2, min (1 / 10) (max A 1)⁻¹, by norm_num, by norm_num,
    lt_min (by norm_num) (inv_pos.mpr (by positivity)), fun t ht htT => ?_⟩
  have hs : 0 < t⁻¹ := inv_pos.mpr ht
  have ht10 : t ≤ 1 / 10 := le_trans htT (min_le_left _ _)
  have hmax : max A 1 ≤ t⁻¹ :=
    (le_inv_comm₀ (by positivity : (0:ℝ) < max A 1) ht).mpr (le_trans htT (min_le_right _ _))
  have him : (imagAxis t⁻¹ hs).im = t⁻¹ := by simp [imagAxis]
  have hA' : A ≤ (imagAxis t⁻¹ hs).im := by
    rw [him]; exact le_trans (le_max_left _ _) hmax
  obtain ⟨hlo, hhi⟩ := hA (imagAxis t⁻¹ hs) hA'
  -- the `S`-transformation law `E₂(S • z) = z² E₂(z) - 6iz/π`
  set x : ℂ := (t : ℂ) * Complex.I with hx
  have hxnorm : ‖x‖ = t := by
    rw [hx, norm_mul]
    simp [abs_of_pos ht]
  have hxne : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hxnorm; linarith
  have hS := Work.Modular.E2_S_smul (imagAxis t ht)
  have hSmul : ModularGroup.S • (imagAxis t ht) = imagAxis t⁻¹ hs := imagAxis_smul_S t ht
  rw [hSmul] at hS
  have hxcoe : ((imagAxis t ht : ℍ) : ℂ) = x := rfl
  rw [hxcoe] at hS
  have hS' : E2Fun (imagAxis t⁻¹ hs) = x ^ 2 * E2Fun (imagAxis t ht)
      - 6 * Complex.I * x / Real.pi := hS
  -- solve for `E₂(it)`
  have hkey : E2Fun (imagAxis t ht)
      = (E2Fun (imagAxis t⁻¹ hs) + 6 * Complex.I * x / Real.pi) / x ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hxne)]
    rw [hS']
    ring
  have hx2 : ‖x ^ 2‖ = t ^ 2 := by rw [norm_pow, hxnorm]
  have ht2 : (0 : ℝ) < t ^ 2 := pow_pos ht 2
  have h6norm : ‖(6 : ℂ) * Complex.I * x / Real.pi‖ = 6 * t / Real.pi := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_of_nonneg Real.pi_pos.le, hxnorm]
  have h6le : ‖(6 : ℂ) * Complex.I * x / Real.pi‖ ≤ 1 / 5 := by
    rw [h6norm, div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three, ht10]
  have hnum_lo : (1 / 4 : ℝ) ≤ ‖E2Fun (imagAxis t⁻¹ hs) + 6 * Complex.I * x / Real.pi‖ := by
    have hsub : ‖E2Fun (imagAxis t⁻¹ hs)‖
        ≤ ‖E2Fun (imagAxis t⁻¹ hs) + 6 * Complex.I * x / Real.pi‖
          + ‖(6 : ℂ) * Complex.I * x / Real.pi‖ := by
      have := norm_sub_le (E2Fun (imagAxis t⁻¹ hs) + 6 * Complex.I * x / Real.pi)
        ((6 : ℂ) * Complex.I * x / Real.pi)
      simpa using this
    linarith [hsub, hlo, h6le]
  have hnum_hi : ‖E2Fun (imagAxis t⁻¹ hs) + 6 * Complex.I * x / Real.pi‖ ≤ 2 := by
    have := norm_add_le (E2Fun (imagAxis t⁻¹ hs)) ((6 : ℂ) * Complex.I * x / Real.pi)
    linarith [this, hhi, h6le]
  have hnorm : ‖E2Fun (imagAxis t ht)‖
      = ‖E2Fun (imagAxis t⁻¹ hs) + 6 * Complex.I * x / Real.pi‖ / t ^ 2 := by
    rw [hkey, norm_div, hx2]
  have hcancel : ∀ a : ℝ, a * (t ^ 2)⁻¹ * t ^ 2 = a := by
    intro a
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt ht2), mul_one]
  constructor
  · rw [hnorm, le_div_iff₀ ht2, hcancel]
    exact hnum_lo
  · rw [hnorm, div_le_iff₀ ht2, hcancel]
    exact hnum_hi

end Work.Asymptotics

