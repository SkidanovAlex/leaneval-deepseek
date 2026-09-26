import Mathlib
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Asymptotics.cusp_U_second
import Submission.Work.Asymptotics.cusp_W_second

namespace Work.Asymptotics

/-- The explicit constant produced by the third-order cusp estimate. -/
private def BigC (a b c d r : ℝ) : ℝ :=
  a + (1 + a) * (b * (b + 2) + d ^ 2 + 2 * (c * (c + 2))
    + (1 + (b * (b + 2) + d ^ 2 + 2 * (c * (c + 2)))) * r)

/-- Positivity of the constant `BigC`. -/
private lemma BigC_pos (a b c d r : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hr : 0 ≤ r) : 0 < BigC a b c d r := by
  unfold BigC
  set K : ℝ := b * (b + 2) + d ^ 2 + 2 * (c * (c + 2)) with hK
  have hKnn : 0 ≤ K := by rw [hK]; nlinarith [hb, hc, hd, sq_nonneg d]
  have h1 : (0 : ℝ) < 1 + a := by linarith
  have h2 : (0 : ℝ) ≤ K + (1 + K) * r := by nlinarith [hKnn, hr]
  have h3 : (0 : ℝ) ≤ (1 + a) * (K + (1 + K) * r) := mul_nonneg h1.le h2
  linarith

/-- Abstract third-order estimate: if `D = e² + O(‖e‖⁴)`, `u = 1 + O(‖e‖)`,
`w = 1 + O(‖e‖)`, `v = O(‖e‖)` and `e8 = 1 + O(‖e‖²)`, then
`D·((u²+v²-2w²)e8) + e² = O(‖e‖³)`. -/
private lemma thirdOrderCore
    (D e u v w e8 : ℂ) (a b c d r : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (he1 : ‖e‖ ≤ 1)
    (hD : ‖D - e ^ 2‖ ≤ a * ‖e‖ ^ 4)
    (hu : ‖u - 1‖ ≤ b * ‖e‖)
    (hw : ‖w - 1‖ ≤ c * ‖e‖)
    (hv : ‖v‖ ≤ d * ‖e‖)
    (he8 : ‖e8 - 1‖ ≤ r * ‖e‖ ^ 2) :
    ‖D * ((u ^ 2 + v ^ 2 - 2 * w ^ 2) * e8) + e ^ 2‖ ≤ BigC a b c d r * ‖e‖ ^ 3 := by
  unfold BigC
  set K1 : ℝ := b * (b + 2) + d ^ 2 + 2 * (c * (c + 2)) with hK1
  have ht0 : (0 : ℝ) ≤ ‖e‖ := norm_nonneg e
  have ht2 : ‖e‖ ^ 2 ≤ ‖e‖ := by simpa using pow_le_pow_of_le_one ht0 he1 (by norm_num : 1 ≤ 2)
  have ht3 : ‖e‖ ^ 3 ≤ ‖e‖ := by simpa using pow_le_pow_of_le_one ht0 he1 (by norm_num : 1 ≤ 3)
  have ht42 : ‖e‖ ^ 4 ≤ ‖e‖ ^ 2 := pow_le_pow_of_le_one ht0 he1 (by norm_num : 2 ≤ 4)
  have ht43 : ‖e‖ ^ 4 ≤ ‖e‖ ^ 3 := pow_le_pow_of_le_one ht0 he1 (by norm_num : 3 ≤ 4)
  have hK1nn : 0 ≤ K1 := by
    rw [hK1]; nlinarith [hb, hc, hd, sq_nonneg d]
  have hu2 : ‖u ^ 2 - 1‖ ≤ b * (b + 2) * ‖e‖ := by
    have hfac : u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
    rw [hfac, norm_mul]
    have hu1 : ‖u + 1‖ ≤ b * ‖e‖ + 2 := by
      have h := norm_add_le (u - 1) (2 : ℂ)
      rw [show (u - 1) + 2 = u + 1 by ring, Complex.norm_ofNat] at h
      linarith
    have hbt : (0 : ℝ) ≤ b * ‖e‖ := mul_nonneg hb ht0
    calc ‖u - 1‖ * ‖u + 1‖ ≤ (b * ‖e‖) * (b * ‖e‖ + 2) :=
          mul_le_mul hu hu1 (norm_nonneg _) hbt
      _ = b ^ 2 * ‖e‖ ^ 2 + 2 * b * ‖e‖ := by ring
      _ ≤ b ^ 2 * ‖e‖ + 2 * b * ‖e‖ := by
            have := mul_le_mul_of_nonneg_left ht2 (sq_nonneg b); linarith
      _ = b * (b + 2) * ‖e‖ := by ring
  have hw2 : ‖w ^ 2 - 1‖ ≤ c * (c + 2) * ‖e‖ := by
    have hfac : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    rw [hfac, norm_mul]
    have hw1 : ‖w + 1‖ ≤ c * ‖e‖ + 2 := by
      have h := norm_add_le (w - 1) (2 : ℂ)
      rw [show (w - 1) + 2 = w + 1 by ring, Complex.norm_ofNat] at h
      linarith
    have hct : (0 : ℝ) ≤ c * ‖e‖ := mul_nonneg hc ht0
    calc ‖w - 1‖ * ‖w + 1‖ ≤ (c * ‖e‖) * (c * ‖e‖ + 2) :=
          mul_le_mul hw hw1 (norm_nonneg _) hct
      _ = c ^ 2 * ‖e‖ ^ 2 + 2 * c * ‖e‖ := by ring
      _ ≤ c ^ 2 * ‖e‖ + 2 * c * ‖e‖ := by
            have := mul_le_mul_of_nonneg_left ht2 (sq_nonneg c); linarith
      _ = c * (c + 2) * ‖e‖ := by ring
  have hv2 : ‖v ^ 2‖ ≤ d ^ 2 * ‖e‖ := by
    rw [norm_pow]
    calc ‖v‖ ^ 2 ≤ (d * ‖e‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hv 2
      _ = d ^ 2 * ‖e‖ ^ 2 := by ring
      _ ≤ d ^ 2 * ‖e‖ := by
            have := mul_le_mul_of_nonneg_left ht2 (sq_nonneg d); linarith
  have hS1 : ‖(u ^ 2 + v ^ 2 - 2 * w ^ 2) + 1‖ ≤ K1 * ‖e‖ := by
    have hkey : (u ^ 2 + v ^ 2 - 2 * w ^ 2) + 1
        = ((u ^ 2 - 1) + v ^ 2) - (2 : ℂ) * (w ^ 2 - 1) := by ring
    rw [hkey]
    have h1 : ‖((u ^ 2 - 1) + v ^ 2) - (2 : ℂ) * (w ^ 2 - 1)‖
        ≤ ‖(u ^ 2 - 1) + v ^ 2‖ + ‖(2 : ℂ) * (w ^ 2 - 1)‖ := norm_sub_le _ _
    have h2 : ‖(u ^ 2 - 1) + v ^ 2‖ ≤ ‖u ^ 2 - 1‖ + ‖v ^ 2‖ := norm_add_le _ _
    have h3 : ‖(2 : ℂ) * (w ^ 2 - 1)‖ = 2 * ‖w ^ 2 - 1‖ := by
      rw [norm_mul, Complex.norm_ofNat]
    rw [h3] at h1
    rw [hK1]
    linarith [h1, h2, hu2, hv2, hw2]
  have hS : ‖u ^ 2 + v ^ 2 - 2 * w ^ 2‖ ≤ 1 + K1 * ‖e‖ := by
    rw [show u ^ 2 + v ^ 2 - 2 * w ^ 2 = ((u ^ 2 + v ^ 2 - 2 * w ^ 2) + 1) - 1 by ring]
    have h := norm_sub_le ((u ^ 2 + v ^ 2 - 2 * w ^ 2) + 1) (1 : ℂ)
    rw [norm_one] at h
    linarith [h, hS1]
  have hB : ‖(u ^ 2 + v ^ 2 - 2 * w ^ 2) * e8 + 1‖ ≤ (K1 + (1 + K1) * r) * ‖e‖ := by
    have hkey : (u ^ 2 + v ^ 2 - 2 * w ^ 2) * e8 + 1
        = ((u ^ 2 + v ^ 2 - 2 * w ^ 2) + 1)
          + (u ^ 2 + v ^ 2 - 2 * w ^ 2) * (e8 - 1) := by ring
    rw [hkey]
    have h1 := norm_add_le ((u ^ 2 + v ^ 2 - 2 * w ^ 2) + 1)
        ((u ^ 2 + v ^ 2 - 2 * w ^ 2) * (e8 - 1))
    have h2 : ‖(u ^ 2 + v ^ 2 - 2 * w ^ 2) * (e8 - 1)‖
        ≤ (1 + K1 * ‖e‖) * (r * ‖e‖ ^ 2) := by
      rw [norm_mul]
      exact mul_le_mul hS he8 (norm_nonneg _) (by positivity)
    have h3 : (1 + K1 * ‖e‖) * (r * ‖e‖ ^ 2) ≤ (1 + K1) * (r * ‖e‖) := by
      have ht32 : ‖e‖ ^ 3 ≤ ‖e‖ ^ 2 := pow_le_pow_of_le_one ht0 he1 (by norm_num : 2 ≤ 3)
      have hA : r * ‖e‖ ^ 2 ≤ r * ‖e‖ := by nlinarith [ht2, ht0, hr]
      have hBl : K1 * (r * ‖e‖ ^ 3) ≤ K1 * (r * ‖e‖ ^ 2) := by
        have h6 : r * ‖e‖ ^ 3 ≤ r * ‖e‖ ^ 2 := by nlinarith [ht32, ht0, hr]
        exact mul_le_mul_of_nonneg_left h6 hK1nn
      nlinarith [hA, hBl, ht0, hK1nn]
    calc ‖((u ^ 2 + v ^ 2 - 2 * w ^ 2) + 1) + (u ^ 2 + v ^ 2 - 2 * w ^ 2) * (e8 - 1)‖
        ≤ ‖(u ^ 2 + v ^ 2 - 2 * w ^ 2) + 1‖
          + ‖(u ^ 2 + v ^ 2 - 2 * w ^ 2) * (e8 - 1)‖ := h1
      _ ≤ K1 * ‖e‖ + (1 + K1 * ‖e‖) * (r * ‖e‖ ^ 2) := by linarith [hS1, h2]
      _ ≤ K1 * ‖e‖ + (1 + K1) * (r * ‖e‖) := by linarith [h3]
      _ = (K1 + (1 + K1) * r) * ‖e‖ := by ring
  have hD4 : ‖D - e ^ 2‖ ≤ a * ‖e‖ ^ 3 := le_trans hD (mul_le_mul_of_nonneg_left ht43 ha)
  have hDn : ‖D‖ ≤ (1 + a) * ‖e‖ ^ 2 := by
    have h1 : ‖D‖ ≤ ‖D - e ^ 2‖ + ‖e‖ ^ 2 := by
      have h := norm_add_le (D - e ^ 2) (e ^ 2)
      rw [sub_add_cancel, norm_pow] at h
      exact h
    calc ‖D‖ ≤ a * ‖e‖ ^ 4 + ‖e‖ ^ 2 := by linarith [h1, hD]
      _ ≤ (1 + a) * ‖e‖ ^ 2 := by nlinarith [ha, ht0, ht42]
  have hkey : D * ((u ^ 2 + v ^ 2 - 2 * w ^ 2) * e8) + e ^ 2
      = (e ^ 2 - D) + D * ((u ^ 2 + v ^ 2 - 2 * w ^ 2) * e8 + 1) := by ring
  rw [hkey]
  have h1 : ‖(e ^ 2 - D) + D * ((u ^ 2 + v ^ 2 - 2 * w ^ 2) * e8 + 1)‖
      ≤ ‖e ^ 2 - D‖ + ‖D‖ * ‖(u ^ 2 + v ^ 2 - 2 * w ^ 2) * e8 + 1‖ := by
    have h := norm_add_le (e ^ 2 - D) (D * ((u ^ 2 + v ^ 2 - 2 * w ^ 2) * e8 + 1))
    rwa [norm_mul] at h
  have h2 : ‖e ^ 2 - D‖ ≤ a * ‖e‖ ^ 3 := by
    rw [norm_sub_rev]; exact hD4
  calc ‖(e ^ 2 - D) + D * ((u ^ 2 + v ^ 2 - 2 * w ^ 2) * e8 + 1)‖
      ≤ ‖e ^ 2 - D‖ + ‖D‖ * ‖(u ^ 2 + v ^ 2 - 2 * w ^ 2) * e8 + 1‖ := h1
    _ ≤ a * ‖e‖ ^ 3 + ((1 + a) * ‖e‖ ^ 2) * ((K1 + (1 + K1) * r) * ‖e‖) := by
        have hm := mul_le_mul hDn hB (norm_nonneg _) (by positivity)
        linarith [h2, hm]
    _ = (a + (1 + a) * (K1 + (1 + K1) * r)) * ‖e‖ ^ 3 := by ring

theorem Delta_xi4prime_E8_third_order :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ
          * ((Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
              - 2 * Work.Kernels.WFun τ ^ 2) * Work.Kernels.E8Fun τ)
        + (Work.Residues.Ept τ) ^ 2‖
        ≤ C * ‖Work.Residues.Ept τ‖ ^ 3 := by
  obtain ⟨Cδ, hCδ, hδ⟩ := Work.Residues.DeltaExpansion
  obtain ⟨CU, hCU, hU⟩ := cusp_U_second
  obtain ⟨CW, hCW, hW⟩ := cusp_W_second
  obtain ⟨CV, hCV, hV⟩ := Work.Residues.VFun_expansion
  obtain ⟨CA, hCA, hE4⟩ := Work.Residues.E4FunSecondOrder
  refine ⟨BigC Cδ (CU + 32) (CW + 32) (CV + 16) ((240 + CA) * (242 + CA)), ?_, ?_⟩
  · exact BigC_pos Cδ (CU + 32) (CW + 32) (CV + 16) ((240 + CA) * (242 + CA))
      hCδ (by positivity) (by positivity) (by positivity) (by positivity)
  · intro τ hτ
    have hu : ‖Work.Kernels.UFun τ - 1‖ ≤ (CU + 32) * ‖Work.Residues.Ept τ‖ := by
      have hUτ := hU τ hτ
      have ht0 : (0 : ℝ) ≤ ‖Work.Residues.Ept τ‖ := norm_nonneg _
      have ht1 : ‖Work.Residues.Ept τ‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one τ)
      have ht2 : ‖Work.Residues.Ept τ‖ ^ 2 ≤ ‖Work.Residues.Ept τ‖ := by
        simpa using pow_le_pow_of_le_one ht0 ht1 (by norm_num : 1 ≤ 2)
      have ht3 : ‖Work.Residues.Ept τ‖ ^ 3 ≤ ‖Work.Residues.Ept τ‖ := by
        simpa using pow_le_pow_of_le_one ht0 ht1 (by norm_num : 1 ≤ 3)
      have hkey : Work.Kernels.UFun τ - 1
          = (Work.Kernels.UFun τ
              - (1 + 8 * Work.Residues.Ept τ + 24 * (Work.Residues.Ept τ) ^ 2))
            + (8 * Work.Residues.Ept τ + 24 * (Work.Residues.Ept τ) ^ 2) := by ring
      rw [hkey]
      have hb : ‖8 * Work.Residues.Ept τ + 24 * (Work.Residues.Ept τ) ^ 2‖
          ≤ 8 * ‖Work.Residues.Ept τ‖ + 24 * ‖Work.Residues.Ept τ‖ ^ 2 := by
        have h := norm_add_le (8 * Work.Residues.Ept τ) (24 * (Work.Residues.Ept τ) ^ 2)
        rw [norm_mul, norm_mul, norm_pow] at h
        simp only [Complex.norm_ofNat] at h
        linarith
      calc ‖(Work.Kernels.UFun τ
              - (1 + 8 * Work.Residues.Ept τ + 24 * (Work.Residues.Ept τ) ^ 2))
            + (8 * Work.Residues.Ept τ + 24 * (Work.Residues.Ept τ) ^ 2)‖
          ≤ ‖Work.Kernels.UFun τ
              - (1 + 8 * Work.Residues.Ept τ + 24 * (Work.Residues.Ept τ) ^ 2)‖
            + ‖8 * Work.Residues.Ept τ + 24 * (Work.Residues.Ept τ) ^ 2‖ := norm_add_le _ _
        _ ≤ CU * ‖Work.Residues.Ept τ‖ ^ 3
              + (8 * ‖Work.Residues.Ept τ‖ + 24 * ‖Work.Residues.Ept τ‖ ^ 2) := by linarith
        _ ≤ (CU + 32) * ‖Work.Residues.Ept τ‖ := by nlinarith [hCU.le, ht0, ht2, ht3]
    have hw : ‖Work.Kernels.WFun τ - 1‖ ≤ (CW + 32) * ‖Work.Residues.Ept τ‖ := by
      have hWτ := hW τ hτ
      have ht0 : (0 : ℝ) ≤ ‖Work.Residues.Ept τ‖ := norm_nonneg _
      have ht1 : ‖Work.Residues.Ept τ‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one τ)
      have ht2 : ‖Work.Residues.Ept τ‖ ^ 2 ≤ ‖Work.Residues.Ept τ‖ := by
        simpa using pow_le_pow_of_le_one ht0 ht1 (by norm_num : 1 ≤ 2)
      have ht3 : ‖Work.Residues.Ept τ‖ ^ 3 ≤ ‖Work.Residues.Ept τ‖ := by
        simpa using pow_le_pow_of_le_one ht0 ht1 (by norm_num : 1 ≤ 3)
      have hkey : Work.Kernels.WFun τ - 1
          = (Work.Kernels.WFun τ
              - (1 - 8 * Work.Residues.Ept τ + 24 * (Work.Residues.Ept τ) ^ 2))
            + (24 * (Work.Residues.Ept τ) ^ 2 - 8 * Work.Residues.Ept τ) := by ring
      rw [hkey]
      have hb : ‖24 * (Work.Residues.Ept τ) ^ 2 - 8 * Work.Residues.Ept τ‖
          ≤ 24 * ‖Work.Residues.Ept τ‖ ^ 2 + 8 * ‖Work.Residues.Ept τ‖ := by
        have h := norm_sub_le (24 * (Work.Residues.Ept τ) ^ 2) (8 * Work.Residues.Ept τ)
        rw [norm_mul, norm_mul, norm_pow] at h
        simp only [Complex.norm_ofNat] at h
        linarith
      calc ‖(Work.Kernels.WFun τ
              - (1 - 8 * Work.Residues.Ept τ + 24 * (Work.Residues.Ept τ) ^ 2))
            + (24 * (Work.Residues.Ept τ) ^ 2 - 8 * Work.Residues.Ept τ)‖
          ≤ ‖Work.Kernels.WFun τ
              - (1 - 8 * Work.Residues.Ept τ + 24 * (Work.Residues.Ept τ) ^ 2)‖
            + ‖24 * (Work.Residues.Ept τ) ^ 2 - 8 * Work.Residues.Ept τ‖ := norm_add_le _ _
        _ ≤ CW * ‖Work.Residues.Ept τ‖ ^ 3
              + (24 * ‖Work.Residues.Ept τ‖ ^ 2 + 8 * ‖Work.Residues.Ept τ‖) := by linarith
        _ ≤ (CW + 32) * ‖Work.Residues.Ept τ‖ := by nlinarith [hCW.le, ht0, ht2, ht3]
    have hv : ‖Work.Kernels.VFun τ‖ ≤ (CV + 16) * ‖Work.Residues.Ept τ‖ := by
      have hVτ := hV τ hτ
      have ht0 : (0 : ℝ) ≤ ‖Work.Residues.Ept τ‖ := norm_nonneg _
      have ht1 : ‖Work.Residues.Ept τ‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one τ)
      have ht3 : ‖Work.Residues.Ept τ‖ ^ 3 ≤ ‖Work.Residues.Ept τ‖ := by
        simpa using pow_le_pow_of_le_one ht0 ht1 (by norm_num : 1 ≤ 3)
      have hkey : Work.Kernels.VFun τ
          = (Work.Kernels.VFun τ - 16 * Work.Residues.Ept τ)
            + 16 * Work.Residues.Ept τ := by ring
      rw [hkey]
      have hb : ‖(16 : ℂ) * Work.Residues.Ept τ‖ = 16 * ‖Work.Residues.Ept τ‖ := by
        rw [norm_mul, Complex.norm_ofNat]
      calc ‖(Work.Kernels.VFun τ - 16 * Work.Residues.Ept τ) + 16 * Work.Residues.Ept τ‖
          ≤ ‖Work.Kernels.VFun τ - 16 * Work.Residues.Ept τ‖
            + ‖(16 : ℂ) * Work.Residues.Ept τ‖ := norm_add_le _ _
        _ ≤ CV * ‖Work.Residues.Ept τ‖ ^ 3 + 16 * ‖Work.Residues.Ept τ‖ := by
              rw [hb]; linarith
        _ ≤ (CV + 16) * ‖Work.Residues.Ept τ‖ := by nlinarith [hCV.le, ht0, ht3]
    have he8 : ‖Work.Kernels.E8Fun τ - 1‖
        ≤ ((240 + CA) * (242 + CA)) * ‖Work.Residues.Ept τ‖ ^ 2 := by
      have hE4τ := hE4 τ hτ
      have ht0 : (0 : ℝ) ≤ ‖Work.Residues.Ept τ‖ := norm_nonneg _
      have ht1 : ‖Work.Residues.Ept τ‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one τ)
      have ht42 : ‖Work.Residues.Ept τ‖ ^ 4 ≤ ‖Work.Residues.Ept τ‖ ^ 2 :=
        pow_le_pow_of_le_one ht0 ht1 (by norm_num : 2 ≤ 4)
      have ht21 : ‖Work.Residues.Ept τ‖ ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
      have hqE : Work.Kernels.qParamFun τ = (Work.Residues.Ept τ) ^ 2 := by
        rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
        congr 1; ring
      have hq2 : ‖Work.Kernels.qParamFun τ‖ ^ 2 = ‖Work.Residues.Ept τ‖ ^ 4 := by
        rw [hqE, norm_pow]; ring
      have hE4τ' : ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ‖
          ≤ CA * ‖Work.Residues.Ept τ‖ ^ 4 := by
        rw [hq2] at hE4τ; exact hE4τ
      have hE41 : ‖Work.Kernels.E4Fun τ - 1‖ ≤ (240 + CA) * ‖Work.Residues.Ept τ‖ ^ 2 := by
        have hq : ‖Work.Kernels.qParamFun τ‖ = ‖Work.Residues.Ept τ‖ ^ 2 := by
          rw [hqE, norm_pow]
        have h240 : ‖(240 : ℂ) * Work.Kernels.qParamFun τ‖
            = 240 * ‖Work.Residues.Ept τ‖ ^ 2 := by
          rw [norm_mul, Complex.norm_ofNat, hq]
        have hkey : Work.Kernels.E4Fun τ - 1
            = (Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ)
              + 240 * Work.Kernels.qParamFun τ := by ring
        rw [hkey]
        calc ‖(Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ)
              + 240 * Work.Kernels.qParamFun τ‖
            ≤ ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ‖
              + ‖240 * Work.Kernels.qParamFun τ‖ := norm_add_le _ _
          _ ≤ CA * ‖Work.Residues.Ept τ‖ ^ 4 + 240 * ‖Work.Residues.Ept τ‖ ^ 2 := by
                rw [h240]; linarith
          _ ≤ (240 + CA) * ‖Work.Residues.Ept τ‖ ^ 2 := by nlinarith [hCA.le, ht0, ht42]
      have hE4p : ‖Work.Kernels.E4Fun τ + 1‖ ≤ 242 + CA := by
        have h := norm_add_le (Work.Kernels.E4Fun τ - 1) (2 : ℂ)
        rw [show (Work.Kernels.E4Fun τ - 1) + 2 = Work.Kernels.E4Fun τ + 1 by ring,
          Complex.norm_ofNat] at h
        have h2 : (240 + CA) * ‖Work.Residues.Ept τ‖ ^ 2 ≤ 240 + CA := by
          have h3 := mul_le_mul_of_nonneg_left ht21 (by positivity : (0 : ℝ) ≤ 240 + CA)
          simpa using h3
        linarith [h, hE41, h2]
      have hfac : Work.Kernels.E8Fun τ - 1
          = (Work.Kernels.E4Fun τ - 1) * (Work.Kernels.E4Fun τ + 1) := by
        rw [show Work.Kernels.E8Fun τ = Work.Kernels.E4Fun τ ^ 2 from rfl]; ring
      rw [hfac, norm_mul]
      calc ‖Work.Kernels.E4Fun τ - 1‖ * ‖Work.Kernels.E4Fun τ + 1‖
          ≤ ((240 + CA) * ‖Work.Residues.Ept τ‖ ^ 2) * (242 + CA) :=
            mul_le_mul hE41 hE4p (norm_nonneg _) (by positivity)
        _ = ((240 + CA) * (242 + CA)) * ‖Work.Residues.Ept τ‖ ^ 2 := by ring
    exact thirdOrderCore (Work.Kernels.DeltaFun τ) (Work.Residues.Ept τ) (Work.Kernels.UFun τ)
      (Work.Kernels.VFun τ) (Work.Kernels.WFun τ) (Work.Kernels.E8Fun τ)
      Cδ (CU + 32) (CW + 32) (CV + 16) ((240 + CA) * (242 + CA))
      hCδ.le (by positivity) (by positivity) (by positivity) (by positivity)
      (le_of_lt (Work.Residues.norm_Ept_lt_one τ)) (hδ τ hτ) hu hw hv he8

end Work.Asymptotics
