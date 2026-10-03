import Mathlib
import Submission.Work.Peluse.AreaA2_of_crux
import Submission.Work.Peluse.Crux.LambdaZ_norm_le
import Submission.Work.Peluse.Crux.dualFn_l1_ge_f1_l1

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

private lemma progAvgSum_nonneg (N' : ℕ) (q : ℤ) (f : ℤ → ℂ) : 0 ≤ progAvgSum N' q f := by
  rw [progAvgSum]
  exact tsum_nonneg (fun x => norm_nonneg _)

private lemma tsum_norm_shift (f : ℤ → ℂ) (p : ℤ) : (∑' x : ℤ, ‖f (x + p)‖) = ∑' x : ℤ, ‖f x‖ := by
  simpa [Equiv.coe_addRight] using Equiv.tsum_eq (Equiv.addRight p) (fun x : ℤ => ‖f x‖)

private lemma progAvgSum_one_one (f : ℤ → ℂ) : progAvgSum 1 ((1:ℕ):ℤ) f = ∑' x : ℤ, ‖f x‖ := by
  rw [progAvgSum]
  have h1 : ∀ x : ℤ, (progAvg 1 ((1:ℕ):ℤ) f) x = f (x + 1) := by
    intro x
    simp [progAvg]
  simp only [h1]
  exact tsum_norm_shift f 1

set_option linter.unusedVariables false

theorem crux_of_nodes {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseUControl P) (h2 : Work.Peluse.PeluseULowering P) :
    Work.Peluse.PeluseCrux P := by
  unfold PeluseCrux
  intro A hA1
  have hApos : (0:ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  obtain ⟨s, hs2, hUC⟩ := h1
  set A' : ℝ := 3*A with hA'def
  have hA'1 : (1:ℝ) ≤ A' := by rw [hA'def]; linarith
  have hA'pos : (0:ℝ) < A' := lt_of_lt_of_le zero_lt_one hA'1
  obtain ⟨C₁, K₁, hC₁1, hK₁1, hUC'⟩ := hUC A' hA'1
  have hC₁R : (1:ℝ) ≤ (C₁:ℝ) := by exact_mod_cast hC₁1
  have hC₁pos : (0:ℝ) < (C₁:ℝ) := by linarith
  obtain ⟨C₂, K₂, hC₂1, hK₂1, hUL⟩ := h2 s hs2 A' hA'1
  have hC₂R : (1:ℝ) ≤ (C₂:ℝ) := by exact_mod_cast hC₂1
  have hC₂pos : (0:ℝ) < (C₂:ℝ) := by linarith
  set K : ℕ := 20*K₁*K₂ + K₁ + 2 with hKdef
  have h20KK : 20*K₁*K₂ ≤ K := by rw [hKdef]; omega
  have h3KK : 3*K₁*K₂ ≤ K :=
    le_trans (Nat.mul_le_mul_right K₂ (Nat.mul_le_mul_right K₁ (by norm_num))) h20KK
  have h6KK : 6*K₁*K₂ ≤ K :=
    le_trans (Nat.mul_le_mul_right K₂ (Nat.mul_le_mul_right K₁ (by norm_num))) h20KK
  have h6KK'' : 6*K₁*K₂ + 1 ≤ K := by nlinarith [hKdef, hK₁1, hK₂1]
  have hKK1 : K₁ ≤ K := by rw [hKdef]; omega
  have hK1 : 1 ≤ K := by rw [hKdef]; omega
  -- the constants
  set Cq_A : ℝ := C₂ * A'^K₂ * (2*C₁)^K₂ * (C₁ * A'^K₁)^K₂ with hCqdef
  have hCq1 : (1:ℝ) ≤ Cq_A := by
    rw [hCqdef]
    have h1 : (1:ℝ) ≤ C₂ * A'^K₂ := by
      calc (1:ℝ) = 1*1 := by norm_num
        _ ≤ _ := mul_le_mul hC₂R (one_le_pow₀ hA'1) (by norm_num) (by positivity)
    have h2 : (1:ℝ) ≤ (2*C₁)^K₂ := one_le_pow₀ (by linarith)
    have h3 : (1:ℝ) ≤ (C₁ * A'^K₁)^K₂ :=
      one_le_pow₀ (by
        calc (1:ℝ) = 1*1 := by norm_num
          _ ≤ (C₁:ℝ) * A'^K₁ := mul_le_mul hC₁R (one_le_pow₀ hA'1) (by norm_num) (by positivity))
    have h4 : (1:ℝ) ≤ C₂ * A'^K₂ * (2*C₁)^K₂ := by
      calc (1:ℝ) = 1*1 := by norm_num
        _ ≤ _ := mul_le_mul h1 h2 (by norm_num) (by positivity)
    calc (1:ℝ) = 1*1 := by norm_num
      _ ≤ _ := mul_le_mul h4 h3 (by norm_num) (by positivity)
  set C₀ : ℝ := 2^(2*K₂) * (C₁:ℝ)^(2*K₂) * (C₁ * A'^K₁)^(2*K₂) * C₂ * A'^K₂ with hC₀def
  have hC₀pos : (0:ℝ) < C₀ := by rw [hC₀def]; positivity
  have hC₀1 : (1:ℝ) ≤ C₀ := by
    rw [hC₀def]
    have h1 : (1:ℝ) ≤ C₁ * A'^K₁ := by
      calc (1:ℝ) = 1*1 := by norm_num
        _ ≤ (C₁:ℝ) * A'^K₁ := mul_le_mul hC₁R (one_le_pow₀ hA'1) (by norm_num) (by positivity)
    have h2 : (1:ℝ) ≤ 2^(2*K₂) := one_le_pow₀ (by norm_num)
    have h2b : (1:ℝ) ≤ (C₁:ℝ)^(2*K₂) := one_le_pow₀ hC₁R
    have h3 : (1:ℝ) ≤ (C₁ * A'^K₁)^(2*K₂) := one_le_pow₀ h1
    have h4 : (1:ℝ) ≤ A'^K₂ := one_le_pow₀ hA'1
    have h5 : (1:ℝ) ≤ (C₂:ℝ) := hC₂R
    have h6 : (1:ℝ) ≤ 2^(2*K₂) * (C₁:ℝ)^(2*K₂) * (C₁ * A'^K₁)^(2*K₂) := by
      have h7 : (1:ℝ) ≤ 2^(2*K₂) * (C₁:ℝ)^(2*K₂) := by
        calc (1:ℝ) = 1*1 := by norm_num
          _ ≤ _ := mul_le_mul h2 h2b (by norm_num) (by positivity)
      calc (1:ℝ) = 1*1 := by norm_num
        _ ≤ _ := mul_le_mul h7 h3 (by norm_num) (by positivity)
    have h8 : (1:ℝ) ≤ 2^(2*K₂) * (C₁:ℝ)^(2*K₂) * (C₁ * A'^K₁)^(2*K₂) * C₂ := by
      calc (1:ℝ) = 1*1 := by norm_num
        _ ≤ _ := mul_le_mul h6 h5 (by norm_num) (by positivity)
    calc (1:ℝ) = 1*1 := by norm_num
      _ ≤ _ := mul_le_mul h8 h4 (by norm_num) (by positivity)
  set Ψ : ℝ := max (max (max (Cq_A * A^(3*K₁*K₂)) (C₀ * Cq_A * A^K * (3*A)))
      (2 * A^K * C₁)) 1 with hΨdef
  have hΨ1 : (1:ℝ) ≤ Ψ := by rw [hΨdef]; exact le_max_right _ _
  set C : ℕ := ⌈Ψ⌉₊ with hCdef
  have hCΨ : Ψ ≤ (C:ℝ) := by rw [hCdef]; exact Nat.le_ceil Ψ
  have hC1 : Cq_A * A^(3*K₁*K₂) ≤ (C:ℝ) := by
    refine le_trans ?_ hCΨ
    rw [hΨdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC3 : C₀ * Cq_A * A^K * (3*A) ≤ (C:ℝ) := by
    refine le_trans ?_ hCΨ
    rw [hΨdef]
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hC3' : C₀ * Cq_A * A^K ≤ (C:ℝ) := by
    refine le_trans ?_ hC3
    have h1 : (1:ℝ) ≤ (3*A) := by linarith
    calc C₀ * Cq_A * A^K = C₀ * Cq_A * A^K * 1 := by ring
      _ ≤ C₀ * Cq_A * A^K * (3*A) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hC6 : 3*A^(K+1)*C₀ ≤ (C:ℝ) := by
    refine le_trans ?_ hC3
    calc 3*A^(K+1)*C₀ ≤ Cq_A * (3*A^(K+1)*C₀) := le_mul_of_one_le_left (by positivity) hCq1
      _ = C₀ * Cq_A * A^K * (3*A) := by rw [pow_succ]; ring
  have hC7 : 2 * A^K * C₁ ≤ (C:ℝ) := by
    refine le_trans ?_ hCΨ
    rw [hΨdef]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨C, K, ?_, ?_, ?_⟩
  · exact Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hΨ1)
  · rw [hKdef]; omega
  · intro N N₀ δ f₀ f₁ f₂ hd' hN1 hδ0 hδ1 hN₀1 hnd hsc hsf0 hsf1 hsf2 hb0 hb1 hb2 hmain
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
    have hN₀pos : (0:ℝ) < (N₀:ℝ) := by exact_mod_cast hN₀1
    have hN1R : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    have hNdpos : (0:ℝ) < (N:ℝ)^P.natDegree := pow_pos hNpos _
    set θ : ℝ := ‖LambdaZ N₀ N P f₀ f₁ f₂‖ with hθdef
    have hθ3 : θ ≤ 3 := by
      rw [hθdef]
      exact Crux.LambdaZ_norm_le hN₀1 hN1 P f₀ f₁ f₂ hsf0 hsf1 hsf2 hb0 hb1 hb2
    have hθpos : 0 < θ := by
      rw [hθdef]
      by_contra hcon
      push_neg at hcon
      have h2 : ‖LambdaZ N₀ N P f₀ f₁ f₂‖ * (N₀:ℝ) ≤ 0 := by
        nlinarith [norm_nonneg (LambdaZ N₀ N P f₀ f₁ f₂), hN₀pos, hcon]
      nlinarith [hmain, mul_pos hδ0 hNdpos, h2]
    -- the threshold delta_U = delta / A
    set δ_U : ℝ := δ / A with hδUdef
    have hδUpos : 0 < δ_U := by rw [hδUdef]; exact div_pos hδ0 hApos
    have hδU1 : δ_U ≤ 1 := by rw [hδUdef, div_le_one hApos]; linarith [hδ1, hA1]
    have hδUθ : δ_U ≤ θ := by
      have h1 : δ * (N:ℝ)^P.natDegree ≤ θ * (N₀:ℝ) := by rw [hθdef]; exact hmain
      have h2 : δ ≤ θ * ((N₀:ℝ)/(N:ℝ)^P.natDegree) := by
        rw [← mul_div_assoc, le_div_iff₀ hNdpos]; exact hmain
      have hρge : (1:ℝ)/A ≤ (N:ℝ)^P.natDegree / (N₀:ℝ) := by
        rw [div_le_div_iff₀ hApos hN₀pos, one_mul, mul_comm]
        exact hsc
      have h3 : (1:ℝ)/A ≤ (N:ℝ)^P.natDegree/(N₀:ℝ) := hρge
      rw [hδUdef]
      calc δ/A = δ * (1/A) := by ring
        _ ≤ δ * ((N:ℝ)^P.natDegree/(N₀:ℝ)) := mul_le_mul_of_nonneg_left h3 hδ0.le
        _ = δ * ((N:ℝ)^P.natDegree/(N₀:ℝ)) := rfl
        _ ≤ θ := by
            rw [show δ * ((N:ℝ)^P.natDegree/(N₀:ℝ)) = δ / ((N₀:ℝ)/(N:ℝ)^P.natDegree) by
              field_simp]
            rw [div_le_iff₀ (by positivity)]
            have h4 : δ ≤ θ * ((N₀:ℝ)/(N:ℝ)^P.natDegree) := h2
            nlinarith [h4, hN₀pos, hNdpos, hθpos, hδ0]
    have hAle : A ≤ δ^K * (N:ℝ) := by
      have h1 : A * (δ⁻¹)^K ≤ (N:ℝ) := hnd
      have h2 : (0:ℝ) < δ^K := pow_pos hδ0 _
      have h3 : A = A * (δ⁻¹)^K * δ^K := by
        rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hδ0), one_pow, mul_one]
      calc A = A * (δ⁻¹)^K * δ^K := h3
        _ = δ^K * (A * (δ⁻¹)^K) := by ring
        _ ≤ δ^K * (N:ℝ) := mul_le_mul_of_nonneg_left h1 h2.le
    -- the scale facts for delta_U
    have hδU_scale : δ_U * (N:ℝ)^P.natDegree ≤ A' * (N₀:ℝ) := by
      have h3 : δ * (N:ℝ)^P.natDegree ≤ θ * (N₀:ℝ) := by rw [hθdef]; exact hmain
      have h1 : δ / A * (N:ℝ)^P.natDegree ≤ 3 * (N₀:ℝ) := by
        rw [show δ / A * (N:ℝ)^P.natDegree = δ * (N:ℝ)^P.natDegree / A by ring]
        rw [div_le_iff₀ hApos]
        calc δ * (N:ℝ)^P.natDegree ≤ θ * (N₀:ℝ) := h3
          _ ≤ 3 * (N₀:ℝ) := mul_le_mul_of_nonneg_right hθ3 hN₀pos.le
          _ ≤ 3 * (N₀:ℝ) * A := by
              calc 3 * (N₀:ℝ) = 3 * (N₀:ℝ) * 1 := by ring
                _ ≤ 3 * (N₀:ℝ) * A := mul_le_mul_of_nonneg_left hA1 (by positivity)
      calc δ_U * (N:ℝ)^P.natDegree = δ / A * (N:ℝ)^P.natDegree := by rw [hδUdef]
        _ ≤ 3 * (N₀:ℝ) := h1
        _ ≤ A' * (N₀:ℝ) := by rw [hA'def]; nlinarith [hN₀pos, hA1]
    have hδle : δ ≤ A * δ_U := by
      rw [hδUdef]
      have h : δ = A * (δ / A) := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hApos)]
      exact le_of_eq h
    have hδUinv : (δ_U)⁻¹ = A * δ⁻¹ := by rw [hδUdef, inv_div, div_eq_mul_inv]
    have hN₀leA' : (N₀:ℝ) ≤ A' * (N:ℝ)^P.natDegree := by
      rw [hA'def]; nlinarith [hsc, hA1]
    have hNdleA' : (N:ℝ)^P.natDegree ≤ A' * δ_U⁻¹ * (N₀:ℝ) := by
      have h : δ_U * (N:ℝ)^P.natDegree ≤ A' * (N₀:ℝ) := hδU_scale
      calc (N:ℝ)^P.natDegree = δ_U⁻¹ * (δ_U * (N:ℝ)^P.natDegree) := by
            rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hδUpos), one_mul]
        _ ≤ δ_U⁻¹ * (A' * (N₀:ℝ)) := mul_le_mul_of_nonneg_left h (by positivity)
        _ = A' * δ_U⁻¹ * (N₀:ℝ) := by ring
    by_cases hbig : 2*C₁ ≤ δ_U^K₁ * (N:ℝ)^P.natDegree
    · -- ============ CASE A ============
      set D : ℕ := ⌊δ_U^K₁ * (N:ℝ)^P.natDegree / (C₁:ℝ)⌋₊ with hDdef
      have hD1 : 1 ≤ D := by
        rw [hDdef]
        have hx : (1:ℝ) ≤ δ_U^K₁ * (N:ℝ)^P.natDegree / (C₁:ℝ) := by
          rw [one_le_div hC₁pos]
          linarith [hbig]
        exact Nat.le_floor (by exact_mod_cast hx)
      have hDle : (D:ℝ) ≤ δ_U^K₁ * (N:ℝ)^P.natDegree / (C₁:ℝ) := Nat.floor_le (by positivity)
      have hDlt : δ_U^K₁ * (N:ℝ)^P.natDegree / (C₁:ℝ) < (D:ℝ) + 1 := Nat.lt_floor_add_one _
      have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
      have hDge : δ_U^K₁ * (N:ℝ)^P.natDegree / (2*C₁) ≤ (D:ℝ) := by
        have h2 : δ_U^K₁ * (N:ℝ)^P.natDegree / (C₁:ℝ) - 1 < (D:ℝ) := by linarith [hDlt]
        have h3 : 2 ≤ δ_U^K₁ * (N:ℝ)^P.natDegree / (C₁:ℝ) := by
          rw [le_div_iff₀ hC₁pos]; linarith [hbig]
        have h5 : (δ_U^K₁ * (N:ℝ)^P.natDegree / (C₁:ℝ) - 1) * C₁ < (D:ℝ) * C₁ :=
          mul_lt_mul_of_pos_right h2 hC₁pos
        have h6 : (δ_U^K₁ * (N:ℝ)^P.natDegree / (C₁:ℝ)) * C₁ = δ_U^K₁ * (N:ℝ)^P.natDegree := by
          field_simp
        have h7 : 2 * C₁ ≤ δ_U^K₁ * (N:ℝ)^P.natDegree := by
          rw [le_div_iff₀ hC₁pos] at h3; linarith [h3]
        have h8 : δ_U^K₁ * (N:ℝ)^P.natDegree - C₁ < (D:ℝ)*C₁ := by linarith [h5, h6]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [h7, h8, hC₁pos]
      have hDleNd : (D:ℝ) ≤ (N:ℝ)^P.natDegree := by
        have h1 : δ_U^K₁ ≤ 1 := pow_le_one₀ hδUpos.le hδU1
        have h2 : δ_U^K₁ * (N:ℝ)^P.natDegree / (C₁:ℝ) ≤ (N:ℝ)^P.natDegree := by
          rw [div_le_iff₀ hC₁pos]
          nlinarith [h1, hNdpos, hC₁R]
        linarith [hDle, h2]
      set U : ℝ := uNormPow s (arithIcc P.leadingCoeff D) (symIcc (dSup P N₀ N)) (dualFn N P f₀ f₁) with hUdef
      have hCDle : (C₁:ℝ) * (D:ℝ) ≤ δ_U^K₁ * (N:ℝ)^P.natDegree := by
        calc (C₁:ℝ) * (D:ℝ) ≤ C₁ * (δ_U^K₁ * (N:ℝ)^P.natDegree / C₁) :=
              mul_le_mul_of_nonneg_left hDle hC₁pos.le
          _ = δ_U^K₁ * (N:ℝ)^P.natDegree := by field_simp
      have hUCA := hUC' N N₀ D f₀ f₁ f₂ δ_U hd hN1 hN₀1 hN₀leA' hNdleA'
        hδUpos hδU1 hD1 hCDle hsf0 hsf1 hsf2 hb0 hb1 hb2 hδUθ
      rw [← hUdef] at hUCA
      have hδ₂A : δ_U^(2*K₁)/(C₁*A'^K₁) ≤ U := by
        rw [div_le_iff₀ (by positivity)]
        have h4 : (δ_U⁻¹)^K₁ * δ_U^K₁ = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hδUpos), one_pow]
        have h1 : δ_U^K₁ * δ_U^K₁ ≤ ((C₁:ℝ) * A'^K₁ * (δ_U⁻¹)^K₁ * U) * δ_U^K₁ :=
          mul_le_mul_of_nonneg_right hUCA (by positivity)
        have h5 : δ_U^K₁ * δ_U^K₁ = δ_U^(2*K₁) := by
          rw [← pow_add]; ring_nf
        have hkey : ((C₁:ℝ) * A'^K₁ * (δ_U⁻¹)^K₁ * U) * δ_U^K₁ = U * (C₁ * A'^K₁) := by
          have h6 : ((C₁:ℝ) * A'^K₁ * (δ_U⁻¹)^K₁ * U) * δ_U^K₁
              = U * (C₁ * A'^K₁) * ((δ_U⁻¹)^K₁ * δ_U^K₁) := by ring
          rw [h6, h4, mul_one]
        calc δ_U^(2*K₁) = δ_U^K₁ * δ_U^K₁ := h5.symm
          _ ≤ ((C₁:ℝ) * A'^K₁ * (δ_U⁻¹)^K₁ * U) * δ_U^K₁ := h1
          _ = U * (C₁ * A'^K₁) := hkey
      set δ₂A : ℝ := δ_U^(2*K₁)/(C₁*A'^K₁) with hδ₂Adef
      have hδ₂A' : δ₂A ≤ U := by rw [hδ₂Adef]; exact hδ₂A
      have hδ₂Apos : 0 < δ₂A := by rw [hδ₂Adef]; positivity
      have hδ₂A1 : δ₂A ≤ 1 := by
        have hp : δ_U^(2*K₁) ≤ δ_U := by
          have hh : δ_U^(2*K₁) ≤ δ_U^1 := pow_le_pow_of_le_one hδUpos.le hδU1 (by omega)
          simpa using hh
        have h2 : (1:ℝ) ≤ C₁ * A'^K₁ := by
          calc (1:ℝ) = 1*1 := by norm_num
            _ ≤ (C₁:ℝ) * A'^K₁ := mul_le_mul hC₁R (one_le_pow₀ hA'1) (by norm_num) (by positivity)
        rw [hδ₂Adef, div_le_one (by positivity)]
        calc δ_U^(2*K₁) ≤ δ_U * 1 := by rw [mul_one]; exact hp
          _ ≤ δ_U * (C₁ * A'^K₁) := mul_le_mul_of_nonneg_left h2 hδUpos.le
          _ ≤ 1 * (C₁ * A'^K₁) := mul_le_mul_of_nonneg_right hδU1 (by positivity)
          _ = C₁ * A'^K₁ := by rw [one_mul]
      have hδ₂Aleδ_U : δ₂A ≤ δ_U := by
        rw [hδ₂Adef, div_le_iff₀ (by positivity)]
        calc δ_U^(2*K₁) ≤ δ_U * 1 := by rw [mul_one]; exact (by
              have hh : δ_U^(2*K₁) ≤ δ_U^1 := pow_le_pow_of_le_one hδUpos.le hδU1 (by omega)
              simpa using hh)
          _ ≤ δ_U * (C₁ * A'^K₁) := mul_le_mul_of_nonneg_left
              (by
                calc (1:ℝ) = 1*1 := by norm_num
                  _ ≤ (C₁:ℝ) * A'^K₁ := mul_le_mul hC₁R (one_le_pow₀ hA'1) (by norm_num)
                      (by positivity)) hδUpos.le
      have hδ₂Asc : δ₂A ≤ A' * (N₀:ℝ) / (N:ℝ)^P.natDegree := by
        have h1 : δ_U ≤ A' * (N₀:ℝ) / (N:ℝ)^P.natDegree := by
          rw [le_div_iff₀ hNdpos]; exact hδU_scale
        exact le_trans hδ₂Aleδ_U h1
      have hscaleA : (N:ℝ)^P.natDegree ≤ A' * δ₂A⁻¹ * (N₀:ℝ) := by
        have h : δ₂A * (N:ℝ)^P.natDegree ≤ A' * (N₀:ℝ) := by
          rw [le_div_iff₀ hNdpos] at hδ₂Asc
          linarith [hδ₂Asc]
        rw [show A' * δ₂A⁻¹ * (N₀:ℝ) = A' * (N₀:ℝ) / δ₂A by ring]
        rw [le_div_iff₀ hδ₂Apos]
        linarith [h]
      obtain ⟨q, N', hq1, hq2, hN'1, hN'N, hN'd, hN'sum⟩ :=
        hUL N N₀ D f₀ f₁ δ₂A hd hN1 hN₀1 hN₀leA' hscaleA
          hδ₂Apos hδ₂A1 hD1 hDleNd hsf0 hsf1 hb0 hb1 hδ₂A'
      -- algebra
      set Q : ℝ := δ₂A^K₂ * ((D:ℝ) / (N:ℝ)^P.natDegree)^K₂ with hQdef
      set Cst : ℝ := (C₂:ℝ) * A'^K₂ * ((N:ℝ)^P.natDegree / (D:ℝ))^K₂ * (δ₂A⁻¹)^K₂ with hCstdef
      have hCstpos : (0:ℝ) < Cst := by rw [hCstdef]; positivity
      have hN'd' : Q * (N:ℝ) ≤ Cst * (N':ℝ) := by rw [hQdef, hCstdef]; exact hN'd
      have hN'sum' : Q * (N₀:ℝ) ≤ Cst * progAvgSum N' (q:ℤ) f₁ := by
        rw [hQdef, hCstdef]; exact hN'sum
      have hDnd : δ_U^K₁ / (2*C₁) ≤ (D:ℝ) / (N:ℝ)^P.natDegree := by
        have h1 : δ_U^K₁ * (N:ℝ)^P.natDegree ≤ (D:ℝ) * (2*C₁) := by
          have h2 := hDge
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*C₁)] at h2
          linarith [h2]
        rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2*C₁) hNdpos]
        linarith [h1]
      have hDN2 : (δ_U^K₁ / (2*C₁))^K₂ ≤ ((D:ℝ) / (N:ℝ)^P.natDegree)^K₂ :=
        pow_le_pow_left₀ (by positivity) hDnd K₂
      have hδ₂Apow : δ₂A^K₂ = (δ_U^(2*K₁))^K₂ / ((C₁:ℝ)*A'^K₁)^K₂ := by
        rw [hδ₂Adef, div_pow]
      have hL : (δ_U^K₁/(2*C₁))^K₂ * ((δ_U^(2*K₁))^K₂ / ((C₁:ℝ)*A'^K₁)^K₂) ≤ Q := by
        rw [hQdef, hδ₂Apow]
        rw [show ((δ_U^K₁/(2*C₁))^K₂ * ((δ_U^(2*K₁))^K₂ / ((C₁:ℝ)*A'^K₁)^K₂))
              = ((δ_U^(2*K₁))^K₂ / ((C₁:ℝ)*A'^K₁)^K₂) * (δ_U^K₁/(2*C₁))^K₂ by ring]
        exact mul_le_mul_of_nonneg_left hDN2 (by positivity)
      have hC₀eq : 2^K₂ * (C₁:ℝ)^K₂ * ((C₁:ℝ)*A'^K₁)^K₂ * Cq_A = C₀ := by
        rw [hCqdef, hC₀def]
        rw [show 2^K₂ * (C₁:ℝ)^K₂ * ((C₁:ℝ)*A'^K₁)^K₂
              * (C₂ * A'^K₂ * (2*C₁)^K₂ * ((C₁:ℝ)*A'^K₁)^K₂)
              = (2^K₂ * 2^K₂) * ((C₁:ℝ)^K₂ * (C₁:ℝ)^K₂)
                * (((C₁:ℝ)*A'^K₁)^K₂ * ((C₁:ℝ)*A'^K₁)^K₂) * (C₂*A'^K₂) by ring,
            ← pow_add, ← pow_add, ← pow_add]
        rw [show K₂ + K₂ = 2*K₂ by ring]
        ring
      have hpowcancel : δ_U^(6*K₁*K₂) * ((δ_U)⁻¹)^(3*K₁*K₂) = δ_U^(3*K₁*K₂) := by
        have hle : 3*K₁*K₂ ≤ 6*K₁*K₂ := Nat.mul_le_mul_right K₂ (Nat.mul_le_mul_right K₁ (by norm_num))
        rw [inv_pow]
        rw [show δ_U^(6*K₁*K₂) * (δ_U^(3*K₁*K₂))⁻¹ = δ_U^(6*K₁*K₂) / δ_U^(3*K₁*K₂) from
          (div_eq_mul_inv _ _).symm]
        rw [show δ_U^(6*K₁*K₂) / δ_U^(3*K₁*K₂) = δ_U^(6*K₁*K₂ - 3*K₁*K₂) from
          (pow_sub₀ δ_U (ne_of_gt hδUpos) hle).symm]
        have h2 : 6*K₁*K₂ - 3*K₁*K₂ = 3*K₁*K₂ := by
          have h : 6*K₁*K₂ = 3*K₁*K₂ + 3*K₁*K₂ := by ring
          omega
        rw [h2]
      have hCst : Cst ≤ Cq_A * ((δ_U)⁻¹)^(3*K₁*K₂) := by
        rw [hCstdef]
        have hND2 : ((N:ℝ)^P.natDegree / (D:ℝ))^K₂ ≤ (2*C₁ * ((δ_U)⁻¹)^K₁)^K₂ := by
          apply pow_le_pow_left₀ (by positivity)
          rw [div_le_iff₀ hDpos, inv_pow]
          rw [show (2*C₁ * (δ_U^K₁)⁻¹) * (D:ℝ) = (2*C₁) * (D:ℝ) / δ_U^K₁ by ring]
          rw [le_div_iff₀ (pow_pos hδUpos K₁)]
          have h3 := hDge
          rw [div_le_iff₀ (by positivity)] at h3
          linarith [h3]
        have hδ₂Ainv : δ₂A⁻¹ ≤ ((C₁:ℝ) * A'^K₁) * ((δ_U)⁻¹)^(2*K₁) := by
          rw [hδ₂Adef, div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow]
          try ring
        have hδ₂Ainv2 : (δ₂A⁻¹)^K₂ ≤ ((C₁:ℝ)*A'^K₁)^K₂ * ((δ_U)⁻¹)^(2*K₁*K₂) := by
          refine le_trans (pow_le_pow_left₀ (by positivity) hδ₂Ainv K₂) (le_of_eq ?_)
          rw [mul_pow, pow_mul]; try ring
        have hND2' : ((N:ℝ)^P.natDegree / (D:ℝ))^K₂ ≤ (2*C₁)^K₂ * ((δ_U)⁻¹)^(K₁*K₂) :=
          le_trans hND2 (le_of_eq (by rw [mul_pow, pow_mul]; try ring))
        have hEp : ((δ_U)⁻¹)^(K₁*K₂) * ((δ_U)⁻¹)^(2*K₁*K₂) = ((δ_U)⁻¹)^(3*K₁*K₂) := by
          rw [← pow_add]; ring_nf
        have step1 : (C₂:ℝ) * A'^K₂ * ((N:ℝ)^P.natDegree / (D:ℝ))^K₂
            ≤ C₂ * A'^K₂ * ((2*C₁)^K₂ * ((δ_U)⁻¹)^(K₁*K₂)) :=
          mul_le_mul_of_nonneg_left hND2' (by positivity)
        calc (C₂:ℝ) * A'^K₂ * ((N:ℝ)^P.natDegree / (D:ℝ))^K₂ * (δ₂A⁻¹)^K₂
            ≤ C₂ * A'^K₂ * ((2*C₁)^K₂ * ((δ_U)⁻¹)^(K₁*K₂))
              * (((C₁:ℝ)*A'^K₁)^K₂ * ((δ_U)⁻¹)^(2*K₁*K₂)) := by
              calc (C₂:ℝ) * A'^K₂ * ((N:ℝ)^P.natDegree / (D:ℝ))^K₂ * (δ₂A⁻¹)^K₂
                  ≤ C₂ * A'^K₂ * ((2*C₁)^K₂ * ((δ_U)⁻¹)^(K₁*K₂)) * (δ₂A⁻¹)^K₂ :=
                    mul_le_mul_of_nonneg_right step1 (by positivity)
                _ ≤ C₂ * A'^K₂ * ((2*C₁)^K₂ * ((δ_U)⁻¹)^(K₁*K₂))
                      * (((C₁:ℝ)*A'^K₁)^K₂ * ((δ_U)⁻¹)^(2*K₁*K₂)) :=
                    mul_le_mul_of_nonneg_left hδ₂Ainv2 (by positivity)
          _ = Cq_A * ((δ_U)⁻¹)^(3*K₁*K₂) := by
              rw [show C₂ * A'^K₂ * ((2*C₁)^K₂ * ((δ_U)⁻¹)^(K₁*K₂))
                    * (((C₁:ℝ)*A'^K₁)^K₂ * ((δ_U)⁻¹)^(2*K₁*K₂))
                  = (C₂ * A'^K₂ * (2*C₁)^K₂ * ((C₁:ℝ)*A'^K₁)^K₂)
                    * (((δ_U)⁻¹)^(K₁*K₂) * ((δ_U)⁻¹)^(2*K₁*K₂)) by ring, hEp, hCqdef]
              try ring
      have hC₀eq2 : (2*C₁)^K₂ * ((C₁:ℝ)*A'^K₁)^K₂ * Cq_A = C₀ := by
        rw [show (2*C₁)^K₂ = 2^K₂ * (C₁:ℝ)^K₂ by rw [mul_pow]]
        exact hC₀eq
      have hkey : (δ_U^K₁/(2*C₁))^K₂ * ((δ_U^(2*K₁))^K₂ / ((C₁:ℝ)*A'^K₁)^K₂)
          * ((2*C₁)^K₂ * ((C₁:ℝ)*A'^K₁)^K₂) = δ_U^(3*K₁*K₂) := by
        rw [div_pow, ← pow_mul, ← pow_mul]
        field_simp
        rw [← pow_add, show K₁*K₂ + 2*K₁*K₂ = 3*K₁*K₂ by ring]
      have h6 : δ_U^(3*K₁*K₂) * Cq_A ≤ Q * C₀ := by
        have hLc : δ_U^(3*K₁*K₂) * Cq_A
            = ((δ_U^K₁/(2*C₁))^K₂ * ((δ_U^(2*K₁))^K₂ / ((C₁:ℝ)*A'^K₁)^K₂)) * C₀ := by
          rw [← hC₀eq2, ← hkey]
          ring
        rw [hLc]
        exact mul_le_mul_of_nonneg_right hL (by positivity)
      have h5 : δ_U^(6*K₁*K₂) * Cst ≤ δ_U^(3*K₁*K₂) * Cq_A := by
        have h4 := mul_le_mul_of_nonneg_left hCst (le_of_lt (pow_pos hδUpos (6*K₁*K₂)))
        refine le_trans h4 (le_of_eq ?_)
        rw [show δ_U^(6*K₁*K₂) * (Cq_A * ((δ_U)⁻¹)^(3*K₁*K₂))
              = Cq_A * (δ_U^(6*K₁*K₂) * ((δ_U)⁻¹)^(3*K₁*K₂)) by ring_nf, hpowcancel]
        ring
      have hQN : δ_U^(6*K₁*K₂) * (N₀:ℝ) / C₀ ≤ Q * (N₀:ℝ) / Cst := by
        rw [div_le_div_iff₀ (by positivity) hCstpos]
        calc δ_U^(6*K₁*K₂) * (N₀:ℝ) * Cst
            = (δ_U^(6*K₁*K₂) * Cst) * (N₀:ℝ) := by ring
          _ ≤ (δ_U^(3*K₁*K₂) * Cq_A) * (N₀:ℝ) := mul_le_mul_of_nonneg_right h5 (by positivity)
          _ ≤ (Q * C₀) * (N₀:ℝ) := mul_le_mul_of_nonneg_right h6 (by positivity)
          _ = Q * (N₀:ℝ) * C₀ := by ring
      have hQN' : δ_U^(6*K₁*K₂) * (N:ℝ) / C₀ ≤ Q * (N:ℝ) / Cst := by
        rw [div_le_div_iff₀ (by positivity) hCstpos]
        calc δ_U^(6*K₁*K₂) * (N:ℝ) * Cst
            = (δ_U^(6*K₁*K₂) * Cst) * (N:ℝ) := by ring
          _ ≤ (δ_U^(3*K₁*K₂) * Cq_A) * (N:ℝ) := mul_le_mul_of_nonneg_right h5 (by positivity)
          _ ≤ (Q * C₀) * (N:ℝ) := mul_le_mul_of_nonneg_right h6 (by positivity)
          _ = Q * (N:ℝ) * C₀ := by ring
      have hN'ge : δ_U^(6*K₁*K₂) * (N:ℝ) / C₀ ≤ (N':ℝ) := by
        have hstep : Q * (N:ℝ) / Cst ≤ (N':ℝ) := by
          rw [div_le_iff₀ hCstpos]; linarith [hN'd']
        exact le_trans hQN' hstep
      have hprog : δ_U^(6*K₁*K₂) * (N₀:ℝ) / C₀ ≤ progAvgSum N' (q:ℤ) f₁ := by
        have hstep : Q * (N₀:ℝ) / Cst ≤ progAvgSum N' (q:ℤ) f₁ := by
          rw [div_le_iff₀ hCstpos]; linarith [hN'sum']
        exact le_trans hQN hstep
      have hδK : δ^K ≤ A^K * δ_U^K := by
        calc δ^K ≤ (A * δ_U)^K := pow_le_pow_left₀ (by positivity) hδle K
          _ = A^K * δ_U^K := mul_pow _ _ _
      have hδUKm : δ_U^K ≤ δ_U^(6*K₁*K₂) := pow_le_pow_of_le_one hδUpos.le hδU1 h6KK
      have hρge : (1:ℝ)/A ≤ (N:ℝ)^P.natDegree/(N₀:ℝ) := by
        rw [div_le_div_iff₀ hApos hN₀pos, one_mul, mul_comm]
        exact hsc
      have hδUρ : δ_U * ((N:ℝ)^P.natDegree/(N₀:ℝ)) ≤ 3*A := by
        have h : δ_U * (N:ℝ)^P.natDegree ≤ A' * (N₀:ℝ) := hδU_scale
        have h2 : δ_U * ((N:ℝ)^P.natDegree/(N₀:ℝ)) * (N₀:ℝ) ≤ A' * (N₀:ℝ) := by
          calc δ_U * ((N:ℝ)^P.natDegree/(N₀:ℝ)) * (N₀:ℝ)
              = δ_U * (N:ℝ)^P.natDegree := by field_simp
            _ ≤ A' * (N₀:ℝ) := h
        have h3 := h2
        rw [hA'def] at h3
        have h4 : δ_U * ((N:ℝ)^P.natDegree/(N₀:ℝ)) ≤ 3*A :=
          le_of_mul_le_mul_right h3 hN₀pos
        exact h4
      have hρle3A : (N:ℝ)^P.natDegree/(N₀:ℝ) ≤ 3*A/δ_U := by
        rw [le_div_iff₀ hδUpos]; linarith [hδUρ]
      refine ⟨q, N', hq1, ?_, hN'1, hN'N, ?_, ?_⟩
      · have hE : ((δ_U)⁻¹)^(3*K₁*K₂) ≤ A^(3*K₁*K₂) * (δ⁻¹)^K := by
          have h8 : ((δ_U)⁻¹)^(3*K₁*K₂) ≤ (A * δ⁻¹)^(3*K₁*K₂) := by
            rw [hδUinv]
          have h9 : (A * δ⁻¹)^(3*K₁*K₂) = A^(3*K₁*K₂) * (δ⁻¹)^(3*K₁*K₂) := mul_pow _ _ _
          have h10 : (δ⁻¹)^(3*K₁*K₂) ≤ (δ⁻¹)^K :=
            pow_le_pow_right₀ (by rw [one_le_inv₀ hδ0]; exact hδ1) h3KK
          calc ((δ_U)⁻¹)^(3*K₁*K₂) ≤ (A * δ⁻¹)^(3*K₁*K₂) := h8
            _ = A^(3*K₁*K₂) * (δ⁻¹)^(3*K₁*K₂) := h9
            _ ≤ A^(3*K₁*K₂) * (δ⁻¹)^K := mul_le_mul_of_nonneg_left h10 (by positivity)
        have h1 : (q:ℝ) ≤ Cq_A * ((δ_U)⁻¹)^(3*K₁*K₂) := le_trans hq2 hCst
        calc (q:ℝ) ≤ Cq_A * ((δ_U)⁻¹)^(3*K₁*K₂) := h1
          _ ≤ Cq_A * (A^(3*K₁*K₂) * (δ⁻¹)^K) := mul_le_mul_of_nonneg_left hE (by positivity)
          _ = (Cq_A * A^(3*K₁*K₂)) * (δ⁻¹)^K := by ring
          _ ≤ (C:ℝ) * (δ⁻¹)^K := mul_le_mul_of_nonneg_right hC1 (by positivity)
      · have h1 : δ^K * (N:ℝ) ≤ A^K * δ_U^(6*K₁*K₂) * (N:ℝ) := by
          calc δ^K * (N:ℝ) ≤ (A^K * δ_U^K) * (N:ℝ) :=
                mul_le_mul_of_nonneg_right hδK (le_of_lt hNpos)
            _ ≤ (A^K * δ_U^(6*K₁*K₂)) * (N:ℝ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδUKm (by positivity))
                  (le_of_lt hNpos)
        have heq1 : (C₀ * Cq_A * A^K) * (δ_U^(6*K₁*K₂) * (N:ℝ) / C₀)
            = Cq_A * (A^K * δ_U^(6*K₁*K₂) * (N:ℝ)) := by
          rw [← mul_div_assoc,
            show C₀ * Cq_A * A^K * (δ_U^(6*K₁*K₂) * (N:ℝ))
              = C₀ * (Cq_A * (A^K * δ_U^(6*K₁*K₂) * (N:ℝ))) by ring,
            mul_div_cancel_left₀ _ (ne_of_gt hC₀pos)]
        have h2 : A^K * δ_U^(6*K₁*K₂) * (N:ℝ)
            ≤ (C₀ * Cq_A * A^K) * (δ_U^(6*K₁*K₂) * (N:ℝ) / C₀) := by
          rw [heq1]
          exact le_mul_of_one_le_left (by positivity : (0:ℝ) ≤ A^K * δ_U^(6*K₁*K₂) * (N:ℝ)) hCq1
        calc δ^K * (N:ℝ) ≤ A^K * δ_U^(6*K₁*K₂) * (N:ℝ) := h1
          _ ≤ (C₀ * Cq_A * A^K) * (δ_U^(6*K₁*K₂) * (N:ℝ) / C₀) := h2
          _ ≤ (C₀ * Cq_A * A^K) * (N':ℝ) := mul_le_mul_of_nonneg_left hN'ge (by positivity)
          _ ≤ (C:ℝ) * (N':ℝ) := mul_le_mul_of_nonneg_right hC3' (by positivity)
      · have h4 : δ_U^(K-6*K₁*K₂) * ((N:ℝ)^P.natDegree/(N₀:ℝ)) ≤ 3*A := by
          have h5 : δ_U^(K-6*K₁*K₂) * ((N:ℝ)^P.natDegree/(N₀:ℝ))
              ≤ δ_U^(K-6*K₁*K₂) * (3*A/δ_U) :=
            mul_le_mul_of_nonneg_left hρle3A (by positivity)
          have h6 : δ_U^(K-6*K₁*K₂) * (3*A/δ_U) = 3*A * (δ_U^(K-6*K₁*K₂)/δ_U) := by ring
          rw [h6] at h5
          have h7 : δ_U^(K-6*K₁*K₂)/δ_U = δ_U^(K-6*K₁*K₂-1) := by
            have hle : 1 ≤ K - 6*K₁*K₂ := by have := h6KK''; omega
            rw [div_eq_iff (ne_of_gt hδUpos), ← pow_succ]
            congr 1
            omega
          rw [h7] at h5
          have h8 : δ_U^(K-6*K₁*K₂-1) ≤ 1 := pow_le_one₀ hδUpos.le hδU1
          calc δ_U^(K-6*K₁*K₂) * ((N:ℝ)^P.natDegree/(N₀:ℝ))
              ≤ 3*A * δ_U^(K-6*K₁*K₂-1) := h5
            _ ≤ 3*A * 1 := mul_le_mul_of_nonneg_left h8 (by positivity)
            _ = 3*A := by ring
        have h4b : δ_U^K * ((N:ℝ)^P.natDegree/(N₀:ℝ)) ≤ δ_U^(6*K₁*K₂) * (3*A) := by
          rw [show K = 6*K₁*K₂ + (K-6*K₁*K₂) by omega, pow_add]
          calc δ_U^(6*K₁*K₂) * δ_U^(K-6*K₁*K₂) * ((N:ℝ)^P.natDegree/(N₀:ℝ))
              = δ_U^(6*K₁*K₂) * (δ_U^(K-6*K₁*K₂) * ((N:ℝ)^P.natDegree/(N₀:ℝ))) := by ring
            _ ≤ δ_U^(6*K₁*K₂) * (3*A) := mul_le_mul_of_nonneg_left h4 (by positivity)
        have h1 : δ^K * (N:ℝ)^P.natDegree ≤ A^K * δ_U^(6*K₁*K₂) * (3*A) * (N₀:ℝ) := by
          have hA1 : δ^K * (N:ℝ)^P.natDegree ≤ A^K * (δ_U^K * ((N:ℝ)^P.natDegree/(N₀:ℝ))) * (N₀:ℝ) := by
            calc δ^K * (N:ℝ)^P.natDegree = (δ^K * ((N:ℝ)^P.natDegree/(N₀:ℝ))) * (N₀:ℝ) := by
                  field_simp
              _ ≤ (A^K * δ_U^K * ((N:ℝ)^P.natDegree/(N₀:ℝ))) * (N₀:ℝ) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hδK (by positivity)) hN₀pos.le
              _ = A^K * (δ_U^K * ((N:ℝ)^P.natDegree/(N₀:ℝ))) * (N₀:ℝ) := by ring
          calc δ^K * (N:ℝ)^P.natDegree
              ≤ A^K * (δ_U^K * ((N:ℝ)^P.natDegree/(N₀:ℝ))) * (N₀:ℝ) := hA1
            _ ≤ A^K * (δ_U^(6*K₁*K₂) * (3*A)) * (N₀:ℝ) := by
                apply mul_le_mul_of_nonneg_right _ hN₀pos.le
                exact mul_le_mul_of_nonneg_left h4b (by positivity)
            _ = A^K * δ_U^(6*K₁*K₂) * (3*A) * (N₀:ℝ) := by ring
        have h2 : A^K * δ_U^(6*K₁*K₂) * (3*A) * (N₀:ℝ)
            = (3*A^(K+1)*C₀) * (δ_U^(6*K₁*K₂) * (N₀:ℝ) / C₀) := by
          rw [← mul_div_assoc,
            show 3*A^(K+1)*C₀ * (δ_U^(6*K₁*K₂) * (N₀:ℝ))
              = C₀ * (3*A^(K+1) * (δ_U^(6*K₁*K₂) * (N₀:ℝ))) by ring,
            mul_div_cancel_left₀ _ (ne_of_gt hC₀pos)]
          rw [pow_succ]
          ring
        calc δ^K * (N:ℝ)^P.natDegree ≤ A^K * δ_U^(6*K₁*K₂) * (3*A) * (N₀:ℝ) := h1
          _ = (3*A^(K+1)*C₀) * (δ_U^(6*K₁*K₂) * (N₀:ℝ) / C₀) := h2
          _ ≤ (3*A^(K+1)*C₀) * progAvgSum N' (q:ℤ) f₁ :=
              mul_le_mul_of_nonneg_left hprog (by positivity)
          _ ≤ (C:ℝ) * progAvgSum N' (q:ℤ) f₁ :=
              mul_le_mul_of_nonneg_right hC6 (progAvgSum_nonneg N' (q:ℤ) f₁)
    · -- ============ CASE B : trivial branch with q = N' = 1 ============
      have hsmall : δ_U^K₁ * (N:ℝ)^P.natDegree < 2*C₁ := not_le.mp hbig
      have hf₁ : δ * (N:ℝ)^P.natDegree ≤ ∑' x : ℤ, ‖f₁ x‖ :=
        Crux.dualFn_l1_ge_f1_l1 hN₀1 hN1 P f₀ f₁ f₂ δ hsf0 hsf1 hsf2 hb0 hb2 hmain
      have hδUKN : δ_U^K * (N:ℝ) ≤ 2*C₁ := by
        have h1 : δ_U^K * (N:ℝ) ≤ δ_U^K * (N:ℝ)^P.natDegree :=
          mul_le_mul_of_nonneg_left (by
            calc (N:ℝ) = (N:ℝ)^1 := (pow_one _).symm
              _ ≤ (N:ℝ)^P.natDegree := pow_le_pow_right₀ hN1R (by omega)) (by positivity)
        have h2 : δ_U^K * (N:ℝ)^P.natDegree ≤ δ_U^K₁ * (N:ℝ)^P.natDegree := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_of_le_one hδUpos.le hδU1 hKK1
        linarith [h1, h2, hsmall]
      have hδKN : δ^K * (N:ℝ) ≤ 2*A^K*C₁ := by
        calc δ^K * (N:ℝ) ≤ (A^K * δ_U^K) * (N:ℝ) := by
              have h := hδle
              have h2 : δ^K ≤ (A * δ_U)^K := pow_le_pow_left₀ (by positivity) hδle K
              rw [mul_pow] at h2
              exact mul_le_mul_of_nonneg_right h2 (by positivity)
          _ = A^K * (δ_U^K * (N:ℝ)) := by ring
          _ ≤ A^K * (2*C₁) := mul_le_mul_of_nonneg_left hδUKN (by positivity)
          _ = 2*A^K*C₁ := by ring
      refine ⟨1, 1, le_refl 1, ?_, le_refl 1, hN1, ?_, ?_⟩
      · -- q bound: 1 ≤ C * (delta^{-1})^K
        have h1 : (1:ℝ) ≤ (δ⁻¹)^K := one_le_pow₀ (by rw [one_le_inv₀ hδ0]; exact hδ1)
        have h2 : (1:ℝ) ≤ (C:ℝ) := by
          have hC0 : 0 < C := by rw [hCdef]; exact Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hΨ1)
          exact_mod_cast (by omega : 1 ≤ C)
        have h3 : (1:ℝ) ≤ (C:ℝ) * (δ⁻¹)^K := by
          calc (1:ℝ) = 1*1 := by norm_num
            _ ≤ (C:ℝ) * (δ⁻¹)^K := mul_le_mul h2 h1 (by norm_num) (by positivity)
        simpa using h3
      · -- delta^K * N ≤ C * 1
        have h1 : (2*A^K*C₁) ≤ (C:ℝ) := by
          refine le_trans ?_ hCΨ
          rw [hΨdef]
          exact le_trans (le_max_right _ _) (le_max_left _ _)
        calc δ^K * (N:ℝ) ≤ 2*A^K*C₁ := hδKN
          _ ≤ (C:ℝ) := h1
          _ = (C:ℝ) * (↑(1:ℕ) : ℝ) := by norm_num
      · -- delta^K * N^d ≤ C * progAvgSum 1 1 f1
        rw [progAvgSum_one_one]
        have h1 : δ^K * (N:ℝ)^P.natDegree ≤ δ * (N:ℝ)^P.natDegree := by
          have hK : δ^K ≤ δ := by
            have h := pow_le_pow_of_le_one hδ0.le hδ1 (by omega : 1 ≤ K)
            simpa using h
          exact mul_le_mul_of_nonneg_right hK (by positivity)
        have h2 : (1:ℝ) ≤ (C:ℝ) := by
          have hC0 : 0 < C := by rw [hCdef]; exact Nat.ceil_pos.mpr (lt_of_lt_of_le zero_lt_one hΨ1)
          exact_mod_cast (by omega : 1 ≤ C)
        calc δ^K * (N:ℝ)^P.natDegree ≤ δ * (N:ℝ)^P.natDegree := h1
          _ ≤ ∑' x : ℤ, ‖f₁ x‖ := hf₁
          _ ≤ (C:ℝ) * ∑' x : ℤ, ‖f₁ x‖ := le_mul_of_one_le_left (by exact tsum_nonneg (fun x => norm_nonneg _)) h2

end

end Work.Peluse
