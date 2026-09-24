import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.region_I_bound
import Submission.Work.GM.Affine.region_III_bound
import Submission.Work.GM.Affine.ghat_poisson_expansion
import Submission.Work.GM.Affine.card_mul_pairs_le
import Submission.Work.GM.Affine.smoothed_local
import Submission.Work.GM.Affine.smoothed_properties
import Submission.Work.GM.Affine.smoothed_lam_transfer
import Submission.Work.GM.Affine.fine_step_arith
import Submission.Work.GM.Affine.assembly_aux
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.gSum_cauchy_gen
import Submission.Work.GM.Affine.Gfun_integral_le
import Submission.Work.GM.Affine.ghat_fine_core2
import Submission.Work.GM.Affine.supf_le_of_decay_three

/-!
# `Work.GM.Affine.ghat_T1_bound`

GM §9, Proposition 9.1 for GM's majorant `gSum` of the affine sum, in the `Λ`-form used
throughout the area.  The analytic core is `Work.GM.Affine.ghat_fine_core2` (GM §9,
(9.3)–(9.8)); this file contains the downward induction on the exponent budget
(`fine_step_arith`), the base case (`gSum_cauchy_gen`) and the assembly.

The induction is run on the family

`FineQg N C₀ T₁ C₃ c C n` : for `T ≥ T₁`, for every admissible `f` with support constant
`2 ^ (N - n) * C₀`, for every triple `(M₁, M₂, M₃)` with `M₃ ≤ C₃ * Mbig`, `Mbig ≤ T ^ 4`,

`∫ (gSum 1 M₁ M₂ M₃ f)² ≤ C T ^ (100 (2/3)^n) (Mbig⁶ (∫f)² + Mbig⁴ ∫f²)`.

One induction step uses the core (with parameter `1`) applied to `f`, the honest affine sum
`Gfun (2 ^ (N - (n+1)) C₀) T M₂ f` produced by the Poisson step, the induction hypothesis at
level `n` applied to the *smoothed* `f̃` (which has support constant `2 ^ (N - n) C₀` and whose
`Gfun`-range is covered because `2 · 2 ^ (N-(n+1)) C₀ M₂ + 1 ≤ C₃ Mbig`), and `fine_step_arith`.
-/

open Complex MeasureTheory Finset Filter
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.GM.Affine

noncomputable section

/-! ### Elementary helpers -/

/-- `2 ^ (N - n) * C₀ ≥ 1` for `C₀ ≥ 1`. -/
private lemma one_le_two_pow_mul {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (N n : ℕ) :
    (1:ℝ) ≤ 2 ^ (N - n) * C₀ := by
  have h : (1:ℝ) ≤ 2 ^ (N - n) := one_le_pow₀ (by norm_num)
  nlinarith [h, hC₀]

/-- `R1 M₁` is empty when `0 ≤ M₁ < 1/2`. -/
private lemma ghatT1_R1_eq_empty {M₁ : ℝ} (h0 : 0 ≤ M₁) (h : M₁ < 1 / 2) : R1 M₁ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rw [R1, Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨h1, h2⟩, h3⟩ := hm
  have hfl : ⌊2 * M₁⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]; constructor <;> linarith
  rw [hfl] at h1 h2
  simp only [neg_zero] at h1 h2
  have hm0 : m = 0 := by omega
  rw [hm0] at h3
  simp only [Int.cast_zero, abs_zero] at h3
  linarith

/-- `R2 M₂` is empty when `M₂ < 1/2`. -/
private lemma ghatT1_R2_eq_empty {M₂ : ℝ} (h : M₂ < 1 / 2) : R2 M₂ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro m hm
  rw [R2, Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨h1, h2⟩, _⟩ := hm
  have h1' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast h1
  have h2' : (m:ℝ) ≤ 2 * M₂ := le_trans (by exact_mod_cast h2) (Int.floor_le (2 * M₂))
  linarith

/-- `gSum` vanishes pointwise when `Mbig < 1/2` (then `M₁ < 1/2` and `R1 M₁ = ∅`). -/
private lemma gSum_eq_zero_of_Mbig_lt_half {K Mbig M₁ M₂ M₃ : ℝ} {f : ℝ → ℝ}
    (hM₁ : 0 < M₁) (hM₁b : M₁ ≤ Mbig) (hhalf : Mbig < 1 / 2) (u : ℝ) :
    gSum K M₁ M₂ M₃ f u = 0 := by
  simp [gSum, ghatT1_R1_eq_empty (le_of_lt hM₁) (lt_of_le_of_lt hM₁b hhalf)]

/-- `gSum` vanishes pointwise when `M₂ < 1/2` (then `R2 M₂ = ∅`). -/
private lemma gSum_eq_zero_of_M₂_lt_half {K M₁ M₂ M₃ : ℝ} {f : ℝ → ℝ} (hhalf : M₂ < 1 / 2)
    (u : ℝ) : gSum K M₁ M₂ M₃ f u = 0 := by
  simp [gSum, ghatT1_R2_eq_empty hhalf]

/-- A pointwise vanishing square has vanishing integral. -/
private lemma integral_sq_eq_zero_of_pointwise_zero {g : ℝ → ℝ} (h : ∀ u, g u = 0) :
    ∫ u, (g u) ^ 2 = 0 := by
  have : (fun u : ℝ => (g u) ^ 2) = fun _ => (0:ℝ) := by
    funext u; rw [h u]; norm_num
  rw [this]
  simp

/-- `Mbig^6 + 1 ≤ 17 * T^100 * Mbig^4` when `1/2 ≤ Mbig`, `Mbig ≤ T^4` and `1 ≤ T`. -/
private lemma pow6_add_one_le {Mbig T : ℝ} (hMb : 1/2 ≤ Mbig) (hMbT : Mbig ≤ T^4)
    (hT : 1 ≤ T) : Mbig ^ 6 + 1 ≤ 17 * T ^ 100 * Mbig ^ 4 := by
  have hMnn : (0:ℝ) ≤ Mbig := le_trans (by norm_num) hMb
  have hM4 : (1:ℝ)/16 ≤ Mbig ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hMb 4
    norm_num at h
    exact h
  have hM2 : Mbig ^ 2 ≤ T ^ 100 := by
    have h1 : Mbig ^ 2 ≤ (T ^ 4) ^ 2 := pow_le_pow_left₀ hMnn hMbT 2
    have h2 : (T ^ 4 : ℝ) ^ 2 = T ^ (8:ℕ) := by rw [← pow_mul]
    rw [h2] at h1
    exact le_trans h1 (pow_le_pow_right₀ hT (by norm_num))
  have hT100 : (1:ℝ) ≤ T ^ 100 := one_le_pow₀ hT
  have h1 : Mbig ^ 6 ≤ T ^ 100 * Mbig ^ 4 := by
    calc Mbig ^ 6 = Mbig ^ 2 * Mbig ^ 4 := by ring
      _ ≤ T ^ 100 * Mbig ^ 4 := mul_le_mul_of_nonneg_right hM2 (by positivity)
  have h16 : (1:ℝ) ≤ 16 * T ^ 100 * Mbig ^ 4 := by
    have h4 : (1:ℝ) ≤ 16 * Mbig ^ 4 := by linarith
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ (16 * Mbig ^ 4) * T ^ 100 := mul_le_mul h4 hT100 zero_le_one (by positivity)
      _ = 16 * T ^ 100 * Mbig ^ 4 := by ring
  linarith

/-- Crude version of `pow6_add_one_le`: for `T < T₁ ≤ T₁` we only have `Mbig ≤ T^4 ≤ T₁^4`,
hence `Mbig^2 ≤ T₁^8`. -/
private lemma pow6_add_one_le_crude {Mbig T T₁ : ℝ} (hMb : 1/2 ≤ Mbig) (hMbT : Mbig ≤ T^4)
    (hT0 : 0 ≤ T) (hTT₁ : T ≤ T₁) (hT₁ : 1 ≤ T₁) : Mbig ^ 6 + 1 ≤ (T₁ ^ 8 + 32) * Mbig ^ 4 := by
  have hMnn : (0:ℝ) ≤ Mbig := le_trans (by norm_num) hMb
  have hM4 : (1:ℝ)/16 ≤ Mbig ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hMb 4
    norm_num at h
    exact h
  have hM2 : Mbig ^ 2 ≤ T₁ ^ 8 := by
    have h1 : Mbig ^ 2 ≤ (T ^ 4) ^ 2 := pow_le_pow_left₀ hMnn hMbT 2
    have h2 : (T ^ 4 : ℝ) ^ 2 = T ^ (8:ℕ) := by rw [← pow_mul]
    have h3 : T ^ (8:ℕ) ≤ T₁ ^ (8:ℕ) := pow_le_pow_left₀ hT0 hTT₁ 8
    rw [h2] at h1
    exact le_trans h1 h3
  have h1 : Mbig ^ 6 ≤ T₁ ^ 8 * Mbig ^ 4 := by
    calc Mbig ^ 6 = Mbig ^ 2 * Mbig ^ 4 := by ring
      _ ≤ T₁ ^ 8 * Mbig ^ 4 := mul_le_mul_of_nonneg_right hM2 (by positivity)
  have h16 : (1:ℝ) ≤ 32 * Mbig ^ 4 := by linarith
  nlinarith [h1, h16, show (0:ℝ) ≤ Mbig ^ 4 by positivity]

/-- `(max Mbig M₃)^6 + 1 ≤ C₃^6 * (Mbig^6 + 1)` if `M₃ ≤ C₃ * Mbig`, `1 ≤ C₃`, `0 ≤ Mbig`,
`0 < M₃`. -/
private lemma max_pow6_add_one_le {Mbig M₃ C₃ : ℝ} (hM₃ : 0 < M₃) (hM₃b : M₃ ≤ C₃ * Mbig)
    (hC₃ : 1 ≤ C₃) (hMbig : 0 ≤ Mbig) :
    (max Mbig M₃) ^ 6 + 1 ≤ C₃ ^ 6 * (Mbig ^ 6 + 1) := by
  have hC₃nn : (0:ℝ) ≤ C₃ := le_trans zero_le_one hC₃
  have hm : (max Mbig M₃) ^ 6 ≤ C₃ ^ 6 * Mbig ^ 6 := by
    rcases le_total Mbig M₃ with h | h
    · rw [max_eq_right h]
      calc M₃ ^ 6 ≤ (C₃ * Mbig) ^ 6 := pow_le_pow_left₀ (le_of_lt hM₃) hM₃b 6
        _ = C₃ ^ 6 * Mbig ^ 6 := by rw [mul_pow]
    · rw [max_eq_left h]
      have h1 : (1:ℝ) ≤ C₃ ^ 6 := one_le_pow₀ hC₃
      nlinarith [h1, pow_nonneg hMbig 6]
  have h1 : (1:ℝ) ≤ C₃ ^ 6 := one_le_pow₀ hC₃
  have h2 : (0:ℝ) ≤ C₃ ^ 6 * Mbig ^ 6 := mul_nonneg (pow_nonneg hC₃nn 6) (pow_nonneg hMbig 6)
  linarith

/-! ### The induction family -/

/-- `FineQg N C₀ T₁ C₃ c C n`: the downward-induction statement of GM §9 at level `n`, for the
majorant `gSum` with parameter `1` and support constant `2 ^ (N - n) * C₀`. -/
private def FineQg (N : ℕ) (C₀ T₁ C₃ : ℝ) (c : ℕ → ℝ → ℝ) (C : ℝ) (n : ℕ) : Prop :=
  ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) →
    SuppHyp (2 ^ (N - n) * C₀) f →
    ∀ Λ : ℝ, 0 < Λ →
      (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
        ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
      Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
      ∀ Mbig M₁ M₂ M₃ : ℝ,
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → 0 < M₃ → M₃ ≤ C₃ * Mbig →
        Mbig ≤ T ^ 4 →
        ∫ u, (gSum 1 M₁ M₂ M₃ f u) ^ 2 ≤
          C * T ^ (100 * ((2:ℝ) / 3) ^ n) *
            (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2)

/-! ### Base case -/

/-- Base case of the induction (`n = 0`, budget `T^100`), from the elementary Cauchy–Schwarz
bound `gSum_cauchy_gen`. -/
private theorem FineQg_base {N : ℕ} {C₀ T₁ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hT₁ : 1 ≤ T₁)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ FineQg N C₀ T₁ C₃ c C 0 := by
  obtain ⟨Cc, hCcpos, hCc⟩ := gSum_cauchy_gen
  refine ⟨Cc * 4 * C₃ ^ 6 * 17 + 1, by positivity, ?_⟩
  intro T hT f hf hnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃ hM₁ hM₁b hM₂ hM₂b hM₃ hM₃b hMbT
  have hT1 : (1:ℝ) ≤ T := le_trans hT₁ hT
  have hV : (0:ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hU : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hnn
  have hexp : (100:ℝ) * ((2:ℝ)/3) ^ (0:ℕ) = ((100:ℕ):ℝ) := by norm_num
  rw [hexp, Real.rpow_natCast]
  by_cases hhalf : Mbig < 1 / 2
  · rw [integral_sq_eq_zero_of_pointwise_zero
      (fun u => gSum_eq_zero_of_Mbig_lt_half hM₁ hM₁b hhalf u)]
    have h1 : (0:ℝ) ≤ Mbig ^ 6 * (∫ u, f u) ^ 2 := mul_nonneg (pow_nonneg (le_of_lt (lt_of_lt_of_le hM₁ hM₁b)) 6) (sq_nonneg _)
    have h2 : (0:ℝ) ≤ Mbig ^ 4 * ∫ u, (f u) ^ 2 := mul_nonneg (pow_nonneg (le_of_lt (lt_of_lt_of_le hM₁ hM₁b)) 4) hV
    exact mul_nonneg (by positivity) (add_nonneg h1 h2)
  · push_neg at hhalf
    have hMnn : (0:ℝ) ≤ Mbig := le_trans (le_of_lt hM₁) hM₁b
    have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp hsupp
    have hcr := hCc 1 (max Mbig M₃) M₁ M₂ M₃ (by norm_num) (by positivity) hM₁
      (le_trans hM₁b (le_max_left _ _)) hM₂ (le_trans hM₂b (le_max_left _ _)) hM₃
      (le_max_right _ _) f hf hcs hnn
    have hmax6 : (max Mbig M₃) ^ 6 + 1 ≤ C₃ ^ 6 * (Mbig ^ 6 + 1) :=
      max_pow6_add_one_le hM₃ hM₃b hC₃ hMnn
    have h61 : Mbig ^ 6 + 1 ≤ 17 * T ^ 100 * Mbig ^ 4 := pow6_add_one_le hhalf hMbT hT1
    have hCcnn : (0:ℝ) ≤ Cc * 4 := by positivity
    refine le_trans hcr ?_
    have hb0 : Cc * (1 + 1) ^ 2 * ((max Mbig M₃) ^ 6 + 1) * ∫ u, (f u) ^ 2
        = Cc * 4 * ((max Mbig M₃) ^ 6 + 1) * ∫ u, (f u) ^ 2 := by norm_num
    rw [hb0]
    calc Cc * 4 * ((max Mbig M₃) ^ 6 + 1) * ∫ u, (f u) ^ 2
        ≤ Cc * 4 * (C₃ ^ 6 * (Mbig ^ 6 + 1)) * ∫ u, (f u) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hV
          exact mul_le_mul_of_nonneg_left hmax6 hCcnn
      _ = Cc * 4 * C₃ ^ 6 * ((Mbig ^ 6 + 1) * ∫ u, (f u) ^ 2) := by ring
      _ ≤ Cc * 4 * C₃ ^ 6 * ((17 * T ^ 100 * Mbig ^ 4) * ∫ u, (f u) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right h61 hV
      _ = (Cc * 4 * C₃ ^ 6 * 17) * T ^ 100 * (Mbig ^ 4 * ∫ u, (f u) ^ 2) := by ring
      _ ≤ (Cc * 4 * C₃ ^ 6 * 17) * T ^ 100 *
            (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h6 : (0:ℝ) ≤ Mbig ^ 6 * (∫ u, f u) ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
          linarith
      _ ≤ (Cc * 4 * C₃ ^ 6 * 17 + 1) * T ^ 100 *
            (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith

/-! ### Induction step -/

/-- Arithmetic for one descent step, when the core bound carries the extra fallback term
`M ^ 4 * V` (the statement `Work.GM.Affine.ghat_fine_core2`).  Same conclusion as
`Work.GM.Affine.fine_step_arith`. -/
private lemma fine_step_arith2 {C₁ C₂ T δs η M U V J Jb : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hT : 1 ≤ T) (hM : 0 ≤ M) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hδs : 0 ≤ δs) (hη : 0 ≤ η) (hJ : 0 ≤ J) (hJb : 0 ≤ Jb)
    (h : J ≤ C₁ * T ^ δs *
      (M ^ 6 * U ^ 2 + M ^ 2 * Real.sqrt V * Real.sqrt Jb + M ^ 4 * V))
    (hJble : Jb ≤ C₂ * T ^ η * (M ^ 6 * U ^ 2 + M ^ 4 * V)) :
    J ≤ C₁ * (1 + 3 * Real.sqrt C₂ / 2) * T ^ (δs + η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
  have hTnn : (0 : ℝ) ≤ T := le_of_lt hTpos
  have hη2 : 0 ≤ η / 2 := by linarith
  have hA : 0 ≤ M ^ 6 * U ^ 2 := mul_nonneg (pow_nonneg hM 6) (pow_nonneg hU 2)
  have hB : 0 ≤ M ^ 4 * V := mul_nonneg (pow_nonneg hM 4) hV
  have hAB : 0 ≤ M ^ 6 * U ^ 2 + M ^ 4 * V := add_nonneg hA hB
  have hsAB : 0 ≤ Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V) := Real.sqrt_nonneg _
  have hsC2 : 0 ≤ Real.sqrt C₂ := Real.sqrt_nonneg _
  have hTηnn : 0 ≤ T ^ (η / 2) := Real.rpow_nonneg hTnn _
  have hTη1 : 1 ≤ T ^ (η / 2) := Real.one_le_rpow hT hη2
  have hMV : M ^ 2 * Real.sqrt V ≤ Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
    have heq : M ^ 2 * Real.sqrt V = Real.sqrt (M ^ 4 * V) := by
      rw [Real.sqrt_mul (pow_nonneg hM 4) V]
      rw [show Real.sqrt (M ^ 4) = M ^ 2 by
        rw [show M ^ 4 = (M ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (pow_nonneg hM 2)]]
    rw [heq]
    exact Real.sqrt_le_sqrt (by linarith [hA])
  have hsqT : Real.sqrt (T ^ η) = T ^ (η / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hTnn η (1 / 2)]
    congr 1
    ring
  have hsqrtJb :
      Real.sqrt Jb ≤ Real.sqrt C₂ * T ^ (η / 2) * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
    have hs := Real.sqrt_le_sqrt hJble
    rw [show C₂ * T ^ η * (M ^ 6 * U ^ 2 + M ^ 4 * V)
        = (C₂ * T ^ η) * (M ^ 6 * U ^ 2 + M ^ 4 * V) by ring] at hs
    rw [Real.sqrt_mul (mul_nonneg hC₂ (Real.rpow_nonneg hTnn η))
          (M ^ 6 * U ^ 2 + M ^ 4 * V)] at hs
    have hsq : Real.sqrt (C₂ * T ^ η) = Real.sqrt C₂ * T ^ (η / 2) := by
      rw [Real.sqrt_mul hC₂ (T ^ η), hsqT]
    rw [hsq] at hs
    exact hs
  have hstep : M ^ 2 * Real.sqrt V * Real.sqrt Jb
      ≤ Real.sqrt C₂ * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
    have hMVnonneg : 0 ≤ M ^ 2 * Real.sqrt V :=
      mul_nonneg (pow_nonneg hM 2) (Real.sqrt_nonneg V)
    have hmid : M ^ 2 * Real.sqrt V * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V)
        ≤ M ^ 6 * U ^ 2 + M ^ 4 * V := by
      calc M ^ 2 * Real.sqrt V * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V)
          ≤ Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V) * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V) :=
            mul_le_mul_of_nonneg_right hMV hsAB
        _ = M ^ 6 * U ^ 2 + M ^ 4 * V := by rw [← pow_two, Real.sq_sqrt hAB]
    calc M ^ 2 * Real.sqrt V * Real.sqrt Jb
        ≤ M ^ 2 * Real.sqrt V *
            (Real.sqrt C₂ * T ^ (η / 2) * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V)) :=
          mul_le_mul_of_nonneg_left hsqrtJb hMVnonneg
      _ = (Real.sqrt C₂ * T ^ (η / 2)) *
            (M ^ 2 * Real.sqrt V * Real.sqrt (M ^ 6 * U ^ 2 + M ^ 4 * V)) := by ring
      _ ≤ (Real.sqrt C₂ * T ^ (η / 2)) * (M ^ 6 * U ^ 2 + M ^ 4 * V) :=
          mul_le_mul_of_nonneg_left hmid (mul_nonneg hsC2 hTηnn)
      _ = Real.sqrt C₂ * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by ring
  have hmain : M ^ 6 * U ^ 2 + M ^ 2 * Real.sqrt V * Real.sqrt Jb + M ^ 4 * V
      ≤ (1 + 3 * Real.sqrt C₂ / 2) * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
    have hcoef : 1 + Real.sqrt C₂ * T ^ (η / 2)
        ≤ (1 + 3 * Real.sqrt C₂ / 2) * T ^ (η / 2) := by
      have h1 : 1 + Real.sqrt C₂ * T ^ (η / 2) ≤ (1 + Real.sqrt C₂) * T ^ (η / 2) := by
        nlinarith [hTη1]
      have h2 : (1 + Real.sqrt C₂) * T ^ (η / 2)
          ≤ (1 + 3 * Real.sqrt C₂ / 2) * T ^ (η / 2) := by
        apply mul_le_mul_of_nonneg_right _ hTηnn
        linarith [hsC2]
      linarith [h1, h2]
    calc M ^ 6 * U ^ 2 + M ^ 2 * Real.sqrt V * Real.sqrt Jb + M ^ 4 * V
        ≤ (M ^ 6 * U ^ 2 + M ^ 4 * V)
            + Real.sqrt C₂ * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
          linarith [hstep]
      _ = (1 + Real.sqrt C₂ * T ^ (η / 2)) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by ring
      _ ≤ (1 + 3 * Real.sqrt C₂ / 2) * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) :=
          mul_le_mul_of_nonneg_right hcoef hAB
  calc J ≤ C₁ * T ^ δs *
        (M ^ 6 * U ^ 2 + M ^ 2 * Real.sqrt V * Real.sqrt Jb + M ^ 4 * V) := h
    _ ≤ C₁ * T ^ δs *
          ((1 + 3 * Real.sqrt C₂ / 2) * T ^ (η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V)) :=
        mul_le_mul_of_nonneg_left hmain (mul_nonneg hC₁ (Real.rpow_nonneg hTnn δs))
    _ = C₁ * (1 + 3 * Real.sqrt C₂ / 2) * T ^ (δs + η / 2) * (M ^ 6 * U ^ 2 + M ^ 4 * V) := by
        rw [Real.rpow_add hTpos]
        ring

/-- One step of the downward induction: the core (`Work.GM.Affine.ghat_fine_core2`) applied to
`f`, the induction hypothesis applied to the smoothed `f̃` through the honest affine sum
`Gfun`, and the arithmetic of `fine_step_arith`. -/
private theorem FineQg_step {N : ℕ} {C₀ T₁ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₁)
    (hC₃ : 2 ^ N * C₀ + 2 ≤ C₃) (hT₁C : 2 ^ N * C₀ ≤ T₁) (c : ℕ → ℝ → ℝ) {n : ℕ}
    (hn : n + 1 ≤ N) (ih : ∃ C : ℝ, 0 < C ∧ FineQg N C₀ T₁ C₃ c C n) :
    ∃ C : ℝ, 0 < C ∧ FineQg N C₀ T₁ C₃ c C (n + 1) := by
  obtain ⟨Cn, hCnpos, ihn⟩ := ih
  have hC₀nn : (0:ℝ) ≤ C₀ := le_trans zero_le_one hC₀
  have hC₃1 : (1:ℝ) ≤ C₃ := by
    have : (0:ℝ) ≤ 2 ^ N * C₀ := mul_nonneg (by positivity) hC₀nn
    linarith
  obtain ⟨Ccore, hCcorepos, hCcore⟩ :=
    ghat_fine_core2 (C₀ := 2 ^ (N - (n + 1)) * C₀) (K := 1) (T₀ := T₁) (C₃ := C₃)
      (one_le_two_pow_mul hC₀ N (n + 1)) one_pos hT₀ hC₃1 c
      (100 * ((2:ℝ) / 3) ^ (n + 1) / 4) (by positivity)
  have hpow : 2 * (2 ^ (N - (n + 1)) * C₀) = 2 ^ (N - n) * C₀ := by
    have hsub : N - n = N - (n + 1) + 1 := by omega
    rw [hsub, pow_succ]; ring
  have hpow' : (2:ℝ) ^ (N - n) * C₀ = 2 * (2 ^ (N - (n + 1)) * C₀) := hpow.symm
  refine ⟨Ccore * (1 + 3 * Real.sqrt Cn / 2), by positivity, ?_⟩
  intro T hT f hf hnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃ hM₁ hM₁b hM₂ hM₂b hM₃ hM₃b hMbT
  have hT1 : (1:ℝ) ≤ T := le_trans hT₀ hT
  have hUnn : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hnn
  have hVnn : (0:ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hBrnn : (0:ℝ) ≤ Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2 :=
    add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (mul_nonneg (by positivity) hVnn)
  by_cases hhalf : M₂ < 1 / 2
  · rw [integral_sq_eq_zero_of_pointwise_zero (fun u => gSum_eq_zero_of_M₂_lt_half hhalf u)]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCcorepos.le (by positivity))
      (Real.rpow_nonneg (le_trans (by norm_num) hT1) _)) hBrnn
  · push_neg at hhalf
    have hMbhalf : (1:ℝ)/2 ≤ Mbig := le_trans hhalf hM₂b
    have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp hsupp
    have hcore := hCcore T hT f hf hnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
      hM₁ hM₁b hM₂ hM₂b hM₃ hM₃b hMbT
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcore
    have hTsup : 2 * (2 ^ (N - (n + 1)) * C₀) ≤ T := by
      rw [hpow]
      exact le_trans (le_trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le N n)) hC₀nn) hT₁C) hT
    obtain ⟨hsc, hsnn, hssupp, hsdec, hscompat, hsmass, hsl2⟩ :=
      smoothed_lam_transfer (c := c) (C₀ := 2 ^ (N - (n + 1)) * C₀)
        (one_le_two_pow_mul hC₀ N (n + 1)) hTsup hf hnn hsupp hΛ hdec hcompat
    have hssupp' : SuppHyp (2 ^ (N - n) * C₀) (smoothed psiSmooth T f) := by
      rw [← hpow]; exact hssupp
    have hr₃C : 2 * (2 ^ (N - (n + 1)) * C₀) * M₂ + 1 ≤ C₃ * Mbig := by
      have h2 : (1:ℝ) ≤ 2 * Mbig := by linarith
      have hstep1 : 2 * (2 ^ (N - (n + 1)) * C₀) * M₂ ≤ 2 ^ N * C₀ * Mbig := by
        rw [hpow]
        calc 2 ^ (N - n) * C₀ * M₂ = (2 ^ (N - n) * C₀) * M₂ := by ring
          _ ≤ (2 ^ N * C₀) * M₂ := by
              apply mul_le_mul_of_nonneg_right _
                (le_of_lt hM₂)
              exact mul_le_mul_of_nonneg_right
                (pow_le_pow_right₀ (by norm_num) (Nat.sub_le N n)) hC₀nn
          _ ≤ (2 ^ N * C₀) * Mbig := mul_le_mul_of_nonneg_left hM₂b (by positivity)
      calc 2 * (2 ^ (N - (n + 1)) * C₀) * M₂ + 1 ≤ (2 ^ N * C₀ + 2) * Mbig := by
            nlinarith [hstep1, h2, show (0:ℝ) ≤ Mbig by positivity]
        _ ≤ C₃ * Mbig := mul_le_mul_of_nonneg_right hC₃ (by positivity)
    have hIH := ihn T hT (smoothed psiSmooth T f) hsc hsnn hssupp' Λ hΛ hsdec hscompat
      Mbig M₂ M₂ (2 * (2 ^ (N - (n + 1)) * C₀) * M₂ + 1) hM₂ hM₂b hM₂ hM₂b
      (by positivity) hr₃C hMbT
    have hGle := Gfun_integral_le (C₀ := 2 ^ (N - (n + 1)) * C₀)
      (le_trans zero_le_one (one_le_two_pow_mul hC₀ N (n + 1)))
      (lt_of_lt_of_le zero_lt_one hT1) hM₂ hf hcs hnn
    have hJble : ∫ u, (Gfun (2 ^ (N - (n + 1)) * C₀) T M₂ f u) ^ 2 ≤
        Cn * T ^ (100 * ((2:ℝ) / 3) ^ n) *
          (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
      refine le_trans hGle (le_trans hIH ?_)
      have h1 : (∫ u, smoothed psiSmooth T f u) ^ 2 = (∫ u, f u) ^ 2 := by rw [hsmass]
      have h2 : Mbig ^ 4 * ∫ u, (smoothed psiSmooth T f u) ^ 2 ≤
          Mbig ^ 4 * ∫ u, (f u) ^ 2 := mul_le_mul_of_nonneg_left hsl2 (by positivity)
      have h3 : Mbig ^ 6 * (∫ u, smoothed psiSmooth T f u) ^ 2 ≤
          Mbig ^ 6 * (∫ u, f u) ^ 2 := by rw [h1]
      exact mul_le_mul_of_nonneg_left (add_le_add h3 h2)
        (mul_nonneg hCnpos.le (Real.rpow_nonneg (le_trans (by norm_num) hT1) _))
    have hJnn : (0:ℝ) ≤ ∫ u, (gSum 1 M₁ M₂ M₃ f u) ^ 2 := integral_nonneg fun u => sq_nonneg _
    have hJbnn : (0:ℝ) ≤ ∫ u, (Gfun (2 ^ (N - (n + 1)) * C₀) T M₂ f u) ^ 2 :=
      integral_nonneg fun u => sq_nonneg _
    have hmain := fine_step_arith2 (C₁ := Ccore) (C₂ := Cn) (T := T)
      (δs := 100 * ((2:ℝ) / 3) ^ (n + 1) / 4) (η := 100 * ((2:ℝ) / 3) ^ n)
      (M := Mbig) (U := ∫ u, f u) (V := ∫ u, (f u) ^ 2)
      (J := ∫ u, (gSum 1 M₁ M₂ M₃ f u) ^ 2)
      (Jb := ∫ u, (Gfun (2 ^ (N - (n + 1)) * C₀) T M₂ f u) ^ 2)
      hCcorepos.le hCnpos.le hT1 (by positivity) hUnn hVnn (by positivity) (by positivity)
      hJnn hJbnn hcore hJble
    have hexp : 100 * ((2:ℝ) / 3) ^ (n + 1) / 4 + (100 * ((2:ℝ) / 3) ^ n) / 2
        = 100 * ((2:ℝ) / 3) ^ (n + 1) := by
      rw [pow_succ]; ring
    rw [hexp] at hmain
    exact hmain

end

end Work.GM.Affine

namespace Work.GM.Affine

noncomputable section

/-! ### The main theorem -/

theorem ghat_T1_bound {C₀ K T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → 0 < M₃ → M₃ ≤ Mbig → Mbig ≤ T ^ 4 →
        ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 ≤
          C' * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
  -- the number of smoothing steps and the threshold
  obtain ⟨N, hNδ, hN1⟩ : ∃ N : ℕ, 150 * ((2:ℝ) / 3) ^ N ≤ δ ∧ 1 ≤ N := by
    have h2 : Tendsto (fun n : ℕ => ((2:ℝ)/3) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h3 : Tendsto (fun n : ℕ => 150 * ((2:ℝ)/3) ^ n) atTop (nhds 0) := by
      simpa using h2.const_mul 150
    obtain ⟨M, hM⟩ := (h3.eventually (eventually_lt_nhds hδ)).exists
    refine ⟨max M 1, ?_, le_max_right M 1⟩
    have hle : ((2:ℝ)/3) ^ (max M 1) ≤ ((2:ℝ)/3) ^ M :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left M 1)
    have h4 := mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 150)
    linarith
  have hC₀nn : (0:ℝ) ≤ C₀ := le_trans zero_le_one hC₀
  set C₃ : ℝ := 2 ^ (N + 1) * C₀ + 2 with hC₃def
  have hC₃2 : 2 ^ N * C₀ + 2 ≤ C₃ := by
    rw [hC₃def]
    have h : (2:ℝ) ^ N * C₀ ≤ 2 ^ (N + 1) * C₀ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ N)) hC₀nn
    linarith
  have hC₃1 : (1:ℝ) ≤ C₃ := by
    rw [hC₃def]
    have h : (0:ℝ) ≤ 2 ^ (N + 1) * C₀ := mul_nonneg (by positivity) hC₀nn
    linarith
  set T₁ : ℝ := max T₀ (2 ^ (N + 1) * C₀) with hT₁def
  have hT₁T₀ : T₀ ≤ T₁ := le_max_left _ _
  have hT₁C1 : 2 ^ (N + 1) * C₀ ≤ T₁ := le_max_right _ _
  have hT₁C : 2 ^ N * C₀ ≤ T₁ :=
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ N))
      hC₀nn) hT₁C1
  have hT₁1 : (1:ℝ) ≤ T₁ := le_trans hT₀ hT₁T₀
  -- the induction
  have hQ : ∀ n : ℕ, n ≤ N → ∃ C : ℝ, 0 < C ∧ FineQg N C₀ T₁ C₃ c C n := by
    intro n
    induction n with
    | zero => intro _; exact FineQg_base hC₀ hT₁1 hC₃1 c
    | succ n ih =>
        intro hn
        exact FineQg_step (N := N) (C₀ := C₀) (T₁ := T₁) (C₃ := C₃) hC₀ hT₁1 hC₃2 hT₁C c
          hn (ih (Nat.le_of_succ_le hn))
  obtain ⟨CN, hCNpos, hQN⟩ := hQ (N - 1) (by omega)
  -- the core with the target's parameter `K` and exponent `δ/2`
  obtain ⟨CK, hCKpos, hCK⟩ :=
    ghat_fine_core2 (C₀ := C₀) (K := K) (T₀ := T₁) (C₃ := C₃) hC₀ hK hT₁1 hC₃1 c
      (δ / 2) (by linarith)
  obtain ⟨Cc, hCcpos, hCc⟩ := gSum_cauchy_gen
  refine ⟨max (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
      (CK * (1 + 3 * Real.sqrt CN / 2)) + 1, by positivity, ?_⟩
  intro T hT f hf hnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃ hM₁ hM₁b hM₂ hM₂b hM₃ hM₃b hMbT
  have hT0 : (0:ℝ) ≤ T := le_trans (by linarith) hT
  have hT1 : (1:ℝ) ≤ T := le_trans hT₀ hT
  have hTδnn : (0:ℝ) ≤ T ^ δ := Real.rpow_nonneg hT0 δ
  have hUnn : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hnn
  have hVnn : (0:ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hBrnn : (0:ℝ) ≤ Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2 :=
    add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (mul_nonneg (by positivity) hVnn)
  have hC'nn : (0:ℝ) ≤ max (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
      (CK * (1 + 3 * Real.sqrt CN / 2)) + 1 := by
    have h1 : (0:ℝ) ≤ Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ := by positivity
    have h2 := le_max_left (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
      (CK * (1 + 3 * Real.sqrt CN / 2))
    linarith
  have hC'le : CK * (1 + 3 * Real.sqrt CN / 2) ≤
      max (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
        (CK * (1 + 3 * Real.sqrt CN / 2)) + 1 := by
    linarith [le_max_right (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
      (CK * (1 + 3 * Real.sqrt CN / 2))]
  have hC'big : Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ ≤
      max (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
        (CK * (1 + 3 * Real.sqrt CN / 2)) + 1 := by
    linarith [le_max_left (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
      (CK * (1 + 3 * Real.sqrt CN / 2))]
  by_cases hbig : T₁ ≤ T
  · -- main case: the core plus the induction hypothesis on the smoothed function
    by_cases hhalf : M₂ < 1 / 2
    · rw [integral_sq_eq_zero_of_pointwise_zero (fun u => gSum_eq_zero_of_M₂_lt_half hhalf u)]
      exact mul_nonneg (mul_nonneg hC'nn hTδnn) hBrnn
    · push_neg at hhalf
      have hMbhalf : (1:ℝ)/2 ≤ Mbig := le_trans hhalf hM₂b
      have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp hsupp
      have hM₃C₃ : M₃ ≤ C₃ * Mbig := by
        have hMbpos : (0:ℝ) < Mbig := lt_of_lt_of_le hM₂ hM₂b
        exact le_trans hM₃b (le_mul_of_one_le_left (le_of_lt hMbpos) hC₃1)
      have hcore := hCK T hbig f hf hnn hsupp Λ hΛ hdec hcompat Mbig M₁ M₂ M₃
        hM₁ hM₁b hM₂ hM₂b hM₃ hM₃C₃ hMbT
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcore
      have hTsup : 2 * C₀ ≤ T := by
        have h1 : (2:ℝ) * C₀ ≤ 2 ^ (N + 1) * C₀ := by
          apply mul_le_mul_of_nonneg_right _ hC₀nn
          calc (2:ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (N + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        exact le_trans h1 (le_trans hT₁C1 hbig)
      obtain ⟨hsc, hsnn, hssupp, hsdec, hscompat, hsmass, hsl2⟩ :=
        smoothed_lam_transfer (c := c) (C₀ := C₀) hC₀ hTsup hf hnn hsupp hΛ hdec hcompat
      have hpow1 : N - (N - 1) = 1 := by omega
      have hssupp' : SuppHyp (2 ^ (N - (N - 1)) * C₀) (smoothed psiSmooth T f) := by
        rw [hpow1]; simpa using hssupp
      have hr₃C : 2 * C₀ * M₂ + 1 ≤ C₃ * Mbig := by
        have h2 : (1:ℝ) ≤ 2 * Mbig := by linarith
        have hstep1 : 2 * C₀ * M₂ ≤ 2 ^ (N + 1) * C₀ * Mbig := by
          calc 2 * C₀ * M₂ ≤ (2 ^ (N + 1) * C₀) * M₂ := by
                apply mul_le_mul_of_nonneg_right _ (le_of_lt hM₂)
                apply mul_le_mul_of_nonneg_right _ hC₀nn
                calc (2:ℝ) = 2 ^ 1 := by norm_num
                  _ ≤ 2 ^ (N + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
            _ ≤ (2 ^ (N + 1) * C₀) * Mbig := mul_le_mul_of_nonneg_left hM₂b (by positivity)
        calc 2 * C₀ * M₂ + 1 ≤ (2 ^ (N + 1) * C₀ + 2) * Mbig := by
              nlinarith [hstep1, h2, show (0:ℝ) ≤ Mbig by positivity]
          _ = C₃ * Mbig := by rw [hC₃def]
      have hIH := hQN T hbig (smoothed psiSmooth T f) hsc hsnn hssupp' Λ hΛ hsdec hscompat
        Mbig M₂ M₂ (2 * C₀ * M₂ + 1) hM₂ hM₂b hM₂ hM₂b (by positivity) hr₃C hMbT
      have hGle := Gfun_integral_le (C₀ := C₀) hC₀nn (lt_of_lt_of_le zero_lt_one hT1)
        hM₂ hf hcs hnn
      have hJble : ∫ u, (Gfun C₀ T M₂ f u) ^ 2 ≤
          CN * T ^ (100 * ((2:ℝ) / 3) ^ (N - 1)) *
            (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
        refine le_trans hGle (le_trans hIH ?_)
        have h1 : (∫ u, smoothed psiSmooth T f u) ^ 2 = (∫ u, f u) ^ 2 := by rw [hsmass]
        have h2 : Mbig ^ 4 * ∫ u, (smoothed psiSmooth T f u) ^ 2 ≤
            Mbig ^ 4 * ∫ u, (f u) ^ 2 := mul_le_mul_of_nonneg_left hsl2 (by positivity)
        have h3 : Mbig ^ 6 * (∫ u, smoothed psiSmooth T f u) ^ 2 ≤
            Mbig ^ 6 * (∫ u, f u) ^ 2 := by rw [h1]
        exact mul_le_mul_of_nonneg_left (add_le_add h3 h2)
          (mul_nonneg hCNpos.le (Real.rpow_nonneg hT0 _))
      have hJnn : (0:ℝ) ≤ ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 := integral_nonneg fun u => sq_nonneg _
      have hJbnn : (0:ℝ) ≤ ∫ u, (Gfun C₀ T M₂ f u) ^ 2 := integral_nonneg fun u => sq_nonneg _
      have hmain := fine_step_arith2 (C₁ := CK) (C₂ := CN) (T := T) (δs := δ / 2)
        (η := 100 * ((2:ℝ) / 3) ^ (N - 1)) (M := Mbig) (U := ∫ u, f u) (V := ∫ u, (f u) ^ 2)
        (J := ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2) (Jb := ∫ u, (Gfun C₀ T M₂ f u) ^ 2)
        hCKpos.le hCNpos.le hT1 (by positivity) hUnn hVnn (by linarith) (by positivity)
        hJnn hJbnn hcore hJble
      have hexp : δ / 2 + (100 * ((2:ℝ) / 3) ^ (N - 1)) / 2 ≤ δ := by
        have h150 : 100 * ((2:ℝ) / 3) ^ (N - 1) = 150 * ((2:ℝ) / 3) ^ N := by
          conv_rhs => rw [show N = N - 1 + 1 by omega, pow_succ]
          ring
        rw [h150]; linarith
      have hBnn : (0:ℝ) ≤ CK * (1 + 3 * Real.sqrt CN / 2) :=
        mul_nonneg hCKpos.le (by positivity)
      refine le_trans hmain ?_
      calc CK * (1 + 3 * Real.sqrt CN / 2) *
              T ^ (δ / 2 + (100 * ((2:ℝ) / 3) ^ (N - 1)) / 2) *
              (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2)
          ≤ CK * (1 + 3 * Real.sqrt CN / 2) * T ^ δ *
              (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ hBrnn
            exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 hexp) hBnn
        _ ≤ (max (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
              (CK * (1 + 3 * Real.sqrt CN / 2)) + 1) * T ^ δ *
              (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ hBrnn
            exact mul_le_mul_of_nonneg_right hC'le hTδnn
  · -- crude case `T < T₁`
    push_neg at hbig
    have hTδ1 : (1:ℝ) ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
    by_cases hhalf : M₂ < 1 / 2
    · rw [integral_sq_eq_zero_of_pointwise_zero (fun u => gSum_eq_zero_of_M₂_lt_half hhalf u)]
      exact mul_nonneg (mul_nonneg hC'nn hTδnn) hBrnn
    · push_neg at hhalf
      by_cases hMbhalf' : Mbig < 1 / 2
      · rw [integral_sq_eq_zero_of_pointwise_zero
          (fun u => gSum_eq_zero_of_Mbig_lt_half hM₁ hM₁b hMbhalf' u)]
        exact mul_nonneg (mul_nonneg hC'nn hTδnn) hBrnn
      · push_neg at hMbhalf'
        have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp hsupp
        have hcr := hCc K Mbig M₁ M₂ M₃ (le_of_lt hK) (lt_of_lt_of_le hM₁ hM₁b)
          hM₁ hM₁b hM₂ hM₂b hM₃ hM₃b f hf hcs hnn
        have h61 : Mbig ^ 6 + 1 ≤ (T₁ ^ 8 + 32) * Mbig ^ 4 :=
          pow6_add_one_le_crude hMbhalf' hMbT hT0 (le_of_lt hbig) hT₁1
        have hK1nn : (0:ℝ) ≤ (K + 1) ^ 2 := sq_nonneg _
        have hCcnn : (0:ℝ) ≤ Cc * (K + 1) ^ 2 := mul_nonneg hCcpos.le hK1nn
        have hXnn : (0:ℝ) ≤ Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ := by positivity
        refine le_trans hcr ?_
        calc Cc * (K + 1) ^ 2 * (Mbig ^ 6 + 1) * ∫ u, (f u) ^ 2
            ≤ Cc * (K + 1) ^ 2 * ((T₁ ^ 8 + 32) * Mbig ^ 4) * ∫ u, (f u) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ hVnn
              exact mul_le_mul_of_nonneg_left h61 hCcnn
          _ = Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * Mbig ^ 4 * ∫ u, (f u) ^ 2 := by ring
          _ ≤ Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ * Mbig ^ 4 * ∫ u, (f u) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ hVnn
              exact mul_le_mul_of_nonneg_right
                (le_mul_of_one_le_right (by positivity)
                  (Real.one_le_rpow hT₁1 hδ.le)) (by positivity)
          _ ≤ (max (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
                (CK * (1 + 3 * Real.sqrt CN / 2)) + 1) * T ^ δ * Mbig ^ 4 *
                ∫ u, (f u) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ hVnn
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              calc Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ ≤
                    max (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
                      (CK * (1 + 3 * Real.sqrt CN / 2)) + 1 := hC'big
                _ ≤ (max (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
                      (CK * (1 + 3 * Real.sqrt CN / 2)) + 1) * T ^ δ :=
                    le_mul_of_one_le_right (by positivity) hTδ1
          _ = (max (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
                (CK * (1 + 3 * Real.sqrt CN / 2)) + 1) * T ^ δ *
                (Mbig ^ 4 * ∫ u, (f u) ^ 2) := by ring
          _ ≤ (max (Cc * (K + 1) ^ 2 * (T₁ ^ 8 + 32) * T₁ ^ δ)
                (CK * (1 + 3 * Real.sqrt CN / 2)) + 1) * T ^ δ *
                (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have h6 : (0:ℝ) ≤ Mbig ^ 6 * (∫ u, f u) ^ 2 :=
                mul_nonneg (by positivity) (sq_nonneg _)
              linarith

/-! ### The `DecayHyp` (`sup f`) form of the contract

`ghat_T1_bound` is stated with a free parameter `Λ` in the decay hypothesis and the
compatibility `Λ ≤ 16 c 2 1 T³ ∫f`.  The shape used by the assembly (GM Prop 9.1 as quoted in
`Submission.GM.AffineStatement`) writes the decay with `supf f` in place of `Λ`; that is the
instance `Λ := supf f`, whose compatibility is `Work.GM.Affine.supf_le_of_decay_three`. -/

theorem ghat_T1_bound_decayHyp {C₀ K T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        DecayHyp c T f →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → 0 < M₃ → M₃ ≤ Mbig → Mbig ≤ T ^ 4 →
        ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 ≤
          C' * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) := by
  obtain ⟨C', hC'pos, hmain⟩ := ghat_T1_bound (C₀ := C₀) (K := K) (T₀ := T₀) hC₀ hK hT₀ c δ hδ
  refine ⟨C', hC'pos, ?_⟩
  intro T hT f hf hnn hsupp hdec Mbig M₁ M₂ M₃ hM₁ hM₁b hM₂ hM₂b hM₃ hM₃b hMbT
  have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp hsupp
  have hT1 : (1:ℝ) ≤ T := le_trans hT₀ hT
  have hT0 : (0:ℝ) ≤ T := le_trans (by norm_num) hT1
  have hUnn : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hnn
  have hVnn : (0:ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hR : (0:ℝ) ≤ C' * T ^ δ * (Mbig ^ 6 * (∫ u, f u) ^ 2 + Mbig ^ 4 * ∫ u, (f u) ^ 2) :=
    mul_nonneg (mul_nonneg hC'pos.le (Real.rpow_nonneg hT0 δ))
      (add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (mul_nonneg (by positivity) hVnn))
  rcases eq_or_lt_of_le (supf_nonneg hf hcs hnn) with hzero | hpos
  · have hf0 : ∀ u, f u = 0 := by
      intro u
      have hle := le_supf hf hcs u
      rw [← hzero] at hle
      exact le_antisymm hle (hnn u)
    rw [integral_sq_eq_zero_of_pointwise_zero (g := fun u => gSum K M₁ M₂ M₃ f u)
      (fun u => by simp [gSum, hf0])]
    exact hR
  · have hcompat : supf f ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u :=
      supf_le_of_decay_three hT1 hf hcs hnn hdec hpos
    exact hmain T hT f hf hnn hsupp (supf f) hpos
      (fun j ε hε ξ hξ => hdec j ε hε ξ hξ) hcompat
      Mbig M₁ M₂ M₃ hM₁ hM₁b hM₂ hM₂b hM₃ hM₃b hMbT

end

end Work.GM.Affine
