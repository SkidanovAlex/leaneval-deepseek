import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.fourier_piece
import Submission.Work.GM.Affine.region_I_bound
import Submission.Work.GM.Affine.ghat_fourier_expansion
import Submission.Work.GM.Affine.tail_inv_sq_integral

/-!
# GM §9, region III of the fine case

This file proves `Work.GM.Affine.region_III_bound`: the region-III estimate of GM Lemma 9.2.

`ghat K M₁ M₂ M₃ f` is the Fourier transform of the "smoothed majorant"

`gSum K M₁ M₂ M₃ f u = Σ_{m₁∈R1} Σ_{m₂∈R2} Σ_{m₃∈R3ext} ψ₁(m₃/M₃) f((m₁ u + m₃)/m₂)`

of the affine sum.  Its explicit Fourier expansion (`ghat_fourier_expansion`) is a finite sum of
terms `ψ₁(m₃/M₃) · |m₂/m₁| · Fhat f (ξ m₂/m₁) · e(ξ m₃/m₁)`.  For `|ξ| > T⁶` every frequency
`ξ m₂/m₁` is large, so the decay hypothesis bounds every term and the whole `L²` mass of `ghat`
outside `[-T⁶, T⁶]` is bounded by `≍ Mbig⁶ (∫f)²`.

The estimate is completely explicit (no `T^δ` is really needed: the proof gives a constant
independent of `T`), so the result is stated with the given `T^δ` and the trivial `T^δ ≥ 1`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

/-! ### Auxiliary definitions (the summands of the Fourier expansion) -/

/-- The size of one summand of the Fourier expansion of `ghat`. -/
def gterm (f : ℝ → ℝ) (ξ : ℝ) (m₁ m₂ : ℤ) : ℝ :=
  ((m₂ : ℝ) / |(m₁ : ℝ)|) * ‖Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ))‖

/-- One summand of the Fourier expansion of `ghat` (`ghat_fourier_expansion`). -/
def gsummand (K M₃ : ℝ) (f : ℝ → ℝ) (ξ : ℝ) (m₁ m₂ m₃ : ℤ) : ℂ :=
  ((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ) * ((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
    Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ)) * efun (ξ * (m₃ : ℝ) / (m₁ : ℝ))

/-! ### Elementary auxiliary estimates -/

/-- `SuppHyp C₀ f` implies that `f` has compact support. -/
lemma hasCompactSupport_of_SuppHyp {C₀ : ℝ} {f : ℝ → ℝ} (h : SuppHyp C₀ f) :
    HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1 / C₀) C₀) isCompact_Icc
    (fun x hx => h x (Function.mem_support.mp hx))

/-- The Fourier transform of a non-negative function is bounded by its integral. -/
lemma norm_Fhat_le_integral {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u) (ξ : ℝ) :
    ‖Fhat f ξ‖ ≤ ∫ u, f u := by
  rw [Fhat, Real.fourier_eq (fun u : ℝ => ((f u : ℝ) : ℂ)) ξ]
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm (e := 𝐞) (μ := volume)
    (L := innerₗ ℝ) (f := fun u : ℝ => ((f u : ℝ) : ℂ)) (w := ξ)).trans ?_
  refine le_of_eq (integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_)))
  show ‖((f u : ℝ) : ℂ)‖ = f u
  rw [Complex.norm_real, Real.norm_of_nonneg (hfnn u)]

/-- Cauchy–Schwarz for a double sum. -/
lemma sum2_sq_le (s1 s2 : Finset ℤ) (g : ℤ → ℤ → ℝ) :
    (∑ m₁ ∈ s1, ∑ m₂ ∈ s2, g m₁ m₂) ^ 2
      ≤ (s1.card : ℝ) * (s2.card : ℝ) * ∑ m₁ ∈ s1, ∑ m₂ ∈ s2, (g m₁ m₂) ^ 2 := by
  have h1 : ∀ m₁ ∈ s1, (∑ m₂ ∈ s2, g m₁ m₂) ^ 2
      ≤ (s2.card : ℝ) * ∑ m₂ ∈ s2, (g m₁ m₂) ^ 2 :=
    fun m₁ _ => sq_sum_le_card_mul_sum_sq
  calc (∑ m₁ ∈ s1, ∑ m₂ ∈ s2, g m₁ m₂) ^ 2
      ≤ (s1.card : ℝ) * ∑ m₁ ∈ s1, (∑ m₂ ∈ s2, g m₁ m₂) ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (s1.card : ℝ) * ∑ m₁ ∈ s1, ((s2.card : ℝ) * ∑ m₂ ∈ s2, (g m₁ m₂) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum h1
    _ = (s1.card : ℝ) * (s2.card : ℝ) * ∑ m₁ ∈ s1, ∑ m₂ ∈ s2, (g m₁ m₂) ^ 2 := by
        rw [← Finset.mul_sum]
        ring

/-- A double sum of a constant. -/
lemma sum2_const (s1 s2 : Finset ℤ) (K : ℝ) :
    (∑ m₁ ∈ s1, ∑ m₂ ∈ s2, K) = (s1.card : ℝ) * (s2.card : ℝ) * K := by
  calc (∑ m₁ ∈ s1, ∑ m₂ ∈ s2, K) = ∑ m₁ ∈ s1, (s2.card : ℝ) * K :=
        Finset.sum_congr rfl (fun m₁ _ => by rw [Finset.sum_const, nsmul_eq_mul])
    _ = (s1.card : ℝ) * ((s2.card : ℝ) * K) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (s1.card : ℝ) * (s2.card : ℝ) * K := by ring

/-- Cardinality of the `m₃`-range, without a hypothesis on the size of `M₃`. -/
lemma card_R3ext_le_general {K M₃ : ℝ} (hK : 0 < K) (hM₃ : 0 < M₃) :
    ((R3ext K M₃).card : ℝ) ≤ 2 * (K + 1) * M₃ + 3 := by
  have hx : 0 < (K + 1) * M₃ := by nlinarith
  have hceil : (0 : ℤ) < ⌈(K + 1) * M₃⌉ := Int.ceil_pos.mpr hx
  have h2 : (R3ext K M₃).card = (2 * ⌈(K + 1) * M₃⌉ + 1).toNat := by
    rw [R3ext, Int.card_Icc]; congr 1; ring
  rw [h2]
  have hpos : (0 : ℤ) ≤ 2 * ⌈(K + 1) * M₃⌉ + 1 := by omega
  have hcast : (((2 * ⌈(K + 1) * M₃⌉ + 1).toNat : ℕ) : ℝ)
      = ((2 * ⌈(K + 1) * M₃⌉ + 1 : ℤ) : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hpos)
  rw [hcast]
  push_cast
  have hc := Int.ceil_lt_add_one ((K + 1) * M₃)
  push_cast at hc
  linarith

/-- Once `R2 M₂` is non-empty, the number of terms of the triple sum is bounded by
`80 (2|K|+5) Mbig³`. -/
lemma card_prod_le_of_R2_ne {K M₁ M₂ M₃ Mbig : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁)
    (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) (hM₁M : M₁ ≤ Mbig) (hM₂M : M₂ ≤ Mbig) (hM₃M : M₃ ≤ Mbig)
    (hcard : (R2 M₂).card ≠ 0) :
    ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ)
      ≤ 80 * (2 * |K| + 5) * Mbig ^ 3 := by
  have hMbigpos : 0 < Mbig := lt_of_lt_of_le hM₂ hM₂M
  have hhalf : (1 / 2 : ℝ) ≤ Mbig := by
    have h1 : (1 : ℝ) ≤ ((R2 M₂).card : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hcard)
    have h2 : ((R2 M₂).card : ℝ) ≤ 2 * M₂ := card_R2_le M₂ hM₂
    linarith
  have hc1 : ((R1 M₁).card : ℝ) ≤ 4 * M₁ + 1 := card_R1_le M₁ hM₁
  have hc2 : ((R2 M₂).card : ℝ) ≤ 2 * M₂ := card_R2_le M₂ hM₂
  have hc3 : ((R3ext K M₃).card : ℝ) ≤ 2 * (K + 1) * M₃ + 3 := card_R3ext_le_general hK hM₃
  have hc1' : (0 : ℝ) ≤ ((R1 M₁).card : ℝ) := by positivity
  have hc2' : (0 : ℝ) ≤ ((R2 M₂).card : ℝ) := by positivity
  have hc3' : (0 : ℝ) ≤ ((R3ext K M₃).card : ℝ) := by positivity
  have hprod : ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ)
      ≤ (4 * M₁ + 1) * (2 * M₂) * (2 * (K + 1) * M₃ + 3) := by
    apply mul_le_mul
    · exact mul_le_mul hc1 hc2 hc2' (by positivity)
    · exact hc3
    · exact hc3'
    · positivity
  by_cases hbig : (1 : ℝ) ≤ Mbig
  · have hA : 4 * M₁ + 1 ≤ 5 * Mbig := by linarith
    have hB : 2 * M₂ ≤ 2 * Mbig := by linarith
    have hC : 2 * (K + 1) * M₃ + 3 ≤ (2 * |K| + 5) * Mbig := by
      have e1 : 2 * (K + 1) * M₃ ≤ 2 * (K + 1) * Mbig := by nlinarith
      have e2 : 3 ≤ 3 * Mbig := by linarith
      have hKabs : K ≤ |K| := le_abs_self K
      nlinarith [e1, e2, hKabs, hMbigpos]
    have hC0 : (0 : ℝ) ≤ (2 * |K| + 5) * Mbig := by positivity
    calc ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ)
        ≤ (4 * M₁ + 1) * (2 * M₂) * (2 * (K + 1) * M₃ + 3) := hprod
      _ ≤ (5 * Mbig) * (2 * Mbig) * ((2 * |K| + 5) * Mbig) := by
          apply mul_le_mul
          · exact mul_le_mul hA hB (by positivity) (by positivity)
          · exact hC
          · positivity
          · positivity
      _ = 10 * (2 * |K| + 5) * Mbig ^ 3 := by ring
      _ ≤ 80 * (2 * |K| + 5) * Mbig ^ 3 := by
          have : (0 : ℝ) ≤ 10 * (2 * |K| + 5) * Mbig ^ 3 := by positivity
          nlinarith [this, abs_nonneg K, hMbigpos]
  · push Not at hbig
    have hM₁1 : M₁ < 1 := lt_of_le_of_lt hM₁M hbig
    have hM₃1 : M₃ < 1 := lt_of_le_of_lt hM₃M hbig
    have hA : 4 * M₁ + 1 ≤ 5 := by linarith
    have hB : 2 * M₂ ≤ 2 := by linarith
    have hC : 2 * (K + 1) * M₃ + 3 ≤ 2 * K + 5 := by nlinarith
    have hC0 : (0 : ℝ) ≤ 2 * K + 5 := by linarith
    have h3 : (1 : ℝ) ≤ 8 * Mbig ^ 3 := by
      have h2 : ((1 / 2 : ℝ)) ^ 3 ≤ Mbig ^ 3 := pow_le_pow_left₀ (by norm_num) hhalf 3
      norm_num at h2
      linarith
    calc ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ)
        ≤ (4 * M₁ + 1) * (2 * M₂) * (2 * (K + 1) * M₃ + 3) := hprod
      _ ≤ 5 * 2 * (2 * K + 5) := by
          apply mul_le_mul
          · exact mul_le_mul hA hB (by linarith) (by linarith)
          · exact hC
          · positivity
          · positivity
      _ = 10 * (2 * K + 5) := by ring
      _ ≤ 10 * (2 * |K| + 5) := by
          have hKabs : K ≤ |K| := le_abs_self K
          linarith
      _ ≤ 80 * (2 * |K| + 5) * Mbig ^ 3 := by
          have hc : (0 : ℝ) ≤ 2 * |K| + 5 := by positivity
          nlinarith [h3, hc]

/-- **Pointwise bound.** On `ξ ≠ 0`, the Fourier transform of the majorant is bounded by
`(number of terms)² · A · B / ξ²`, where `A` bounds `Fhat f` and `B/η²` bounds it at infinity. -/
lemma ghat_sq_le {K M₁ M₂ M₃ : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) {A B : ℝ} (hA0 : 0 ≤ A)
    (hB0 : 0 ≤ B) (hA : ∀ η : ℝ, ‖Fhat f η‖ ≤ A)
    (hB : ∀ η : ℝ, η ≠ 0 → ‖Fhat f η‖ ≤ B / η ^ 2) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2
      ≤ (((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ)) ^ 2 * A * B
          / ξ ^ 2 := by
  classical
  -- per-term bound: `gterm f ξ m₁ m₂ ≤ A · B / ξ²` in squares
  have hmod : ∀ m₁ ∈ R1 M₁, ∀ m₂ ∈ R2 M₂, (gterm f ξ m₁ m₂) ^ 2 ≤ A * B / ξ ^ 2 := by
    intro m₁ hm₁ m₂ hm₂
    have hm₁0 : (m₁ : ℝ) ≠ 0 := by
      rw [R1, Finset.mem_filter] at hm₁
      intro h0
      rw [h0] at hm₁
      simp only [Int.cast_zero, abs_zero] at hm₁
      linarith [hm₁.2, hM₁]
    have hm₂pos : 0 < (m₂ : ℝ) := by
      rw [R2, Finset.mem_filter, Finset.mem_Icc] at hm₂
      have h1 : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm₂.1.1
      linarith
    have hm₂0 : (m₂ : ℝ) ≠ 0 := ne_of_gt hm₂pos
    have hβ : ξ * (m₂ : ℝ) / (m₁ : ℝ) ≠ 0 := by
      rw [div_ne_zero_iff]
      exact ⟨mul_ne_zero hξ hm₂0, hm₁0⟩
    have h1 := hB _ hβ
    have h2 := hA (ξ * (m₂ : ℝ) / (m₁ : ℝ))
    have h3 : ‖Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ))‖ ^ 2
        ≤ A * (B / (ξ * (m₂ : ℝ) / (m₁ : ℝ)) ^ 2) := by
      rw [pow_two]
      exact mul_le_mul h2 h1 (norm_nonneg _) hA0
    unfold gterm
    calc (((m₂ : ℝ) / |(m₁ : ℝ)|) * ‖Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ))‖) ^ 2
        = ((m₂ : ℝ) / |(m₁ : ℝ)|) ^ 2 * ‖Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ))‖ ^ 2 := by ring
      _ ≤ ((m₂ : ℝ) / |(m₁ : ℝ)|) ^ 2
            * (A * (B / (ξ * (m₂ : ℝ) / (m₁ : ℝ)) ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = A * B / ξ ^ 2 := by
          rw [div_pow, sq_abs, div_pow, mul_pow]
          field_simp
          try ring
  -- per-term bound: `‖gsummand‖ ≤ gterm`
  have hterm : ∀ m₁ ∈ R1 M₁, ∀ m₂ ∈ R2 M₂, ∀ m₃ ∈ R3ext K M₃,
      ‖gsummand K M₃ f ξ m₁ m₂ m₃‖ ≤ gterm f ξ m₁ m₂ := by
    intro m₁ hm₁ m₂ hm₂ m₃ hm₃
    have hm₂pos : 0 < (m₂ : ℝ) := by
      rw [R2, Finset.mem_filter, Finset.mem_Icc] at hm₂
      have h1 : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm₂.1.1
      linarith
    have hpsi : ‖((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (psi1_nonneg K _)]
      exact psi1_le_one K _
    have hbb : ‖((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ)‖ = (m₂ : ℝ) / |(m₁ : ℝ)| := by
      rw [Complex.norm_real, Real.norm_of_nonneg (abs_nonneg _), abs_div, abs_of_pos hm₂pos]
    have hef : ‖efun (ξ * (m₃ : ℝ) / (m₁ : ℝ))‖ = 1 := norm_efun _
    unfold gterm gsummand
    calc ‖((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ) * ((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
            Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ)) * efun (ξ * (m₃ : ℝ) / (m₁ : ℝ))‖
        = ‖((psi1 K ((m₃ : ℝ) / M₃) : ℝ) : ℂ)‖ * ‖((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ)‖ *
            ‖Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ))‖
            * ‖efun (ξ * (m₃ : ℝ) / (m₁ : ℝ))‖ := by
          rw [norm_mul, norm_mul, norm_mul]
      _ ≤ 1 * ((m₂ : ℝ) / |(m₁ : ℝ)|) * ‖Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ))‖ * 1 := by
          rw [hbb, hef]
          gcongr <;> try exact hpsi
      _ = (m₂ : ℝ) / |(m₁ : ℝ)| * ‖Fhat f (ξ * (m₂ : ℝ) / (m₁ : ℝ))‖ := by ring
  -- the norm of `ghat` is bounded by the triple sum of `gterm`
  have hstep : ‖ghat K M₁ M₂ M₃ f ξ‖
      ≤ ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, gterm f ξ m₁ m₂ := by
    rw [ghat_fourier_expansion hK hM₁ hM₂ hM₃ hf hcs ξ]
    show ‖∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃,
            gsummand K M₃ f ξ m₁ m₂ m₃‖
        ≤ ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, gterm f ξ m₁ m₂
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun m₁ hm₁ => ?_)
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun m₂ hm₂ => ?_)
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun m₃ hm₃ => ?_)
    exact hterm m₁ hm₁ m₂ hm₂ m₃ hm₃
  -- collapse the `m₃` sum and apply Cauchy–Schwarz
  have hcollapse : ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, gterm f ξ m₁ m₂
      = ((R3ext K M₃).card : ℝ) * ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, gterm f ξ m₁ m₂ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m₁ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m₂ _ => ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  have hCS : (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, gterm f ξ m₁ m₂) ^ 2
      ≤ ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) *
          ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, (gterm f ξ m₁ m₂) ^ 2 :=
    sum2_sq_le (R1 M₁) (R2 M₂) (gterm f ξ)
  have hsum_sq_le : ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, (gterm f ξ m₁ m₂) ^ 2
      ≤ ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * (A * B / ξ ^ 2) := by
    calc ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, (gterm f ξ m₁ m₂) ^ 2
        ≤ ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, (A * B / ξ ^ 2) :=
          Finset.sum_le_sum (fun m₁ hm₁ =>
            Finset.sum_le_sum (fun m₂ hm₂ => hmod m₁ hm₁ m₂ hm₂))
      _ = ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * (A * B / ξ ^ 2) :=
          sum2_const (R1 M₁) (R2 M₂) (A * B / ξ ^ 2)
  have hw : (0 : ℝ) ≤ A * B / ξ ^ 2 := by positivity
  calc ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2
      ≤ (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, ∑ m₃ ∈ R3ext K M₃, gterm f ξ m₁ m₂) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hstep 2
    _ = (((R3ext K M₃).card : ℝ)
          * ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, gterm f ξ m₁ m₂) ^ 2 := by rw [hcollapse]
    _ = ((R3ext K M₃).card : ℝ) ^ 2
          * (∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, gterm f ξ m₁ m₂) ^ 2 := by ring
    _ ≤ ((R3ext K M₃).card : ℝ) ^ 2
          * (((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ)
              * ∑ m₁ ∈ R1 M₁, ∑ m₂ ∈ R2 M₂, (gterm f ξ m₁ m₂) ^ 2) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
    _ ≤ ((R3ext K M₃).card : ℝ) ^ 2
          * (((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ)
              * (((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * (A * B / ξ ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hsum_sq_le
    _ = (((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ)) ^ 2
          * A * B / ξ ^ 2 := by ring

/-! ### Region III -/

/-- **Region III of GM Lemma 9.2.** For `|ξ| > T^6` the Fourier decay hypothesis (with the
budget `Λ ≤ 16 c 2 1 T³ ∫f` and `Mbig ≤ T^4`) makes `ghat` negligible:
`∫_{|ξ|>T^6} ‖ghat‖² ≤ C' T^δ Mbig^6 (∫f)²`. -/
theorem region_III_bound {C₀ K T₀ : ℝ} (hC₀ : 1 ≤ C₀) (hK : 0 < K) (hT₀ : 1 ≤ T₀)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₁ M₂ M₃ : ℝ,
        0 < M₁ → M₁ ≤ Mbig → 0 < M₂ → M₂ ≤ Mbig → 0 < M₃ → M₃ ≤ Mbig → Mbig ≤ T ^ 4 →
        (∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
          + (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
          ≤ C' * T ^ δ * Mbig ^ 6 * (∫ u, f u) ^ 2 := by
  refine ⟨204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 5) ^ 2 + 1, by positivity, ?_⟩
  intro T hT f hf hfnn hSupp Λ hΛ hdecay hΛbd Mbig M₁ M₂ M₃ hM₁ hM₁M hM₂ hM₂M hM₃ hM₃M hMbigT
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (by linarith : (0 : ℝ) < T₀) hT
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hT
  have hcs : HasCompactSupport f := hasCompactSupport_of_SuppHyp hSupp
  set A : ℝ := ∫ u, f u with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact integral_nonneg hfnn
  have hc21 : 0 < c 2 1 := by
    have h1 : 0 < 16 * c 2 1 * T ^ 3 * A := by
      rw [hAdef] at hΛbd
      exact lt_of_lt_of_le hΛ hΛbd
    have h2 : 0 ≤ 16 * T ^ 3 * A := by positivity
    have h3 : 0 < c 2 1 * (16 * T ^ 3 * A) := by
      rw [show c 2 1 * (16 * T ^ 3 * A) = 16 * c 2 1 * T ^ 3 * A by ring]
      exact h1
    exact pos_of_mul_pos_left h3 h2
  set B : ℝ := c 2 1 * T ^ 3 * Λ with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hFhatA : ∀ η : ℝ, ‖Fhat f η‖ ≤ A := by
    intro η
    rw [hAdef]
    exact norm_Fhat_le_integral hfnn η
  have hFhatB : ∀ η : ℝ, η ≠ 0 → ‖Fhat f η‖ ≤ B / η ^ 2 := by
    intro η hη
    have h1 := hdecay 2 1 (by norm_num) η hη
    rw [hBdef]
    refine h1.trans (le_of_eq ?_)
    rw [Real.rpow_one, div_pow, sq_abs]
    field_simp
    try ring
  have hT6 : (0 : ℝ) < T ^ 6 := by positivity
  set N : ℝ := ((R1 M₁).card : ℝ) * ((R2 M₂).card : ℝ) * ((R3ext K M₃).card : ℝ) with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; positivity
  have hpt : ∀ ξ : ℝ, ξ ≠ 0 → ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2 ≤ N ^ 2 * A * B / ξ ^ 2 := by
    intro ξ hξ
    rw [hNdef]
    exact ghat_sq_le hK hM₁ hM₂ hM₃ hf hcs hA0 hB0 hFhatA hFhatB hξ
  have hint1 : (∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ N ^ 2 * A * B / T ^ 6 := by
    have hle : (∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
        ≤ ∫ ξ in Set.Ioi (T ^ 6), (N ^ 2 * A * B) / ξ ^ 2 := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun ξ => by positivity)
      · exact (tail_inv_sq_integral (N ^ 2 * A * B) (T ^ 6) hT6).1
      · show ∀ᵐ a ∂(MeasureTheory.volume.restrict (Set.Ioi (T ^ 6))),
            ‖ghat K M₁ M₂ M₃ f a‖ ^ 2 ≤ (N ^ 2 * A * B) / a ^ 2
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
        filter_upwards with ξ hξ
        have hξ0 : ξ ≠ 0 := by
          intro h0
          rw [h0] at hξ
          simp only [Set.mem_Ioi] at hξ
          linarith [hT6]
        exact hpt ξ hξ0
    exact hle.trans (le_of_eq (tail_inv_sq_integral (N ^ 2 * A * B) (T ^ 6) hT6).2.1)
  have hint2 : (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ N ^ 2 * A * B / T ^ 6 := by
    have hle : (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
        ≤ ∫ ξ in Set.Iio (-(T ^ 6)), (N ^ 2 * A * B) / ξ ^ 2 := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun ξ => by positivity)
      · exact (tail_inv_sq_integral (N ^ 2 * A * B) (T ^ 6) hT6).2.2.1
      · show ∀ᵐ a ∂(MeasureTheory.volume.restrict (Set.Iio (-(T ^ 6)))),
            ‖ghat K M₁ M₂ M₃ f a‖ ^ 2 ≤ (N ^ 2 * A * B) / a ^ 2
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Iio]
        filter_upwards with ξ hξ
        have hξ0 : ξ ≠ 0 := by
          intro h0
          rw [h0] at hξ
          simp only [Set.mem_Iio] at hξ
          linarith [hT6]
        exact hpt ξ hξ0
    exact hle.trans (le_of_eq (tail_inv_sq_integral (N ^ 2 * A * B) (T ^ 6) hT6).2.2.2)
  have hsum_int : (∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      + (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
      ≤ 2 * N ^ 2 * A * B / T ^ 6 := by
    have h2 : (2 : ℝ) * (N ^ 2 * A * B / T ^ 6) = 2 * N ^ 2 * A * B / T ^ 6 := by ring
    rw [← h2]
    linarith [hint1, hint2]
  have hAB : A * B ≤ 16 * (c 2 1) ^ 2 * T ^ 6 * A ^ 2 := by
    have h1 : Λ ≤ 16 * c 2 1 * T ^ 3 * A := by rw [hAdef] at hΛbd; exact hΛbd
    rw [hBdef]
    calc A * (c 2 1 * T ^ 3 * Λ)
        ≤ A * (c 2 1 * T ^ 3 * (16 * c 2 1 * T ^ 3 * A)) := by
          apply mul_le_mul_of_nonneg_left _ hA0
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 16 * (c 2 1) ^ 2 * T ^ 6 * A ^ 2 := by ring
  have hmain : 2 * N ^ 2 * A * B / T ^ 6 ≤ 32 * (c 2 1) ^ 2 * N ^ 2 * A ^ 2 := by
    rw [div_le_iff₀ hT6]
    have h2 : (0 : ℝ) ≤ 2 * N ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left hAB h2
    nlinarith [h3, hT6]
  by_cases hcard : (R2 M₂).card = 0
  · have hzero : ∀ ξ : ℝ, ghat K M₁ M₂ M₃ f ξ = 0 := by
      intro ξ
      rw [ghat_fourier_expansion hK hM₁ hM₂ hM₃ hf hcs ξ, Finset.card_eq_zero.mp hcard]
      simp
    have hz1 : (fun ξ : ℝ => ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext ξ
      rw [hzero ξ]
      simp
    rw [hz1]
    simp only [MeasureTheory.integral_zero, add_zero]
    have hTd : 0 < T ^ δ := Real.rpow_pos_of_pos hT0 δ
    have hCpos : (0 : ℝ) < 204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 5) ^ 2 + 1 := by positivity
    have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    have hMbig6 : (0 : ℝ) ≤ Mbig ^ 6 := by positivity
    have hfin : 0 ≤ (204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 5) ^ 2 + 1) * T ^ δ
        * Mbig ^ 6 * A ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCpos) (le_of_lt hTd)) hMbig6) hA2
    linarith
  · have hNle := card_prod_le_of_R2_ne hK hM₁ hM₂ hM₃ hM₁M hM₂M hM₃M hcard
    have hNle' : N ≤ 80 * (2 * |K| + 5) * Mbig ^ 3 := by rw [hNdef]; exact hNle
    have hN2 : N ^ 2 ≤ 6400 * (2 * |K| + 5) ^ 2 * Mbig ^ 6 := by
      calc N ^ 2 ≤ (80 * (2 * |K| + 5) * Mbig ^ 3) ^ 2 := pow_le_pow_left₀ hN0 hNle' 2
        _ = 6400 * (2 * |K| + 5) ^ 2 * Mbig ^ 6 := by ring
    have hXY : 204800 * (c 2 1) ^ 2 * (2 * |K| + 5) ^ 2
        ≤ (204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 5) ^ 2 + 1) * T ^ δ := by
      have h1 : 204800 * (c 2 1) ^ 2 * (2 * |K| + 5) ^ 2
          ≤ 204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 5) ^ 2 + 1 := by
        nlinarith [sq_nonneg (2 * |K| + 5), sq_nonneg (c 2 1)]
      have h2 : (0 : ℝ) ≤ 204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 5) ^ 2 + 1 := by positivity
      exact h1.trans (le_mul_of_one_le_right h2 (Real.one_le_rpow hT1 (le_of_lt hδ)))
    have hMbig6 : (0 : ℝ) ≤ Mbig ^ 6 := by positivity
    have hA2 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
    calc (∫ ξ in Set.Ioi (T ^ 6), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
          + (∫ ξ in Set.Iio (-(T ^ 6)), ‖ghat K M₁ M₂ M₃ f ξ‖ ^ 2)
        ≤ 2 * N ^ 2 * A * B / T ^ 6 := hsum_int
      _ ≤ 32 * (c 2 1) ^ 2 * N ^ 2 * A ^ 2 := hmain
      _ ≤ 32 * (c 2 1) ^ 2 * (6400 * (2 * |K| + 5) ^ 2 * Mbig ^ 6) * A ^ 2 := by
          have hc2 : (0 : ℝ) ≤ 32 * (c 2 1) ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN2 hc2) hA2
      _ = 204800 * (c 2 1) ^ 2 * (2 * |K| + 5) ^ 2 * Mbig ^ 6 * A ^ 2 := by ring
      _ ≤ (204800 * ((c 2 1) ^ 2 + 1) * (2 * |K| + 5) ^ 2 + 1) * T ^ δ * Mbig ^ 6 * A ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hXY hMbig6) hA2

end

end Work.GM.Affine
