/-
# The assembly of `VarpLossLarge` from the three estimates of §6--§8

This module assembles the large-scale estimate `VarpLossLarge P p₁ p₂` (the regime
`N > splitCut ρ L` of `VarpLossKMT` at the exponents `(p₁,p₂) ≠ (2,2)`) from the three estimates
into which the paper's §6--§8 analysis is divided:

* `ModelApprox` (§6): the concrete column family `colTuple` and the model tuple `modelTuple`
  agree, in the main regime, up to an acceptable error
  `≲ ⟨L⟩^{O(1)} 2^{O(ρL)} ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`;
* `ModelLargeBound` (§8): the model tuple itself obeys that bound;
* `ExceptionalBound`: the contribution of the exceptional scales (admissible and large, but with
  `Log N < k + 2u`) is bounded by `K(Λ) ‖f‖_{ℓ^{p₁}}‖g‖_{ℓ^{p₂}}` — there are only
  `O_{C₀}(1)` such scales, and the crude single-scale Hölder bound applies to each of them.

The pointwise identity `colTuple = modelTuple + (mainPartTuple − modelTuple) + exceptionalPart`
(`colTuple_eq_sum`, `Large/Defs.lean`) splits the variational norm, and the loss exponents of the
first two estimates (which may depend on `C₀` and `r`, but not on `ρ`) are combined into a single
exponent `A = max c₁ c₂ + 1`; the extra factor `2^{ρL}` absorbs the polynomial loss
`⟨L⟩^{max c₁ c₂}`, so that the third (exceptional) contribution, which carries no loss at all,
is absorbed as well.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open Filter Asymptotics MeasureTheory Polynomial Finset Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract Work.Analysis.EndVar

/-! ## Absorbing the polynomial loss into one exponential factor -/

/-- The polynomial factor `⟨L⟩^c` is dominated by an exponential factor `2^{ρL}` times a
constant (which depends on `ρ` and `c`).  This is the elementary fact that an exponential grows
faster than any polynomial; the proof compares `(1+L)^c` with `2^{ρL}` through `ε = ρ log 2 /
(2(c+1))` and the sublinearity of the logarithm. -/
theorem rpow_poly_le_const_exp (c ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 < ρ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ L : ℕ, (1 + (L : ℝ)) ^ c ≤ C * (2 : ℝ) ^ (ρ * (L : ℝ)) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set ε : ℝ := ρ * Real.log 2 / (2 * (c + 1)) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hb : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ ε * ‖x ^ (1:ℝ)‖ :=
    (isLittleO_log_rpow_atTop (r := 1) (by norm_num)).bound hε
  rw [eventually_atTop] at hb
  obtain ⟨x₀, hx₀⟩ := hb
  set L₀ : ℕ := ⌈max x₀ 1⌉₊ with hL₀
  have hcε : c * ε ≤ ρ * Real.log 2 / 2 := by
    have hfrac : c / (2 * (c + 1)) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * (c + 1))]
      linarith
    calc c * ε = (ρ * Real.log 2) * (c / (2 * (c + 1))) := by rw [hεdef]; ring_nf
      _ ≤ (ρ * Real.log 2) * (1/2) := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = ρ * Real.log 2 / 2 := by ring
  have key : ∀ L : ℕ, L₀ ≤ L →
      (1 + (L:ℝ)) ^ c ≤ Real.exp (c * ε) * (2:ℝ) ^ (ρ/2 * (L:ℝ)) := by
    intro L hL
    have hx : x₀ ≤ 1 + (L:ℝ) := by
      have h1 : x₀ ≤ (L₀:ℝ) := le_trans (le_max_left _ _) (Nat.le_ceil _)
      have h2 : (L₀:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
      linarith
    have hlog := hx₀ (1 + (L:ℝ)) hx
    have hpos : (0:ℝ) < 1 + (L:ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith)), Real.rpow_one,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hlog
    have hclog : c * Real.log (1 + (L:ℝ)) ≤ c * (ε * (1 + (L:ℝ))) :=
      mul_le_mul_of_nonneg_left hlog hc
    have hfin : c * Real.log (1 + (L:ℝ)) ≤ c * ε + (ρ/2 * Real.log 2) * (L:ℝ) := by
      have h1 : c * (ε * (1 + (L:ℝ))) = c*ε + c*ε*(L:ℝ) := by ring
      rw [h1] at hclog
      have h2 : c * ε * (L:ℝ) ≤ (ρ/2 * Real.log 2) * (L:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [hcε]
      linarith
    calc (1 + (L:ℝ)) ^ c = Real.exp (Real.log (1 + (L:ℝ)) * c) := Real.rpow_def_of_pos hpos c
      _ = Real.exp (c * Real.log (1 + (L:ℝ))) := by rw [mul_comm]
      _ ≤ Real.exp (c * ε + (ρ/2 * Real.log 2) * (L:ℝ)) := Real.exp_le_exp.mpr hfin
      _ = Real.exp (c * ε) * Real.exp ((ρ/2 * Real.log 2) * (L:ℝ)) := Real.exp_add _ _
      _ = Real.exp (c * ε) * (2:ℝ) ^ (ρ/2 * (L:ℝ)) := by
          congr 1
          rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
          ring_nf
  refine ⟨max (Real.exp (c*ε)) ((1 + (L₀:ℝ))^c) + 1, ?_, fun L => ?_⟩
  · have h0 : (0:ℝ) ≤ max (Real.exp (c*ε)) ((1 + (L₀:ℝ))^c) :=
      le_trans (le_of_lt (Real.exp_pos _)) (le_max_left _ _)
    linarith
  set C : ℝ := max (Real.exp (c*ε)) ((1 + (L₀:ℝ))^c) + 1 with hCdef
  have hCexp : Real.exp (c*ε) ≤ C := le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one)
  have hCL0 : (1 + (L₀:ℝ))^c ≤ C := le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)
  have hpow2 : (1:ℝ) ≤ (2:ℝ) ^ (ρ * (L:ℝ)) :=
    Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) (by positivity : (0:ℝ) ≤ ρ * (L:ℝ))
  by_cases hL : L₀ ≤ L
  · have h2 : (2:ℝ) ^ (ρ/2 * (L:ℝ)) ≤ (2:ℝ) ^ (ρ * (L:ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [hρ, (Nat.cast_nonneg L : (0:ℝ) ≤ (L:ℝ))]
    calc (1 + (L:ℝ)) ^ c ≤ Real.exp (c * ε) * (2:ℝ) ^ (ρ/2 * (L:ℝ)) := key L hL
      _ ≤ C * (2:ℝ) ^ (ρ/2 * (L:ℝ)) := by gcongr
      _ ≤ C * (2:ℝ) ^ (ρ * (L:ℝ)) := by gcongr
  · push_neg at hL
    have h1 : (1 + (L:ℝ))^c ≤ (1 + (L₀:ℝ))^c := by
      apply Real.rpow_le_rpow
      · positivity
      · have : (L:ℝ) ≤ (L₀:ℝ) := by exact_mod_cast (le_of_lt hL)
        linarith
      · exact hc
    calc (1 + (L:ℝ)) ^ c ≤ (1 + (L₀:ℝ))^c := h1
      _ ≤ C := hCL0
      _ = C * 1 := by ring
      _ ≤ C * (2:ℝ) ^ (ρ * (L:ℝ)) := by gcongr

/-- The loss weight `lossWeight c ρ l₁ l₂ k₁ k₂ = ⟨L⟩^c · 2^{cρL}` of the estimates at the
exponents `(p₁,p₂) ≠ (2,2)` is dominated by the single exponential factor
`2^{(c+1)ρL}`, up to a constant depending on `ρ, c`. -/
theorem lossWeight_le (c ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 < ρ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l₁ l₂ k₁ k₂ : ℕ),
      lossWeight c ρ l₁ l₂ k₁ k₂ ≤ C * (2 : ℝ) ^ ((c + 1) * ρ * lmaxR l₁ l₂ k₁ k₂) := by
  obtain ⟨C, hC1, hC⟩ := rpow_poly_le_const_exp c ρ hc hρ
  refine ⟨C, hC1, fun l₁ l₂ k₁ k₂ => ?_⟩
  have hnn : (0:ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
    rw [Work.Analysis.EndVar.lmax]
    refine le_trans (Int.natCast_nonneg l₁) (le_trans (le_max_left _ _) (le_max_left _ _))
  set M : ℕ := (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ)).toNat with hM
  have hMcast : (M : ℝ) = lmaxR l₁ l₂ k₁ k₂ := by
    have hz : ((lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ)).toNat : ℤ) = lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) :=
      Int.toNat_of_nonneg hnn
    rw [lmaxR, hM]
    exact_mod_cast hz
  have h1 : (1 + (M:ℝ)) ^ c ≤ C * (2:ℝ) ^ (ρ * (M:ℝ)) := hC M
  have h2 : (0:ℝ) < (2:ℝ) ^ (c * ρ * (M:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : (2:ℝ) ^ (ρ * (M:ℝ)) * (2:ℝ) ^ (c * ρ * (M:ℝ))
      = (2:ℝ) ^ ((c+1) * ρ * (M:ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  rw [lossWeight, ← hMcast]
  calc (1 + (M:ℝ)) ^ c * (2:ℝ) ^ (c * ρ * (M:ℝ))
      ≤ (C * (2:ℝ) ^ (ρ * (M:ℝ))) * (2:ℝ) ^ (c * ρ * (M:ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt h2)
    _ = C * ((2:ℝ) ^ (ρ * (M:ℝ)) * (2:ℝ) ^ (c * ρ * (M:ℝ))) := by ring
    _ = C * (2:ℝ) ^ ((c+1) * ρ * (M:ℝ)) := by rw [h3]


/-- Monotonicity of the loss weight in the loss exponent `c` (for `ρ ≥ 0`). -/
theorem lossWeight_mono {c c' ρ : ℝ} (l₁ l₂ k₁ k₂ : ℕ) (hc : c ≤ c') (hρ : 0 ≤ ρ) :
    lossWeight c ρ l₁ l₂ k₁ k₂ ≤ lossWeight c' ρ l₁ l₂ k₁ k₂ := by
  have hL : (0:ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
    have hnn : (0:ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      rw [Work.Analysis.EndVar.lmax]
      exact le_trans (Int.natCast_nonneg l₁) (le_trans (le_max_left _ _) (le_max_left _ _))
    rw [lmaxR]
    exact_mod_cast hnn
  have h1 : (1 + lmaxR l₁ l₂ k₁ k₂) ^ c ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ c' :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hc
  have h2 : (2:ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) ≤ (2:ℝ) ^ (c' * ρ * lmaxR l₁ l₂ k₁ k₂) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    calc c * ρ * lmaxR l₁ l₂ k₁ k₂ = (c * ρ) * lmaxR l₁ l₂ k₁ k₂ := by ring
      _ ≤ (c' * ρ) * lmaxR l₁ l₂ k₁ k₂ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hρ) hL
      _ = c' * ρ * lmaxR l₁ l₂ k₁ k₂ := by ring
  rw [lossWeight, lossWeight]
  exact mul_le_mul h1 h2 (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by linarith) _)

/-- **The assembly of `VarpLossLarge`.**  The three estimates of §6--§8 (`ModelApprox`,
`ModelLargeBound`, `ExceptionalBound`) imply the large-scale estimate `VarpLossLarge P p₁ p₂`. -/
theorem largeLoss_of_bounds (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (h1 : ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
    (h2 : ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
    (h3 : ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r → ∃ K : NNReal → NNReal,
      ∀ (ρ : ℝ) (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        0 < ρ → ρ ≤ 1 → 1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :
    VarpLossLarge P p₁ p₂ := by
  intro C₀ r hC₀ hr
  obtain ⟨c₁, hc₁, s₁, hs₁, hA⟩ := h1 C₀ r hC₀ hr
  obtain ⟨c₂, hc₂, s₂, hs₂, hB⟩ := h2 C₀ r hC₀ hr
  obtain ⟨K₃, hC⟩ := h3 C₀ r hC₀ hr
  have hc : (0:ℝ) ≤ max c₁ c₂ := le_trans hc₁ (le_max_left _ _)
  refine ⟨max c₁ c₂ + 1, by positivity, min (min s₁ s₂) 1, lt_min (lt_min hs₁ hs₂) one_pos, ?_⟩
  intro ρ hρ hρle
  have hρs₁ : ρ ≤ s₁ := le_trans hρle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρs₂ : ρ ≤ s₂ := le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_right _ _)
  obtain ⟨K₁, hA'⟩ := hA ρ hρ hρs₁
  obtain ⟨K₂, hB'⟩ := hB ρ hρ hρs₂
  obtain ⟨Cw, hCw1, hCw⟩ := lossWeight_le (max c₁ c₂) ρ hc hρ
  set CW : NNReal := ⟨Cw, le_trans zero_le_one hCw1⟩ with hCWdef
  refine ⟨fun Λ => max 1 ((K₁ Λ + K₂ Λ + K₃ Λ) * CW), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hq : 1 ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  -- the three estimates
  have e1 := hA' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  have e2 := hB' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  have e3 := hC ρ a Λ l₁ l₂ k₁ k₂ f g hρ hρ1 hΛ ha ha1
  -- abbreviations for the four families
  set Fc : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFc
  set Fm : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFm
  set Fa : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFa
  set Fe : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFe
  set X : ENNReal := eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count with hX
  -- abbreviations for the four scalar families and the scalar factors
  set Fc : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFc
  set Fm : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFm
  set Fa : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFa
  set Fe : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFe
  set Wm : ENNReal := ENNReal.ofReal (lossWeight (max c₁ c₂) ρ l₁ l₂ k₁ k₂) with hWm
  set W : ENNReal := ENNReal.ofReal
    (((2:ℝ) ^ ((max c₁ c₂ + 1) * ρ * lmaxR l₁ l₂ k₁ k₂))) with hW
  set Cf : ENNReal := (CW : ENNReal) with hCf
  set X : ENNReal := MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
    * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hX
  -- the pointwise splitting of the column family
  have hsplit0 : ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + (PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) := by
    intro x
    have heq : (fun n : ℕ => colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = (fun n : ℕ => modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            + ((mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) := by
      funext n
      have hpt := congrFun (congrFun (colTuple_eq_sum ρ P C₀ a f g l₁ l₂ k₁ k₂) n) x
      simpa only [Pi.add_apply, Pi.sub_apply] using hpt
    rw [heq]
    calc PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            + ((mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              (mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) :=
          variationalNorm_add_le hr1 _ _
      _ ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + (PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) := by
          gcongr
          exact variationalNorm_add_le hr1 _ _
  have hsplit : ∀ x : ℤ, Fc x ≤ Fm x + (Fa x + Fe x) := by
    intro x
    simpa only [hFc, hFm, hFa, hFe] using hsplit0 x
  -- the scalar estimates
  have hCWreal : (CW : ENNReal) = ENNReal.ofReal Cw :=
    (ENNReal.ofReal_coe_nnreal (p := CW)).symm
  have hWm_le : Wm ≤ Cf * W := by
    rw [hWm, hW, hCf, hCWreal, ← ENNReal.ofReal_mul (le_trans zero_le_one hCw1)]
    exact ENNReal.ofReal_le_ofReal (hCw l₁ l₂ k₁ k₂)
  have hW1 : (1:ENNReal) ≤ W := by
    rw [hW, ENNReal.one_le_ofReal]
    refine Real.one_le_rpow (by norm_num) ?_
    have hL : (0:ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
      have hnn : (0:ℤ) ≤ lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
        rw [Work.Analysis.EndVar.lmax]
        exact le_trans (Int.natCast_nonneg l₁) (le_trans (le_max_left _ _) (le_max_left _ _))
      rw [lmaxR]
      exact_mod_cast hnn
    exact mul_nonneg (mul_nonneg (by linarith) hρ.le) hL
  have hCW1 : (1:ENNReal) ≤ Cf := by
    rw [hCf]
    have h1 : ((1:NNReal) : ENNReal) ≤ (CW : ENNReal) := by
      rw [ENNReal.coe_le_coe]
      exact hCw1
    simpa using h1
  -- the three bounds, in the abridged notation
  have b1 : MeasureTheory.eLpNorm Fa ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ (K₁ Λ : ENNReal) * Wm * X := by
    rw [hFa, hX]
    have hw : ENNReal.ofReal (lossWeight c₁ ρ l₁ l₂ k₁ k₂) ≤ Wm := by
      rw [hWm]
      exact ENNReal.ofReal_le_ofReal (lossWeight_mono l₁ l₂ k₁ k₂ (le_max_left _ _) hρ.le)
    refine e1.trans ?_
    calc (K₁ Λ : ENNReal) * ENNReal.ofReal (lossWeight c₁ ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
        = (K₁ Λ : ENNReal) * ENNReal.ofReal (lossWeight c₁ ρ l₁ l₂ k₁ k₂)
          * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by ring
      _ ≤ (K₁ Λ : ENNReal) * Wm * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :=
          mul_le_mul_left (mul_le_mul_right hw (K₁ Λ : ENNReal)) _
  have b2 : MeasureTheory.eLpNorm Fm ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ (K₂ Λ : ENNReal) * Wm * X := by
    rw [hFm, hX]
    have hw : ENNReal.ofReal (lossWeight c₂ ρ l₁ l₂ k₁ k₂) ≤ Wm := by
      rw [hWm]
      exact ENNReal.ofReal_le_ofReal (lossWeight_mono l₁ l₂ k₁ k₂ (le_max_right _ _) hρ.le)
    refine e2.trans ?_
    calc (K₂ Λ : ENNReal) * ENNReal.ofReal (lossWeight c₂ ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
        = (K₂ Λ : ENNReal) * ENNReal.ofReal (lossWeight c₂ ρ l₁ l₂ k₁ k₂)
          * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by ring
      _ ≤ (K₂ Λ : ENNReal) * Wm * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :=
          mul_le_mul_left (mul_le_mul_right hw (K₂ Λ : ENNReal)) _
  have b3 : MeasureTheory.eLpNorm Fe ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ (K₃ Λ : ENNReal) * X := by
    rw [hFe, hX]
    simpa only [mul_assoc] using e3
  -- the algebraic steps
  have step1 : (K₂ Λ : ENNReal) * Wm * X + ((K₁ Λ : ENNReal) * Wm * X + (K₃ Λ : ENNReal) * X)
      ≤ (K₂ Λ : ENNReal) * (Cf * W) * X
        + ((K₁ Λ : ENNReal) * (Cf * W) * X + (K₃ Λ : ENNReal) * W * X) := by
    have h2 : (K₂ Λ : ENNReal) * Wm * X ≤ (K₂ Λ : ENNReal) * (Cf * W) * X :=
      mul_le_mul_left (mul_le_mul_right hWm_le (K₂ Λ : ENNReal)) X
    have h3 : (K₁ Λ : ENNReal) * Wm * X ≤ (K₁ Λ : ENNReal) * (Cf * W) * X :=
      mul_le_mul_left (mul_le_mul_right hWm_le (K₁ Λ : ENNReal)) X
    have h4 : (K₃ Λ : ENNReal) * X ≤ (K₃ Λ : ENNReal) * W * X := by
      calc (K₃ Λ : ENNReal) * X = (K₃ Λ : ENNReal) * 1 * X := by ring
        _ ≤ (K₃ Λ : ENNReal) * W * X :=
            mul_le_mul_left (mul_le_mul_right hW1 (K₃ Λ : ENNReal)) X
    exact add_le_add h2 (add_le_add h3 h4)
  have step2 : (K₂ Λ : ENNReal) * (Cf * W) * X
        + ((K₁ Λ : ENNReal) * (Cf * W) * X + (K₃ Λ : ENNReal) * W * X)
      ≤ ((K₁ Λ : ENNReal) + (K₂ Λ : ENNReal) + (K₃ Λ : ENNReal)) * (Cf * W) * X := by
    have hWcf : W ≤ Cf * W := by
      calc W = 1 * W := (one_mul W).symm
        _ ≤ Cf * W := mul_le_mul_left hCW1 W
    have h4 : (K₃ Λ : ENNReal) * W * X ≤ (K₃ Λ : ENNReal) * (Cf * W) * X :=
      mul_le_mul_left (mul_le_mul_right hWcf (K₃ Λ : ENNReal)) X
    calc (K₂ Λ : ENNReal) * (Cf * W) * X
          + ((K₁ Λ : ENNReal) * (Cf * W) * X + (K₃ Λ : ENNReal) * W * X)
        ≤ (K₂ Λ : ENNReal) * (Cf * W) * X
          + ((K₁ Λ : ENNReal) * (Cf * W) * X + (K₃ Λ : ENNReal) * (Cf * W) * X) :=
          add_le_add_right (add_le_add_right h4 ((K₁ Λ : ENNReal) * (Cf * W) * X))
            ((K₂ Λ : ENNReal) * (Cf * W) * X)
      _ = ((K₁ Λ : ENNReal) + (K₂ Λ : ENNReal) + (K₃ Λ : ENNReal)) * (Cf * W) * X := by ring
  have step3 : ((K₁ Λ : ENNReal) + (K₂ Λ : ENNReal) + (K₃ Λ : ENNReal)) * (Cf * W) * X
      ≤ (max 1 ((K₁ Λ + K₂ Λ + K₃ Λ) * CW) : ENNReal) * W * X := by
    have hSC : ((K₁ Λ : ENNReal) + (K₂ Λ : ENNReal) + (K₃ Λ : ENNReal)) * Cf
        ≤ (max 1 ((K₁ Λ + K₂ Λ + K₃ Λ) * CW) : ENNReal) := by
      have h1 : ((K₁ Λ : ENNReal) + (K₂ Λ : ENNReal) + (K₃ Λ : ENNReal)) * Cf
          = (((K₁ Λ + K₂ Λ + K₃ Λ) * CW : NNReal) : ENNReal) := by
        rw [hCf, ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_add]
      rw [h1]
      exact_mod_cast (le_max_right (1:NNReal) ((K₁ Λ + K₂ Λ + K₃ Λ) * CW))
    calc ((K₁ Λ : ENNReal) + (K₂ Λ : ENNReal) + (K₃ Λ : ENNReal)) * (Cf * W) * X
        = (((K₁ Λ : ENNReal) + (K₂ Λ : ENNReal) + (K₃ Λ : ENNReal)) * Cf) * W * X := by ring
      _ ≤ (max 1 ((K₁ Λ + K₂ Λ + K₃ Λ) * CW) : ENNReal) * W * X :=
          mul_le_mul_left (mul_le_mul_left hSC W) X
  -- monotonicity and subadditivity of `eLpNorm`
  have hmono : MeasureTheory.eLpNorm Fc ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => Fm x + (Fa x + Fe x))
          ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := Fc) (g := fun x : ℤ => Fm x + (Fa x + Fe x))
      (fun x => by simpa only [enorm_eq_self] using hsplit x)
  have hsub1 : MeasureTheory.eLpNorm (fun x : ℤ => Fm x + (Fa x + Fe x))
        ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm Fm ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => Fa x + Fe x)
            ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_add_le hq
  have hsub2 : MeasureTheory.eLpNorm (fun x : ℤ => Fa x + Fe x)
        ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm Fa ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm Fe ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_add_le hq
  have hmain : MeasureTheory.eLpNorm Fc ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ (max 1 ((K₁ Λ + K₂ Λ + K₃ Λ) * CW) : ENNReal) * W * X :=
    hmono.trans (hsub1.trans ((add_le_add_right hsub2 _).trans
      ((add_le_add b2 (add_le_add b1 b3)).trans (step1.trans (step2.trans step3)))))
  have hconv : (max 1 ((K₁ Λ + K₂ Λ + K₃ Λ) * CW) : ENNReal)
      = ((max 1 ((K₁ Λ + K₂ Λ + K₃ Λ) * CW) : NNReal) : ENNReal) :=
    (ENNReal.coe_max (1:NNReal) ((K₁ Λ + K₂ Λ + K₃ Λ) * CW)).symm
  have hmain'' : MeasureTheory.eLpNorm Fc ((p₁⁻¹ + p₂⁻¹)⁻¹) MeasureTheory.Measure.count
      ≤ ((max 1 ((K₁ Λ + K₂ Λ + K₃ Λ) * CW) : NNReal) : ENNReal) * W * X := by
    rw [← hconv]
    exact hmain
  simpa only [hW, hX, hFc, colTuple, ← mul_assoc, lmaxR] using hmain''

end

end Work.KMTAreas.A7
