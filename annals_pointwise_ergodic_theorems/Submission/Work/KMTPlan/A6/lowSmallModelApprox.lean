/-
# The small-scale model approximation of the low case (area A6)

Target: `Work.KMTPlan.A6.lowSmallModelApprox` — Krause--Mirek--Tao's Proposition `mod-approx`
(Annals 195 (2022), §6), composed with the functional calculus `bn-ident`, at the exponents
`(p₁,p₂,p) = (2,2,1)`, in the *low* case `k₁ = 0 ∨ k₂ = 0` and at the *small* scales
`⌊a n⌋ ≤ splitCut ρ L`.

Both columns are bilinear convolution operators on `ℤ`, so the estimate is proved through the
paper's `crude-mult`(ii): the `ℓ¹(ℤ²)`-mass of the kernel of the *difference*
`colSmall − lowModel` is bounded by the `ξ`-derivatives of the symbol of the difference, which is
the paper's `M₀` times the two §5 bumps (`Work.KMTPlan.A6.symD`); those derivatives are the
paper's single-scale symbol estimate (`Work.A7.M0DerivBound`,
`Work.A7.ModelApproxCore_M0_deriv_bound`).

The pieces of the proof are:

* `Work.KMTPlan.A6.colSmall_eq_bilinOp_symC` — the concrete column is `bilinOp` with the
  coefficient kernel of the symbol `symC`;
* `Work.KMTPlan.A6.lowModel_eq_bilinOp_symM` — the same for the model column and `symM`;
* `Work.KMTPlan.A6.symC_sub_symM_eq_symD` — the collapse `symC − symM = symD` (the paper's
  `mod-approx` at the level of symbols, under the non-aliasing of the arithmetic frequencies);
* `Work.KMTPlan.A6.symD_deriv_bound` — the paper's `ξ`-derivative estimates for `symD`;
* `Work.KMTPlan.A6.symD_period_contDiff`, `Work.KMTPlan.A6.symC_symM_summable`,
  `Work.KMTPlan.A6.coeff2_sub_symC_symM` — periodicity/smoothness of `symD`, `ℓ¹`-summability of
  the two kernels and the linearity of `coeff2`, which turn the two operator identities into the
  kernel identity for the difference;
* `Work.KMTPlan.A6.modelWeight_absorbs_symD` — the weight arithmetic;
* `Work.KMTPlan.A6.lowSmall_crude_bound` and `Work.KMTPlan.A6.lcL_le_of_not_nonAliasing` — the
  crude bound for the (finitely many, `ρ`-dependent) scales on which the non-aliasing of the
  arithmetic frequencies fails.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.symC_sub_symM_eq_symD
import Submission.Work.KMTPlan.A6.symD_deriv_bound
import Submission.Work.KMTPlan.A6.lowSmall_crude_bound
import Submission.Work.KMTPlan.A6.modelWeight_absorbs_symD
import Submission.Work.KMTPlan.A6.symD_period_contDiff
import Submission.Work.KMTPlan.A6.symC_symM_summable
import Submission.Work.KMTPlan.A6.coeff2_sub_symC_symM
import Submission.Work.KMTPlan.A6.lcL_le_of_not_nonAliasing
import Submission.Work.KMTPlan.A6.SymToolbox_tsum_coeff2_le

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6
noncomputable section
open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7
open Work.Analysis.EndVar


/-! ## Elementary weight arithmetic -/

lemma modelWeight_mono_A (ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) {A A' : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') :
    modelWeight A ρ l₁ l₂ k₁ k₂ ≤ modelWeight A' ρ l₁ l₂ k₁ k₂ := by
  rw [modelWeight, modelWeight]
  have h1 : (1 + lmaxR l₁ l₂ k₁ k₂) ^ A ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ A' :=
    Real.rpow_le_rpow_of_exponent_le (one_add_lmaxR_ge_one l₁ l₂ k₁ k₂) hAA
  have h2 : (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂))
      ≤ (2 : ℝ) ^ (A' * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hAA (Real.rpow_nonneg (by norm_num) _))
  exact mul_le_mul h1 h2 (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (le_of_lt (one_add_lmaxR_pos l₁ l₂ k₁ k₂)) _)

lemma two_pow_le_modelWeight (ρ : ℝ) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    (2 : ℝ) ^ A ≤ modelWeight A ρ l₁ l₂ k₁ k₂ := by
  rw [modelWeight]
  have h1 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ A :=
    Real.one_le_rpow (one_add_lmaxR_ge_one l₁ l₂ k₁ k₂) hA
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hρ (lmaxR_nonneg l₁ l₂ k₁ k₂))
  have h4 : A ≤ A * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂) := by nlinarith [h3, hA]
  have h2 : (2 : ℝ) ^ A ≤ (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
  calc (2 : ℝ) ^ A = 1 * (2 : ℝ) ^ A := by ring
    _ ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ A * (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂)) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (le_of_lt (one_add_lmaxR_pos l₁ l₂ k₁ k₂)) _)

lemma one_add_Sval_sq_div_le (P : ℤ[X]) (N k₁ k₂ : ℕ) (hN : 1 ≤ N) :
    1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ)
      ≤ (2 : ℝ) ^ (2 * (k₁ + P.natDegree * k₂) + 3) := by
  set Kk : ℕ := k₁ + P.natDegree * k₂ with hKk
  have hk₁ : k₁ ≤ Kk := Nat.le_add_right k₁ _
  have hk₂ : P.natDegree * k₂ ≤ Kk := Nat.le_add_left _ k₁
  have hSval : Work.A7.Sval P k₁ k₂ ≤ (2 : ℝ) ^ (Kk + 1) := by
    rw [Work.A7.Sval]
    have h1 : (2 : ℝ) ^ k₁ ≤ (2 : ℝ) ^ Kk := pow_le_pow_right₀ (by norm_num) hk₁
    have h2 : (2 : ℝ) ^ (P.natDegree * k₂) ≤ (2 : ℝ) ^ Kk := pow_le_pow_right₀ (by norm_num) hk₂
    calc (2 : ℝ) ^ k₁ + (2 : ℝ) ^ (P.natDegree * k₂) ≤ (2 : ℝ) ^ Kk + (2 : ℝ) ^ Kk := by linarith
      _ = (2 : ℝ) ^ (Kk + 1) := by rw [pow_succ]; ring
  have h0 : (0 : ℝ) ≤ Work.A7.Sval P k₁ k₂ := by rw [Work.A7.Sval]; positivity
  have hsq : (Work.A7.Sval P k₁ k₂) ^ 2 ≤ (2 : ℝ) ^ (2 * Kk + 2) := by
    calc (Work.A7.Sval P k₁ k₂) ^ 2 ≤ ((2 : ℝ) ^ (Kk + 1)) ^ 2 := pow_le_pow_left₀ h0 hSval 2
      _ = (2 : ℝ) ^ (2 * Kk + 2) := by rw [← pow_mul]; ring_nf
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdiv : (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) ≤ (Work.A7.Sval P k₁ k₂) ^ 2 := by
    rw [div_le_iff₀ hNpos]
    calc (Work.A7.Sval P k₁ k₂) ^ 2 = (Work.A7.Sval P k₁ k₂) ^ 2 * 1 := by ring
      _ ≤ (Work.A7.Sval P k₁ k₂) ^ 2 * (N : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hN) (sq_nonneg _)
  have hbig : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * Kk + 2) := one_le_pow₀ (by norm_num)
  have hstep : (2 : ℝ) ^ (2 * Kk + 2) * 2 = (2 : ℝ) ^ (2 * Kk + 3) := by
    rw [← pow_succ]
  calc 1 + (Work.A7.Sval P k₁ k₂) ^ 2 / (N : ℝ) ≤ 1 + (2 : ℝ) ^ (2 * Kk + 2) := by linarith
    _ ≤ (2 : ℝ) ^ (2 * Kk + 2) + (2 : ℝ) ^ (2 * Kk + 2) := by linarith
    _ = (2 : ℝ) ^ (2 * Kk + 3) := by rw [← hstep]; ring
    _ = (2 : ℝ) ^ (2 * (k₁ + P.natDegree * k₂) + 3) := by rw [hKk]

lemma uScale_mono {ρ : ℝ} (hρ : 0 ≤ ρ) : Monotone (fun L : ℕ => uScale ρ L) := by
  intro L L' hLL
  have h1 : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (L' : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
    have h : (L : ℝ) ≤ (L' : ℝ) := by exact_mod_cast hLL
    nlinarith
  have h2 : ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋
      ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L' : ℝ))⌋ := by
    refine Int.floor_mono ?_
    simpa using h1
  show Work.Analysis.EndVar.scaleCount 1 ρ L ≤ Work.Analysis.EndVar.scaleCount 1 ρ L'
  rw [Work.Analysis.EndVar.scaleCount, Work.Analysis.EndVar.scaleCount]
  exact Int.toNat_le_toNat (by simpa using h2)

lemma splitCut_mono (ρ : ℝ) (hρ : 0 ≤ ρ) {L B : ℕ} (h : L ≤ B) : splitCut ρ L ≤ splitCut ρ B := by
  rw [splitCut, splitCut]
  exact pow_le_pow_right₀ (by norm_num) (pow_le_pow_right₀ (by norm_num) (uScale_mono hρ h))

/-- `coeff2` depends only on the pointwise values of the symbol. -/
lemma coeff2_congr {σ τ : ℝ → ℝ → ℂ} (h : ∀ x y, σ x y = τ x y) (p₁ p₂ : ℤ) :
    coeff2 σ p₁ p₂ = coeff2 τ p₁ p₂ := by
  rw [coeff2, coeff2]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  refine intervalIntegral.integral_congr (fun y _ => ?_)
  rw [h x y]

/-- The kernel identity for the difference: `coeff2 symC − coeff2 symM = coeff2 symD`. -/
lemma coeff2_symC_sub_symM_eq_coeff2_symD (P : ℤ[X]) (hd : 1 ≤ P.natDegree) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N l₁ l₂ k₁ k₂ : ℕ) (hN : 1 ≤ N)
    (hC2 : max k₁ k₂ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1 ≤ (logN N).toNat)
    (hna : NonAliasing (-(2 * (uScale ρ (lcL l₁ l₂ k₁ k₂)) : ℤ))
      (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ l₂)) (p₁ p₂ : ℤ) :
    coeff2 (symC ρ P N l₁ l₂ k₁ k₂) p₁ p₂ - coeff2 (symM ρ P N l₁ l₂ k₁ k₂) p₁ p₂
      = coeff2 (symD ρ P N l₁ l₂ k₁ k₂) p₁ p₂ := by
  rw [coeff2_sub_symC_symM ρ hρ hρ1 P N l₁ l₂ k₁ k₂ p₁ p₂]
  exact coeff2_congr (fun x y =>
    symC_sub_symM_eq_symD P hd ρ hρ hρ1 N l₁ l₂ k₁ k₂ hN hC2 hna x y) p₁ p₂

/-- **The bilinear convolution operator is additive in its kernel**, for bounded inputs. -/
lemma bilinOp_sub_kernel {K K' : ℤ → ℤ → ℂ} (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    (hK' : Summable fun p : ℤ × ℤ => ‖K' p.1 p.2‖) {u v : ℤ → ℂ} {Cu Cv : ℝ}
    (hu : ∀ y, ‖u y‖ ≤ Cu) (hv : ∀ y, ‖v y‖ ≤ Cv) (x : ℤ) :
    bilinOp K u v x - bilinOp K' u v x = bilinOp (fun a b => K a b - K' a b) u v x := by
  have hCu : 0 ≤ Cu := le_trans (norm_nonneg _) (hu 0)
  have hCv : 0 ≤ Cv := le_trans (norm_nonneg _) (hv 0)
  have hsum1 : Summable fun p : ℤ × ℤ => K p.1 p.2 * u (x - p.1) * v (x - p.2) := by
    refine Summable.of_norm_bounded (hK.mul_right (Cu * Cv)) (fun p => ?_)
    rw [norm_mul, norm_mul]
    have h1 : ‖K p.1 p.2‖ * ‖u (x - p.1)‖ ≤ ‖K p.1 p.2‖ * Cu :=
      mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _)
    have h2 : ‖K p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K p.1 p.2‖ * Cu * Cv :=
      mul_le_mul h1 (hv _) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hCu)
    calc ‖K p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K p.1 p.2‖ * Cu * Cv := h2
      _ = ‖K p.1 p.2‖ * (Cu * Cv) := by ring
  have hsum2 : Summable fun p : ℤ × ℤ => K' p.1 p.2 * u (x - p.1) * v (x - p.2) := by
    refine Summable.of_norm_bounded (hK'.mul_right (Cu * Cv)) (fun p => ?_)
    rw [norm_mul, norm_mul]
    have h1 : ‖K' p.1 p.2‖ * ‖u (x - p.1)‖ ≤ ‖K' p.1 p.2‖ * Cu :=
      mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _)
    have h2 : ‖K' p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K' p.1 p.2‖ * Cu * Cv :=
      mul_le_mul h1 (hv _) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hCu)
    calc ‖K' p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K' p.1 p.2‖ * Cu * Cv := h2
      _ = ‖K' p.1 p.2‖ * (Cu * Cv) := by ring
  have hKsub : Summable fun p : ℤ × ℤ => ‖K p.1 p.2 - K' p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_sub_le _ _) (hK.add hK')
  rw [Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum hK hu hv x,
    Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum hK' hu hv x,
    Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum hKsub hu hv x,
    ← Summable.tsum_sub hsum1 hsum2]
  exact tsum_congr (fun p => by ring)

/-- The `rpow` product produced by the crude-mult input: `N⁻¹·(N⁻¹)^{1-j₁}·((N^d)⁻¹)^{1-j₂}`
equals the `zpow` `N^{(j₁-2)+d(j₂-1)}`. -/
lemma inv_rpow_prod (N d j₁ j₂ : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ))⁻¹ * ((N : ℝ))⁻¹ ^ ((1 : ℝ) - (j₁ : ℝ))
        * (((N : ℝ) ^ d)⁻¹) ^ ((1 : ℝ) - (j₂ : ℝ))
      = (N : ℝ) ^ (((j₁ : ℤ) - 2) + (d : ℤ) * ((j₂ : ℤ) - 1)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have key1 : ((N : ℝ))⁻¹ ^ ((1 : ℝ) - (j₁ : ℝ))
      = ((N : ℝ))⁻¹ ^ ((((1 : ℤ) - (j₁ : ℤ)) : ℤ) : ℝ) := by
    congr 1
    push_cast
    ring
  have h1 : ((N : ℝ))⁻¹ ^ ((1 : ℝ) - (j₁ : ℝ)) = (N : ℝ) ^ ((j₁ : ℤ) - 1) := by
    rw [key1, Real.rpow_intCast, inv_zpow, ← zpow_neg]
    congr 1
    ring
  have key2 : (((N : ℝ) ^ d)⁻¹) ^ ((1 : ℝ) - (j₂ : ℝ))
      = (((N : ℝ) ^ d)⁻¹) ^ ((((1 : ℤ) - (j₂ : ℤ)) : ℤ) : ℝ) := by
    congr 1
    push_cast
    ring
  have h2 : (((N : ℝ) ^ d)⁻¹) ^ ((1 : ℝ) - (j₂ : ℝ))
      = (N : ℝ) ^ ((d : ℤ) * ((j₂ : ℤ) - 1)) := by
    rw [key2, Real.rpow_intCast, inv_zpow, ← zpow_neg, ← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [h1, h2, ← zpow_neg_one, ← zpow_add₀ hNne, ← zpow_add₀ hNne]
  congr 1
  push_cast
  ring

/-! ## The main theorem -/

theorem lowSmallModelApprox (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (Λ : NNReal) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) (f g : ℤ → ℂ),
      (k₁ = 0 ∨ k₂ = 0) → MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
      Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
      Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)) →
      (max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
          ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) →
      Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂
        ≤ 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTPlan.A6.colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - Work.KMTPlan.A6.lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂)
            * ENNReal.ofReal (((Nat.floor (a n) : ℕ) : ℝ)⁻¹)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨K, D, hK, hD, hder⟩ := symD_deriv_bound P hd ρ hρ hρ1
  obtain ⟨A₁, hA₁, habs⟩ := modelWeight_absorbs_symD P ρ hρ K (40 * D) hK (by linarith)
  obtain ⟨Cna, hCnapos, hna_size⟩ := nonAliasing_of_size ρ hρ hρ1
  obtain ⟨M, hMpos, hcrude⟩ := lowSmall_crude_bound P hd C₀ (⌈Real.logb 2 Cna / ρ⌉₊ + 1) ρ hρ hρ1
  set Nmax : ℕ := splitCut ρ (⌈Real.logb 2 Cna / ρ⌉₊ + 1) with hNmax
  set A : ℝ := max A₁ (max 0 (Real.logb 2 (M * (Nmax : ℝ)) + 1)) with hAdef
  refine ⟨A, ?_, ?_⟩
  · rw [hAdef]; exact le_trans hA₁ (le_max_left _ _)
  · intro Λ a l₁ l₂ k₁ k₂ n f g hk hf hg hΛ ha ha1 hset hreg hC2 hC1
    set N : ℕ := Nat.floor (a n) with hNdef
    have hN1 : 1 ≤ N := by
      have h1 : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha1 n
      exact Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr h1).ne'
    have hbf : Work.KMTAreas.A5.BoundedZ f :=
      Work.KMTAreas.A5.boundedZ_of_memLp (by norm_num : (1 : ℝ≥0∞) < 2) hf
    have hbg : Work.KMTAreas.A5.BoundedZ g :=
      Work.KMTAreas.A5.boundedZ_of_memLp (by norm_num : (1 : ℝ≥0∞) < 2) hg
    have hAN₁ : A₁ ≤ A := by rw [hAdef]; exact le_max_left _ _
    by_cases hna : NonAliasing (-(2 * ((uScale ρ (lcL l₁ l₂ k₁ k₂)) : ℤ)))
        (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ l₂)
    · -- ================= main case =================
      have hsumC : Summable fun p : ℤ × ℤ => ‖coeff2 (symC ρ P N l₁ l₂ k₁ k₂) p.1 p.2‖ :=
        (symC_symM_summable ρ hρ hρ1 P N l₁ l₂ k₁ k₂).1
      have hsumM : Summable fun p : ℤ × ℤ => ‖coeff2 (symM ρ P N l₁ l₂ k₁ k₂) p.1 p.2‖ :=
        (symC_symM_summable ρ hρ hρ1 P N l₁ l₂ k₁ k₂).2
      have hpt : (fun x : ℤ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          = fun x : ℤ => bilinOp (fun u v => coeff2 (symD ρ P N l₁ l₂ k₁ k₂) u v) f g x := by
        funext x
        rw [colSmall_eq_bilinOp_symC ρ hρ hρ1 P C₀ a f g l₁ l₂ k₁ k₂ n x hbf hbg hset,
          lowModel_eq_bilinOp_symM ρ hρ hρ1 P C₀ a f g l₁ l₂ k₁ k₂ n x hbf hbg hset,
          bilinOp_sub_kernel hsumC hsumM hbf.choose_spec hbg.choose_spec x]
        congr 1
        funext u v
        exact coeff2_symC_sub_symM_eq_coeff2_symD P (le_trans (by norm_num) hd) ρ hρ hρ1
          N l₁ l₂ k₁ k₂ hN1 hC2 hna u v
      rw [hpt]
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
      set C0 : ℝ := D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
            + ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
          * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹) with hC0
      set Acr : ℝ := C0 * ((N : ℝ))⁻¹ with hAcr
      have hC0nn : 0 ≤ C0 := by
        rw [hC0]
        exact mul_nonneg (mul_nonneg (le_of_lt hD) (by positivity))
          (by positivity)
      have hAcrnn : 0 ≤ Acr := by
        rw [hAcr]
        exact mul_nonneg hC0nn (inv_nonneg.mpr (le_of_lt hNpos))
      have hr₁ : 0 < ((N : ℝ))⁻¹ := inv_pos.mpr hNpos
      have hr₁1 : ((N : ℝ))⁻¹ ≤ 1 := by
        rw [inv_le_one₀ hNpos]; exact_mod_cast hN1
      have hr₂ : 0 < (((N : ℝ)) ^ P.natDegree)⁻¹ :=
        inv_pos.mpr (by positivity : (0:ℝ) < (N:ℝ) ^ P.natDegree)
      have hr₂1 : (((N : ℝ)) ^ P.natDegree)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ (by positivity)]
        exact one_le_pow₀ (by exact_mod_cast hN1)
      have hder' : ∀ j₁ j₂ : ℕ, j₁ ≤ 2 → j₂ ≤ 2 →
          (∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1,
              ENNReal.ofReal ‖dp j₁ j₂ (symD ρ P N l₁ l₂ k₁ k₂) x y‖)
            ≤ ENNReal.ofReal (Acr * ((N : ℝ))⁻¹ ^ ((1 : ℝ) - (j₁ : ℝ))
                * (((N : ℝ) ^ P.natDegree)⁻¹) ^ ((1 : ℝ) - (j₂ : ℝ))) := by
        intro j₁ j₂ hj₁ hj₂
        refine (hder N l₁ l₂ k₁ k₂ hN1 hC2 j₁ j₂ hj₁ hj₂).trans ?_
        refine ENNReal.ofReal_le_ofReal ?_
        have hprod := inv_rpow_prod N P.natDegree j₁ j₂ hN1
        rw [hAcr, hC0]
        refine le_of_eq ?_
        rw [← hprod]
        ring
      obtain ⟨hsumD, hmassD⟩ := SymToolbox_tsum_coeff2_le (fun x y => symD ρ P N l₁ l₂ k₁ k₂ x y)
        (fun x y => (symD_period_contDiff P ρ N l₁ l₂ k₁ k₂).1 x y)
        (fun x y => (symD_period_contDiff P ρ N l₁ l₂ k₁ k₂).2.1 x y)
        (symD_period_contDiff P ρ N l₁ l₂ k₁ k₂).2.2 hr₁ hr₁1 hr₂ hr₂1 hAcrnn hder'
      have hLP := BilinOpLp (K := fun u v => coeff2 (symD ρ P N l₁ l₂ k₁ k₂) u v)
        (p := 1) (p₁ := 2) (p₂ := 2) (by rw [ENNReal.inv_two_add_inv_two, inv_one]) le_rfl hsumD f g
      have hB : 40 * Acr ≤ modelWeight A ρ l₁ l₂ k₁ k₂ * ((N : ℝ))⁻¹ := by
        rw [hAcr, hC0]
        have hkey : 40 * (D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
              + ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
              * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹))
            ≤ modelWeight A ρ l₁ l₂ k₁ k₂ := by
          have hs : 1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹
              ≤ (2 : ℝ) ^ (2 * (k₁ + P.natDegree * k₂) + 3) := by
            simpa only [div_eq_mul_inv] using one_add_Sval_sq_div_le P N k₁ k₂ hN1
          have hstep : 40 * (D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
                + ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
                * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹))
              ≤ 40 * (D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
                + ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
                * (2 : ℝ) ^ (2 * (k₁ + P.natDegree * k₂) + 3)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact mul_le_mul_of_nonneg_left hs (by positivity)
          refine hstep.trans ?_
          have heq : (40 : ℝ) * (D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
                + ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
                * (2 : ℝ) ^ (2 * (k₁ + P.natDegree * k₂) + 3))
              = 40 * D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
                + ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
                * (2 : ℝ) ^ (2 * (k₁ + P.natDegree * k₂) + 3) := by ring
          rw [heq]
          exact le_trans (habs l₁ l₂ k₁ k₂) (modelWeight_mono_A ρ l₁ l₂ k₁ k₂ hA₁ hAN₁)
        have hfin : 40 * (D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
              + ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
              * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹) * ((N : ℝ))⁻¹)
            ≤ modelWeight A ρ l₁ l₂ k₁ k₂ * ((N : ℝ))⁻¹ := by
          have h1 := mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr (le_of_lt hNpos))
          have heq : (40 : ℝ) * (D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
                + ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
                * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹) * ((N : ℝ))⁻¹)
              = 40 * (D * (2 : ℝ) ^ (K * (2 ^ (ρ * ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ))
                + ((lcL l₁ l₂ k₁ k₂ : ℕ) : ℝ)))
                * (1 + (Work.A7.Sval P k₁ k₂) ^ 2 * ((N : ℝ))⁻¹)) * ((N : ℝ))⁻¹ := by ring
          rw [heq]
          exact h1
        exact hfin
      have hineq : ENNReal.ofReal (∑' q : ℤ × ℤ, ‖coeff2 (symD ρ P N l₁ l₂ k₁ k₂) q.1 q.2‖)
          ≤ ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂) * ENNReal.ofReal ((N : ℝ)⁻¹) := by
        rw [← ENNReal.ofReal_mul
          (modelWeight_nonneg A ρ (le_trans hA₁ (le_max_left _ _)) l₁ l₂ k₁ k₂)]
        exact ENNReal.ofReal_le_ofReal (hmassD.trans hB)
      have hmain2 : ENNReal.ofReal (∑' q : ℤ × ℤ, ‖coeff2 (symD ρ P N l₁ l₂ k₁ k₂) q.1 q.2‖)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂) * ENNReal.ofReal ((N : ℝ)⁻¹)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
        mul_le_mul' (mul_le_mul' hineq le_rfl) le_rfl
      exact hLP.trans hmain2
    · -- ================= crude case =================
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
      have hLB : lcL l₁ l₂ k₁ k₂ ≤ ⌈Real.logb 2 Cna / ρ⌉₊ + 1 :=
        lcL_le_of_not_nonAliasing ρ hρ hρ1 Cna hCnapos
          (fun l K hK => by
            have h := hna_size l l K (by simpa using hK)
            simpa using h) l₁ l₂ k₁ k₂ hna
      have hcut : N ≤ splitCut ρ (⌈Real.logb 2 Cna / ρ⌉₊ + 1) :=
        le_trans hset.2 (splitCut_mono ρ hρ.le hLB)
      have hbound := hcrude Λ a l₁ l₂ k₁ k₂ n f g hΛ ha ha1 hf hg hLB hset hreg hC2
      -- the weight dominates the crude constant
      have hMN : M ≤ modelWeight A ρ l₁ l₂ k₁ k₂ * (N : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hNpos]
        have hMN' : M * (N : ℝ) ≤ modelWeight A ρ l₁ l₂ k₁ k₂ := by
          have h1 : M * (Nmax : ℝ) ≤ (2 : ℝ) ^ A := by
            have hlogb : Real.logb 2 (M * (Nmax : ℝ)) + 1 ≤ A := by
              rw [hAdef]
              exact le_trans (le_max_right _ _) (le_max_right _ _)
            have hNmaxpos : (0 : ℝ) < (Nmax : ℝ) := by
              have hpos : 0 < Nmax := by rw [hNmax, splitCut]; positivity
              exact_mod_cast hpos
            have h3 : (2 : ℝ) ^ (Real.logb 2 (M * (Nmax : ℝ))) = M * (Nmax : ℝ) :=
              Real.rpow_logb (by norm_num) (by norm_num) (mul_pos hMpos hNmaxpos)
            have h2 : M * (Nmax : ℝ) ≤ (2 : ℝ) ^ A := by
              rw [← h3]
              exact Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) (by linarith)
            exact h2
          have h2 : M * (N : ℝ) ≤ M * (Nmax : ℝ) := by
            have hMnn : 0 ≤ M := le_of_lt hMpos
            have hle : (N : ℝ) ≤ (Nmax : ℝ) := by
              have hc := hcut
              rw [← hNmax] at hc
              exact_mod_cast hc
            exact mul_le_mul_of_nonneg_left hle hMnn
          exact le_trans h2 (le_trans h1 (two_pow_le_modelWeight ρ hρ.le l₁ l₂ k₁ k₂
            (le_trans hA₁ (le_max_left _ _))))
        exact hMN'
      have hineq : ENNReal.ofReal M
          ≤ ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂) * ENNReal.ofReal ((N : ℝ)⁻¹) := by
        rw [← ENNReal.ofReal_mul
          (modelWeight_nonneg A ρ (le_trans hA₁ (le_max_left _ _)) l₁ l₂ k₁ k₂)]
        exact ENNReal.ofReal_le_ofReal hMN
      have hcrude2 : ENNReal.ofReal M * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (modelWeight A ρ l₁ l₂ k₁ k₂) * ENNReal.ofReal ((N : ℝ)⁻¹)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
        mul_le_mul' (mul_le_mul' hineq le_rfl) le_rfl
      exact hbound.trans hcrude2

end

end Work.KMTPlan.A6
