import Mathlib
import Submission.Work.KMTAreas.A7Hi.VariationalConvLe
import Submission.Work.KMTPlan.A6Clean.PacketProfile
import Submission.Work.KMTPlan.A6Clean.WinConvRZero

namespace Work.KMTPlan.A6Clean

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

noncomputable section

/-! ## The loss weight -/

/-- `lmaxR l₁ l₂ k₁ k₂` is the cast of `lcL l₁ l₂ k₁ k₂`. -/
theorem lmaxR_eq_lcL (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ = (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ : ℝ) := by
  rw [Work.KMTAreas.A7.lmaxR, Work.Analysis.EndVar.lmax, Work.KMTPlan.A6.lcL]
  norm_num

/-- The `lmaxR` factor of the loss weight is nonnegative. -/
theorem lmaxR_nonnegc (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR_eq_lcL]; positivity

/-- The loss weight is nonnegative. -/
theorem lossWeight_nonnegc (c ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    0 ≤ Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂ := by
  rw [Work.KMTAreas.A7.lossWeight]
  exact mul_nonneg (Real.rpow_nonneg (by linarith [lmaxR_nonnegc l₁ l₂ k₁ k₂]) _)
    (Real.rpow_nonneg (by norm_num) _)

/-- The loss weight is at least `1` for `c ≥ 0`, `ρ ≥ 0`. -/
theorem one_le_lossWeightc (c ρ : ℝ) (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 ≤ Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂ := by
  rw [Work.KMTAreas.A7.lossWeight]
  have hL := lmaxR_nonnegc l₁ l₂ k₁ k₂
  have h1 : (1 : ℝ) ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ c :=
    Real.one_le_rpow (by linarith) hc
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (c * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ _ := mul_le_mul h1 h2 (by norm_num) (by positivity)

/-- The loss weight is multiplicative in its exponent parameter. -/
theorem lossWeight_mulc (a b ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lossWeight a ρ l₁ l₂ k₁ k₂ * Work.KMTAreas.A7.lossWeight b ρ l₁ l₂ k₁ k₂
      = Work.KMTAreas.A7.lossWeight (a + b) ρ l₁ l₂ k₁ k₂ := by
  rw [Work.KMTAreas.A7.lossWeight, Work.KMTAreas.A7.lossWeight, Work.KMTAreas.A7.lossWeight]
  have h1 : (0 : ℝ) < 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    linarith [lmaxR_nonnegc l₁ l₂ k₁ k₂]
  have h2 : a * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
      + b * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
      = (a + b) * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by ring
  rw [mul_mul_mul_comm, ← Real.rpow_add h1, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), h2]

/-- The loss weight is monotone in its exponent parameter (for `c ≥ 0`, `ρ ≥ 0`). -/
theorem lossWeight_mono (c c' ρ : ℝ) (h : c ≤ c') (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂
      ≤ Work.KMTAreas.A7.lossWeight c' ρ l₁ l₂ k₁ k₂ := by
  rw [Work.KMTAreas.A7.lossWeight, Work.KMTAreas.A7.lossWeight]
  have hL := lmaxR_nonnegc l₁ l₂ k₁ k₂
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · exact Real.rpow_le_rpow_of_exponent_le (by linarith) h
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hρ) hL)

/-- **The sixth power of the loss weight.**  `lossWeight (6C) = (lossWeight C)^6`. -/
theorem lossWeight_pow_six (C ρ : ℝ) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lossWeight (6 * C) ρ l₁ l₂ k₁ k₂
      = (Work.KMTAreas.A7.lossWeight C ρ l₁ l₂ k₁ k₂) ^ 6 := by
  have h1 : (0 : ℝ) < 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    linarith [lmaxR_nonnegc l₁ l₂ k₁ k₂]
  have e1 : ((1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ C) ^ (6 : ℕ)
      = (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ (6 * C) := by
    rw [← Real.rpow_natCast ((1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ C) 6,
      ← Real.rpow_mul (le_of_lt h1) C ((6 : ℕ) : ℝ),
      show C * ((6 : ℕ) : ℝ) = 6 * C from by ring]
  have e2 : ((2 : ℝ) ^ (C * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)) ^ (6 : ℕ)
      = (2 : ℝ) ^ (6 * C * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (C * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)) 6,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
        (C * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ((6 : ℕ) : ℝ)]
    congr 1
    ring
  rw [Work.KMTAreas.A7.lossWeight, Work.KMTAreas.A7.lossWeight, mul_pow, ← e1, ← e2]

/-! ## Elementary arithmetic-character bounds -/

/-- The variational product rule with constant `1` (local copy of
`Work.KMTAreas.A7.variationalNorm_mul_le_one`, which lives in the clash-prone
`A7/LoMixedAux.lean`). -/
theorem variationalNorm_mul_le_one_local (r : NNReal) (hr : 1 ≤ r) (u v : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => u n * v n) ≤
      PointwiseErgodicTheorems.variationalNorm r u *
        PointwiseErgodicTheorems.variationalNorm r v := by
  have hvar := Work.KMTAreas.A7.varPart_mul_le hr u v
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r (fun n => u n * v n),
      Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r u,
      Submission.PointwiseErgodicTheorems.variationalNorm_eq_add r v]
  calc (⨆ n, ‖u n * v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r (fun n => u n * v n)
      ≤ ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
          + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
              + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v) :=
        add_le_add (Work.KMTAreas.A7.iSup_enorm_mul_le u v) hvar
    _ ≤ ((⨆ n, ‖u n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r u)
          * ((⨆ n, ‖v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r v) := by
        calc ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
              + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
                  + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v)
            ≤ ((⨆ n, ‖u n‖ₑ) * (⨆ n, ‖v n‖ₑ))
              + ((⨆ n, ‖v n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r u
                  + (⨆ n, ‖u n‖ₑ) * Submission.PointwiseErgodicTheorems.varPart r v)
              + (Submission.PointwiseErgodicTheorems.varPart r u
                  * Submission.PointwiseErgodicTheorems.varPart r v) := le_add_right le_rfl
          _ = ((⨆ n, ‖u n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r u)
                * ((⨆ n, ‖v n‖ₑ) + Submission.PointwiseErgodicTheorems.varPart r v) := by ring

/-- The arithmetic character of a finite set of frequencies is bounded by its cardinality. -/
theorem norm_arithCharSet_le_card (A : Finset Work.Analysis.IonescuWainger.Circle) (y : ℤ) :
    ‖Work.KMTAreas.A7.arithCharSet A y‖ ≤ (A.card : ℝ) := by
  rw [Work.KMTAreas.A7.arithCharSet]
  calc ‖∑ α ∈ A, fourier (T := 1) y α‖ ≤ ∑ α ∈ A, ‖fourier (T := 1) y α‖ := norm_sum_le _ _
    _ = ∑ _α ∈ A, (1 : ℝ) :=
        Finset.sum_congr rfl (fun α _ => Work.KMTAreas.A7.norm_fourier_applyR y α)
    _ = (A.card : ℝ) := by simp

/-- The `cw m`-convolution of an `ℓ¹`-kernel with a bounded character is summable, with the
`ℓ¹`-mass bounded by `#A` times the mass of `cw m`. -/
theorem summable_arithCharSet_mul_cw {A : Finset Work.Analysis.IonescuWainger.Circle}
    {m : ℝ → ℂ} {n₀ : ℤ} (hm : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖)) :
    Summable (fun j : ℤ =>
        ‖Work.KMTAreas.A7.arithCharSet A (n₀ - j) * Work.KMTAreas.A7.cw m j‖) ∧
      ∑' j : ℤ, ‖Work.KMTAreas.A7.arithCharSet A (n₀ - j) * Work.KMTAreas.A7.cw m j‖
        ≤ (A.card : ℝ) * ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ := by
  have hle : ∀ j : ℤ, ‖Work.KMTAreas.A7.arithCharSet A (n₀ - j) * Work.KMTAreas.A7.cw m j‖
      ≤ (A.card : ℝ) * ‖Work.KMTAreas.A7.cw m j‖ := by
    intro j
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_arithCharSet_le_card A (n₀ - j))
      (norm_nonneg _)
  have hsum : Summable (fun j : ℤ =>
      ‖Work.KMTAreas.A7.arithCharSet A (n₀ - j) * Work.KMTAreas.A7.cw m j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hle (hm.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' j : ℤ, ‖Work.KMTAreas.A7.arithCharSet A (n₀ - j) * Work.KMTAreas.A7.cw m j‖
      ≤ ∑' j : ℤ, (A.card : ℝ) * ‖Work.KMTAreas.A7.cw m j‖ :=
        Summable.tsum_le_tsum hle hsum (hm.mul_left _)
    _ = (A.card : ℝ) * ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ := tsum_mul_left

/-! ## The fibre-Young bound for the cumulative-height fibre -/

/-- **The `ℓ²` fibre-Young bound for the cumulative-height fibre.**  For an arbitrary family
`u : ℕ → ℤ → ℂ` and an arbitrary modulus `q ≥ 1`, the `ℓ²(ℤ; V^r)`-norm of the residue average of
the variational norms of the fibres `fiberOpSet A m n₀ (u ·)` is bounded by the `ℓ¹`-mass of the
kernel `j ↦ arithCharSet A (n₀ - j) · cw m j` times the `ℓ²(ℤ; V^r)`-norm of `u` — uniformly in
the residue `n₀`.

The proof is `Work.KMTAreas.A7Hi.VariationalConvLe` (the Young inequality for the variational norm,
with the `ℓ¹`-kernel convolution) followed by the residue aggregation
`Work.KMTAreas.A7.eLpNorm_residueLp_le`, which is free because the bound is uniform in `n₀`. -/
theorem eLpNorm_residueLp_fiberOpSet_le (r : NNReal) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset Work.Analysis.IonescuWainger.Circle) (m : ℝ → ℂ) (q : ℕ)
      (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖)) (u : ℕ → ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q
          (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.fiberOpSet A m n₀ (u n) y)) x)
        2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal (C * (A.card : ℝ) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖))
          * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => u n x)) 2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  obtain ⟨C, hCpos, hC⟩ := Work.KMTAreas.A7Hi.VariationalConvLe 2 (by norm_num) r hr
  refine ⟨C, hCpos, fun A m q hmsum u => ?_⟩
  have h2 : ENNReal.ofReal 2 = 2 := ENNReal.ofReal_ofNat 2
  have hper : ∀ n₀ : ℕ, MeasureTheory.eLpNorm (fun y : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (Work.KMTAreas.A7.arithCharSet A ((n₀ : ℤ) - j)
            * Work.KMTAreas.A7.cw m j) * u n (y - j)))
        (ENNReal.ofReal 2) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal (C * (A.card : ℝ) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖))
        * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => u n x)) (ENNReal.ofReal 2)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
    intro n₀
    have hmass₀ := summable_arithCharSet_mul_cw (A := A) (n₀ := (n₀ : ℤ)) hmsum
    have h := hC (fun j : ℤ => Work.KMTAreas.A7.arithCharSet A ((n₀ : ℤ) - j)
        * Work.KMTAreas.A7.cw m j) hmass₀.1 u
    refine h.trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    calc C * ∑' j : ℤ, ‖Work.KMTAreas.A7.arithCharSet A ((n₀ : ℤ) - j)
            * Work.KMTAreas.A7.cw m j‖
        ≤ C * ((A.card : ℝ) * ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖) :=
          mul_le_mul_of_nonneg_left hmass₀.2 (le_of_lt hCpos)
      _ = C * (A.card : ℝ) * ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ := by ring
  simpa only [Work.KMTAreas.A7.fiberOpSet, h2] using
    (Work.KMTAreas.A7.eLpNorm_residueLp_le (p := 2) (by norm_num) (q := q)
      (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' j : ℤ, (Work.KMTAreas.A7.arithCharSet A ((n₀ : ℤ) - j)
          * Work.KMTAreas.A7.cw m j) * u n (y - j)))
      (ENNReal.ofReal (C * (A.card : ℝ) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖))
        * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => u n x)) (ENNReal.ofReal 2)
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ))
      (fun n₀ _ => hper n₀))

/-- **The `P`-twisted (`g`-side) analogue** of `eLpNorm_residueLp_fiberOpSet_le`. -/
theorem eLpNorm_residueLp_fiberOpPSet_le (r : NNReal) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Polynomial ℤ)
      (A : Finset Work.Analysis.IonescuWainger.Circle) (m : ℝ → ℂ) (q : ℕ)
      (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖)) (u : ℕ → ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q
          (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.fiberOpPSet P A m n₀ (u n) y)) x)
        2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal (C * (A.card : ℝ) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖))
          * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => u n x)) 2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  obtain ⟨C, hCpos, hC⟩ := Work.KMTAreas.A7Hi.VariationalConvLe 2 (by norm_num) r hr
  refine ⟨C, hCpos, fun P A m q hmsum u => ?_⟩
  have h2 : ENNReal.ofReal 2 = 2 := ENNReal.ofReal_ofNat 2
  have hper : ∀ n₀ : ℕ, MeasureTheory.eLpNorm (fun y : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (Work.KMTAreas.A7.arithCharSet A (P.eval (n₀ : ℤ) - j)
            * Work.KMTAreas.A7.cw m j) * u n (y - j)))
        (ENNReal.ofReal 2) (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal (C * (A.card : ℝ) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖))
        * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => u n x)) (ENNReal.ofReal 2)
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
    intro n₀
    have hmass₀ := summable_arithCharSet_mul_cw (A := A) (n₀ := P.eval (n₀ : ℤ)) hmsum
    have h := hC (fun j : ℤ => Work.KMTAreas.A7.arithCharSet A (P.eval (n₀ : ℤ) - j)
        * Work.KMTAreas.A7.cw m j) hmass₀.1 u
    refine h.trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    calc C * ∑' j : ℤ, ‖Work.KMTAreas.A7.arithCharSet A (P.eval (n₀ : ℤ) - j)
            * Work.KMTAreas.A7.cw m j‖
        ≤ C * ((A.card : ℝ) * ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖) :=
          mul_le_mul_of_nonneg_left hmass₀.2 (le_of_lt hCpos)
      _ = C * (A.card : ℝ) * ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ := by ring
  simpa only [Work.KMTAreas.A7.fiberOpPSet, h2] using
    (Work.KMTAreas.A7.eLpNorm_residueLp_le (p := 2) (by norm_num) (q := q)
      (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' j : ℤ, (Work.KMTAreas.A7.arithCharSet A (P.eval (n₀ : ℤ) - j)
          * Work.KMTAreas.A7.cw m j) * u n (y - j)))
      (ENNReal.ofReal (C * (A.card : ℝ) * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖))
        * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => u n x)) (ENNReal.ofReal 2)
              (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ))
      (fun n₀ _ => hper n₀))

/-! ## The pointwise fibre decomposition of the twisted bilinear multiplier -/

/-- **The variational norm of the twisted bilinear multiplier is bounded by the residue average of
the products of the variational norms of the two fibres.**  This is the composition of the fibre
identity `Work.KMTAreas.A7.Btwist_eq_fiberSum` (in the `∀ m` form), the subadditivity of the
variational norm over the finite residue sum
(`Work.KMTAreas.A7.variationalNorm_finset_sum_le`), its homogeneity
(`Submission.PointwiseErgodicTheorems.variationalNorm_smul`) and the product rule
(`Work.KMTAreas.A7.variationalNorm_mul_le_one`, constant `1`). -/
theorem variationalNorm_Btwist_fiber_le (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (u v : ℕ → ℤ → ℂ) (r : NNReal) (hr : 1 ≤ r) (x : ℤ)
    (h₁ : ∀ (m : ℕ) (n₀ : ℤ), Summable (fun j : ℤ =>
      Work.KMTAreas.A7.arithChar ρ l₁ (n₀ - j) * Work.KMTAreas.A7.cw m₁ j * u m (x - j)))
    (h₂ : ∀ (m : ℕ) (n₀ : ℤ), Summable (fun j : ℤ =>
      Work.KMTAreas.A7.arithChar ρ l₂ (P.eval n₀ - j) * Work.KMTAreas.A7.cw m₂ j * v m (x - j))) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ (u m) (v m) x) ≤
      ((Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ENNReal))⁻¹ *
        ∑ n₀ ∈ Finset.range (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
          PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ =>
            Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
              m₁ n₀ (u m) x) *
          PointwiseErgodicTheorems.variationalNorm r (fun m : ℕ =>
            Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
              m₂ n₀ (v m) x) := by
  have hfam : (fun m : ℕ => Work.KMTAreas.A7.Btwist ρ P l₁ l₂ m₁ m₂ (u m) (v m) x)
      = ((Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℂ))⁻¹ •
        (fun m : ℕ => ∑ n₀ ∈ Finset.range (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
          Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
              m₁ n₀ (u m) x
            * Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
                m₂ n₀ (v m) x) := by
    funext m
    rw [Pi.smul_apply, smul_eq_mul]
    exact Work.KMTAreas.A7.Btwist_eq_fiberSum ρ P l₁ l₂ m₁ m₂ (u m) (v m) x (h₁ m) (h₂ m)
  rw [hfam, Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := r) hr]
  have hnorm : ‖((Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℂ))⁻¹‖ₑ
      = ((Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ENNReal))⁻¹ := by
    rw [enorm_inv (by
      exact_mod_cast (Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂)).ne'),
      ← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
  rw [hnorm]
  refine mul_le_mul_of_nonneg_left ?_ bot_le
  exact (Work.KMTAreas.A7.variationalNorm_finset_sum_le hr _ _).trans
    (Finset.sum_le_sum fun n₀ _ => variationalNorm_mul_le_one_local r hr _ _)

/-- The fibre of the zero sequence vanishes. -/
theorem fiberOpSet_zero_right (A : Finset Work.Analysis.IonescuWainger.Circle) (m : ℝ → ℂ)
    (n₀ : ℤ) (x : ℤ) :
    Work.KMTAreas.A7.fiberOpSet A m n₀ (0 : ℤ → ℂ) x = 0 := by
  simp only [Work.KMTAreas.A7.fiberOpSet]
  simp

/-- The exact-height fibre of the zero sequence vanishes. -/
theorem fiberOp_zero_right (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ) (x : ℤ) :
    Work.KMTAreas.A7.fiberOp ρ l m n₀ (0 : ℤ → ℂ) x = 0 := by
  simp only [Work.KMTAreas.A7.fiberOp]
  simp

/-- The `P`-twisted fibre of the zero sequence vanishes. -/
theorem fiberOpPSet_zero_right (P : Polynomial ℤ) (A : Finset Work.Analysis.IonescuWainger.Circle)
    (m : ℝ → ℂ) (n₀ : ℤ) (x : ℤ) :
    Work.KMTAreas.A7.fiberOpPSet P A m n₀ (0 : ℤ → ℂ) x = 0 := by
  simp only [Work.KMTAreas.A7.fiberOpPSet]
  simp

/-- The `P`-twisted exact-height fibre of the zero sequence vanishes. -/
theorem fiberOpP_zero_right (ρ : ℝ) (P : Polynomial ℤ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ) (x : ℤ) :
    Work.KMTAreas.A7.fiberOpP ρ P l m n₀ (0 : ℤ → ℂ) x = 0 := by
  simp only [Work.KMTAreas.A7.fiberOpP]
  simp

/-! ## The cumulative-height fibre off the exact-height band -/

/-- `diffFreqs ρ l ⊆ iwArithFreqs ρ l`. -/
theorem diffFreqs_subset_iwArithFreqs (ρ : ℝ) (l : ℕ) :
    Work.KMTAreas.A7.diffFreqs ρ l ⊆ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
  rw [Work.KMTAreas.A7.diffFreqs]
  split_ifs with h
  · rw [h]
  · exact Finset.sdiff_subset

/-- **The cumulative-height fibre coincides with the exact-height fibre** when the input is
band-limited to the exact-height arcs and the arithmetic frequencies are separated: the window
pieces at the non-exact-height frequencies vanish
(`Work.KMTPlan.A6Clean.winConvR_eq_zero_of_not_exact`). -/
theorem fiberOpSet_cumulative_eq_of_exact_band (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ)
    (m : ℝ → ℂ) (δW γ : ℝ) (hδW : 0 < δW) (hγ : 0 < γ)
    (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖))
    (hmsupp : ∀ θ : ℝ, 2 * δW < |θ| → m θ = 0)
    (h : ℤ → ℂ) (hh : Memℓp h 2)
    (hhE : Work.BourgainPlan.IonescuWainger.HasFreqSupport h hh
      (⋃ β ∈ Work.KMTAreas.A7.diffFreqs ρ l, Work.BourgainPlan.IonescuWainger.arcSet β γ))
    (hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
      ∀ β ∈ Work.KMTAreas.A7.diffFreqs ρ l, α ≠ β → 2 * δW + γ < ‖α - β‖)
    (n₀ : ℤ) (x : ℤ) :
    Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) m n₀ h x
      = Work.KMTAreas.A7.fiberOpSet (Work.KMTAreas.A7.diffFreqs ρ l) m n₀ h x := by
  have hsumm : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j * h (x - j)) :=
    Work.KMTAreas.A7.summable_cw_mul_of_memℓp hmsum hh x
  rw [fiberOpSet_eq_windowPieceR (Work.Analysis.IonescuWainger.iwArithFreqs ρ l) m n₀ h x hsumm,
    fiberOpSet_eq_windowPieceR (Work.KMTAreas.A7.diffFreqs ρ l) m n₀ h x hsumm]
  refine (Finset.sum_subset (diffFreqs_subset_iwArithFreqs ρ l) (fun α hαA hαd => ?_)).symm
  have hz : winPieceR m h α x = 0 := by
    simp only [winPieceR]
    exact congrFun (winConvR_eq_zero_of_not_exact ρ hρ hρ1 l m δW γ hδW hγ hm hmsum hmsupp h hh
      hhE hsep α hαA hαd) x
  rw [hz, mul_zero]


end

end Work.KMTPlan.A6Clean
