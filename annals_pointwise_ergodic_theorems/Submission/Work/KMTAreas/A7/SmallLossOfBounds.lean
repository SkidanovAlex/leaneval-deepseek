import Mathlib
import Submission.Work.KMTAreas.A7.SmallDefs
import Submission.Work.KMTAreas.A7.Large.Assembly
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar

/-- **The assembly of `VarpLossSmall` from the three estimates of the small-scale regime.**
The small-scale tuple `smallColTuple` (the §5 columns clamped by `N ≤ splitCut ρ L`) splits
pointwise (`smallColTuple_eq_sum`) into the model tuple `smallModelTuple`, the model-approximation
error `smallMainPart - smallModelTuple` and the exceptional part `smallExcPart`; the three
hypotheses bound the `ℓ^p(ℤ;V^r)` norms of those three families, and the three weights
(`lossWeight c ρ L` for the first two, none for the third) combine into one exponent
`A = max c₁ c₂ + 1` with the help of `lossWeight_le` and `lossWeight_mono`.

This is the small-scale mirror image of `Work.KMTAreas.A7.largeLoss_of_bounds`
(`A7/Large/Assembly.lean`), which is proved; the only differences are the inequality defining the
scale cut (`N ≤ splitCut` here versus `splitCut < N` there) and the restricted range
`ρ ≤ 1/(8 C₀)` of the exceptional hypothesis (`h3`), which is what makes the exceptional small
scales bounded (`Work.KMTAreas.A7.SmallExcSupport`).  SUGGESTED ROUTE: copy the proof of
`largeLoss_of_bounds`, replacing `colTuple` by `smallColTuple`, `modelTuple` by `smallModelTuple`,
`mainPartTuple` by `smallMainPart`, `exceptionalPart` by `smallExcPart`, and adding the factor
`1 / (8 * C₀)` to the final `ρ₀`. -/
theorem SmallLossOfBounds (P : ℤ[X]) (p₁ p₂ : ENNReal) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (h1 : ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
    (h2 : ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
    (h3 : ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r → ∃ K : NNReal → NNReal,
      ∀ (ρ : ℝ) (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        0 < ρ → ρ ≤ 1 / (8 * (C₀ : ℝ)) → 1 < Λ →
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :
    Work.KMTAreas.A7.VarpLossSmall P p₁ p₂ := by
  classical
  intro C₀ r hC₀ hr
  obtain ⟨c₁, hc₁, s₁, hs₁, hA⟩ := h1 C₀ r hC₀ hr
  obtain ⟨c₂, hc₂, s₂, hs₂, hB⟩ := h2 C₀ r hC₀ hr
  obtain ⟨K₃, hC⟩ := h3 C₀ r hC₀ hr
  have hc : (0:ℝ) ≤ max c₁ c₂ := le_trans hc₁ (le_max_left _ _)
  have hC₀pos : (0:ℝ) < (C₀ : ℝ) := by
    have h1 : (1:ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
    linarith
  have hρe : 0 < 1 / (8 * (C₀ : ℝ)) := by positivity
  refine ⟨max c₁ c₂ + 1, by positivity, min (min s₁ s₂) (1 / (8 * (C₀ : ℝ))),
    lt_min (lt_min hs₁ hs₂) hρe, ?_⟩
  intro ρ hρ hρle
  have hρs₁ : ρ ≤ s₁ := le_trans hρle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρs₂ : ρ ≤ s₂ := le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρexc : ρ ≤ 1 / (8 * (C₀ : ℝ)) := le_trans hρle (min_le_right _ _)
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
  have e3 := hC ρ a Λ l₁ l₂ k₁ k₂ f g hρ hρexc hΛ ha ha1
  -- abbreviations for the four scalar families and the scalar factors
  set Fc : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => smallColTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFc
  set Fm : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFm
  set Fa : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFa
  set Fe : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFe
  set Wm : ENNReal := ENNReal.ofReal (lossWeight (max c₁ c₂) ρ l₁ l₂ k₁ k₂) with hWm
  set W : ENNReal := ENNReal.ofReal
    (((2:ℝ) ^ ((max c₁ c₂ + 1) * ρ * lmaxR l₁ l₂ k₁ k₂))) with hW
  set Cf : ENNReal := (CW : ENNReal) with hCf
  set X : ENNReal := MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
    * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hX
  -- the pointwise splitting of the column family
  have hsplit0 : ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => smallColTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + (PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) := by
    intro x
    have heq : (fun n : ℕ => smallColTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = (fun n : ℕ => smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            + ((smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) := by
      funext n
      have hpt := congrFun (congrFun (smallColTuple_eq_sum ρ P C₀ a f g l₁ l₂ k₁ k₂) n) x
      simpa only [Pi.add_apply, Pi.sub_apply] using hpt
    rw [heq]
    calc PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            + ((smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              (smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) :=
          variationalNorm_add_le hr1 _ _
      _ ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + (PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => smallExcPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) := by
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
  have hgoal1 : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if Nat.floor (a n) ≤ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) then
          varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x else 0)) = Fc := by
    rw [hFc]
    funext x
    congr 1
  rw [hgoal1]
  refine le_trans hmain'' (le_of_eq ?_)
  rw [hW, hX, lmaxR]
  ring

end Work.KMTAreas.A7

