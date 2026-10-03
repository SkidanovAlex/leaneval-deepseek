/-
# The assembly of `VarpLossLarge` with the *repaired* §6 model `modelTupleRep`

This module is a verbatim copy of the two assemblies

* `Work.KMTAreas.A7.largeLoss_of_bounds` (`Large/Assembly.lean`),
* `Work.KMTAreas.A7.largeLoss_of_hi_lo` (`Large/AssemblyLo.lean`),

with the model tuple `modelTuple` replaced by the repaired `modelTupleRep` of
`Large/Defs.lean` (whose symbol `m_*` has the band `uRep` that separates the exact-height
arithmetic fibres, and whose guard contains the band condition `bandCond`).  Names of the copied
theorems carry the suffix `_rep`.

Motivation: with the workspace's normalisation `u = uScale ρ L = ⌊2^{2ρL}⌋` (the paper's `C₂`
pinned to `1`) the functional calculus `bn-ident` fails whenever `max (l₁,l₂)` is large compared
with `L` (cross-fibre terms of size `O(1)`, no `N^{-1}` gain), which is why
`Work.KMTAreas.A7.HiMassBound` and the single-scale content of `ModelApproxHi` are FALSE as
stated; see `NOTES_A7_HiMassBoundHolds_VERDICT.md` §3 and
`NOTES_A7_level0_model_and_LargeLoss.md`.

The hypotheses are exactly those of `largeLoss_of_hi_lo`, with `modelTuple` replaced by
`modelTupleRep`; the exceptional term `exceptionalPart` is model-independent, so
`Work.KMTAreas.A7.ExceptionalBound` (proved) is still the fourth input.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.AssemblyLo
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract
open Work.Analysis.EndVar

/-- **The assembly of `VarpLossLarge`.**  The three estimates of §6--§8 (`ModelApprox`,
`ModelLargeBound`, `ExceptionalBound`) imply the large-scale estimate `VarpLossLarge P p₁ p₂`. -/
theorem largeLoss_of_bounds_rep (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (h1 : ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
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
                  modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
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
    variationalNorm r (fun n : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFm
  set Fa : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFa
  set Fe : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFe
  set X : ENNReal := eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count with hX
  -- abbreviations for the four scalar families and the scalar factors
  set Fc : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFc
  set Fm : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFm
  set Fa : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFa
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
            (fun n : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + (PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            + PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) := by
    intro x
    have heq : (fun n : ℕ => colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = (fun n : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            + ((mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) := by
      funext n
      have hpt := congrFun (congrFun (colTuple_eq_sum_rep ρ P C₀ a f g l₁ l₂ k₁ k₂) n) x
      simpa only [Pi.add_apply, Pi.sub_apply] using hpt
    rw [heq]
    calc PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            + ((mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              (mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
              + exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) :=
          variationalNorm_add_le hr1 _ _
      _ ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          + (PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
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

/-- **The assembly of `VarpLossLarge` from the four estimates**, with the model-approximation
bound split into the two ranges `1 ≤ l₁ ∧ 1 ≤ l₂` and its complement. -/
theorem largeLoss_of_hi_lo_rep (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
    (hdeg : 2 ≤ P.natDegree) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hHi : ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            1 ≤ l₁ → 1 ≤ l₂ →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
    (hLo : ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            ¬ (1 ≤ l₁ ∧ 1 ≤ l₂) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
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
                  modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
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
  refine largeLoss_of_bounds_rep P p₁ p₂ hdeg hsum ?_ h2 h3
  -- the unrestricted model-approximation bound, by the case split on `l₁, l₂ ≥ 1`
  intro C₀ r hC₀ hr
  obtain ⟨cA, hcA, ρA, hρA, hA⟩ := hHi C₀ r hC₀ hr
  obtain ⟨cB, hcB, ρB, hρB, hB⟩ := hLo C₀ r hC₀ hr
  refine ⟨max cA cB, le_trans hcA (le_max_left _ _), min ρA ρB, lt_min hρA hρB, ?_⟩
  intro ρ hρ hρle
  have hρA' : ρ ≤ ρA := le_trans hρle (min_le_left _ _)
  have hρB' : ρ ≤ ρB := le_trans hρle (min_le_right _ _)
  obtain ⟨KA, hA'⟩ := hA ρ hρ hρA'
  obtain ⟨KB, hB'⟩ := hB ρ hρ hρB'
  refine ⟨fun Λ => KA Λ + KB Λ, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  have hρnn : (0 : ℝ) ≤ ρ := le_of_lt hρ
  by_cases hhi : 1 ≤ l₁ ∧ 1 ≤ l₂
  · refine (hA' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hhi.1 hhi.2).trans ?_
    have hwA : ENNReal.ofReal (lossWeight cA ρ l₁ l₂ k₁ k₂)
        ≤ ENNReal.ofReal (lossWeight (max cA cB) ρ l₁ l₂ k₁ k₂) :=
      ofReal_lossWeight_mono_L (c := cA) (c' := max cA cB) hρnn (le_max_left _ _) l₁ l₂ k₁ k₂
    have hKA : (KA Λ : ENNReal) ≤ ((KA Λ + KB Λ : NNReal) : ENNReal) :=
      coe_le_coe_add (KA Λ) (KB Λ)
    calc (KA Λ : ENNReal) * ENNReal.ofReal (lossWeight cA ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
        ≤ (KA Λ : ENNReal) * ENNReal.ofReal (lossWeight (max cA cB) ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
          mul_le_mul_of_le_left (mul_le_mul_of_le_left
            (mul_le_mul_of_le_right hwA (KA Λ : ENNReal))
            (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count))
            (MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
      _ ≤ (((KA Λ + KB Λ : NNReal)) : ENNReal)
          * ENNReal.ofReal (lossWeight (max cA cB) ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
          mul_le_mul_of_le_left (mul_le_mul_of_le_left
            (mul_le_mul_of_le_left hKA
              (ENNReal.ofReal (lossWeight (max cA cB) ρ l₁ l₂ k₁ k₂)))
            (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count))
            (MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
  · refine (hB' a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hhi).trans ?_
    have hwB : ENNReal.ofReal (lossWeight cB ρ l₁ l₂ k₁ k₂)
        ≤ ENNReal.ofReal (lossWeight (max cA cB) ρ l₁ l₂ k₁ k₂) :=
      ofReal_lossWeight_mono_L (c := cB) (c' := max cA cB) hρnn (le_max_right _ _) l₁ l₂ k₁ k₂
    have hKB : (KB Λ : ENNReal) ≤ ((KA Λ + KB Λ : NNReal) : ENNReal) :=
      coe_le_coe_add' (KA Λ) (KB Λ)
    calc (KB Λ : ENNReal) * ENNReal.ofReal (lossWeight cB ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
        ≤ (KB Λ : ENNReal) * ENNReal.ofReal (lossWeight (max cA cB) ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
          mul_le_mul_of_le_left (mul_le_mul_of_le_left
            (mul_le_mul_of_le_right hwB (KB Λ : ENNReal))
            (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count))
            (MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
      _ ≤ (((KA Λ + KB Λ : NNReal)) : ENNReal)
          * ENNReal.ofReal (lossWeight (max cA cB) ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
          mul_le_mul_of_le_left (mul_le_mul_of_le_left
            (mul_le_mul_of_le_left hKB
              (ENNReal.ofReal (lossWeight (max cA cB) ρ l₁ l₂ k₁ k₂)))
            (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count))
            (MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)

end

end Work.KMTAreas.A7
