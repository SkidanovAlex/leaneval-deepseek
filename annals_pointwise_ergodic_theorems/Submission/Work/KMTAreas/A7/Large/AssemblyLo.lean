/-
# The large-scale assembly with the arithmetic height `l = 0` isolated

This module refines the assembly `Work.KMTAreas.A7.largeLoss_of_bounds` (`Large/Assembly.lean`).

## Why the split is needed

The model tuple `Work.KMTAreas.A7.modelTuple` of `Large/Defs.lean` uses the *exact-height*
Ionescu--Wainger multipliers `Tex ρ l φ` and the exact-height arithmetic kernel
`arithKernelExact`, both built on `iwArithFreqsNew ρ l = iwArithFreqs ρ l \ iwArithFreqs ρ (l-1)`.
Since `iwArithFreqsNew ρ 0 = ∅` (truncated subtraction), the objects at the *arithmetic height*
`l = 0` vanish identically:

* `Tex ρ 0 φ f = 0`, hence `modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ = 0` as soon as `l₁ = 0` or `l₂ = 0`;
* `arithKernelExact ρ P q l₁ l₂ = 0` as soon as `l₁ = 0` or `l₂ = 0`.

But the contract's columns `varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂` at `l₁ = 0` are **not** zero:
the §5 pieces are the *exact-height* projections `Π_{0,≤k} = Π_{≤0,≤k}` (the paper's convention
`(ℚ/ℤ)_0 = Height_ρ^{-1}(1) = {0}`, cf. `Analysis/EndVar/Defs.lean`, `piExact`), so
`Fpiece Pj 0 0 k N f = Π_{0,≤-Log N+k} f` is the non-trivial low-arithmetic-frequency projection.

Consequently the single statement "`V^r(mainPartTuple - modelTuple)` is acceptable for *all*
quadruples `(l₁,l₂,k₁,k₂)`" mixes two different regimes: for `lᵢ ≥ 1` it is the paper's
Proposition `mod-approx` (which is what the §6 analysis proves), while for `l₁ = 0` or `l₂ = 0`
the model vanishes and the statement becomes a direct estimate for the concrete columns (the
`l = 0` case of the paper's §8).  Both are true, but they are proved by disjoint arguments, and a
statement mixing them is what the provers of `ModelApproxCore`/`ModApproxSingle` correctly
rejected.

## The split

`largeLoss_of_hi_lo` therefore takes the two halves separately:

* `hHi` — the model-approximation bound restricted to `1 ≤ l₁ ∧ 1 ≤ l₂` (the paper's
  Proposition `mod-approx`, i.e. the §6 core; for `l ≥ 1` the exact-height objects are the
  intended ones, `iwArithFreqsNew ρ l = diffFreqs ρ l`);
* `hLo` — the same bound restricted to `¬ (1 ≤ l₁ ∧ 1 ≤ l₂)` (the `l = 0` columns);
* `h2` — the bound for the model tuple itself (§8, cf. `ModelLargeBound`);
* `h3` — the bound for the exceptional scales (`ExceptionalBound`, *proved*),

and feeds `largeLoss_of_bounds` with the unrestricted model-approximation bound obtained by the
case split, upgrading `lossWeight c ρ L` to `lossWeight (max c c') ρ L` with `lossWeight_mono`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Assembly

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract
open Work.Analysis.EndVar

/-! ## Elementary complements -/

/-- `lmaxR` is non-negative. -/
theorem lmaxR_nonneg_L (l₁ l₂ k₁ k₂ : ℕ) : 0 ≤ lmaxR l₁ l₂ k₁ k₂ := by
  have hnn : (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
    rw [Work.Analysis.EndVar.lmax]
    exact le_trans (Int.natCast_nonneg l₁)
      (le_trans (le_max_left _ _) (le_max_left _ _))
  rw [lmaxR]
  exact_mod_cast hnn

/-- The loss weight is at least `1` (for `c, ρ ≥ 0`). -/
theorem one_le_lossWeight_L {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 ≤ lossWeight c ρ l₁ l₂ k₁ k₂ := by
  have hL := lmaxR_nonneg_L l₁ l₂ k₁ k₂
  have h1 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ c :=
    Real.one_le_rpow (by linarith) hc
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ c * (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) :=
        mul_le_mul h1 h2 (by norm_num) (le_trans zero_le_one h1)
    _ = lossWeight c ρ l₁ l₂ k₁ k₂ := rfl

/-- Monotonicity of `ENNReal.ofReal (lossWeight ·)` in the loss exponent. -/
theorem ofReal_lossWeight_mono_L {c c' ρ : ℝ} (hρ : 0 ≤ ρ) (hc : c ≤ c') (l₁ l₂ k₁ k₂ : ℕ) :
    ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂)
      ≤ ENNReal.ofReal (lossWeight c' ρ l₁ l₂ k₁ k₂) :=
  ENNReal.ofReal_le_ofReal (lossWeight_mono l₁ l₂ k₁ k₂ hc hρ)

/-- Monotonicity of an `ENNReal`-product in its left factor. -/
theorem mul_le_mul_of_le_left {a a' : ENNReal} (h : a ≤ a') (b : ENNReal) :
    a * b ≤ a' * b :=
  mul_le_mul h le_rfl bot_le bot_le

/-- Monotonicity of an `ENNReal`-product in its right factor. -/
theorem mul_le_mul_of_le_right {b b' : ENNReal} (h : b ≤ b') (a : ENNReal) :
    a * b ≤ a * b' :=
  mul_le_mul le_rfl h bot_le bot_le

/-- `(x : ENNReal) ≤ ((x + y : NNReal) : ENNReal)`. -/
theorem coe_le_coe_add (x y : NNReal) : (x : ENNReal) ≤ ((x + y : NNReal) : ENNReal) :=
  ENNReal.coe_le_coe.mpr (le_add_of_nonneg_right bot_le)

/-- `(y : ENNReal) ≤ ((x + y : NNReal) : ENNReal)`. -/
theorem coe_le_coe_add' (x y : NNReal) : (y : ENNReal) ≤ ((x + y : NNReal) : ENNReal) :=
  ENNReal.coe_le_coe.mpr (le_add_of_nonneg_left bot_le)

/-- The variational norm is subadditive on differences. -/
theorem variationalNorm_sub_le_L {r : ℝ≥0} (hr : 1 ≤ r) (a b : ℕ → ℂ) :
    variationalNorm r (a - b) ≤ variationalNorm r a + variationalNorm r b := by
  have h : a - b = a + (-1 : ℂ) • b := by
    funext n
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  refine (variationalNorm_add_le hr a ((-1 : ℂ) • b)).trans ?_
  rw [variationalNorm_smul hr]
  simp

/-! ## The assembly -/

/-- **The assembly of `VarpLossLarge` from the four estimates**, with the model-approximation
bound split into the two ranges `1 ≤ l₁ ∧ 1 ≤ l₂` and its complement. -/
theorem largeLoss_of_hi_lo (P : Polynomial ℤ) (p₁ p₂ : ENNReal)
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
                    - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
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
  refine largeLoss_of_bounds P p₁ p₂ hdeg hsum ?_ h2 h3
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
