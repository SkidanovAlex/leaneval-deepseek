import Mathlib
import Submission.Work.KMTPlan.A6.PieceBoundedH.HeightZeroAux
import Submission.Work.PieceBoundedH.heightZeroZeroSmallRho
import Submission.Work.KMTPlan.A6.BoundedHMain.heightZeroLeft
import Submission.Work.KMTPlan.A6.BoundedHMain.heightZeroRight
import Submission.Port.Aesm

namespace Work.KMTPlan.A6.PieceBoundedH

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-!
# The height-zero bound for the concrete §5 columns (`Work.KMTPlan.A6.MainPieceBoundedH`)

This module proves `heightZeroBound`, the range `l₁ = 0 ∨ l₂ = 0` (together with the low case
`k₁ = 0 ∨ k₂ = 0`) of the bounded-height `(2,2,1)` estimate `Work.KMTPlan.A6.MainPieceBoundedH`
for the concrete columns `Work.KMTAreas.A7.mainPartTuple` of the §5 decomposition.

## The strategy

The range splits into

* `heightZeroZeroBound` — `l₁ = l₂ = 0`, where the pieces are independent of `ρ`
  (`varpPiece_height_zero_eq`, from `iwArithFreqs ρ 0 = {0}`) and the §6 model tuple vanishes
  (`modelTuple_eq_zero_of_lo`), so the estimate is the `l = 0` half of the model approximation
  `Work.KMTAreas.A7.ModelApproxLo`, transported from a small `ρ` to the given one by
  `mainPartTuple_heightZero_restrict` + `variationalNorm_indicator_upper_le` and with the loss
  weight absorbed by `lossWeight_le_const`;
* `mixedRangeBound` — exactly one of `l₁, l₂` vanishes, which is the mixed chapter of §6--§8
  (the model approximation of the mixed range together with the §8 linear estimates).

The two are combined in `heightZeroBound` by subadditivity of the constants.
-/

/-- `eLpNorm` of a constant multiple of an `ℝ≥0∞`-valued function at `p = 1`. -/
theorem eLpNorm_one_const_mul (c : ENNReal) (hc : c ≠ ⊤) (F : ℤ → ENNReal) :
    MeasureTheory.eLpNorm (fun x : ℤ => c * F x) 1 MeasureTheory.Measure.count
      = c * MeasureTheory.eLpNorm F 1 MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm),
    MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  have h1 : (fun x : ℤ => ‖c * F x‖ₑ) = fun x : ℤ => c * F x := by
    funext x; simp only [enorm_eq_self]
  have h2 : (fun x : ℤ => ‖F x‖ₑ) = F := by
    funext x; simp only [enorm_eq_self]
  rw [h1, h2, MeasureTheory.lintegral_const_mul' c F hc]

/-- **The range `l₁ = l₂ = 0` of the target.**  The estimate at the given parameter `ρ` is obtained
from the estimate at a smaller reference parameter `ρ'' ≤ ρ` (where the pieces agree, the guard
being an upper subset) by `mainPartTuple_heightZero_restrict` + `variationalNorm_indicator_upper_le`
and the absorption `lossWeight_le_const` of the §6 loss weight at bounded height. -/
theorem heightZeroZeroBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL 0 0 k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  obtain ⟨c, hc, ρ₀, hρ₀, hK⟩ :=
    Work.PieceBoundedH.heightZeroZeroSmallRho P hd r hr C₀ hC₀ hA1 B
  set ρ'' : ℝ := min ρ ρ₀ / 2 with hρ''def
  have hminpos : 0 < min ρ ρ₀ := lt_min hρ hρ₀
  have hρ''pos : 0 < ρ'' := by rw [hρ''def]; linarith
  have hρ''lt : ρ'' < min ρ ρ₀ := by rw [hρ''def]; linarith
  have hρ''leρ : ρ'' ≤ ρ := le_trans hρ''lt.le (min_le_left _ _)
  have hρ''leρ₀ : ρ'' ≤ ρ₀ := le_trans hρ''lt.le (min_le_right _ _)
  obtain ⟨K, hK'⟩ := hK ρ'' hρ''pos hρ''leρ₀
  set W : ℝ := (1 + (B : ℝ)) ^ c * (2 : ℝ) ^ (c * (B : ℝ)) with hWdef
  have hWnn : 0 ≤ W := by rw [hWdef]; positivity
  refine ⟨fun Λ => (2 : NNReal) * (K Λ * Real.toNNReal W), ?_⟩
  intro a Λ k₁ k₂ f g hΛ ha ha1 hlcL hQ
  have hb := hK' a Λ k₁ k₂ f g hΛ ha ha1 hlcL hQ
  have hWle : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight c ρ'' 0 0 k₁ k₂)
      ≤ ENNReal.ofReal W := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hWdef]
    exact lossWeight_le_const hc hρ''pos (le_trans hρ''leρ hρ1) hlcL
  have hb' : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ'' P C₀ a f g 0 0 k₁ k₂ n x))
      1 MeasureTheory.Measure.count
      ≤ (K Λ : ENNReal) * ENNReal.ofReal W
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
    hb.trans (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hWle) le_rfl) le_rfl)
  have hpoint : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x)
      ≤ 2 * PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ'' P C₀ a f g 0 0 k₁ k₂ n x) := by
    intro x
    set E : Set ℕ := {n | Work.KMTAreas.A7.loGuard ρ C₀ a 0 0 k₁ k₂ n} with hE
    have hEup : ∀ n m : ℕ, n ∈ E → n ≤ m → m ∈ E := by
      intro n m hn hnm
      exact loGuard_mono_index hΛ ha ha1 hnm hn
    have hfam : (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x)
        = E.indicator (fun n : ℕ =>
            Work.KMTAreas.A7.mainPartTuple ρ'' P C₀ a f g 0 0 k₁ k₂ n x) := by
      funext n
      rw [Set.indicator_apply]
      exact mainPartTuple_heightZero_restrict hρ''leρ P C₀ a f g k₁ k₂ n x
    rw [hfam]
    exact variationalNorm_indicator_upper_le hr1 _ E hEup
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 0 k₁ k₂ n x))
        1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => 2 * PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ'' P C₀ a f g 0 0 k₁ k₂ n x))
        1 MeasureTheory.Measure.count :=
        MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by
          simpa only [enorm_eq_self] using hpoint x)
    _ = 2 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ'' P C₀ a f g 0 0 k₁ k₂ n x))
        1 MeasureTheory.Measure.count :=
        eLpNorm_one_const_mul 2 (by norm_num) _
    _ ≤ 2 * ((K Λ : ENNReal) * ENNReal.ofReal W
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := mul_le_mul' le_rfl hb'
    _ = (((2 : NNReal) * (K Λ * Real.toNNReal W) : NNReal) : ENNReal)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
        rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_ofNat,
          ← ENNReal.ofNNReal_toNNReal]
        ring

/-- **The mixed range of the target**: exactly one of `l₁`, `l₂` vanishes.  This is the mixed
chapter of §6--§8, proved for `0 < ρ ≤ 1` and bounded heights in the parallel development
`Work.KMTPlan.A6.BoundedHMain` (`heightZeroLeft` for `l₁ = 0`, `l₂ ≥ 1`, `heightZeroRight` for
`l₁ ≥ 1`, `l₂ = 0`); the two constants are combined with `max`. -/
theorem mixedRangeBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) →
        ((l₁ = 0 ∧ 1 ≤ l₂) ∨ (1 ≤ l₁ ∧ l₂ = 0)) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨Kl, hKl⟩ := Work.KMTPlan.A6.BoundedHMain.heightZeroLeft P hd r hr C₀ hC₀ ρ hρ hρ1 B
  obtain ⟨Kr, hKr⟩ := Work.KMTPlan.A6.BoundedHMain.heightZeroRight P hd r hr C₀ hC₀ ρ hρ hρ1 B
  refine ⟨fun Λ => max (Kl Λ) (Kr Λ), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hB hQ hL
  have hle : (Kl Λ : ENNReal) ≤ ((max (Kl Λ) (Kr Λ) : NNReal) : ENNReal) :=
    ENNReal.coe_le_coe.mpr (le_max_left _ _)
  have hle' : (Kr Λ : ENNReal) ≤ ((max (Kl Λ) (Kr Λ) : NNReal) : ENNReal) :=
    ENNReal.coe_le_coe.mpr (le_max_right _ _)
  rcases hL with ⟨h₁, hl₂⟩ | ⟨hl₁, h₂⟩
  · subst h₁
    exact (hKl a Λ l₂ k₁ k₂ f g hΛ ha ha1 hB hQ hl₂).trans
      (mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl)
  · subst h₂
    exact (hKr a Λ l₁ k₁ k₂ f g hΛ ha ha1 hB hQ hl₁).trans
      (mul_le_mul' (mul_le_mul' hle' le_rfl) le_rfl)

/-- **The height-zero bound for the concrete §5 columns.**  Case split into `l₁ = l₂ = 0`
(`heightZeroZeroBound`) and the mixed range (`mixedRangeBound`); the constants are added so that
both branches are dominated by a single `K`. -/
theorem heightZeroBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) → (l₁ = 0 ∨ l₂ = 0) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨K₀, hK₀⟩ := heightZeroZeroBound P hd r hr C₀ hC₀ hA1 ρ hρ hρ1 B
  obtain ⟨Km, hKm⟩ := mixedRangeBound P hd r hr C₀ hC₀ hA1 ρ hρ hρ1 B
  refine ⟨fun Λ => K₀ Λ + Km Λ, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hB hQ hL
  have hle : (K₀ Λ : ENNReal) ≤ ((K₀ Λ + Km Λ : NNReal) : ENNReal) := by
    rw [ENNReal.coe_add]
    exact le_add_of_nonneg_right bot_le
  have hle' : (Km Λ : ENNReal) ≤ ((K₀ Λ + Km Λ : NNReal) : ENNReal) := by
    rw [ENNReal.coe_add]
    exact le_add_of_nonneg_left bot_le
  rcases hL with h | h
  · subst h
    by_cases h₂ : l₂ = 0
    · subst h₂
      refine (hK₀ a Λ k₁ k₂ f g hΛ ha ha1 hB hQ).trans ?_
      exact mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl
    · exact (hKm a Λ 0 l₂ k₁ k₂ f g hΛ ha ha1 hB hQ (Or.inl ⟨rfl, by omega⟩)).trans
        (mul_le_mul' (mul_le_mul' hle' le_rfl) le_rfl)
  · subst h
    by_cases h₁ : l₁ = 0
    · subst h₁
      refine (hK₀ a Λ k₁ k₂ f g hΛ ha ha1 hB hQ).trans ?_
      exact mul_le_mul' (mul_le_mul' hle le_rfl) le_rfl
    · exact (hKm a Λ l₁ 0 k₁ k₂ f g hΛ ha ha1 hB hQ (Or.inr ⟨by omega, rfl⟩)).trans
        (mul_le_mul' (mul_le_mul' hle' le_rfl) le_rfl)

end Work.KMTPlan.A6.PieceBoundedH
