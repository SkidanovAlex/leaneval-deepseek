/-
# The §6 model-approximation error at bounded heights (`Work.KMTPlan.A6.PieceBoundedH.errorBound`)

Target: the `ℓ¹(ℤ; V^r)`-bound for the family `mainPartTuple − modelTupleRep` (the error of the §6
model approximation), uniformly in the lacunary scale sequence `a`, in the quadruples of
heights with `lcL l₁ l₂ k₁ k₂ ≤ B` and `1 ≤ l₁, l₂`, and in `f, g`, with a constant `K(Λ)`
depending only on the lacunarity parameter:

  `‖ Vʳ_n (mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n · − modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n ·) ‖_{ℓ¹(ℤ)}`
  `   ≤ K(Λ) ‖f‖₂ ‖g‖₂`.

This is the `(2,2,1)` instance of the paper's Proposition `mod-approx` at *bounded arithmetic
height*, with the loss absorbed into `K(Λ)`: the height bound `lcL ≤ B` makes every weight of the
§6 estimate a constant (`repWeight A ρ l₁ l₂ k₁ k₂ ≤ 2 ^ (A * (2 ^ (ρ*B) + B))`) and bounds the band
parameter (`uRep ρ l₁ l₂ k₁ k₂ ≤ uRep ρ B B B B`), and it makes the *off-band* scales
(`¬ bandCond`, where the repaired model vanishes and only the concrete column is left) a *finite*
initial segment of the lacunary sequence.  No smallness restriction on `ρ` (the paper's
`ρ ≤ 1/(4C₀)`, as in `Work.KMTAreas.A7.repMain`) is needed; only `0 < ρ ≤ 1`, which is what
`Work.KMTAreas.A7.RepMassBound` requires.

## Structure of the proof

The family splits pointwise, with no hypothesis,

  `mainPartTuple − modelTupleRep = uOn + uOff`,

where `uOn` is the part on the band (`hiCore ∧ bandCond`) and `uOff` the part off the band
(`hiCore ∧ ¬ bandCond`); off `hiCore` both tuples vanish.  By the subadditivity of the variational
norm and of the `ℒ¹`-seminorm it therefore suffices to bound the two masked families, which is the
content of the two modules `errorBoundOnBand` (mass bound of `RepMassBound` + the single-scale
estimate `repSingleScale` + the lacunary summability `invFloor_tsum_le`) and `errorBoundOffBand`
(finitely many scales + the crude single-scale bound `RepOffBandCrude`).  The present file contains
the assembly `errorBound_of_halves` and the final application.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.PieceBoundedH.onBandSelf
import Submission.Work.KMTPlan.A6.PieceBoundedH.offBandSelf
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.PieceBoundedH

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-! ## The two halves of the estimate, as `Prop`s -/

/-- **The on-band half**: on the admissible scales of the main regime which also satisfy the band
condition `bandCond`, the `ℓ¹(ℤ;V^r)`-norm of the masked family
`mainPartTuple − modelTupleRep` is bounded by `K(Λ)‖f‖₂‖g‖₂`. -/
def OnBandBound (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) : Prop :=
  ∃ K : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
      lcL l₁ l₂ k₁ k₂ ≤ B → 1 ≤ l₁ → 1 ≤ l₂ →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
              ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
            Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            else 0))
        1 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-- **The off-band half**: on the admissible scales of the main regime where the band condition
*fails* (there the repaired model vanishes and the family is the concrete column), the same bound
holds. -/
def OffBandBound (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) : Prop :=
  ∃ K : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
      lcL l₁ l₂ k₁ k₂ ≤ B → 1 ≤ l₁ → 1 ≤ l₂ →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
              ∧ ¬ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
            Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            else 0))
        1 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-! ## The assembly -/

/-- **The bounded-height §6 model-approximation error, from its two halves.**

`mainPartTuple − modelTupleRep = uOn + uOff` pointwise (off `hiCore` both tuples vanish, on
`hiCore` the two masks `bandCond` and `¬ bandCond` partition the scales), so the variational norm is
subadditive and the `ℒ¹`-seminorm is subadditive (`eLpNorm_add_le` at the exponent `1`); adding the
two halves and combining the constants finishes. -/
theorem errorBound_of_halves (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ)
    (hOn : OnBandBound P r C₀ ρ B) (hOff : OffBandBound P r C₀ ρ B) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        lcL l₁ l₂ k₁ k₂ ≤ B → 1 ≤ l₁ → 1 ≤ l₂ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨Kon, hKon⟩ := hOn
  obtain ⟨Koff, hKoff⟩ := hOff
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  refine ⟨fun Λ => Kon Λ + Koff Λ, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hl₁ hl₂
  -- the two masked families
  set uOn : ℕ → ℤ → ℂ := fun n x =>
      if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
          ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
        Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      else 0 with huOn
  set uOff : ℕ → ℤ → ℂ := fun n x =>
      if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
          ∧ ¬ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
        Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      else 0 with huOff
  -- the two halves
  have hOn' : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => uOn n x))
      1 MeasureTheory.Measure.count
      ≤ (Kon Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    simpa only [huOn] using hKon a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hl₁ hl₂
  have hOff' : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => uOff n x))
      1 MeasureTheory.Measure.count
      ≤ (Koff Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    simpa only [huOff] using hKoff a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hl₁ hl₂
  -- the pointwise splitting
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => uOn n x)
        + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => uOff n x) := by
    intro x
    have heq : (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = (fun n : ℕ => uOn n x) + (fun n : ℕ => uOff n x) := by
      funext n
      by_cases hc : Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
      · by_cases hb : Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
        · have hcond : Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
              ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) := ⟨hc, hb⟩
          have hcond2 : ¬ (Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
              ∧ ¬ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) :=
            fun h => h.2 hb
          simp only [huOn, huOff, Pi.add_apply, if_pos hcond, if_neg hcond2, add_zero]
        · have hcond : ¬ (Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
              ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) := fun h => hb h.2
          have hcond2 : Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
              ∧ ¬ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) := ⟨hc, hb⟩
          simp only [huOn, huOff, Pi.add_apply, if_neg hcond, if_pos hcond2, zero_add]
      · -- off `hiCore` both tuples vanish
        have h1 : Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n = 0 := by
          have hconj : ¬ (Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ))
              (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
              ∧ Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
                  < Nat.floor (a n)
              ∧ Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n))) :=
            fun h => hc ⟨h.1, h.2.1, h.2.2⟩
          funext y
          simp only [Work.KMTAreas.A7.mainPartTuple, if_neg hconj, Pi.zero_apply]
        have h2 : Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n = 0 := by
          have hconj : ¬ (Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ))
              (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
              ∧ Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
                  < Nat.floor (a n)
              ∧ Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n))
              ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) :=
            fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩
          funext y
          simp only [Work.KMTAreas.A7.modelTupleRep, if_neg hconj, Pi.zero_apply]
        have hcond : ¬ (Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
            ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) := fun h => hc h.1
        have hcond2 : ¬ (Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
            ∧ ¬ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) := fun h => hc h.1
        rw [h1, h2]
        simp only [huOn, huOff, Pi.add_apply, Pi.zero_apply, sub_zero, zero_add,
          if_neg hcond, if_neg hcond2]
    rw [heq]
    exact Submission.PointwiseErgodicTheorems.variationalNorm_add_le hr1 _ _
  -- the `ℒ¹`-seminorm is subadditive and monotone
  have hmono : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => uOn n x)
            + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => uOff n x))
        1 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpt x)
  have hadd : MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => uOn n x)
            + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => uOff n x))
        1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => uOn n x))
          1 MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => uOff n x))
          1 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_add_le le_rfl
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        1 MeasureTheory.Measure.count
      ≤ _ := hmono
    _ ≤ _ := hadd
    _ ≤ (Kon Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
        + (Koff Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := add_le_add hOn' hOff'
    _ = ((Kon Λ + Koff Λ : NNReal) : ENNReal)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
        rw [ENNReal.coe_add]
        ring

theorem errorBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → 1 ≤ l₁ → 1 ≤ l₂ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
  errorBound_of_halves P hd r hr C₀ hC₀ ρ hρ hρ1 B
    (onBandSelf P hd r hr C₀ hC₀ ρ hρ hρ1 B)
    (offBandSelf P hd r hr C₀ hC₀ ρ hρ hρ1 B)

end

end Work.KMTPlan.A6.PieceBoundedH
