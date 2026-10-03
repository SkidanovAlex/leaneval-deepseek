/-
# The `l = 0` input of the large-scale assembly, reduced to the proved `ModelApproxLo`

On the range `¬ (1 ≤ l₁ ∧ 1 ≤ l₂)` of the arithmetic heights at least one of `l₁, l₂` is `0`, and
then *both* models vanish identically:

* `Tex ρ 0 φ f = 0` because `iwArithFreqsNew ρ 0 = ∅` (`Nat` truncated subtraction), hence
  `Work.KMTAreas.A7.modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ = 0` (`LoDefs.modelTuple_eq_zero_of_lo`) and
  `Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ = 0`
  (`ModelApproxLoRepClean.modelTupleRep_eq_zero_of_lo`).

Consequently the `hLo` input of `Work.KMTAreas.A7.largeLoss_of_hi_lo_rep` is *the same statement* as
the already proved `Work.KMTAreas.A7.ModelApproxLo` (which is about `modelTuple`), and
`ModelApproxLoBridge` below is the two-line transfer.  This file exists so that the dependency of
`LargeLoss` on the heavy §8 machinery of `ModelApproxLoRep.lean` is replaced by a dependency on
`ModelApproxLo` alone (the file `ModelApproxLoRep.lean` imports `A7Hi2.supBound` and
`A7Hi2.chainLe`, whose closures currently clash on the duplicate declaration
`Work.KMTAreas.A7Hi2.abelAnnuli`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxLoRepClean

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-- **The `l = 0` half of the §6 model approximation for the repaired model `modelTupleRep`**,
transferred from the proved `Work.KMTAreas.A7.ModelApproxLo` (whose statement is identical up to
the vanishing of the two model tuples on this range). -/
theorem ModelApproxLoBridge (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
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
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  intro C₀ r hC₀ hr
  obtain ⟨c, hc, ρ₀, hρ₀, h⟩ :=
    ModelApproxLo P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum C₀ r hC₀ hr
  refine ⟨c, hc, ρ₀, hρ₀, ?_⟩
  intro ρ hρ hρle
  obtain ⟨K, hK⟩ := h ρ hρ hρle
  refine ⟨K, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hlo
  have hfam : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)) := by
    funext x
    congr 1
    funext n
    rw [modelTupleRep_eq_zero_of_lo ρ P C₀ a f g l₁ l₂ k₁ k₂ hlo,
      modelTuple_eq_zero_of_lo ρ P C₀ a f g l₁ l₂ k₁ k₂ hlo]
  rw [hfam]
  exact hK a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hlo

end

end Work.KMTAreas.A7
