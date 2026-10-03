import Mathlib
import Submission.LpMinkowski
import Submission.VarSums
import Submission.Port.Aesm

/-!
# Countable subadditivity of the variational norm, fourfold

This module combines the two tools of `Submission.Work.Analysis.EndVar.VarpTsum`,

* `variationalNorm_tsum_le`, the subadditivity of the variational norm over a pointwise countable
  sum of eventually vanishing families, and
* `eLpNorm_tsum_le_tsum_eLpNorm`, Minkowski's inequality for countable sums,

into the fourfold form used by the §5 assembly of the major arc part: the `ℓ^p(ℤ;V^r)` norm of a
quadruple series of eventually vanishing columns is at most the quadruple series of the
`ℓ^p(ℤ;V^r)` norms of its columns.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Analysis.EndVar

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems

/-- One level of the countable subadditivity: the `ℓ^p(ℤ;V^r)` norm of a pointwise countable sum
of eventually vanishing columns is at most the sum of the `ℓ^p(ℤ;V^r)` norms of the columns. -/
lemma eLpNorm_variationalNorm_tsum_le {r : ℝ≥0} (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {b : ℕ → (ℕ → ℤ → ℂ)}
    (hb : ∀ n : ℕ, ∃ K : ℕ, ∀ k ≥ K, ∀ x : ℤ, b k n x = 0) :
    eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => ∑' k, b k n x)) p Measure.count
      ≤ ∑' k, eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => b k n x))
          p Measure.count := by
  have hpoint : ∀ x : ℤ, variationalNorm r (fun n : ℕ => ∑' k, b k n x)
      ≤ ∑' k, variationalNorm r (fun n : ℕ => b k n x) := by
    intro x
    refine variationalNorm_tsum_le hr (b := fun k n => b k n x) ?_
    intro n
    obtain ⟨K, hK⟩ := hb n
    exact ⟨K, fun k hk => hK k hk x⟩
  refine (eLpNorm_mono_enorm (hf := by pw_aesm)
    (f := fun x : ℤ => variationalNorm r (fun n : ℕ => ∑' k, b k n x))
    (g := fun x : ℤ => ∑' k, variationalNorm r (fun n : ℕ => b k n x))
    (fun x => ?_)).trans ?_
  · simpa only [enorm_eq_self] using hpoint x
  · refine eLpNorm_tsum_le_tsum_eLpNorm hp (fun k => ?_)
    exact (measurable_of_countable _).aemeasurable

/-- **Fourfold countable subadditivity.**  If each index family is eventually zero along every
column, the `ℓ^p(ℤ;V^r)` norm of the quadruple series is at most the quadruple series of the
`ℓ^p(ℤ;V^r)` norms. -/
theorem variationalNorm_quad_tsum_eLpNorm_le {r : ℝ≥0} (hr : 1 ≤ r) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {b : ℕ → ℕ → ℕ → ℕ → (ℕ → ℤ → ℂ)}
    (hb1 : ∀ n : ℕ, ∃ K : ℕ, ∀ l₁ ≥ K, ∀ l₂ k₁ k₂ (x : ℤ), b l₁ l₂ k₁ k₂ n x = 0)
    (hb2 : ∀ n l₁ : ℕ, ∃ K : ℕ, ∀ l₂ ≥ K, ∀ k₁ k₂ (x : ℤ), b l₁ l₂ k₁ k₂ n x = 0)
    (hb3 : ∀ n l₁ l₂ : ℕ, ∃ K : ℕ, ∀ k₁ ≥ K, ∀ k₂ (x : ℤ), b l₁ l₂ k₁ k₂ n x = 0)
    (hb4 : ∀ n l₁ l₂ k₁ : ℕ, ∃ K : ℕ, ∀ k₂ ≥ K, ∀ x : ℤ, b l₁ l₂ k₁ k₂ n x = 0) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ, b l₁ l₂ k₁ k₂ n x))
      p MeasureTheory.Measure.count
      ≤ ∑' l₁ : ℕ, ∑' l₂ : ℕ, ∑' k₁ : ℕ, ∑' k₂ : ℕ,
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => b l₁ l₂ k₁ k₂ n x)) p MeasureTheory.Measure.count := by
  have hb1' : ∀ (n : ℕ), ∃ K : ℕ, ∀ l₁ ≥ K, ∀ x : ℤ,
      (∑' l₂, ∑' k₁, ∑' k₂, b l₁ l₂ k₁ k₂ n x) = 0 := by
    intro n
    obtain ⟨K, hK⟩ := hb1 n
    refine ⟨K, fun l₁ hl₁ x => ?_⟩
    have hz : ∀ l₂ k₁ k₂, b l₁ l₂ k₁ k₂ n x = 0 := fun l₂ k₁ k₂ => hK l₁ hl₁ l₂ k₁ k₂ x
    simp only [hz, tsum_zero]
  have hb2' : ∀ (l₁ : ℕ) (n : ℕ), ∃ K : ℕ, ∀ l₂ ≥ K, ∀ x : ℤ,
      (∑' k₁, ∑' k₂, b l₁ l₂ k₁ k₂ n x) = 0 := by
    intro l₁ n
    obtain ⟨K, hK⟩ := hb2 n l₁
    refine ⟨K, fun l₂ hl₂ x => ?_⟩
    have hz : ∀ k₁ k₂, b l₁ l₂ k₁ k₂ n x = 0 := fun k₁ k₂ => hK l₂ hl₂ k₁ k₂ x
    simp only [hz, tsum_zero]
  have hb3' : ∀ (l₁ l₂ : ℕ) (n : ℕ), ∃ K : ℕ, ∀ k₁ ≥ K, ∀ x : ℤ,
      (∑' k₂, b l₁ l₂ k₁ k₂ n x) = 0 := by
    intro l₁ l₂ n
    obtain ⟨K, hK⟩ := hb3 n l₁ l₂
    refine ⟨K, fun k₁ hk₁ x => ?_⟩
    have hz : ∀ k₂, b l₁ l₂ k₁ k₂ n x = 0 := fun k₂ => hK k₁ hk₁ k₂ x
    simp only [hz, tsum_zero]
  have hb4' : ∀ (l₁ l₂ k₁ : ℕ) (n : ℕ), ∃ K : ℕ, ∀ k₂ ≥ K, ∀ x : ℤ,
      b l₁ l₂ k₁ k₂ n x = 0 := by
    intro l₁ l₂ k₁ n
    obtain ⟨K, hK⟩ := hb4 n l₁ l₂ k₁
    exact ⟨K, fun k₂ hk₂ x => hK k₂ hk₂ x⟩
  calc eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => ∑' l₁, ∑' l₂, ∑' k₁, ∑' k₂, b l₁ l₂ k₁ k₂ n x)) p Measure.count
      ≤ ∑' l₁, eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => ∑' l₂, ∑' k₁, ∑' k₂, b l₁ l₂ k₁ k₂ n x)) p Measure.count :=
        eLpNorm_variationalNorm_tsum_le hr hp
          (b := fun l₁ n x => ∑' l₂, ∑' k₁, ∑' k₂, b l₁ l₂ k₁ k₂ n x) hb1'
    _ ≤ ∑' l₁, ∑' l₂, eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => ∑' k₁, ∑' k₂, b l₁ l₂ k₁ k₂ n x)) p Measure.count :=
        ENNReal.tsum_le_tsum (fun l₁ => eLpNorm_variationalNorm_tsum_le hr hp
          (b := fun l₂ n x => ∑' k₁, ∑' k₂, b l₁ l₂ k₁ k₂ n x) (hb2' l₁))
    _ ≤ ∑' l₁, ∑' l₂, ∑' k₁, eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => ∑' k₂, b l₁ l₂ k₁ k₂ n x)) p Measure.count :=
        ENNReal.tsum_le_tsum (fun l₁ => ENNReal.tsum_le_tsum (fun l₂ =>
          eLpNorm_variationalNorm_tsum_le hr hp
            (b := fun k₁ n x => ∑' k₂, b l₁ l₂ k₁ k₂ n x) (hb3' l₁ l₂)))
    _ ≤ ∑' l₁, ∑' l₂, ∑' k₁, ∑' k₂, eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => b l₁ l₂ k₁ k₂ n x)) p Measure.count :=
        ENNReal.tsum_le_tsum (fun l₁ => ENNReal.tsum_le_tsum (fun l₂ =>
          ENNReal.tsum_le_tsum (fun k₁ => eLpNorm_variationalNorm_tsum_le hr hp
            (b := fun k₂ n x => b l₁ l₂ k₁ k₂ n x) (hb4' l₁ l₂ k₁))))

end

end Work.Analysis.EndVar
