import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FockBridge.Count
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FockBridge

open MeasureTheory

/-- **The FS box projection `Q_{B,i}` is `B`-sector additive.**

FS's mean-free projection `Q_{B,i}Φ = 1_{A}(x_i)·Φ − P_{B,i}Φ` is *linear* in `Φ`, and its two
occurrences of `Φ` — the pointwise value `Φ x` and the fibre average `∫_A Φ(x[i↦z]) dz` — are
both additive over the sector decomposition `Φ = Σ_k 1_{sector k}·Φ`.  The pointwise part is the
sector partition (`sum_sectorPiece`); the fibre part uses that a finite sum interacts with the
Bochner integral (finiteness, no convergence issue: each sector piece is integrable by `hint`).

So `Q_{B,i}` of the whole state is the sum of `Q_{B,i}` of its count-`k` pieces — the
particle-number decomposition of the kinetic half of the residual. -/
theorem boxQInd_eq_sum_sectorPiece {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {volA : ℝ} (i : Fin N) {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hint : ∀ k ∈ Finset.range (N + 1), ∀ x : Fin N → EuclideanSpace ℝ (Fin 3),
      MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        Work.FockBridge.sectorPiece A k Φ (Function.update x i z)))
    (hint0 : ∀ x : Fin N → EuclideanSpace ℝ (Fin 3),
      MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Function.update x i z)))
    (x : Fin N → EuclideanSpace ℝ (Fin 3)) :
    Work.UBBInputs8.boxQInd volA A i Φ x
      = ∑ k ∈ Finset.range (N + 1),
          Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ) x := by
  classical
  -- `Q_{B,i}` factors the box indicator out of both terms.
  have key : ∀ Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ,
      Work.UBBInputs8.boxQInd volA A i Ψ x
        = A.indicator (fun _ => (1 : ℝ)) (x i) *
          (Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z)) := by
    intro Ψ
    simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    ring
  rw [key Φ]
  rw [show (∑ k ∈ Finset.range (N + 1),
        Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ) x)
      = A.indicator (fun _ => (1 : ℝ)) (x i) *
        (∑ k ∈ Finset.range (N + 1), (Work.FockBridge.sectorPiece A k Φ x
          - (1 / volA) *
            ∫ z in A, Work.FockBridge.sectorPiece A k Φ (Function.update x i z))) from by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => key (Work.FockBridge.sectorPiece A k Φ))]
  congr 1
  rw [Finset.sum_sub_distrib]
  congr 1
  · exact (Work.FockBridge.sum_sectorPiece A Φ x).symm
  · rw [← Finset.mul_sum]
    congr 1
    rw [← MeasureTheory.integral_finsetSum (μ := volume.restrict A) (Finset.range (N + 1))
      (f := fun k z => Work.FockBridge.sectorPiece A k Φ (Function.update x i z))]
    · exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
        (fun z => (Work.FockBridge.sum_sectorPiece A Φ (Function.update x i z)).symm))
    · intro k hk
      exact (hint k hk x).integrableOn

end Work.FockBridge
