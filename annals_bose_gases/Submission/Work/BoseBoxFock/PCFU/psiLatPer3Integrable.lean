import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pinQLimDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- On the ball of radius `ρ`, the `ℓℤ³`-periodisation of a weight vanishing outside the ball of
radius `R` is the finite sum over the lattice points `m` with `‖ℓ • latVec m‖ ≤ R + ρ`. -/
lemma latPer_eq_sum_latBall {ℓ ρ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWs : ∀ x, R ≤ ‖x‖ → W x = 0) {z : E3} (hz : ‖z‖ ≤ ρ) :
    LatFourier.latPer ℓ W z
      = ∑ m ∈ LatFourier.latBall ((R + ρ) / ℓ), ((W (z + ℓ • latVec m) : ℝ) : ℂ) := by
  rw [LatFourier.latPer]
  refine tsum_eq_sum (s := LatFourier.latBall ((R + ρ) / ℓ)) (fun m hm => ?_)
  have hnot : (R + ρ) / ℓ < ‖latVec m‖ := by
    rw [← not_le]
    intro hc
    exact hm ((LatFourier.mem_latBall).mpr hc)
  have h5 : ‖ℓ • latVec m‖ = ℓ * ‖latVec m‖ := LatFourier.latVec_norm_smul ℓ hℓ.le m
  have h4 : R + ρ < ℓ * ‖latVec m‖ := by
    rw [div_lt_iff₀ hℓ] at hnot; linarith
  have hgt : R ≤ ‖z + ℓ • latVec m‖ := by
    have h2 : ‖ℓ • latVec m‖ ≤ ‖z + ℓ • latVec m‖ + ‖z‖ := by
      calc ‖ℓ • latVec m‖ = ‖(z + ℓ • latVec m) - z‖ := by congr 1; abel
        _ ≤ ‖z + ℓ • latVec m‖ + ‖z‖ := norm_sub_le _ _
    linarith
  simp [hWs _ hgt]

/-- Integrability of the pairing of a smooth compactly supported `Ψ` with the periodisation
`latPer3 ℓ W = ℓ³ Σ'_m W(· + ℓ • latVec m)` of an `L¹` weight `W` supported in the ball of radius
`R` (`hWs`).  (`W` need not be continuous nor bounded; on the support of `Ψ` the periodisation is a
finite sum over `Work.BoseBoxFock.LatFourier.latFinSet ℓ (R + ρ)`, `ρ` a support radius of `Ψ`.) -/
theorem psiLatPer3Integrable {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hWs : ∀ x, R ≤ ‖x‖ → W x = 0)
    {Ψ : EuclideanSpace ℝ (Fin 3) → ℂ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨs : HasCompactSupport Ψ) :
    MeasureTheory.Integrable (fun z => Ψ z * Work.BoseBoxFock.latPer3 ℓ W z) := by
  -- a support radius of `Ψ`
  obtain ⟨ρ, hρ⟩ := hΨs.isCompact.isBounded.subset_closedBall (0 : E3)
  have hsupp : Function.support Ψ ⊆ Metric.closedBall (0 : E3) ρ :=
    (subset_tsupport Ψ).trans hρ
  have hzero : ∀ z, z ∉ Metric.closedBall (0 : E3) ρ → Ψ z = 0 := fun z hz =>
    not_not.mp (fun h => hz (hsupp (Function.mem_support.mpr h)))
  -- a bound for `Ψ`
  obtain ⟨C₀, hC₀⟩ := hΨs.exists_bound_of_continuous hΨ.continuous
  set C : ℝ := max C₀ 0 with hCdef
  have hC : ∀ z, ‖Ψ z‖ ≤ C := fun z => le_trans (hC₀ z) (le_max_left _ _)
  -- the finite set of relevant lattice points
  set s : Finset (Fin 3 → ℤ) := LatFourier.latBall ((R + ρ) / ℓ) with hs
  -- on the support of `Ψ` the target is the finite sum over `s`
  have hpoint : ∀ z : E3, (∑ m ∈ s,
        (((ℓ ^ 3 : ℝ) : ℂ) * (((W (z + ℓ • latVec m) : ℝ) : ℂ) * Ψ z)))
      = Ψ z * Work.BoseBoxFock.latPer3 ℓ W z := by
    intro z
    by_cases hz : ‖z‖ ≤ ρ
    · rw [Work.BoseBoxFock.latPer3, latPer_eq_sum_latBall hℓ hWs hz]
      rw [← mul_assoc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    · have hz' : z ∉ Metric.closedBall (0 : E3) ρ := by
        simp only [Metric.mem_closedBall, dist_eq_norm]
        simpa using not_le.mp hz
      rw [hzero z hz']
      simp
  -- that finite sum is integrable
  have hF : Integrable (fun z : E3 => ∑ m ∈ s,
        (((ℓ ^ 3 : ℝ) : ℂ) * (((W (z + ℓ • latVec m) : ℝ) : ℂ) * Ψ z))) := by
    refine integrable_finsetSum _ (fun m _ => ?_)
    refine Integrable.const_mul ?_ _
    exact ((hW.comp_add_right (ℓ • latVec m)).ofReal).mul_bdd
      hΨ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => hC z))
  exact hF.congr (Filter.Eventually.of_forall (fun z => hpoint z))

end Work.BoseBoxFock.PCFU
