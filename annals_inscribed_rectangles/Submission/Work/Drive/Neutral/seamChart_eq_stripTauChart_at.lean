import Mathlib
import Submission.Work.Drive.Neutral.stripSeamChart
import Submission.Work.Drive.Neutral.stripTauChart

/-!
# The seam chart at a single point is the `τ`-chart of the strip

`Submission/Work/Drive/stripSeamChart.lean` proves the *eventual* statement
`Work.Drive.Neutral.seamChart_eq_stripTauChart`: on a neighbourhood of the base point `p₀`, every point `p` of the
half-plane `τ ≥ 0` at which the factorised data `G` is *honest* (positive radial coordinate, disk
coordinate in the closed unit disk, third coordinate of unit modulus and branch point avoided) has the same
image under the seam chart of the capped plane and under the `τ`-chart of the configuration strip.

This file records the *pointwise* form of that computation, which is what the assembly needs: with the
honesty conditions assumed at the single point `p`, the two charts agree *at* `p`.  The proof is the same
chain of identifications (`seamHalf` squares to the circle coordinate `circOf`, the lens-space class of the
configuration point maps to the projective class of `seamProjVec`, and `seamChart` is `cappingSpaceHomeoProj`
inverse), with the `filter_upwards` of the original replaced by explicit hypotheses.
-/

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff Topology
open Classical

noncomputable section

theorem seamChart_eq_stripTauChart_at (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (σ₀ : ℝ)
    {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p₀ p : EuclideanSpace ℝ (Fin 2)} (hunit : ‖(G p₀).2.2‖ = 1)
    (hp0 : 0 ≤ p 1) (h1 : 0 < (G p).1) (h2 : ‖(G p).2.1‖ ≤ 1)
    (h3 : ‖(G p).2.2‖ = 1) (hw : Work.Drive.Neutral.seamW G p₀ p + 1 ≠ 0) :
    Work.Drive.Neutral.seamChart G p₀ hunit p = Work.Drive.Neutral.stripTauChart hγ hγne G σ₀ p := by
  have hne : (G p).2.2 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at h3
    norm_num at h3
  have hmem : (G p).2.1 ∈ Metric.closedBall (0 : ℂ) 1 :=
    mem_closedBall_of_norm_le_one h2
  have htd : tauData hγ hγne G σ₀ p = ((G p).1, (G p).2.1, tauS G p) :=
    tauData_eq_of_good hγ hγne G σ₀ ⟨h1, h2⟩
  have hη : tauS G p = circOf ((G p).2.2) h3 := by
    apply circleOf_injective
    rw [circleOf_tauS, tauE_eq_of_norm_eq_one h3, circleOf_circOf]
  have hpiece : (⟨tauData hγ hγne G σ₀ p, tauData_pos hγ hγne G σ₀ p,
      tauData_norm_le_one hγ hγne G σ₀ p⟩ : ConfigPiece)
      = ⟨((G p).1, (G p).2.1, circOf ((G p).2.2) h3), h1, h2⟩ := by
    refine Subtype.ext ?_
    show tauData hγ hγne G σ₀ p = ((G p).1, (G p).2.1, circOf ((G p).2.2) h3)
    rw [htd, hη]
  have hA : cappingSpaceHomeoProj (stripTauChart hγ hγne G σ₀ p)
      = (⟨(G p).1, h1⟩, lensToProj (Quotient.mk'' (Sum.inr
          ((⟨(G p).2.1, hmem⟩ : Metric.closedBall (0 : ℂ) 1), circOf ((G p).2.2) h3) :
            CapTorus ⊕ ConfTorus) : LensSpace)) := by
    have hq : stripTauChart hγ hγne G σ₀ p
        = Quotient.mk'' (Sum.inl ⟨((G p).1, (G p).2.1, circOf ((G p).2.2) h3), h1, h2⟩) := by
      unfold stripTauChart
      exact congrArg (fun x : ConfigPiece => (Quotient.mk'' (Sum.inl x) : CappingSpace)) hpiece
    rw [hq]
    exact cappingSpaceHomeoProj_confPiece (G p).1 (G p).2.1 (circOf ((G p).2.2) h3) h1 h2
  have hu : (seamHalf G p₀ p) ^ 2 = circleOf (circOf ((G p).2.2) h3) := by
    rw [seamHalf_sq hunit hne hw, seamCN_eq_of_norm_eq_one h3]
    exact (circleOf_circOf ((G p).2.2) h3).symm
  have hB : lensToProj (Quotient.mk'' (Sum.inr
        ((⟨(G p).2.1, hmem⟩ : Metric.closedBall (0 : ℂ) 1), circOf ((G p).2.2) h3) :
          CapTorus ⊕ ConfTorus) : LensSpace)
      = Projectivization.mk ℝ (seamProjVec G p₀ p) (seamProjVec_ne_zero hunit p) := by
    rw [lensToProj_confTorus (⟨(G p).2.1, hmem⟩ : Metric.closedBall (0 : ℂ) 1)
      (circOf ((G p).2.2) h3) hu]
    exact projectivizationMk_congr ℝ (Eucl 3)
  have hval : cappingSpaceHomeoProj (stripTauChart hγ hγne G σ₀ p) = seamProj G p₀ hunit p := by
    rw [hA, hB]
    unfold seamProj
    rw [dif_pos h1]
  have hL : cappingSpaceHomeoProj (seamChart G p₀ hunit p) = seamProj G p₀ hunit p := by
    rw [seamChart]
    exact Homeomorph.apply_symm_apply cappingSpaceHomeoProj (seamProj G p₀ hunit p)
  exact cappingSpaceHomeoProj.injective (by rw [hL, hval])

end

end Work.Drive.Neutral
