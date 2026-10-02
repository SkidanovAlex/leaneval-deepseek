import Mathlib
import Submission.Work.ThomBordism.LeadChapter.bdryAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold Topology

namespace Work.ThomBordism.LeadChapter

theorem psiPhiCont (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (ψ : OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)))
    (hbd : ∀ q ∈ ψ.source,
      q ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W ↔ (ψ q).1 0 = 0)
    {y : W} (hyψ : y ∈ ψ.source)
    (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (τ : ℝ) (hτ : 0 < τ) (χ : W → ℝ) (K : Set W)
    (hχ : Continuous χ) (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hK : IsCompact K) (hKsub : K ⊆ ψ.source)
    (hout : ∀ z ∉ K, χ z = 0)
    (hvan : ∀ z ∈ ψ.source, Work.ThomBordism.LeadChapter.psiVa ψ y τ z = 0 → χ z = 1)
    (hcont : ∀ t₀ : ℝ, ∀ v₀ : EuclideanSpace ℝ (Fin (n + 1)), 0 ≤ t₀ → t₀ ≤ 1 →
      (v₀ ≠ 0 ∨ t₀ = 1) →
      ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) =>
        Work.ThomBordism.BCU.profile2 (0 : EuclideanSpace ℝ (Fin (n + 1))) p.1 p.2) (t₀, v₀)) :
    Continuous (Work.ThomBordism.LeadChapter.psiPhi ψ y τ χ) ∧
      (∀ z, Work.ThomBordism.LeadChapter.psiPhi ψ y τ χ z ∈
        Work.ThomBordism.stdHalfBall (n + 1)) := by
  classical
  have hKcl : IsClosed K := hK.isClosed
  refine ⟨?_, ?_⟩
  · -- Continuity: outside `K` the collapse is the constant north pole; inside `K` the point lies in
    -- the (open) source of `ψ`, where `ψ`-coordinates are continuous, and `hcont` is applied to the
    -- pair `(χ z, psiVa z)` — the side condition `v ≠ 0 ∨ t = 1` is exactly `hvan`.
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hzK : z ∈ K
    · have hzsrc : z ∈ ψ.source := hKsub hzK
      have hch : ContinuousAt (fun w : W => (ψ w).1) z :=
        continuous_subtype_val.continuousAt.comp (ψ.continuousAt hzsrc)
      have hva : ContinuousAt (fun w : W => psiVa ψ y τ w) z := by
        simp only [psiVa, psiCh]
        exact (hch.sub continuousAt_const).const_smul τ
      have hpair : ContinuousAt (fun w : W => (χ w, psiVa ψ y τ w)) z :=
        hχ.continuousAt.prodMk hva
      have hcase : psiVa ψ y τ z ≠ 0 ∨ χ z = 1 := by
        by_cases h : psiVa ψ y τ z = 0
        · exact Or.inr (hvan z hzsrc h)
        · exact Or.inl h
      have hprof := hcont (χ z) (psiVa ψ y τ z) (hχ01 z).1 (hχ01 z).2 hcase
      exact ContinuousAt.comp (f := fun w : W => (χ w, psiVa ψ y τ w)) hprof hpair
    · have hev : (fun w => psiPhi ψ y τ χ w) =ᶠ[𝓝 z] (fun _ => BCU.northPole n) := by
        filter_upwards [hKcl.isOpen_compl.mem_nhds hzK] with w hw
        exact psiPhi_eq_northPole ψ y τ χ w (hout w hw)
      exact (continuousAt_const (y := BCU.northPole n)).congr hev.symm
  · -- Membership in the standard half-ball.  Outside `K` the collapse is the north pole; inside `K`
    -- one applies `bcu_profile2_properties` to `psiVa`, whose `0`-th coordinate is nonnegative
    -- because `hy` puts `y` on the hyperplane and `ψ` lands in the half-space.
    intro z
    by_cases hzK : z ∈ K
    · have hcoord : 0 ≤ (psiVa ψ y τ z) 0 :=
        psiVa_coord_nonneg ψ hbd hyψ hy hτ.le (hKsub hzK)
      have hmem := (bcu_profile2_properties n).1 0 (psiVa ψ y τ z) (χ z)
        (by simp) hcoord (hχ01 z).1 (hχ01 z).2
      simpa [psiPhi] using hmem
    · rw [psiPhi_eq_northPole ψ y τ χ z (hout z hzK)]
      exact BCU.bcu_northPole_mem n

end Work.ThomBordism.LeadChapter
