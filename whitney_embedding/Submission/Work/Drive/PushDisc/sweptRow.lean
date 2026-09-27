import Mathlib
import Submission.Work.Drive.PushDisc.asymChart

/-!
# The swept row of `AsymChartData`, and the isolation of a compact anchor

This file contains the two bookkeeping bricks of the lead's design audit (2026-09-25, 10:10):

* `Work.Drive.PushDisc.hswept_of_hnear_hiso` — the **bridge**: the discarded quantitative rows
  (`hnear`: the pushed values are within `δ` of `f (K₁ ∪ K₂)`; `hiso`: everything within `δ` of
  `f (K₁ ∪ K₂)` lies in the two tubes) imply the new row `hswept` of
  `Work.Drive.PushDisc.AsymChartData`.

* `Work.Drive.PushDisc.isolation_of_compact_anchor` — the **isolation criterion**: if `f : M → E` is
  continuous on a compact `M`, `V ⊆ M` is open, `A ⊆ E` is compact and *no* point of `M` outside `V`
  maps into `A`, then there is `δ > 0` such that every point whose image is within `δ` of `A` already
  lies in `V`.  This is the tool that converts the *combinatorial* statement "the preimage of the
  moved locus is contained in `U₁ ∪ W₀`" (produced from the Whitney disc through the general
  position of `Work.Drive.PushDisc.exists_whitneyDisc`) into the quantitative row consumed by the
  collision argument.  Proof: `f '' Vᶜ` is compact (as `V` is open in the compact `M`), hence closed
  and disjoint from `A`; the minimum over `A` of `infDist (f ·) (f '' Vᶜ)` is positive.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set

/-- **The bridge from the quantitative rows to the swept row.**  If the pushed values of the moved
points are within `δ` of the image of the compact anchor `K₁ ∪ K₂` (`hnear`), and every point of `M`
whose image is within `δ` of that anchor lies in `U₁ ∪ W₀` (`hiso`), then every preimage of a moved
value already lies in `U₁ ∪ W₀` (`hswept`). -/
theorem hswept_of_hnear_hiso {k : ℕ} {M : Type*} [TopologicalSpace M]
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (K₁ K₂ U₁ W₀ : Set M) (δ : ℝ) (h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k))
    (X' : ℝ) (m l : ℝ → ℝ)
    (hnear : ∀ p ∈ asymReg k X', 2 * m p.1 * l (‖p.2‖ ^ 2) ≠ 0 →
      ∃ y : M, y ∈ K₁ ∪ K₂ ∧
        dist (Θ (p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (h p).2, p.2)) (f y) < δ)
    (hiso : ∀ x : M, (∃ y : M, y ∈ K₁ ∪ K₂ ∧ dist (f x) (f y) < δ) → x ∈ U₁ ∪ W₀) :
    ∀ p ∈ asymReg k X', 2 * m p.1 * l (‖p.2‖ ^ 2) ≠ 0 → ∀ z : M,
      f z = Θ (p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (h p).2, p.2) → z ∈ U₁ ∪ W₀ := by
  intro p hpreg hne z hz
  obtain ⟨y, hy, hyd⟩ := hnear p hpreg hne
  exact hiso z ⟨y, hy, by rw [hz]; exact hyd⟩

/-- **Isolation of a compact anchor.**  Let `f : M → E` be continuous on a compact Hausdorff `M`,
let `V ⊆ M` be open, and let `A ⊆ E` be compact, with the *combinatorial* hypothesis that no point
of `M` outside `V` maps into `A`.  Then the image of any point within `δ` of `A` (for some `δ > 0`)
already lies in `V`.

This is the quantitative form of the containment `f ⁻¹' A ⊆ V`. -/
theorem isolation_of_compact_anchor {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    {E : Type*} [PseudoMetricSpace E] [T2Space E]
    (f : M → E) (hf : Continuous f) (V : Set M) (hV : IsOpen V)
    (A : Set E) (hAc : IsCompact A)
    (hAV : ∀ z : M, f z ∈ A → z ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : M, ∀ a ∈ A, dist (f z) a < δ → z ∈ V := by
  classical
  by_cases hVc : (Vᶜ : Set M).Nonempty
  · by_cases hAne : A.Nonempty
    · have hKc : IsCompact (f '' Vᶜ) := hV.isClosed_compl.isCompact.image hf
      have hKne : (f '' Vᶜ).Nonempty := hVc.image f
      have hdisj : Disjoint A (f '' Vᶜ) := by
        rw [Set.disjoint_left]
        rintro y hyA ⟨z, hz, hzy⟩
        exact hz (hAV z (hzy ▸ hyA))
      have hcont : Continuous fun a : E => Metric.infDist a (f '' Vᶜ) :=
        Metric.continuous_infDist_pt _
      obtain ⟨a₀, ha₀A, hmin⟩ := hAc.exists_isMinOn hAne hcont.continuousOn
      have hpos : 0 < Metric.infDist a₀ (f '' Vᶜ) :=
        (hKc.isClosed.notMem_iff_infDist_pos hKne).mp (fun hmem => hdisj.le_bot ⟨ha₀A, hmem⟩)
      refine ⟨Metric.infDist a₀ (f '' Vᶜ), hpos, ?_⟩
      intro z a ha hlt
      by_contra hzV
      have hzK : f z ∈ f '' Vᶜ := ⟨z, by simpa using hzV, rfl⟩
      have h1 : Metric.infDist a₀ (f '' Vᶜ) ≤ Metric.infDist a (f '' Vᶜ) := hmin ha
      have h2 : Metric.infDist a (f '' Vᶜ) ≤ dist a (f z) :=
        Metric.infDist_le_dist_of_mem hzK
      have h3 : dist a (f z) = dist (f z) a := dist_comm _ _
      linarith
    · exact ⟨1, one_pos, fun z a ha _ => absurd ⟨a, ha⟩ hAne⟩
  · exact ⟨1, one_pos, fun z a ha _ => by
      by_contra hz
      exact hVc ⟨z, by simpa using hz⟩⟩

end Work.Drive.PushDisc
