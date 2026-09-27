import Mathlib
import Submission.Work.Drive.Whitney.whitneyDiscDefs
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Projection.exists_countable_chart_cover_general
import Submission.Work.Projection.Defs
import Submission.Work.Drive.Whitney.badAvoidParam

namespace Work.Drive.Whitney

/-- **Hausdorff-dimension bound for the avoidance-bad parameters.**
(The result should live in namespace `Work.Drive.Whitney`.)

`Work.Drive.Whitney.badAvoid f γ₁ γ₂` (defined in
`Submission.Work.Drive.Whitney.whitneyDiscDefs`) is the set of translation parameters `v` for
which the candidate disc `Work.Drive.Whitney.discMap f γ₁ γ₂ v` meets `f '' M` at a point of the
open square `Work.Drive.Whitney.discSq` (`discMap v p = baseDisc p + ∑ k, discBump k p • v k`).

Proof design: `discBump (0,0)` does not vanish on `discSq`, so a bad `v` with witness `(p, y)` is
recovered from the three other blocks of `v` by solving for the `(0,0)`-block.  Cover `M` by
countably many charts and parametrise `badAvoid` as the countable union over the charts `i` of the
images of the `C^1` maps `(p, u, w) ↦ v` defined on the open subset
`discSq × (chartAt _ (p i)).target × univ` of the space
`(ℝ × ℝ) × EuclideanSpace ℝ (Fin n) × ({k : Fin 2 × Fin 2 // k ≠ (0,0)} → EuclideanSpace ℝ (Fin (2 * n)))`,
whose `finrank` is `2 + n + 3 * (2 * n) = 7 * n + 2`.  `Work.Projection.dimH_image_le_of_contDiffOn`
plus `dimH_iUnion` then gives the bound; the smoothness of `p ↦ baseDisc p` comes from `hf`, `hγ₁`,
`hγ₂`. -/
theorem dimH_badAvoid {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂) :
    dimH (Work.Drive.Whitney.badAvoid f γ₁ γ₂) ≤ ((7 * n + 2 : ℕ) : ENNReal) := by
  rcases isEmpty_or_nonempty M with hMempty | hMne
  · haveI := hMempty
    have hempty : badAvoid f γ₁ γ₂ = ∅ := by
      ext v
      constructor
      · rintro ⟨p, hp, y, -⟩
        exact isEmptyElim y
      · intro hv
        exact absurd hv (Set.notMem_empty v)
    rw [hempty, dimH_empty]
    exact bot_le
  · haveI := hMne
    obtain ⟨p, hp⟩ := Work.Projection.exists_countable_chart_cover_general
      (E := EuclideanSpace ℝ (Fin n)) (H := EuclideanSpace ℝ (Fin n))
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) (M := M)
    have hsub : badAvoid f γ₁ γ₂ ⊆
        ⋃ i, badAvoidParam f γ₁ γ₂ (p i) '' badAvoidDom (p i) :=
      badAvoid_subset_param f γ₁ γ₂ p
        (fun y => Set.mem_iUnion.mp (hp (Set.mem_univ y)))
    calc dimH (Work.Drive.Whitney.badAvoid f γ₁ γ₂)
        ≤ dimH (⋃ i, badAvoidParam f γ₁ γ₂ (p i) '' badAvoidDom (p i)) := dimH_mono hsub
      _ = ⨆ i, dimH (badAvoidParam f γ₁ γ₂ (p i) '' badAvoidDom (p i)) := dimH_iUnion _
      _ ≤ ((7 * n + 2 : ℕ) : ENNReal) := by
          refine iSup_le fun i => ?_
          have h := Work.Projection.dimH_image_le_of_contDiffOn
            (E := discParamSrc n) (F := (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)))
            (U := badAvoidDom (p i)) (isOpen_badAvoidDom (p i))
            (contDiffOn_badAvoidParam f hf γ₁ γ₂ hγ₁ hγ₂ (p i)) (Set.Subset.refl _)
          rwa [finrank_discParamSrc n] at h

end Work.Drive.Whitney
