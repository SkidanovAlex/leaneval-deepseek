import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.homology_zero_free
import Submission.Work.Cohomology.free_homology_iUnion_of_split
import Submission.Work.Cohomology.free_and_vanishing_ball_compl
import Submission.Work.Cohomology.free_of_iUnion_submodule
import Submission.Work.Cohomology.exists_ball_sequence
import Submission.Work.Cohomology.euclidean_stages_homology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Cohomology

noncomputable section

/-- **The top homology of the complement of a compact set in `ℝ^N` is free** (`N ≥ 2`): for
`C ⊆ ℝ^N` compact, `H_{N-1}(ℝ^N∖C; ℤ)` is a free `ℤ`-module.

The proof runs the classical Alexander-duality argument through the `LocalTopFree` development of
this workspace.  `Work.Cohomology.exists_ball_sequence` produces a decreasing sequence
`T n = ⋃_{j < k n} closedBall (c n j) (r n j)` of finite unions of closed balls with
`T (n+1) ⊆ interior (T n)`, `C ⊆ T n`, every ball meeting `C`, and `⋂ n, T n = C`.  Setting
`V n := (T n)ᶜ` gives an increasing sequence of open sets with `⋃ n, V n = Cᶜ`, and
`Work.Cohomology.euclidean_stages_homology` provides both the freeness of each `H_{N-1}(V n)` and a
splitting of each transition map `H_{N-1}(V n) → H_{N-1}(V (n+1))`.  The freeness of the union
then follows from `Work.Cohomology.free_homology_iUnion_of_split`. -/
theorem euclidean_compl_top_homology_free {N : ℕ} (hN : 2 ≤ N)
    (C : Set (EuclideanSpace ℝ (Fin N))) (hC : IsCompact C) :
    Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥{y : EuclideanSpace ℝ (Fin N) | y ∉ C})).homology (N - 1)) := by
  obtain ⟨T, k, c, r, hr, hT, hmeet, hKsub, htop, hinter⟩ :=
    exists_ball_sequence (N := N) (by omega : 1 ≤ N) C hC
  have hmono : ∀ n, T (n + 1) ⊆ T n := fun n => (htop n).trans interior_subset
  have hTinter : (⋂ n, T n) = C := by
    refine le_antisymm hinter ?_
    intro x hx
    exact Set.mem_iInter.mpr (fun n => hKsub n hx)
  obtain ⟨hfreeT, hsplitT⟩ :=
    euclidean_stages_homology (N := N) (by omega : 1 ≤ N) C T hmono htop hKsub k c r hr hT hmeet
  let V : ℕ → Set (EuclideanSpace ℝ (Fin N)) := fun n => Set.compl (T n)
  have hclosed : ∀ n, IsClosed (T n) := by
    intro n
    rw [hT n]
    exact isClosed_iUnion_of_finite (fun j => Metric.isClosed_closedBall)
  have hopen : ∀ n, IsOpen (V n) := fun n => (hclosed n).isOpen_compl
  have hmonoV : Monotone V :=
    fun a b hab => Set.compl_subset_compl.mpr ((antitone_nat_of_succ_le hmono) hab)
  have hsplit : ∀ n, ∃ σ : ↥((singularChains ℤ (TopCat.of (V (n + 1)))).homology (N - 1)) →ₗ[ℤ]
      ↥((singularChains ℤ (TopCat.of (V n))).homology (N - 1)),
      σ.comp (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ (TopCat.of (V n))
        (TopCat.of (V (n + 1))) (Work.Cohomology.inclSet
          (X := TopCat.of (EuclideanSpace ℝ (Fin N)))
          (A := V n) (B := V (n + 1)) (hmonoV (Nat.le_succ n)))) (N - 1)).hom
        = LinearMap.id := by
    intro n
    obtain ⟨s, hs, -⟩ := hsplitT n
    refine ⟨s, ?_⟩
    have hstep : (Work.Cohomology.inclSet (X := TopCat.of (EuclideanSpace ℝ (Fin N)))
        (A := V n) (B := V (n + 1)) (hmonoV (Nat.le_succ n)))
        = Work.Cohomology.stageIncl T hmono n := by
      unfold Work.Cohomology.stageIncl
      rw [show hmonoV (Nat.le_succ n) = Set.compl_subset_compl.mpr (hmono n) from
        Subsingleton.elim _ _]
    rw [hstep]
    exact hs
  have hmain : Module.Free ℤ
      ↥((Work.Cohomology.singularChains ℤ (TopCat.of (⋃ n, V n))).homology (N - 1)) :=
    free_homology_iUnion_of_split (X := TopCat.of (EuclideanSpace ℝ (Fin N)))
      V hopen hmonoV (N - 1) hfreeT hsplit
  have hUeq : (⋃ n, V n) = {y : EuclideanSpace ℝ (Fin N) | y ∉ C} := by
    have h1 : (⋃ n, V n) = (⋂ n, T n)ᶜ := by
      rw [Set.compl_iInter]
      rfl
    rw [h1, hTinter]
    rfl
  exact moduleFree_homology_of_homeomorph
    (X := TopCat.of ↥{y : EuclideanSpace ℝ (Fin N) | y ∉ C})
    (Y := TopCat.of (⋃ n, V n)) (Homeomorph.setCongr hUeq.symm) (N - 1) hmain

end

end Work.Cohomology
