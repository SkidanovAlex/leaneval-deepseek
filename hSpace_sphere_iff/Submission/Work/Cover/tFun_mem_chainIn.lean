import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Cover

namespace Work.Cover

open CategoryTheory Simplicial Opposite

open Submission.Cohomology

/-- Pushing the singular chain associated with a chain of pieces of `Δ^N` forward along the map
of a simplex `σ : Δ^N → X` stays in the chains lying in any set containing the image of `σ`:
every simplex in the pushforward is the composite of `σ` with an affine simplex of `Δ^N`. -/
lemma pushChain_toSingChain_mem_chainIn {X : TopCat.{0}} {W : Set X} {N m : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋N⦌))
    (hσ : ∀ t, (TopCat.toSSetObjEquivT X (op ⦋N⦌)) σ t ∈ W)
    (z : Submission.Cohomology.Piece N m →₀ ℚ) :
    Submission.Cohomology.pushChain (Submission.Cohomology.homOfSimplex σ) m
        (Submission.Cohomology.toSingChain z) ∈ Submission.Cohomology.chainIn X W m := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [Submission.Cohomology.toSingChain_add, map_add]
      exact Submodule.add_mem _ hx hy
  | single q r =>
      rw [Submission.Cohomology.toSingChain_single, map_smul,
        Submission.Cohomology.pushChain_single]
      refine Submodule.smul_mem _ _ ?_
      refine Submission.Cohomology.single_mem_chainIn _ ?_
      intro t
      rw [Submission.Cohomology.pushSimplex_apply, ContinuousMap.comp_apply,
        Submission.Cohomology.toSSetObjEquivT_simplexOfPiece,
        Submission.Cohomology.homOfSimplex_apply]
      exact hσ _

theorem tFun_mem_chainIn (X : TopCat.{0}) (W : Set X) (n : ℕ) :
    (Submission.Cohomology.chainIn X W n).map (Submission.Cohomology.tFun X n)
      ≤ Submission.Cohomology.chainIn X W (n+1) := by
  rw [Submission.Cohomology.chainIn, Submodule.map_span]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨σ, hσ, rfl⟩ := hc
  rw [Submission.Cohomology.tFun_single, one_smul]
  exact pushChain_toSingChain_mem_chainIn σ hσ (Submission.Cohomology.TPieces n)

end Work.Cover
