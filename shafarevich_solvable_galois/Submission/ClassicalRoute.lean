/-
Copyright (c) 2025. All rights reserved.

# The classical route: Ore's reduction from Theorem 14 of Schmidt–Wingberg

`Submission/Shafarevich.lean` proves Shafarevich's theorem from the *minimal* embedding step
`MinimalNormalKernelStep` (a nontrivial minimal normal kernel), which is the weakest statement
sufficient for the induction.  This file records the *classical* route, which is the one followed
in the literature:

> **Theorem 14** (Schmidt–Wingberg, arXiv:math/9809211; Shafarevich 1954).
> Let `L/ℚ` be a finite Galois extension and `N` a finite nilpotent group with an action of
> `Gal(L/ℚ)`.  Then the *split* embedding problem
> `1 → N → N ⋊ Gal(L/ℚ) → Gal(L/ℚ) → 1` over `ℚ` has a **proper solution**.

* `Work.Fitting.SplitEmbeddingSolvable L N φ` is the unfolded, universe-polymorphic form of that
  proper solution (from `Submission/Work/Fitting/`, Ore's group-theoretic reduction);
* `SplitEmbeddingTheoremOverRat` is Theorem 14 over `ℚ`, and
  `realizable_of_solvable_of_split` proves that it implies the target theorem (Ore's argument:
  `G` is a quotient of `F(G) ⋊ U` with `F(G)` the nilpotent Fitting subgroup and `U < G` a proper
  supplement; `U` is realizable by induction and `F(G) ⋊ U` by Theorem 14);
* `minimalNormalKernelStep_of_split` records that the classical input therefore implies the
  minimal input used by `realizable_of_solvable`.

None of this is new mathematics — it is the formalised reduction chain, and it shows that the
single gap of this development (`MinimalNormalKernelStep`, which is *implied* by the target
theorem and hence weaker) is reached from the literature's main embedding theorem.
-/
import Mathlib
import Submission.Shafarevich
import Submission.Combine
import Submission.Work.Fitting.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

universe u

open scoped Classical

/-- **Theorem 14 of Schmidt–Wingberg over `ℚ`**: every split embedding problem over `ℚ` with
finite nilpotent kernel has a proper solution.  This is the classical deep input of Shafarevich's
theorem, stated in the unfolded form `Work.Fitting.SplitEmbeddingSolvable`. -/
def SplitEmbeddingTheoremOverRat : Prop :=
  ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (N : Type) [Group N] [Finite N], Group.IsNilpotent N →
    ∀ φ : (L ≃ₐ[ℚ] L) →* MulAut N, Work.Fitting.SplitEmbeddingSolvable L N φ

/-- **Ore's reduction**: Theorem 14 over `ℚ` implies that every finite solvable group is
realizable over `ℚ`.  (This is `Work.Fitting.realizable_of_solvable_of_split_embedding`, the
group-theoretic argument of Ore: a nontrivial finite solvable group `G` is a quotient of
`F(G) ⋊ U` with `F(G)` the nilpotent Fitting subgroup and `U < G` a proper supplement, `U` is
realizable by induction, and `F(G) ⋊ U` is realizable by Theorem 14.) -/
theorem realizable_of_solvable_of_split (h : SplitEmbeddingTheoremOverRat) :
    ∀ (G : Type) [Group G] [Finite G] [Group.IsSolvable G], RealizableOver ℚ G :=
  fun G _ _ _ =>
    Work.Fitting.realizable_of_solvable_of_split_embedding
      (fun L _ _ N _ _ hN φ => h L N hN φ) G

/-- Theorem 14 over `ℚ` implies the minimal embedding step which `realizable_of_solvable`
takes as its only input. -/
theorem minimalNormalKernelStep_of_split (h : SplitEmbeddingTheoremOverRat) :
    MinimalNormalKernelStep.{0} := by
  refine elementaryAbelianKernelStep_implies_minimalNormal ?_
  intro G _ _ _ A _ hAne p hp hcomm hpow hquot
  exact realizable_of_solvable_of_split h G

end Submission
