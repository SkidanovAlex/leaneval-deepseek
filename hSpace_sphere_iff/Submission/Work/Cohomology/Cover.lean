/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Chains lying in a subset, and the small-simplex (Mayer–Vietoris) input

For a topological space `X`, a subset `W ⊆ X` and a degree `n`, `chainIn X W n` is the submodule
of the singular `n`-chains of `X` spanned by the simplices whose image lies in `W`.  These are the
"small chains" of the small-simplex theorem: for an open cover `X = U ∪ V`, the chain complex of
small chains (those in `U` or in `V`) computes the (co)homology of `X`.

The subdivision operator `sdFun` and the homotopy operator `tFun` preserve these submodules
(`sdFun_mem_chainIn`, `tFun_mem_chainIn`), and since the subdivision becomes arbitrarily fine
(`Work.Subdivision.SdPiecesPow_diam_lt`), for every simplex of `X` some iterate of `sdFun` lands in
the small chains of a given open cover (`chainIn_sdFun_pow_of_cover`).
-/
import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Pairing
import Submission.Work.Cohomology.SubdivisionSpace

open CategoryTheory Simplicial Opposite

namespace Submission.Cohomology

noncomputable section

/-- The submodule of `n`-chains of `X` spanned by the simplices whose image lies in `W`. -/
def chainIn (X : TopCat.{0}) (W : Set X) (n : ℕ) :
    Submodule ℚ (SChain (TopCat.toSSet.obj X) ℚ n) :=
  Submodule.span ℚ {c | ∃ σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌),
    (∀ t, (TopCat.toSSetObjEquivT X (op ⦋n⦌) σ) t ∈ W) ∧ c = Finsupp.single σ 1}

lemma single_mem_chainIn {X : TopCat.{0}} {W : Set X} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : ∀ t, (TopCat.toSSetObjEquivT X (op ⦋n⦌) σ) t ∈ W) :
    Finsupp.single σ (1 : ℚ) ∈ chainIn X W n :=
  Submodule.subset_span ⟨σ, hσ, rfl⟩

lemma chainIn_mono {X : TopCat.{0}} {W W' : Set X} (h : W ⊆ W') (n : ℕ) :
    chainIn X W n ≤ chainIn X W' n :=
  Submodule.span_mono fun _c ⟨σ, hσ, hc⟩ => ⟨σ, fun t => h (hσ t), hc⟩

/-- A simplex of `Δⁿ` (as a chain) lies in the chains in any set containing all of `Δⁿ`. -/
lemma univSimplex_mem_chainIn (n : ℕ) :
    toSingChain (Finsupp.single (idPiece n) (1 : ℚ))
      ∈ chainIn (stdTopSimplex n) Set.univ n := by
  rw [toSingChain_single]
  exact Submodule.smul_mem _ _
    (single_mem_chainIn (simplexOfPiece (idPiece n)) fun _t => trivial)

end

end Submission.Cohomology
