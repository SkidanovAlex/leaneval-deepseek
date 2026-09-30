import Mathlib
import ChallengeDeps
import Submission.Work.DeltaHomology.PunctSkelBasic
import Submission.Work.DeltaHomology.isQuotientMap_punctToPiece
import Submission.Work.DeltaHomology.isClosed_skelSet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Continuity of the radial homotopy of the collar

The radial homotopy `homotopyFun R k` of the collar `χ.punctSkel (k+1)` of the `k`-skeleton
(`Submission/Work/DeltaHomology/PunctSkelBasic.lean`) is continuous.  It is glued from the
identity on the `k`-skeleton and the collar flow `χ (k+1) τ (collarMap (k+1) ·)` on the piece
carried by each `(k+1)`-simplex; the latter descends through the quotient map
`punctToPiece R k τ` of the punctured standard simplex onto its image
(`Submission/Work/DeltaHomology/isQuotientMap_punctToPiece.lean`), which is legitimate because
the fibers of the characteristic map on punctured simplices are contracted by the collar — that
is the content of `DeltaRealization.cls_collarMap_eq_of_cls_eq`.
-/

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped unitInterval

namespace Work.DeltaHomology

noncomputable section

attribute [local instance] Classical.propDecidable

variable {K : DeltaCx} {X : TopCat}

/-- Continuity of a two-variable function on `univ ×ˢ s`, from continuity of its restriction to
`α × ↥s`. -/
theorem continuousOn_prod_univ {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] (s : Set β) (f : α × β → γ)
    (h : Continuous fun p : α × ↥s => f (p.1, (p.2 : β))) :
    ContinuousOn f ((Set.univ : Set α) ×ˢ s) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hproj : Continuous (fun p : ↥((Set.univ : Set α) ×ˢ s) =>
      (((p : α × β).1, (⟨(p : α × β).2, (Set.mem_prod.mp p.2).2⟩ : ↥s)) : α × ↥s)) :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      (Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val)
        (fun p => (Set.mem_prod.mp p.2).2))
  exact Continuous.comp (Y := α × ↥s) h hproj

/-- The collar flow on a punctured `(k+1)`-simplex: the characteristic map of `τ` applied to
the collar trajectory of a point of the punctured standard simplex. -/
def collarFlow (R : DeltaRealization K X) (k : ℕ) (τ : Fin (K.card (k + 1))) :
    I × ↥(punctStdSimplex (k + 1)) → ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) :=
  fun p => ⟨R.toDeltaSimplexMap.cls (k + 1) τ (collarMap (k + 1) p),
    R.cls_mem_punctSkel (k + 1) τ (collarMap (k + 1) p).2⟩

theorem continuous_collarFlow (R : DeltaRealization K X) (k : ℕ) (τ : Fin (K.card (k + 1))) :
    Continuous (collarFlow R k τ) := by
  apply Continuous.subtype_mk
  have h1 : Continuous fun p : I × ↥(punctStdSimplex (k + 1)) =>
      ((collarMap (k + 1) p : ↥(punctStdSimplex (k + 1))) : StdSimplex ℝ (Fin (k + 2))) :=
    continuous_subtype_val.comp (collarMap (k + 1)).continuous
  exact (R.toDeltaSimplexMap.cls (k + 1) τ).continuous.comp h1

/-- On a punctured cell, the value of the radial homotopy is the collar flow. -/
theorem homotopyVal_of_piece (R : DeltaRealization K X) (k : ℕ) (τ : Fin (K.card (k + 1)))
    (t : I) (y : ↥(punctStdSimplex (k + 1))) :
    homotopyVal R k (t, punctToPiece R k τ y) =
      R.toDeltaSimplexMap.cls (k + 1) τ (collarMap (k + 1) (t, y)) := by
  rw [homotopyVal_apply]
  exact homotopyPt_of_cls R k t τ y

theorem homotopyFun_of_piece (R : DeltaRealization K X) (k : ℕ) (τ : Fin (K.card (k + 1)))
    (t : I) (y : ↥(punctStdSimplex (k + 1))) :
    homotopyFun R k (t, punctToPiece R k τ y) = collarFlow R k τ (t, y) :=
  Subtype.ext (homotopyVal_of_piece R k τ t y)

/-- The homotopy is continuous on the piece of the collar carried by a `(k+1)`-simplex. -/
theorem continuousOn_homotopyFun_piece (R : DeltaRealization K X) (k : ℕ)
    (τ : Fin (K.card (k + 1))) :
    ContinuousOn (homotopyFun R k) (Set.univ ×ˢ collarPiece R k τ) := by
  have hq := isQuotientMap_punctToPiece R k τ
  have hcomp : Continuous (fun p : I × ↥(punctStdSimplex (k + 1)) =>
      homotopyFun R k (p.1, punctToPiece R k τ p.2)) := by
    have heq : (fun p : I × ↥(punctStdSimplex (k + 1)) =>
        homotopyFun R k (p.1, punctToPiece R k τ p.2)) = collarFlow R k τ := by
      funext p
      exact homotopyFun_of_piece R k τ p.1 p.2
    rw [heq]
    exact continuous_collarFlow R k τ
  have hmain : Continuous (fun q : I × ↥(collarPiece R k τ) =>
      homotopyFun R k (q.1, q.2)) :=
    hq.continuous_lift_prod_right hcomp
  exact continuousOn_prod_univ (collarPiece R k τ) (homotopyFun R k) hmain

/-- The homotopy is continuous on the `k`-skeleton, where it is the identity. -/
theorem continuousOn_homotopyFun_skel (R : DeltaRealization K X) (k : ℕ) :
    ContinuousOn (homotopyFun R k)
      (Set.univ ×ˢ {z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) |
        (z : X) ∈ R.toDeltaSimplexMap.skelSet k}) := by
  refine (continuous_snd.continuousOn).congr ?_
  intro p hp
  exact homotopyFun_fixes R k p.1 hp.2

/-- The `k`-skeleton, viewed inside the collar, is a closed subset. -/
theorem isClosed_skelPiece (R : DeltaRealization K X) (k : ℕ) :
    IsClosed ({z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) |
      (z : X) ∈ R.toDeltaSimplexMap.skelSet k}) :=
  IsClosed.preimage continuous_subtype_val (isClosed_skelSet R k)

/-- The piece of the collar carried by a `(k+1)`-simplex is a closed subset. -/
theorem isClosed_collarPiece (R : DeltaRealization K X) (k : ℕ) (τ : Fin (K.card (k + 1))) :
    IsClosed (collarPiece R k τ) := by
  have hc : IsClosed (Set.range (R.toDeltaSimplexMap.cls (k + 1) τ)) := by
    letI : T2Space X := R.t2
    exact (isCompact_range (R.toDeltaSimplexMap.cls (k + 1) τ).continuous).isClosed
  exact IsClosed.preimage continuous_subtype_val hc

/-- Every point of the collar lies in the `k`-skeleton or in the piece carried by some
`(k+1)`-simplex. -/
theorem mem_skelPiece_or_mem_collarPiece (R : DeltaRealization K X) (k : ℕ)
    (z : ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) :
    (z : X) ∈ R.toDeltaSimplexMap.skelSet k ∨ ∃ τ, z ∈ collarPiece R k τ := by
  rcases DeltaSimplexMap.punctSkel_succ_subset R.toDeltaSimplexMap k z.2 with h | h
  · exact Or.inl h
  · rcases Set.mem_iUnion.mp h with ⟨τ, y, hy⟩
    exact Or.inr ⟨τ, ⟨y, hy⟩⟩

/-- **Continuity of the radial homotopy of the collar.** -/
theorem continuous_homotopyFun (R : DeltaRealization K X) (k : ℕ) :
    Continuous (homotopyFun R k) := by
  let A : Set ↥(R.toDeltaSimplexMap.punctSkel (k + 1)) :=
    {z | (z : X) ∈ R.toDeltaSimplexMap.skelSet k}
  let F : Option (Fin (K.card (k + 1))) →
      Set (I × ↥(R.toDeltaSimplexMap.punctSkel (k + 1))) :=
    fun i => match i with
      | none => Set.univ ×ˢ A
      | some τ => Set.univ ×ˢ collarPiece R k τ
  have hcov : ⋃ i, F i = Set.univ := by
    ext p
    constructor
    · intro _; exact trivial
    · intro _
      rw [Set.iUnion_option]
      rcases mem_skelPiece_or_mem_collarPiece R k p.2 with h | ⟨τ, hτ⟩
      · exact Or.inl ⟨trivial, h⟩
      · exact Or.inr (Set.mem_iUnion.mpr ⟨τ, ⟨trivial, hτ⟩⟩)
  refine LocallyFinite.continuous (locallyFinite_of_finite F) hcov ?_ ?_
  · rintro (_ | τ)
    · exact isClosed_univ.prod (isClosed_skelPiece R k)
    · exact isClosed_univ.prod (isClosed_collarPiece R k τ)
  · rintro (_ | τ)
    · exact continuousOn_homotopyFun_skel R k
    · exact continuousOn_homotopyFun_piece R k τ

end

end Work.DeltaHomology
