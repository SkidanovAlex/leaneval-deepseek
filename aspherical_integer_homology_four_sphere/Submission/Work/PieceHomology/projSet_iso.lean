import Mathlib
import Submission.Work.PieceHomology.CircCover
import Submission.Work.Homology.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The projection `X × W → X` is a homology isomorphism for contractible `W`

For a subset `W ⊆ Circ` (the circle `ℝ/ℤ`) which is contractible and nonempty (`w : W`),
the projection `projSet X W : X × W → X` is a homotopy equivalence — its homotopy inverse is
the section `sectSet X W w : X → X × W` at the point `w` — and hence induces an isomorphism
on singular homology in every degree.  The main statement `projSet_iso` packages the
isomorphism together with the identification of its forward map with
`singHomologyMap ZMod k (projSet X W)`.

The homotopy `projSet ≫ sectSet ~ 𝟙` is obtained from a homotopy
`const w ~ id` on `W` (`ContinuousMap.homotopic_const_iff` together with the
nullhomotopy of the identity furnished by `ContractibleSpace`), transported to
`X × W` coordinatewise.
-/

open ContinuousMap CategoryTheory
open scoped unitInterval

namespace Work.PieceHomology

/-- The composite `projSet ≫ sectSet` is homotopic to the identity of `X × W`. -/
private lemma projSet_sectSet_homotopic (X : Type) [TopologicalSpace X] (W : Set Circ) (w : W)
    (hW : ContractibleSpace ↥W) :
    Nonempty (TopCat.Homotopy (projSet X W ≫ sectSet X W w)
      (𝟙 (TopCat.of ↥{p : X × Circ | p.2 ∈ W}))) := by
  have : ContractibleSpace ↥W := hW
  -- A homotopy `const w ~ id` on `W`, from the nullhomotopy of the identity and
  -- path-connectedness of `W`.
  obtain ⟨y₀, hy₀⟩ := id_nullhomotopic ↥W
  have hJ : (ContinuousMap.const ↥W w).Homotopic (ContinuousMap.id ↥W) :=
    (ContinuousMap.homotopic_const_iff.mpr (PathConnectedSpace.joined w y₀)).trans hy₀.symm
  obtain ⟨J⟩ := hJ
  let A := ↥{p : X × Circ | p.2 ∈ W}
  -- The first coordinate of the homotopy: the projection to `X`.
  let pX : C(I × A, X) := (projSet X W).hom.comp ContinuousMap.snd
  -- The canonical map to `W` given by the second coordinate.
  let aW : C(A, ↥W) :=
    ⟨fun a => ⟨a.val.2, a.property⟩,
      (continuous_snd.comp continuous_subtype_val).subtype_mk (fun a => a.property)⟩
  -- The `W`-coordinate of the homotopy.
  let jj : C(I × A, ↥W) :=
    J.toContinuousMap.comp (ContinuousMap.fst.prodMk (aW.comp ContinuousMap.snd))
  let hh : C(I × A, X × ↥W) := pX.prodMk jj
  -- Reassembly into `X × W ⊆ X × Circ`.
  let toA : C(X × ↥W, A) :=
    ⟨fun z => ⟨(z.1, ↑z.2), z.2.property⟩,
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk
        (fun z => z.2.property)⟩
  refine ⟨⟨toA.comp hh, ?_, ?_⟩⟩
  · intro a
    change ↑(toA (hh (0, a))) =
      ↑((TopCat.Hom.hom (sectSet X W w)) ((TopCat.Hom.hom (projSet X W)) a))
    simp only [hh, pX, jj, aW, toA, ContinuousMap.prod_eval, ContinuousMap.comp_apply,
      ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.apply_zero,
      ContinuousMap.const_apply, ContinuousMap.coe_mk, ContinuousMap.fst_apply,
      ContinuousMap.snd_apply]
    apply Subtype.ext
    rfl
  · intro a
    change ↑(toA (hh (1, a))) = ↑a
    simp only [hh, pX, jj, aW, toA, ContinuousMap.prod_eval, ContinuousMap.comp_apply,
      ContinuousMap.Homotopy.coe_toContinuousMap, ContinuousMap.Homotopy.apply_one,
      ContinuousMap.coe_mk, ContinuousMap.fst_apply, ContinuousMap.snd_apply]
    apply Subtype.ext
    rfl

/-- **The projection `X × W → X` is a homotopy equivalence** whenever `W` is contractible
and nonempty (`w : W`). -/
private lemma projSet_isHomotopyEquivalence (X : Type) [TopologicalSpace X] (W : Set Circ) (w : W)
    (hW : ContractibleSpace ↥W) :
    Work.Homology.IsHomotopyEquivalence (projSet X W) := by
  refine ⟨sectSet X W w, ?_, ?_⟩
  · exact projSet_sectSet_homotopic X W w hW
  · rw [projSet_sectSet X W w]
    exact ⟨TopCat.Homotopy.refl (𝟙 (TopCat.of X))⟩

theorem projSet_iso (X : Type) [TopologicalSpace X] (W : Set Work.PieceHomology.Circ)
    (w : W) (hW : ContractibleSpace ↥W) (k : ℕ) :
    ∃ e : Work.Homology.singHomology Work.Homology.ZMod k
        (TopCat.of ↥{p : X × Work.PieceHomology.Circ | p.2 ∈ W})
      ≅ Work.Homology.singHomology Work.Homology.ZMod k (TopCat.of X),
      e.hom = Work.Homology.singHomologyMap Work.Homology.ZMod k
        (Work.PieceHomology.projSet X W) := by
  have h1 : Nonempty (TopCat.Homotopy (projSet X W ≫ sectSet X W w)
      (𝟙 (TopCat.of ↥{p : X × Circ | p.2 ∈ W}))) := projSet_sectSet_homotopic X W w hW
  have h2 : Nonempty (TopCat.Homotopy (sectSet X W w ≫ projSet X W)
      (𝟙 (TopCat.of X))) := by
    rw [projSet_sectSet X W w]
    exact ⟨TopCat.Homotopy.refl (𝟙 (TopCat.of X))⟩
  refine ⟨{ hom := Work.Homology.singHomologyMap Work.Homology.ZMod k (projSet X W)
            inv := Work.Homology.singHomologyMap Work.Homology.ZMod k (sectSet X W w)
            hom_inv_id := ?_
            inv_hom_id := ?_ }, rfl⟩
  · rw [← Work.Homology.singHomologyMap_comp Work.Homology.ZMod k (projSet X W) (sectSet X W w),
      Work.Homology.singHomologyMap_congr Work.Homology.ZMod k h1.some,
      Work.Homology.singHomologyMap_id]
  · rw [← Work.Homology.singHomologyMap_comp Work.Homology.ZMod k (sectSet X W w) (projSet X W),
      Work.Homology.singHomologyMap_congr Work.Homology.ZMod k h2.some,
      Work.Homology.singHomologyMap_id]

end Work.PieceHomology
