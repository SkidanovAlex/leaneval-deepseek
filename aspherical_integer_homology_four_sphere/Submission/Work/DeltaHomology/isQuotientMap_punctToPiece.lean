import Mathlib
import Submission.Work.DeltaHomology.PunctSkelBasic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology Work.DeltaHomology
open scoped Simplicial unitInterval

/-- **The punctured cell is a quotient of the punctured standard simplex.**  The characteristic
map of a `(k+1)`-simplex `τ` of a realization, restricted to the punctured standard simplex
`Δ^{k+1} ∖ {barycentre}` and corestricted to the piece `collarPiece R k τ` of the collar of the
`(k+1)`-skeleton that it carries, is a quotient map.  Equivalently: a subset of that piece is
open as soon as its preimage in the punctured simplex is open, i.e. the piece carries the
quotient topology of the characteristic map.

Route.  Let `f := (χ (k+1) τ)` corestricted to `↥(Set.range (χ (k+1) τ))`; it is surjective by
definition and continuous, and the source `StdSimplex ℝ (Fin (k+2))` is compact while the target
(a subspace of the Hausdorff space `X`) is Hausdorff, so `IsQuotientMap.of_surjective_continuous`
gives that `f` is a quotient map.  The set
`s := {z : ↥(Set.range (χ (k+1) τ)) | (z : X) ∈ barycenterSet (k+1)}` is finite, hence closed
(Hausdorff), so `IsOpen sᶜ`, and `IsQuotientMap.restrictPreimage_isOpen` gives that
`sᶜ.restrictPreimage f` is a quotient map; its source is `χ (k+1) τ ⁻¹' sᶜ = punctStdSimplex (k+1)`
(by `cls_eq_barycenter_iff`) and its target is the subtype of the punctured cell.  Finally
transport this quotient map to `punctToPiece R k τ` along the "identity on points"
homeomorphisms between the avatars of the piece (`Homeomorph.setCongr` for the source, and a
hand-built `≃ₜ` for the target whose `toFun` is `Subtype.ext`-style), using `IsQuotientMap.comp`
and `Homeomorph.isQuotientMap`. -/
theorem isQuotientMap_punctToPiece {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X) (k : ℕ)
    (τ : Fin (K.card (k + 1))) :
    Topology.IsQuotientMap (punctToPiece R k τ) := by
  classical
  have hT2 : T2Space X := R.t2
  have hC : CompactSpace X := R.compact
  -- The characteristic map `χ (k+1) τ`, its range `A`, the barycentres `B` of the
  -- `(k+1)`-simplices, the corestriction `f` of the characteristic map to its range, and the
  -- set `s` of barycentres inside the range.
  let A : Set X := Set.range (R.toDeltaSimplexMap.cls (k + 1) τ)
  let B : Set X := R.toDeltaSimplexMap.barycenterSet (k + 1)
  let f : StdSimplex ℝ (Fin (k + 1 + 1)) → ↥A :=
    fun y => ⟨R.toDeltaSimplexMap.cls (k + 1) τ y, ⟨y, rfl⟩⟩
  let s : Set ↥A := Subtype.val ⁻¹' B
  -- `f` is a quotient map: compact source, Hausdorff target, surjective and continuous.
  have hfq : Topology.IsQuotientMap f := by
    refine Topology.IsQuotientMap.of_surjective_continuous (fun z => ?_) ?_
    · exact ⟨z.2.choose, Subtype.ext z.2.choose_spec⟩
    · exact Continuous.subtype_mk (R.toDeltaSimplexMap.cls (k + 1) τ).continuous
        (fun y => ⟨y, rfl⟩)
  -- `s` is finite, hence closed, so its complement is open.
  have hs_open : IsOpen sᶜ := by
    have hB : B.Finite := R.toDeltaSimplexMap.barycenterSet_finite (k + 1)
    exact ((hB.isClosed).preimage continuous_subtype_val).isOpen_compl
  -- Restricting to the preimage of an open set preserves quotient maps.
  have hq : Topology.IsQuotientMap ((sᶜ).restrictPreimage f) :=
    hfq.restrictPreimage_isOpen hs_open
  -- The source of the restricted map is the punctured standard simplex.
  have hsrc : punctStdSimplex (k + 1) = f ⁻¹' sᶜ := by
    ext y
    rw [Set.mem_preimage, Set.mem_compl_iff, mem_punctStdSimplex_iff]
    have hiff : f y ∈ s ↔ y = simplexBarycenter (k + 1) :=
      R.cls_eq_barycenter_iff (k + 1) τ y
    rw [hiff]
  let e₁ : ↥(punctStdSimplex (k + 1)) ≃ₜ ↥(f ⁻¹' sᶜ) := Homeomorph.setCongr hsrc
  -- The target of the restricted map is the punctured cell, the avatar of `collarPiece`.
  have hskel : ∀ z : ↥(sᶜ), (z.1.1 : X) ∈ R.toDeltaSimplexMap.skelSet (k + 1) := by
    intro z
    obtain ⟨y, hy⟩ := z.1.2
    rw [← hy]
    exact R.toDeltaSimplexMap.cls_mem_skelSet le_rfl τ y
  have hnotbar : ∀ z : ↥(sᶜ), (z.1.1 : X) ∉ B := fun z => z.2
  let t : ↥(sᶜ) → ↥(collarPiece R k τ) :=
    fun z => ⟨⟨z.1.1, ⟨hskel z, hnotbar z⟩⟩, z.1.2⟩
  let u : ↥(collarPiece R k τ) → ↥(sᶜ) :=
    fun w => ⟨⟨w.1.1, w.2⟩, w.1.2.2⟩
  have hleft : Function.LeftInverse u t := fun z => rfl
  have hright : Function.RightInverse u t := fun w => rfl
  let e₂ : ↥(sᶜ) ≃ₜ ↥(collarPiece R k τ) :=
    { toFun := t
      invFun := u
      left_inv := hleft
      right_inv := hright
      continuous_toFun := by
        have h1 : Continuous (fun z : ↥(sᶜ) => (z.1.1 : X)) :=
          continuous_subtype_val.comp continuous_subtype_val
        have h2 : Continuous (fun z : ↥(sᶜ) =>
            (⟨z.1.1, ⟨hskel z, hnotbar z⟩⟩ : ↥(R.toDeltaSimplexMap.punctSkel (k + 1)))) :=
          Continuous.subtype_mk h1 (fun z => ⟨hskel z, hnotbar z⟩)
        exact Continuous.subtype_mk h2 (fun z => z.1.2)
      continuous_invFun := by
        have h1 : Continuous (fun w : ↥(collarPiece R k τ) => (w.1.1 : X)) :=
          continuous_subtype_val.comp continuous_subtype_val
        have h2 : Continuous (fun w : ↥(collarPiece R k τ) => (⟨w.1.1, w.2⟩ : ↥A)) :=
          Continuous.subtype_mk h1 (fun w => w.2)
        exact Continuous.subtype_mk h2 (fun w => w.1.2.2) }
  -- Transport the quotient map along the two homeomorphisms.
  have hcomp : Topology.IsQuotientMap (e₂ ∘ (sᶜ).restrictPreimage f ∘ e₁) :=
    (Homeomorph.isQuotientMap e₂).comp (hq.comp (Homeomorph.isQuotientMap e₁))
  have heq : punctToPiece R k τ = e₂ ∘ (sᶜ).restrictPreimage f ∘ e₁ := by
    funext y
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [heq]
  exact hcomp

end Work.DeltaHomology
