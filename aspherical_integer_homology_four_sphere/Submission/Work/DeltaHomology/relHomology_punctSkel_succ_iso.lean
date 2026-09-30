import Mathlib
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.isIso_relHomologyMap_of_deformationRetract
import Submission.Work.DeltaHomology.exists_deformationRetract_punctSkel
import Submission.Work.Homology.Basic
import Submission.Work.DeltaHomology.relHomology_skel_succ_excision
import Submission.Work.DeltaHomology.relHomology_cell_splitting
import Submission.Work.DeltaHomology.cell_relHomology_iso

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

/-! ## Two categorical bookkeeping lemmas

These assemble the relative homology `H_m(X^{k+1}, punctSkel (k+1))` out of the splitting over
the open `(k+1)`-cells: the first says that a coproduct of zero objects is zero, the second
distributes the `if` on the degree `m = k+1` over a coproduct. -/

/-- **A coproduct of zero objects is a zero object.**  If every `f i` is a zero object then so is
`∐ f`: the identity of the coproduct has zero components, hence is `0`. -/
theorem isZero_coproduct_of_forall {C : Type*} [Category C] [HasZeroMorphisms C] {ι : Type*}
    {f : ι → C} [HasCoproduct f] (h : ∀ i, IsZero (f i)) : IsZero (∐ f) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sigma.hom_ext
  intro b
  rw [Category.comp_id, comp_zero]
  exact (h b).eq_zero_of_src _

/-- **Distribution of the degree condition over a coproduct.**  In degree `m = k+1` a coproduct of
`ℤ`'s is the coproduct of the constant family, and in the other degrees it is a coproduct of zero
modules, hence (by `isZero_coproduct_of_forall`) the zero module. -/
theorem coproduct_ite_iso (N k m : ℕ) :
    Nonempty ((∐ fun _ : Fin N =>
        (if m = k + 1 then Work.Homology.ZMod else ModuleCat.of ℤ PUnit)) ≅
      (if m = k + 1 then (∐ fun _ : Fin N => Work.Homology.ZMod)
        else ModuleCat.of ℤ PUnit)) := by
  by_cases hm : m = k + 1
  · have h1 : (fun _ : Fin N =>
          (if m = k + 1 then Work.Homology.ZMod else ModuleCat.of ℤ PUnit))
        = fun _ => Work.Homology.ZMod := by
      funext i; rw [if_pos hm]
    have h2 : (if m = k + 1 then (∐ fun _ : Fin N => Work.Homology.ZMod)
          else ModuleCat.of ℤ PUnit) = (∐ fun _ : Fin N => Work.Homology.ZMod) := by
      rw [if_pos hm]
    rw [h1, h2]
    exact ⟨Iso.refl _⟩
  · have h1 : (fun _ : Fin N =>
          (if m = k + 1 then Work.Homology.ZMod else ModuleCat.of ℤ PUnit))
        = fun _ => ModuleCat.of ℤ PUnit := by
      funext i; rw [if_neg hm]
    have h2 : (if m = k + 1 then (∐ fun _ : Fin N => Work.Homology.ZMod)
          else ModuleCat.of ℤ PUnit) = ModuleCat.of ℤ PUnit := by
      rw [if_neg hm]
    rw [h1, h2]
    exact ⟨(isZero_coproduct_of_forall (f := fun _ : Fin N => ModuleCat.of ℤ PUnit)
      (fun _ => ModuleCat.isZero_of_iff_subsingleton.mpr inferInstance)).iso
        (ModuleCat.isZero_of_iff_subsingleton.mpr inferInstance)⟩

namespace Work.DeltaHomology

/-- **The relative homology `H_m(X^{k+1}, punctSkel (k+1))` is free on the `(k+1)`-simplices in
degree `k+1` and vanishes otherwise.**  This is the assembled form of (V_k) of the skeleta
induction of Hatcher's theorem: it combines

* the good pair `H_m(X^{k+1}, X^k) ≅ H_m(X^{k+1}, punctSkel (k+1))`
  (`relHomology_skel_succ_goodPair`, with the deformation retract
  `exists_deformationRetract_punctSkel`),
* the excision `H_m(X^{k+1} ∖ X^k, ·) ≅ H_m(X^{k+1}, punctSkel (k+1))`
  (`relHomology_skel_succ_excision`, in
  `Submission.Work.DeltaHomology.relHomology_skel_succ_excision` — import it),
* the clopen splitting over the open `(k+1)`-cells (`relHomology_cell_splitting`), and
* the per-cell computation `H_m(cell, cell ∖ {b}) ≅ ℤ` in degree `m = k+1` and `0` otherwise
  (`cell_relHomology_iso`).

Every ingredient is `Nonempty (… ≅ …)`; the statement below is the composite isomorphism.
The `biproduct`-vs-`coproduct` bookkeeping can use `biproduct.isoCoproduct`; the fixed finite
index type is `Fin (K.card (k+1))`, the target of the coproduct in the statement.  For the
`m ≠ k+1` branch one also needs that a coproduct of zero modules is zero. -/
theorem relHomology_punctSkel_succ_iso {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k m : ℕ) :
    Nonempty (relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
        {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
          (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} ≅
      (if m = k + 1 then (∐ fun _ : Fin (K.card (k + 1)) => ZMod)
        else ModuleCat.of ℤ PUnit)) := by
  -- The group computed is `H_m(X^{k+1}, punctSkel (k+1))`, which by the collar
  -- (`exists_deformationRetract_punctSkel`) and the good pair
  -- (`relHomology_skel_succ_goodPair`) is also `H_m(X^{k+1}, X^k)`; the computation itself
  -- starts from the punctured pair.
  -- excision of the `k`-skeleton
  obtain ⟨e₂⟩ := relHomology_skel_succ_excision R k m
  -- the clopen splitting over the open `(k+1)`-cells
  obtain ⟨e₃⟩ := relHomology_cell_splitting R k m
  -- the per-cell computation, transported from the closed cell to the open cell
  have hcell : ∀ σ : Fin (K.card (k + 1)),
      Nonempty (relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.intCell (k + 1) σ))
          {x : ↥(R.toDeltaSimplexMap.intCell (k + 1) σ) |
            (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter (k + 1) σ} ≅
        (if m = k + 1 then ZMod else ModuleCat.of ℤ PUnit)) := by
    intro σ
    obtain ⟨a⟩ := relHomology_cell_intCell_iso R (k + 1) m σ
    obtain ⟨b⟩ := cell_relHomology_iso R (k + 1) σ m
    exact ⟨a.symm ≪≫ b⟩
  -- assemble, and distribute the degree condition over the coproduct
  exact ⟨(e₂ ≪≫ e₃ ≪≫ Sigma.mapIso (fun σ => (hcell σ).some)) ≪≫
    (coproduct_ite_iso (K.card (k + 1)) k m).some⟩

end Work.DeltaHomology

/-! ## The same lemma under its flat name

The statement above is registered in the namespace `Work.DeltaHomology.Work.DeltaHomology` (the
file carries two identical `namespace Work.DeltaHomology` lines, as it was delivered).  The
statement below is the *same* lemma, restated in the namespace `Work.DeltaHomology`, which is
the name under which the rest of the project refers to it
(`Work.DeltaHomology.relHomology_punctSkel_succ_iso`). -/
theorem relHomology_punctSkel_succ_iso {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (k m : ℕ) :
    Nonempty (relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.skelSet (k + 1)))
        {x : ↥(R.toDeltaSimplexMap.skelSet (k + 1)) |
          (x : X) ∈ R.toDeltaSimplexMap.punctSkel (k + 1)} ≅
      (if m = k + 1 then (∐ fun _ : Fin (K.card (k + 1)) => ZMod)
        else ModuleCat.of ℤ PUnit)) :=
  _root_.Work.DeltaHomology.Work.DeltaHomology.relHomology_punctSkel_succ_iso R k m

end Work.DeltaHomology
