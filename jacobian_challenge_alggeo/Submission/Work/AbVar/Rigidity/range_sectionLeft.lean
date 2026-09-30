import Mathlib
import Submission.Work.AbVar.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.AbVar.Rigidity

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory

/-- For a `k`-point `y : Point Y`, the graph section `sectionLeft X Y y : X ⟶ X ⊗ Y` has
range exactly the fibre of `snd X Y : X ⊗ Y ⟶ Y` over the point `y(∗)`.  (The statement is
phrased without mentioning the point, as `Set.range y.left`.)

Proof sketch (only the fibre-product API is needed, no hypotheses on `X`, `Y` besides that
they are `k`-schemes):
* `⊆`: `sectionLeft X Y y ≫ snd X Y = toUnit X ≫ y`, so the second coordinate of
  `sectionLeft X Y y x` is the point of `y`.
* `⊇`: the square
  `X --sectionLeft X Y y--> X ⊗ Y`, `X --toUnit X--> 𝟙_`, `𝟙_ --y--> Y`,
  `X ⊗ Y --snd X Y--> Y`
  is a pullback: with `(X ⊗ Y).left = pullback X.hom Y.hom`
  (`CategoryTheory.Over.tensorObj_left`), `(toUnit X).left = X.hom` and
  `(sectionLeft X Y y).left = pullback.lift (𝟙 X.left) (X.hom ≫ y.left)`, one checks
  `IsIso (pullback.lift (sectionLeft X Y y).left (toUnit X).left _)` using
  `AlgebraicGeometry.Scheme.Pullback.range_fst` and the universal property of the product
  (`CategoryTheory.Over.tensorObj_ext`, `pullback.lift_fst`, `pullback.lift_snd`,
  `pullback.condition`, `Work.AbVar.sectionLeft_fst`, `Work.AbVar.sectionLeft_snd`).
  Then `Set.range (sectionLeft X Y y).left = Set.range (pullback.fst (snd X Y).left y.left)`
  `= (snd X Y).left ⁻¹' Set.range y.left` (`Scheme.Pullback.range_fst`). -/
theorem range_sectionLeft {k : Type*} [Field k] (X Y : Work.AbVar.Sch k) (y : Work.AbVar.Point Y) :
    Set.range (Work.AbVar.sectionLeft X Y y).left =
      (SemiCartesianMonoidalCategory.snd X Y).left ⁻¹' Set.range y.left := by
  -- First projection and second projection of the fibre product `X ⊗ Y = X ×ₖ Y`.
  have hx1 : (Work.AbVar.sectionLeft X Y y).left ≫ pullback.fst X.hom Y.hom = 𝟙 X.left := by
    rw [← Over.fst_left, ← Over.comp_left, Work.AbVar.sectionLeft_fst, Over.id_left]
  have hx2 : (Work.AbVar.sectionLeft X Y y).left ≫ pullback.snd X.hom Y.hom
      = X.hom ≫ y.left := by
    rw [← Over.snd_left, ← Over.comp_left, Work.AbVar.sectionLeft_snd, Over.comp_left,
      Over.toUnit_left]
  have hcond1 : pullback.fst X.hom Y.hom ≫ X.hom = pullback.snd X.hom Y.hom ≫ Y.hom :=
    pullback.condition
  have hcond2 : pullback.fst (pullback.snd X.hom Y.hom) y.left ≫ pullback.snd X.hom Y.hom
      = pullback.snd (pullback.snd X.hom Y.hom) y.left ≫ y.left := pullback.condition
  have hyw : y.left ≫ Y.hom = 𝟙 (𝟙_ (Work.AbVar.Sch k)).left := Over.w y
  -- The comparison map from `X` to the pullback `X ×_{X ×ₖ Y} Spec k`.
  let iso : X.left ⟶ pullback (pullback.snd X.hom Y.hom) y.left :=
    pullback.lift (Work.AbVar.sectionLeft X Y y).left X.hom hx2
  let pf : pullback (pullback.snd X.hom Y.hom) y.left ⟶ pullback X.hom Y.hom :=
    pullback.fst (pullback.snd X.hom Y.hom) y.left
  have hiso_fst : iso ≫ pf = (Work.AbVar.sectionLeft X Y y).left := pullback.lift_fst _ _ _
  have hiso_snd : iso ≫ pullback.snd (pullback.snd X.hom Y.hom) y.left = X.hom :=
    pullback.lift_snd _ _ _
  -- `pf` is fixed by the graph projection `p₁ ≫ x`.
  have hstep : pf ≫ (pullback.fst X.hom Y.hom ≫ (Work.AbVar.sectionLeft X Y y).left) = pf := by
    apply pullback.hom_ext
    · calc (pf ≫ (pullback.fst X.hom Y.hom ≫ (Work.AbVar.sectionLeft X Y y).left))
            ≫ pullback.fst X.hom Y.hom
          = pf ≫ (pullback.fst X.hom Y.hom
              ≫ ((Work.AbVar.sectionLeft X Y y).left ≫ pullback.fst X.hom Y.hom)) := by
            simp only [Category.assoc]
        _ = pf ≫ (pullback.fst X.hom Y.hom ≫ 𝟙 X.left) := by rw [hx1]
        _ = pf ≫ pullback.fst X.hom Y.hom := by rw [Category.comp_id]
    · calc (pf ≫ (pullback.fst X.hom Y.hom ≫ (Work.AbVar.sectionLeft X Y y).left))
            ≫ pullback.snd X.hom Y.hom
          = pf ≫ (pullback.fst X.hom Y.hom
              ≫ ((Work.AbVar.sectionLeft X Y y).left ≫ pullback.snd X.hom Y.hom)) := by
            simp only [Category.assoc]
        _ = pf ≫ (pullback.fst X.hom Y.hom ≫ (X.hom ≫ y.left)) := by rw [hx2]
        _ = pf ≫ ((pullback.fst X.hom Y.hom ≫ X.hom) ≫ y.left) := by simp only [Category.assoc]
        _ = pf ≫ ((pullback.snd X.hom Y.hom ≫ Y.hom) ≫ y.left) := by rw [hcond1]
        _ = pf ≫ (pullback.snd X.hom Y.hom ≫ (Y.hom ≫ y.left)) := by simp only [Category.assoc]
        _ = (pf ≫ pullback.snd X.hom Y.hom) ≫ (Y.hom ≫ y.left) := by simp only [Category.assoc]
        _ = (pullback.snd (pullback.snd X.hom Y.hom) y.left ≫ y.left) ≫ (Y.hom ≫ y.left) := by
            rw [hcond2]
        _ = pullback.snd (pullback.snd X.hom Y.hom) y.left ≫ (y.left ≫ (Y.hom ≫ y.left)) := by
            simp only [Category.assoc]
        _ = pullback.snd (pullback.snd X.hom Y.hom) y.left ≫ ((y.left ≫ Y.hom) ≫ y.left) := by
            simp only [Category.assoc]
        _ = pullback.snd (pullback.snd X.hom Y.hom) y.left
              ≫ (𝟙 (𝟙_ (Work.AbVar.Sch k)).left ≫ y.left) := by rw [hyw]
        _ = pullback.snd (pullback.snd X.hom Y.hom) y.left ≫ y.left := by rw [Category.id_comp]
        _ = pf ≫ pullback.snd X.hom Y.hom := hcond2.symm
  have hf2 : pf ≫ (pullback.fst X.hom Y.hom ≫ X.hom)
      = pullback.snd (pullback.snd X.hom Y.hom) y.left := by
    calc pf ≫ (pullback.fst X.hom Y.hom ≫ X.hom)
        = pf ≫ (pullback.snd X.hom Y.hom ≫ Y.hom) := by rw [hcond1]
      _ = (pf ≫ pullback.snd X.hom Y.hom) ≫ Y.hom := by simp only [Category.assoc]
      _ = (pullback.snd (pullback.snd X.hom Y.hom) y.left ≫ y.left) ≫ Y.hom := by rw [hcond2]
      _ = pullback.snd (pullback.snd X.hom Y.hom) y.left ≫ (y.left ≫ Y.hom) := by
          simp only [Category.assoc]
      _ = pullback.snd (pullback.snd X.hom Y.hom) y.left ≫ 𝟙 (𝟙_ (Work.AbVar.Sch k)).left := by
          rw [hyw]
      _ = pullback.snd (pullback.snd X.hom Y.hom) y.left := by rw [Category.comp_id]
  -- The two composites showing that `iso` is inverse to `p₁ ≫ pf`.
  have hiso_phi : iso ≫ (pf ≫ pullback.fst X.hom Y.hom) = 𝟙 X.left := by
    rw [← Category.assoc, hiso_fst, hx1]
  have hphi_iso : (pf ≫ pullback.fst X.hom Y.hom) ≫ iso
      = 𝟙 (pullback (pullback.snd X.hom Y.hom) y.left) := by
    apply pullback.hom_ext
    · calc ((pf ≫ pullback.fst X.hom Y.hom) ≫ iso) ≫ pf
          = pf ≫ (pullback.fst X.hom Y.hom ≫ (iso ≫ pf)) := by simp only [Category.assoc]
        _ = pf ≫ (pullback.fst X.hom Y.hom ≫ (Work.AbVar.sectionLeft X Y y).left) := by
            rw [hiso_fst]
        _ = pf := hstep
        _ = 𝟙 (pullback (pullback.snd X.hom Y.hom) y.left) ≫ pf := (Category.id_comp _).symm
    · calc ((pf ≫ pullback.fst X.hom Y.hom) ≫ iso)
            ≫ pullback.snd (pullback.snd X.hom Y.hom) y.left
          = pf ≫ (pullback.fst X.hom Y.hom
              ≫ (iso ≫ pullback.snd (pullback.snd X.hom Y.hom) y.left)) := by
            simp only [Category.assoc]
        _ = pf ≫ (pullback.fst X.hom Y.hom ≫ X.hom) := by rw [hiso_snd]
        _ = pullback.snd (pullback.snd X.hom Y.hom) y.left := hf2
        _ = 𝟙 (pullback (pullback.snd X.hom Y.hom) y.left)
              ≫ pullback.snd (pullback.snd X.hom Y.hom) y.left := (Category.id_comp _).symm
  have hpf : pf = (pf ≫ pullback.fst X.hom Y.hom) ≫ (Work.AbVar.sectionLeft X Y y).left := by
    calc pf = 𝟙 (pullback (pullback.snd X.hom Y.hom) y.left) ≫ pf := (Category.id_comp _).symm
      _ = ((pf ≫ pullback.fst X.hom Y.hom) ≫ iso) ≫ pf := by rw [← hphi_iso]
      _ = (pf ≫ pullback.fst X.hom Y.hom) ≫ (iso ≫ pf) := by simp only [Category.assoc]
      _ = (pf ≫ pullback.fst X.hom Y.hom) ≫ (Work.AbVar.sectionLeft X Y y).left := by
          rw [hiso_fst]
  have hrange : Set.range (Work.AbVar.sectionLeft X Y y).left = Set.range pf := by
    apply Set.Subset.antisymm
    · rintro z ⟨a, rfl⟩
      refine ⟨iso a, ?_⟩
      rw [(Scheme.Hom.comp_apply iso pf a).symm, ← hiso_fst]
    · rintro z ⟨w, rfl⟩
      refine ⟨(pf ≫ pullback.fst X.hom Y.hom) w, ?_⟩
      rw [(Scheme.Hom.comp_apply (pf ≫ pullback.fst X.hom Y.hom)
            (Work.AbVar.sectionLeft X Y y).left w).symm, ← hpf]
  rw [hrange]
  exact AlgebraicGeometry.Scheme.Pullback.range_fst (pullback.snd X.hom Y.hom) y.left

end Work.AbVar.Rigidity
