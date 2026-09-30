import Mathlib
import Submission.Work.Homology.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Homology

open CategoryTheory CategoryTheory.Limits

/-- **The cokernel of a finite biproduct of maps is the biproduct of the cokernels.**  As the
coproduct functor `C^J → C` is a left adjoint it preserves cokernels, and in an abelian category
the biproduct over a finite `J` is the coproduct; cokernels in `C^J` are computed pointwise. -/
theorem cokernel_biproduct_map_iso {C : Type*} [Category C] [Abelian C] [HasFiniteBiproducts C]
    {J : Type*} [Fintype J] (X Y : J → C) (f : ∀ j, X j ⟶ Y j) :
    Nonempty (cokernel (biproduct.map f) ≅ ⨁ fun j => cokernel (f j)) := by
  classical
  -- `biproduct.map (cokernel.π ∘ f)` vanishes after `biproduct.map f`, so it induces a map
  -- out of `cokernel (biproduct.map f)`.
  have h : biproduct.map f ≫ biproduct.map (fun j => cokernel.π (f j)) = 0 := by
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, biproduct.map_π]
    rw [← Category.assoc, biproduct.map_π]
    simp [cokernel.condition]
  -- The factorisation of any map killing `biproduct.map f` through the biproduct of cokernels.
  let descFn : ∀ {A : C} (k : ⨁ Y ⟶ A),
      (biproduct.map f ≫ k = 0) → ((⨁ fun j => cokernel (f j)) ⟶ A) :=
    fun {A} k hk => biproduct.desc (fun j => cokernel.desc (f j) (biproduct.ι Y j ≫ k) (by
      rw [← Category.assoc, ← biproduct.ι_map (g := Y) f j, Category.assoc, hk, comp_zero]))
  have hfac : ∀ {A : C} (k : ⨁ Y ⟶ A) (hk : biproduct.map f ≫ k = 0),
      biproduct.map (fun j => cokernel.π (f j)) ≫ descFn k hk = k := by
    intro A k hk
    dsimp only [descFn]
    rw [biproduct.map_desc]
    apply biproduct.hom_ext'
    intro j
    rw [biproduct.ι_desc, cokernel.π_desc]
  -- Hence `biproduct.map (cokernel.π ∘ f)` is a cokernel of `biproduct.map f`.
  have hcolim : IsColimit (CokernelCofork.ofπ (biproduct.map (fun j => cokernel.π (f j))) h) :=
    CokernelCofork.IsColimit.ofπ' _ _ (fun k hk => ⟨descFn k hk, hfac k hk⟩)
  exact ⟨colimit.isoColimitCocone ⟨CokernelCofork.ofπ _ h, hcolim⟩⟩

end Work.Homology
