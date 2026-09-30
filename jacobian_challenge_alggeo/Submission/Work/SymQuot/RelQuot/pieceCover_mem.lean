import Mathlib
import Submission.Work.SymQuot.RelQuot.Defs
import Submission.Work.SymQuot.Quotient

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.RelQuot

universe u
open CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
theorem pieceCover_mem {K : Type u} [Field K] {X Y : Work.SpecLin.Sch K} {Γ : Type u}
    [Group Γ] [Fintype Γ] (D : Work.SymQuot.QuotientData Γ X.left)
    (hbase : ∀ g : Γ, D.action.hom g ≫ X.hom = X.hom)
    (x : ((Work.SymQuot.relQuotScheme X D hbase) ⊗ Y).left) :
    ∃ (U : D.Chart) (V : Y.left.affineOpens),
      x ∈ Set.range (Work.SymQuot.RelQuot.chartιOv D hbase U ⊗ₘ
        Work.SymQuot.RelQuot.ovVι V).left := by
  obtain ⟨U, y, hy⟩ := D.chartι_jointly_surjective
    (pullback.fst (Work.SymQuot.relQuotScheme X D hbase).hom Y.hom x)
  have hVex : ∃ V : Y.left.affineOpens,
      pullback.snd (Work.SymQuot.relQuotScheme X D hbase).hom Y.hom x ∈ (V.1 : Y.left.Opens) := by
    obtain ⟨s, ⟨V, hVmem, rfl⟩, hxs, -⟩ :=
      Y.left.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (pullback.snd (Work.SymQuot.relQuotScheme X D hbase).hom Y.hom x))
        isOpen_univ
    exact ⟨⟨V, hVmem⟩, hxs⟩
  obtain ⟨V, hV⟩ := hVex
  refine ⟨U, V, ?_⟩
  have hx_mem : x ∈ pullback.fst (Work.SymQuot.relQuotScheme X D hbase).hom Y.hom ⁻¹'
        Set.range (D.chartι U) ∩
      pullback.snd (Work.SymQuot.relQuotScheme X D hbase).hom Y.hom ⁻¹'
        Set.range (V.1.ι) :=
    ⟨⟨y, hy⟩, by simpa using hV⟩
  rw [CategoryTheory.Over.tensorHom_left, AlgebraicGeometry.Scheme.Pullback.range_map]
  exact hx_mem

end Work.SymQuot.RelQuot
