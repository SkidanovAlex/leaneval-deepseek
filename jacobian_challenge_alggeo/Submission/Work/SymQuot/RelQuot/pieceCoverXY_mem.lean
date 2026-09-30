import Mathlib
import Submission.Work.SymQuot.RelQuot.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.RelQuot

universe u
open CategoryTheory Limits AlgebraicGeometry in
open scoped MonoidalCategory in
theorem pieceCoverXY_mem {K : Type u} [Field K] {X Y : Work.SpecLin.Sch K} {Γ : Type u}
    [Group Γ] [Fintype Γ] (D : Work.SymQuot.QuotientData Γ X.left)
    (x : (X ⊗ Y).left) :
    ∃ (U : D.Chart) (V : Y.left.affineOpens),
      x ∈ Set.range (Work.SymQuot.RelQuot.ovIncl (D := D) U ⊗ₘ
        Work.SymQuot.RelQuot.ovVι V).left := by
  obtain ⟨U, hUaff, hUinv, hxU⟩ := D.covers (pullback.fst X.hom Y.hom x)
  have hVex : ∃ V : Y.left.affineOpens,
      pullback.snd X.hom Y.hom x ∈ (V.1 : Y.left.Opens) := by
    obtain ⟨s, ⟨V, hVmem, rfl⟩, hxs, -⟩ :=
      Y.left.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (pullback.snd X.hom Y.hom x)) isOpen_univ
    exact ⟨⟨V, hVmem⟩, hxs⟩
  obtain ⟨V, hV⟩ := hVex
  refine ⟨⟨U, hUaff, hUinv⟩, V, ?_⟩
  have hx_mem : x ∈ pullback.fst X.hom Y.hom ⁻¹' Set.range (U.ι) ∩
      pullback.snd X.hom Y.hom ⁻¹' Set.range (V.1.ι) :=
    ⟨by rw [Scheme.Opens.range_ι]; exact hxU,
      by rw [Scheme.Opens.range_ι]; exact hV⟩
  rw [Over.tensorHom_left, Scheme.Pullback.range_map]
  exact hx_mem

end Work.SymQuot.RelQuot
