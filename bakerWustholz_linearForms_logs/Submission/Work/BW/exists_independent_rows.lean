import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Every finite family `a : Fin M → Fin N → F` of vectors contains a linearly independent
subfamily (indexed by `Fin M'`) with the same span: the standard fact that a finite spanning
set contains a basis of its span, in the indexed form needed below. -/
theorem exists_independent_rows {F : Type*} [Field F] {M N : ℕ} (a : Fin M → Fin N → F) :
    ∃ (M' : ℕ) (σ : Fin M' → Fin M), Function.Injective σ ∧
      LinearIndependent F (fun i : Fin M' => a (σ i)) ∧
      Submodule.span F (Set.range (fun i : Fin M' => a (σ i))) = Submodule.span F (Set.range a) := by
  classical
  -- Extract a basis `b ⊆ Set.range a` of the span of `a`, with `b` finite.
  obtain ⟨b, hb_sub, hspan, hli⟩ := exists_linearIndependent F (Set.range a)
  have hbfin : b.Finite := Set.Finite.subset (Set.finite_range a) hb_sub
  letI : Fintype b := hbfin.fintype
  -- Reindex `b` by `Fin (Fintype.card b)` and choose preimages under `a`.
  let e : Fin (Fintype.card b) ≃ b := (Fintype.equivFin b).symm
  let σ : Fin (Fintype.card b) → Fin M := fun i => Classical.choose (hb_sub (e i).property)
  have hσ : ∀ i, a (σ i) = (e i).val := fun i => Classical.choose_spec (hb_sub (e i).property)
  have hfun : (fun i : Fin (Fintype.card b) => a (σ i)) = ((↑) : b → (Fin N → F)) ∘ e :=
    funext hσ
  refine ⟨Fintype.card b, σ, ?_, ?_, ?_⟩
  · -- `σ` is injective, since it factors through the injective map `e` via `a`.
    intro i j hij
    have h2 : (e i).val = (e j).val := by rw [← hσ i, ← hσ j, hij]
    exact e.injective (Subtype.ext h2)
  · -- Linear independence transports along the injective reindexing `e`.
    rw [hfun]
    exact hli.comp e e.injective
  · -- The ranges agree, so the spans do.
    rw [hfun, Set.range_comp, e.surjective.range_eq, Set.image_univ, Subtype.range_coe]
    exact hspan

end Work.BW
