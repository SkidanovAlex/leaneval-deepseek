/-
AREA TOOLKIT — the finite comparison map `∐ f ⟶ ∏ f` is a monomorphism.

For a *finite* index type `β` and a family `f : β → Cpx` of cochain complexes of light
condensed abelian groups, the canonical map

`Pi.lift (fun b => coord f b) : (∐ f) ⟶ (∏ f)`

whose `b`-th component is the `b`-th coordinate of the coproduct, is a monomorphism.

The point of the finiteness hypothesis is that `β` is then a *biproduct* index type: `Cpx`
has finite biproducts, so the coproduct and the product of `f` are canonically identified by
the matrix with entries `δ_{ij}`.  Concretely the comparison map is the composite

`(biproduct.isoCoproduct f).inv ≫ (biproduct.isoProduct f).hom`,

an isomorphism, hence a (split) monomorphism.  This is the finite-index input to the
(countable) statement that a morphism into a small coproduct whose coordinates all vanish is
zero, used to see that the telescope map `1 - shift` of a sequential diagram is a
monomorphism.
-/
import Mathlib
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Instances
import Submission.Work.TOOLKIT.SeqColim.Defs

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

namespace Work.TOOLKIT.SeqColim

/-- For a finite index type `β`, the coordinate comparison map `∐ f ⟶ ∏ f` is the canonical
isomorphism between the coproduct and the product coming from the biproduct `⨁ f`. -/
lemma pi_lift_coord_eq_biproduct_iso {β : Type} [Fintype β] [DecidableEq β] (f : β → Cpx)
    [HasBiproduct f] :
    Pi.lift (fun b => coord f b)
      = (biproduct.isoCoproduct f).inv ≫ (biproduct.isoProduct f).hom := by
  haveI : HasFiniteBiproducts Cpx := HasFiniteBiproducts.of_hasFiniteProducts
  apply Pi.hom_ext
  intro b
  rw [Pi.lift_comp_π, Category.assoc, biproduct.isoProduct_hom, Pi.lift_comp_π,
    biproduct.isoCoproduct_inv]
  apply Sigma.hom_ext
  intro c
  rw [coord, Sigma.ι_comp_desc, ← Category.assoc, Sigma.ι_comp_desc, biproduct.ι_π]
  by_cases h : c = b
  · subst h; simp
  · simp [h]

/-- **The finite comparison map is a monomorphism.**  For a finite index type `β`, the map
`∐ f ⟶ ∏ f` whose `b`-th component is the `b`-th coordinate `coord f b` is a monomorphism. -/
theorem mono_finite_comparison {β : Type} [Fintype β] [DecidableEq β]
    (f : β → Work.TOOLKIT.Cpx) :
    CategoryTheory.Mono (CategoryTheory.Limits.Pi.lift (fun b => Work.TOOLKIT.SeqColim.coord f b)) := by
  haveI : HasFiniteBiproducts Cpx := HasFiniteBiproducts.of_hasFiniteProducts
  haveI hb : HasBiproduct f := inferInstance
  -- The comparison map is the structure isomorphism of the biproduct; in particular it has an
  -- explicit two-sided inverse, so we prove mono-ness by cancellation instead of by instance
  -- search (which is expensive in this large category).
  set e : (∐ f) ≅ (∏ᶜ f) := (biproduct.isoCoproduct f).symm ≪≫ biproduct.isoProduct f with he
  have key : Pi.lift (fun b => coord f b) = e.hom := by
    rw [he, Iso.trans_hom, Iso.symm_hom]
    exact pi_lift_coord_eq_biproduct_iso f
  rw [key]
  refine ⟨fun {Z} a b' hab => ?_⟩
  have h : a ≫ e.hom ≫ e.inv = b' ≫ e.hom ≫ e.inv := by
    rw [← Category.assoc, hab, Category.assoc]
  simpa only [Iso.hom_inv_id, Category.comp_id] using h

end Work.TOOLKIT.SeqColim
