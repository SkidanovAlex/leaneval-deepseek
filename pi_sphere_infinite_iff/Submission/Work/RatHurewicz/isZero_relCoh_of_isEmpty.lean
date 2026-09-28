import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Thom.Cohomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The rational relative cohomology of a pair with empty total space

Let `X` be a topological space, `S ⊆ X` a subset whose subtype `↥S` is **empty** (i.e. `S = ∅`),
and `B ⊆ ↥S` any subset of it (automatically empty as well).  Then the singular relative
cohomology `H^n(↥S, B; ℚ)` vanishes: it is a zero object of the category of `ℚ`-modules.

The reason is that an empty space has no singular simplices at all: the singular `n`-simplices of a
space `Y` are the continuous maps `Δ^n → Y`, and there are none when `Y` is empty but `Δ^n` is not.
Hence the singular chain module `C_n(↥S)` is a coproduct indexed by an empty type, i.e. a zero
object; dually every singular cochain module `C^n(↥S; ℚ)` is a zero object, and so is every
submodule of it — in particular the relative cochains `C^n(↥S, B)`, which are the kernel of the
restriction `C^n(↥S) → C^n(B)`.  A cochain complex whose `n`-th term is a zero object has
vanishing `n`-th homology, which is the statement.

Only the vanishing of the `n`-th term is used, so no hypothesis on `B` (beyond it being a subset)
is needed; in particular the lemma applies verbatim to the `B = ∅` and `B = univ` cases used in the
rational Hurewicz argument.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.RatHurewicz

noncomputable section

/-- A coproduct over an empty index type is a zero object. -/
lemma isZero_coproduct_of_isEmpty' {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasZeroObject C] {β : Type*} [IsEmpty β] (f : β → C) [HasCoproduct f] :
    IsZero (∐ f) :=
  (coproductIsCoproduct f).isZero_pt
    ((Functor.isZero_iff (Discrete.functor f)).mpr (fun X => isEmptyElim X.as))

/-- The singular `n`-simplices of an empty space form an empty type: a singular simplex is a
continuous map from the (nonempty) standard `n`-simplex into the empty space, of which there are
none. -/
lemma isEmpty_singularSimplex_of_isEmpty' (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsEmpty ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) := by
  refine ⟨fun x => ?_⟩
  have hx := (TopCat.toSSetObjEquivT Y (Opposite.op (SimplexCategory.mk n))) x
  haveI : Nonempty (↑(stdSimplex ℝ (Fin ((Opposite.unop (Opposite.op
    (SimplexCategory.mk n))).len + 1)))) := inferInstance
  exact isEmptyElim (hx (Classical.arbitrary _))

/-- Every component of the singular chain complex of an empty space is a zero object. -/
lemma isZero_singularChains_of_isEmpty' (Y : TopCat) [IsEmpty (↥Y)] (n : ℕ) :
    IsZero ((Work.Cohomology.singularChains ℚ Y).X n) := by
  haveI : IsEmpty ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) :=
    isEmpty_singularSimplex_of_isEmpty' Y n
  exact isZero_coproduct_of_isEmpty'
    (fun _ : ((TopCat.toSSet.obj Y).obj (Opposite.op (SimplexCategory.mk n))) => ModuleCat.of ℚ ℚ)

/-- A cochain complex whose `n`-th term is a zero object has vanishing `n`-th homology. -/
lemma isZero_homology_of_isZero_X' {K : CochainComplex (ModuleCat ℚ) ℕ} (n : ℕ)
    (h : IsZero (K.X n)) : IsZero (K.homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ h

/-- The rational relative cohomology of a pair whose total space is empty vanishes. -/
theorem isZero_relCoh_of_isEmpty {X : Type} [TopologicalSpace X] {S : Set X}
    (hS : IsEmpty ↥S) (B : Set ↥S) (n : ℕ) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ n ↥S B) := by
  haveI hSe : IsEmpty ↥S := hS
  -- the singular `n`-chains of `↥S` form a coproduct over an empty type
  have hchain : IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of ↥S)).X n) :=
    isZero_singularChains_of_isEmpty' (TopCat.of ↥S) n
  -- hence the singular `n`-cochains, and every submodule of them, are zero objects
  haveI : Subsingleton ((Work.Cohomology.singularChains ℚ (TopCat.of ↥S)).X n) :=
    ModuleCat.subsingleton_of_isZero hchain
  haveI : Subsingleton ((Work.Cohomology.singularCochainComplex ℚ (TopCat.of ↥S)).X n) := by
    haveI : Subsingleton ((Work.Cohomology.singularChains ℚ (TopCat.of ↥S)).X n →ₗ[ℚ] ℚ) :=
      ⟨fun f g => by ext x; rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    exact ‹Subsingleton ((Work.Cohomology.singularChains ℚ (TopCat.of ↥S)).X n →ₗ[ℚ] ℚ)›
  haveI : Subsingleton (Work.Cohomology.relKern ℚ (TopCat.of ↥S) B n) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩
  haveI : Subsingleton ↑((Work.Cohomology.relComplex ℚ (TopCat.of ↥S) B).X n) :=
    ‹Subsingleton (Work.Cohomology.relKern ℚ (TopCat.of ↥S) B n)›
  exact isZero_homology_of_isZero_X' n (ModuleCat.isZero_of_subsingleton _)

end

end Work.RatHurewicz
