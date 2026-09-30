import Mathlib
import Submission.Work.HomologyMV.Model
import Submission.Work.HomologyMV.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `HomologyIso/`: the biproduct of free `ℤ`-modules of ranks `r i`

This file proves `Work.HomologyIso.biproduct_freeMod`:

`⨁_i ℤ^{r i} ≅ ℤ^{∑ i, r i}`,

i.e. the (finite) direct sum of the pieces of a *disjoint union of bases* is the free module on
that union.  It is the algebraic half of the per-cusp decomposition of the models
`ModelM k = ⊕_v H_k(T³_v)` and `ModelB k = ⊕_v H_k(T²_v)` of the Mayer–Vietoris computation
of `M̂`.

The proof goes through the three standard identifications

* `ModuleCat.biproductIsoPi` — the biproduct of `ℤ`-modules is the Cartesian product,
  `⨁_i M_i ≅ ↧(∀ i, M_i)`;
* currying — `(∀ i, Fin (r i) → ℤ) ≃ₗ[ℤ] ((Σ i, Fin (r i)) → ℤ)` (`piCurryLinear`);
* reindexing along the bijection `(Σ i, Fin (r i)) ≃ Fin (∑ i, r i)`
  (`finSigmaFinEquiv`), which turns a tuple on the disjoint union into a tuple on `Fin (∑ i, r i)`.

## Main definitions and results

* `piCurryLinear`, `finSigmaFinEquiv`, `biprodLinEquiv` — the ingredients above;
* `biproductFreeModIso` — the isomorphism `⨁_i ℤ^{r i} ≅ ℤ^{∑ i, r i}`;
* `biproduct_freeMod` — the same, as a `Nonempty` statement.
-/

namespace Work.HomologyIso

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {ι : Type} [Fintype ι]

/-! ## §1  The linear algebra of a disjoint union of bases -/

/-- **Currying**: a family of tuples, one for each `i`, is the same thing as a single tuple
indexed by the disjoint union `Σ i, Fin (r i)`.  The linear form of
`(Π i, α i → M) ≃ ((Σ i, α i) → M)` for `M = ℤ`. -/
def piCurryLinear (r : ι → ℕ) :
    (∀ i, Fin (r i) → ℤ) ≃ₗ[ℤ] ((Σ i, Fin (r i)) → ℤ) where
  toFun f := fun x => f x.1 x.2
  invFun g := fun i j => g ⟨i, j⟩
  left_inv f := by funext i j; rfl
  right_inv g := by funext x; obtain ⟨i, j⟩ := x; rfl
  map_add' f g := by funext x; rfl
  map_smul' c f := by funext x; rfl

/-- The bijection `(Σ i : ι, Fin (r i)) ≃ Fin (∑ i, r i)`: both sides count the elements of the
disjoint union of the bases, and any two finite types of the same cardinality are equivalent. -/
def finSigmaFinEquiv (r : ι → ℕ) : (Σ i, Fin (r i)) ≃ Fin (Finset.univ.sum r) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_sigma]; simp)

/-- **The linear algebra lemma**: `(∀ i, Fin (r i) → ℤ) ≃ₗ[ℤ] (Fin (∑ i, r i) → ℤ)`.

This is the composition of currying (`piCurryLinear`) with the reindexing along
`finSigmaFinEquiv`. -/
def biprodLinEquiv (r : ι → ℕ) :
    (∀ i, Fin (r i) → ℤ) ≃ₗ[ℤ] (Fin (Finset.univ.sum r) → ℤ) :=
  (piCurryLinear r).trans ((LinearEquiv.funCongrLeft ℤ ℤ (finSigmaFinEquiv r)).symm)

/-! ## §2  The isomorphism of the biproduct with the free module -/

/-- **The biproduct of the free `ℤ`-modules `ℤ^{r i}` is the free `ℤ`-module `ℤ^{∑ i, r i}`**: the
biproduct is the product (`ModuleCat.biproductIsoPi`), the product of the tuples is the curried
tuple on the disjoint union of the bases (`biprodLinEquiv`). -/
def biproductFreeModIso (r : ι → ℕ) :
    (⨁ fun i => Work.HomologyMV.freeMod (r i)) ≅
      Work.HomologyMV.freeMod (Finset.univ.sum r) :=
  (ModuleCat.biproductIsoPi (fun i => Work.HomologyMV.freeMod (r i))).trans
    (LinearEquiv.toModuleIso (biprodLinEquiv r))

open CategoryTheory CategoryTheory.Limits in
/-- **The biproduct of free `ℤ`-modules of ranks `r i` is free of rank `∑ i, r i`.**

Here `Work.HomologyMV.freeMod n = ModuleCat.of ℤ (Fin n → ℤ)`, so this is the statement that
`(⨁ i, (Fin (r i) → ℤ)) ≅ (Fin (∑ i, r i) → ℤ)` — the direct sum of the pieces of a disjoint union
of bases is the basis of the union.  It is the algebraic half of the per-cusp decomposition of the
models `ModelM k = ⊕_v H_k(T³_v)` and `ModelB k = ⊕_v H_k(T²_v)` of the Mayer–Vietoris computation
of `M̂`.

A useful ingredient for the proof is `finSigmaFinEquiv : (Σ i : Fin n, Fin (f i)) ≃ Fin (∑ i, f i)`
together with the currying equivalence `(Π i, α i → M) ≃ ((Σ i, α i) → M)`. -/
theorem biproduct_freeMod {ι : Type} [Fintype ι] (r : ι → ℕ) :
    Nonempty ((CategoryTheory.Limits.biproduct
        (fun i => Work.HomologyMV.freeMod (r i))) ≅
      Work.HomologyMV.freeMod (Finset.univ.sum r)) :=
  ⟨biproductFreeModIso r⟩

end

end Work.HomologyIso
