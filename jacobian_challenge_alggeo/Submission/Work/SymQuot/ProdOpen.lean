/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Product opens and the symmetric-group action on `Xⁿ` (area SY)

For a `K`-scheme `X`, an open subscheme `V ⊆ X` and `n : ℕ`, the *product open*
`piOpen X V n ⊆ Xⁿ` is the open subscheme of `n`-tuples all of whose coordinates lie in `V`.
It is `S_n`-invariant (`piOpen_invariant`), it is affine when `V` is affine (delegated:
`Work.SymQuot.isAffineOpen_piOpen`), and meets of product opens are product opens
(`piOpen_inf`).  These are exactly the properties that make the `S_n`-invariant affine open
cover of `Cⁿ` needed for the construction of `Sym^n C` (see `Submission/Work/SymQuot/NOTES.md`).
-/
import Submission.Work.SymQuot.SymAction
import Submission.Work.SymQuot.Product.permIso_hom_proj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SymQuot

variable {K : Type u} [Field K]

/-- **The product open `Vⁿ` of `Xⁿ`**: the points all of whose coordinates lie in `V`.

It is defined as the set-theoretic intersection of the preimages of `V` under the projections, so
that membership is `mem_piOpen` by definition. -/
noncomputable def piOpen (X : Work.GCBasics.Sch K) (V : X.left.Opens) (n : ℕ) :
    (prod X n).left.Opens :=
  ⟨⋂ m, ((proj X n m).left ⁻¹ᵁ V : Set (prod X n).left),
    isOpen_iInter_of_finite fun m => (proj X n m).left ⁻¹ᵁ V |>.2⟩

@[simp]
theorem mem_piOpen {X : Work.GCBasics.Sch K} {V : X.left.Opens} {n : ℕ}
    {x : (prod X n).left} :
    x ∈ piOpen X V n ↔ ∀ m, (proj X n m).left x ∈ V := by
  change x ∈ (⋂ m, ((proj X n m).left ⁻¹ᵁ V : Set (prod X n).left)) ↔
    ∀ m, (proj X n m).left x ∈ V
  rw [Set.mem_iInter]
  simp only [SetLike.mem_coe, Scheme.Hom.mem_preimage]

theorem piOpen_mono {X : Work.GCBasics.Sch K} {V W : X.left.Opens} (h : V ≤ W) (n : ℕ) :
    piOpen X V n ≤ piOpen X W n := by
  intro x hx
  rw [mem_piOpen] at hx ⊢
  exact fun m => h (hx m)

/-- The meet of two product opens is the product open of the meet. -/
theorem piOpen_inf (X : Work.GCBasics.Sch K) (V W : X.left.Opens) (n : ℕ) :
    piOpen X (V ⊓ W) n = piOpen X V n ⊓ piOpen X W n := by
  ext x
  simp only [SetLike.mem_coe]
  simp [mem_piOpen, forall_and]

theorem piOpen_top (X : Work.GCBasics.Sch K) (n : ℕ) :
    piOpen X (⊤ : X.left.Opens) n = ⊤ := by
  ext x
  simp [mem_piOpen]

/-- **The `n`-th projection after a permutation.**  This is the projection formula
`permIso_hom_proj` transported to the underlying schemes. -/
theorem comp_hom_proj (X : Work.GCBasics.Sch K) (n : ℕ) (σ : Equiv.Perm (Fin n))
    (m : Fin n) :
    (permGAction X n).hom σ ≫ (proj X n m).left = (proj X n (σ.symm m)).left :=
  congrArg (fun f : prod X n ⟶ X => f.left)
    (Work.SymQuot.Product.permIso_hom_proj X σ m)

/-- The projection formula, evaluated at a point. -/
theorem apply_hom_proj (X : Work.GCBasics.Sch K) (n : ℕ) (σ : Equiv.Perm (Fin n)) (m : Fin n)
    (x : (prod X n).left) :
    (proj X n m).left ((permGAction X n).hom σ x) = (proj X n (σ.symm m)).left x :=
  congrArg (fun (f : (prod X n).left ⟶ X.left) => f x) (comp_hom_proj X n σ m)

/-- The action of `S_n` on `Xⁿ` permutes the coordinates, hence preserves each product open. -/
theorem piOpen_invariant (X : Work.GCBasics.Sch K) (V : X.left.Opens) (n : ℕ) :
    (permGAction X n).IsInvariantOpen (piOpen X V n) := by
  intro σ
  ext x
  simp only [SetLike.mem_coe, Scheme.Hom.mem_preimage, mem_piOpen]
  constructor
  · intro h m
    have h' := h (σ m)
    have key := apply_hom_proj X n σ (σ m) x
    rw [Equiv.symm_apply_apply] at key
    rwa [key] at h'
  · intro h m
    rw [apply_hom_proj X n σ m x]
    exact h (σ.symm m)

end Work.SymQuot
