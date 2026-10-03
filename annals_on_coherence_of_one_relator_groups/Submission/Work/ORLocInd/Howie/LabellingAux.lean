/-
# Conjugation of paths into a vertex group, and the labelling it induces

This file provides the combinatorial core of Howie's *Case 1* (the indicable case of Theorem 3.1):
given a connected graph `Γ` (a quiver with an involutive reversal), a base vertex `v` and a chosen
path `d x : v ⟶ x` to every vertex, every path `p : a → b` of `Γ` can be *conjugated* into the
vertex group at `v`,

`conjElem d p = d a · p · (d b)⁻¹  ∈  F(Γ)_v`,

and `conjElem` is a "groupoid homomorphism along paths": it is multiplicative under composition
(`conjElem_comp`, proved in `conjElem_comp.lean`), sends `nil` to `1` and reverses to inverses.

A homomorphism `ψ : F(Γ)_v →* ℤ` therefore induces a *balanced labelling* of the arrows,

`labOf d ψ e = ψ (d (e.left) · e · d (e.right)⁻¹)`,

whose path sums are the `ψ`-values of the conjugated loops (`pathSum_labOf`).  This is the
labelling `θ` of Howie's Case 1 and the construction of `exists_labelling`.

## What is proved here

* `pmul_red_left`, `pmul_red_right`: `red` is a normal form for the free-groupoid product `pmul`;
* `conjPath`, `conjElem`: the conjugation of a path into `F(Γ)_v`;
* `conjElem_nil`, `conjElem_coe`;
* `labOf`: the induced integer labelling of the arrows.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Basic
import Submission.Work.ORLocInd.Howie.Cover

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
variable {v : V}

/-! ## `red` is a normal form for `pmul` -/

/-- Replacing a path by its reduced form does not change the product on the left. -/
theorem pmul_red_left {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    pmul (red p) q = pmul p q := by
  show red ((red p).comp q) = red (p.comp q)
  refine (red_eq_of_reducesTo_isReduced ?_ (isReduced_red _)).symm
  exact ((reducesTo_red p).comp_right q).trans (reducesTo_red ((red p).comp q))

/-- Replacing a path by its reduced form does not change the product on the right. -/
theorem pmul_red_right {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    pmul p (red q) = pmul p q := by
  show red (p.comp (red q)) = red (p.comp q)
  refine (red_eq_of_reducesTo_isReduced ?_ (isReduced_red _)).symm
  exact (reducesTo_comp_left (reducesTo_red q) p).trans (reducesTo_red (p.comp (red q)))

/-! ## Conjugation of a path into the vertex group at `v` -/

/-- The closed path at `v` obtained by conjugating `p : a → b` with the chosen paths
`d a : v → a` and `d b : v → b`: `d a · p · (d b)⁻¹` (concatenated and reduced). -/
noncomputable def conjPath (d : ∀ x : V, Quiver.Path v x) {a b : V} (p : Quiver.Path a b) :
    Quiver.Path v v :=
  pmul (pmul (d a) p) (d b).reverse

/-- The element of the vertex group `F(Γ)_v` obtained by conjugating `p : a → b` with the chosen
paths to `a` and `b`. -/
noncomputable def conjElem (d : ∀ x : V, Quiver.Path v x) {a b : V} (p : Quiver.Path a b) :
    VertexGroup v :=
  ⟨conjPath d p, pmul_isReduced _ _⟩

@[simp] theorem conjElem_coe (d : ∀ x : V, Quiver.Path v x) {a b : V} (p : Quiver.Path a b) :
    (conjElem d p).1 = conjPath d p := rfl

/-- Unfolding the conjugation of a path. -/
theorem conjElem_eq (d : ∀ x : V, Quiver.Path v x) {a b : V} (p : Quiver.Path a b) :
    conjElem d p = ⟨pmul (pmul (d a) p) (d b).reverse, pmul_isReduced _ _⟩ := rfl

/-- The conjugation of the empty path is trivial. -/
@[simp] theorem conjElem_nil (d : ∀ x : V, Quiver.Path v x) (a : V) :
    conjElem d (Quiver.Path.nil : Quiver.Path a a) = 1 := by
  apply Subtype.ext
  show pmul (pmul (d a) Quiver.Path.nil) (d a).reverse = Quiver.Path.nil
  rw [pmul_nil_right, pmul_red_left]
  exact pmul_reverse (d a)

/-! ## The induced labelling of the arrows -/

/-- The labelling of the arrows of `Γ` by integers induced by a homomorphism
`ψ : F(Γ)_v →* ℤ`: the arrow `e : a → b` is sent to the `ψ`-value of the conjugated loop
`d a · e · (d b)⁻¹`. -/
noncomputable def labOf (d : ∀ x : V, Quiver.Path v x)
    (ψ : VertexGroup v →* Multiplicative ℤ) : Quiver.Total V → ℤ :=
  fun e => Multiplicative.toAdd (ψ (conjElem d e.hom.toPath))

end Work.ORLocInd.Howie
