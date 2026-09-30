import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `HomologyMV/`: the Mayer–Vietoris interface

This file fixes the **shape of the input** to the Mayer–Vietoris computation of `H_*(M̂)`
(blueprint §3, area `HMV`).

The space `M̂` is covered by two open sets `A` (a thickening of `M̄`) and `B` (the union of
the five filling pieces), and the Mayer–Vietoris sequence is

```
⋯ → H_k(A ∩ B) → H_k(A) ⊞ H_k(B) → H_k(X) → H_{k-1}(A ∩ B) → ⋯
```

Its terms are indexed here by `MVI := ℤ × Fin 3`, where

* `(k, 0)` is `H_k(A ∩ B)`,
* `(k, 1)` is `H_k(A) ⊞ H_k(B)`,
* `(k, 2)` is `H_k(X)`.

The `(k, 2) → (k-1, 0)` step lowers the degree, which is why the index set is a
*cyclic* arrangement of three slots per degree and the successor map sends `(k, 2)` to
`(k - 1, 0)`.  Terms in negative degrees are the zero module (this is not enforced by the
structure: a term `H (-1, r)` is simply part of the data and will be the zero module).

## Main definitions

* `Work.HomologyMV.MVI`, `Work.HomologyMV.mvSucc` — the index set and its successor;
* `Work.HomologyMV.MVLES` — a long exact sequence of `ℤ`-modules in this indexing;
* `Work.HomologyMV.MVLES.mkOfSlots` — constructor from the three families of exactness
  statements (`H_k(A∩B) → H_k(A) ⊞ H_k(B) → H_k(X)`, `H_k(A) ⊞ H_k(B) → H_k(X) → H_{k-1}(A∩B)`,
  `H_k(X) → H_{k-1}(A∩B) → H_{k-1}(A) ⊞ H_{k-1}(B)`) that `Submission/Work/Homology` exports;
* `Work.HomologyMV.functionExact_of_shortExact` — the bridge from `ShortComplex.Exact`
  (the form in which `mv_H_exact₁₂₃` are stated) to `Function.Exact`.
-/

namespace Work.HomologyMV

open CategoryTheory
open CategoryTheory.Limits

/-! ## A typeclass priority for `ℤ`-module structures

A `ℤ`-module structure on the subtype `↥p` of a submodule can be found by typeclass search in
two propositionally equal but not definitionally equal ways: the restriction of the ambient
scalar multiplication (`Submodule.module`) and the canonical action of `ℤ` on any additive
group (`AddCommGroup.toIntModule`).  Mathlib's own `LinearEquiv` constructions (such as
`LinearMap.quotKerEquivRange` and `LinearEquiv.ofEq`) use the former, so we raise its priority
here; this makes statements of the form `↥(f.ker) ≃ₗ[ℤ] ↥(g.ker)` elaborate and compose.
The same bump is needed for quotients (`Submodule.Quotient.module`). -/
attribute [instance 2000] Submodule.module Submodule.Quotient.module

noncomputable section

/-- The Mayer–Vietoris index set: `(k, 0)` is the `A ∩ B` slot, `(k, 1)` the `A ⊞ B` slot and
`(k, 2)` the `X` slot, in degree `k`. -/
abbrev MVI : Type := ℤ × Fin 3

/-- The successor of an index in the Mayer–Vietoris sequence:
`(k,0) ↦ (k,1) ↦ (k,2) ↦ (k-1,0)`. -/
def mvSucc (i : MVI) : MVI :=
  match i.2 with
  | ⟨0, _⟩ => (i.1, 1)
  | ⟨1, _⟩ => (i.1, 2)
  | ⟨2, _⟩ => (i.1 - 1, 0)

@[simp] theorem mvSucc_zero (k : ℤ) : mvSucc (k, 0) = (k, 1) := rfl

@[simp] theorem mvSucc_one (k : ℤ) : mvSucc (k, 1) = (k, 2) := rfl

@[simp] theorem mvSucc_two (k : ℤ) : mvSucc (k, 2) = (k - 1, 0) := rfl

/-- The three slot indices are distinct, in the sense that the successor map has no fixed
point. -/
theorem mvSucc_ne_self (i : MVI) : mvSucc i ≠ i := by
  obtain ⟨k, r⟩ := i
  fin_cases r <;> simp [mvSucc]

/-- A **Mayer–Vietoris long exact sequence**, indexed by `MVI`: a `ℤ`-module `H i` for each
index and maps `d i : H i ⟶ H (mvSucc i)` that are exact at every node.

Exactness is recorded in the function form `Function.Exact (d i) (d (mvSucc i))`, which is
equivalent to `(d (mvSucc i)).ker = (d i).range`; the vanishing of the composites
`d i ≫ d (mvSucc i) = 0` is *derived* (`MVLES.d_comp`). -/
structure MVLES where
  /-- The terms of the sequence. -/
  H : MVI → ModuleCat ℤ
  /-- The maps of the sequence. -/
  d : ∀ i, H i ⟶ H (mvSucc i)
  /-- Exactness at every node. -/
  exact : ∀ i, Function.Exact (d i) (d (mvSucc i))

namespace MVLES

variable (L : MVLES)

/-- Exactness at the `A ⊞ B` slot in degree `k`: `ker(H_k(A) ⊞ H_k(B) → H_k(X)) = im H_k(A∩B)`. -/
theorem exactA (k : ℤ) : Function.Exact (L.d (k, 0)) (L.d (k, 1)) := L.exact (k, 0)

/-- Exactness at the `X` slot in degree `k`: `ker(H_k(X) → H_{k-1}(A∩B)) = im(H_k(A) ⊞ H_k(B))`. -/
theorem exactB (k : ℤ) : Function.Exact (L.d (k, 1)) (L.d (k, 2)) := L.exact (k, 1)

/-- Exactness at the `A ∩ B` slot in degree `k - 1`: this is the exactness statement whose
incoming map is `d (k,2)`, namely `ker(H_{k-1}(A∩B) → H_{k-1}(A) ⊞ H_{k-1}(B)) =
im(H_k(X) → H_{k-1}(A∩B))`.  It is recorded in the "successor" indexing so that it is
literally `L.exact (k, 2)`. -/
theorem exactC (k : ℤ) : Function.Exact (L.d (k, 2)) (L.d (k - 1, 0)) := L.exact (k, 2)

/-- The composite of two consecutive maps in the Mayer–Vietoris sequence vanishes. -/
theorem d_comp (i : MVI) : L.d i ≫ L.d (mvSucc i) = 0 := by
  apply ModuleCat.hom_ext
  ext x
  have hker : (L.d (mvSucc i)).hom.ker = (L.d i).hom.range := by
    simpa using LinearMap.exact_iff.mp (L.exact i)
  have hx : (L.d i).hom x ∈ (L.d (mvSucc i)).hom.ker := by
    rw [hker]; exact ⟨x, rfl⟩
  simpa using hx

end MVLES

/-- Constructor for `MVLES` from the three families of exactness statements in *successor*
form.  These are exactly what the Mayer–Vietoris sequence of a cover provides. -/
def MVLES.mkOfSlots (H : MVI → ModuleCat ℤ) (d : ∀ i, H i ⟶ H (mvSucc i))
    (hA : ∀ k, Function.Exact (d (k, 0)) (d (k, 1)))
    (hB : ∀ k, Function.Exact (d (k, 1)) (d (k, 2)))
    (hC : ∀ k, Function.Exact (d (k, 2)) (d (k - 1, 0))) : MVLES where
  H := H
  d := d
  exact := fun i => by
    obtain ⟨k, r⟩ := i
    fin_cases r
    · exact hA k
    · exact hB k
    · exact hC k

/-- Exactness is automatic at a node whose middle term is a trivial module.  This is what makes
the zero terms of the Mayer–Vietoris sequence in degrees `< 0` (and, for the lead's
instantiation, in degrees `≥ 5`) free of any work. -/
theorem functionExact_of_subsingleton_mid {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C] [Subsingleton B]
    (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C) : Function.Exact f g := by
  intro y
  have hy : y = 0 := Subsingleton.elim _ _
  subst hy
  exact ⟨fun _ => ⟨0, by simp⟩, fun _ => by simp⟩

/-- Constructor for `MVLES` that requires the exactness only in non-negative degrees, the terms
in negative degrees being the zero module.  (In an actual instantiation the negative-degree
terms are `H_k(A ∩ B)`, `H_k(A) ⊞ H_k(B)`, `H_k(M̂)` for `k < 0`, i.e. the zero module.) -/
def MVLES.mkOfNonneg (H : MVI → ModuleCat ℤ) (d : ∀ i, H i ⟶ H (mvSucc i))
    (hneg : ∀ i, i.1 < 0 → IsZero (H i))
    (hex : ∀ i, 0 ≤ i.1 → Function.Exact (d i) (d (mvSucc i))) : MVLES where
  H := H
  d := d
  exact := fun i => by
    by_cases hi : i.1 < 0
    · have hlt : (mvSucc i).1 < 0 := by
        obtain ⟨k, r⟩ := i
        fin_cases r <;> simp_all [mvSucc] <;> omega
      have hsub : Subsingleton (H (mvSucc i)) :=
        ModuleCat.isZero_iff_subsingleton.mp (hneg (mvSucc i) hlt)
      have h := functionExact_of_subsingleton_mid (f := (d i).hom) (g := (d (mvSucc i)).hom)
      exact h
    · exact hex i (by omega)

/-- The bridge from the `ShortComplex.Exact` form of Mayer–Vietoris exactness (as exported by
`Submission/Work/Homology` and `Submission/Work/Cohomology`) to the function form used here. -/
theorem functionExact_of_shortExact {M N P : ModuleCat ℤ} (f : M ⟶ N) (g : N ⟶ P)
    (h : f ≫ g = 0) (hs : (ShortComplex.mk f g h).Exact) : Function.Exact f g :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hs

/-- Two morphisms of `ℤ`-modules that agree on a generating set are equal.  This is the form in
which chain-level certificates (a homology class matched on the classes of a basis of cycles)
are turned into equalities of maps. -/
theorem ModuleCat.ext_on_span {M N : ModuleCat ℤ} {s : Set M} (hs : Submodule.span ℤ s = ⊤)
    {f g : M ⟶ N} (h : ∀ x ∈ s, f x = g x) : f = g :=
  ModuleCat.hom_ext (LinearMap.ext_on hs fun x hx => h x hx)

end

end Work.HomologyMV
