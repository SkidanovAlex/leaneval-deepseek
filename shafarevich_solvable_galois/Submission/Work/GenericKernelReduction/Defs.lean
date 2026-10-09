/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The generic-kernel hypothesis over `ℚ`

This file states the single deep hypothesis on which the present area is conditional:
`Work.GenericKernelReduction.GenericKernelSolvable`, the *generic kernel* form of the split
embedding theorem over `ℚ` (Theorem 15 of A. Schmidt and K. Wingberg, *Šafarevič's theorem on
solvable groups as Galois groups*, arXiv:math/9809211, **without** its two local conditions
(i), (ii)).

## The mathematical content

Let `L/ℚ` be a finite Galois extension inside a fixed algebraic closure `ℚ̄ = AlgebraicClosure ℚ`
and let `G = Gal(L/ℚ)`.  For a prime `p` and `n, ν : ℕ` let

  `F^(n)/F^(n)(ν) = Work.ProP.FreePQuotient p n ν`

be the `ν`-th quotient of the descending `p`-central (Zassenhaus) filtration of the free group
`F^(n) = FreeGroup (Fin n)`; this is the *generic kernel* of Schmidt–Wingberg, the discrete shadow
of the quotient `F^(n)/F^(n)(ν)` of the free pro-`p` `G`-operator group `F^(n)` of rank `n`.  An
action `ρ : G →* MulAut (FreeGroup (Fin n))` descends to an action `Φ` on
`F^(n)/F^(n)(ν)` (`Work.ProP.exists_freePQuotientAction`; the filtration terms are
characteristic), and `GenericKernelSolvable` asserts that the *split embedding problem*
`1 → F^(n)/F^(n)(ν) → (F^(n)/F^(n)(ν)) ⋊[Φ] G → G → 1` over `ℚ` has a **proper solution**: a
finite Galois extension `L' ⊇ L` of `ℚ` with `L'/L` Galois and an isomorphism
`(F^(n)/F^(n)(ν)) ⋊[Φ] G ≃* Gal(L'/ℚ)` restricting along `Gal(L'/ℚ) → Gal(L/ℚ)` to the canonical
projection (this is exactly the unfolded predicate `Work.Fitting.SplitEmbeddingSolvable`).

Theorem 15 of Schmidt–Wingberg is the same assertion *with* the two additional local conditions

* (i) every prime `p ∈ Ram(K/k) ∪ S_p ∪ S_∞` is completely decomposed in `N^{n,τ}/K`;
* (ii) if `p` is ramified in `N^{n,τ}/K` then it splits completely in `K/k` and `N^{n,τ}_p/k_p`
  is a (cyclic) totally ramified extension of local fields,

which are used only to make the induction on the refined index `τ` work (`τ = (1,1)` is trivial;
the conditions are preserved under the shrinking step).  Those conditions are what forces the
*refined* filtration `F^(n)(τ)`, `τ = (i,j)`, and the use of Chebotarev/Grünwald–Wang; they are
**omitted here**, which is exactly the sense in which `GenericKernelSolvable` is the
"generic-kernel statement for each prime" of the reduction of Theorem 14: it is the statement
that suffices for Theorem 14 (see `GenericKernelReduction.splitEmbeddingTheoremOverRat_of_genericKernel`),
but is strictly weaker than Theorem 15 as literally stated (no local conditions, and only the
one-parameter filtration `ν` is used rather than the two-parameter refinement `τ = (i,j)`).

In one respect the statement below is *stronger* than the paper's: the paper only uses the
canonical operator structure on the free pro-`p` `G`-operator group `F^(n)` (its action on the
basis `x_{i,g}`), whereas a formalisation has no canonical `F^(n)` with a fixed `G`-action, so the
action has to be part of the data: `GenericKernelSolvable` quantifies over *all* actions `ρ` of `G`
on `FreeGroup (Fin n)` and their descents `Φ`.  This is the form `Work.ProP` provides (its
equivariant generic-kernel corollary is stated for an arbitrary `ρ`), and it is exactly the form
the reduction consumes: the reduction produces `(ρ, Φ)` from the given finite `G`-operator
`p`-group and applies the hypothesis to that pair.

## Main definitions

* `Work.GenericKernelReduction.IsDescendedAction` : the predicate that `Φ` is the action on
  `F^(n)/F^(n)(ν)` induced by `ρ` on `F^(n)`.
* `Work.GenericKernelReduction.GenericKernelSolvable` : **the hypothesis**, the prime-by-prime
  generic-kernel split embedding theorem over `ℚ` without local conditions.
-/

import Mathlib
import Submission.ClassicalRoute
import Submission.Work.ProP.All
import Submission.Work.Fitting.SplitEmbedding
import Submission.Work.Fitting.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GenericKernelReduction

open scoped Classical

/-- `IsDescendedAction p n ν ρ Φ` says that the action `Φ` of a group `G` on the generic kernel
quotient `F^(n)/F^(n)(ν)` (`Work.ProP.FreePQuotient p n ν`) is the one induced by the action `ρ`
of `G` on the free group `F^(n) = FreeGroup (Fin n)`: the class of `x` is sent to the class of
`ρ g x`.  (The existence of such a `Φ` for every `ρ` is
`Work.ProP.exists_freePQuotientAction`.) -/
def IsDescendedAction {G : Type*} [Group G] (p n ν : ℕ)
    (ρ : G →* MulAut (FreeGroup (Fin n)))
    (Φ : G →* MulAut (Work.ProP.FreePQuotient p n ν)) : Prop :=
  ∀ (g : G) (x : FreeGroup (Fin n)),
    Φ g (Work.ProP.freePQuotientMk p n ν x)
      = Work.ProP.freePQuotientMk p n ν (ρ g x)

/-- The descended action always exists: a restatement of
`Work.ProP.exists_freePQuotientAction` in the vocabulary of `IsDescendedAction`. -/
theorem exists_descendedAction {G : Type*} [Group G] (p n ν : ℕ)
    (ρ : G →* MulAut (FreeGroup (Fin n))) :
    ∃ Φ : G →* MulAut (Work.ProP.FreePQuotient p n ν), IsDescendedAction p n ν ρ Φ :=
  Work.ProP.exists_freePQuotientAction p n ν ρ

/-- **The generic-kernel hypothesis over `ℚ`.**

For every finite Galois extension `L/ℚ` inside `AlgebraicClosure ℚ` (with group `G = Gal(L/ℚ)`),
every prime `p`, all `n ν : ℕ`, every action `ρ` of `G` on the free group `F^(n) = FreeGroup (Fin n)`
and every descended action `Φ` of `G` on the generic kernel `F^(n)/F^(n)(ν)` (in the sense of
`IsDescendedAction`), the split embedding problem
`1 → F^(n)/F^(n)(ν) → (F^(n)/F^(n)(ν)) ⋊[Φ] G → G → 1` over `ℚ` has a *proper solution*
(`Work.Fitting.SplitEmbeddingSolvable`).

This is Theorem 15 of Schmidt–Wingberg for the base field `ℚ`, *without* its local conditions
(i) and (ii) (see the module docstring); it is the single deep input consumed by
`GenericKernelReduction.splitEmbeddingTheoremOverRat_of_genericKernel`. -/
def GenericKernelSolvable : Prop :=
  ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (p : ℕ) [Fact p.Prime] (n ν : ℕ)
    (ρ : (L ≃ₐ[ℚ] L) →* MulAut (FreeGroup (Fin n)))
    (Φ : (L ≃ₐ[ℚ] L) →* MulAut (Work.ProP.FreePQuotient p n ν)),
    IsDescendedAction p n ν ρ Φ →
    Work.Fitting.SplitEmbeddingSolvable L (Work.ProP.FreePQuotient p n ν) Φ


/-! ## The closure form of a proper solution

A proper solution of a split embedding problem is an *abstract* finite Galois extension `L'/ℚ` of
`L` together with an isomorphism `G ≃* Gal(L'/ℚ)`.  To *combine* the solutions belonging to the
Sylow subgroups of a nilpotent kernel (the step of the reduction of Theorem 14 that passes from a
single prime to all primes) the solutions have to live in a *common* field, namely a fixed
algebraic closure `AlgebraicClosure ℚ` of `ℚ` containing `L`.  The predicate below is the
corresponding refinement of `Work.Fitting.SplitEmbeddingSolvable`. -/

/-- `SplitEmbeddingSolvedInClosure L N φ` says that the split embedding problem
`1 → N → N ⋊[φ] Gal(L/ℚ) → Gal(L/ℚ) → 1` has a proper solution *inside the fixed algebraic
closure* `AlgebraicClosure ℚ`: there is a finite Galois extension `M/ℚ` inside `AlgebraicClosure ℚ`
with `L ≤ M`, `M/L` Galois, and an isomorphism `N ⋊[φ] Gal(L/ℚ) ≃* Gal(M/ℚ)` whose composite with
the restriction to `L` (i.e. with `algebraMap`) is the canonical projection
`SemidirectProduct.rightHom`.

This is the same data as `Work.Fitting.SplitEmbeddingSolvable`, with the extra requirement that
the field `M` be a subfield of `AlgebraicClosure ℚ` containing `L`.  The two are equivalent
(`splitEmbeddingSolvable_of_inClosure` below is the trivial direction;
`inClosure_of_splitEmbeddingSolvable` is the other one). -/
def SplitEmbeddingSolvedInClosure (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (N : Type*) [Group N] [Finite N]
    (φ : (L ≃ₐ[ℚ] L) →* MulAut N) : Prop :=
  ∃ (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : L ≤ M)
    (_ : FiniteDimensional ℚ M) (_ : IsGalois ℚ M)
    (_ : Algebra ↥L ↥M) (_ : IsScalarTower ℚ ↥L ↥M)
    (_ : FiniteDimensional ↥L ↥M) (_ : IsGalois ↥L ↥M),
    ∃ (e : N ⋊[φ] (L ≃ₐ[ℚ] L) ≃* (M ≃ₐ[ℚ] M)), ∀ (g : N ⋊[φ] (L ≃ₐ[ℚ] L)) (x : ↥L),
      e g (algebraMap ↥L ↥M x) = algebraMap ↥L ↥M (SemidirectProduct.rightHom g x)

/-- A solution inside the algebraic closure is a proper solution: this is the trivial direction of
the equivalence between `SplitEmbeddingSolvedInClosure` and `Work.Fitting.SplitEmbeddingSolvable`
(the field `M` is used as the abstract field `L'`). -/
theorem splitEmbeddingSolvable_of_inClosure {L : IntermediateField ℚ (AlgebraicClosure ℚ)}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {N : Type} [Group N] [Finite N]
    {φ : (L ≃ₐ[ℚ] L) →* MulAut N} (h : SplitEmbeddingSolvedInClosure L N φ) :
    Work.Fitting.SplitEmbeddingSolvable L N φ := by
  obtain ⟨M, hLM, hfd, hgal, hAlg, hST, hfdL, hgalL, e, he⟩ := h
  exact ⟨↥M, inferInstance, inferInstance, hfd, hgal, hAlg, hST, hfdL, hgalL, e, he⟩

/-- **The generic-kernel hypothesis in closure form.**  As `GenericKernelSolvable`, but the
solution is required to live inside `AlgebraicClosure ℚ` (i.e. it is a
`SplitEmbeddingSolvedInClosure`).  This is the form in which the hypothesis is used in the body of
the reduction; `GenericKernelSolvable` implies it (the solution of an embedding problem over `ℚ`
can always be realised inside a fixed algebraic closure of `ℚ`, see
`inClosure_of_splitEmbeddingSolvable`). -/
def GenericKernelSolvableInClosure : Prop :=
  ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (p : ℕ) [Fact p.Prime] (n ν : ℕ)
    (ρ : (L ≃ₐ[ℚ] L) →* MulAut (FreeGroup (Fin n)))
    (Φ : (L ≃ₐ[ℚ] L) →* MulAut (Work.ProP.FreePQuotient p n ν)),
    IsDescendedAction p n ν ρ Φ →
    SplitEmbeddingSolvedInClosure L (Work.ProP.FreePQuotient p n ν) Φ

/-! ## Product actions

The reduction of Theorem 14 for a nilpotent kernel `N` from its Sylow subgroups needs the product
of the actions on the factors. -/

/-- The action of a group `G` on a product of two `G`-operator groups induced by the actions on
the two factors: `g • (a, b) = (g • a, g • b)`. -/
noncomputable def prodAction {G : Type*} [Group G] {A B : Type*} [Group A] [Group B]
    (φA : G →* MulAut A) (φB : G →* MulAut B) : G →* MulAut (A × B) where
  toFun g :=
    { toFun := fun x => (φA g x.1, φB g x.2)
      invFun := fun x => ((φA g).symm x.1, (φB g).symm x.2)
      left_inv := by rintro ⟨a, b⟩; simp
      right_inv := by rintro ⟨a, b⟩; simp
      map_mul' := by rintro ⟨a, b⟩ ⟨c, d⟩; simp [map_mul] }
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨a, b⟩ := x
    simp
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨a, b⟩ := x
    simp [MulAut.mul_apply, map_mul]

@[simp]
theorem prodAction_apply {G : Type*} [Group G] {A B : Type*} [Group A] [Group B]
    (φA : G →* MulAut A) (φB : G →* MulAut B) (g : G) (x : A × B) :
    prodAction φA φB g x = (φA g x.1, φB g x.2) := rfl

/-- The action of a group `G` on a product `∀ i, A i` of `G`-operator groups, induced
componentwise. -/
noncomputable def piAction {G : Type*} [Group G] {ι : Type*} {A : ι → Type*}
    [∀ i, Group (A i)] (φ : ∀ i, G →* MulAut (A i)) : G →* MulAut (∀ i, A i) where
  toFun g :=
    { toFun := fun x i => φ i g (x i)
      invFun := fun x i => (φ i g).symm (x i)
      left_inv := by intro x; funext i; simp
      right_inv := by intro x; funext i; simp
      map_mul' := by intro x y; funext i; simp [map_mul] }
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    funext i
    simp
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    funext i
    simp [MulAut.mul_apply, map_mul]

@[simp]
theorem piAction_apply {G : Type*} [Group G] {ι : Type*} {A : ι → Type*} [∀ i, Group (A i)]
    (φ : ∀ i, G →* MulAut (A i)) (g : G) (x : ∀ i, A i) (i : ι) :
    piAction φ g x i = φ i g (x i) := rfl


/-! ## Turning a homomorphism `G →* MulAut M` into a `MulDistribMulAction`

Mathlib's `MulDistribMulAction.compHom` produces *an* action from a homomorphism into `MulAut`,
but its `MulDistribMulAction.toMulAut` is only propositionally equal to the original
homomorphism.  The construction below is definitionally the given homomorphism:
`(mdmaOfHom φ).toMulAut = φ`.  This is what lets one translate between
`MulDistribMulAction`-flavoured statements (as in `Work.ProP`) and `⋊[φ]`-flavoured ones. -/

/-- The `G`-operator-group structure on `M` whose induced automorphism of `M` at `g` is `φ g`,
definitionally. -/
@[reducible] def mdmaOfHom {G M : Type*} [Group G] [Monoid M] (φ : G →* MulAut M) :
    MulDistribMulAction G M :=
  { MulAction.compHom M φ with
    smul_one := fun g => map_one (φ g)
    smul_mul := fun g a b => map_mul (φ g) a b }

/-- The automorphism induced by `mdmaOfHom φ` at `g` is `φ g`. -/
theorem toMulAut_mdmaOfHom {G M : Type*} [Group G] [Monoid M] (φ : G →* MulAut M) :
    @MulDistribMulAction.toMulAut G M _ _ (mdmaOfHom φ) = φ := by
  ext g m
  rw [MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
  rfl

/-- The scalar multiplication of `mdmaOfHom φ` is evaluation of `φ`. -/
theorem mdmaOfHom_smul {G M : Type*} [Group G] [Monoid M] (φ : G →* MulAut M) (g : G) (m : M) :
    letI : MulDistribMulAction G M := mdmaOfHom φ
    g • m = φ g m := rfl

end Work.GenericKernelReduction
