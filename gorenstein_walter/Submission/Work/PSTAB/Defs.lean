/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.GLUE.Defs

set_option autoImplicit false

open scoped MatrixGroups
open Subgroup

/-!
# AREA PSTAB — `p`-stability of D-groups (Glauberman Lemma 6.3, (a) ⇒ (b))

This is the definition module of the area `PSTAB` of the `gorenstein_walter` project
(route: Bender 1981 + Bender–Glauberman 1981, Feit–Thompson available).

The **deliverable** is

* `Work.GW2.pStable : Work.GW2.PStableProp`  ("`Qd(p)` is not involved, hence `p`-stable")

where `Work.GW2.PStableProp` is the contract statement of
`Submission/Work/_design_gw/Contracts2.lean`:

```
def PStableProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → DihOrCycSylow X →
    IsPStable' p X
```

Everything the contract's `PStableProp` mentions — `Work.GW2.pCore`, `Work.GW2.IsPStable'`,
`Work.GW2.DihOrCycSylow`, `Work.GW2.PStableProp` — is the verbatim copy of the contract file
that the area `GLUE` maintains in `Submission/Work/GLUE/Defs.lean` (namespace `Work.GW2`); this
area imports it rather than duplicating the names.  The definitions added *here* are the two
lemma-level contracts of `Submission/Work/_design_gw/Core2.lean` §B, which belong to this area:

* `Work.GW2.NoQuaternionSectionProp`  (design2 §3 Step 1),
* `Work.GW2.QuadPairProp`             (design2 §3 Step 2, verbatim),

together with the working vocabulary of the area (`Work.PSTAB.NoBadSection`,
`Work.PSTAB.IsCyclicOrDihedral`, `Work.PSTAB.QuadPairIrrProp`), see the docstrings below.

## Route (design2 §3)

* **Step 1** `NoQuaternionSectionProp`: a Sylow 2-subgroup of a section of `X` is a section of
  a Sylow 2-subgroup of `X`; subgroups and quotients of a cyclic or dihedral 2-group are cyclic
  or dihedral; none of these has a noncyclic 2-subgroup with a unique involution.
* **Step 2** `QuadPairIrrProp` (the irreducible-strength form of `QuadPairProp` that the
  argument actually produces, and the form used in Step 3): Baer–Suzuki produces `g` with
  `D = ⟨x, x^g⟩` not a `p`-group; BG Appendix A (`thmA2`,
  `quadratic_two_generated_irreducible_finrank_eq_two`) applied after the base change to the
  algebraic closure of the self-intertwiner field (`isAbsolutelyIrreducible_overEnd`) gives
  `dim = 2` and `D ≤ SL₂`; `−1` is the unique involution of `SL₂`, so a Sylow 2-subgroup of `D`
  is cyclic or generalized quaternion, and Burnside rules out cyclic.
* **Step 3** `PStableProp`: the characteristic series of `K` has elementary abelian `p`-factors
  `Vᵢ` on which `a` acts quadratically; the kernel of the action of `X/C_X(K)` on all the `Vᵢ`
  is a normal `p`-subgroup, hence some factor `Lᵢ` has `āᵢ ∉ O_p(Lᵢ)`; Step 2 applied to the
  faithful irreducible factor `Lᵢ ↷ Vᵢ` produces a forbidden section of `X`, contradicting
  Step 1.

## Conventions

All contract statements live in namespace `Work.GW2`; the area's own vocabulary lives in
namespace `Work.PSTAB`.  Nothing under `Submission/OddOrder/` is edited; results there are
cited by name.
-/

namespace Work.GW2

/-- A finite group with dihedral or cyclic Sylow 2-subgroups has no section containing `Q₈`.
Stated as: no subgroup `K`, normal `N ≤ K`, and subgroup of `K ⧸ N` with a unique involution
that is not cyclic, among 2-groups.

(Verbatim from `Submission/Work/_design_gw/Core2.lean` §B.) -/
def NoQuaternionSectionProp : Prop :=
  ∀ (X : Type) [Group X] [Finite X], DihOrCycSylow X →
    ∀ (K : Subgroup X) (N : Subgroup K) [N.Normal] (Q : Subgroup (K ⧸ N)),
      IsPGroup 2 Q → ¬ IsCyclic Q → ¬ ∃! z : Q, orderOf z = 2

/-- Quadratic-pair lemma (replaces Glauberman L6.2 / Dickson).
* `L` acts faithfully on a finite `𝔽_p`-space `V` (p odd).
* `x ∈ L` is a `p`-element acting quadratically, with `x ∉ O_p(L)`.
* Then `L` has a 2-subgroup that is noncyclic with a unique involution.
Route: Baer–Suzuki, a composition factor of `⟨x, x^g⟩`, BG App. A
`quadratic_two_generated_irreducible_finrank_eq_two` and `thmA2`, SL₂ has unique involution `-1`,
Burnside.

(Verbatim from `Submission/Work/_design_gw/Core2.lean` §B.) -/
def QuadPairProp : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      (ρ : Representation (ZMod p) L V), Function.Injective ρ →
    ∀ x : L, IsPGroup p (zpowers x) → ((ρ x : Module.End (ZMod p) V) - 1) ^ 2 = 0 →
      x ∉ pCore p L →
      ∃ Q : Subgroup L, IsPGroup 2 Q ∧ ¬ IsCyclic Q ∧ ∃! z : Q, orderOf z = 2

end Work.GW2

namespace Work.PSTAB

/-! ## The area's own vocabulary -/

/-- `T` has no section that is a noncyclic 2-group with a unique involution.  This is the
conclusion `¬ …` of `Work.GW2.NoQuaternionSectionProp`, packaged as a predicate so that it can
be passed around. -/
def NoBadSection (T : Type*) [Group T] : Prop :=
  ∀ (K : Subgroup T) (N : Subgroup K) [N.Normal] (Q : Subgroup (K ⧸ N)),
    IsPGroup 2 Q → ¬ IsCyclic Q → ¬ ∃! z : Q, orderOf z = 2

/-- `T` is cyclic or (isomorphic to) a dihedral group.  `DihedralGroup 0` is infinite
dihedral, `DihedralGroup 1` is cyclic of order `2` and `DihedralGroup 2` is the Klein
four-group. -/
def IsCyclicOrDihedral (T : Type*) [Group T] : Prop :=
  IsCyclic T ∨ ∃ n : ℕ, Nonempty (T ≃* DihedralGroup n)

/-- `IsCyclicOrDihedral` is exactly the `Prop` appearing in `Work.GW2.DihOrCycSylow`. -/
theorem isCyclicOrDihedral_iff {T : Type*} [Group T] :
    IsCyclicOrDihedral T ↔ IsCyclic T ∨ ∃ n : ℕ, Nonempty (T ≃* DihedralGroup n) :=
  Iff.rfl

/-- **The `2`-structurer of a cyclic or dihedral group, in the weak form used by PSTAB.**

`DihCycShape T` holds if there is a normal cyclic subgroup `R` such that the complement `T \ R`
consists of involutions and is closed under products: equivalently `T/R` has at most two
elements, every element outside `R` is an involution, and `R` is cyclic.  For `T` cyclic take
`R = ⊤`; for `T = DihedralGroup n` take `R = ⟨r 1⟩` (the rotation subgroup: index `2`, and every
element outside it is a reflection of order `2`).

This is deliberately weaker than "`T` is cyclic or dihedral" — it is closed under subgroups and
under quotients, which is all that the argument of `NoQuaternionSectionProp` uses, and it is far
cheaper to establish. -/
def DihCycShape (T : Type*) [Group T] : Prop :=
  ∃ R : Subgroup T, R.Normal ∧ IsCyclic ↥R ∧
    (∀ g : T, g ∉ R → g ^ 2 = 1) ∧
    (∀ g h : T, g ∉ R → h ∉ R → g * h ∈ R)

/-- **The irreducible quadratic-pair lemma** — the working form of `Work.GW2.QuadPairProp`.

`L` acts faithfully and *irreducibly* on a finite `𝔽_p`-space `V` (with `p` odd), and `x ∈ L`
is a `p`-element acting quadratically with `ρ x ≠ 1`; then `L` has a 2-subgroup that is
noncyclic with a unique involution.

(Note the two differences from the contract's `Work.GW2.QuadPairProp`: `V` is required to be
`L`-irreducible, which is what the proof of the quadratic-pair lemma actually uses — and which
holds for every chief factor in Step 3 — and the hypothesis `x ∉ O_p(L)` is replaced by
`ρ x ≠ 1`, its equivalent under faithfulness + irreducibility.) -/
def QuadPairIrrProp : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      (ρ : Representation (ZMod p) L V), Function.Injective ρ →
      (∀ (W : Submodule (ZMod p) V),
        (∀ g : L, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) →
    ∀ x : L, IsPGroup p (zpowers x) → ((ρ x : Module.End (ZMod p) V) - 1) ^ 2 = 0 →
      ρ x ≠ 1 →
      ∃ Q : Subgroup L, IsPGroup 2 Q ∧ ¬ IsCyclic Q ∧ ∃! z : Q, orderOf z = 2

/-- **The section-strength irreducible quadratic-pair lemma** (design pass 11, §4 fallback).

Same hypotheses as `QuadPairIrrProp`, but the conclusion is only that `L` has a *section* that
is a noncyclic `2`-group with a unique involution.  This is what the single-composition-factor
argument with `Work.PSTAB.UnipotentSL2` delivers; `QuadPairIrrProp` additionally requires
assembling the factors into a subdirect product and lifting back through the (odd-order) kernel
on all factors. -/
def QuadPairIrrSectionProp : Prop :=
  ∀ (L : Type*) [Group L] [Finite L] (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ (V : Type*) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      (ρ : Representation (ZMod p) L V), Function.Injective ρ →
      (∀ (W : Submodule (ZMod p) V),
        (∀ g : L, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) →
    ∀ x : L, IsPGroup p (Subgroup.zpowers x) → ((ρ x : Module.End (ZMod p) V) - 1) ^ 2 = 0 →
      ρ x ≠ 1 → ¬ NoBadSection L

/-- **Sections of a quotient are sections.**  If `M` has no bad section then neither does any
quotient `M ⧸ C`. -/
def BadSectionOfQuotientProp : Prop :=
  ∀ {M : Type*} [Group M] [Finite M] (C : Subgroup M) [C.Normal],
    NoBadSection M → NoBadSection (M ⧸ C)

end Work.PSTAB
