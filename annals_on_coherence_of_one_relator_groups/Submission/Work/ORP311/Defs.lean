/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (JZLA20 Proposition 3.11 in the concrete `U(G)`)

# JZLA20 Proposition 3.11 in the concrete `U(G)`: the "`1 + A·t` is invertible" property

This file fixes the vocabulary of the ORP311 area.  We work with the **concrete** envelope
`U(G)` of a countable group `G`, i.e. the algebra of operators affiliated to the group von
Neumann algebra `N(G) = ρ(G)' ⊆ B(ℓ²(G))`, as constructed by the N5 area
(`Work.ORVonNeumann.countableStarRegularEnvelope`, whose every field is a theorem).  In
particular we do **not** use the `Classical.choice` envelope.

Notation, for subgroups `N ≤ H ≤ G` and `t ∈ H`:

* `phiN N : ℂ[↥N] →+* U(G)` is the composite `ℂ[↥N] → ℂ[G] → U(G)`;
* `closureCN N = U_N` is the `∗`-regular closure of the image of `ℂ[↥N]` in `U(G)`
  (JZLA20 §3.1: the smallest `∗`-regular `∗`-subring containing it); since `U(N) ⊆ U(G)`
  is a `∗`-regular `∗`-subring containing that image, `U_N ⊆ U(N)`;
* `IsExtensionByZ H N t` is the hypothesis `H = N ⋊ ⟨t⟩` with `t` of infinite order modulo
  `N`, i.e. `∀ h : H, ∃ n : N, ∃ k : ℤ, h = n * t ^ k` and `t ^ k ∈ N → k = 0`.

The main object of the area is

* `Prop311 (G)`: **JZLA20, Proposition 3.11** (in the form used by the route design, i.e. the
  "`1 + A·t` is invertible" property of `U(G)`, equivalently the Hughes-freeness of the
  enveloping rank function): for every `H : Subgroup G`, `N : Subgroup G` with `N ≤ H` and `N`
  normal in `H` (so `N.subgroupOf H` is normal in `↥H`), `t : ↥H` with `H = N ⋊ ⟨t⟩`, every
  `n` and every `A : Mₙ(U_N)` over the `∗`-regular closure `U_N` of `ι(ℂ[N])` in `U(G)`,

  `1 + A · ι t` is a unit of `Mₙ(U(G))`.

* `Core311 (G)`: the same with `A` ranging over all of `U(N)` (stronger, since `U_N ⊆ U(N)`);
  this is the form in which the analytic argument is carried out.

This is the analytic input of JZLA20 Theorem 6.1 and it is *not* implied by Linnell
independence alone; the reduction and the proof are developed in the sibling modules.
-/
import Mathlib
import Submission.Work.ORVonNeumann.CountableEnvelope
import Submission.Work.ORVonNeumann.Envelope
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.Instances
import Submission.Work.ORHughesFree.StarRegular.starRegularClosure_le

set_option autoImplicit false

universe u

namespace Work.ORP311

open Work.ORVonNeumann

variable {G : Type u}

/-- **The concrete envelope `U(G)`.**  This is the N5 area's unconditional construction from
the group von Neumann algebra `N(G) = ρ(G)' ⊆ B(ℓ²(G))`; every field of the structure is a
theorem.  The measurable structure is the counting `σ`-algebra. -/
noncomputable abbrev concreteEnvelope (G : Type u) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] : StarRegularEnvelope G :=
  Work.ORVonNeumann.countableStarRegularEnvelope

/-- **Vocabulary bridge (N5 → N6)**, general form: `Work.ORVonNeumann.IsStarRegularRing`
(von Neumann regular plus a *right-handed* proper involution) implies
`Work.ORHughesFree.IsStarRegular` (the same with left-handed properness).  The only content is
the handedness.

(Compare `Work.ORDivLoc.isStarRegular_of_isStarRegularRing`, the same bridge in the
`ORDivLoc` area.) -/
theorem isStarRegular_of_isStarRegularRing {R : Type*} [Ring R] [StarRing R]
    (h : Work.ORVonNeumann.IsStarRegularRing R) : Work.ORHughesFree.IsStarRegular R where
  vonNeumannRegular := ⟨fun x => h.1 x⟩
  proper := fun x hx => by
    have hy : star x = 0 := h.2 (star x) (by simpa using hx)
    calc x = star (star x) := (star_star x).symm
      _ = star 0 := by rw [hy]
      _ = 0 := by simp

/-- **Vocabulary bridge (N5 → N6)** for the concrete envelope: the whole
`Work.ORHughesFree` closure calculus (`starRegularClosure`, `starRegularChain`,
`IsRelativeInverse`, …) applies to `U(G)`. -/
instance instIsStarRegularConcreteU (G : Type u) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] : Work.ORHughesFree.IsStarRegular
      (concreteEnvelope G).U :=
  isStarRegular_of_isStarRegularRing (concreteEnvelope G).starRegular

/-- **Vocabulary bridge (N5 → N6)**, positive definiteness: `U(G)` is positive definite in
the sense of the JZLA20 engine. -/
theorem isPositiveDefiniteStarRegular_concreteU (G : Type u) [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] :
    Work.ORHughesFree.IsPositiveDefiniteStarRegular (concreteEnvelope G).U :=
  fun n => isStarRegular_of_isStarRegularRing ((concreteEnvelope G).posDef.2 n)

/-- The structure map `ℂ[G] →+* U(G)` of the concrete envelope, isolated so that statements
read as `ι (single t 1)` rather than as a projection out of a structure. -/
noncomputable def iota (G : Type u) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] :
    MonoidAlgebra ℂ G →+* (concreteEnvelope G).U :=
  (concreteEnvelope G).ι

@[simp]
theorem iota_apply (G : Type u) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (x : MonoidAlgebra ℂ G) :
    iota G x = (concreteEnvelope G).ι x := rfl

section Basic

variable [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The composite `ℂ[↥N] → ℂ[G] → U(G)`. -/
noncomputable def phiN (N : Subgroup G) :
    MonoidAlgebra ℂ ↥N →+* (concreteEnvelope G).U :=
  (iota G).comp (MonoidAlgebra.mapDomainRingHom ℂ N.subtype)

/-- **The `∗`-regular closure `U_N`** of the image of `ℂ[↥N]` in `U(G)`
(JZLA20, §3.1).  It is the smallest `∗`-regular `∗`-subring of `U(G)` containing the image
of `ℂ[↥N]`; in particular `U_N ⊆ U(N)`. -/
noncomputable def closureCN (N : Subgroup G) :
    Work.ORHughesFree.StarSubring (concreteEnvelope G).U :=
  Work.ORHughesFree.starRegularClosure
    (Work.ORHughesFree.starSubringClosure (Set.range (phiN N)))

/-- The carrier of `U_N`. -/
abbrev closureCNty (N : Subgroup G) : Type u :=
  ↥(closureCN N)

instance instIsStarRegularClosureCN (N : Subgroup G) :
    Work.ORHughesFree.IsStarRegular (closureCNty N) :=
  Work.ORHughesFree.instIsStarRegularStarRegularClosure _

/-- Membership in `U_N`: everything in the image of `ℂ[↥N]` lies in `U_N`. -/
theorem mem_closureCN {N : Subgroup G} {x : (concreteEnvelope G).U}
    (hx : x ∈ Set.range (phiN N)) : x ∈ (closureCN N : Set (concreteEnvelope G).U) :=
  Work.ORHughesFree.subset_starRegularClosure _
    (Work.ORHughesFree.subset_starSubringClosure _ hx)

/-- `U_N` is contained in every `∗`-regular `∗`-subring of `U(G)` containing the image of
`ℂ[↥N]`; in particular `U_N ⊆ U(N)`. -/
theorem closureCN_le {N : Subgroup G}
    {S : Work.ORHughesFree.StarSubring (concreteEnvelope G).U}
    [Work.ORHughesFree.IsStarRegular S]
    (h : Set.range (phiN N) ⊆ (S : Set (concreteEnvelope G).U)) :
    (closureCN N : Set (concreteEnvelope G).U) ⊆ (S : Set (concreteEnvelope G).U) :=
  Work.ORHughesFree.StarRegular.starRegularClosure_le
    (R := Work.ORHughesFree.starSubringClosure (Set.range (phiN N))) (S := S)
    (Work.ORHughesFree.starSubringClosure_le h)

/-- The inclusion `U_N ⊆ U(G)`, as a ring homomorphism. -/
noncomputable def closureCN.subtype (N : Subgroup G) :
    closureCNty N →+* (concreteEnvelope G).U :=
  (closureCN N).toSubring.subtype

@[simp]
theorem closureCN.subtype_apply (N : Subgroup G) (x : closureCNty N) :
    closureCN.subtype N x = (x : (concreteEnvelope G).U) := rfl

/-- The element `1 + A · ι t` of `Mₙ(U(G))`, for `A` a matrix over `U_N`: the shape whose
invertibility is asserted by `Prop311`. -/
noncomputable def onePlusCT (H N : Subgroup G) (t : ↥H) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (closureCNty N)) :
    Matrix (Fin n) (Fin n) (concreteEnvelope G).U :=
  1 + A.map (closureCN.subtype N) *
    Matrix.scalar (Fin n) (iota G (MonoidAlgebra.single (t : G) 1))

/-- The `U_N`-polynomial `∑_{k ≤ m} φ(B_k) · ι(t)^k` of `Mₙ(U(G))`: the shape of the elements
against which the finite-support form of Proposition 3.11 is applied. -/
noncomputable def polyElt (H N : Subgroup G) (t : ↥H) {n : ℕ} {m : ℕ}
    (B : Fin (m + 1) → Matrix (Fin n) (Fin n) (closureCNty N)) :
    Matrix (Fin n) (Fin n) (concreteEnvelope G).U :=
  ∑ k : Fin (m + 1), (B k).map (closureCN.subtype N) *
    Matrix.scalar (Fin n)
      (iota G (MonoidAlgebra.single (((t ^ ((k : ℕ) : ℤ)) : ↥H) : G) 1))

end Basic

/-- **The hypothesis `H = N ⋊ ⟨t⟩` with `t` of infinite order modulo `N`.**  The first
component says that every element of `H` is `n * t ^ k` with `n ∈ N` and `k ∈ ℤ`; the second
that no nonzero power of `t` lies in `N`, so that the cosets `N * t ^ k` are pairwise
distinct. -/
def IsExtensionByZ (H : Type u) [Group H] (N : Subgroup H) (t : H) : Prop :=
  (∀ h : H, ∃ n : N, ∃ k : ℤ, h = (n : H) * t ^ k) ∧ (∀ k : ℤ, t ^ k ∈ N → k = 0)

/-- **JZLA20, Proposition 3.11** (the form needed by the route design: the "`1 + A·t` is
invertible" property of the concrete `U(G)`).

For `N ≤ H ≤ G` with `N` normal in `H`, `t : ↥H` with `H = N ⋊ ⟨t⟩` (and `t` of infinite
order modulo `N`), every `n` and every `A : Mₙ(U_N)` over the `∗`-regular closure `U_N` of
`ι(ℂ[N])` in `U(G)`,

`1 + A · ι (single t 1)` is a unit of `Mₙ(U(G))`.

Equivalently (JZLA20 §3.2, and the form in which the N6 area consumes it), the enveloping
rank function of `U(G)` is Hughes-free. -/
def Prop311 (G : Type u) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] : Prop :=
  ∀ (H N : Subgroup G) (hNH : N ≤ H) [hN : (N.subgroupOf H).Normal] (t : ↥H),
    IsExtensionByZ ↥H (N.subgroupOf H) t →
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (closureCNty N)),
      IsUnit (1 + A.map (closureCN.subtype N) *
        Matrix.scalar (Fin n) (iota G (MonoidAlgebra.single (t : G) 1)))

/-- **The analytic core of Proposition 3.11**, in the *reduced* form: the `1 + A·t` property
with `A` ranging over the canonical `U(N)` (the N5 envelope-inclusion data
`(concreteEnvelope G).sub N = (U(N) ↪ U(G))`) rather than only over the `∗`-regular closure of
`ℂ[N]`.  Since `U_N ⊆ U(N)`, this statement is *stronger* than `Prop311`, and
`prop311_of_core311` reduces `Prop311` to it.

**WARNING (2026-10-02).**  This statement is *not the right intermediate and is not provable
as written*: `(concreteEnvelope G).sub N` is `Classical.choice (envelopeInclusionGeneral N)`,
an opaque element of the structure type, so `V` and `φ` cannot be identified with the concrete
`U(N) ⊆ U(G)`, and the fields of `EnvelopeInclusion` do not by themselves imply the conclusion
(a counterexample model is recorded in `Submission/Work/ORP311/core311_envelope.lean` and in
`NOTES.md`).  Keep the definition only as a record; do not route new proofs through it. -/
def Core311 (G : Type u) [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] : Prop :=
  ∀ (H N : Subgroup G) (hNH : N ≤ H) [hN : (N.subgroupOf H).Normal] (t : ↥H),
    IsExtensionByZ ↥H (N.subgroupOf H) t →
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ((concreteEnvelope G).sub N).V),
      IsUnit (1 + A.map ((concreteEnvelope G).sub N).φ *
        Matrix.scalar (Fin n) (iota G (MonoidAlgebra.single (t : G) 1)))

end Work.ORP311
