/-
# `annAt` from the paper's Lemma 5.1′ (node N8, `Work.ORTorsion`)

The paper *On the coherence of one-relator groups and their group algebras* (Jaikin-Zapirain--Linton,
Annals 2025) proves the statement "the Fox component of the root is a non-zero-divisor" — JL Claim
5.9 together with Lemma 5.1 — through the **division closure** `D = D_{K[G̅]}` of the group algebra
in the algebra of affiliated operators:

* JL Claim 5.9 (`nontrivial3`): for the root `u` of a one-relator group and a letter `x`, the
  *support* of the Fox derivative `∂u/∂x` consists of group elements with pairwise distinct images in
  the quotient `G̅ = G/⟨⟨u⟩⟩` (this is Weinbaum's subword theorem);
* JL Lemma 5.1 (`injectiveaction`, formalised as **`Work.ORTorsion.torsionFree_tensor`**): an element
  `β ∈ K[G]` whose support maps injectively into `G̅` acts **injectively** on `V ⊗_K D` for every
  suitable module `V`.

This file carries out the (entirely ring-theoretic) passage from those two inputs to the workspace's
annihilator predicate `Work.ORLyndon.annAt`, hence to the `MagnusDescent` half of
`Work.ORLyndon.EpsNeZeroDescent`:

* `Work.ORLyndon.annAt_of_torsionData` — **the main theorem**: if `L : TorsionData K G U` is a
  torsion datum for the one-relator group `G = ⟨α | r = u^l⟩` whose root is the class of `u`, and if
  `β = rootVec K r u x` is non-zero with support injective in `G ⧸ ⟨⟨L.u⟩⟩`, then `β` is a *right*
  non-zero-divisor of `K[G]`;
* `Work.ORLyndon.annAt_of_torsionData_of_charZero` — the same, with the non-vanishing of `β` read
  off from `eps x u ≠ 0` in characteristic zero (`Work.ORLyndon.augmentation_rootVec`);
* `Work.ORLyndon.magnusDescent_of_torsionData` — the consequence in the shape in which the descent
  of `Submission/Work/ORLyndon/annChain.lean` consumes it.

## The three ingredients

1. `Work.ORLyndon.genTopAlg` — the algebra map `K[G] → D(⊤)` induced by `L.gen`.  It is **injective**
   (`Work.ORLyndon.algHomD_top_injective`, from the Linnell-independence field of the interface):
   this is what lets a statement about `D(⊤)` be pulled back to `K[G]`.
2. `Work.ORLyndon.leftRegular_of_injective_diagTriv` — `torsionFree_tensor` at the trivial module
   `V = K` (on which `K[G]` acts through the augmentation, `Work.ORLyndon.trivModule`) says exactly
   that `genTopAlg β` is a *left* non-zero-divisor of `D(⊤)`.
3. `Work.ORLyndon.rightRegular_of_leftRegular_isSemisimple` — in the semisimple ring `D(⊤)`
   (field `semisimple` of the interface) a left non-zero-divisor is a unit, hence a right
   non-zero-divisor; this is the step that converts the left-action statement of Lemma 5.1 into the
   right-divisibility needed by `Work.ORLyndon.annAt`.

## Scope and the two remaining inputs of the paper's route

The passage above is characteristic-free, but the *interface* `TorsionData` is satisfiable only in
residue characteristic coprime to the torsion of the division closures (its `semisimple` field is
Maschke).  In particular this route proves `annAt` for fields of characteristic `0`; in
characteristic `p` the truth of the residual rests on the Karrass--Magnus--Solitar torsion theorem
("every torsion element of `⟨α | u^l⟩` is conjugate to a power of `u`"), which rules out the
norm-element zero divisors `1 ± of g` with `orderOf g` divisible by `p`.  The second input,
Weinbaum's subword theorem for the support of `∂u/∂x`, is a hypothesis (`hβ`) of the theorems below;
it is proved in the workspace as `Work.OROneRel.weinbaum_at` /
`Work.ORLyndon.occTerm_distinct` but is not yet importable in this cone (see the import-hygiene
section of `Submission/Work/ORLyndon/NOTES_epsNeZeroDescent_level.md`).
-/
import Mathlib
import Submission.Work.ORLyndon.epsNeZeroDescent
import Submission.Work.ORLyndon.augmentation_rootVec
import Submission.Work.ORTorsion.Main
import Submission.Work.ORLyndon.algHomD_top_injective
import Submission.Work.ORLyndon.leftRegular_of_injective_diagTriv
import Submission.Work.ORLyndon.rightRegular_of_leftRegular_isSemisimple

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v w

variable {K : Type v} [Field K] {G : Type u} [Group G] {U : Type w} [Ring U] [Algebra K U]

/-! ## The algebra map `K[G] → D(⊤)` -/

/-- The `K`-algebra map `K[G] → D(⊤)` induced by the image `L.gen : G →* Uˣ` of the group. -/
noncomputable def genTopAlg (L : Work.ORTorsion.TorsionData K G U) :
    MonoidAlgebra K G →ₐ[K] ↥(L.D ⊤) :=
  MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop

variable (L : Work.ORTorsion.TorsionData K G U) in
theorem genTopAlg_injective [Nontrivial U] : Function.Injective (genTopAlg L) :=
  algHomD_top_injective L

/-! ## The augmentation as a ring homomorphism, and the trivial module `K` -/

/-- The augmentation `K[G] →+* K`, `of g ↦ 1`.  It is `MonoidAlgebra.lift` of the trivial monoid
homomorphism. -/
noncomputable def augHom (K : Type v) [Field K] (G : Type u) [Group G] :
    MonoidAlgebra K G →+* K :=
  (MonoidAlgebra.lift K K G (1 : G →* K)).toRingHom

theorem augHom_single (g : G) (c : K) : augHom K G (single g c) = c := by
  show (MonoidAlgebra.lift K K G (1 : G →* K)) (MonoidAlgebra.single g c) = c
  rw [MonoidAlgebra.lift_single]
  simp

theorem augHom_smul (k : K) (x : MonoidAlgebra K G) : augHom K G (k • x) = k * augHom K G x := by
  show (MonoidAlgebra.lift K K G (1 : G →* K)) (k • x)
      = k * ((MonoidAlgebra.lift K K G (1 : G →* K)) x)
  rw [map_smul, smul_eq_mul]

/-- The **trivial module structure** on `K` over the group algebra `K[G]`, through the augmentation:
`x • c = ε(x) * c`.  This is the module `V = K` at which Lemma 5.1′ (`torsionFree_tensor`) is applied
in `Work.ORLyndon.annAt_of_torsionData`. -/
@[instance_reducible] noncomputable def trivModule (K : Type v) [Field K] (G : Type u) [Group G] :
    Module (MonoidAlgebra K G) K :=
  Module.compHom K (augHom K G)

/-! ## The main theorem -/

/-- **`annAt` from JL Claim 5.9 and Lemma 5.1′.**  Let `L` be a torsion datum for a one-relator
group `G = ⟨α | r⟩` whose root `L.u` is the class of `u` (`r = u ^ l`), let `x : α`, and let
`β = rootVec K r u x ∈ K[G]` be the `x`-component of the Fox vector of the root.  If

* `β ≠ 0`, and
* the support of `β` has pairwise distinct images in `G ⧸ ⟨⟨L.u⟩⟩` (JL Claim 5.9, Weinbaum),

then `β` is a **right non-zero-divisor** of `K[G]`: every `b` with `b * β = 0` vanishes.  This is
`Work.ORLyndon.annAt K r u {x}`. -/
theorem annAt_of_torsionData [Nontrivial U] {α : Type u} [DecidableEq α] {r u : FreeGroup α}
    (L : Work.ORTorsion.TorsionData K (OneRelatorGroup r) U) (hu : L.u = presentRho r u) {x : α}
    (hβ0 : rootVec K r u x ≠ 0)
    (hβ : Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure {L.u}))
      (rootVec K r u x).coeff.support) :
    annAt K r u {x} := by
  intro b hb
  set β : MonoidAlgebra K (OneRelatorGroup r) := rootVec K r u x with hβdef
  letI : Module (MonoidAlgebra K (OneRelatorGroup r)) K := trivModule K (OneRelatorGroup r)
  haveI : IsScalarTower K (MonoidAlgebra K (OneRelatorGroup r)) K := ⟨fun a c d => by
    show augHom K (OneRelatorGroup r) (a • c) * d
        = a * (augHom K (OneRelatorGroup r) c * d)
    rw [augHom_smul, mul_assoc]⟩
  have hone : ∀ g : OneRelatorGroup r,
      (MonoidAlgebra.single g (1 : K) : MonoidAlgebra K (OneRelatorGroup r)) • (1 : K) = 1 := by
    intro g
    show augHom K (OneRelatorGroup r) (MonoidAlgebra.single g (1 : K)) * 1 = 1
    rw [augHom_single, mul_one]
  -- Lemma 5.1′ at the trivial module
  have hinj : Function.Injective
      (fun m : TensorProduct K K (L.D ⊤) => β • m) :=
    Work.ORTorsion.torsionFree_tensor L K β hβ hβ0
  -- `genTopAlg β` is a left non-zero-divisor of `D(⊤)`
  have hleft : ∀ y : (L.D ⊤), genTopAlg L β * y = 0 → y = 0 :=
    leftRegular_of_injective_diagTriv hone L β hinj
  -- in the semisimple ring `D(⊤)` it is then a right non-zero-divisor as well
  haveI : IsSemisimpleRing ↥(L.D ⊤) := L.semisimple ⊤
  have hright : ∀ y : (L.D ⊤), y * genTopAlg L β = 0 → y = 0 :=
    rightRegular_of_leftRegular_isSemisimple hleft
  have hbβ : b * β = 0 := hb x (Set.mem_singleton x)
  have h1 : genTopAlg L b * genTopAlg L β = 0 := by
    change (genTopAlg L).toRingHom b * (genTopAlg L).toRingHom β = 0
    rw [← map_mul, hbβ, map_zero]
  have h2 : genTopAlg L b = 0 := hright _ h1
  exact genTopAlg_injective L (by rw [h2, map_zero])

/-- **`annAt` from the paper's inputs in characteristic zero.**  The non-vanishing of the Fox
component is automatic here: its augmentation is `eps x u ≠ 0`, and `(eps x u : K) ≠ 0` in
characteristic `0` (`Work.ORLyndon.augmentation_rootVec`). -/
theorem annAt_of_torsionData_of_charZero [Nontrivial U] [CharZero K] {α : Type u} [DecidableEq α]
    {r u : FreeGroup α} (L : Work.ORTorsion.TorsionData K (OneRelatorGroup r) U)
    (hu : L.u = presentRho r u) {x : α} (hx : Work.OROneRel.eps x u ≠ 0)
    (hβ : Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure {L.u}))
      (rootVec K r u x).coeff.support) :
    annAt K r u {x} := by
  refine annAt_of_torsionData L hu ?_ hβ
  intro h0
  have h1 := augmentation_rootVec (K := K) r u x
  rw [h0, map_zero] at h1
  refine hx ?_
  have h2 : ((Work.OROneRel.eps x u : ℤ) : K) = 0 := h1.symm
  exact_mod_cast h2

/-- **The `MagnusDescent` half of `Work.ORLyndon.EpsNeZeroDescent` from the paper's inputs.**  If for
a letter `x ∈ S` of a root `u` of relator norm `≥ 2` the hypotheses of `annAt_of_torsionData` hold
for the presentation `⟨α | u ^ l⟩`, then the descent data exists.  (The remaining component of
`EpsNeZeroDescent`, the order statement `orderOf (presentRho (u ^ l) u) = l`, is proved in
`Submission/Work/ORLyndon/orderOf_presentRho_eps_ne_zero.lean`.) -/
theorem magnusDescent_of_torsionData [Nontrivial U] {α : Type u} [DecidableEq α] {u : FreeGroup α}
    {l : ℕ}
    {S : Set α} (hS : S.Nonempty) (hrn : 2 ≤ Work.OROneRel.relatorNorm u) {x : α} (hxS : x ∈ S)
    (L : Work.ORTorsion.TorsionData K (OneRelatorGroup (u ^ l)) U)
    (hu : L.u = presentRho (u ^ l) u) (hβ0 : rootVec K (u ^ l) u x ≠ 0)
    (hβ : Set.InjOn (QuotientGroup.mk (s := Subgroup.normalClosure {L.u}))
      (rootVec K (u ^ l) u x).coeff.support) :
    MagnusDescent K u l S :=
  magnusDescent_of_annAt hrn hS
    (annAt_mono (Set.singleton_subset_iff.mpr hxS)
      (annAt_of_torsionData L hu hβ0 hβ))

end Work.ORLyndon
