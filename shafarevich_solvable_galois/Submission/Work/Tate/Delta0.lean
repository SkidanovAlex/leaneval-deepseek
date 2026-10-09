/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The connecting map `δ₀ : Ĥ⁰(G, C) → H¹(G, A)`

For a short exact sequence of `G`-modules `0 → A --f--> B --g--> C → 0` (a `Work.Tate.SES`),
the next connecting map of the Tate long exact sequence is

`δ₀ : Ĥ⁰(G, C) = C^G/N(C) → H¹(G, A)`,

the *Tate* version of the usual connecting map `H⁰(G,C) = C^G → H¹(G,A)`.  Explicitly, for a
fixed point `c ∈ C^G` one lifts `c` to `b ∈ B`; then `γ • b - b ∈ ker g = im f` for every
`γ : G`, and

`γ ↦ f⁻¹(γ • b - b)`

is a `1`-cocycle of `A`; the class of this cocycle in `H¹(G,A)` is independent of the lift `b`
and kills `N(C) ⊆ C^G`, so it descends to `Ĥ⁰(G,C)`.

This file provides the cocycle-level construction:

* `Work.Tate.SES.toShortExactSeq` : the same data as a
  `Work.GroupCohomology.ShortExactSeq` (bridge to the inhomogeneous `H¹`/`H²` API);
* `Work.Tate.SES.delta0CocycleOf`, `Work.Tate.SES.delta0Cocycle` : the cocycles above,
  with `S.f (S.delta0CocycleOf b hb γ) = γ • b - b`.

The construction of the map `S.delta0 : Ĥ⁰(G,C) →+ H¹(G,A)` and its exactness live in
`Submission/Work/Tate/Delta0Map.lean`.
-/
import Mathlib
import Submission.Work.GroupCohomology.ShortExact
import Submission.Work.Tate.SES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.Tate

variable {G : Type u} {A : Type v} {B : Type w} {C : Type x} [Group G] [AddCommGroup A]
  [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
  [DistribMulAction G C]

/-- A `Work.Tate.SES` is the same data as a `Work.GroupCohomology.ShortExactSeq`. -/
def SES.toShortExactSeq (S : SES G A B C) : GroupCohomology.ShortExactSeq G A B C where
  iota := S.f
  pi := S.g
  iota_equivariant := S.f_equiv
  pi_equivariant := S.g_equiv
  iota_injective := S.f_injective
  pi_surjective := S.g_surjective
  range_iota_eq_ker_pi := S.range_f_eq_ker_g

@[simp] theorem SES.toShortExactSeq_iota (S : SES G A B C) :
    S.toShortExactSeq.iota = S.f := rfl

@[simp] theorem SES.toShortExactSeq_pi (S : SES G A B C) :
    S.toShortExactSeq.pi = S.g := rfl

section Fintype

variable [Fintype G]

/-- For `b : B` whose image in `C` is fixed, the map `γ ↦ f⁻¹ (γ • b - b)`, where the inverse
is taken along the injection `f` (possible because `γ • b - b ∈ ker g = im f`). -/
noncomputable def SES.delta0CocycleOf (S : SES G A B C) (b : B)
    (hb : ∀ γ : G, S.g (γ • b - b) = 0) : G → A :=
  fun γ => Classical.choose (S.exists_of_g_eq_zero (hb γ))

theorem SES.f_delta0CocycleOf (S : SES G A B C) (b : B)
    (hb : ∀ γ : G, S.g (γ • b - b) = 0) (γ : G) :
    S.f (S.delta0CocycleOf b hb γ) = γ • b - b :=
  Classical.choose_spec (S.exists_of_g_eq_zero (hb γ))

/-- The canonical lift of a fixed point has fixed image, so the cocycle construction applies. -/
theorem SES.sec_sub_self_mem_ker (S : SES G A B C) (c : fixedSubgroup G C) (γ : G) :
    S.g (γ • S.sec (c : C) - S.sec (c : C)) = 0 := by
  rw [map_sub, S.g_equiv, S.sec_spec, c.2 γ, sub_self]

/-- The `1`-cocycle of `A` attached to a fixed point `c ∈ C^G`, built from the canonical lift
`S.sec c`. -/
noncomputable def SES.delta0Cocycle (S : SES G A B C) (c : fixedSubgroup G C) : G → A :=
  S.delta0CocycleOf (S.sec (c : C)) (S.sec_sub_self_mem_ker c)

theorem SES.f_delta0Cocycle (S : SES G A B C) (c : fixedSubgroup G C) (γ : G) :
    S.f (S.delta0Cocycle c γ) = γ • S.sec (c : C) - S.sec (c : C) :=
  S.f_delta0CocycleOf (S.sec (c : C)) (S.sec_sub_self_mem_ker c) γ

end Fintype

end Work.Tate
