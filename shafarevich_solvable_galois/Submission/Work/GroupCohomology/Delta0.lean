/-
Copyright (c) 2025. All rights reserved.

# The connecting map `δ⁰ : H⁰(G, C) → H¹(G, A)`

For a short exact sequence of `G`-modules `0 → A --iota--> B --pi--> C → 0`, the connecting map
in degrees `0 → 1` is defined as follows: an invariant `c ∈ C^G` is lifted to an element `b ∈ B`
along the surjective `pi`; then `g • b - b ∈ ker pi = im iota`, so it pulls back (uniquely, using
injectivity of `iota`) to an element of `A`, and `g ↦ iota⁻¹(g • b - b)` is a `1`-cocycle.

## Main definitions

* `Work.GroupCohomology.ShortExactSeq.liftElem`
* `Work.GroupCohomology.ShortExactSeq.delta0Cocycle`
-/
import Submission.Work.GroupCohomology.ShortExact
import Submission.Work.GroupCohomology.Connecting
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.GroupCohomology

variable {G : Type u} {A : Type v} {B : Type w} {C : Type x} [Group G]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]

namespace ShortExactSeq

variable (S : ShortExactSeq G A B C)

/-- A lift of an element of `C` along the projection `pi`. -/
noncomputable def liftElem (c : C) : B := Classical.choose (S.pi_surjective c)

theorem pi_liftElem (c : C) : S.pi (S.liftElem c) = c :=
  Classical.choose_spec (S.pi_surjective c)

/-- **The connecting map on invariants**, at the level of cocycles: for `c ∈ H⁰(G,C)`, the
`1`-cocycle `g ↦ iota⁻¹ (g • b - b)`, where `b` is a lift of `c`. -/
noncomputable def delta0Cocycle (c : H0 G C) : G → A :=
  fun g => S.preimage (g • S.liftElem (c : C) - S.liftElem (c : C)) (by
    rw [AddMonoidHom.mem_ker, map_sub, S.pi_equivariant, S.pi_liftElem, c.2 g, sub_self])

theorem iota_delta0Cocycle (c : H0 G C) (g : G) :
    S.iota (S.delta0Cocycle c g) = g • S.liftElem (c : C) - S.liftElem (c : C) :=
  S.iota_preimage _ _

/-- `delta0Cocycle c` is a `1`-cocycle. -/
theorem delta0Cocycle_mem (c : H0 G C) : S.delta0Cocycle c ∈ Z1 G A := by
  rw [mem_Z1_iff]
  intro g h
  apply S.iota_injective
  rw [S.iota_delta0Cocycle, map_add, S.iota_equivariant, S.iota_delta0Cocycle,
    S.iota_delta0Cocycle, smul_sub, mul_smul]
  abel

/-- The `1`-cocycle of the connecting map, as an element of `Z¹(G, A)`. -/
noncomputable def delta0Elem (c : H0 G C) : Z1 G A :=
  ⟨S.delta0Cocycle c, S.delta0Cocycle_mem c⟩

/-- The zero class is sent to zero: the cocycle of `0 ∈ H⁰(G,C)` is a coboundary. -/
theorem delta0Elem_zero : H1π G A (S.delta0Elem 0) = 0 := by
  have hfun : (S.delta0Elem (0 : H0 G C) : G → A) = S.delta0Cocycle (0 : H0 G C) := rfl
  have hmem : (S.delta0Elem (0 : H0 G C) : G → A) ∈ B1 G A := by
    refine ⟨S.preimage (S.liftElem (0 : H0 G C)) (by
        rw [AddMonoidHom.mem_ker, S.pi_liftElem, AddSubgroup.coe_zero]), ?_⟩
    rw [hfun]
    funext g
    apply S.iota_injective
    rw [d0_apply, map_sub, S.iota_equivariant, S.iota_preimage, S.iota_delta0Cocycle]
  rw [H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
  exact hmem

end ShortExactSeq

end Work.GroupCohomology
