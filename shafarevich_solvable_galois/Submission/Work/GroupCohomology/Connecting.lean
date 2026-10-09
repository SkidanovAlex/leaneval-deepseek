/-
Copyright (c) 2025. All rights reserved.

# The connecting map `H¹(G, C) → H²(G, A)` of a short exact sequence

For a short exact sequence of `G`-modules `0 → A --iota--> B --pi--> C → 0`, the connecting map
in degrees `1 → 2` is defined as follows: lift a `1`-cocycle `c : G → C` to a cochain
`b : G → B` along the surjective `pi`; then `d¹ b` takes values in `ker pi = im iota`, so it
pulls back (uniquely, using injectivity of `iota`) to a `2`-cochain with values in `A`, which is a
`2`-cocycle because `d² ∘ d¹ = 0` and `iota` is injective.

## Main definitions

* `Work.GroupCohomology.ShortExactSeq.liftCochain`
* `Work.GroupCohomology.ShortExactSeq.preimage`
* `Work.GroupCohomology.ShortExactSeq.deltaCocycle : Z¹(G, C) → Z²(G, A)`
-/
import Submission.Work.GroupCohomology.ShortExact
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

/-- A lift of a cochain `c : G → C` along the projection `pi`, using `Classical.choose`. -/
noncomputable def liftCochain (c : G → C) : G → B := fun g => Classical.choose (S.pi_surjective (c g))

theorem pi_liftCochain (c : G → C) (g : G) : S.pi (S.liftCochain c g) = c g :=
  Classical.choose_spec (S.pi_surjective (c g))

/-- The unique preimage in `A` of an element of `ker pi`. -/
noncomputable def preimage (b : B) (hb : b ∈ S.pi.ker) : A :=
  Classical.choose (S.exists_preimage hb)

theorem iota_preimage (b : B) (hb : b ∈ S.pi.ker) : S.iota (S.preimage b hb) = b :=
  Classical.choose_spec (S.exists_preimage hb)

/-- The differential of a lift of a `1`-cocycle of `C` lies in `ker pi`. -/
theorem pi_d1_liftCochain (c : G → C) (hc : c ∈ Z1 G C) (g h : G) :
    S.pi (d1 G B (S.liftCochain c) (g, h)) = 0 := by
  have h1 : S.pi (g • S.liftCochain c h) = g • c h := by
    rw [S.pi_equivariant g (S.liftCochain c h), S.pi_liftCochain]
  have h2 : S.pi (S.liftCochain c (g * h)) = c (g * h) := S.pi_liftCochain c (g * h)
  have h3 : S.pi (S.liftCochain c g) = c g := S.pi_liftCochain c g
  have hc' : c (g * h) = g • c h + c g := hc g h
  simp only [d1_apply, map_sub, map_add, h1, h2, h3]
  rw [hc']
  abel

/-- The connecting map on cocycles: `Z¹(G, C) → Z²(G, A)`, defined by lifting a `1`-cocycle
along `pi` and pulling `d¹` of the lift back along `iota`. -/
noncomputable def deltaCocycle (c : Z1 G C) : Z2 G A :=
  ⟨fun p => S.preimage (d1 G B (S.liftCochain (c : G → C)) p) (by
      obtain ⟨g, h⟩ := p
      exact S.pi_d1_liftCochain (c : G → C) c.2 g h),
    by
      rw [mem_Z2_iff]
      intro g h k
      apply S.iota_injective
      rw [map_add, map_add, S.iota_equivariant,
        S.iota_preimage, S.iota_preimage, S.iota_preimage, S.iota_preimage]
      have hzero : g • d1 G B (S.liftCochain (c : G → C)) (h, k) -
          d1 G B (S.liftCochain (c : G → C)) (g * h, k) +
          d1 G B (S.liftCochain (c : G → C)) (g, h * k) -
          d1 G B (S.liftCochain (c : G → C)) (g, h) = 0 := by
        have h2 : d2 G B (d1 G B (S.liftCochain (c : G → C))) (g, h, k) = 0 :=
          congrFun (d2_d1 G B (S.liftCochain (c : G → C))) (g, h, k)
        simpa only [Pi.zero_apply, d2_apply] using h2
      rw [← sub_eq_zero]
      rw [show d1 G B (S.liftCochain (c : G → C)) (g * h, k) +
            d1 G B (S.liftCochain (c : G → C)) (g, h) -
            (g • d1 G B (S.liftCochain (c : G → C)) (h, k) +
              d1 G B (S.liftCochain (c : G → C)) (g, h * k)) =
          -(g • d1 G B (S.liftCochain (c : G → C)) (h, k) -
            d1 G B (S.liftCochain (c : G → C)) (g * h, k) +
            d1 G B (S.liftCochain (c : G → C)) (g, h * k) -
            d1 G B (S.liftCochain (c : G → C)) (g, h)) from by abel]
      rw [hzero, neg_zero]⟩

@[simp] theorem deltaCocycle_apply (c : Z1 G C) (g h : G) :
    (S.deltaCocycle c : G × G → A) (g, h) =
      S.preimage (d1 G B (S.liftCochain (c : G → C)) (g, h))
        (S.pi_d1_liftCochain (c : G → C) c.2 g h) := rfl

theorem iota_deltaCocycle (c : Z1 G C) (g h : G) :
    S.iota ((S.deltaCocycle c : G × G → A) (g, h)) =
      d1 G B (S.liftCochain (c : G → C)) (g, h) :=
  S.iota_preimage _ (S.pi_d1_liftCochain (c : G → C) c.2 g h)

end ShortExactSeq

end Work.GroupCohomology
