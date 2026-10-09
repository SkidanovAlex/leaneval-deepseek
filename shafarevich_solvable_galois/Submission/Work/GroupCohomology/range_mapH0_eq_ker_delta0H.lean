import Mathlib
import Submission.Work.GroupCohomology.Delta0Map
import Submission.Work.GroupCohomology.H1pi_eq_zero_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

namespace ShortExactSeq

variable {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
  [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
  [DistribMulAction G C]

variable (S : ShortExactSeq G A B C)

/-- The underlying cochain of `delta0Elem` is `delta0Cocycle`. -/
theorem delta0Elem_coe (c : H0 G C) : (S.delta0Elem c : G → A) = S.delta0Cocycle c := rfl

end ShortExactSeq

theorem range_mapH0_eq_ker_delta0H {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : Work.GroupCohomology.ShortExactSeq G A B C) :
    (Work.GroupCohomology.mapH0 G S.pi S.pi_equivariant).range =
      (S.delta0H).ker := by
  ext x
  constructor
  · -- An element of the image of `H⁰(G,B) → H⁰(G,C)` has trivial connecting image.
    intro hx
    obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.mp hx
    rw [AddMonoidHom.mem_ker, S.delta0H_apply, H1pi_eq_zero_iff, mem_B1_iff]
    -- `pi b = x`
    have hbval : S.pi (b : B) = (x : C) := by
      have h := congrArg Subtype.val hb
      simpa [mapH0] using h
    -- lift `x` first, then correct by `b`
    have hker : S.liftElem (x : C) - (b : B) ∈ S.pi.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, S.pi_liftElem, hbval, sub_self]
    have hia : S.iota (S.preimage (S.liftElem (x : C) - (b : B)) hker)
        = S.liftElem (x : C) - (b : B) := S.iota_preimage _ hker
    refine ⟨S.preimage (S.liftElem (x : C) - (b : B)) hker, ?_⟩
    rw [S.delta0Elem_coe]
    funext g
    apply S.iota_injective
    rw [d0_apply, map_sub, S.iota_equivariant, hia, S.iota_delta0Cocycle, smul_sub, b.2 g]
    abel
  · -- An element killed by the connecting homomorphism comes from an invariant of `B`.
    intro hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [S.delta0H_apply, H1pi_eq_zero_iff, mem_B1_iff] at hx
    obtain ⟨a₀, ha₀⟩ := hx
    -- `b = liftElem x - iota a₀` is `G`-invariant and projects to `x`
    refine AddMonoidHom.mem_range.mpr ⟨⟨S.liftElem (x : C) - S.iota a₀, ?_⟩, ?_⟩
    · intro g
      refine sub_eq_zero.mp ?_
      have h3 : g • a₀ - a₀ = S.delta0Cocycle x g := by
        have h := congrFun ha₀ g
        simpa [S.delta0Elem_coe] using h
      have key : g • S.iota a₀ - S.iota a₀
          = g • S.liftElem (x : C) - S.liftElem (x : C) := by
        rw [← S.iota_equivariant g a₀, ← map_sub, h3, S.iota_delta0Cocycle]
      calc g • (S.liftElem (x : C) - S.iota a₀) - (S.liftElem (x : C) - S.iota a₀)
          = (g • S.liftElem (x : C) - S.liftElem (x : C))
              - (g • S.iota a₀ - S.iota a₀) := by rw [smul_sub]; abel
        _ = (g • S.liftElem (x : C) - S.liftElem (x : C))
              - (g • S.liftElem (x : C) - S.liftElem (x : C)) := by rw [key]
        _ = 0 := sub_self _
    · apply Subtype.ext
      change S.pi (S.liftElem (x : C) - S.iota a₀) = (x : C)
      rw [map_sub, S.pi_liftElem, S.pi_iota, sub_zero]

end Work.GroupCohomology
