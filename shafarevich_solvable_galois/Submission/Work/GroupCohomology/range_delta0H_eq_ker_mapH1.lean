/-
Copyright (c) 2025. All rights reserved.

# Exactness at `H¹(G, A)`: `range δ⁰ = ker (H¹(G,A) → H¹(G,B))`

This is the `H⁰ → H¹` piece of the long exact sequence of a short exact sequence of `G`-modules
`0 → A --iota--> B --pi--> C → 0`.

* `⊆`: for `c = δ⁰ c₀` with `c₀ ∈ H⁰(G, C)`, the cocycle representing `c` is
  `g ↦ iota⁻¹(g • b - b)` with `b` a lift of `c₀`; pushing it along `iota` gives `d⁰ b`, a
  coboundary, so its class dies in `H¹(G, B)`.

* `⊇`: if `f ∈ Z¹(G, A)` has `iota ∘ f` cohomologous to zero, say `iota (f g) = g • b - b`, then
  `pi b` is `G`-invariant and any other lift `b'` of `pi b` differs from `b` by `iota a` for some
  `a : A`; the two cocycles `delta0Cocycle ⟨pi b, _⟩` and `f` then differ by the coboundary
  `d⁰ (-a)`.
-/
import Mathlib
import Submission.Work.GroupCohomology.Delta0Map
import Submission.Work.GroupCohomology.H1pi_eq_iff
import Submission.Work.GroupCohomology.H1pi_eq_zero_iff
import Submission.Work.GroupCohomology.H1_induction_on
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

theorem range_delta0H_eq_ker_mapH1 {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] (S : Work.GroupCohomology.ShortExactSeq G A B C) :
    (S.delta0H).range =
      (Work.GroupCohomology.mapH1 (A := A) (B := B) G S.iota S.iota_equivariant).ker := by
  apply le_antisymm
  · -- image `⊆` kernel: `iota ∘ delta0Cocycle c` is the coboundary `d⁰ (liftElem c)`.
    intro y hy
    rw [AddMonoidHom.mem_range] at hy
    obtain ⟨c, rfl⟩ := hy
    rw [AddMonoidHom.mem_ker, ShortExactSeq.delta0H_apply, mapH1_H1π, H1pi_eq_zero_iff,
      mem_B1_iff]
    refine ⟨S.liftElem (c : C), ?_⟩
    funext g
    simp only [mapZ1_coe, mapCochain1_apply, d0_apply]
    exact (S.iota_delta0Cocycle c g).symm
  · -- kernel `⊆` image.
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddMonoidHom.mem_range]
    revert hx
    induction x using H1_induction_on with
    | h f =>
      intro hx
      rw [mapH1_H1π, H1pi_eq_zero_iff, mem_B1_iff] at hx
      obtain ⟨b, hb⟩ := hx
      -- `hb` says `iota (f g) = g • b - b` for all `g`.
      have hbval : ∀ g : G, S.iota ((f : G → A) g) = g • b - b := by
        intro g
        have h := congrFun hb g
        simp only [mapZ1_coe, mapCochain1_apply, d0_apply] at h
        exact h.symm
      -- `pi b` is `G`-invariant.
      have hmem : S.pi b ∈ H0 G C := by
        intro g
        rw [← sub_eq_zero, ← S.pi_equivariant g b, ← map_sub, ← hbval g, S.pi_iota]
      -- the chosen lift of `pi b` differs from `b` by `iota a`.
      have hker : b - S.liftElem (S.pi b) ∈ S.pi.ker := by
        rw [AddMonoidHom.mem_ker, map_sub, S.pi_liftElem, sub_self]
      obtain ⟨a, ha⟩ := S.exists_preimage hker
      refine ⟨⟨S.pi b, hmem⟩, ?_⟩
      rw [ShortExactSeq.delta0H_apply, H1pi_eq_iff]
      -- the two cocycles differ by the coboundary `d⁰ (-a)`
      have key : ((S.delta0Elem ⟨S.pi b, hmem⟩ - f : Z1 G A) : G → A) = d0 G A (-a) := by
        funext g
        apply S.iota_injective
        have hL : S.iota (((S.delta0Elem ⟨S.pi b, hmem⟩ - f : Z1 G A) : G → A) g)
            = (g • S.liftElem (S.pi b) - S.liftElem (S.pi b)) - (g • b - b) := by
          change S.iota (S.delta0Cocycle ⟨S.pi b, hmem⟩ g - (f : G → A) g) = _
          rw [map_sub, S.iota_delta0Cocycle, hbval g]
        have hR : S.iota ((d0 G A (-a)) g)
            = (g • S.liftElem (S.pi b) - S.liftElem (S.pi b)) - (g • b - b) := by
          rw [d0_apply, map_sub, S.iota_equivariant, map_neg, ha, smul_neg, smul_sub]
          abel
        rw [hL, hR]
      rw [key]
      exact (mem_B1_iff G A _).mpr ⟨-a, rfl⟩

end Work.GroupCohomology
