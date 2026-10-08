import Mathlib
import Submission.Work.Models.Port.BenderSetup
import Submission.Work.Models.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Transport of a Bender pair along a group isomorphism

Given a `BenderPair P` on a finite group `G` and an isomorphism `e : G ≃* G'`, the data
`(B, U, T, w)` transported by `e` is again a `BenderPair`.  This generalizes
`Submission.BenderPair.conj` (conjugation by an inner automorphism) to an arbitrary
isomorphism; the two are proved the same way, replacing `MulAut.conj g` by `e`.

Every axiom of `BenderPair` is transported by `Subgroup.map e.toMonoidHom`; the only
two inputs are that `e` is injective (used for cardinalities, `map_inf`,
non-triviality) and surjective (used for strong embedding and the index).
-/

set_option linter.style.haveILetI false

namespace Work.Models.Abstract

open LeanEval.GroupTheory.Defs

theorem benderPairMapEquiv {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (P : Submission.BenderPair G) (e : G ≃* G') :
    ∃ P' : Submission.BenderPair G',
      P'.B = P.B.map e.toMonoidHom ∧ P'.U = P.U.map e.toMonoidHom ∧
      P'.T = P.T.map e.toMonoidHom ∧ P'.w = e P.w := by
  have hker : e.toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective
  have hkerle : e.toMonoidHom.ker ≤ P.U := by rw [hker]; exact bot_le
  refine ⟨{ B := P.B.map e.toMonoidHom
            U := P.U.map e.toMonoidHom
            T := P.T.map e.toMonoidHom
            w := e P.w
            hSemb := ?_
            hU2 := ?_
            hUne := ?_
            hoddT := ?_
            hB := ?_
            hUT := ?_
            hTnU := ?_
            hwB := ?_
            hwT := ?_
            hCU := ?_
            hindex := ?_ }, rfl, rfl, rfl, rfl⟩
  · -- strong embedding is transported by a surjective homomorphism with odd kernel
    exact Commons.GroupTheory.StronglyEmbedded.stronglyEmbedded_map_of_surjective
      e.toMonoidHom e.surjective P.B P.hSemb.1 P.hSemb.2.1 P.hSemb.2.2
      (by rw [hker]; exact bot_le) (by rw [hker]; exact bot_le)
      (by rw [hker, Subgroup.card_bot]; exact odd_one)
  · -- `U` is a `2`-group: `e` is injective, so `|U.map e| = |U|`
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := P.hU2.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [Subgroup.card_map_of_injective e.injective, hk]
  · -- `U ≠ ⊥`: the kernel of `e` is trivial
    intro h
    rw [Subgroup.map_eq_bot_iff, hker, le_bot_iff] at h
    exact P.hUne h
  · -- `|T|` is odd: `e` is injective
    rw [Subgroup.card_map_of_injective e.injective]
    exact P.hoddT
  · -- `B = U ⊔ T`
    rw [P.hB, Subgroup.map_sup]
  · -- `U ⊓ T = ⊥`: the kernel of `e` lies in `U`, so `map` commutes with `⊓`
    rw [← Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le e.toMonoidHom P.U P.T hkerle,
      P.hUT, Subgroup.map_bot]
  · -- `T` normalizes `U`: `map` is monotone on normalizers
    exact (Subgroup.map_mono (f := e.toMonoidHom) P.hTnU).trans
      (Subgroup.le_normalizer_map (H := P.U) e.toMonoidHom)
  · -- `e w ∉ B.map e`, since `e` is injective and `w ∉ B`
    intro h
    exact P.hwB ((Subgroup.mem_map_iff_mem e.injective).mp h)
  · -- `e w` normalizes `T.map e`
    exact Subgroup.le_normalizer_map (H := P.T) e.toMonoidHom
      (Subgroup.mem_map.mpr ⟨P.w, P.hwT, rfl⟩)
  · -- `C_{U.map e}(T.map e) = 1`: pull the centralizing element back along `e`
    intro u hu hcent
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    have hcent' : ∀ t ∈ P.T, u₀ * t = t * u₀ := by
      intro t ht
      have h := hcent (e.toMonoidHom t) (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
      rw [← map_mul, ← map_mul] at h
      exact e.injective h
    rw [P.hCU u₀ hu₀ hcent', map_one]
  · -- the index is preserved: `index_map`, with trivial kernel and full range
    have hidx : (P.B.map e.toMonoidHom).index = P.B.index := by
      rw [Subgroup.index_map, hker, sup_bot_eq, MonoidHom.range_eq_top.mpr e.surjective,
        Subgroup.index_top, mul_one]
    rw [hidx, Subgroup.card_map_of_injective e.injective, P.hindex]

end Work.Models.Abstract
