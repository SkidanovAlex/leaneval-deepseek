import Mathlib
import Submission.Work.GroupCohomology.All
import Submission.Work.Tate.All
import Submission.Work.Tate.DimensionShiftH
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.tate

open Work.GroupCohomology

/-- Naturality of the connecting map on `2`-cocycles: if `(α, β, γ)` is a morphism of short
exact sequences of `G`-modules, then the two `2`-cocycles of `A'` obtained by connecting after
pushing along `γ`, or pushing along `α` after connecting, define the same class in `H²`. -/
theorem deltaCocycle_natural
    {G A B C A' B' C' : Type*}
    [Group G] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [DistribMulAction G A'] [DistribMulAction G B'] [DistribMulAction G C']
    (S : ShortExactSeq G A B C) (S' : ShortExactSeq G A' B' C')
    (α : A →+ A') (β : B →+ B') (γ : C →+ C')
    (hα : IsEquivariant G α) (hβ : IsEquivariant G β) (hγ : IsEquivariant G γ)
    (hβι : ∀ a : A, β (S.iota a) = S'.iota (α a))
    (hγπ : ∀ b : B, S'.pi (β b) = γ (S.pi b))
    (c : Z1 G C) :
    ((S'.deltaCocycle (mapZ1 G γ hγ c) - mapZ2 G α hα (S.deltaCocycle c) : Z2 G A') :
        G × G → A') ∈ B2 G A' := by
  classical
  -- `S'.pi` kills the difference of the two lifts of `γ ∘ c`
  have hpi : ∀ g : G, S'.pi (S'.liftCochain ((mapZ1 G γ hγ c : Z1 G C') : G → C') g
        - β (S.liftCochain (c : G → C) g)) = 0 := by
    intro g
    rw [map_sub, S'.pi_liftCochain, hγπ (S.liftCochain (c : G → C) g),
      S.pi_liftCochain,
      show ((mapZ1 G γ hγ c : Z1 G C') : G → C') g = γ ((c : G → C) g) from rfl,
      sub_self]
  -- hence it is the image under `S'.iota` of a cochain `k`
  let k : G → A' := fun g => S'.preimage _ (AddMonoidHom.mem_ker.mpr (hpi g))
  have hk : ∀ g, S'.iota (k g) = S'.liftCochain ((mapZ1 G γ hγ c : Z1 G C') : G → C') g
        - β (S.liftCochain (c : G → C) g) := fun g => S'.iota_preimage _ _
  have hmap : mapCochain1 G S'.iota k
      = S'.liftCochain ((mapZ1 G γ hγ c : Z1 G C') : G → C')
        - mapCochain1 G β (S.liftCochain (c : G → C)) := by
    funext g
    rw [mapCochain1_apply, Pi.sub_apply, mapCochain1_apply, hk g]
  -- and `d¹ k` is the difference of the two connecting cocycles
  rw [mem_B2_iff]
  refine ⟨k, funext fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  apply S'.iota_injective
  rw [AddSubgroup.coe_sub, Pi.sub_apply, map_sub]
  have hA : S'.iota (d1 G A' k (g, h)) = d1 G B' (mapCochain1 G S'.iota k) (g, h) := by
    have hh := congrFun (mapCochain2_d1 G S'.iota S'.iota_equivariant k) (g, h)
    rwa [mapCochain2_apply] at hh
  rw [hA, hmap, map_sub, Pi.sub_apply]
  congr 1
  · rw [← S'.iota_deltaCocycle (mapZ1 G γ hγ c) g h]
  · have hb2 : S'.iota ((mapZ2 G α hα (S.deltaCocycle c) : G × G → A') (g, h))
        = β (d1 G B (S.liftCochain (c : G → C)) (g, h)) := by
      rw [show (mapZ2 G α hα (S.deltaCocycle c) : G × G → A') (g, h)
            = mapCochain2 G α (S.deltaCocycle c) (g, h) from rfl]
      rw [mapCochain2_apply, ← hβι ((S.deltaCocycle c : G × G → A) (g, h)),
        S.iota_deltaCocycle c g h]
    have hb3 : β (d1 G B (S.liftCochain (c : G → C)) (g, h))
        = d1 G B' (mapCochain1 G β (S.liftCochain (c : G → C))) (g, h) := by
      have hh := congrFun (mapCochain2_d1 G β hβ (S.liftCochain (c : G → C))) (g, h)
      rw [mapCochain2_apply] at hh
      exact hh
    rw [hb2, hb3]

theorem deltaH1_natural_shortExact
    {G A B C A' B' C' : Type*}
    [Group G] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [DistribMulAction G A'] [DistribMulAction G B'] [DistribMulAction G C']
    (S : Work.GroupCohomology.ShortExactSeq G A B C) (S' : Work.GroupCohomology.ShortExactSeq G A' B' C')
    (α : A →+ A') (β : B →+ B') (γ : C →+ C')
    (hα : Work.GroupCohomology.IsEquivariant G α) (hβ : Work.GroupCohomology.IsEquivariant G β) (hγ : Work.GroupCohomology.IsEquivariant G γ)
    (hβι : ∀ a : A, β (S.iota a) = S'.iota (α a))
    (hγπ : ∀ b : B, S'.pi (β b) = γ (S.pi b)) :
    S'.deltaH1.comp (Work.GroupCohomology.mapH1 G γ hγ) = (Work.GroupCohomology.mapH2 G α hα).comp S.deltaH1 := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using Work.GroupCohomology.H1_induction_on with
  | h c =>
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
    rw [Work.GroupCohomology.mapH1_H1π, Work.GroupCohomology.ShortExactSeq.deltaH1_H1π]
    rw [Work.GroupCohomology.ShortExactSeq.deltaH1_H1π, Work.GroupCohomology.mapH2_H2π]
    rw [Work.GroupCohomology.H2pi_eq_iff]
    exact deltaCocycle_natural S S' α β γ hα hβ hγ hβι hγπ c

end Work.CohomologicalShrinking.tate
