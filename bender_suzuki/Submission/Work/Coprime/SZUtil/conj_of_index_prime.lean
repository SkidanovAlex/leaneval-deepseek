import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Conjugacy of complements of a normal subgroup of prime index

Let `N` be a normal subgroup of a finite group `G` whose order `|N|` is coprime to its
index `[G : N]`, and suppose that `[G : N] = p` is prime.  Then any two complements of
`N` in `G` are conjugate.

The point is that a complement `H` of `N` has order `[G : N] = p`, and that **every**
subgroup of order `p` is a Sylow `p`-subgroup: since `p ∤ |N|` and `|G| = |N| · p`, we
have `p² ∤ |G|`, so all subgroups of order `p` have index coprime to `p`.  Sylow's
theorem (any two Sylow `p`-subgroups are conjugate) then yields the statement.
-/

open scoped Pointwise

namespace Work.Coprime.SZUtil

theorem conj_of_index_prime {G : Type*} [Group G] [Finite G] {N H K : Subgroup G} [N.Normal]
    (hc : (Nat.card N).Coprime N.index) (hp : N.index.Prime)
    (hH : N.IsComplement' H) (hK : N.IsComplement' K) :
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  have : Fact N.index.Prime := ⟨hp⟩
  -- A complement of `N` has order `[G : N] = p`.
  have hcardH : Nat.card H = N.index := Subgroup.IsComplement.card_right hH
  have hcardK : Nat.card K = N.index := Subgroup.IsComplement.card_right hK
  -- Its index is `|N|`, which is coprime to `p`.
  have hidxH : H.index = Nat.card N := (Subgroup.IsComplement.card_right hH.symm).symm
  have hidxK : K.index = Nat.card N := (Subgroup.IsComplement.card_right hK.symm).symm
  have hndvd : ¬ N.index ∣ Nat.card N := hp.coprime_iff_not_dvd.mp hc.symm
  -- Both `H` and `K` are `p`-subgroups of index not divisible by `p`, i.e. Sylow subgroups.
  have hPH : IsPGroup N.index H := IsPGroup.of_card (n := 1) (by rw [hcardH, pow_one])
  have hPK : IsPGroup N.index K := IsPGroup.of_card (n := 1) (by rw [hcardK, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G
    (hPH.toSylow (by rw [hidxH]; exact hndvd))
    (hPK.toSylow (by rw [hidxK]; exact hndvd))
  refine ⟨g, ?_⟩
  have hcoe : MulAut.conj g • (H : Subgroup G) = K := by
    have h1 := congrArg (fun S : Sylow N.index G => (S : Subgroup G)) hg
    rw [Sylow.coe_subgroup_smul] at h1
    rw [IsPGroup.toSylow_coe, IsPGroup.toSylow_coe] at h1
    exact h1
  rw [← hcoe, Subgroup.pointwise_smul_def]
  rfl

end Work.Coprime.SZUtil
