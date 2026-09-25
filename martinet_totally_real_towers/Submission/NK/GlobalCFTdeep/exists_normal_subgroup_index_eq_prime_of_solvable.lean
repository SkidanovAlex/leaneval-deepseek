import Mathlib

namespace NK.GlobalCFTdeep

/-- **Existence of a maximal proper normal subgroup** in a finite nontrivial group: among the
proper normal subgroups (nonempty, since `⊥` is one) pick a maximal element with respect to
inclusion, which exists because the lattice of subgroups of a finite group is well-founded. -/
theorem exists_maximal_normal_subgroup {G : Type} [Group G] [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ ∀ K : Subgroup G, K.Normal → K ≠ ⊤ → N ≤ K → K = N := by
  have hwf : WellFounded (fun x y : Subgroup G => y < x) := inferInstance
  have hbot : (⊥ : Subgroup G) ≠ ⊤ := by
    intro hbot
    obtain ⟨a, b, hab⟩ := ‹Nontrivial G›
    exact hab ((Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top a)).trans
      (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top b)).symm)
  obtain ⟨N, hNmem, hNmax⟩ := hwf.has_min
    {H : Subgroup G | H.Normal ∧ H ≠ ⊤} ⟨⊥, inferInstance, hbot⟩
  obtain ⟨hNnorm, hNne⟩ := hNmem
  refine ⟨N, hNnorm, hNne, fun K hK hKne hle => ?_⟩
  by_contra hne
  exact hNmax _ ⟨hK, hKne⟩ (lt_of_le_of_ne hle (Ne.symm hne))

/-- **Every nontrivial finite solvable group has a normal subgroup of prime index.**
Take a maximal proper normal subgroup `N`; then `G/N` is simple, and simple solvable groups are
cyclic of prime order (a simple solvable group is abelian because its commutator subgroup is a
proper normal subgroup, hence trivial), so `N.index = Nat.card (G ⧸ N)` is prime. -/
theorem exists_normal_subgroup_index_eq_prime_of_solvable {G : Type} [Group G] [Finite G]
    (hG : Group.IsSolvable G) (h : Nontrivial G) :
    ∃ N : Subgroup G, N.Normal ∧ ∃ p : ℕ, p.Prime ∧ N.index = p := by
  obtain ⟨N, hNnorm, hNne, hNmax⟩ := exists_maximal_normal_subgroup (G := G)
  haveI : N.Normal := hNnorm
  -- `G ⧸ N` is nontrivial and simple: a normal subgroup of `G ⧸ N` pulls back to a normal
  -- subgroup of `G` containing `N`, hence is `N` or `⊤` by maximality of `N`.
  haveI : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNne
  haveI : IsSimpleGroup (G ⧸ N) := by
    rw [isSimpleGroup_iff]
    refine ⟨inferInstance, ?_⟩
    intro K hK
    have hKnorm : (K.comap (QuotientGroup.mk' N)).Normal := hK.comap _
    have hle : N ≤ K.comap (QuotientGroup.mk' N) :=
      calc N = (QuotientGroup.mk' N).ker := (QuotientGroup.ker_mk' N).symm
        _ ≤ K.comap (QuotientGroup.mk' N) := MonoidHom.ker_le_comap _ _
    rcases eq_or_ne (K.comap (QuotientGroup.mk' N)) ⊤ with htop | hne
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K, htop,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    · left
      have heq : K.comap (QuotientGroup.mk' N) = N := hNmax _ hKnorm hne hle
      rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K, heq,
        Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  -- `G ⧸ N` is solvable, so being simple it is commutative, hence of prime order.
  have hcomm : ∀ a b : G ⧸ N, a * b = b * a :=
    IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance
  have hp : (Nat.card (G ⧸ N)).Prime := by
    letI : CommGroup (G ⧸ N) := { (inferInstance : Group (G ⧸ N)) with mul_comm := hcomm }
    exact IsSimpleGroup.prime_card
  exact ⟨N, hNnorm, Nat.card (G ⧸ N), hp, Subgroup.index_eq_card N⟩

end NK.GlobalCFTdeep
