import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

/-!
# Maximal subgroups of finite `p`-groups have index `p`

If `H` is a finite `p`-group and `M ≤ H` is a maximal proper subgroup (a coatom in the
subgroup lattice), then the index of `M` in `H` equals `p`.

The proof strategy is the classical one:

* a finite `p`-group is nilpotent, hence satisfies the normalizer condition, so every maximal
  subgroup is normal (`Subgroup.NormalizerCondition.normal_of_coatom`);
* by the correspondence theorem, a normal coatom has a simple quotient;
* a simple nilpotent group is commutative, so the quotient `H ⧸ M` is a simple commutative group,
  hence of prime order;
* the quotient is also a `p`-group, so its order is a power of `p`; the only prime power that is
  prime is `p` itself, and `M.index = Nat.card (H ⧸ M)`.
-/

namespace Work.PGroup

/-- The quotient of a group by a normal maximal (coatom) subgroup is simple. -/
theorem isSimpleGroup_quotient_of_isCoatom {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : IsCoatom N) : IsSimpleGroup (G ⧸ N) where
  exists_pair_ne := by
    have hnt : Nontrivial (G ⧸ N) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hs
      exact hN.ne_top (QuotientGroup.subgroup_eq_top_of_subsingleton N hs)
    exact hnt.exists_pair_ne
  eq_bot_or_eq_top_of_normal := by
    intro K _
    -- `K` sits between `⊥` and `⊤` in the quotient hence, by the correspondence theorem, its
    -- preimage sits between `N` and `⊤` in `G`.
    have hf : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
    have hinj : Function.Injective (Subgroup.comap (QuotientGroup.mk' N)) :=
      Subgroup.comap_injective hf
    have hle : N ≤ K.comap (QuotientGroup.mk' N) := QuotientGroup.le_comap_mk' N K
    rcases (hN.le_iff.mp hle) with h | h
    · right
      exact hinj (by rw [h, Subgroup.comap_top])
    · left
      have hb : Subgroup.comap (QuotientGroup.mk' N) (⊥ : Subgroup (G ⧸ N)) = N := by
        rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
      exact hinj (h.trans hb.symm)

/-- A maximal subgroup of a finite `p`-group has index `p`. -/
theorem isCoatom_index_eq_prime {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hH : IsPGroup p H) {M : Subgroup H} (hM : IsCoatom M) : M.index = p := by
  -- A finite `p`-group is nilpotent, hence every maximal subgroup is normal.
  have hNil : Group.IsNilpotent H := hH.isNilpotent
  haveI : Group.IsNilpotent H := hNil
  have hMN : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM
  haveI : M.Normal := hMN
  -- The quotient is simple, a `p`-group, and nilpotent.
  have hS : IsSimpleGroup (H ⧸ M) := isSimpleGroup_quotient_of_isCoatom hM
  haveI : IsSimpleGroup (H ⧸ M) := hS
  have hPQ : IsPGroup p (H ⧸ M) := hH.to_quotient M
  haveI : IsPGroup p (H ⧸ M) := hPQ
  have hNilQ : Group.IsNilpotent (H ⧸ M) := hPQ.isNilpotent
  -- A simple nilpotent group is commutative; get the bundled `CommGroup` on the canonical
  -- group structure of the quotient.
  have hcomm : ∀ a b : (H ⧸ M), a * b = b * a :=
    hS.comm_iff_isSolvable.mpr (IsNilpotent.to_isSolvable (G := H ⧸ M))
  letI : CommGroup (H ⧸ M) := CommGroup.mk hcomm
  have hprime : (Nat.card (H ⧸ M)).Prime := IsSimpleGroup.prime_card
  have hlt : 1 < Nat.card (H ⧸ M) :=
    Finite.one_lt_card_iff_nontrivial.mpr hS.toNontrivial
  -- The order of the quotient is a nontrivial power of `p`, hence divisible by `p` ...
  have hpdvd : p ∣ Nat.card (H ⧸ M) := by
    rcases hPQ.card_eq_or_dvd with h1 | h2
    · exact absurd h1 (ne_of_gt hlt)
    · exact h2
  -- ... and being prime it must equal `p`.
  rw [Subgroup.index_eq_card]
  exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hprime).mp hpdvd).symm

end Work.PGroup
