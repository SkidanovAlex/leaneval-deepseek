import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

/-- A nontrivial finite solvable group has a normal subgroup of prime index.  (Proof route: take a
proper normal subgroup `N` of maximal cardinality; then `A ⧸ N` is simple, and it is solvable, hence
abelian by `IsSimpleGroup.comm_iff_isSolvable`, hence of prime order by `IsSimpleGroup.prime_card`
so that `N.index = Nat.card (A ⧸ N)` is prime.) -/
lemma exists_prime_index_normal {A : Type} [Group A] [Finite A] (hA : Nontrivial A)
    (hsol : Group.IsSolvable A) :
    ∃ (p : ℕ) (N : Subgroup A), N.Normal ∧ p.Prime ∧ N.index = p := by
  have : Group.IsSolvable A := hsol
  have : Nontrivial A := hA
  -- A proper normal subgroup always exists: the commutator subgroup of a nontrivial
  -- solvable group is proper.
  have hcomm_lt : commutator A < (⊤ : Subgroup A) :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial A
  -- Take a proper normal subgroup `M` of maximal cardinality.
  let S := {N : Subgroup A // N.Normal ∧ N < ⊤}
  have hSne : Nonempty S :=
    ⟨commutator A, Subgroup.commutator_normal ⊤ ⊤, hcomm_lt⟩
  obtain ⟨⟨M, hMn, hMlt⟩, hNmax⟩ := Finite.exists_max (fun N : S => Nat.card N.1)
  have hMmax : ∀ K : Subgroup A, K.Normal → K < ⊤ → Nat.card K ≤ Nat.card M := by
    intro K hKn hKlt
    exact hNmax ⟨K, hKn, hKlt⟩
  have hMnorm : M.Normal := hMn
  -- The quotient `A ⧸ M` is simple.
  have hnt : Nontrivial (A ⧸ M) := QuotientGroup.nontrivial_iff.mpr (ne_of_lt hMlt)
  have hsimple : IsSimpleGroup (A ⧸ M) :=
    ⟨fun H hH => by
      let f : A →* A ⧸ M := QuotientGroup.mk' M
      let K : Subgroup A := Subgroup.comap f H
      have hKn : K.Normal := hH.comap f
      have hMK : M ≤ K := QuotientGroup.le_comap_mk' M H
      have hmap : Subgroup.map f K = H :=
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective M) H
      rcases eq_or_lt_of_le (le_top : K ≤ (⊤ : Subgroup A)) with hK | hK
      · right
        rw [← hmap, hK, Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective M)]
      · left
        have hcardK : Nat.card K ≤ Nat.card M := hMmax K hKn hK
        have hcardM : Nat.card M ≤ Nat.card K := Subgroup.card_le_of_le hMK
        have hMKeq : M = K := Subgroup.eq_of_le_of_card_ge hMK hcardK
        rw [← hmap, ← hMKeq, QuotientGroup.map_mk'_self M]⟩
  -- It is solvable, hence abelian, hence of prime order.
  have hsolq : Group.IsSolvable (A ⧸ M) := inferInstance
  have hcomm : ∀ a b : A ⧸ M, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).mpr hsolq
  have hmulcomm : IsMulCommutative (A ⧸ M) := ⟨⟨hcomm⟩⟩
  have hprime : (Nat.card (A ⧸ M)).Prime := (Group.is_simple_iff_prime_card).mp hsimple
  exact ⟨M.index, M, hMn, Subgroup.index_eq_card M ▸ hprime, rfl⟩

end Work.ThreePoints
