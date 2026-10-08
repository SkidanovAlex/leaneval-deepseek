import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

/-!
# A finite solvable nontrivial group has a normal subgroup of prime index

We prove that if `A` is a finite solvable nontrivial group, then there exists a prime `q` and a
normal subgroup `M < ⊤` with `Nat.card (A ⧸ M) = q`.

The proof goes through the maximal (proper) normal subgroup.  Equivalently, since the abelianization
`Abelianization A = A ⧸ commutator A` is a nontrivial finite abelian group, its subgroup lattice
contains a coatom `K`; the quotient `Abelianization A ⧸ K` is then a simple abelian group, hence
finite of prime order.  Pulling back along `A →* Abelianization A →* Abelianization A ⧸ K` and
taking the kernel gives the required normal subgroup.
-/

namespace Work.Solvable

open Subgroup

/-- The subgroup lattice of a finite group is coatomic: every proper subgroup is contained in a
maximal one. -/
instance instIsCoatomicSubgroupOfFinite {G : Type*} [Group G] [Finite G] :
    IsCoatomic (Subgroup G) := by
  refine ⟨fun b => ?_⟩
  rcases eq_or_ne b ⊤ with rfl | hb
  · exact Or.inl rfl
  · right
    have hfin : ({K : Subgroup G | b ≤ K ∧ K < ⊤} : Set (Subgroup G)).Finite := Set.toFinite _
    have hne : ({K : Subgroup G | b ≤ K ∧ K < ⊤} : Set (Subgroup G)).Nonempty :=
      ⟨b, ⟨le_rfl, lt_top_iff_ne_top.mpr hb⟩⟩
    obtain ⟨K, hK⟩ := hfin.exists_maximal hne
    refine ⟨K, ?_, hK.1.1⟩
    rw [isCoatom_iff_ge_of_le]
    exact ⟨lt_top_iff_ne_top.mp hK.1.2,
      fun j hj hjK => hK.2 (y := j) ⟨hK.1.1.trans hjK, lt_top_iff_ne_top.mpr hj⟩ hjK⟩

theorem exists_normal_prime_quotient {A : Type*} [Group A] [Finite A]
    (hsol : Group.IsSolvable A) (hnt : Nontrivial A) :
    ∃ (q : ℕ) (_ : q.Prime) (M : Subgroup A) (_ : M.Normal), M < ⊤ ∧ Nat.card (A ⧸ M) = q := by
  haveI : Nontrivial A := hnt
  haveI : Group.IsSolvable A := hsol
  -- The commutator subgroup of `A` is proper, since `A` is solvable and nontrivial.
  have hDlt : commutator A < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial A
  obtain ⟨-, g, -, hg⟩ := SetLike.lt_iff_le_and_exists.mp hDlt
  -- The abelianization is nontrivial.
  have hBnt : Nontrivial (Abelianization A) := by
    refine ⟨Abelianization.of g, 1, fun h => hg ?_⟩
    have hmem : g ∈ (Abelianization.of (G := A)).ker := MonoidHom.mem_ker.mpr h
    rw [Abelianization.ker_of] at hmem
    exact hmem
  haveI := hBnt
  -- A coatom `K` of the subgroup lattice of the abelianization; its quotient is simple.
  obtain ⟨K, hK⟩ := IsCoatomic.exists_coatom (Subgroup (Abelianization A))
  haveI : IsSimpleGroup (Abelianization A ⧸ K) :=
    (CommGroup.isSimpleGroup_iff_isCoatom).mpr hK
  have hprime : Nat.Prime (Nat.card (Abelianization A ⧸ K)) :=
    (Group.is_simple_iff_prime_card).mp ‹IsSimpleGroup _›
  -- The composite map `A →* Abelianization A →* Abelianization A ⧸ K`.
  let φ : A →* (Abelianization A ⧸ K) :=
    (QuotientGroup.mk' K).comp (Abelianization.of (G := A))
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective K y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (commutator A) b
    exact ⟨a, rfl⟩
  refine ⟨Nat.card (Abelianization A ⧸ K), hprime, φ.ker, inferInstance, ?_, ?_⟩
  · -- the kernel is proper, as the codomain is nontrivial and `φ` is surjective
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨y, hy⟩ := exists_ne (1 : Abelianization A ⧸ K)
    obtain ⟨x, hx⟩ := hsurj y
    rw [← hx] at hy
    have hxm : x ∈ φ.ker := htop ▸ Subgroup.mem_top x
    exact hy (MonoidHom.mem_ker.mp hxm)
  · -- first isomorphism theorem identifies the quotient with `Abelianization A ⧸ K`
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv

end Work.Solvable
