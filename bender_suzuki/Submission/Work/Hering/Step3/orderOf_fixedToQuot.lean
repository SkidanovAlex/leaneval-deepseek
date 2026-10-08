import Mathlib
import Submission.Work.Hering.Step3.NormalizerQuotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The class of a `P`-fixed involution in `N_G(P)/P` has order `2`

Let `P` be a subgroup of odd order and `s ∈ Inv(G)` an involution fixed by `P` (equivalently
`s ∈ C_G(P) ≤ N_G(P)`). Then the class of `s` in `N_G(P)/P` is an involution:

* its square is `1`, because `s^2 = 1` and `N_G(P) → N_G(P)/P` is a homomorphism;
* it is not `1`, because that would force `s ∈ P`, and an odd order group has no element of
  order `2`.
-/

namespace Work.Hering.Step3

open Work.Hering

theorem orderOf_fixedToQuot {G : Type*} [Group G] {P : Subgroup G} (hPodd : Odd (Nat.card P))
    (s : {x : G // x ∈ involutions G}) (hs : s ∈ involutionsFixedBy P) :
    orderOf (fixedToQuot P s hs) = 2 := by
  let N := P.subgroupOf (Subgroup.normalizer (P : Set G))
  let g : ↥(Subgroup.normalizer (P : Set G)) :=
    ⟨(s : G), mem_normalizer_of_mem_involutionsFixedBy hs⟩
  have hfq : fixedToQuot P s hs = QuotientGroup.mk' N g := rfl
  -- `s` is an involution, so its image `g` in `N_G(P)` also satisfies `g ^ 2 = 1`.
  have hg2 : g ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    show (g : G) ^ 2 = ((1 : ↥(Subgroup.normalizer (P : Set G))) : G)
    rw [show (g : G) = (s : G) from rfl]
    rw [show ((1 : ↥(Subgroup.normalizer (P : Set G))) : G) = 1 from rfl]
    rw [pow_two, sq_eq_one_of_orderOf_eq_two s.2]
  have hpow : (fixedToQuot P s hs) ^ 2 = 1 := by
    rw [hfq, ← map_pow, hg2, map_one]
  -- `s ∉ P`, since `P` has odd order while `s` has order `2`.
  have hne : fixedToQuot P s hs ≠ 1 := by
    rw [hfq]
    intro h1
    have hgN : g ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) g).mp (by simpa using h1)
    have hsP : (s : G) ∈ P := by
      have := Subgroup.mem_subgroupOf.mp hgN
      simpa using this
    have hodd : Odd (orderOf (s : G)) := Odd.of_dvd_nat hPodd (P.orderOf_dvd_natCard hsP)
    rw [show orderOf (s : G) = 2 from s.2] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  exact orderOf_eq_prime hpow hne

end Work.Hering.Step3
