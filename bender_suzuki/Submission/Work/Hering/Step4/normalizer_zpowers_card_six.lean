import Mathlib
import Submission.Work.Hering.InvSubgroup
import Submission.Work.Hering.Step4.card_six_mul_centralizer
import Submission.Work.Hering.Step4.centralizer_card_three_nz
import Submission.Work.Hering.Step4.count_order_three_nz
import Submission.Work.Hering.Step4.card_conjClass_mul_card_centralizer
import Submission.Work.Hering.Step4.normalizer_zpowers_two_mul

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step4

open LeanEval.GroupTheory.Defs Work.Hering

/-- With `|V| = 4` and `C_G(V)` a 2-group, the normaliser in `G` of `⟨z⟩` has order `6` for every
element `z` of order `3`.  Indeed `N_G(⟨z⟩) = C_G(z) ∪ g·C_G(z)` for an element `g` inverting `z`
(and `|C_G(z)| = 3`); no element of `G` can invert `z` only if the class of `z` has `|G| / 3`
elements, while the elements of order `3` are the `2 * |C_G(V)|` elements of the two cosets of
`C_G(V)` — so `z²` is conjugate to `z`. -/
theorem normalizer_zpowers_card_six {G : Type*} [Group G] [Finite G] {hDT : DTInv G}
    {h4 : HasFourGroup G}
    (hC : ∀ U : Subgroup G, U ≤ invSubgroup hDT h4 → Nat.card U = 4 →
      IsPGroup 2 ↥(Subgroup.centralizer (U : Set G)))
    (hV : Nat.card ↥(invSubgroup hDT h4) = 4) {z : G} (hz : orderOf z = 3) :
    Nat.card ↥(Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G)) = 6 := by
  -- `C = C_G(V)`, the kernel of the conjugation action of `G` on `V`.
  set C : Subgroup G := Subgroup.centralizer (((invSubgroup hDT h4) : Subgroup G) : Set G) with hCdef
  -- `|G| = 6 * |C_G(V)|`.
  have hcardG : Nat.card G = 6 * Nat.card ↥C := by rw [hCdef]; exact card_six_mul_centralizer hV
  -- `|C_G(z)| = 3`.
  have hCz : Nat.card ↥(Subgroup.centralizer ({z} : Set G)) = 3 :=
    centralizer_card_three_nz hC hV hz
  -- there are exactly `2 * |C_G(V)|` elements of order `3`.
  have hcount : Nat.card {g : G // orderOf g = 3} = 2 * Nat.card ↥C := by
    rw [hCdef]; exact count_order_three_nz hC hV
  -- the class of `z` has `|G| / |C_G(z)| = 2 * |C_G(V)|` elements.
  have hcl := card_conjClass_mul_card_centralizer (G := G) z
  rw [hCz, hcardG] at hcl
  have hclcard : Nat.card (ConjClasses.mk z).carrier = 2 * Nat.card ↥C := by omega
  -- the class of `z` is contained in the set of order-`3` elements
  set Ss : Set G := {g : G | orderOf g = 3} with hSdef
  have hsub : (ConjClasses.mk z).carrier ⊆ Ss := by
    intro y hy
    rw [ConjClasses.mem_carrier_iff_mk_eq] at hy
    have hconj : IsConj y z := (ConjClasses.mk_eq_mk_iff_isConj).mp hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    show orderOf y = 3
    have hord : orderOf y = orderOf z := by
      rw [← hc]
      exact (orderOf_conj c y).symm
    rw [hord, hz]
  -- ... and has the same cardinality, hence is the whole set of order-`3` elements.
  have hncard : Ss.ncard = (ConjClasses.mk z).carrier.ncard := by
    have h1 : Ss.ncard = Nat.card {g : G // orderOf g = 3} := (Nat.card_coe_set_eq Ss).symm
    have h2 : (ConjClasses.mk z).carrier.ncard = Nat.card (ConjClasses.mk z).carrier :=
      (Nat.card_coe_set_eq _).symm
    rw [h1, h2, hcount, hclcard]
  have heq : (ConjClasses.mk z).carrier = Ss :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq hncard)
  -- in particular `z ^ 2` is conjugate to `z`.
  have hz2mem : z ^ 2 ∈ (ConjClasses.mk z).carrier := by
    rw [heq]
    show orderOf (z ^ 2) = 3
    have hdvd : orderOf (z ^ 2) ∣ orderOf z := orderOf_pow_dvd 2
    rw [hz] at hdvd
    have hne1 : orderOf (z ^ 2) ≠ 1 := by
      intro hh
      have hz21 : z ^ 2 = 1 := orderOf_eq_one_iff.mp hh
      have h3dvd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz21
      rw [hz] at h3dvd
      omega
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hz2inv : z ^ 2 = z⁻¹ := by
    have h3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)
  have hconj2 : IsConj z (z ^ 2) := by
    have hmm : ConjClasses.mk (z ^ 2) = ConjClasses.mk z :=
      (ConjClasses.mem_carrier_iff_mk_eq).mp hz2mem
    exact isConj_comm.mp ((ConjClasses.mk_eq_mk_iff_isConj).mp hmm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj2
  -- so `g` inverts `z`, and `N_G(⟨z⟩)/C_G(z) ≅ Z/2`.
  have hg' : g * z * g⁻¹ = z⁻¹ := by rw [hg, hz2inv]
  rw [normalizer_zpowers_two_mul hz ⟨g, hg'⟩, hCz]

end Work.Hering.Step4
