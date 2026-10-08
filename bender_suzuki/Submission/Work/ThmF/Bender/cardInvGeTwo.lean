import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.Bender.twoInvolutionsOdd
import Submission.Work.ThmF.Bender.existsInvolutionConjugating

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi I, Ch. I §2: `|Inv(H)| ≥ 2`

If `H` is strongly embedded in a finite group `G` of 2-rank `≥ 2` (`HasFourGroup G`), then `H`
contains at least two involutions.  This is the fact that makes `n = |Inv(H)|` at least `2` in
the notation of Peterfalvi I, Ch. I §2.

The proof uses the elementary properties of strongly embedded subgroups established in Ch. I §1:

* every involution of `G` lies in a conjugate of `H` (`exists_conj_of_involution` below,
  Ch. I §1 (3));
* the centraliser of an involution of a strongly embedded subgroup is contained in it
  (`Work.ThmF.centralizer_involution_le`, Ch. I §1 (2));
* conjugates of a strongly embedded subgroup are strongly embedded
  (`Work.Models.IsStronglyEmbedded.conj`).

Let `a, b` be distinct commuting involutions of `G` (the hypothesis `HasFourGroup`).  Pick `g`
with `a ∈ H^g`.  Since `H^g` is strongly embedded and `a ∈ H^g` is an involution,
`C_G(a) ≤ H^g`; as `b` commutes with `a`, also `b ∈ H^g`.  So `H^g` contains the two distinct
involutions `a` and `b` (indeed the whole four-group `{1, a, b, ab}`).  Conjugation by `g` is a
bijection carrying the involutions of `H` onto those of `H^g`
(`Work.Models.involutions_conj`), so `H` itself contains at least two involutions.

The two ingredients `twoInvolutionsOdd` and `existsInvolutionConjugating` do not mention the
group `G` of the theorem: the first says that for `s ∈ H` an involution and `t ∉ H` an
involution the product `s * t` has odd order, the second that two involutions with an odd-order
product are conjugate (by an involution).
-/

namespace Work.ThmF.Bender

open LeanEval.GroupTheory.Defs

open Submission.Blueprint

/-- A strongly embedded subgroup has even order, hence contains an involution (Cauchy's
theorem). -/
theorem exists_involution_mem_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : IsStronglyEmbedded H) : ∃ u : G, u ∈ H ∧ orderOf u = 2 := by
  have h2 : 2 ∣ Nat.card H := even_iff_two_dvd.mp hH.2.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 h2
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe, hx]⟩

/-- **Peterfalvi I, Ch. I §1 (3)–(2).**  Every involution of a finite group with a strongly
embedded subgroup `H` lies in a conjugate of `H`.

If `v ∉ H`, then `u * v` has odd order for any involution `u ∈ H` (this is exactly the content
of `twoInvolutionsOdd`, and it says that `H ∩ H^v` has no involution — Ch. I §1 (2)); by
`existsInvolutionConjugating`, some involution `x` conjugates `u` to `v`, i.e. `v ∈ H^x`. -/
theorem exists_conj_of_involution {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {v : G} (hv : orderOf v = 2) : ∃ g : G, v ∈ conj g H := by
  by_cases hvH : v ∈ H
  · exact ⟨1, by rw [Work.Models.conj_one]; exact hvH⟩
  · obtain ⟨u, huH, hu2⟩ := exists_involution_mem_of_isStronglyEmbedded hH
    have hodd : Odd (orderOf (u * v)) := twoInvolutionsOdd hH huH hu2 hv hvH
    obtain ⟨x, -, hxu⟩ := existsInvolutionConjugating hu2 hv hodd
    refine ⟨x, (Work.Models.mem_conj_iff).mpr ?_⟩
    rw [show x⁻¹ * v * x = u from by rw [← hxu]; group]
    exact huH

/-- A strongly embedded subgroup containing two distinct commuting involutions contains at
least two involutions: it contains the centraliser of either of them (Peterfalvi I, Ch. I
§1 (2)), hence the whole four-group they generate. -/
theorem two_le_ncard_involutions_of_commuting_involutions {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} (hK : IsStronglyEmbedded K) {a b : G} (ha : a ∈ K)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hne : a ≠ b) (hcomm : a * b = b * a) :
    2 ≤ (involutions (K : Set G)).ncard := by
  have hC : Subgroup.centralizer ({a} : Set G) ≤ K :=
    Work.ThmF.centralizer_involution_le hK ha ha2
  have hbC : b ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hcomm
  have hbK : b ∈ K := hC hbC
  have hsub : ({a, b} : Set G) ⊆ involutions (K : Set G) := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨ha, ha2⟩
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨hbK, hb2⟩
  have h := Set.ncard_le_ncard hsub
  rwa [Set.ncard_pair hne] at h

open LeanEval.GroupTheory.Defs Submission.Blueprint in theorem cardInvGeTwo {G : Type*} [Group G] [Finite G] {H : Subgroup G} (hH : IsStronglyEmbedded H) (hfour : HasFourGroup G) : 2 ≤ (involutions (H : Set G)).ncard := by
  obtain ⟨a, b, ha2, hb2, hne, hcomm⟩ := hfour
  -- `a` is an involution, so it lies in a conjugate of `H` (Peterfalvi I, Ch. I §1 (3)).
  obtain ⟨g, hga⟩ := exists_conj_of_involution hH ha2
  have hK : IsStronglyEmbedded (conj g H) := Work.Models.IsStronglyEmbedded.conj hH g
  -- hence the four-group `{1, a, b, ab}` lies in `H^g`
  have h2K : 2 ≤ (involutions ((conj g H : Subgroup G) : Set G)).ncard :=
    two_le_ncard_involutions_of_commuting_involutions hK hga ha2 hb2 hne hcomm
  -- conjugation by `g` identifies the involutions of `H` with those of `H^g`
  have hcard : (involutions ((conj g H : Subgroup G) : Set G)).ncard
      = (involutions (H : Set G)).ncard := by
    rw [Work.Models.involutions_conj g H]
    exact Set.ncard_image_of_injective _ (fun x y hxy => mul_left_cancel (mul_right_cancel hxy))
  rw [hcard] at h2K
  exact h2K

end Work.ThmF.Bender
