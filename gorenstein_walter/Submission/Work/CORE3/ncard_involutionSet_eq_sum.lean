import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.existsUnique_mul_of_normal_sup

/-!
# Counting the involutions of `H = U ⋊ S`, `U` of odd order

Let `H ≤ G` be a finite group, `U ⊴ H` a normal subgroup of **odd** order and `S ≤ H` a
complement of `U` in `H` (`U ⊔ S = H`, `U ⊓ S = ⊥`).  Then `H = U ⋊ S` and the involutions of
`H` (elements of order exactly `2`) are exactly the products `u * s` with `s` an involution of
`S` and `u ∈ I_U(s) = {x ∈ U : s x s⁻¹ = x⁻¹}`.  The map `(s, u) ↦ u * s` is bijective, so

`|{x ∈ H : x² = 1}| = ∑_{s ∈ I(S)} |I_U(s)|`

which is the statement of `ncard_involutionSet_eq_sum`.  This is the counting step of the
Gorenstein–Walter analysis of `C_G(t)`.

## Contents

* `Work.CORE3.orderOf_mul_invSet_iff` : the elementwise criterion
  `orderOf (u * s) = 2 ↔ orderOf s = 2 ∧ u ∈ invSet U s`;
* `Work.CORE3.existsUnique_mul_of_normal_sup` (imported) : the unique decomposition `x = u * s`;
* `Work.CORE3.ncard_involutionSet_eq_sum` : the cardinality statement.
-/

namespace Work.CORE3

open scoped Pointwise
open Subgroup

/-- **The involution criterion.**  In the internal semidirect product `H = U ⋊ S` with `U ⊴ H`
of odd order and `U ⊓ S = ⊥`, an element `u * s` (`u ∈ U`, `s ∈ S`) is an involution of `G`
(exactly: `orderOf (u * s) = 2`) if and only if `s` is an involution of `S` and `u` is inverted
by `s`.

The computation is `(u * s)² = u · (s * u * s⁻¹) · s²`, whose two factors lie in `U` and in `S`,
so that `(u * s)² = 1` splits via `U ⊓ S = ⊥` into `s² = 1` and `s * u * s⁻¹ = u⁻¹`.  Oddness
of `|U|` is exactly what rules out the case `s = 1`. -/
theorem orderOf_mul_invSet_iff {G : Type} [Group G] (U S H : Subgroup G)
    (hUH : U ≤ H) (hSH : S ≤ H) (hUnorm : (U.subgroupOf H).Normal)
    (hdisj : U ⊓ S = ⊥) (hUodd : Odd (Nat.card U))
    (u : G) (hu : u ∈ U) (s : G) (hs : s ∈ S) :
    orderOf (u * s) = 2 ↔ orderOf s = 2 ∧ u ∈ Work.GW2.invSet U s := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huH : u ∈ H := hUH hu
  have hsH : s ∈ H := hSH hs
  -- `s` normalises `U`, because `U ⊴ H ∋ s`.
  have hconj : s * u * s⁻¹ ∈ U := by
    have h2 := hUnorm.conj_mem (⟨u, huH⟩ : ↥H)
      (show (⟨u, huH⟩ : ↥H) ∈ U.subgroupOf H from by rw [Subgroup.mem_subgroupOf]; exact hu)
      (⟨s, hsH⟩ : ↥H)
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  -- an odd order subgroup has no element of order two other than `1`
  have hodd1 : ∀ {x : G}, x ∈ U → x * x = 1 → x = 1 := by
    intro x hx hxx
    have hd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    have hdU : orderOf x ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hx
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hd2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      rw [h1] at hdU
      exact (Nat.not_even_iff_odd.mpr hUodd) (even_iff_two_dvd.mpr hdU)
  constructor
  · intro h2
    have hpow : (u * s) * (u * s) = 1 := by
      have h3 : (u * s) ^ 2 = 1 := by
        rw [show (2 : ℕ) = orderOf (u * s) from h2.symm]
        exact pow_orderOf_eq_one _
      rwa [pow_two] at h3
    -- `(u * s)² = (u * (s * u * s⁻¹)) * (s * s)`, a product of an element of `U` and one of `S`
    have hkey : (u * (s * u * s⁻¹)) * (s * s) = 1 := by
      rw [← hpow]; group
    have haU : u * (s * u * s⁻¹) ∈ U := U.mul_mem hu hconj
    have hbS : s * s ∈ S := S.mul_mem hs hs
    have haS : u * (s * u * s⁻¹) ∈ S := by
      rw [← inv_eq_of_mul_eq_one_left hkey]; exact S.inv_mem hbS
    have ha1 : u * (s * u * s⁻¹) = 1 := by
      have h4 : u * (s * u * s⁻¹) ∈ (⊥ : Subgroup G) := by
        rw [← hdisj]; exact ⟨haU, haS⟩
      exact Subgroup.mem_bot.mp h4
    have hss : s * s = 1 := by
      rw [ha1, one_mul] at hkey; exact hkey
    have hx : s * u * s⁻¹ = u⁻¹ :=
      mul_left_cancel (show u * (s * u * s⁻¹) = u * u⁻¹ by rw [mul_inv_cancel]; exact ha1)
    refine ⟨?_, hu, hx⟩
    refine orderOf_eq_prime (p := 2) ?_ ?_
    · rw [pow_two]; exact hss
    · intro hs1
      -- `s = 1` would make `u` an involution of `U`, impossible in odd order
      have huinv : u = u⁻¹ := by
        have h3 : s * u * s⁻¹ = u⁻¹ := hx
        rw [hs1] at h3; simpa using h3
      have huu : u * u = 1 := by
        have h4 := congrArg (fun z : G => u * z) huinv
        rw [mul_inv_cancel] at h4
        exact h4
      have hu1 : u = 1 := hodd1 hu huu
      have h5 : u * s = 1 := by rw [hu1, hs1, one_mul]
      rw [h5, orderOf_one] at h2
      exact absurd h2 (by norm_num)
  · rintro ⟨hs2, hu_inv⟩
    obtain ⟨huU, hx⟩ := Work.CORE2A.mem_invSet.mp hu_inv
    have hss : s * s = 1 := by
      rw [← pow_two, ← hs2]; exact pow_orderOf_eq_one s
    refine orderOf_eq_prime (p := 2) ?_ ?_
    · rw [pow_two]
      have h3 : (u * s) * (u * s) = (u * (s * u * s⁻¹)) * (s * s) := by group
      rw [h3, hx, hss, mul_one, mul_inv_cancel]
    · intro h1
      -- `u * s = 1` forces `s ∈ U ⊓ S = ⊥`
      have hsU : s ∈ U := by
        have h4 : s = u⁻¹ :=
          mul_left_cancel (show u * s = u * u⁻¹ by rw [mul_inv_cancel]; exact h1)
        rw [h4]; exact U.inv_mem huU
      have hsbot : s ∈ (⊥ : Subgroup G) := by
        rw [← hdisj]; exact ⟨hsU, hs⟩
      rw [Subgroup.mem_bot.mp hsbot, orderOf_one] at hs2
      exact absurd hs2 (by norm_num)

/-- **Counting the involutions of a semidirect product.**  If `H = U ⊔ S` with `U ⊴ H` of odd
order and `U ⊓ S = ⊥`, then the number of involutions of `H` is the sum, over the involutions
`s` of the complement `S`, of the number of elements of `U` inverted by `s`.

The map `(s, u) ↦ u * s` is a bijection between `{(s,u) : s² = 1, s * u * s⁻¹ = u⁻¹}` and the
involutions of `H` (see `orderOf_mul_invSet_iff` and `existsUnique_mul_of_normal_sup`), and it
identifies the latter set with a disjoint union of `ncard`-many translates of the sets
`I_U(s) = invSet U s`. -/
theorem ncard_involutionSet_eq_sum {G : Type} [Group G] [Finite G] (H U S : Subgroup G)
    (hUH : U ≤ H) (hSH : S ≤ H) (hUnorm : (U.subgroupOf H).Normal)
    (hUS : U ⊔ S = H) (hdisj : U ⊓ S = ⊥) (hUodd : Odd (Nat.card U)) [Fintype ↥S] :
    (Work.GW2.involutionSet H).ncard =
      ∑ s : {s : ↥S // orderOf (s : G) = 2}, (Work.GW2.invSet U (s : G)).ncard := by
  classical
  -- the involutions of `H` are the disjoint union of the translates `I_U(s) * s`
  have hset : Work.GW2.involutionSet H =
      ⋃ s : {s : ↥S // orderOf (s : G) = 2},
        ((fun u : G => u * (s : G)) '' (Work.GW2.invSet U (s : G))) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxH, hx2⟩ := Work.CORE2A.mem_involutionSet.mp hx
      obtain ⟨p, hp, _⟩ :=
        existsUnique_mul_of_normal_sup U S H hUH hSH hUnorm hUS hdisj x hxH
      have hcrit := (orderOf_mul_invSet_iff U S H hUH hSH hUnorm hdisj hUodd
        (p.1 : G) p.1.2 (p.2 : G) p.2.2).mp (by rw [hp]; exact hx2)
      exact Set.mem_iUnion.mpr ⟨⟨p.2, hcrit.1⟩, (p.1 : G), hcrit.2, hp⟩
    · intro hx
      obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
      rw [Set.mem_image] at hxs
      obtain ⟨u, hu, hus⟩ := hxs
      obtain ⟨huU, -⟩ := Work.CORE2A.mem_invSet.mp hu
      have hord : orderOf (u * (s : G)) = 2 :=
        (orderOf_mul_invSet_iff U S H hUH hSH hUnorm hdisj hUodd u huU (s : G) (s : ↥S).2).mpr
          ⟨s.2, hu⟩
      exact Work.CORE2A.mem_involutionSet.mpr
        ⟨by rw [← hus]; exact H.mul_mem (hUH huU) (hSH (s : ↥S).2),
         by rw [← hus]; exact hord⟩
  -- distinct involutions of `S` give disjoint translates, by uniqueness of `u * s`
  have hpair : Pairwise (Function.onFun Disjoint
      (fun s : {s : ↥S // orderOf (s : G) = 2} =>
        ((fun u : G => u * (s : G)) '' (Work.GW2.invSet U (s : G))))) := by
    intro s t hst
    rw [Function.onFun_apply, Set.disjoint_left]
    intro x hxs hxt
    rw [Set.mem_image] at hxs hxt
    obtain ⟨u, hu, hus⟩ := hxs
    obtain ⟨v, hv, hvt⟩ := hxt
    have huU : u ∈ U := (Work.CORE2A.mem_invSet.mp hu).1
    have hvU : v ∈ U := (Work.CORE2A.mem_invSet.mp hv).1
    have heq : u * (s : G) = v * (t : G) := by rw [hus, hvt]
    have hkey : v⁻¹ * u = (t : G) * (s : G)⁻¹ := by
      calc v⁻¹ * u = v⁻¹ * (u * (s : G)) * (s : G)⁻¹ := by group
        _ = v⁻¹ * (v * (t : G)) * (s : G)⁻¹ := by rw [← heq]
        _ = (t : G) * (s : G)⁻¹ := by group
    have hmemU : v⁻¹ * u ∈ U := U.mul_mem (U.inv_mem hvU) huU
    have hmemS : v⁻¹ * u ∈ S := by
      rw [hkey]; exact S.mul_mem (t : ↥S).2 (S.inv_mem (s : ↥S).2)
    have hbot : v⁻¹ * u ∈ (⊥ : Subgroup G) := by
      have h4 : v⁻¹ * u ∈ U ⊓ S := ⟨hmemU, hmemS⟩
      rwa [hdisj] at h4
    have hvu : (v : G) = u := by
      have h4 := inv_eq_of_mul_eq_one_right (Subgroup.mem_bot.mp hbot)
      simpa using h4
    have h5 : u * (s : G) = u * (t : G) := by rw [heq, hvu]
    exact hst (Subtype.ext (Subtype.ext (mul_left_cancel h5)))
  have hfin : ∀ s : {s : ↥S // orderOf (s : G) = 2},
      ((fun u : G => u * (s : G)) '' (Work.GW2.invSet U (s : G))).Finite :=
    fun s => (Set.toFinite _).image _
  calc (Work.GW2.involutionSet H).ncard
      = (⋃ s : {s : ↥S // orderOf (s : G) = 2},
          ((fun u : G => u * (s : G)) '' (Work.GW2.invSet U (s : G)))).ncard := by rw [hset]
    _ = ∑ᶠ s : {s : ↥S // orderOf (s : G) = 2},
          ((fun u : G => u * (s : G)) '' (Work.GW2.invSet U (s : G))).ncard :=
        Set.ncard_iUnion_of_finite hfin hpair
    _ = ∑ᶠ s : {s : ↥S // orderOf (s : G) = 2},
          (Work.GW2.invSet U (s : G)).ncard := by
        refine finsum_congr fun s => ?_
        exact Set.ncard_image_of_injective _ (fun a b hab => mul_right_cancel hab)
    _ = ∑ s : {s : ↥S // orderOf (s : G) = 2},
          (Work.GW2.invSet U (s : G)).ncard := finsum_eq_sum_of_fintype _

end Work.CORE3
