import Mathlib
import Submission.Work.BSW.Defs
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Cases.K4.exists_not_mem_centralizer_of_isPGroup
import Submission.Work.BSW.Cases.K4.card_centralizer_sylow_five_le
import Submission.Work.BSW.Cases.K4.ncard_orderOf_eq_fifteen_eq_eight

set_option linter.style.haveILetI false

namespace Work.BSW.Cases.K4

/-- An element `x` of order `15` of a group of order `360` is centralized by the Sylow
`5`-subgroup `⟨x³⟩` (which has order `5`, hence is a Sylow `5`-subgroup as `5² ∤ 360`). -/
theorem exists_sylow_five_centralizes_of_orderOf_eq_fifteen {G : Type} [Group G] [Finite G]
    {x : G} (hx : orderOf x = 15) (hG : Nat.card G = 360) :
    ∃ P : Sylow 5 G, x ∈ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  -- `⟨x³⟩` has order `5`.
  let H : Subgroup G := Subgroup.zpowers (x ^ 3)
  have hHcard : Nat.card ↥H = 5 := by
    show Nat.card ↥(Subgroup.zpowers (x ^ 3)) = 5
    rw [Nat.card_zpowers, orderOf_pow, hx]
    norm_num
  -- A subgroup of order `5` is a Sylow `5`-subgroup, since `|G| = 360` has `5`-part `5`.
  have hcardeq : Nat.card ↥H = 5 ^ (Nat.card G).factorization 5 := by
    rw [hHcard, hG]
    norm_num [Nat.factorization]
  refine ⟨Sylow.ofCard H hcardeq, ?_⟩
  have hPeq : ((Sylow.ofCard H hcardeq : Sylow 5 G) : Subgroup G) = H :=
    Sylow.coe_ofCard H hcardeq
  -- `x` commutes with every power of `x³`.
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [hPeq] at hh
  change h ∈ Subgroup.zpowers (x ^ 3) at hh
  rw [Subgroup.mem_zpowers_iff] at hh
  obtain ⟨k, hk⟩ := hh
  rw [← hk, ← zpow_natCast x 3]
  exact ((Commute.refl x).zpow_right 3).zpow_right k |>.eq.symm

/-- For a fixed Sylow `5`-subgroup `P` of the simple nonabelian group `G` of order `360` with
`n₅ = 6`, at most `8` elements of `G` have order `15` and centralize `P`: the centralizer has
order at most `30` (`card_centralizer_sylow_five_le`) and a group of order `≤ 30` containing an
element of order `15` has exactly `8` elements of order `15`
(`ncard_orderOf_eq_fifteen_eq_eight`). -/
theorem ncard_centralizer_sylow_five_orderOf_fifteen_le {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hG : Nat.card G = 360)
    (h5 : Nat.card (Sylow 5 G) = 6) (P : Sylow 5 G) :
    {x : G | orderOf x = 15 ∧ x ∈ Subgroup.centralizer ((P : Subgroup G) : Set G)}.ncard ≤ 8 := by
  set C := Subgroup.centralizer ((P : Subgroup G) : Set G) with hC
  have hle : Nat.card ↥C ≤ 30 := card_centralizer_sylow_five_le hnab hG h5 P
  -- The elements of `G` of order `15` lying in `C` correspond to the elements of `C` of order `15`.
  have key : {x : G | orderOf x = 15 ∧ x ∈ C}.ncard ≤ {y : ↥C | orderOf y = 15}.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    let f : {x : G // orderOf x = 15 ∧ x ∈ C} → {y : ↥C // orderOf y = 15} :=
      fun x => ⟨⟨x.1, x.2.2⟩, by rw [Subgroup.orderOf_mk]; exact x.2.1⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h1 : (⟨x.1, x.2.2⟩ : ↥C) = ⟨y.1, y.2.2⟩ := congrArg (fun z => z.1) hxy
      have h2 : x.1 = y.1 := congrArg (fun z : ↥C => (z : G)) h1
      exact Subtype.ext h2
    exact Nat.card_le_card_of_injective f hf
  have htle : {y : ↥C | orderOf y = 15}.ncard ≤ 8 := by
    by_cases hex : ∃ y : ↥C, orderOf y = 15
    · rw [ncard_orderOf_eq_fifteen_eq_eight hex hle]
    · push Not at hex
      have hempty : {y : ↥C | orderOf y = 15} = ∅ := by ext y; simp [hex y]
      rw [hempty]; simp
  exact le_trans key htle

/-- In the simple nonabelian group `G` of order `360` with `n₅ = 6`, the number of elements of
order `15` is at most `48` (this is the `n₅ = 6` branch of the proof that `n₅ = 36`).

An element `x` of order `15` satisfies `x ∈ C_G(P)` for the Sylow `5`-subgroup `P := ⟨x³⟩` (as
`x³` has order `5`), so the set of elements of order `15` is contained in the union of the sets
`{x : G | x ∈ C_G(P) ∧ orderOf x = 15}` over the `6` Sylow `5`-subgroups `P`
(`IsPGroup.exists_le_sylow` to see `⟨x³⟩` is a Sylow `5`-subgroup).  For each `P`,
`|C_G(P)|` divides `|N_G(P)| = 360/6 = 60`, is divisible by `5` (as `P ≤ C_G(P)`), and is not `60`
(otherwise `N_G(P) ≤ C_G(P)` and Burnside's normal `p`-complement theorem
`Work.BSW.Cases.K4.exists_not_mem_centralizer_of_isPGroup` is contradicted by simplicity); hence
`|C_G(P)| ≤ 30`, and a group of order `≤ 30` containing an element of order `15` has exactly `8`
elements of order `15` (its elements of order `15` all lie in the index-`2`/full cyclic subgroup
of order `15`, giving `Nat.totient 15 = 8` of them).  A union bound
(`Set.ncard_iUnion_le_of_fintype`) then gives `≤ 8 · 6 = 48`. -/
theorem ncard_orderOf_eq_fifteen_le {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hK4 : Nat.card ↥K = 4) (hG : Nat.card G = 360)
    (h5 : Nat.card (Sylow 5 G) = 6) :
    {x : G | orderOf x = 15}.ncard ≤ 48 := by
  haveI hfin : Finite (Sylow 5 G) := Nat.finite_of_card_ne_zero (by rw [h5]; norm_num)
  haveI : Fintype (Sylow 5 G) := Fintype.ofFinite _
  let B : Sylow 5 G → Set G := fun P =>
    {x : G | orderOf x = 15 ∧ x ∈ Subgroup.centralizer ((P : Subgroup G) : Set G)}
  -- Every element of order `15` lies in `C_G(P)` for some Sylow `5`-subgroup `P`.
  have hcover : {x : G | orderOf x = 15} ⊆ ⋃ P, B P := by
    intro x hx
    obtain ⟨P, hP⟩ := exists_sylow_five_centralizes_of_orderOf_eq_fifteen hx hG
    exact Set.mem_iUnion.mpr ⟨P, hx, hP⟩
  -- Union bound over the `6` Sylow `5`-subgroups, each contributing at most `8` elements.
  calc {x : G | orderOf x = 15}.ncard
      ≤ (⋃ P, B P).ncard := Set.ncard_le_ncard hcover
    _ ≤ ∑ P, (B P).ncard := Set.ncard_iUnion_le_of_fintype B
    _ ≤ ∑ _P : Sylow 5 G, 8 :=
        Finset.sum_le_sum (fun P _ => ncard_centralizer_sylow_five_orderOf_fifteen_le hnab hG h5 P)
    _ = 48 := by
        rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, h5]
        norm_num

end Work.BSW.Cases.K4
