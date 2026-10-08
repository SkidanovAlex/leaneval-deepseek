/-
Area A7F of the Gorenstein--Walter project: the two odd divisors `35` and `63` of `|A₇| = 2520`
are not the orders of subgroups of `A₇`.

`2520 = 2³ · 3² · 5 · 7`, so the odd divisors of `|A₇|` are `1, 3, 5, 7, 9, 15, 21, 35, 45, 63,
105, 315`.  The two sitting strictly between `21` and `45` are excluded here:

* a subgroup `X` of order `35 = 5 · 7` or `63 = 9 · 7` contains a subgroup of order `7`
  (Cauchy's theorem);
* because `7² ∤ 35, 63`, such a subgroup of order `7` is a Sylow `7`-subgroup of `X`, and Sylow's
  third theorem forces it to be the unique one, so it is normal in `X`;
* the normalizer in `A₇` of any subgroup of order `7` has order `21`
  (`Work.A7F.normalizer_zpowers_order_seven`: this is the Frobenius group `7 : 3 = AGL(1,7) ∩ A₇`);
* hence `X`, being contained in that normalizer, would have order at most `21` — contradiction.

The oddness hypothesis `hodd` is carried along from the request but is in fact redundant: a group
of order `35` or `63` is odd-order by definition of those numbers.
-/
import Mathlib
import Submission.Work.A7F.Defs
import Submission.Work.A7F.normalizer_zpowers_order_seven

set_option linter.style.haveILetI false

namespace Work.A7F

open Subgroup

/-! ### Two general group-theoretic inputs -/

/-- In a finite group of order `35` or `63`, every subgroup of order `7` is normal.

`35 = 5 · 7` and `63 = 9 · 7` are divisible by `7` but not by `7²`, so a subgroup `H` of order `7`
is a Sylow `7`-subgroup.  By Sylow's third theorem the number `n₇` of Sylow `7`-subgroups divides
the index of `H` (`5` or `9`) and satisfies `n₇ ≡ 1 (mod 7)`; among the divisors of `5` or `9` only
`1` has that property.  Hence the Sylow `7`-subgroup is unique, and `H`, being one, equals it, so
`H` is normal. -/
theorem normal_of_card_seven_of_card_35_63 (G : Type) [Group G] [Finite G]
    (h : Nat.card G = 35 ∨ Nat.card G = 63) (H : Subgroup G) (hH : Nat.card H = 7) :
    H.Normal := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hidx : H.index = Nat.card G / 7 := by rw [Subgroup.index_eq_card_div, hH]
  have hidx' : H.index = 5 ∨ H.index = 9 := by
    rw [hidx]
    rcases h with h | h <;> rw [h] <;> norm_num
  have hnotdvd : ¬ 7 ∣ H.index := by
    rcases hidx' with hi | hi <;> rw [hi] <;> norm_num
  -- `H` is a Sylow `7`-subgroup.
  have hP1 : IsPGroup 7 ↥H := IsPGroup.of_card (n := 1) (by rw [hH]; norm_num)
  let P : Sylow 7 G := hP1.toSylow hnotdvd
  haveI hne : Nonempty (Sylow 7 G) := ⟨P⟩
  haveI hfin : Finite (Sylow 7 G) := P.finite_of_finiteIndex
  -- ... and it is the only one.
  have hdvd : Nat.card (Sylow 7 G) ∣ H.index := by
    have hd := P.card_dvd_index
    simpa [P] using hd
  have hmod : Nat.card (Sylow 7 G) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 G
  have hcard1 : Nat.card (Sylow 7 G) = 1 := by
    have hm : Nat.card (Sylow 7 G) % 7 = 1 := by
      have hh := hmod
      rw [Nat.ModEq] at hh
      simpa using hh
    have hge : 1 ≤ Nat.card (Sylow 7 G) := Nat.card_pos
    rcases hidx' with hi | hi
    · -- `n₇ ∣ 5` and `n₇ ≤ 5`; among `1, …, 5` only `1` is `≡ 1 (mod 7)`.
      have h5 : Nat.card (Sylow 7 G) ∣ 5 := by rwa [hi] at hdvd
      have hle : Nat.card (Sylow 7 G) ≤ 5 := Nat.le_of_dvd (by norm_num) h5
      interval_cases Nat.card (Sylow 7 G)
      · rfl
      · exact absurd hm (by norm_num)
      · exact absurd hm (by norm_num)
      · exact absurd hm (by norm_num)
      · exact absurd hm (by norm_num)
    · -- `n₇ ∣ 9` and `n₇ ≤ 9`; the divisors of `9` are `1, 3, 9`, of which only `1` is
      -- `≡ 1 (mod 7)`.
      have h9 : Nat.card (Sylow 7 G) ∣ 9 := by rwa [hi] at hdvd
      have hle : Nat.card (Sylow 7 G) ≤ 9 := Nat.le_of_dvd (by norm_num) h9
      interval_cases Nat.card (Sylow 7 G)
      · rfl
      · exact absurd hm (by norm_num)
      · exact absurd hm (by norm_num)
      · exact absurd hm (by norm_num)
      · exact absurd hm (by norm_num)
      · exact absurd hm (by norm_num)
      · exact absurd hm (by norm_num)
      · exact absurd h9 (by norm_num)
      · exact absurd hm (by norm_num)
  haveI : Subsingleton (Sylow 7 G) := Finite.card_le_one_iff_subsingleton.mp hcard1.le
  have hPn : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  simpa [P] using hPn

/-- If `N` is normal in a subgroup `X` of `G`, then `X` normalizes the image of `N` in `G`:
conjugation in `X` is the restriction of conjugation in `G`. -/
theorem le_normalizer_map_subtype {G : Type*} [Group G] (X : Subgroup G) (N : Subgroup ↥X)
    (hN : N.Normal) : X ≤ Subgroup.normalizer (N.map X.subtype : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * z * ⟨x, hx⟩⁻¹, hN.conj_mem z hz ⟨x, hx⟩, ?_⟩
  simp

/-! ### The exclusion of the orders `35` and `63` in `A₇` -/

theorem no_odd_subgroup_card_35_63 (X : Subgroup (alternatingGroup (Fin 7)))
    (hodd : Odd (Nat.card X)) : Nat.card X ≠ 35 ∧ Nat.card X ≠ 63 := by
  -- The oddness hypothesis is not needed below: `35` and `63` are odd, so a subgroup of one of
  -- those orders would have odd order automatically.
  have _hodd := hodd
  have key : Nat.card X = 35 ∨ Nat.card X = 63 → Nat.card X ≤ 21 := by
    intro hcard
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have h7dvd : 7 ∣ Nat.card X := by
      rcases hcard with h | h <;> rw [h] <;> norm_num
    -- Cauchy: `X` has an element of order `7`.
    obtain ⟨c, hc⟩ : ∃ c : ↥X, orderOf c = 7 :=
      exists_prime_orderOf_dvd_card' (G := ↥X) 7 h7dvd
    have hH7 : Nat.card (Subgroup.zpowers c) = 7 := by rw [Nat.card_zpowers, hc]
    -- `⟨c⟩` is the unique subgroup of order `7` of `X`, hence normal in `X`.
    have hnormal : (Subgroup.zpowers c).Normal :=
      normal_of_card_seven_of_card_35_63 ↥X hcard (Subgroup.zpowers c) hH7
    -- so `X` normalizes the image of `⟨c⟩` in `A₇` ...
    have hle : X ≤ Subgroup.normalizer
        ((Subgroup.zpowers c).map X.subtype : Set (alternatingGroup (Fin 7))) :=
      le_normalizer_map_subtype X (Subgroup.zpowers c) hnormal
    -- ... i.e. `X ≤ N_{A₇}(⟨c⟩)`, a group of order `21`.
    have hN21 : Nat.card (Subgroup.normalizer
        ((Subgroup.zpowers c).map X.subtype : Set (alternatingGroup (Fin 7)))) = 21 := by
      rw [MonoidHom.map_zpowers]
      refine normalizer_zpowers_order_seven (X.subtype c) ?_
      show orderOf ((c : ↥X) : alternatingGroup (Fin 7)) = 7
      rw [Subgroup.orderOf_coe, hc]
    calc Nat.card X ≤ Nat.card (Subgroup.normalizer
          ((Subgroup.zpowers c).map X.subtype : Set (alternatingGroup (Fin 7)))) :=
        Nat.card_le_card_of_injective
          (fun x : ↥X => (⟨(x : alternatingGroup (Fin 7)), hle x.2⟩ :
            ↥(Subgroup.normalizer ((Subgroup.zpowers c).map X.subtype :
              Set (alternatingGroup (Fin 7))))))
          (fun a b hab => Subtype.ext (congrArg
            (Subtype.val : ↥(Subgroup.normalizer ((Subgroup.zpowers c).map X.subtype :
              Set (alternatingGroup (Fin 7)))) → alternatingGroup (Fin 7)) hab))
      _ = 21 := hN21
  constructor
  · intro h35
    have h := key (Or.inl h35)
    rw [h35] at h
    exact absurd h (by norm_num)
  · intro h63
    have h := key (Or.inr h63)
    rw [h63] at h
    exact absurd h (by norm_num)

end Work.A7F
