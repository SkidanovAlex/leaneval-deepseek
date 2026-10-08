import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Api.card_centralizer_of_card_K_two
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Cases.sylow_two_structure
import Submission.Work.BSW.Cases.normalizer_centralizer_card
import Submission.Work.BSW.Cases.normalizer_centralizer_structure
import Submission.Work.BSW.Cases.sylow_number_and_ncard
import Submission.Work.BSW.Cases.K2Count.three_not_dvd_sylow_two
import Submission.Work.BSW.Cases.K2Count.k2_inv_count_of_ne
import Submission.Work.BSW.Cases.k2_count_involutions_outside

/-!
# The `|K| = 2` case of Bender's BSW theorem: `|G| = 60`

This file assembles Bender's counting argument (`REFS/bender1974_bsw.txt`, p. 230) for the case
`|K| = 2`.  With `H = C_G(t) = K ⊔ ⟨s⟩` of order `4` (a Sylow 2-subgroup) and `N = N_G(H)`:

* `Work.BSW.Cases.sylow_two_structure`: every Sylow 2-subgroup has order `4`, `C_G(u)` (for an
  involution `u`) is the unique Sylow 2-subgroup containing `u`, distinct Sylow 2-subgroups
  intersect trivially.
* `Work.BSW.Cases.normalizer_centralizer_card`: `|N| = 12` (hence `|N : H| = 3`).
* `Work.BSW.Cases.normalizer_centralizer_structure`: `N` has exactly four subgroups of order `3`,
  every element of `N ∖ H` has order `3`, and `T ≤ N` of order `3` is self-normalizing in `N`.
* `Work.BSW.Cases.sylow_number_and_ncard`: `12 n₂ = |G|`, `n₂ % 4 = 1`, `5 ≤ n₂`, where
  `n₂ = Nat.card (Sylow 2 G)`; in particular `3 ∤ n₂` will follow from the character-theoretic
  `Work.BSW.Cases.K2Count.three_not_dvd_sylow_two`.

Write `I = #{u : G // orderOf u = 2}`, `m = #{u : orderOf u = 2, u ∉ N}` and, for a subgroup
`T ≤ N` of order `3`, `c = #{u : orderOf u = 2, u ∈ N_G(T)}`.  Then

* `I = |G : H| = 3 n₂` (the involutions are exactly the conjugates of `t`), and the involutions of
  `N` are exactly the three involutions of `H`, so `m = 3 n₂ - 3 = 3 (n₂ - 1)`;
* `m = 4 c` (`k2_count_involutions_outside`: every involution outside `N` normalizes exactly one of
  the four subgroups of order `3`, and the count is independent of the subgroup because the four
  are conjugate in `N`);
* `c = |C_G(T)|`: first `N_G(T) ≠ C_G(T)` — otherwise `N_G(T) = C_G(T)` has odd order
  (no involution commutes with a nonidentity element of odd order, `no_involution_centralizes_odd`),
  so `c = 0` and `m = 4 c = 0` gives `n₂ = 1`, contradicting `5 ≤ n₂`; then
  `Work.BSW.Cases.K2Count.k2_inv_count_of_ne` shows that an involution of `N_G(T)` inverts the
  odd-order group `C_G(T)`, so that every element of `N_G(T) ∖ C_G(T)` is an involution and
  `c = |C_G(T)|`;
* `|C_G(T)| ∣ |G| = 12 n₂` (Lagrange) and `|C_G(T)|` is odd.

So `4 |C_G(T)| = 3 (n₂ - 1)` and `|C_G(T)| ∣ 12 n₂` with `|C_G(T)|` odd force `|C_G(T)| = 3` and
`n₂ = 5`, whence `|G| = 12 · 5 = 60` (`k2_order_arith`).

The two inputs not proved here are `Work.BSW.Cases.k2_count_involutions_outside` (the double count
`m = 4 c`) and `Work.BSW.Cases.K2Count.k2_inv_count_of_ne` (the involution of `N_G(T)` inverts
`C_G(T)`); together with the character-theoretic `Work.BSW.Cases.K2Count.three_not_dvd_sylow_two`
(`3 ∤ n₂`) and `Work.BSW.Cases.sylow_number_and_ncard` (`12 n₂ = |G|`, `n₂ ≡ 1 mod 4`, `n₂ ≥ 5`).
-/

namespace Work.BSW.Cases

open Subgroup Work.GW2

/-- **No involution commutes with a nonidentity element of odd order.**

In the `|K| = 2` case every involution `u` has `|C_G(u)| = 4`
(`Work.BSW.Cases.sylow_two_structure`).  If `x ≠ 1` had odd order and `u x = x u`, then `x` would
lie in `C_G(u)`, so `orderOf x ∣ 4`; being odd, `orderOf x = 1`, i.e. `x = 1`. -/
theorem no_involution_centralizes_odd {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    ∀ x : G, x ≠ 1 → Odd (orderOf x) → ∀ u : G, orderOf u = 2 → ¬ (u * x = x * u) := by
  intro x hx1 hxodd u hu hcomm
  obtain ⟨-, hcen, -, -⟩ := Work.BSW.Cases.sylow_two_structure t s K h hk
  have hxmem : x ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm
  have hdvd : orderOf x ∣ Nat.card ↥(Subgroup.centralizer ({u} : Set G)) := by
    have hle : Subgroup.zpowers x ≤ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.zpowers_le.mpr hxmem
    have h' := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers] at h'
  rw [hcen u hu] at hdvd
  have hpos : 0 < orderOf x := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases hx : orderOf x
  · exact hx1 (orderOf_eq_one_iff.mp hx)
  · rcases hxodd with ⟨m, hm⟩; omega
  · exact absurd hdvd (by norm_num)
  · rcases hxodd with ⟨m, hm⟩; omega

/-- The number of involutions in `N = N_G(C_G(t))` is `3`: the involutions of `N` are exactly the
three involutions of `C_G(t)` (`Work.BSW.Cases.ncc_involutions_centralizer_t`), because every
element of `N ∖ C_G(t)` has order `3`
(`Work.BSW.Cases.normalizer_centralizer_structure`). -/
theorem k2_involutions_normalizer_card {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) :
    Nat.card {u : G // orderOf u = 2 ∧
        u ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)} = 3 := by
  have hstruct := Work.BSW.Cases.normalizer_centralizer_structure t s K h hk
  have h3 := Work.BSW.Cases.ncc_involutions_centralizer_t h hk
  have he : Nat.card {u : G // orderOf u = 2 ∧
        u ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)}
      = Nat.card {y : G // y ∈ Subgroup.centralizer ({t} : Set G) ∧ orderOf y = 2} :=
    Nat.card_congr
      { toFun := fun u => ⟨u.1, ⟨by
          by_contra hnot
          have hord := hstruct.1 u.1 u.2.2 hnot
          omega, u.2.1⟩⟩
        invFun := fun y => ⟨y.1, y.2.2, Subgroup.le_normalizer y.2.1⟩
        left_inv := fun u => Subtype.ext rfl
        right_inv := fun y => Subtype.ext rfl }
  rw [he]
  exact h3

/-- The total number of involutions of `G` is `3 n₂`, where `n₂ = Nat.card (Sylow 2 G)`: it is
`|G : C_G(t)| = |G| / 4 = 12 n₂ / 4`. -/
theorem k2_involutions_total_card {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    (hcardG : 12 * Nat.card (Sylow 2 G) = Nat.card G) :
    Nat.card {u : G // orderOf u = 2} = 3 * Nat.card (Sylow 2 G) := by
  have hI : ({x : G | orderOf x = 2} : Set G).ncard
      = (Subgroup.centralizer ({t} : Set G)).index := Work.BSW.Api.ncard_involutions_eq_index h
  have hI' : Nat.card {u : G // orderOf u = 2}
      = (Subgroup.centralizer ({t} : Set G)).index := hI
  have hH4 : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 4 :=
    Work.BSW.Api.card_centralizer_of_card_K_two h hk
  have him := Subgroup.index_mul_card (Subgroup.centralizer ({t} : Set G))
  rw [hH4, ← hcardG] at him
  have hidx : (Subgroup.centralizer ({t} : Set G)).index = 3 * Nat.card (Sylow 2 G) := by
    have h3 : (Subgroup.centralizer ({t} : Set G)).index * 4
        = (3 * Nat.card (Sylow 2 G)) * 4 := by omega
    exact Nat.mul_right_cancel (by norm_num : 0 < 4) h3
  rw [hI', hidx]

/-- The number of involutions outside `N = N_G(C_G(t))` is `3 n₂ - 3 = 3 (n₂ - 1)`: the involutions
split into those in `N` (three of them) and those outside. -/
theorem k2_involutions_outside_card {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    (hcardG : 12 * Nat.card (Sylow 2 G) = Nat.card G) :
    Nat.card {u : G // orderOf u = 2 ∧
        u ∉ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)}
      = 3 * Nat.card (Sylow 2 G) - 3 := by
  have hN := k2_involutions_normalizer_card h hk
  have hI := k2_involutions_total_card h hk hcardG
  classical
  have hpart : Nat.card {u : G // orderOf u = 2} =
      Nat.card {u : G // orderOf u = 2 ∧
          u ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)} +
        Nat.card {u : G // orderOf u = 2 ∧
          u ∉ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)} := by
    have hdisj : Disjoint ({u : G | orderOf u = 2 ∧
          u ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)} : Set G)
        {u : G | orderOf u = 2 ∧
          u ∉ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)} := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hxN⟩ ⟨-, hxN'⟩
      exact hxN' hxN
    have hunion : ({u : G | orderOf u = 2 ∧
            u ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)} : Set G) ∪
          {u : G | orderOf u = 2 ∧
            u ∉ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)}
        = {u : G | orderOf u = 2} := by
      ext x
      constructor
      · rintro (⟨hx2, -⟩ | ⟨hx2, -⟩) <;> exact hx2
      · intro hx2
        by_cases hxN : x ∈ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)))
        · exact Or.inl ⟨hx2, hxN⟩
        · exact Or.inr ⟨hx2, hxN⟩
    have h1 := Set.ncard_union_eq hdisj
    rw [hunion] at h1
    exact h1
  omega

/-- The arithmetic endgame.  If `4 c = 3 (n₂ - 1)`, `c ∣ 12 n₂` and `c` is odd with `0 < c`, then
`n₂ = 5`:  `3 ∣ 4 c` forces `c = 3 k`, whence `n₂ = 4 k + 1`; `c ∣ 12 n₂` gives `3 k ∣ 12`, so
`k ∣ 4`, while `c` odd forces `k` odd, hence `k = 1`. -/
theorem k2_order_arith (n₂ c : ℕ) (hcpos : 0 < c) (h4c : 4 * c = 3 * (n₂ - 1))
    (hdvd : c ∣ 12 * n₂) (hodd : Odd c) : n₂ = 5 := by
  have h3c : 3 ∣ c := by
    have h : 3 ∣ 4 * c := by rw [h4c]; exact dvd_mul_right 3 (n₂ - 1)
    exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 4) h
  obtain ⟨k, rfl⟩ := h3c
  rcases hodd with ⟨m, hm⟩
  have hk4 : 4 * k = n₂ - 1 := by
    have h : 3 * (4 * k) = 3 * (n₂ - 1) := by omega
    exact Nat.mul_left_cancel (by norm_num : 0 < 3) h
  have hn2 : n₂ = 4 * k + 1 := by omega
  have hkdvd : k ∣ 4 := by
    have h48 : 3 * k ∣ 48 * k := ⟨16, by ring⟩
    have hsum : 3 * k ∣ 48 * k + 12 := by
      have hh := hdvd
      rw [hn2] at hh
      convert hh using 1
      ring
    have h12 : 3 * k ∣ 12 := by
      have h := Nat.dvd_sub hsum h48
      rwa [show 48 * k + 12 - 48 * k = 12 from by omega] at h
    obtain ⟨j, hj⟩ := h12
    have hkj : 3 * (k * j) = 3 * 4 := by rw [← mul_assoc, ← hj]
    exact ⟨j, (Nat.mul_left_cancel (by norm_num : 0 < 3) hkj).symm⟩
  have hle : k ≤ 4 := Nat.le_of_dvd (by norm_num) hkdvd
  interval_cases k
  · omega
  · omega
  · omega
  · rcases hkdvd with ⟨j, hj⟩; omega
  · omega

/-- **Bender 1974, §1** (`REFS/bender1974_bsw.txt`, p. 230), the `|K| = 2` case.

With `|K| = 2`, `C_G(t) = ⟨t⟩ ⊔ ⟨s⟩ ≅ V₄` has order `4` and is a Sylow 2-subgroup
(`Work.BSW.Api.card_centralizer_of_card_K_two`, `Work.BSW.Api.sylow_card_of_card_K_two`), so all
Sylow 2-subgroups have order `4`.  Counting involutions in the cosets of `N = N_G(C_G(t))`
(every coset of `H = C_G(t)` outside `N` contains exactly one involution; `N/H` has order `3` and
`N` contains four subgroups of order `3`, each normalized by three involutions) gives
`|G : H| = 15` and hence `|G| = 60`. -/
theorem bswK2OrderProp : Work.BSW.BSWK2OrderProp := by
  intro G _ _ hsimple hnab t s K h hk
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hcardG, -, hge5⟩ := sylow_number_and_ncard hsimple hnab t s K h hk
  -- `3 ∤ n₂`
  have h3 : ¬ 3 ∣ Nat.card (Sylow 2 G) :=
    Work.BSW.Cases.K2Count.three_not_dvd_sylow_two hsimple hnab t s K h hk
  -- a subgroup of order `3` inside `N_G(C_G(t))`
  have hdvd3 : 3 ∣ Nat.card ↥(Subgroup.normalizer
      ((Subgroup.centralizer ({t} : Set G)) : Set G)) := by
    rw [normalizer_centralizer_card hsimple hnab t s K h hk]
    norm_num
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G))) 3 hdvd3
  let T : Subgroup G := Subgroup.zpowers ((g : ↥(Subgroup.normalizer
    ((Subgroup.centralizer ({t} : Set G)) : Set G))) : G)
  have hT : Nat.card T = 3 := by
    show Nat.card ↥(Subgroup.zpowers ((g : ↥(Subgroup.normalizer
      ((Subgroup.centralizer ({t} : Set G)) : Set G))) : G)) = 3
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg]
  have hTN : T ≤ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G) :=
    Subgroup.zpowers_le.mpr g.2
  -- the number of involutions outside `N = N_G(C_G(t))` is `3 n₂ - 3`
  have hm := k2_involutions_outside_card h hk hcardG
  -- Bender's double count: `m = 4 c` with `c = #{u : orderOf u = 2, u ∈ N_G(T)}`
  have hA : Nat.card {u : G // orderOf u = 2 ∧
        u ∉ Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G)) : Set G)}
      = 4 * Nat.card {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (T : Set G)} :=
    Work.BSW.Cases.k2_count_involutions_outside hsimple hnab t s K h hk T hT hTN
  -- `C_G(T)` has odd order: no involution commutes with a nonidentity element of odd order
  have hCodd : Odd (Nat.card ↥(Subgroup.centralizer (T : Set G))) := by
    by_contra hnot
    rw [Nat.not_odd_iff_even] at hnot
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(Subgroup.centralizer (T : Set G))) 2 hnot.two_dvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 3 (by simpa [hT] using dvd_refl 3)
    have hx1 : (x : G) ≠ 1 := by
      intro h1
      have h2 : orderOf (x : G) = 1 := by rw [h1, orderOf_one]
      rw [Subgroup.orderOf_coe, hx] at h2
      norm_num at h2
    have hxodd : Odd (orderOf (x : G)) := by
      rw [Subgroup.orderOf_coe, hx]
      exact ⟨1, by norm_num⟩
    have hu2 : orderOf (u : G) = 2 := (Subgroup.orderOf_coe u).trans hu
    have hcomm : (u : G) * (x : G) = (x : G) * (u : G) :=
      ((Subgroup.mem_centralizer_iff.mp u.2) (x : G) x.2).symm
    exact (no_involution_centralizes_odd h hk (x : G) hx1 hxodd
      (u : G) hu2) hcomm
  -- `N_G(T) ≠ C_G(T)`: otherwise `N_G(T)` has odd order, so `m = 4 c = 0` and `n₂ = 1`
  have hne : Subgroup.normalizer (T : Set G) ≠ Subgroup.centralizer (T : Set G) := by
    intro heq
    have hNodd : Odd (Nat.card ↥(Subgroup.normalizer (T : Set G))) := by
      rw [heq]; exact hCodd
    have hc0 : Nat.card {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (T : Set G)} = 0 := by
      haveI : IsEmpty {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (T : Set G)} :=
        ⟨fun u => by
          have h2 : 2 ∣ Nat.card ↥(Subgroup.normalizer (T : Set G)) := by
            have hd := Subgroup.orderOf_dvd_natCard (Subgroup.normalizer (T : Set G)) u.2.2
            rwa [u.2.1] at hd
          obtain ⟨k, hk⟩ := h2
          rcases hNodd with ⟨j, hj⟩
          omega⟩
      simp
    rw [hA, hc0] at hm
    omega
  -- the involution of `N_G(T)` inverts `C_G(T)`: `c = |C_G(T)|`
  have hB : Nat.card {u : G // orderOf u = 2 ∧ u ∈ Subgroup.normalizer (T : Set G)} =
      Nat.card ↥(Subgroup.centralizer (T : Set G)) :=
    Work.BSW.Cases.K2Count.k2_inv_count_of_ne h hk T hT hne
  -- `4 |C_G(T)| = 3 (n₂ - 1)`
  have h4c : 4 * Nat.card ↥(Subgroup.centralizer (T : Set G))
      = 3 * (Nat.card (Sylow 2 G) - 1) := by
    rw [hA, hB] at hm
    omega
  -- `c | 12 n₂`
  have hcdvd : Nat.card ↥(Subgroup.centralizer (T : Set G)) ∣ 12 * Nat.card (Sylow 2 G) := by
    have hh := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (T : Set G))
    rwa [← hcardG] at hh
  have hcpos : 0 < Nat.card ↥(Subgroup.centralizer (T : Set G)) := Nat.card_pos
  rw [k2_order_arith (Nat.card (Sylow 2 G)) (Nat.card ↥(Subgroup.centralizer (T : Set G)))
    hcpos h4c hcdvd hCodd] at hcardG
  omega

end Work.BSW.Cases
