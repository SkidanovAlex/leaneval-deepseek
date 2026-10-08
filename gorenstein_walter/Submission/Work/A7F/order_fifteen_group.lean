import Mathlib
import Submission.Work.A7F.Defs

set_option linter.style.haveILetI false

namespace Work.A7F

/-- A group of order `15` is cyclic: it has an element of order `15`.

Both Sylow subgroups are normal (Sylow's third theorem: the number of Sylow `5`-subgroups
divides `3` and is `≡ 1 (mod 5)`, hence `1`; likewise for `5 = [G : P₃]` and `p = 3`).
The two normal Sylow subgroups have coprime orders, so they commute elementwise; the product
of an element of order `5` and one of order `3` therefore has order `5 · 3 = 15`. -/
theorem order_fifteen_group (G : Type) [Group G] [Finite G] (h : Nat.card G = 15) :
    ∃ g : G, orderOf g = 15 := by
  haveI hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI hp3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow 3 G) := inferInstance
  -- The Sylow subgroups have the expected orders.
  have hPcard : Nat.card (P : Subgroup G) = 5 := by
    rw [Sylow.card_eq_multiplicity, h, Nat.factorization_def 15 (by norm_num : Nat.Prime 5)]
    have h1 : padicValNat 5 15 = 1 := by
      have h2 : padicValNat 5 (5 * 3) = padicValNat 5 5 + padicValNat 5 3 :=
        padicValNat.mul (p := 5) (a := 5) (b := 3) (by norm_num) (by norm_num)
      rw [show (5 : ℕ) * 3 = 15 from rfl, padicValNat_base (by norm_num : 1 < (5 : ℕ)),
          padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (5 : ℕ) ∣ 3)] at h2
      norm_num at h2 ⊢
      exact h2
    rw [h1, pow_one]
  have hQcard : Nat.card (Q : Subgroup G) = 3 := by
    rw [Sylow.card_eq_multiplicity, h, Nat.factorization_def 15 (by norm_num : Nat.Prime 3)]
    have h1 : padicValNat 3 15 = 1 := by
      have h2 : padicValNat 3 (3 * 5) = padicValNat 3 3 + padicValNat 3 5 :=
        padicValNat.mul (p := 3) (a := 3) (b := 5) (by norm_num) (by norm_num)
      rw [show (3 : ℕ) * 5 = 15 from rfl, padicValNat_base (by norm_num : 1 < (3 : ℕ)),
          padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 5)] at h2
      norm_num at h2 ⊢
      exact h2
    rw [h1, pow_one]
  haveI hfin5 : Finite (Sylow 5 G) := P.finite_of_finiteIndex
  haveI hfin3 : Finite (Sylow 3 G) := Q.finite_of_finiteIndex
  -- Sylow's third theorem: the number of Sylow `p`-subgroups divides the index and is `≡ 1`.
  have hidx5 : (P : Subgroup G).index = 3 := by
    rw [Subgroup.index_eq_card_div, h, hPcard]
  have hidx3 : (Q : Subgroup G).index = 5 := by
    rw [Subgroup.index_eq_card_div, h, hQcard]
  have hdvd5 : Nat.card (Sylow 5 G) ∣ 3 := by
    have hd := P.card_dvd_index; rwa [hidx5] at hd
  have hdvd3 : Nat.card (Sylow 3 G) ∣ 5 := by
    have hd := Q.card_dvd_index; rwa [hidx3] at hd
  have hmod5 : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 G
  have hmod3 : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hcard5 : Nat.card (Sylow 5 G) = 1 := by
    have hle : Nat.card (Sylow 5 G) ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd5
    have hge : 1 ≤ Nat.card (Sylow 5 G) := Nat.card_pos
    have hm : Nat.card (Sylow 5 G) % 5 = 1 := by
      have hh := hmod5; rw [Nat.ModEq] at hh; simpa using hh
    interval_cases Nat.card (Sylow 5 G) <;> simp_all
  have hcard3 : Nat.card (Sylow 3 G) = 1 := by
    have hle : Nat.card (Sylow 3 G) ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd3
    have hge : 1 ≤ Nat.card (Sylow 3 G) := Nat.card_pos
    have hm : Nat.card (Sylow 3 G) % 3 = 1 := by
      have hh := hmod3; rw [Nat.ModEq] at hh; simpa using hh
    interval_cases Nat.card (Sylow 3 G) <;> simp_all
  haveI hsub5 : Subsingleton (Sylow 5 G) := Finite.card_le_one_iff_subsingleton.mp hcard5.le
  haveI hsub3 : Subsingleton (Sylow 3 G) := Finite.card_le_one_iff_subsingleton.mp hcard3.le
  -- A unique Sylow subgroup is normal.
  have hPn : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  have hQn : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
  -- The two normal Sylow subgroups have coprime orders, hence are disjoint.
  have hdisj : Disjoint (P : Subgroup G) Q :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hPcard, hQcard]; norm_num)
  -- Elements of the two Sylow subgroups.
  obtain ⟨x, hxmem, hxord⟩ : ∃ x : G, x ∈ (P : Subgroup G) ∧ orderOf x = 5 := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup G)) 5 (by rw [hPcard])
    exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  obtain ⟨y, hymem, hyord⟩ : ∃ y : G, y ∈ (Q : Subgroup G) ∧ orderOf y = 3 := by
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (Q : Subgroup G)) 3 (by rw [hQcard])
    exact ⟨(y : G), y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  -- Elements of disjoint normal subgroups commute.
  have hcomm : Commute x y :=
    Subgroup.commute_of_normal_of_disjoint _ _ hPn hQn hdisj x y hxmem hymem
  refine ⟨x * y, ?_⟩
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hxord, hyord]; norm_num), hxord, hyord]

end Work.A7F
