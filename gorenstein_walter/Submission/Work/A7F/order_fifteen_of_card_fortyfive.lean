import Mathlib
import Submission.Work.A7F.Defs

namespace Work.A7F

/-- Every group of order `45` has an element of order divisible by `15`.

Since `45 = 3² · 5`, Sylow's third theorem shows that both the number of Sylow `5`-subgroups
(dividing `9`, `≡ 1 (mod 5)`) and the number of Sylow `3`-subgroups (dividing `5`,
`≡ 1 (mod 3)`) is `1`.  Hence the Sylow `5`-subgroup `P` (order `5`) and a Sylow `3`-subgroup `Q`
(order `9`) are both normal, and as their orders are coprime they are disjoint.  Normal disjoint
subgroups commute elementwise, so an element `x ∈ P` of order `5` and an element `y ∈ Q` of order
`3` (Cauchy) commute, whence `orderOf (x * y) = 5 · 3 = 15`, which is divisible by `15`. -/
theorem order_fifteen_of_card_fortyfive (G : Type) [Group G] [Finite G] (h : Nat.card G = 45) :
    ∃ g : G, 15 ∣ orderOf g := by
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow 3 G) := inferInstance
  -- The Sylow subgroups have the expected orders.
  have hPcard : Nat.card (P : Subgroup G) = 5 := by
    have h1 : padicValNat 5 45 = 1 := by
      have h2 : padicValNat 5 (5 * 9) = padicValNat 5 5 + padicValNat 5 9 :=
        padicValNat.mul (p := 5) (a := 5) (b := 9) (by norm_num) (by norm_num)
      rw [show (5 : ℕ) * 9 = 45 from rfl, padicValNat_base (by norm_num : 1 < (5 : ℕ)),
          padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (5 : ℕ) ∣ 9)] at h2
      norm_num at h2 ⊢
      exact h2
    rw [Sylow.card_eq_multiplicity, h, Nat.factorization_def 45 (by norm_num : Nat.Prime 5),
        h1, pow_one]
  have hQcard : Nat.card (Q : Subgroup G) = 9 := by
    have h1 : padicValNat 3 45 = 2 := by
      have h3 : padicValNat 3 15 = 1 := by
        have h2 : padicValNat 3 (3 * 5) = padicValNat 3 3 + padicValNat 3 5 :=
          padicValNat.mul (p := 3) (a := 3) (b := 5) (by norm_num) (by norm_num)
        rw [show (3 : ℕ) * 5 = 15 from rfl, padicValNat_base (by norm_num : 1 < (3 : ℕ)),
            padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (3 : ℕ) ∣ 5)] at h2
        norm_num at h2 ⊢
        exact h2
      have h2 : padicValNat 3 (3 * 15) = padicValNat 3 3 + padicValNat 3 15 :=
        padicValNat.mul (p := 3) (a := 3) (b := 15) (by norm_num) (by norm_num)
      rw [show (3 : ℕ) * 15 = 45 from rfl, padicValNat_base (by norm_num : 1 < (3 : ℕ)),
          h3] at h2
      norm_num at h2 ⊢
      exact h2
    rw [Sylow.card_eq_multiplicity, h, Nat.factorization_def 45 (by norm_num : Nat.Prime 3),
        h1]
    norm_num
  have hfin5 : Finite (Sylow 5 G) := P.finite_of_finiteIndex
  have hfin3 : Finite (Sylow 3 G) := Q.finite_of_finiteIndex
  -- Indices of the Sylow subgroups in `G`.
  have hidx5 : (P : Subgroup G).index = 9 := by
    rw [Subgroup.index_eq_card_div, h, hPcard]
  have hidx3 : (Q : Subgroup G).index = 5 := by
    rw [Subgroup.index_eq_card_div, h, hQcard]
  -- Sylow's third theorem: the number of Sylow `p`-subgroups divides the index and is `≡ 1 (mod p)`.
  have hdvd5 : Nat.card (Sylow 5 G) ∣ 9 := by
    have hd := P.card_dvd_index; rwa [hidx5] at hd
  have hdvd3 : Nat.card (Sylow 3 G) ∣ 5 := by
    have hd := Q.card_dvd_index; rwa [hidx3] at hd
  have hmod5 : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 G
  have hmod3 : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hcard5 : Nat.card (Sylow 5 G) = 1 := by
    have hle : Nat.card (Sylow 5 G) ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd5
    have hm : Nat.card (Sylow 5 G) % 5 = 1 := by
      have hh := hmod5; rw [Nat.ModEq] at hh; simpa using hh
    interval_cases Nat.card (Sylow 5 G) <;> simp_all
  have hcard3 : Nat.card (Sylow 3 G) = 1 := by
    have hle : Nat.card (Sylow 3 G) ≤ 5 := Nat.le_of_dvd (by norm_num) hdvd3
    have hm : Nat.card (Sylow 3 G) % 3 = 1 := by
      have hh := hmod3; rw [Nat.ModEq] at hh; simpa using hh
    interval_cases Nat.card (Sylow 3 G) <;> simp_all
  have hsub5 : Subsingleton (Sylow 5 G) := Finite.card_le_one_iff_subsingleton.mp hcard5.le
  have hsub3 : Subsingleton (Sylow 3 G) := Finite.card_le_one_iff_subsingleton.mp hcard3.le
  -- A unique Sylow subgroup is normal.
  have hPn : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  have hQn : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
  -- Normal subgroups of coprime order are disjoint.
  have hdisj : Disjoint (P : Subgroup G) Q :=
    Subgroup.disjoint_of_coprime_natCard (by rw [hPcard, hQcard]; norm_num)
  -- Elements of order `5` and `3` in the two Sylow subgroups (Cauchy).
  obtain ⟨x, hxmem, hxord⟩ : ∃ x : G, x ∈ (P : Subgroup G) ∧ orderOf x = 5 := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup G)) 5 (by rw [hPcard])
    exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  obtain ⟨y, hymem, hyord⟩ : ∃ y : G, y ∈ (Q : Subgroup G) ∧ orderOf y = 3 := by
    obtain ⟨y, hy⟩ :=
      exists_prime_orderOf_dvd_card' (G := (Q : Subgroup G)) 3 (by rw [hQcard]; norm_num)
    exact ⟨(y : G), y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  -- Elements of disjoint normal subgroups commute.
  have hcomm : Commute x y :=
    Subgroup.commute_of_normal_of_disjoint _ _ hPn hQn hdisj x y hxmem hymem
  refine ⟨x * y, ?_⟩
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hxord, hyord]; norm_num), hxord, hyord]

end Work.A7F
