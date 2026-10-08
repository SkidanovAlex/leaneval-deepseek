import Mathlib
import Submission.Work.BSW.Defs
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Cases.K4.Setup

namespace Work.BSW.Cases.K4

/-- In the `|K| = 4` case of BSW, an element of even order has order `2` or `4`.

If `m = orderOf x` is even then `y = x ^ (m / 2)` is an involution commuting with `x`, so
`Subgroup.zpowers x ≤ C_G(y)` and `m = |⟨x⟩|` divides `|C_G(y)| = 8`
(`Work.BSW.Cases.K4.card_centralizer_of_orderOf_eq_two`); hence `m ∈ {2, 4, 8}`.  If `m = 8` then
`x ∈ C_G(x⁴)` with `x⁴` an involution, but every element of an involution centralizer has order
`1`, `2` or `4` (`Work.BSW.Cases.K4.orderOf_dichotomy_of_mem_centralizer_of_orderOf_eq_two`). -/
theorem orderOf_even_eq_two_or_four {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hK4 : Nat.card ↥K = 4) (x : G)
    (hx : Even (orderOf x)) : orderOf x = 2 ∨ orderOf x = 4 := by
  -- `m = orderOf x = 2k` with `k > 0`, and `y = x ^ k` is an involution with `x ∈ C_G(y)`.
  obtain ⟨k, hk⟩ := (even_iff_two_dvd.mp hx : 2 ∣ orderOf x)
  have hkpos : 0 < k := by
    have hG : 0 < Nat.card G := Nat.card_pos
    have hd := Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard x) hG
    omega
  set y := x ^ k with hydef
  have hyy : y * y = 1 := by
    rw [hydef, ← pow_add]
    have hkk : k + k = orderOf x := by omega
    rw [hkk, pow_orderOf_eq_one]
  have hyne : y ≠ 1 := by
    intro h1
    rw [hydef] at h1
    have hdvd : orderOf x ∣ k := orderOf_dvd_iff_pow_eq_one.mpr h1
    have hle : orderOf x ≤ k := Nat.le_of_dvd hkpos hdvd
    omega
  have hy2 : orderOf y = 2 := by
    have h2 : y ^ 2 = 1 := by rw [pow_two]; exact hyy
    exact orderOf_eq_prime h2 hyne
  have hmem : x ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hydef]
    group
  -- Every element of an involution centralizer has order `1`, `2` or `4`.
  have hdich := orderOf_dichotomy_of_mem_centralizer_of_orderOf_eq_two h hK4 hy2 hmem
  have hne1 : orderOf x ≠ 1 := by
    intro h1
    rw [h1] at hx
    norm_num at hx
  rcases hdich with h1 | h1 | h1
  · exact absurd h1 hne1
  · exact Or.inl h1
  · exact Or.inr h1

end Work.BSW.Cases.K4
