import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.FiniteField

/-- In a finite cyclic commutative group `G` of order divisible by `n`, an element is an
`n`-th power if and only if its `(card G / n)`-th power is `1`. -/
private theorem pow_card_div_eq_one_iff {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (n : ℕ) (hn : n ∣ Nat.card G) (x : G) :
    x ^ (Nat.card G / n) = 1 ↔ x ∈ (powMonoidHom n).range := by
  set m := Nat.card G with hm
  have hle : (powMonoidHom n : G →* G).range ≤ (powMonoidHom (m / n) : G →* G).ker := by
    intro y hy
    rw [MonoidHom.mem_range] at hy
    obtain ⟨z, rfl⟩ := hy
    rw [MonoidHom.mem_ker, powMonoidHom_apply, powMonoidHom_apply, ← pow_mul,
      Nat.mul_div_cancel' hn]
    exact pow_card_eq_one'
  have hR : Nat.card ↥(powMonoidHom n : G →* G).range = m / n := by
    rw [IsCyclic.card_powMonoidHom_range, ← hm, Nat.gcd_eq_right_iff_dvd.mpr hn]
  have hK : Nat.card ↥(powMonoidHom (m / n) : G →* G).ker = m / n := by
    rw [IsCyclic.card_powMonoidHom_ker, ← hm,
      Nat.gcd_eq_right_iff_dvd.mpr (Nat.div_dvd_of_dvd hn)]
  have hEq : (powMonoidHom n : G →* G).range = (powMonoidHom (m / n) : G →* G).ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hR, hK])
  rw [hEq, MonoidHom.mem_ker, powMonoidHom_apply]

theorem pow_card_sub_one_div_eq_one_iff {K : Type*} [Field K] [Fintype K] (n : ℕ)
    (hn : n ∣ Fintype.card K - 1) (x : Kˣ) :
    x ^ ((Fintype.card K - 1) / n) = 1 ↔ x ∈ (powMonoidHom n).range := by
  have hcard : Nat.card Kˣ = Fintype.card K - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
  rw [← hcard] at hn ⊢
  exact pow_card_div_eq_one_iff n hn x

end Commons.FieldTheory.FiniteField