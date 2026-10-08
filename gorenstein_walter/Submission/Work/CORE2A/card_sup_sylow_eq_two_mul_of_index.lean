import Mathlib
import Submission.Work.CORE2A.Defs

namespace Work.CORE2A

/-- **The index of `E` in `P ⊔ E` is `2`.**

Setting `X = [P ⊔ E : E]`:

* `E ⊔ C` is a normal subgroup (both `E` and `C` are normal) of index `2 * m` with `m` odd, so
  `E.index = [E ⊔ C : E] * (2 * m) = 2 * ([E ⊔ C : E] * m)`, and the second factor is odd because
  `[E ⊔ C : E] = [C : C ⊓ E]` (second isomorphism theorem, `E` normal) divides the odd number
  `|C|`.  Hence `4 ∤ E.index`.
* `X * (P ⊔ E).index = E.index`, so `X ∣ E.index`.
* `X ≠ 1` (otherwise `P ⊔ E ≤ E`, i.e. `P ≤ E`), and
  `X = E.relIndex (P ⊔ E) = E.relIndex P` (second isomorphism theorem again), so
  `X * |E ⊓ P| = |P|` and `X` divides the order of the `2`-group `P`: `X = 2 ^ k` with `k ≥ 1`.
* `4 ∤ E.index` then forces `k ≤ 1`, so `X = 2`.

Finally `|P ⊔ E| = X * |E| = 2 * |E|` by Lagrange (`Subgroup.relIndex_mul_card`). -/
theorem card_sup_sylow_eq_two_mul_of_index {K : Type} [Group K] [Finite K] (E C P : Subgroup K)
    (hEn : E.Normal) (hCn : C.Normal) (hCodd : Odd (Nat.card C)) (hP : IsPGroup 2 P)
    (hPi : Odd P.index) (m : ℕ) (hm : Odd m) (hidx : (E ⊔ C).index = 2 * m)
    (hSE : ¬ P ≤ E) :
    Nat.card ↥(P ⊔ E) = 2 * Nat.card ↥E := by
  haveI : E.Normal := hEn
  -- ### Step 1: `4 ∤ E.index`.
  -- `[E ⊔ C : E] = [C : C ⊓ E]` divides `|C|`, hence is odd.
  have hErelN : E.relIndex (E ⊔ C) = E.relIndex C := Subgroup.relIndex_sup_left C E
  have hErelC_dvd : E.relIndex C ∣ Nat.card ↥C :=
    ⟨Nat.card ↥(E ⊓ C), (Subgroup.relIndex_mul_card E C).symm⟩
  have hErelN_odd : Odd (E.relIndex (E ⊔ C)) := hErelN ▸ Odd.of_dvd_nat hCodd hErelC_dvd
  have hEidx : E.index = E.relIndex (E ⊔ C) * (E ⊔ C).index :=
    (Subgroup.relIndex_mul_index le_sup_left).symm
  have hnot4 : ¬ 4 ∣ E.index := by
    rw [hEidx, hidx]
    have hform : E.relIndex (E ⊔ C) * (2 * m) = 2 * (E.relIndex (E ⊔ C) * m) := by ring
    rw [hform]
    intro h4
    rw [show (4 : ℕ) = 2 * 2 from by norm_num] at h4
    have h2dvd : 2 ∣ E.relIndex (E ⊔ C) * m :=
      (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 2)).mp h4
    have hodd : Odd (E.relIndex (E ⊔ C) * m) := hErelN_odd.mul hm
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  -- ### Step 2: `X := [P ⊔ E : E]` is `2 ^ k` with `k ≥ 1`.
  have hXeq : E.relIndex (P ⊔ E) = E.relIndex P := Subgroup.relIndex_sup_right P E
  have hXmul : E.relIndex (P ⊔ E) * (P ⊔ E).index = E.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have hXne : E.relIndex (P ⊔ E) ≠ 1 := by
    intro h1
    exact hSE (le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hXdvdP : E.relIndex (P ⊔ E) ∣ Nat.card ↥P := by
    rw [hXeq]
    exact ⟨Nat.card ↥(E ⊓ P), (Subgroup.relIndex_mul_card E P).symm⟩
  have hXdvdP' : E.relIndex (P ⊔ E) ∣ 2 ^ n := by rw [← hn]; exact hXdvdP
  obtain ⟨k, _hkn, hXk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hXdvdP'
  have hk_pos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero] at hXk
      exact absurd hXk hXne
    · exact h
  have hk_le_one : k ≤ 1 := by
    by_contra hk
    rw [not_le] at hk
    have h4dvdX : 4 ∣ E.relIndex (P ⊔ E) := by
      rw [hXk]
      simpa using Nat.pow_dvd_pow 2 hk
    exact hnot4 (h4dvdX.trans ⟨(P ⊔ E).index, hXmul.symm⟩)
  have hk : k = 1 := le_antisymm hk_le_one hk_pos
  have hX2 : E.relIndex (P ⊔ E) = 2 := by rw [hXk, hk]; norm_num
  -- ### Step 3: Lagrange.
  have hcard : Nat.card ↥(P ⊔ E) = E.relIndex (P ⊔ E) * Nat.card ↥E := by
    have h := Subgroup.relIndex_mul_card E (P ⊔ E)
    rw [inf_eq_left.mpr le_sup_right] at h
    exact h.symm
  rw [hcard, hX2]

end Work.CORE2A
