import Mathlib
import Submission.Work.Params.qall
import Submission.Work.Params.basic
import Submission.Work.Params.defs

set_option autoImplicit false

namespace Work.Params

/-- `Q = ∏_{k<d} (2Fk+1)(2Fk-1)` is positive: it is a product of positive factors. -/
theorem Qall_pos : 0 < Qall := by
  unfold Qall
  apply List.prod_pos
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  have hja : 1 ≤ j + 1 := Nat.le_add_left 1 j
  have hmul : 1 ≤ Ffac * (j + 1) := by
    have := Nat.mul_le_mul Ffac_one_le hja
    simpa using this
  have h2 : 2 ≤ 2 * Ffac * (j + 1) := by
    calc 2 = 2 * 1 := by ring
      _ ≤ 2 * (Ffac * (j + 1)) := Nat.mul_le_mul_left 2 hmul
      _ = 2 * Ffac * (j + 1) := by ring
  have ha : 0 < 2 * Ffac * (j + 1) + 1 := by omega
  have hb : 0 < 2 * Ffac * (j + 1) - 1 := by omega
  exact mul_pos ha hb

/-- Pure arithmetic core of the construction of `u₀`: for `F ≥ 2`, `Q ≥ 1` the number
`Q + m·(F·Q)` with `m = (L + F·Q - 1 - Q)/(F·Q)` is the least number `≥ L` of the form
`Q·(1 + mF)`, hence lies in `[L, L + F·Q)` and equals `Q·(1 + mF)`. -/
theorem upar_core (L F Q : ℕ) (hF : 2 ≤ F) (hQ : 1 ≤ Q) :
    L ≤ Q + ((L + F * Q - 1 - Q) / (F * Q)) * (F * Q) ∧
    Q + ((L + F * Q - 1 - Q) / (F * Q)) * (F * Q) < L + F * Q ∧
    Q + ((L + F * Q - 1 - Q) / (F * Q)) * (F * Q)
      = Q * (1 + ((L + F * Q - 1 - Q) / (F * Q)) * F) := by
  set k := F * Q with hk
  set m := (L + k - 1 - Q) / k with hm
  have hk1 : 1 ≤ k := by rw [hk]; nlinarith [hF, hQ]
  have hkpos : 0 < k := by omega
  have hQk : Q ≤ k - 1 := by
    rw [hk]
    have : Q + 1 ≤ F * Q := by nlinarith [hF, hQ]
    omega
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : L ≤ Q
    · omega
    · have h' : Q < L := Nat.lt_of_not_le h
      have hNd : L + k - 1 - Q = (L - Q) + (k - 1) := by omega
      have hm' : m = ((L - Q) + (k - 1)) / k := by rw [hm, hNd]
      rw [hm', mul_comm]
      have hdec := Nat.div_add_mod ((L - Q) + (k - 1)) k
      have hmodlt := Nat.mod_lt ((L - Q) + (k - 1)) hkpos
      have : L - Q ≤ k * (((L - Q) + (k - 1)) / k) := by omega
      omega
  · have hmlt : m * k ≤ L + k - 1 - Q := by rw [hm]; exact Nat.div_mul_le_self _ _
    have hNQ : Q + (L + k - 1 - Q) = L + k - 1 := Nat.add_sub_of_le (by omega)
    omega
  · rw [hm, hk]; ring

theorem uparfacts (n : ℕ) :
    Lpar n ≤ upar n ∧ upar n < Lpar n + Ffac * Qall ∧
    Qall ∣ upar n ∧ upar n ≡ 1 [MOD Ffac] ∧
    upar n = Qall * (1 + ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * Ffac) := by
  have hQ1 : 1 ≤ Qall := by have := Qall_pos; omega
  have hcore := upar_core (Lpar n) Ffac Qall Ffac_two_le hQ1
  unfold upar
  refine ⟨hcore.1, hcore.2.1, ?_, ?_, hcore.2.2⟩
  · exact ⟨1 + ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * Ffac, hcore.2.2⟩
  · have hmF : ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * Ffac ≡ 0 [MOD Ffac] :=
      Nat.modEq_zero_iff_dvd.mpr
        ⟨(Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall), by ring⟩
    have h1 : 1 + ((Lpar n + Ffac * Qall - 1 - Qall) / (Ffac * Qall)) * Ffac ≡ 1 [MOD Ffac] := by
      have hh := Nat.ModEq.add (Nat.ModEq.refl 1) hmF
      simpa using hh
    have h2 := Nat.ModEq.mul Qall_modEq_one h1
    rw [hcore.2.2]
    simpa using h2

end Work.Params
