import Mathlib
import Submission.Work.A7REC.Char.a7Excl120Common

set_option linter.style.haveILetI false

namespace Work.A7REC.Char

open Subgroup

theorem a7Excl120IdxForty {C : Type*} [Group C] [Finite C] {U S : Subgroup C} {τ : C}
    (h : Excl120Setup U S τ)
    (hi : (Subgroup.normalizer (U : Set C)).index = 40) : False := by
  have hN3 : Nat.card ↥(Subgroup.normalizer (U : Set C)) = 3 := by
    have hmul := Subgroup.card_mul_index (Subgroup.normalizer (U : Set C))
    rw [hi, h.card_eq] at hmul
    omega
  have hle : U ≤ Subgroup.normalizer (U : Set C) := Subgroup.le_normalizer
  have hUeqN : U = Subgroup.normalizer (U : Set C) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hN3, h.card_U])
  have hτN : τ ∈ Subgroup.normalizer (U : Set C) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.tau_normalizes
  have hτU : τ ∈ U := by rw [hUeqN]; exact hτN
  have hdvd : orderOf τ ∣ Nat.card U := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hτU)
  rw [h.card_U, h.tau_order] at hdvd
  omega


end Work.A7REC.Char
