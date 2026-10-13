import Mathlib

namespace Work.WilG4c

open Finset

/-- The cardinality of the initial segment `{a : Fin N // a ≤ i}`. -/
lemma card_filter_le_fin {N : ℕ} (i : Fin N) :
    (Finset.univ.filter (fun a : Fin N => a ≤ i)).card = (i : ℕ) + 1 := by
  rw [show Finset.univ.filter (fun a : Fin N => a ≤ i) = Finset.Iic i by
    ext a; simp]
  exact Fin.card_Iic i

/-- The cardinality of the strict initial segment `{a : Fin N // a < i}`. -/
lemma card_filter_lt_fin {N : ℕ} (i : Fin N) :
    (Finset.univ.filter (fun a : Fin N => a < i)).card = (i : ℕ) := by
  rw [show Finset.univ.filter (fun a : Fin N => a < i) = Finset.Iio i by
    ext a; simp]
  exact Fin.card_Iio i

theorem FilterCardInitialSegment {N : ℕ} (p : Fin N → ℕ) (hp : ∀ a b : Fin N, a ≤ b → p a ≤ p b)
    (j : ℕ) (i : Fin N) :
    (p i ≤ j ↔ (i : ℕ) < (Finset.univ.filter (fun i : Fin N => p i ≤ j)).card) := by
  classical
  set S := Finset.univ.filter (fun i : Fin N => p i ≤ j) with hS
  have hmem : ∀ a : Fin N, a ∈ S ↔ p a ≤ j := by
    intro a; rw [hS]; simp
  constructor
  · intro h
    -- every `a ≤ i` lies in `S`, so `i + 1 = #{a ≤ i} ≤ #S`
    have hsub : Finset.univ.filter (fun a : Fin N => a ≤ i) ⊆ S := by
      intro a ha
      rw [hmem]
      exact le_trans (hp a i (Finset.mem_filter.mp ha).2) h
    have hle := Finset.card_le_card hsub
    rw [card_filter_le_fin i] at hle
    omega
  · intro hlt
    -- if `p i > j` then every element of `S` is `< i`, so `#S ≤ i`
    by_contra hnot
    rw [not_le] at hnot
    have hsub : S ⊆ Finset.univ.filter (fun a : Fin N => a < i) := by
      intro a ha
      have hpa : p a ≤ j := (hmem a).mp ha
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ a, ?_⟩
      by_contra h
      rw [not_lt] at h
      have : p i ≤ p a := hp i a h
      omega
    have hle := Finset.card_le_card hsub
    rw [card_filter_lt_fin i] at hle
    omega

end Work.WilG4c
