import Mathlib

namespace Work.FIArea7

/-- Two-to-one counting bound: the odd integers `r ∈ [-Rz, Rz]` with `F r.natAbs` are at most
twice the number of naturals `n ∈ [1, max Rz 0]` with `Odd n ∧ F n`.

Proof: split the left-hand filter by the sign of `r` (e.g. `Finset.card_filter_add_card_filter_not`
or `Finset.card_eq_sum_card_fiberwise`), and in each part use
`Finset.card_le_card_of_injOn` with the maps `r ↦ r.toNat` (on `0 ≤ r`) and `r ↦ (-r).toNat`
(on `r < 0`).  For `r ≥ 0`, `r.toNat = r.natAbs`, `Odd r → Odd r.natAbs` (`Int.natAbs_odd`), and
`r ≠ 0` because `Odd 0` is false, so `1 ≤ r.natAbs`; the interval `-Rz ≤ r ≤ Rz` gives
`r.natAbs ≤ max Rz 0` (if `Rz < 0` the interval is empty).  Then combine the two parts with
`Finset.card_filter_add_card_filter_not`. -/
theorem card_Icc_neg_filter_le_two_mul (Rz : ℤ) (F : ℕ → Prop) [DecidablePred F] :
    ((Finset.Icc (-Rz) Rz).filter (fun r : ℤ => Odd r ∧ F r.natAbs)).card
      ≤ 2 * ((Finset.Icc 1 (max Rz 0).toNat).filter (fun n : ℕ => Odd n ∧ F n)).card := by
  -- Write `A` for the set of odd integers in `[-Rz, Rz]` and `B` for the candidate target set.
  set A := (Finset.Icc (-Rz) Rz).filter (fun r : ℤ => Odd r ∧ F r.natAbs) with hA
  set B := (Finset.Icc 1 (max Rz 0).toNat).filter (fun n : ℕ => Odd n ∧ F n) with hB
  -- The map `r ↦ r.natAbs` has fibres of size at most two on `A`, since `a.natAbs = b` forces
  -- `a = b` or `a = -b`.
  have hfiber : ∀ b ∈ Finset.image (fun r : ℤ => r.natAbs) A,
      (A.filter (fun a : ℤ => a.natAbs = b)).card ≤ 2 := by
    intro b _
    have hsub : A.filter (fun a : ℤ => a.natAbs = b) ⊆ ({(b : ℤ), -(b : ℤ)} : Finset ℤ) := by
      intro a ha
      simp only [Finset.mem_filter] at ha
      rcases Int.natAbs_eq_iff.mp ha.2 with h | h <;> simp [h]
    calc (A.filter (fun a : ℤ => a.natAbs = b)).card
        ≤ ({(b : ℤ), -(b : ℤ)} : Finset ℤ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  have hmain : A.card ≤ 2 * (Finset.image (fun r : ℤ => r.natAbs) A).card :=
    Finset.card_le_mul_card_image (f := fun r : ℤ => r.natAbs) A 2 hfiber
  -- Every `r ∈ A` has `r.natAbs ∈ B`.
  have himage : Finset.image (fun r : ℤ => r.natAbs) A ⊆ B := by
    rw [Finset.image_subset_iff]
    intro x hx
    simp only [hA, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hlow, hhigh⟩, hodd, hF⟩ := hx
    have hodd' : Odd x.natAbs := Int.natAbs_odd.mpr hodd
    simp only [hB, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hodd', hF⟩
    · rcases hodd' with ⟨k, hk⟩; omega
    · have hb : (↑x.natAbs : ℤ) ≤ max Rz 0 := by
        rw [← Int.abs_eq_natAbs]
        exact abs_le.mpr
          ⟨by linarith [hlow, le_max_left Rz 0], by linarith [hhigh, le_max_left Rz 0]⟩
      have := Int.toNat_le_toNat hb
      simpa using this
  calc A.card ≤ 2 * (Finset.image (fun r : ℤ => r.natAbs) A).card := hmain
    _ ≤ 2 * B.card := Nat.mul_le_mul_left 2 (Finset.card_le_card himage)

end Work.FIArea7
