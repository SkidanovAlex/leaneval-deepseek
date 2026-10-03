import Mathlib

namespace Work.FIArea7.TwoCharPV

/-- Reindexing an interval sum over `ℤ` as a sum over `ℕ`: for `X ≤ Y` the map `t ↦ X + t`
identifies `Finset.Icc 0 (Y - X).toNat ⊆ ℕ` with `Finset.Icc X Y ⊆ ℤ`.

Suggested proof: `Finset.sum_bij` with the map `t ↦ X + (t : ℤ)`; the membership conditions use
`Int.toNat_of_nonneg` (as `X ≤ Y` gives `0 ≤ Y - X`), `Int.toNat_le_toNat`, and injectivity of
`t ↦ X + t`. -/
theorem sum_Icc_int_reindex (X Y : ℤ) (hXY : X ≤ Y) (g : ℤ → ℝ) :
    ∑ n ∈ Finset.Icc X Y, g n = ∑ t ∈ Finset.Icc 0 (Y - X).toNat, g (X + (t : ℤ)) := by
  rw [eq_comm]
  refine Finset.sum_bij (fun t (_ : t ∈ Finset.Icc 0 (Y - X).toNat) => X + (t : ℤ)) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Icc] at ha ⊢
    obtain ⟨h0, hN⟩ := ha
    refine ⟨by linarith, ?_⟩
    have hcast : ((Y - X).toNat : ℤ) = Y - X := Int.toNat_of_nonneg (by linarith)
    have : (a : ℤ) ≤ ((Y - X).toNat : ℤ) := by exact_mod_cast hN
    linarith
  · intro a1 _ a2 _ h
    have h' : (a1 : ℤ) = (a2 : ℤ) := by linarith
    exact_mod_cast h'
  · intro b hb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hbX, hbY⟩ := hb
    refine ⟨(b - X).toNat, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      refine ⟨Nat.zero_le _, ?_⟩
      apply Int.toNat_le_toNat
      linarith
    · have hcast : (((b - X).toNat : ℤ)) = b - X := Int.toNat_of_nonneg (by linarith)
      linarith
  · intro a ha
    rfl

end Work.FIArea7.TwoCharPV
