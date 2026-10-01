import Mathlib

namespace Work.LinnikAreas

/-- In any interval `[0, N)` the number of integers congruent to a fixed residue
`r` modulo `q` is at most `⌈N/q⌉ = (N + q - 1) / q`. -/
theorem fiber_card_le (q N : ℕ) [NeZero q] (r : ZMod q) :
    ((Finset.range N).filter (fun n : ℕ => ((n : ℕ) : ZMod q) = r)).card ≤ (N + q - 1) / q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let S := (Finset.range N).filter (fun n : ℕ => ((n : ℕ) : ZMod q) = r)
  -- Every `n ∈ S` equals `r.val + q * (n / q)`, so `S` is contained in the image
  -- of `range ((N + q - 1) / q)` under `k ↦ r.val + q * k`.
  have hsub : S ⊆ (Finset.range ((N + q - 1) / q)).image (fun k => r.val + q * k) := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hnr⟩ := hn
    have hmod : n % q = r.val := by
      have hh := congrArg ZMod.val hnr
      rwa [ZMod.val_natCast] at hh
    have hk : n / q < (N + q - 1) / q := by
      rw [Nat.lt_div_iff_mul_lt hq]
      have h1 : n / q * q ≤ n := Nat.div_mul_le_self n q
      have hlt : n / q * q < N := lt_of_le_of_lt h1 hnN
      have h2 : (N + q - 1) - (q - 1) = N := by omega
      rwa [h2]
    refine Finset.mem_image.mpr ⟨n / q, Finset.mem_range.mpr hk, ?_⟩
    have hrec : n % q + q * (n / q) = n := by
      rw [Nat.add_comm]
      exact Nat.div_add_mod n q
    rw [hmod] at hrec
    exact hrec
  calc S.card ≤ ((Finset.range ((N + q - 1) / q)).image (fun k => r.val + q * k)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range ((N + q - 1) / q)).card := Finset.card_image_le
    _ = (N + q - 1) / q := Finset.card_range _

end Work.LinnikAreas
