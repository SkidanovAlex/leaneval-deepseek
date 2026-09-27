import Mathlib
import Submission.Work.EKLC6Route.L7Aux
import Submission.Work.EKLC6Route.gridIdx_mem_Icc

/-!
# `Work.EKLC6Route.exists_cellFinset`

Counting the level-`L` grid cells that meet `VtSet t ∩ V ρ`.

By `Work.EKLC6Route.gridIdx_mem_Icc`, for `k ∈ V ρ` every entry of the grid index
`gridIdx ρ L k` lies in `[-2^L, 2^L]`, because
`gridIdx ρ L k i j = ⌊(kᵢⱼ - 1ᵢⱼ)·2^L/ρ⌋` and `|kᵢⱼ - 1ᵢⱼ| < ρ` force
`|(kᵢⱼ - 1ᵢⱼ)·2^L/ρ| < 2^L`.

Hence the whole image of `VtSet t ∩ V ρ` under `gridIdx ρ L` is contained in the finite set of
`3 × 3` integer tuples with entries in `[-2^L, 2^L]`; that set has
`(2^L + 2^L + 1)^9 = (2^(L+1)+1)^9 ≤ (2^(L+1)+3)^9` elements.  This is the `cellCount`-style
counting step of `C6GEOM_ROUTE_LEAD.md` (`L7`).
-/

namespace Work.EKLC6Route

/-- **Counting the grid cells meeting `V ρ`.**  There is a finite set `C` of grid indices which
contains `gridIdx ρ L k` for every `k ∈ VtSet t ∩ V ρ`, with
`C.card ≤ (2^(L+1)+3)^9`. -/
theorem exists_cellFinset (ρ : ℝ) (hρ : 0 < ρ) (L : ℕ) (t : Fin 3 → ℝ) :
    ∃ C : Finset (Fin 3 → Fin 3 → ℤ),
      (∀ k ∈ Work.EKLC6Route.VtSet t ∩ Work.EKLContract.V ρ,
        Work.EKLC6Route.gridIdx ρ L k ∈ C) ∧
      C.Nonempty ∧ C.card ≤ (2 ^ (L + 1) + 3) ^ 9 := by
  classical
  -- the one-dimensional index box `[-2^L, 2^L]`
  set T : Finset ℤ := Finset.Icc (-(2 ^ L : ℤ)) (2 ^ L : ℤ) with hT
  have hTcard : T.card = 2 * 2 ^ L + 1 := by
    rw [hT, Int.card_Icc]
    have hcast : (2 ^ L : ℤ) + 1 - (-(2 ^ L : ℤ)) = ((2 * 2 ^ L + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [hcast, Int.toNat_natCast]
  have hTne : T.Nonempty := by
    rw [hT]
    refine ⟨0, ?_⟩
    rw [Finset.mem_Icc]
    exact ⟨neg_nonpos.mpr (by positivity), by positivity⟩
  have hinner : (Fintype.piFinset (fun _ : Fin 3 => T)).card = T.card ^ 3 := by
    rw [Fintype.card_piFinset]
    simp
  have hcard : (Fintype.piFinset (fun _ : Fin 3 => Fintype.piFinset (fun _ : Fin 3 => T))).card
      = (T.card ^ 3) ^ 3 := by
    rw [Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hinner]
  refine ⟨Fintype.piFinset (fun _ : Fin 3 => Fintype.piFinset (fun _ : Fin 3 => T)), ?_, ?_, ?_⟩
  · -- every `gridIdx ρ L k`, `k ∈ VtSet t ∩ V ρ`, lands in the box
    intro k hk
    rw [Fintype.mem_piFinset]
    intro i
    rw [Fintype.mem_piFinset]
    intro j
    exact gridIdx_mem_Icc ρ hρ L hk.2 i j
  · -- the box is nonempty
    rw [Fintype.piFinset_nonempty]
    intro i
    rw [Fintype.piFinset_nonempty]
    intro j
    exact hTne
  · -- the count
    rw [hcard]
    calc (T.card ^ 3) ^ 3 = T.card ^ 9 := by rw [← pow_mul]
      _ = (2 * 2 ^ L + 1) ^ 9 := by rw [hTcard]
      _ ≤ (2 ^ (L + 1) + 3) ^ 9 := Nat.pow_le_pow_left (by rw [pow_succ]; omega) 9

end Work.EKLC6Route
