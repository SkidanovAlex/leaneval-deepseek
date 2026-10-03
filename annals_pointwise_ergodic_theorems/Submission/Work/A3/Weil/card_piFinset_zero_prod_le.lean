import Mathlib

/-!
# Counting tuples with zero product over a finite set of integers

For a finite set `T : Finset ℤ` and `1 ≤ k`, the number of `k`-tuples drawn from `T` whose
product vanishes is at most `k * T.card ^ (k - 1)`.

The point is that `T` is a `Finset`, so it contains at most one zero.  A tuple has zero product
iff some coordinate is zero (integrality of `ℤ`), hence the set of such tuples is contained in
the union over the `k` coordinates of the tuples with that coordinate equal to zero; each of
those `k` sets has at most `T.card ^ (k - 1)` elements.  The union bound gives the claim.
-/

namespace Work.A3.Weil

theorem card_piFinset_zero_prod_le (T : Finset ℤ) (k : ℕ) (hk : 1 ≤ k) :
    ((Fintype.piFinset (fun _ : Fin k => T)).filter (fun l => ∏ i, l i = 0)).card ≤
      k * T.card ^ (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  -- Each coordinate hyperplane `l i = 0` meets the box in at most `T.card ^ m` tuples: deleting
  -- the coordinate `i` is injective on it.
  have hfiber : ∀ i : Fin (m + 1),
      ((Fintype.piFinset (fun _ : Fin (m + 1) => T)).filter (fun l => l i = 0)).card ≤
        T.card ^ m := by
    intro i
    have hmap : Set.MapsTo (fun l : Fin (m + 1) → ℤ => fun j : Fin m => l (i.succAbove j))
        ↑((Fintype.piFinset (fun _ : Fin (m + 1) => T)).filter (fun l => l i = 0))
        ↑(Fintype.piFinset (fun _ : Fin m => T)) := by
      intro l hl
      simp only [Finset.mem_coe, Finset.mem_filter] at hl
      exact Fintype.mem_piFinset.mpr (fun j => (Fintype.mem_piFinset.mp hl.1) (i.succAbove j))
    have hinj : Set.InjOn (fun l : Fin (m + 1) → ℤ => fun j : Fin m => l (i.succAbove j))
        ↑((Fintype.piFinset (fun _ : Fin (m + 1) => T)).filter (fun l => l i = 0)) := by
      intro l₁ hl₁ l₂ hl₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hl₁ hl₂
      funext j
      by_cases hj : j = i
      · rw [hj, hl₁.2, hl₂.2]
      · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hj
        rw [← hz]
        exact congr_fun heq z
    have hmain := Finset.card_le_card_of_injOn
      (s := (Fintype.piFinset (fun _ : Fin (m + 1) => T)).filter (fun l => l i = 0))
      (t := Fintype.piFinset (fun _ : Fin m => T))
      (fun l : Fin (m + 1) → ℤ => fun j : Fin m => l (i.succAbove j)) hmap hinj
    simpa [Fintype.card_piFinset] using hmain
  -- A tuple with zero product has a zero coordinate.
  have hsub : (Fintype.piFinset (fun _ : Fin (m + 1) => T)).filter (fun l => ∏ i, l i = 0) ⊆
      Finset.univ.biUnion (fun i : Fin (m + 1) =>
        (Fintype.piFinset (fun _ : Fin (m + 1) => T)).filter (fun l => l i = 0)) := by
    intro l hl
    simp only [Finset.mem_filter] at hl
    obtain ⟨hlS, hprod⟩ := hl
    obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.mp
      (by simpa using hprod : ∏ i ∈ (Finset.univ : Finset (Fin (m + 1))), l i = 0)
    exact Finset.mem_biUnion.mpr
      ⟨a, Finset.mem_univ a, by simp only [Finset.mem_filter]; exact ⟨hlS, ha⟩⟩
  have hfin : ((Fintype.piFinset (fun _ : Fin (m + 1) => T)).filter
      (fun l => ∏ i, l i = 0)).card ≤ (m + 1) * T.card ^ m := by
    calc ((Fintype.piFinset (fun _ : Fin (m + 1) => T)).filter (fun l => ∏ i, l i = 0)).card
        ≤ (Finset.univ.biUnion (fun i : Fin (m + 1) =>
            (Fintype.piFinset (fun _ : Fin (m + 1) => T)).filter (fun l => l i = 0))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ i : Fin (m + 1),
            ((Fintype.piFinset (fun _ : Fin (m + 1) => T)).filter (fun l => l i = 0)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin (m + 1), T.card ^ m := Finset.sum_le_sum (fun i _ => hfiber i)
      _ = (m + 1) * T.card ^ m := by simp
  simpa using hfin

end Work.A3.Weil
