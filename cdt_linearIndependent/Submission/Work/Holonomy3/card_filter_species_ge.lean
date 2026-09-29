import Mathlib
import Submission.Work.Holonomy3.defs

/-!
# Counting the positions with high species

For a balanced species vector `i : Fin d → Fin m` (each of the `m` species occurring exactly
`d/m` times) and a threshold `u ≤ m`, exactly `(m - u) · (d/m)` of the positions `s : Fin d` carry
a species `i s ≥ u`: there are `m - u` species in `{u, u+1, …, m-1} ⊆ Fin m`, and each of them
occurs `d/m` times.
-/

namespace Work.Holonomy3

open scoped BigOperators

/-- The number of `a : Fin m` with `u ≤ a` is `m - u`. -/
lemma card_fin_filter_le {m u : ℕ} :
    (Finset.univ.filter (fun a : Fin m => u ≤ (a : ℕ))).card = m - u := by
  rw [Finset.card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun i => if u ≤ i then (1 : ℕ) else 0) m]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  have hIco : (Finset.range m).filter (fun i => u ≤ i) = Finset.Ico u m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hIco, Nat.card_Ico]

lemma card_filter_species_ge {m d : ℕ} (hm : 0 < m) (hmd : m ∣ d) (i : Fin d → Fin m)
    (hi : Work.Holonomy3.Balanced i) {u : ℕ} (hu : u ≤ m) :
    (Finset.univ.filter (fun s : Fin d => u ≤ (i s : ℕ))).card = (m - u) * (d / m) := by
  classical
  -- each species `a` occurs exactly `d/m` times, in either orientation of the equality
  have hi' : ∀ a : Fin m, (Finset.univ.filter (fun s : Fin d => a = i s)).card = d / m := by
    intro a
    rw [Finset.filter_congr (fun s (_ : s ∈ Finset.univ) => eq_comm)]
    exact hi a
  -- distribute the indicator of the fibre of `i s` over the species
  have key : ∀ s : Fin d, (if u ≤ (i s : ℕ) then (1 : ℕ) else 0)
      = ∑ a : Fin m, (if a = i s then (if u ≤ (a : ℕ) then (1 : ℕ) else 0) else 0) := by
    intro s
    rw [Finset.sum_ite_eq']
    simp
  calc (Finset.univ.filter (fun s : Fin d => u ≤ (i s : ℕ))).card
      = ∑ s : Fin d, (if u ≤ (i s : ℕ) then (1 : ℕ) else 0) := Finset.card_filter _ _
    _ = ∑ s : Fin d, ∑ a : Fin m,
          (if a = i s then (if u ≤ (a : ℕ) then (1 : ℕ) else 0) else 0) :=
          Finset.sum_congr rfl (fun s _ => key s)
    _ = ∑ a : Fin m, ∑ s : Fin d,
          (if a = i s then (if u ≤ (a : ℕ) then (1 : ℕ) else 0) else 0) := Finset.sum_comm
    _ = ∑ a : Fin m, (d / m) * (if u ≤ (a : ℕ) then (1 : ℕ) else 0) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, hi' a]
    _ = (d / m) * (∑ a : Fin m, (if u ≤ (a : ℕ) then (1 : ℕ) else 0)) := by
          rw [Finset.mul_sum]
    _ = (m - u) * (d / m) := by
          rw [← Finset.card_filter, card_fin_filter_le, Nat.mul_comm]

end Work.Holonomy3
