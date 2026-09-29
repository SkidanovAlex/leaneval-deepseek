import Mathlib
import Submission.Work.Holonomy3.count_le_of_disc

/-!
# The discrepancy statistics of the exponent vectors (`F stats`)

This module records the consequences of a small box discrepancy `disc t ≤ ε` for a configuration
`t : Fin d → ℝ` of `d` numbers, in the two forms used by the paper's Corollary `F stats`:

* `sorted_bounds` : the **sorted** configuration is within `ε` of the uniform grid `i/d`;
* `sum_bounds`    : the total sum is within `d ε` of `(d-1)/2` (paper's display
  `(discrepancy t)`, used to pin down the vanishing order `α = mdD/2`).

Everything is stated for a nondecreasing configuration; `disc` and the total sum are invariant under
relabelling (`disc_comp_perm`, `sum_bounds_of_perm`), so this covers an arbitrary configuration after
sorting the variables (the "relabelling" step of the paper's §"Seeding").
-/

namespace Work.Holonomy3

open Submission.CDT.Discrepancy
open scoped BigOperators

/-- For a monotone configuration, at least `i+1` points are `≤ t i`. -/
lemma card_le_count_mono {d : ℕ} (t : Fin d → ℝ) (hmono : Monotone t) (i : Fin d) :
    i.1 + 1 ≤ (Finset.univ.filter (fun j : Fin d => t j ≤ t i)).card := by
  have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j : Fin d => t j ≤ t i) := by
    intro j hj
    simp only [Finset.mem_Iic] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmono hj
  have h := Finset.card_le_card hsub
  simpa [Fin.card_Iic] using h

/-- For a monotone configuration, the points `≥ t i` are at least `d - i` in number. -/
lemma card_ge_count_mono {d : ℕ} (t : Fin d → ℝ) (hmono : Monotone t) (i : Fin d) :
    d - i.1 ≤ (Finset.univ.filter (fun j : Fin d => t i ≤ t j)).card := by
  have hsub : Finset.Ici i ⊆ Finset.univ.filter (fun j : Fin d => t i ≤ t j) := by
    intro j hj
    simp only [Finset.mem_Ici] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmono hj
  have h := Finset.card_le_card hsub
  simpa [Fin.card_Ici] using h

/-- The number of points `≥ t i` is at most the number of points in `[t i, 1)`. -/
lemma count_ge_le_cnt {d : ℕ} (t : Fin d → ℝ) (ht : ∀ j, t j ∈ Set.Ico 0 1) (i : Fin d) :
    (Finset.univ.filter (fun j : Fin d => t i ≤ t j)).card ≤ cnt t (t i) 1 := by
  refine Finset.card_le_card ?_
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  simp only [cnt, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico]
  exact ⟨hj, (ht j).2⟩

/-- `∑_{i : Fin d} i = d(d-1)/2`. -/
lemma sum_fin_cast (d : ℕ) : ∑ i : Fin d, (i : ℝ) = (d : ℝ) * ((d : ℝ) - 1) / 2 := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

/-- **Sorted form of the box-discrepancy estimate.** If `t : Fin d → ℝ` is nondecreasing with all
values in `[0,1)` and `disc t ≤ ε`, then `t i` is within `ε` of the uniform grid point `i/d`. -/
theorem sorted_bounds {d : ℕ} (t : Fin d → ℝ) (ht : ∀ j, t j ∈ Set.Ico 0 1)
    (hmono : Monotone t) {ε : ℝ} (hε : 0 ≤ ε) (hd : disc t ≤ ε) (i : Fin d) :
    (i : ℝ) / d - ε ≤ t i ∧ t i ≤ (i : ℝ) / d + ε := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Fin.pos i
  constructor
  · have hle := (abs_le.mp (count_le_of_disc ε hε t ht hd i)).2
    have hc := card_le_count_mono t hmono i
    have hc' : ((i.1 + 1 : ℕ) : ℝ) ≤
        ((Finset.univ.filter (fun j : Fin d => t j ≤ t i)).card : ℝ) := by
      exact_mod_cast hc
    push_cast at hc'
    have hmain : (i : ℝ) ≤ (t i + ε) * (d : ℝ) := by linarith
    have h2 : (i : ℝ) / (d : ℝ) ≤ t i + ε := (div_le_iff₀ hd0).mpr hmain
    linarith
  · have hb := abs_sub_cnt_div_le_disc ε t hd (a := t i) (b := 1) (ht i).1 (ht i).2.le le_rfl
    have h3 : -(ε) ≤ (1 - t i) - (cnt t (t i) 1 : ℝ) / (d : ℝ) := (abs_le.mp hb).1
    have hc := card_ge_count_mono t hmono i
    have hc2 := count_ge_le_cnt t ht i
    have hc' : ((d - i.1 : ℕ) : ℝ) ≤ (cnt t (t i) 1 : ℝ) := by
      exact_mod_cast le_trans hc hc2
    have hcast : ((d - i.1 : ℕ) : ℝ) = (d : ℝ) - (i : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt i.2)]
    rw [hcast] at hc'
    have hdiv : ((d : ℝ) - (i : ℝ)) / (d : ℝ) ≤ (cnt t (t i) 1 : ℝ) / (d : ℝ) :=
      div_le_div_of_nonneg_right hc' hd0.le
    have hstep : ((d : ℝ) - (i : ℝ)) / (d : ℝ) - ε ≤ 1 - t i := by linarith
    have e1 : ((d : ℝ) - (i : ℝ)) / (d : ℝ) = 1 - (i : ℝ) / d := by
      have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
      rw [show (1 : ℝ) = (d : ℝ) / (d : ℝ) by rw [div_self hdne], sub_div]
    rw [e1] at hstep
    linarith

/-- **The sum form of the discrepancy estimate** (paper's display `(discrepancy t)`): a sorted
configuration of `d` points in `[0,1)` with box discrepancy `≤ ε` has total sum within `dε` of
`(d-1)/2`. -/
theorem sum_bounds {d : ℕ} (hd0 : 0 < d) (t : Fin d → ℝ) (ht : ∀ j, t j ∈ Set.Ico 0 1)
    (hmono : Monotone t) {ε : ℝ} (hε : 0 ≤ ε) (hd : disc t ≤ ε) :
    |(∑ j, t j) - ((d : ℝ) - 1) / 2| ≤ (d : ℝ) * ε := by
  have hsum1 : ∑ i : Fin d, ((i : ℝ) / d - ε) = ((d : ℝ) - 1) / 2 - (d : ℝ) * ε := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_fin_cast d, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    field_simp
    ring
  have hsum2 : ∑ i : Fin d, ((i : ℝ) / d + ε) = ((d : ℝ) - 1) / 2 + (d : ℝ) * ε := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, sum_fin_cast d, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    field_simp
    ring
  have hlower : ((d : ℝ) - 1) / 2 - (d : ℝ) * ε ≤ ∑ j, t j := by
    have h1 : ∑ i : Fin d, ((i : ℝ) / d - ε) ≤ ∑ i : Fin d, t i :=
      Finset.sum_le_sum (fun i _ => (sorted_bounds t ht hmono hε hd i).1)
    linarith [hsum1]
  have hupper : ∑ j, t j ≤ ((d : ℝ) - 1) / 2 + (d : ℝ) * ε := by
    have h1 : ∑ i : Fin d, t i ≤ ∑ i : Fin d, ((i : ℝ) / d + ε) :=
      Finset.sum_le_sum (fun i _ => (sorted_bounds t ht hmono hε hd i).2)
    linarith [hsum2]
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The number of points in an interval is invariant under a permutation of the configuration. -/
lemma cnt_comp_perm {n : ℕ} (t : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (a b : ℝ) :
    cnt (fun j => t (σ j)) a b = cnt t a b := by
  refine Finset.card_bij (fun j _ => σ j) ?_ ?_ ?_
  · intro j hj
    simpa using hj
  · intro j1 _ j2 _ h
    exact σ.injective h
  · intro j hj
    exact ⟨σ.symm j, by simpa using hj, by simp⟩

/-- The box discrepancy is invariant under relabelling of the configuration. -/
lemma disc_comp_perm {n : ℕ} (t : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    disc (fun j => t (σ j)) = disc t := by
  simp only [disc]
  congr 1
  ext y
  constructor <;> rintro ⟨p, hp, rfl⟩ <;>
    exact ⟨p, hp, by simp only [cnt_comp_perm]⟩

/-- The sum form of the discrepancy estimate for an arbitrary configuration: sort it by a
permutation and apply `sum_bounds`. -/
theorem sum_bounds_of_perm {d : ℕ} (hd0 : 0 < d) (n : Fin d → ℝ)
    (hn : ∀ j, n j ∈ Set.Ico 0 1) (σ : Equiv.Perm (Fin d))
    (hmono : Monotone (fun i => n (σ i))) {ε : ℝ} (hε : 0 ≤ ε) (hd : disc n ≤ ε) :
    |(∑ j, n j) - ((d : ℝ) - 1) / 2| ≤ (d : ℝ) * ε := by
  have h1 := sum_bounds hd0 (fun i => n (σ i)) (fun i => hn (σ i)) hmono hε
    (by rw [disc_comp_perm]; exact hd)
  rwa [Equiv.sum_comp] at h1

end Work.Holonomy3
