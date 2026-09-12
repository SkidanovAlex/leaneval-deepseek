import Mathlib
import Submission.Commons.Combinatorics.Finset.sum_range_comp_eq_sum_card_mul

/-!
# The stage count of the accumulated family

The accumulation produces a monotone stage assignment `st : ℕ → ℕ` for the `ℓ` indices, subject to
the *capacity relation* `ω (st j − 1) ≤ j < ω (st j)` (with `ω` the running maximum of the supply
counts, `ω 0 = 0`, `ω N = ℓ`, monotone).  This module records the resulting layer-cake identity

    `#{j < ℓ : st j = u} = ω u − ω (u − 1)`   (`1 ≤ u`),

so that a charge `F (st j)` per index can be re-summed as `Σ_u (ω u − ω (u−1))·F u`.

Module `Submission.Work.Extraction.StageCount`, namespace `Submission.StageCount`.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace Submission.StageCount

/-- The stage assignment is *minimal*: any stage whose capacity reaches `j` is at least `st j`. -/
lemma stage_le_of_lt {ω st : ℕ → ℕ} (hωmono : Monotone ω) {j : ℕ}
    (hst : ω (st j - 1) ≤ j) {u : ℕ} (hu : j < ω u) : st j ≤ u := by
  by_contra h
  push Not at h
  have h1 : st j - 1 ≥ u := by omega
  have h2 : ω u ≤ ω (st j - 1) := hωmono h1
  omega

/-- **The layer-cake identity.** -/
theorem card_stage_eq {ω st : ℕ → ℕ} (hω0 : ω 0 = 0) (hωmono : Monotone ω) {ℓ N : ℕ}
    (hωN : ω N = ℓ) (hstle : ∀ j < ℓ, st j ≤ N)
    (hst : ∀ j < ℓ, ω (st j - 1) ≤ j ∧ j < ω (st j)) {u : ℕ} (hu1 : 1 ≤ u) (huN : u ≤ N) :
    ((Finset.range ℓ).filter (fun j => st j = u)).card = ω u - ω (u - 1) := by
  have hset : (Finset.range ℓ).filter (fun j => st j = u) =
      (Finset.range ℓ).filter (fun j => ω (u - 1) ≤ j ∧ j < ω u) := by
    apply Finset.filter_congr
    intro j hj
    rw [Finset.mem_range] at hj
    constructor
    · intro h
      have h1 := (hst j hj).1
      have h2 := (hst j hj).2
      rw [h] at h1 h2
      exact ⟨h1, h2⟩
    · intro h
      obtain ⟨h1, h2⟩ := h
      have hle := stage_le_of_lt hωmono (hst j hj).1 h2
      have hge : u ≤ st j := by
        by_contra hc
        push Not at hc
        have hcu : st j < u := hc
        have hthis : st j ≤ u - 1 := by omega
        have h3 : ω (st j) ≤ ω (u - 1) := hωmono hthis
        have h4 : ω (st j) ≤ j := le_trans h3 h1
        have h5 := (hst j hj).2
        omega
      omega
  rw [hset]
  have hsub : (Finset.range ℓ).filter (fun j => ω (u - 1) ≤ j ∧ j < ω u) =
      Finset.Ico (ω (u - 1)) (ω u) := by
    refine Finset.Subset.antisymm (fun j hj => ?_) (fun j hj => ?_)
    · rw [Finset.mem_filter] at hj
      exact Finset.mem_Ico.mpr ⟨hj.2.1, hj.2.2⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
      rw [Finset.mem_filter]
      refine ⟨?_, h1, h2⟩
      have huN : u ≤ N := by omega
      have hle : ω u ≤ ℓ := by rw [← hωN]; exact hωmono huN
      rw [Finset.mem_range]
      exact lt_of_lt_of_le h2 hle
  rw [hsub, Nat.card_Ico]

/-- **The charge identity.**  A sum over the `ℓ` indices of a charge depending only on the stage
equals the weighted sum over the stages. -/
theorem sum_comp_stage_eq {ω st : ℕ → ℕ} (hω0 : ω 0 = 0) (hωmono : Monotone ω) {ℓ N : ℕ}
    (hωN : ω N = ℓ) (hstle : ∀ j < ℓ, st j ≤ N)
    (hst : ∀ j < ℓ, ω (st j - 1) ≤ j ∧ j < ω (st j)) (F : ℕ → ℝ) :
    (∑ j ∈ Finset.range ℓ, F (st j)) =
      ∑ u ∈ Finset.range N, (((ω (u + 1) : ℝ) - (ω u : ℝ)) * F (u + 1)) := by
  classical
  have hcard : ∀ u, u < N + 1 →
      ((Finset.range ℓ).filter (fun j => st j = u)).card =
        (if u = 0 then 0 else ω u - ω (u - 1)) := by
    intro u hu
    rcases Nat.eq_zero_or_pos u with h0 | hpos
    · subst h0
      have : (Finset.range ℓ).filter (fun j => st j = 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j hj
        rw [Finset.mem_range] at hj
        intro h
        have := (hst j hj).2
        rw [h] at this
        omega
      rw [this]
      simp
    · rw [if_neg (by omega)]
      exact card_stage_eq hω0 hωmono hωN hstle hst hpos (by omega)
  have h1 : (∑ j ∈ Finset.range ℓ, F (st j)) =
      ∑ u ∈ Finset.range (N + 1),
        (((Finset.range ℓ).filter (fun j => st j = u)).card : ℝ) * F u := by
    refine Commons.Combinatorics.Finset.sum_range_comp_eq_sum_card_mul (ℓ := ℓ) (R := N + 1)
      (n := st) (fun j hj => ?_) F
    have := hstle j hj
    omega
  have h0 : ((Finset.range ℓ).filter (fun j => st j = 0)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj hjeq
    rw [Finset.mem_range] at hj
    have h2 := (hst j hj).2
    rw [hjeq] at h2
    omega
  rw [h1, Finset.sum_range_succ', h0]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [Finset.mem_range] at hu
  have hcu := hcard (u + 1) (by omega)
  rw [if_neg (by omega : ¬ (u + 1 = 0))] at hcu
  rw [hcu, Nat.add_sub_cancel]
  have hle : ω u ≤ ω (u + 1) := hωmono (Nat.le_succ u)
  rw [Nat.cast_sub hle]

end Submission.StageCount

end
