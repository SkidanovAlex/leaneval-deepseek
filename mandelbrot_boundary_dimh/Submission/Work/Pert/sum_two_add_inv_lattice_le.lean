import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.sum_inv_dist_gate_walk
import Submission.Work.Pert.count_gate_walk_close
import Submission.Work.Pert.card_lattice_le_of_gate_walk

namespace Work.Pert

open scoped Classical

noncomputable section

/-!
# PERT · `Work.Pert.sum_two_add_inv_lattice_le`

Along a gate walk `w` (steps within `1/32` of `+1`, vertices in the gate `Qm Ξ α`) whose
vertices either sit *exactly* on the lattice `ℤ/α` or stay at lattice distance
`≥ c₀ ‖α‖` (hypothesis `hlat`), the accumulated per-step weight

`2 + (9 / 25) / dist (α * w j) ℤ`

satisfies the harmonic bound

`∑_{j<n} (2 + (9/25)/d_j) ≤ 2 n + 11 (1+n‖α‖)(1+log(2+n))/‖α‖ + 5 (1+n‖α‖)/(c₀‖α‖)`.

**Proof.**  The `2`-terms give exactly `2 n`, so only `D := ∑_{j<n} 1/d_j` (a term with `d_j = 0`
contributes the Lean-junk value `1/0 = 0`) has to be bounded.  Split the indices at the level
`‖α‖`:

* far indices (`d_j > ‖α‖`): `1/d_j = 1/max ‖α‖ d_j`, and `Work.Pert.sum_inv_dist_gate_walk`
  bounds the full sum of `1/max ‖α‖ d_j` by `30 (1+n‖α‖)(1+log(2+n))/‖α‖`; after multiplying by
  `9/25` this is `10.8 < 11`.
* near indices (`d_j ≤ ‖α‖`): by `hlat` (and `d_j ≥ 0`), `1/d_j ≤ 1/(c₀‖α‖)`, so the near part is
  at most `#near /(c₀‖α‖)`.  The count `#near ≤ (125/9)(1+n‖α‖)` is the sharp one
  (`Work.Pert.card_lattice_le_of_gate_walk`), because `(9/25)·(125/9) = 5` exactly.
-/

/-! ## Elementary arithmetic -/

private lemma near_arith {ν c r : ℝ} :
    (9 / 25 : ℝ) * ((125 / 9 : ℝ) * (1 + ν) * (1 / (c * r))) ≤ 5 * (1 + ν) / (c * r) := by
  have h1 : (9 / 25 : ℝ) * (125 / 9 : ℝ) * (1 + ν) = 5 * (1 + ν) := by ring
  have h2 : (9 / 25 : ℝ) * ((125 / 9 : ℝ) * (1 + ν) * (1 / (c * r)))
      = ((9 / 25 : ℝ) * (125 / 9 : ℝ) * (1 + ν)) * (1 / (c * r)) := by ring
  rw [h2, h1, mul_one_div]

private lemma far_arith {ν L r : ℝ} (hr : 0 < r) (hν : 0 ≤ ν) (hL : 0 ≤ L) :
    (9 / 25 : ℝ) * (30 * (1 + ν) * (1 + L) / r) ≤ 11 * (1 + ν) * (1 + L) / r := by
  have h : (9 / 25 : ℝ) * 30 ≤ 11 := by norm_num
  have hnn : 0 ≤ (1 + ν) * (1 + L) / r := by positivity
  calc (9 / 25 : ℝ) * (30 * (1 + ν) * (1 + L) / r)
      = ((9 / 25 : ℝ) * 30) * ((1 + ν) * (1 + L) / r) := by ring
    _ ≤ 11 * ((1 + ν) * (1 + L) / r) := mul_le_mul_of_nonneg_right h hnn
    _ = 11 * (1 + ν) * (1 + L) / r := by ring

private lemma final_arith {ν c r L : ℝ} (hr : 0 < r) (hν : 0 ≤ ν) (hL : 0 ≤ L) :
    (9 / 25 : ℝ) * ((125 / 9 : ℝ) * (1 + ν) * (1 / (c * r)) + 30 * (1 + ν) * (1 + L) / r)
      ≤ 5 * (1 + ν) / (c * r) + 11 * (1 + ν) * (1 + L) / r := by
  have h1 := near_arith (ν := ν) (c := c) (r := r)
  have h2 := far_arith (ν := ν) (L := L) (r := r) hr hν hL
  have h3 : (9 / 25 : ℝ) * ((125 / 9 : ℝ) * (1 + ν) * (1 / (c * r)) + 30 * (1 + ν) * (1 + L) / r)
      = (9 / 25 : ℝ) * ((125 / 9 : ℝ) * (1 + ν) * (1 / (c * r)))
        + (9 / 25 : ℝ) * (30 * (1 + ν) * (1 + L) / r) := by ring
  linarith [h1, h2, h3]

/-- A single near term: if `0 ≤ d ≤ r` and every *positive* lattice distance is `≥ c * r`, then
`1/d ≤ 1/(c r)` (the case `d = 0` contributes the junk value `1/0 = 0`). -/
private lemma one_div_le_of_near {d c r : ℝ} (hcr : 0 < c * r) (hd : 0 ≤ d)
    (hlat : 0 < d → c * r ≤ d) : 1 / d ≤ 1 / (c * r) := by
  by_cases h : 0 < d
  · exact one_div_le_one_div_of_le hcr (hlat h)
  · have h0 : d = 0 := le_antisymm (not_lt.mp h) hd
    rw [h0, one_div, inv_zero]
    positivity

/-! ## The main theorem -/

theorem sum_two_add_inv_lattice_le {w : ℕ → ℂ} {α : ℂ} {Ξ : ℝ} {n : ℕ} {c₀ : ℝ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (hc₀ : 0 < c₀)
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, w j ∈ Work.Pert.Qm Ξ α)
    (hlat : ∀ j, j < n → 0 < (⨅ k : ℤ, dist (α * w j) (k : ℂ)) →
      c₀ * ‖α‖ ≤ (⨅ k : ℤ, dist (α * w j) (k : ℂ))) :
    (∑ j ∈ Finset.range n, (2 + (9 / 25) / (⨅ k : ℤ, dist (α * w j) (k : ℂ))))
      ≤ 2 * (n : ℝ)
        + 11 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖
        + 5 * (1 + (n : ℝ) * ‖α‖) / (c₀ * ‖α‖) := by
  classical
  have hInF1' : |α.im| < α.re := hInF1
  have hrpos : 0 < ‖α‖ := by
    have h1 : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1'
    have hne : α ≠ 0 := by intro h; rw [h] at h1; simp at h1
    exact norm_pos_iff.mpr hne
  have hc0a : 0 < c₀ * ‖α‖ := mul_pos hc₀ hrpos
  set d : ℕ → ℝ := fun j => ⨅ k : ℤ, dist (α * w j) (k : ℂ) with hd
  have hdnn : ∀ j, 0 ≤ d j := fun j => by
    rw [hd]; exact le_ciInf (fun k => dist_nonneg)
  set A : Finset ℕ := (Finset.range n).filter (fun j => d j ≤ ‖α‖) with hA
  set B : Finset ℕ := (Finset.range n).filter (fun j => ¬ (d j ≤ ‖α‖)) with hB
  -- (1) the sum `∑ (2 + (9/25)/d_j)` is `2n` plus `(9/25)` times the harmonic sum
  have hsum1 : (∑ j ∈ Finset.range n, (2 + (9 / 25) / d j))
      = 2 * (n : ℝ) + (9 / 25) * (∑ j ∈ Finset.range n, 1 / d j) := by
    have h1 : ∀ j, (9 / 25) / d j = (9 / 25) * (1 / d j) := fun j => by
      rw [one_div, div_eq_mul_inv, div_eq_mul_inv]
    calc (∑ j ∈ Finset.range n, (2 + (9 / 25) / d j))
        = ∑ j ∈ Finset.range n, (2 + (9 / 25) * (1 / d j)) :=
          Finset.sum_congr rfl (fun j _ => by rw [h1 j])
      _ = (∑ _j ∈ Finset.range n, (2 : ℝ)) + ∑ j ∈ Finset.range n, (9 / 25) * (1 / d j) :=
          Finset.sum_add_distrib
      _ = 2 * (n : ℝ) + (9 / 25) * (∑ j ∈ Finset.range n, 1 / d j) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
          ring
  -- (2) split of the harmonic sum at the level `‖α‖`
  have hsplit : (∑ j ∈ A, 1 / d j) + (∑ j ∈ B, 1 / d j) = ∑ j ∈ Finset.range n, 1 / d j := by
    rw [hA, hB]
    exact Finset.sum_filter_add_sum_filter_not (Finset.range n) (fun j => d j ≤ ‖α‖)
      (fun j => 1 / d j)
  -- (3) the near part, via `hlat`
  have hnear : ∑ j ∈ A, 1 / d j ≤ (A.card : ℝ) * (1 / (c₀ * ‖α‖)) := by
    have hpt : ∀ j ∈ A, 1 / d j ≤ 1 / (c₀ * ‖α‖) := by
      intro j hj
      rw [hA, Finset.mem_filter] at hj
      obtain ⟨hjn, hjle⟩ := hj
      exact one_div_le_of_near hc0a (hdnn j)
        (fun hp => hlat j (Finset.mem_range.mp hjn) hp)
    calc ∑ j ∈ A, 1 / d j ≤ ∑ _j ∈ A, 1 / (c₀ * ‖α‖) := Finset.sum_le_sum hpt
      _ = (A.card : ℝ) * (1 / (c₀ * ‖α‖)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- (4) the sharp count of near indices
  have hAcard : (A.card : ℝ) ≤ (125 / 9 : ℝ) * (1 + (n : ℝ) * ‖α‖) := by
    have hsub : A ⊆ (Finset.range (n + 1)).filter (fun j => d j ≤ ‖α‖) := by
      intro j hj
      rw [hA, Finset.mem_filter] at hj
      have hjlt : j < n := Finset.mem_range.mp hj.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj.2⟩
    have h1 : (A.card : ℝ)
        ≤ (((Finset.range (n + 1)).filter (fun j => d j ≤ ‖α‖)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2' : (((Finset.range (n + 1)).filter (fun j => d j ≤ ‖α‖)).card : ℝ)
        ≤ (125 / 9 : ℝ) * (1 + (n : ℝ) * ‖α‖) := by
      have h2 := card_lattice_le_of_gate_walk (w := w) (α := α) (Ξ := Ξ) (n := n)
        hΞ hInF1 hstep hgate
      simpa [hd] using h2
    linarith
  -- (5) the far part: `1/d_j = 1/max ‖α‖ d_j` on `B`, then the gate-walk harmonic bound
  have hBfar : ∑ j ∈ B, 1 / d j ≤ ∑ j ∈ Finset.range n, 1 / max ‖α‖ (d j) := by
    have heq : ∑ j ∈ B, 1 / d j = ∑ j ∈ B, 1 / max ‖α‖ (d j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hB, Finset.mem_filter] at hj
      rw [max_eq_right (le_of_lt (lt_of_not_ge hj.2))]
    rw [heq]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      rw [hB, Finset.mem_filter] at hj
      exact hj.1
    · intro i _ _
      have : 0 < max ‖α‖ (d i) := lt_of_lt_of_le hrpos (le_max_left _ _)
      positivity
  have hfar : ∑ j ∈ B, 1 / d j
      ≤ 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖ := by
    refine le_trans hBfar ?_
    have h1 : ∑ j ∈ Finset.range n, 1 / max ‖α‖ (d j)
        ≤ ∑ j ∈ Finset.range (n + 1), 1 / max ‖α‖ (d j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        have hjlt : j < n := Finset.mem_range.mp hj
        exact Finset.mem_range.mpr (by omega)
      · intro i _ _
        have : 0 < max ‖α‖ (d i) := lt_of_lt_of_le hrpos (le_max_left _ _)
        positivity
    refine le_trans h1 ?_
    have h2 := sum_inv_dist_gate_walk (α := α) (Ξ := Ξ) (w := w) (n := n) (ρ := ‖α‖)
      hΞ hInF1 le_rfl hstep hgate
    simpa [hd] using h2
  -- (6) the harmonic sum bound
  have hD : ∑ j ∈ Finset.range n, 1 / d j
      ≤ (125 / 9 : ℝ) * (1 + (n : ℝ) * ‖α‖) * (1 / (c₀ * ‖α‖))
        + 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖ := by
    rw [← hsplit]
    refine add_le_add ?_ hfar
    calc ∑ j ∈ A, 1 / d j ≤ (A.card : ℝ) * (1 / (c₀ * ‖α‖)) := hnear
      _ ≤ ((125 / 9 : ℝ) * (1 + (n : ℝ) * ‖α‖)) * (1 / (c₀ * ‖α‖)) :=
          mul_le_mul_of_nonneg_right hAcard (by positivity)
  -- (7) assembly
  have hνnn : (0 : ℝ) ≤ (n : ℝ) * ‖α‖ := by positivity
  have hLnn : (0 : ℝ) ≤ Real.log (2 + (n : ℝ)) :=
    Real.log_nonneg (by have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
  have hstep7 := final_arith (ν := (n : ℝ) * ‖α‖) (c := c₀) (r := ‖α‖)
    (L := Real.log (2 + (n : ℝ))) hrpos hνnn hLnn
  calc (∑ j ∈ Finset.range n, (2 + (9 / 25) / d j))
      = 2 * (n : ℝ) + (9 / 25) * (∑ j ∈ Finset.range n, 1 / d j) := hsum1
    _ ≤ 2 * (n : ℝ) + (9 / 25) * ((125 / 9 : ℝ) * (1 + (n : ℝ) * ‖α‖) * (1 / (c₀ * ‖α‖))
          + 30 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖) := by
        linarith [mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 9 / 25)]
    _ ≤ 2 * (n : ℝ) + (5 * (1 + (n : ℝ) * ‖α‖) / (c₀ * ‖α‖)
          + 11 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖) := by
        linarith [hstep7]
    _ = 2 * (n : ℝ) + 11 * (1 + (n : ℝ) * ‖α‖) * (1 + Real.log (2 + (n : ℝ))) / ‖α‖
          + 5 * (1 + (n : ℝ) * ‖α‖) / (c₀ * ‖α‖) := by ring

end

end Work.Pert
