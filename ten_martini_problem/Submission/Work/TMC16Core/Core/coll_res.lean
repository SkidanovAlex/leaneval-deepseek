import Mathlib
import Submission.Work.TMC16Core.Core.windows
import Submission.Work.TMC16Core.Core.coll_card_le_one
import Submission.Work.TMC16Core.Core.coll_sin_lb
import Submission.Work.TMC16Core.Core.coll_sum_card_le_one

/-!
# Collision residue of the resonant windows (`Core/coll_res`)

This file assembles the estimate that the *collisions* (pairs of indices in the two
resonant windows whose difference is a multiple of `q n`) contribute at most a deficit
`β q n + O(1)` to the Lagrange product.

Two facts are used:

* `coll_card_le_one`: for every `j` in the union of the windows there is **at most one**
  other index `i` with `q n ∣ (i - j)`;
* `coll_sin_lb`: each such term satisfies
  `log |sin (π (i - j) α)| ≥ -β q n`.

The sum over at most one term is then compared with the (non-positive) bound `-β q n - 10`
via `coll_sum_card_le_one`.
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-- `q n ≥ 1` follows from the two-sided Diophantine hypothesis on `q n α`. -/
lemma coll_qn_pos {α : ℝ} {q : ℕ → ℕ} {n : ℕ}
    (hΔlo : 1 / (((q (n + 1) : ℝ)) + (q n : ℝ)) < fracDist ((q n : ℝ) * α)) :
    1 ≤ q n := by
  by_contra h
  have h0 : q n = 0 := by omega
  rw [h0] at hΔlo
  have h1 : (0 : ℝ) ≤ 1 / ((q (n + 1) : ℝ) + ((0 : ℕ) : ℝ)) := by positivity
  have h2 : fracDist (((0 : ℕ) : ℝ) * α) = 0 := by simp [fracDist]
  rw [h2] at hΔlo
  exact absurd hΔlo (not_lt.mpr h1)

/-- Every element of the union of the two resonant windows lies in
`[-h, (ℓ+1) q - h - 1]`. -/
lemma coll_mem_bounds {q h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hh' : h ≤ 5 * q / 8) {i : ℤ}
    (hi : i ∈ J1resG h ∪ J2resG q h ℓ) :
    -(h : ℤ) ≤ i ∧ i ≤ ((ℓ : ℤ) + 1) * (q : ℤ) - (h : ℤ) - 1 := by
  have h8 : 8 * h ≤ 5 * q := by omega
  have hle : h ≤ q := by omega
  have h2hq : 2 * (h : ℤ) ≤ ((ℓ : ℤ) + 1) * (q : ℤ) := by
    have h1 : 2 * (h : ℤ) ≤ 2 * (q : ℤ) := by omega
    have h2 : (2 : ℤ) * (q : ℤ) ≤ ((ℓ : ℤ) + 1) * (q : ℤ) := by
      have : (2 : ℤ) ≤ (ℓ : ℤ) + 1 := by omega
      exact mul_le_mul_of_nonneg_right this (by positivity)
    linarith
  rcases Finset.mem_union.mp hi with hi | hi
  · rw [J1resG, Finset.mem_Icc] at hi
    obtain ⟨h1, h2⟩ := hi
    exact ⟨h1, by omega⟩
  · rw [J2resG, Finset.mem_Icc] at hi
    obtain ⟨h1, h2⟩ := hi
    have hlq : (0 : ℤ) ≤ ((ℓ : ℤ) - 1) * (q : ℤ) :=
      mul_nonneg (by omega) (by positivity)
    refine ⟨by omega, h2⟩

/-- A collision index `i ≠ j` in the union of the windows differs from `j` by `m · q` with
`m ≠ 0` and `|m| ≤ ℓ`. -/
lemma coll_m_exists {q h ℓ : ℕ} (hq : 1 ≤ q) (hℓ : 1 ≤ ℓ) (hh' : h ≤ 5 * q / 8) {i j : ℤ}
    (hi : i ∈ J1resG h ∪ J2resG q h ℓ) (hj : j ∈ J1resG h ∪ J2resG q h ℓ)
    (hij : i ≠ j) (hd : (q : ℤ) ∣ (i - j)) :
    ∃ m : ℤ, i - j = m * (q : ℤ) ∧ m ≠ 0 ∧ |m| ≤ (ℓ : ℤ) := by
  obtain ⟨c, hc⟩ := hd
  have hbi := coll_mem_bounds hℓ hh' hi
  have hbj := coll_mem_bounds hℓ hh' hj
  have hdiff : |i - j| ≤ ((ℓ : ℤ) + 1) * (q : ℤ) - 1 := by
    rw [abs_le]
    exact ⟨by omega, by omega⟩
  refine ⟨c, by rw [hc, mul_comm], ?_, ?_⟩
  · intro hc0
    have hzero : i - j = 0 := by rw [hc, hc0, mul_zero]
    exact hij (by omega)
  · have hqc : |c| * (q : ℤ) ≤ ((ℓ : ℤ) + 1) * (q : ℤ) - 1 := by
      have h := hdiff
      rw [hc, abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ (q : ℤ))] at h
      have h' : (q : ℤ) * |c| = |c| * (q : ℤ) := mul_comm _ _
      linarith
    by_contra hcon
    push Not at hcon
    have h1 : (ℓ : ℤ) + 1 ≤ |c| := by omega
    have h2 : ((ℓ : ℤ) + 1) * (q : ℤ) ≤ |c| * (q : ℤ) :=
      mul_le_mul_of_nonneg_right h1 (by omega)
    linarith

theorem coll_res {α β : ℝ} {q : ℕ → ℕ} {n h ℓ : ℕ}
    (hβ0 : 0 ≤ β) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hh : 3 * q n / 5 ≤ h) (hh' : h ≤ 5 * q n / 8)
    (hℓb : 10 * (ℓ : ℤ) * (q n : ℤ) ≤ (q (n + 1) : ℤ))
    (hΔlo : 1 / (((q (n + 1) : ℝ)) + (q n : ℝ)) < Work.TMC16Core.fracDist ((q n : ℝ) * α))
    (hΔup : Work.TMC16Core.fracDist ((q n : ℝ) * α) ≤ 1 / ((q (n + 1) : ℝ)))
    (hβ : (q (n + 1) : ℝ) ≤ Real.exp (β * (q n : ℝ))) :
    ∀ j ∈ Work.TMC16Core.Core.J1resG h ∪ Work.TMC16Core.Core.J2resG (q n) h ℓ,
      -β * (q n : ℝ) - 10 ≤
        ∑ i ∈ (Work.TMC16Core.Core.J1resG h ∪ Work.TMC16Core.Core.J2resG (q n) h ℓ).filter
            (fun i => i ≠ j ∧ (q n : ℤ) ∣ (i - j)),
          Real.log |Real.sin (Real.pi * (((i - j : ℤ)) : ℝ) * α)| := by
  have hq : 1 ≤ q n := coll_qn_pos hΔlo
  intro j hj
  refine coll_sum_card_le_one
      (f := fun i : ℤ => Real.log |Real.sin (Real.pi * (((i - j : ℤ)) : ℝ) * α)|)
      (coll_card_le_one hq hh hh' hℓ j hj) ?_ ?_
  · have hqnn : (0 : ℝ) ≤ (q n : ℝ) := Nat.cast_nonneg _
    nlinarith
  · intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hiU, hij, hdvd⟩ := hi
    obtain ⟨m, hm, hmne, hmle⟩ := coll_m_exists hq hℓ hh' hiU hj hij hdvd
    have hkey := coll_sin_lb (α := α) (β := β) (qn := q n) (qn1 := q (n + 1))
      hℓ hq hℓb hΔlo hΔup hβ hmne hmle
    have harg : Real.pi * (((i - j : ℤ)) : ℝ) * α = Real.pi * ((m : ℝ) * (q n : ℝ) * α) := by
      rw [hm]; push_cast; ring
    have hlog : -β * (q n : ℝ) ≤
        Real.log |Real.sin (Real.pi * (((i - j : ℤ)) : ℝ) * α)| := by
      rw [harg]
      have := Real.log_le_log (Real.exp_pos (-β * (q n : ℝ))) hkey
      rwa [Real.log_exp] at this
    linarith

end Work.TMC16Core.Core
