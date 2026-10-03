import Mathlib
import Submission.Work.Pert.sum_inv_dist_gate_walk
import Submission.Work.Pert.Count.exists_int_dist_le_of_iInf_le

/-!
# PERT · `Work.Pert.card_lattice_le_of_gate_walk`

The *counting* companion of `Work.Pert.sum_inv_dist_gate_walk`: along a walk `w` whose steps are
within `1/32` of `+1`, the number of indices `j ≤ n` for which `α * w j` comes within `‖α‖` of the
lattice is bounded by `(125/9) (1 + n ‖α‖)` — a *linear* bound with no logarithmic factor.

Mechanism.  Writing `R = ‖α‖ > 0` (positivity is exactly `InF1 α`), the real walk
`y j = Re (α * w j)` has increments in `[(2/3) R, (33/32) R]` (`Work.Pert.re_alpha_step`), so it
is strictly increasing with step `≥ (2/3) R`.  Membership of `α * w j` in the `R`-neighbourhood of
the lattice implies that `y j` is within `R` of an integer (`exists_int_dist_re_le_of_iInf_le`),
and `Work.Pert.Count.card_le_of_mono_walk` gives the count

`# {j ≤ n} ≤ (y n - y 0 + 2 R + 1) (2 R / ((2/3) R) + 1)`
           `≤ 4 (n (33/32) R + 2 R + 1)`,

the second factor being exactly `4`.  For `n = 0` the count is at most `1`; for `n ≥ 1` the
elementary inequality `4 (n (33/32) R + 2 R + 1) ≤ (125/9) (1 + n R)` closes the proof.  Neither
the gate hypothesis nor `Ξ > 0` is used: the estimate is purely about the walk.
-/

namespace Work.Pert

open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

/-- From a point of `ℂ` within `s ≥ 0` of the lattice `ℤ ⊂ ℂ`, an integer is within `s` of the
real part. -/
lemma exists_int_dist_re_le_of_iInf_le {z : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (h : (⨅ k : ℤ, dist z (k : ℂ)) ≤ s) : ∃ k : ℤ, dist z.re (k : ℝ) ≤ s := by
  obtain ⟨k, hk⟩ := Work.Pert.Count.exists_int_dist_le_of_iInf_le hs h
  refine ⟨k, ?_⟩
  have h1 : |z.re - (k : ℝ)| = |(z - (k : ℂ)).re| := by simp
  calc dist z.re (k : ℝ) = |z.re - (k : ℝ)| := Real.dist_eq _ _
    _ = |(z - (k : ℂ)).re| := h1
    _ ≤ ‖z - (k : ℂ)‖ := Complex.abs_re_le_norm _
    _ = dist z (k : ℂ) := by rw [dist_eq_norm]
    _ ≤ s := hk

/-- Elementary arithmetic of the counting bound: for `n ≥ 1` and `R ≥ 0`,
`4 ((33/32) n R + 2 R + 1) ≤ (125/9) (1 + n R)`. -/
lemma four_mul_arith {n : ℕ} {R : ℝ} (hn : 1 ≤ n) (hR : 0 ≤ R) :
    4 * (((33 : ℝ) / 32) * (n : ℝ) * R + 2 * R + 1) ≤ (125 / 9 : ℝ) * (1 + (n : ℝ) * R) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0 : (0 : ℝ) ≤ ((n : ℝ) - 1) * R := mul_nonneg (by linarith) hR
  nlinarith [h0, hR, hn1]

theorem card_lattice_le_of_gate_walk {w : ℕ → ℂ} {α : ℂ} {Ξ : ℝ} {n : ℕ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α)
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, w j ∈ Work.Pert.Qm Ξ α) :
    (((Finset.range (n + 1)).filter
        (fun j => (⨅ k : ℤ, dist (α * w j) (k : ℂ)) ≤ ‖α‖)).card : ℝ)
      ≤ (125 / 9 : ℝ) * (1 + (n : ℝ) * ‖α‖) := by
  classical
  -- `InF1 α` forces `α ≠ 0`, hence `R = ‖α‖ > 0`.
  have hαne : α ≠ 0 := by
    intro h0
    have h1 : |α.im| < α.re := hInF1
    rw [h0] at h1
    simp at h1
  have hRpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  -- the increments of the real walk `j ↦ (α * w j).re`
  have hsteplo : ∀ j < n, (2 / 3) * ‖α‖ ≤ (α * w (j + 1)).re - (α * w j).re :=
    fun j hj => (Work.Pert.re_alpha_step hInF1 hstep j hj).1
  have hstephi : ∀ j < n, (α * w (j + 1)).re - (α * w j).re ≤ (33 / 32) * ‖α‖ :=
    fun j hj => (Work.Pert.re_alpha_step hInF1 hstep j hj).2
  -- the counting lemma for a monotone walk
  have hcount := Work.Pert.Count.card_le_of_mono_walk
      (t := fun j => (α * w j).re) (n := n) (s := ‖α‖) (δ := (2 / 3) * ‖α‖)
      (p := fun j => (⨅ k : ℤ, dist (α * w j) (k : ℂ)) ≤ ‖α‖)
      (by positivity) (norm_nonneg α)
      (fun j hj => by have h := hsteplo j hj; linarith)
      (fun j _ hj => exists_int_dist_re_le_of_iInf_le (norm_nonneg α) hj)
  -- the total displacement of the walk
  have hwin : (α * w n).re - (α * w 0).re ≤ (n : ℝ) * ((33 / 32) * ‖α‖) :=
    Work.Pert.Count.walk_telescope_le (m := fun j => (α * w j).re) (c₁ := (33 / 32) * ‖α‖)
      (fun j hj => hstephi j hj)
  have hfib : 2 * ‖α‖ / ((2 / 3) * ‖α‖) + 1 = 4 := by
    have h : ‖α‖ ≠ 0 := hRpos.ne'
    field_simp
    norm_num
  -- the unconditional bound `count ≤ 4 (n (33/32) R + 2 R + 1)`
  have hbound : (((Finset.range (n + 1)).filter
        (fun j => (⨅ k : ℤ, dist (α * w j) (k : ℂ)) ≤ ‖α‖)).card : ℝ)
      ≤ 4 * (((33 : ℝ) / 32) * (n : ℝ) * ‖α‖ + 2 * ‖α‖ + 1) := by
    refine hcount.trans ?_
    rw [hfib]
    calc (((α * w n).re - (α * w 0).re) + 2 * ‖α‖ + 1) * 4
        ≤ ((n : ℝ) * ((33 / 32) * ‖α‖) + 2 * ‖α‖ + 1) * 4 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          linarith [hwin]
      _ = 4 * (((33 : ℝ) / 32) * (n : ℝ) * ‖α‖ + 2 * ‖α‖ + 1) := by ring
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- `n = 0`: the count is at most `1`
    subst hn0
    have hcard : (((Finset.range (0 + 1)).filter
        (fun j => (⨅ k : ℤ, dist (α * w j) (k : ℂ)) ≤ ‖α‖)).card : ℝ) ≤ 1 := by
      have h1 := Finset.card_le_card
        (Finset.filter_subset (fun j => (⨅ k : ℤ, dist (α * w j) (k : ℂ)) ≤ ‖α‖)
          (Finset.range (0 + 1)))
      rw [Finset.card_range] at h1
      exact_mod_cast h1
    have htarget : (125 / 9 : ℝ) * (1 + ((0 : ℕ) : ℝ) * ‖α‖) = 125 / 9 := by norm_num
    rw [htarget]
    linarith
  · exact hbound.trans (four_mul_arith hnpos (norm_nonneg α))

end

end Work.Pert
