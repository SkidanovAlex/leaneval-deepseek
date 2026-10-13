import Mathlib
import Submission.Work.WilG1.Cell.JunkDefs
import Submission.Work.WilG1.Cell.Junk.DiscDefs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic

set_option autoImplicit false

noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Cell.Junk

open WilkiesDesign

/-! ## The `ε`-`δ` form of continuity at a point

`Metric.continuousAt_iff` measures distances with the sup metric on `Fin n → ℝ`, while the
`Ω`-construction of `DiscDefs` uses the *sum of squares* `Σ_j (x_j - y_j)²`.  The two are
interchangeable because for a finite index set the two quantities are comparable, and the two
families of "balls" therefore generate the same neighbourhood filter.  Concretely,

* `Σ_j (x_j - y_j)² ≤ n · (dist x y)²` bounds the Euclidean quantity by the sup metric
  (`sum_sq_le_mul_dist`), which is what the direction "RHS ⟹ discontinuous" needs;
* conversely `dist x y ≤ max_j |x_j - y_j|`, and `(x_j - y_j)² < (δ/2)²` for all `j` forces
  `dist x y < δ`, which is what the direction "discontinuous ⟹ RHS" needs.

No square root is needed: the constants are chosen so that `n · (δ/(√n + 1))² < δ²`. -/

/-- The sum of squares is bounded by `n` times the square of the sup distance. -/
theorem sum_sq_le_mul_dist {n : ℕ} (x y : Fin n → ℝ) :
    (∑ j : Fin n, (x j - y j) ^ 2) ≤ (n : ℝ) * dist x y ^ 2 := by
  have h1 : ∀ j : Fin n, (x j - y j) ^ 2 ≤ dist x y ^ 2 := by
    intro j
    have h : dist (x j) (y j) ≤ dist x y := (dist_pi_le_iff dist_nonneg).mp le_rfl j
    rw [Real.dist_eq] at h
    refine sq_le_sq.mpr ?_
    simpa only [abs_of_nonneg dist_nonneg] using h
  calc (∑ j : Fin n, (x j - y j) ^ 2) ≤ ∑ _j : Fin n, dist x y ^ 2 :=
        Finset.sum_le_sum (fun j _ => h1 j)
    _ = (n : ℝ) * dist x y ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A real `x` is discontinuous at `y` exactly when some positive `ε` is realised as an
oscillation on every scale `δ`: the `ε`-`δ` formula of discontinuity written with the sum of
squares `Σ_j (x_j - y_j)²` instead of the sup distance. -/
theorem not_continuousAt_aux {n : ℕ} (h : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ) :
    ¬ ContinuousAt h y ↔
      ∃ ε > 0, ∀ δ > 0, ∃ x : Fin n → ℝ,
        (∑ j : Fin n, (x j - y j) ^ 2) < δ ^ 2 ∧ ε ^ 2 ≤ (h x - h y) ^ 2 := by
  constructor
  · intro hc
    rw [Metric.continuousAt_iff] at hc
    push_neg at hc
    obtain ⟨ε, hε, H⟩ := hc
    refine ⟨ε, hε, fun δ hδ => ?_⟩
    have hden : 0 < Real.sqrt (n : ℝ) + 1 := by positivity
    have hdpos : 0 < δ / (Real.sqrt (n : ℝ) + 1) := div_pos hδ hden
    obtain ⟨x, hx1, hx2⟩ := H (δ / (Real.sqrt (n : ℝ) + 1)) hdpos
    refine ⟨x, ?_, ?_⟩
    · have hb := sum_sq_le_mul_dist x y
      have hsq : dist x y ^ 2 < (δ / (Real.sqrt (n : ℝ) + 1)) ^ 2 := by
        refine sq_lt_sq.mpr ?_
        rwa [abs_of_nonneg dist_nonneg, abs_of_pos hdpos]
      have hkey : (n : ℝ) * (δ / (Real.sqrt (n : ℝ) + 1)) ^ 2 < δ ^ 2 := by
        have hs : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
        have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        have hpos : 0 < (Real.sqrt (n : ℝ) + 1) ^ 2 := by positivity
        rw [div_pow, ← mul_div_assoc, div_lt_iff₀ hpos]
        nlinarith [hs, hs0, mul_pos hδ hδ]
      calc (∑ j : Fin n, (x j - y j) ^ 2) ≤ (n : ℝ) * dist x y ^ 2 := hb
        _ ≤ (n : ℝ) * (δ / (Real.sqrt (n : ℝ) + 1)) ^ 2 :=
            mul_le_mul_of_nonneg_left (le_of_lt hsq) (Nat.cast_nonneg n)
        _ < δ ^ 2 := hkey
    · rw [Real.dist_eq] at hx2
      refine sq_le_sq.mpr ?_
      rwa [abs_of_nonneg hε.le]
  · rintro ⟨ε, hε, H⟩ hcont
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hδ'⟩ := hcont ε hε
    obtain ⟨x, hx1, hx2⟩ := H (δ / 2) (by linarith)
    have hδ2 : 0 < δ / 2 := by linarith
    have hdist : dist x y < δ := by
      have hb : ∀ j : Fin n, dist (x j) (y j) ≤ δ / 2 := by
        intro j
        have h1 : (x j - y j) ^ 2 < (δ / 2) ^ 2 :=
          lt_of_le_of_lt (Finset.single_le_sum (fun i _ => sq_nonneg (x i - y i))
            (Finset.mem_univ j)) hx1
        have h2 : |x j - y j| < δ / 2 := by
          have := sq_lt_sq.mp h1
          rwa [abs_of_pos hδ2] at this
        rw [Real.dist_eq]
        exact le_of_lt h2
      have := (dist_pi_le_iff (le_of_lt hδ2)).mpr hb
      linarith
    have hlt := hδ' hdist
    rw [Real.dist_eq] at hlt
    have hle : ε ≤ |h x - h y| := by
      have := sq_le_sq.mp hx2
      rwa [abs_of_nonneg hε.le] at this
    linarith [hlt, hle]

/-- The discontinuity locus of a function whose graph is `Ω`-definable is again `Ω`-definable:
`disc h = {y | ¬ ContinuousAt h y}` is carved out of `graphOf h` by the `ε`-`δ` formula of
discontinuity, which is a chain of projections and complements.

`resSet_mem` (in `DiscDefs`) supplies the `Ω`-membership of the set

`resSet n h = {y | ∃ ε > 0, ∀ δ > 0, ∃ x, Σ_j (x_j - y_j)² < δ² ∧ ε² ≤ (h x - h y)²}`,

`mem_resSet` identifies `resSet n h` with that set, and `not_continuousAt_aux` identifies the
`ε`-`δ` formula with `¬ ContinuousAt h y`. -/
theorem disc_mem (S : WilkiesDesign.SOMin) {n F D : ℕ} (h : (Fin n → ℝ) → ℝ)
    (hh : WilkiesDesign.graphOf h ∈ S.Ω F D (n + 1)) :
    ∃ (a : ℕ) (b : Polynomial ℕ), disc h ∈ S.Ω a (b.eval D) n := by
  obtain ⟨a, b, hb⟩ := resSet_mem (S := S) (n := n) (F := F) (D := D) hh
  refine ⟨a, b, ?_⟩
  have hset : resSet n h = disc h := by
    ext y
    simp only [mem_resSet, disc, Set.mem_ofPred_eq]
    exact (not_continuousAt_aux h y).symm
  rwa [hset] at hb

end Work.WilG1.Cell.Junk
