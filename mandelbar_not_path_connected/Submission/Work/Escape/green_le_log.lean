import Mathlib
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Escape.norm_iterate_le_geomSum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Global upper bound for the Green function

For a map `f` with `MonicGrowth f d A` and `d ≥ 2`, the Green function of every point `z ∈ ℂ` is
bounded above by `d * log (max 2 (max (A + 1) ‖z‖))`.

The mechanism is the crude a priori bound `norm_iterate_le_geomSum`: with the radius
`B = max 2 (max (A + 1) ‖z‖)` (so that `B ≥ 2`, `A ≤ B` and `‖z‖ ≤ B`) the orbit satisfies
`‖f^[n] z‖ ≤ B ^ (1 + d + ⋯ + d^n)`.  Hence the `n`-th partial Green function obeys

`greenIter f d z n ≤ d^{-n} (1 + d + ⋯ + d^n) log B ≤ d/(d-1) log B ≤ d log B`,

where the geometric-sum identity `(1 + d + ⋯ + d^n)(d - 1) = d^{n+1} - 1` gives the middle step.
The bound is uniform in `n`, so passing to the limit (which exists by `tendsto_greenIter`) yields
the claim.  In particular the Green function is locally bounded, which is what the escape theory
needs downstream.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

theorem green_le_log (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d) (z : ℂ) :
    green f d z ≤ (d : ℝ) * Real.log (max 2 (max (A + 1) ‖z‖)) := by
  set B : ℝ := max 2 (max (A + 1) ‖z‖) with hBdef
  have hB1 : (1 : ℝ) ≤ B := by
    have : (2 : ℝ) ≤ B := le_max_left _ _
    linarith
  have hAB : A ≤ B := by
    have h1 : A ≤ A + 1 := by linarith
    exact h1.trans ((le_max_left _ _).trans (le_max_right _ _))
  have hzB : ‖z‖ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hbound : ∀ n : ℕ, greenIter f d z n ≤ (d : ℝ) * Real.log B := by
    intro n
    set S : ℕ := ∑ i ∈ Finset.range (n + 1), d ^ i with hSdef
    have hnorm : ‖(f^[n]) z‖ ≤ B ^ S := by
      have h2 : (2 : ℝ) ≤ B := le_max_left _ _
      have := norm_iterate_le_geomSum f d A h hd h2 hzB hAB n
      simpa [hSdef] using this
    have hM1 : (1 : ℝ) ≤ B ^ S := one_le_pow₀ hB1
    have h1 := greenIter_le_of_norm_le (f := f) (d := d) (z := z) (n := n) hM1 hnorm
    rw [Real.log_pow] at h1
    have hcast : (S : ℝ) = ∑ i ∈ Finset.range (n + 1), (d : ℝ) ^ i := by
      rw [hSdef]; push_cast; ring
    have hSle : (S : ℝ) ≤ (d : ℝ) ^ (n + 1) := by
      rw [hcast]
      have hgeom := geom_sum_mul (d : ℝ) (n + 1)
      have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
        linarith
      have hSnn : 0 ≤ ∑ i ∈ Finset.range (n + 1), (d : ℝ) ^ i :=
        Finset.sum_nonneg (fun i _ => by positivity)
      have h2 : ∑ i ∈ Finset.range (n + 1), (d : ℝ) ^ i
          ≤ (∑ i ∈ Finset.range (n + 1), (d : ℝ) ^ i) * ((d : ℝ) - 1) := by nlinarith
      rw [hgeom] at h2
      have h3 : (0 : ℝ) ≤ (d : ℝ) ^ (n + 1) := by positivity
      linarith
    have hpos : (0 : ℝ) < (d : ℝ) ^ n := by positivity
    have hkey : ((d : ℝ) ^ n)⁻¹ * (S : ℝ) ≤ (d : ℝ) := by
      calc ((d : ℝ) ^ n)⁻¹ * (S : ℝ) ≤ ((d : ℝ) ^ n)⁻¹ * (d : ℝ) ^ (n + 1) :=
            mul_le_mul_of_nonneg_left hSle (inv_nonneg.mpr hpos.le)
        _ = (d : ℝ) := by
              rw [pow_succ, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
    calc greenIter f d z n ≤ ((d : ℝ) ^ n)⁻¹ * ((S : ℝ) * Real.log B) := h1
      _ = (((d : ℝ) ^ n)⁻¹ * (S : ℝ)) * Real.log B := by ring
      _ ≤ (d : ℝ) * Real.log B := mul_le_mul_of_nonneg_right hkey hlogB
  exact le_of_tendsto (tendsto_greenIter f d A h hd z) (Filter.Eventually.of_forall hbound)

end Work.Escape
