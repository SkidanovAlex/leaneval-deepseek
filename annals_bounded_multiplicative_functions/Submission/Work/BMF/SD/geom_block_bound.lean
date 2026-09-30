import Mathlib
import Submission.Work.BMF.SD.abel_geom_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

open Finset

/-- Geometric-series-in-short-intervals block bound.

Given a sequence `a m = z (m*q + r)` of unit complex numbers whose consecutive
blocks are almost equal up to the twist `star ζ` (i.e. `a (m+1) ≈ ζ * a m` with
error `ε` at each step), the partial sum of the first `M` terms is bounded by
`(1 + M*ε) * min M (2/‖ζ-1‖)`.

The proof reduces to `abel_geom_bound` applied to the normalised sequence
`w m = a m * ζ⁻¹^m`, which is `ε`-slowly varying with `‖w m‖ ≤ 1`, and using
`∑_{m<M} a m = ∑_{m<M} ζ^m * w m`. -/
theorem geom_block_bound (ζ : ℂ) (z : ℕ → ℂ) (q r M : ℕ) (ε : ℝ)
    (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) (hε : 0 ≤ ε)
    (hz1 : ∀ n, ‖z n‖ = 1)
    (hz : ∀ m < M, ‖z ((m+1)*q + r) * star ζ - z (m*q+r)‖ ≤ ε) :
    ‖∑ m ∈ Finset.range M, z (m*q + r)‖ ≤ (1 + (M:ℝ)*ε) * min (M:ℝ) (2/‖ζ-1‖) := by
  have _ : (0:ℝ) ≤ ε := hε
  have hζne : ζ ≠ 0 := by rw [← norm_pos_iff, hζ]; norm_num
  -- normalised sequence: `w m = z (m*q+r) * ζ⁻¹^m`
  let w : ℕ → ℂ := fun m => z (m*q+r) * ζ⁻¹^m
  -- `w` is `ε`-slowly varying
  have hw : ∀ m < M, ‖w (m+1) - w m‖ ≤ ε := by
    intro m hm
    have key : w (m+1) - w m = (z ((m+1)*q+r) * ζ⁻¹ - z (m*q+r)) * ζ⁻¹^m := by
      simp only [w]
      rw [pow_succ]
      ring
    rw [key, norm_mul, norm_pow, norm_inv, hζ, inv_one, one_pow, mul_one]
    simpa [Complex.inv_eq_conj hζ] using hz m hm
  -- `w` takes values of norm `≤ 1`
  have hw1 : ∀ m < M, ‖w m‖ ≤ 1 := by
    intro m _
    have : ‖w m‖ = 1 := by
      simp only [w, norm_mul, norm_pow, norm_inv, hζ, inv_one, one_pow, mul_one, hz1]
    rw [this]
  -- the two sums agree
  have hterm : ∀ m, ζ^m * w m = z (m*q+r) := by
    intro m
    simp only [w]
    rw [show ζ^m * (z (m*q+r) * ζ⁻¹^m) = z (m*q+r) * (ζ^m * ζ⁻¹^m) by ring]
    rw [← mul_pow, mul_inv_cancel₀ hζne, one_pow, mul_one]
  have hsum : (∑ m ∈ Finset.range M, z (m*q+r)) = ∑ m ∈ Finset.range M, ζ^m * w m :=
    Finset.sum_congr rfl (fun m _ => (hterm m).symm)
  have habel := abel_geom_bound ζ w M ε hζ hζ1 hw hw1
  rw [hsum]
  exact habel

end Work.BMF.SD
