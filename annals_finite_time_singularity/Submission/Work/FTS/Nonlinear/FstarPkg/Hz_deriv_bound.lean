/-
Copyright: work module for the Elgindi finite-time singularity project.

# The uniform weighted bound `|(z+1)^k H^{(k)}(z)| ≤ HB k` for the radial factor of `D_z F_*`

`Work.FTS.Nonlinear.FstarPkg.Hz z = 2z(1-z)/(1+z)³` is the radial factor of
`D_z F_* = α·(Γ/c)·H` (`Work.Construction.Dz_Fstar_eq`); see
`Submission/Work/FTS/Nonlinear/FstarPkg/DzHzDefs.lean`.  This file proves that the
weighted derivatives `(z+1)^k H^{(k)}(z)` are bounded uniformly in `k` on `[0,∞)` by
the explicit sequence

  `HB k = 2·((k+1)!(k+2) + k·k!(k+1))`,

which is what makes `D_z F_* ∈ 𝒲^{4,∞}` with an `α`-independent constant.

## Mathematics

On `(-1,∞)` we have `H(z) = 2·z·h'(z)` with `h(z) = z/(1+z)²` (`Hz_eq_mul_deriv`), so by
Leibniz (`z^{(j)} = 0` for `j ≥ 2`)

  `H^{(k)} = 2·(z·h^{(k+1)} + k·h^{(k)})`.

For `z ≥ 0`, `|(z+1)^k h^{(k)}(z)| ≤ k!(k+1)` (`pzIter_hKer_bound`), and writing
`z = (z+1)·z/(z+1)` with `0 ≤ z/(z+1) ≤ 1` gives `|z·(z+1)^k h^{(k+1)}(z)| ≤ (k+1)!(k+2)`.
Adding the two pieces yields `HB k`.

The iterated-derivative formula for `H` is proved by induction on `k`, using the closed
form `hKerClosed` of `Work.Spaces.pzIter_hKer_bound` (`hasDerivAt_hKerClosed`); it is the
only place where a derivative of `H` is taken, so `Hz` itself (a rational function) is
never differentiated directly.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs
import Submission.Work.Spaces.pzIter_hKer_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.FstarPkg

open scoped Topology
open Work.Spaces

-- Intended full name: `Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound`
-- (declare it inside `namespace Work.FTS.Nonlinear.FstarPkg`).  Here `Hz` and `HB` are the
-- definitions of `Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs`;
-- `Hz_eq_mul_deriv` (same module) gives `Hz z = 2 * (z * deriv hKer z)` for `z > -1`, and
-- `Work.Spaces.iter_deriv_hKerClosed` / `Work.Spaces.pzIter_hKer_bound` give
-- `deriv^[m] hKer = hKerClosed m` with `|(z+1)^m hKerClosed m z| ≤ m!(m+1)` for `z ≥ 0`.
theorem Hz_deriv_bound (k : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    |(z + 1) ^ k * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z|
      ≤ Work.FTS.Nonlinear.FstarPkg.HB k := by
  -- The iterated derivatives of `Hz` in closed form, on `(-1,∞)`:
  -- `H^{(n)} = 2·(y·h^{(n+1)} + n·h^{(n)})` (Leibniz, since `y'' = 0`).
  have hiter : ∀ n : ℕ, ∀ y : ℝ, -1 < y →
      deriv^[n] Work.FTS.Nonlinear.FstarPkg.Hz y
        = 2 * (y * hKerClosed (n + 1) y + (n : ℝ) * hKerClosed n y) := by
    intro n
    induction n with
    | zero =>
      intro y hy
      simp only [Function.iterate_zero_apply]
      have h1 : deriv Work.Spaces.hKer y = hKerClosed 1 y := by
        show deriv (fun y : ℝ => y / (1 + y) ^ 2) y = hKerClosed 1 y
        exact Work.Spaces.iter_deriv_hKerClosed 1 y hy
      rw [Work.FTS.Nonlinear.FstarPkg.Hz_eq_mul_deriv hy, h1]
      simp [zero_mul]
    | succ n ih =>
      intro y hy
      rw [Function.iterate_succ_apply']
      have hev : deriv^[n] Work.FTS.Nonlinear.FstarPkg.Hz =ᶠ[𝓝 y]
          (fun t : ℝ => 2 * (t * hKerClosed (n + 1) t + (n : ℝ) * hKerClosed n t)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
        exact ih t ht
      rw [hev.deriv_eq]
      have hyne : y ≠ -1 := by linarith
      have hd1 : HasDerivAt (fun t : ℝ => t * hKerClosed (n + 1) t)
          (1 * hKerClosed (n + 1) y + y * hKerClosed ((n + 1) + 1) y) y :=
        (hasDerivAt_id y).mul (Work.Spaces.hasDerivAt_hKerClosed (n + 1) hyne)
      have hd2 : HasDerivAt (fun t : ℝ => (n : ℝ) * hKerClosed n t)
          ((n : ℝ) * hKerClosed (n + 1) y) y :=
        (Work.Spaces.hasDerivAt_hKerClosed n hyne).const_mul (n : ℝ)
      have hd : HasDerivAt
          (fun t : ℝ => 2 * (t * hKerClosed (n + 1) t + (n : ℝ) * hKerClosed n t))
          (2 * (1 * hKerClosed (n + 1) y + y * hKerClosed ((n + 1) + 1) y
            + (n : ℝ) * hKerClosed (n + 1) y)) y :=
        (hd1.add hd2).const_mul 2
      rw [hd.deriv]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
  -- The weighted bound for the closed form of `h` (`Work.Spaces.pzIter_hKer_bound`).
  have hpz : ∀ n : ℕ, ∀ y : ℝ, 0 ≤ y →
      |(y + 1) ^ n * hKerClosed n y| ≤ (n.factorial : ℝ) * (n + 1) := by
    intro n y hy
    have h := Work.Spaces.pzIter_hKer_bound n y hy
    rwa [show deriv^[n] (fun t : ℝ => t / (1 + t) ^ 2) y = hKerClosed n y from
        Work.Spaces.iter_deriv_hKerClosed n y (by linarith)] at h
  have hz1 : -1 < z := by linarith
  rw [hiter k z hz1]
  have hzp : (0 : ℝ) < z + 1 := by linarith
  -- The `z·h^{(k+1)}` term: move the factor `z` onto the weight `(z+1)^{k+1}`.
  have hpow : z * ((z + 1) ^ k * hKerClosed (k + 1) z)
      = (z / (z + 1)) * ((z + 1) ^ (k + 1) * hKerClosed (k + 1) z) := by
    field_simp
    ring
  have hr0 : 0 ≤ z / (z + 1) := div_nonneg hz (le_of_lt hzp)
  have hr1 : z / (z + 1) ≤ 1 := by
    rw [div_le_one hzp]
    linarith
  have hA : |z * ((z + 1) ^ k * hKerClosed (k + 1) z)|
      ≤ ((k + 1).factorial : ℝ) * ((k + 2 : ℕ) : ℝ) := by
    rw [hpow, abs_mul, abs_of_nonneg hr0]
    have hbase := hpz (k + 1) z hz
    have hcast : (((k + 1 : ℕ) : ℝ) + 1) = ((k + 2 : ℕ) : ℝ) := by
      push_cast
      ring
    calc (z / (z + 1)) * |(z + 1) ^ (k + 1) * hKerClosed (k + 1) z|
        ≤ 1 * (((k + 1).factorial : ℝ) * (((k + 1 : ℕ) : ℝ) + 1)) :=
          mul_le_mul hr1 hbase (abs_nonneg _) zero_le_one
      _ = ((k + 1).factorial : ℝ) * ((k + 2 : ℕ) : ℝ) := by rw [one_mul, hcast]
  -- The `k·h^{(k)}` term.
  have hB : |(k : ℝ) * ((z + 1) ^ k * hKerClosed k z)|
      ≤ (k : ℝ) * ((k.factorial : ℝ) * (k + 1)) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact mul_le_mul_of_nonneg_left (hpz k z hz) (Nat.cast_nonneg k)
  have hsplit : (z + 1) ^ k * (2 * (z * hKerClosed (k + 1) z + (k : ℝ) * hKerClosed k z))
      = 2 * (z * ((z + 1) ^ k * hKerClosed (k + 1) z)
        + (k : ℝ) * ((z + 1) ^ k * hKerClosed k z)) := by
    ring
  rw [hsplit]
  rw [abs_mul, abs_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2)]
  calc 2 * |z * ((z + 1) ^ k * hKerClosed (k + 1) z)
        + (k : ℝ) * ((z + 1) ^ k * hKerClosed k z)|
      ≤ 2 * (|z * ((z + 1) ^ k * hKerClosed (k + 1) z)|
        + |(k : ℝ) * ((z + 1) ^ k * hKerClosed k z)|) := by
        have h := abs_add_le (z * ((z + 1) ^ k * hKerClosed (k + 1) z))
          ((k : ℝ) * ((z + 1) ^ k * hKerClosed k z))
        linarith
    _ ≤ 2 * (((k + 1).factorial : ℝ) * ((k + 2 : ℕ) : ℝ)
        + (k : ℝ) * ((k.factorial : ℝ) * (k + 1))) := by
        linarith
    _ = Work.FTS.Nonlinear.FstarPkg.HB k := by
        rw [Work.FTS.Nonlinear.FstarPkg.HB]
        push_cast
        ring

end Work.FTS.Nonlinear.FstarPkg
