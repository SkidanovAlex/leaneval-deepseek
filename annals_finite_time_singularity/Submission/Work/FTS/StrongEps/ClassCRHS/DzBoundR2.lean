/-
Copyright: work module for the Elgindi finite-time singularity project.

# `D_z`-bounds for the third radial profile `SR2`

For `SR2 z = 2 z² (1-z)/(1+z)⁴` we prove the bound
`|DzdIter i SR2 z| ≤ C z²/(1+z)³` for `i ≤ 4` and `z ≥ 0`, with an explicit universal
constant (`C = 30000`).

The proof uses the substitution `x = z/(1+z)`, under which `D_z = z ∂_z` becomes the
operator `x(1-x) ∂_x`:

* `SR2 z = polyR2 0 (z/(1+z))` with `polyR2 0 x = 2x²(1-x)(1-2x)`;
* `DzdIter i SR2 z = polyR2 i (z/(1+z))` for `i ≤ 4`, where
  `polyR2 (i+1) x = x(1-x)·(D polyR2 i) x` (`D` the ordinary derivative);
* each `polyR2 i` factors as `x²(1-x)·AR2 i x` and `|AR2 i x| ≤ 30000` on `[0,1]`;
* finally `x²(1-x) = z²/(1+z)³` when `x = z/(1+z)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAux
import Submission.Work.Elliptic.L12Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real

namespace Work.FTS.StrongEps.ClassCRHS

set_option autoImplicit false

/-- The substitution `x = z/(1+z)` transporting `D_z = z ∂_z` into `x(1-x) ∂_x`. -/
def xtR2 (z : ℝ) : ℝ := z / (1 + z)

/-- The `i`-th `D_z`-iterate of `SR2` in the variable `x = z/(1+z)`: the `i`-fold
application of `x(1-x) ∂_x` to `2x²(1-x)(1-2x)`. -/
def polyR2 : ℕ → ℝ → ℝ
  | 0 => fun x => 2 * x ^ 2 - 6 * x ^ 3 + 4 * x ^ 4
  | 1 => fun x => 4 * x ^ 2 - 22 * x ^ 3 + 34 * x ^ 4 - 16 * x ^ 5
  | 2 => fun x => 8 * x ^ 2 - 74 * x ^ 3 + 202 * x ^ 4 - 216 * x ^ 5 + 80 * x ^ 6
  | 3 => fun x => 16 * x ^ 2 - 238 * x ^ 3 + 1030 * x ^ 4 - 1888 * x ^ 5 + 1560 * x ^ 6
                - 480 * x ^ 7
  | 4 => fun x => 32 * x ^ 2 - 746 * x ^ 3 + 4834 * x ^ 4 - 13560 * x ^ 5 + 18800 * x ^ 6
                - 12720 * x ^ 7 + 3360 * x ^ 8
  | _ => fun _ => 0

/-- The ordinary derivative of `polyR2 k`, for `k ≤ 3`. -/
def dpolyR2 : ℕ → ℝ → ℝ
  | 0 => fun x => 4 * x - 18 * x ^ 2 + 16 * x ^ 3
  | 1 => fun x => 8 * x - 66 * x ^ 2 + 136 * x ^ 3 - 80 * x ^ 4
  | 2 => fun x => 16 * x - 222 * x ^ 2 + 808 * x ^ 3 - 1080 * x ^ 4 + 480 * x ^ 5
  | 3 => fun x => 32 * x - 714 * x ^ 2 + 4120 * x ^ 3 - 9440 * x ^ 4 + 9360 * x ^ 5
                - 3360 * x ^ 6
  | _ => fun _ => 0

/-- The polynomial cofactor of `polyR2 i`: `polyR2 i x = x²(1-x)·AR2 i x`. -/
def AR2 : ℕ → ℝ → ℝ
  | 0 => fun x => 2 - 4 * x
  | 1 => fun x => 4 - 18 * x + 16 * x ^ 2
  | 2 => fun x => 8 - 66 * x + 136 * x ^ 2 - 80 * x ^ 3
  | 3 => fun x => 16 - 222 * x + 808 * x ^ 2 - 1080 * x ^ 3 + 480 * x ^ 4
  | 4 => fun x => 32 - 714 * x + 4120 * x ^ 2 - 9440 * x ^ 3 + 9360 * x ^ 4 - 3360 * x ^ 5
  | _ => fun _ => 0

/-- The explicit derivative of `polyR2 k` for `k ≤ 3`. -/
lemma hasDerivAt_polyR2 : ∀ k : ℕ, k ≤ 3 → ∀ x : ℝ,
    HasDerivAt (polyR2 k) (dpolyR2 k x) x := by
  intro k hk x
  interval_cases k
  · exact (by
      have h2 : HasDerivAt (fun y : ℝ => 2 * y ^ 2 - 6 * y ^ 3 + 4 * y ^ 4)
          (4 * x - 18 * x ^ 2 + 16 * x ^ 3) x := by
        have hc := (((hasDerivAt_pow 2 x).const_mul 2).sub
          ((hasDerivAt_pow 3 x).const_mul 6)).add ((hasDerivAt_pow 4 x).const_mul 4)
        convert hc using 1
        norm_num
        ring
      exact h2)
  · exact (by
      have h2 : HasDerivAt (fun y : ℝ => 4 * y ^ 2 - 22 * y ^ 3 + 34 * y ^ 4 - 16 * y ^ 5)
          (8 * x - 66 * x ^ 2 + 136 * x ^ 3 - 80 * x ^ 4) x := by
        have hc := ((((hasDerivAt_pow 2 x).const_mul 4).sub
          ((hasDerivAt_pow 3 x).const_mul 22)).add
          ((hasDerivAt_pow 4 x).const_mul 34)).sub ((hasDerivAt_pow 5 x).const_mul 16)
        convert hc using 1
        norm_num
        ring
      exact h2)
  · exact (by
      have h2 : HasDerivAt
          (fun y : ℝ => 8 * y ^ 2 - 74 * y ^ 3 + 202 * y ^ 4 - 216 * y ^ 5 + 80 * y ^ 6)
          (16 * x - 222 * x ^ 2 + 808 * x ^ 3 - 1080 * x ^ 4 + 480 * x ^ 5) x := by
        have hc := (((((hasDerivAt_pow 2 x).const_mul 8).sub
          ((hasDerivAt_pow 3 x).const_mul 74)).add
          ((hasDerivAt_pow 4 x).const_mul 202)).sub
          ((hasDerivAt_pow 5 x).const_mul 216)).add ((hasDerivAt_pow 6 x).const_mul 80)
        convert hc using 1
        norm_num
        ring
      exact h2)
  · exact (by
      have h2 : HasDerivAt
          (fun y : ℝ => 16 * y ^ 2 - 238 * y ^ 3 + 1030 * y ^ 4 - 1888 * y ^ 5
            + 1560 * y ^ 6 - 480 * y ^ 7)
          (32 * x - 714 * x ^ 2 + 4120 * x ^ 3 - 9440 * x ^ 4 + 9360 * x ^ 5
            - 3360 * x ^ 6) x := by
        have hc := ((((((hasDerivAt_pow 2 x).const_mul 16).sub
          ((hasDerivAt_pow 3 x).const_mul 238)).add
          ((hasDerivAt_pow 4 x).const_mul 1030)).sub
          ((hasDerivAt_pow 5 x).const_mul 1888)).add
          ((hasDerivAt_pow 6 x).const_mul 1560)).sub ((hasDerivAt_pow 7 x).const_mul 480)
        convert hc using 1
        norm_num
        ring
      exact h2)

/-- The recursion `polyR2 (k+1) x = x(1-x)·(polyR2 k)' x`, for `k ≤ 3`. -/
lemma step_polyR2 : ∀ k : ℕ, k ≤ 3 → ∀ x : ℝ,
    x * (1 - x) * dpolyR2 k x = polyR2 (k + 1) x := by
  intro k hk x
  interval_cases k <;> (simp only [dpolyR2, polyR2]; ring)

/-- `polyR2 i` is `x²(1-x)` times the polynomial `AR2 i`. -/
lemma factor_polyR2 : ∀ i : ℕ, i ≤ 4 → ∀ x : ℝ,
    polyR2 i x = x ^ 2 * (1 - x) * AR2 i x := by
  intro i hi x
  interval_cases i <;> (simp only [polyR2, AR2]; ring)

/-- The cofactors `AR2 i`, `i ≤ 4`, are bounded by `30000` on `[0,1]` (their coefficient
`ℓ¹`-norms are `6, 38, 290, 2606, 27026`). -/
lemma cof_bound : ∀ i : ℕ, i ≤ 4 → ∀ x : ℝ, 0 ≤ x → x ≤ 1 → |AR2 i x| ≤ 30000 := by
  intro i hi x hx0 hx1
  interval_cases i
  all_goals
    simp only [AR2]
    refine abs_le.mpr ⟨?_, ?_⟩ <;>
      nlinarith [hx0, hx1, pow_le_one₀ (n := 2) hx0 hx1, pow_le_one₀ (n := 3) hx0 hx1,
        pow_le_one₀ (n := 4) hx0 hx1, pow_le_one₀ (n := 5) hx0 hx1,
        pow_nonneg hx0 2, pow_nonneg hx0 3, pow_nonneg hx0 4, pow_nonneg hx0 5]

/-- `x ↦ z/(1+z)` has derivative `1/(1+z)²` at `z ≠ -1`. -/
lemma hasDerivAt_xtR2 (z : ℝ) (hz : 1 + z ≠ 0) :
    HasDerivAt xtR2 (1 / (1 + z) ^ 2) z := by
  have hden : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
    convert ((hasDerivAt_const z (1 : ℝ)).add (hasDerivAt_id z)) using 1
    · funext w; simp
    · simp
  have h2 : HasDerivAt (fun w : ℝ => w / (1 + w)) (1 / (1 + z) ^ 2) z := by
    have h := (hasDerivAt_id z).div hden (by simpa using hz)
    convert h using 1
    · funext w
      simp [Pi.div_apply]
    · simp only [id_eq]
      field_simp
      ring
  exact h2

/-- `z·(1+z)^{-2} = x(1-x)` for `x = z/(1+z)`. -/
lemma mul_xtR2 (z : ℝ) (hz : 1 + z ≠ 0) : z * (1 / (1 + z) ^ 2) = xtR2 z * (1 - xtR2 z) := by
  simp only [xtR2]
  field_simp
  ring

/-- `x²(1-x) = z²/(1+z)³` for `x = z/(1+z)`. -/
lemma sq_xtR2 (z : ℝ) (hz : 1 + z ≠ 0) : (xtR2 z) ^ 2 * (1 - xtR2 z) = z ^ 2 / (1 + z) ^ 3 := by
  simp only [xtR2]
  field_simp
  ring

/-- `SR2` in the variable `x = z/(1+z)`. -/
lemma SR2_eq_polyR2 (z : ℝ) (hz : 1 + z ≠ 0) : SR2 z = polyR2 0 (xtR2 z) := by
  simp only [SR2, xtR2, polyR2]
  field_simp
  ring

/-- The `D_z`-iterates of `SR2`, expressed through the substitution `x = z/(1+z)`. -/
lemma DzdIter_SR2_eq (i : ℕ) (hi : i ≤ 4) : ∀ z : ℝ, 1 + z ≠ 0 →
    Work.Elliptic.DzdIter i SR2 z = polyR2 i (xtR2 z) := by
  induction i with
  | zero =>
      intro z hz
      simpa only [Work.Elliptic.DzdIter_zero, polyR2] using SR2_eq_polyR2 z hz
  | succ k ih =>
      intro z hz
      have hk4 : k ≤ 4 := le_trans (Nat.le_succ k) hi
      have hk3 : k ≤ 3 := by omega
      have hev : Work.Elliptic.DzdIter k SR2 =ᶠ[nhds z] fun w => polyR2 k (xtR2 w) := by
        filter_upwards [eventually_ne_nhds (show z ≠ -1 by intro h; exact hz (by linarith))]
          with w hw
        exact ih hk4 w (by intro h; exact hw (by linarith))
      have hcomp : deriv (fun w => polyR2 k (xtR2 w)) z
          = dpolyR2 k (xtR2 z) * (1 / (1 + z) ^ 2) := by
        have hX := hasDerivAt_xtR2 z hz
        have hp := hasDerivAt_polyR2 k hk3 (xtR2 z)
        exact (hp.comp z hX).deriv
      rw [show Work.Elliptic.DzdIter (k + 1) SR2 z
            = z * deriv (Work.Elliptic.DzdIter k SR2) z from rfl,
        hev.deriv_eq, hcomp]
      rw [show z * (dpolyR2 k (xtR2 z) * (1 / (1 + z) ^ 2))
            = xtR2 z * (1 - xtR2 z) * dpolyR2 k (xtR2 z) from by
          calc z * (dpolyR2 k (xtR2 z) * (1 / (1 + z) ^ 2))
              = (z * (1 / (1 + z) ^ 2)) * dpolyR2 k (xtR2 z) := by ring
            _ = (xtR2 z * (1 - xtR2 z)) * dpolyR2 k (xtR2 z) := by rw [mul_xtR2 z hz]]
      rw [step_polyR2 k hk3 (xtR2 z)]

/-- `|DzdIter i SR2 z| ≤ 30000 z²/(1+z)³` for `i ≤ 4` and `z ≥ 0`. -/
theorem DzdIter_SR2_bound (i : ℕ) (hi : i ≤ 4) (z : ℝ) (hz0 : 0 ≤ z) :
    |Work.Elliptic.DzdIter i SR2 z| ≤ 30000 * z ^ 2 / (1 + z) ^ 3 := by
  have hz : 1 + z ≠ 0 := by positivity
  rw [DzdIter_SR2_eq i hi z hz, factor_polyR2 i hi (xtR2 z)]
  have hx0 : 0 ≤ xtR2 z := by simp only [xtR2]; positivity
  have hx1 : xtR2 z ≤ 1 := by
    simp only [xtR2]
    rw [div_le_one (by linarith : (0 : ℝ) < 1 + z)]
    linarith
  have hnn : 0 ≤ (xtR2 z) ^ 2 * (1 - xtR2 z) := by
    nlinarith [sq_nonneg (xtR2 z), hx1]
  have hcof := cof_bound i hi (xtR2 z) hx0 hx1
  calc |(xtR2 z) ^ 2 * (1 - xtR2 z) * AR2 i (xtR2 z)|
      = (xtR2 z) ^ 2 * (1 - xtR2 z) * |AR2 i (xtR2 z)| := by
        rw [abs_mul, abs_of_nonneg hnn]
    _ ≤ (xtR2 z) ^ 2 * (1 - xtR2 z) * 30000 := mul_le_mul_of_nonneg_left hcof hnn
    _ = 30000 * z ^ 2 / (1 + z) ^ 3 := by rw [sq_xtR2 z hz]; ring

theorem DzBoundR2 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 4 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR2 z|
      ≤ C * z ^ 2 / (1 + z) ^ 3 := by
  exact ⟨30000, by norm_num, fun i hi z hz0 => DzdIter_SR2_bound i hi z hz0⟩

end Work.FTS.StrongEps.ClassCRHS
