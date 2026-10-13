import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs
import Submission.Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound
import Submission.Work.Spaces.pzIter_hKer_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

open scoped Topology

/-! ## Elementary ingredients

`Hz z = 2z(1-z)/(1+z)³` is the radial factor of `D_z F_*`.  The route to the weighted bound
`|z^n Hz^{(n)}(z)| ≤ C·z/(1+z)²` is the closed form for the iterated derivatives
(`iter_deriv_Hz`) together with the weighted bound for the closed form `hKerClosed` of the
derivatives of `h(z) = z/(1+z)²` (`zpow_hKerClosed_le`). -/

/-- The absolute value of the closed form `hKerClosed k z = (-1)^k k! (z-k)(1+z)^{-(k+2)}`. -/
private lemma abs_hKerClosed (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |Work.Spaces.hKerClosed k z|
      = (k.factorial : ℝ) * |z - (k : ℝ)| * ((1 + z)⁻¹) ^ (k + 2) := by
  have h1 : (0:ℝ) < 1 + z := by linarith
  unfold Work.Spaces.hKerClosed
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k.factorial:ℝ)),
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (le_of_lt h1)) _), abs_pow]
  norm_num
  ring

/-- The elementary inequality `|z^k (z-k)| ≤ (k+1) z (1+z)^k` for `z ≥ 0`. -/
private lemma zpow_mul_sub_le (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * (z - (k : ℝ))| ≤ ((k : ℝ) + 1) * z * (1 + z) ^ k := by
  have hsub : |z - (k : ℝ)| ≤ z + (k : ℝ) := by
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  rcases k with _ | k
  · simp only [Nat.cast_zero, sub_zero, pow_zero, mul_one, zero_add, one_mul]
    rw [abs_of_nonneg hz]
  · push_cast at hsub ⊢
    have hz1 : (0:ℝ) ≤ 1 + z := by linarith
    have hstep : z ^ k ≤ (1+z)^k := pow_le_pow_left₀ hz (by linarith) k
    have hb : z + ((k:ℝ)+1) ≤ ((k:ℝ)+2) * (1+z) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k, hz]
    have hstep2 : z^k * (z + ((k:ℝ)+1)) ≤ (1+z)^k * (((k:ℝ)+2) * (1+z)) := by
      calc z^k * (z + ((k:ℝ)+1)) ≤ (1+z)^k * (z + ((k:ℝ)+1)) :=
            mul_le_mul_of_nonneg_right hstep (by linarith [Nat.cast_nonneg (α := ℝ) k])
        _ ≤ (1+z)^k * (((k:ℝ)+2) * (1+z)) := mul_le_mul_of_nonneg_left hb (pow_nonneg hz1 k)
    calc |z ^ (k + 1) * (z - ((k:ℝ)+1))|
        = z * (z ^ k * |z - ((k:ℝ)+1)|) := by
            rw [abs_mul, abs_of_nonneg (pow_nonneg hz _), pow_succ]; ring
      _ ≤ z * (z ^ k * (z + ((k:ℝ)+1))) := by
            refine mul_le_mul_of_nonneg_left ?_ hz
            exact mul_le_mul_of_nonneg_left hsub (pow_nonneg hz k)
      _ ≤ z * ((1+z)^k * (((k:ℝ)+2) * (1+z))) := mul_le_mul_of_nonneg_left hstep2 hz
      _ = ((k:ℝ) + 1 + 1) * z * (1 + z) ^ (k+1) := by rw [pow_succ]; ring

/-- The weighted bound `|z^k h^{(k)}(z)| ≤ k!(k+1)·z/(1+z)²` for the profile
`h = hKer` (`Work.Spaces.hKerClosed` is its closed-form `k`-th derivative), `z ≥ 0`. -/
private lemma zpow_hKerClosed_le (k : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    |z ^ k * Work.Spaces.hKerClosed k z|
      ≤ (k.factorial : ℝ) * ((k : ℝ) + 1) * (z * ((1 + z)⁻¹) ^ 2) := by
  have h1z : (0:ℝ) < 1 + z := by linarith
  have hne : (1 + z) ≠ 0 := ne_of_gt h1z
  have hpow : (1 + z)^k * ((1 + z)⁻¹)^(k + 2) = ((1 + z)⁻¹)^2 := by
    rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_mul]
  have hstep : z ^ k * |z - (k : ℝ)| ≤ ((k : ℝ) + 1) * z * (1 + z)^k := by
    have := zpow_mul_sub_le k hz
    rwa [abs_mul, abs_of_nonneg (pow_nonneg hz k)] at this
  have hsub : |z ^ k * Work.Spaces.hKerClosed k z|
      = (k.factorial : ℝ) * (z ^ k * |z - (k : ℝ)|) * ((1 + z)⁻¹)^(k + 2) := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hz k), abs_hKerClosed k hz]
    ring
  rw [hsub]
  have hnn : (0:ℝ) ≤ ((1 + z)⁻¹)^(k + 2) :=
    pow_nonneg (inv_nonneg.mpr (le_of_lt h1z)) _
  have hk : (0:ℝ) ≤ (k.factorial : ℝ) := by positivity
  calc (k.factorial : ℝ) * (z ^ k * |z - (k : ℝ)|) * ((1 + z)⁻¹)^(k + 2)
      ≤ (k.factorial : ℝ) * (((k : ℝ) + 1) * z * (1 + z)^k) * ((1 + z)⁻¹)^(k + 2) := by
        gcongr
    _ = (k.factorial : ℝ) * ((k : ℝ) + 1) * (z * ((1 + z)⁻¹)^2) := by
        rw [← hpow]; ring

/-- The closed form of the iterated derivatives of `Hz = 2·id·h'` (Leibniz, since
`(id)'' = 0`): `Hz^{(n)}(y) = 2·(y·h^{(n+1)}(y) + n·h^{(n)}(y))` for `y > -1`. -/
private lemma iter_deriv_Hz (n : ℕ) {z : ℝ} (hz : -1 < z) :
    deriv^[n] Work.FTS.Nonlinear.FstarPkg.Hz z
      = 2 * (z * Work.Spaces.hKerClosed (n + 1) z
             + (n : ℝ) * Work.Spaces.hKerClosed n z) := by
  have hmain : ∀ m : ℕ, ∀ y : ℝ, -1 < y →
      deriv^[m] Work.FTS.Nonlinear.FstarPkg.Hz y
        = 2 * (y * Work.Spaces.hKerClosed (m + 1) y
               + (m : ℝ) * Work.Spaces.hKerClosed m y) := by
    intro m
    induction m with
    | zero =>
      intro y hy
      simp only [Function.iterate_zero_apply]
      have h1 : deriv Work.Spaces.hKer y = Work.Spaces.hKerClosed 1 y := by
        show deriv (fun y : ℝ => y / (1 + y) ^ 2) y = Work.Spaces.hKerClosed 1 y
        exact Work.Spaces.iter_deriv_hKerClosed 1 y hy
      rw [Work.FTS.Nonlinear.FstarPkg.Hz_eq_mul_deriv hy, h1]
      simp
    | succ m ih =>
      intro y hy
      rw [Function.iterate_succ_apply']
      have hev : deriv^[m] Work.FTS.Nonlinear.FstarPkg.Hz =ᶠ[𝓝 y]
          (fun t : ℝ => 2 * (t * Work.Spaces.hKerClosed (m + 1) t
            + (m : ℝ) * Work.Spaces.hKerClosed m t)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
        exact ih t ht
      rw [hev.deriv_eq]
      have hyne : y ≠ -1 := by linarith
      have hd1 : HasDerivAt (fun t : ℝ => t * Work.Spaces.hKerClosed (m + 1) t)
          (1 * Work.Spaces.hKerClosed (m + 1) y + y * Work.Spaces.hKerClosed ((m + 1) + 1) y) y :=
        (hasDerivAt_id y).mul (Work.Spaces.hasDerivAt_hKerClosed (m + 1) hyne)
      have hd2 : HasDerivAt (fun t : ℝ => (m : ℝ) * Work.Spaces.hKerClosed m t)
          ((m : ℝ) * Work.Spaces.hKerClosed (m + 1) y) y :=
        (Work.Spaces.hasDerivAt_hKerClosed m hyne).const_mul (m : ℝ)
      have hd : HasDerivAt
          (fun t : ℝ => 2 * (t * Work.Spaces.hKerClosed (m + 1) t
            + (m : ℝ) * Work.Spaces.hKerClosed m t))
          (2 * (1 * Work.Spaces.hKerClosed (m + 1) y + y * Work.Spaces.hKerClosed ((m + 1) + 1) y
            + (m : ℝ) * Work.Spaces.hKerClosed (m + 1) y)) y :=
        (hd1.add hd2).const_mul 2
      rw [hd.deriv]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
  exact hmain n z hz

/-- The weighted `z`-derivative bounds of the radial factor `Hz z = 2z(1-z)/(1+z)^3` of `D_z F_*`: for every order `n ≤ 4` and every `z ≥ 0`, `|z^n · Hz^{(n)}(z)| ≤ C · z/(1+z)^2`, with `C` universal. Reviewers computed the ratios `|z^n Hz^{(n)}(z)|(1+z)^2/z` in closed form as `2|z−1|/(z+1)`, `2|z²−4z+1|/(z+1)²`, `4z|z²−7z+4|/(1+z)³`, `12z²|z²−10z+9|/(1+z)⁴`, `48z³|z²−13z+16|/(1+z)⁵` for `n = 0..4`, all bounded on `[0,∞)`; `C = 100` is safe. Route hint: `Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound` derives inside its proof the closed form `deriv^[n] Hz y = 2*(y*hKerClosed (n+1) y + n*hKerClosed n y)` on `(-1,∞)` (with `Work.Spaces.hKerClosed k z = (-1)^k k! (z-k) (1+z)^{-(k+2)}`, `Work.Spaces.hasDerivAt_hKerClosed`, `Work.Spaces.iter_deriv_hKerClosed`), from which `z^n deriv^[n] Hz z = 2*z^n*(1+z)^{-(n+3)}*P n z` with the explicit quadratic `P n z = (-1)^(n+1)*(n+1)!*z*(z-n-1) + n*(-1)^n*n!*(z-n)*(1+z)`. (Namespace: `Work.FTS.Nonlinear.Pieces.RNP.row19`.) -/
theorem abs_zpow_deriv_Hz_le : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≤ 4 → ∀ z : ℝ, 0 ≤ z →
    |z ^ n * deriv^[n] Work.FTS.Nonlinear.FstarPkg.Hz z|
      ≤ C * (z / (1 + z) ^ 2) := by
  refine ⟨10000, by norm_num, fun n hn z hz => ?_⟩
  have hz1 : -1 < z := by linarith
  have hZnn : 0 ≤ z * ((1 + z)⁻¹)^2 := mul_nonneg hz (sq_nonneg _)
  rw [iter_deriv_Hz n hz1]
  have hsplit : z ^ n * (2 * (z * Work.Spaces.hKerClosed (n + 1) z
        + (n : ℝ) * Work.Spaces.hKerClosed n z))
      = 2 * (z ^ (n+1) * Work.Spaces.hKerClosed (n+1) z
        + (n:ℝ) * (z^n * Work.Spaces.hKerClosed n z)) := by
    rw [pow_succ]; ring
  rw [hsplit, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have hA : |z ^ (n+1) * Work.Spaces.hKerClosed (n+1) z|
      ≤ ((n+1).factorial : ℝ) * ((((n+1:ℕ):ℝ)) + 1) * (z * ((1+z)⁻¹)^2) :=
    zpow_hKerClosed_le (n+1) hz
  have hB : |(n:ℝ) * (z^n * Work.Spaces.hKerClosed n z)|
      ≤ (n:ℝ) * ((n.factorial : ℝ) * ((n:ℝ) + 1) * (z * ((1+z)⁻¹)^2)) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    exact mul_le_mul_of_nonneg_left (zpow_hKerClosed_le n hz) (Nat.cast_nonneg n)
  -- the numerical constant, for `n ≤ 4`
  have hnum : 2 * (((n+1).factorial : ℝ) * ((((n+1:ℕ):ℝ)) + 1)
      + (n:ℝ) * ((n.factorial : ℝ) * ((n:ℝ) + 1))) ≤ 10000 := by
    interval_cases n <;> norm_num
  have hconv : z * ((1+z)⁻¹)^2 = z / (1+z)^2 := by rw [div_eq_mul_inv, inv_pow]
  have hmain : 2 * |z ^ (n+1) * Work.Spaces.hKerClosed (n+1) z
        + (n:ℝ) * (z^n * Work.Spaces.hKerClosed n z)|
      ≤ 10000 * (z * ((1+z)⁻¹)^2) := by
    have h1 : |z ^ (n+1) * Work.Spaces.hKerClosed (n+1) z
        + (n:ℝ) * (z^n * Work.Spaces.hKerClosed n z)| ≤
        ((n+1).factorial : ℝ) * ((((n+1:ℕ):ℝ)) + 1) * (z * ((1+z)⁻¹)^2)
          + (n:ℝ) * ((n.factorial : ℝ) * ((n:ℝ) + 1) * (z * ((1+z)⁻¹)^2)) :=
      le_trans (abs_add_le _ _) (add_le_add hA hB)
    nlinarith [h1, hnum, hZnn]
  rw [hconv] at hmain
  exact hmain

end Work.FTS.Nonlinear.Pieces.RNP.row19
