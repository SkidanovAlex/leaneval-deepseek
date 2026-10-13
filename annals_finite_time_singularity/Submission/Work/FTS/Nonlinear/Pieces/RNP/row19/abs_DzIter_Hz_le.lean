/-
# Row 19 of the N4 table — the weighted `D_z`-bound for the radial factor `Hz`

The radial factor of `D_zF_*` is `Hz z = 2z(1-z)/(1+z)³`
(`Work.FTS.Nonlinear.FstarPkg.Hz`), a rational function whose only pole is at `z = -1`.  In
the decomposition `V·D_zF_* = (V/z)·(z·D_zF_*)` of row 19 (`row19aux.Vs_mul_Gs_eq`) the
profile `z·D_zF_* = α·Γ(θ)/c · 2z²(1-z)/(1+z)³` is explicit, but the coefficient `V/z`
carries `D_z`-derivatives of a general factor, so the estimate also needs the *weighted*
`D_z`-iterates of the radial profile itself.

This file proves the pointwise bound

  `|D_z^m (fun z _ => Hz z) z θ| ≤ C · z/(1+z)²`  for `m ≤ 4`, `z ≥ 0`,

with a universal `C`.  Note that the weight `z/(1+z)²` is exactly the profile scale of
`F_*` (`= z/(1+z)²` up to a factor `2`): the bound is *not* uniform on `[0,∞)` — it vanishes
like `z` at the origin and decays like `1/z` at infinity, matching the behaviour of
`D_z^m Hz` at both ends.

## The route

* `DzIter_eq_sum_scoef_smooth` (the genuine `C^∞`-order Stirling expansion
  `D_z^m = ∑_{k≤m} S(m,k) z^k ∂_z^k`, `Work.FTS.H2.WPQ`) reduces the estimate to the
  *weighted* plain derivative bounds `|z^k ∂_z^k Hz z| ≤ C_k z/(1+z)²`, `k ≤ m`; the `θ`
  variable is a dummy (`pzIter_Hz_eq`), so the statement is genuinely one-dimensional;
* the weighted derivative bounds are `row19.abs_zpow_deriv_Hz_le`, proved separately from the
  closed form of `deriv^[k] Hz` (it is the only analytic input of this file);
* the Stirling coefficients are summed with `Work.Spaces.abs_sum_scoef_mul_le`, whose total
  mass is the Bell number `bell m ≤ 15` for `m ≤ 4` (`Work.FTS.H2.WPQ.bell_le_15`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.Nonlinear.FstarPkg.DzHzDefs
import Submission.Work.FTS.Nonlinear.FstarPkg.Hz_deriv_bound
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.Spaces.pzIter_hKer_bound
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row19.abs_zpow_deriv_Hz_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.row19

set_option autoImplicit false

/-- The `θ`-variable is a dummy in `fun z _ => Hz z`: the iterated plain `z`-derivative of the
`θ`-slice is the iterated derivative of the one-variable function `Hz`. -/
theorem pzIter_Hz_eq (n : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter n (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ
      = deriv^[n] Work.FTS.Nonlinear.FstarPkg.Hz z := by
  induction n generalizing z with
  | zero => rfl
  | succ k ih =>
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pz]
    rw [show (fun z' => Work.Spaces.pzIter k (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z' θ)
        = deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz from funext (fun z' => ih z')]
    exact congrFun (Function.iterate_succ_apply' deriv k Work.FTS.Nonlinear.FstarPkg.Hz).symm z

/-- The radial factor `Hz = 2z(1-z)/(1+z)³` is `C^∞` on `(-1,∞)` (its only pole is `z = -1`).
This is the smoothness hypothesis of the Stirling expansion
`Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth`. -/
theorem contDiffOn_Hz :
    ContDiffOn ℝ Work.Stability.smoothOrder Work.FTS.Nonlinear.FstarPkg.Hz (Set.Ioi (-1)) := by
  have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => 2 * z * (1 - z)) (Set.Ioi (-1)) := by fun_prop
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => (1 + z) ^ 3) (Set.Ioi (-1)) := by fun_prop
  exact h1.div h2 (fun x hx => by
    have hx' : -1 < x := hx
    have : 0 < 1 + x := by linarith
    positivity)

/-- **The Stirling expansion of `D_z^m` on the radial factor.**  For `z > -1` and every `m`,
`D_z^m (fun z _ => Hz z) = ∑_{k≤m} S(m,k) z^k ∂_z^k Hz`, the `θ`-variable being a dummy. -/
theorem DzIter_Hz_eq_sum (m : ℕ) (z θ : ℝ) (hz : z ∈ Set.Ioi (-1)) :
    Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ
      = ∑ k ∈ Finset.range (m + 1), (Work.Spaces.scoef m k : ℝ) *
          (z ^ k * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z) := by
  have hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z => (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ) (Set.Ioi (-1)) :=
    contDiffOn_Hz
  rw [Work.FTS.H2.WPQ.DzIter_eq_sum_scoef_smooth
    (h := fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) (θ := θ) hsmooth m z hz]
  exact Finset.sum_congr rfl fun k _ => by rw [pzIter_Hz_eq]

/-- **The weighted `D_z`-bounds of the radial factor `Hz`.**  There is a universal constant `C`
with
`|D_z^m (fun z _ => Hz z) z θ| ≤ C · z/(1+z)²` for every `m ≤ 4`, every `z ≥ 0` and every
angle `θ`. -/
theorem abs_DzIter_Hz_le : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 ≤ z → ∀ θ : ℝ,
    |Work.Spaces.DzIter m (fun z _ => Work.FTS.Nonlinear.FstarPkg.Hz z) z θ|
      ≤ C * (z / (1 + z) ^ 2) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := abs_zpow_deriv_Hz_le
  refine ⟨100 * C₀ + 1, by linarith, ?_⟩
  intro m hm z hz θ
  have hz' : z ∈ Set.Ioi (-1) := by
    simp only [Set.mem_Ioi]; linarith
  have hw : 0 ≤ z / (1 + z) ^ 2 := div_nonneg hz (by positivity)
  have hMnn : 0 ≤ C₀ * (z / (1 + z) ^ 2) := mul_nonneg hC₀pos.le hw
  rw [DzIter_Hz_eq_sum m z θ hz']
  have hsum := Work.Spaces.abs_sum_scoef_mul_le m (C₀ * (z / (1 + z) ^ 2))
    (fun k => z ^ k * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z)
    (fun k hk => hC₀ k (le_trans hk hm) z hz)
  have hbell : (Work.Spaces.bell m : ℝ) ≤ 15 := by
    exact_mod_cast Work.FTS.H2.WPQ.bell_le_15 m hm
  calc |∑ k ∈ Finset.range (m + 1), (Work.Spaces.scoef m k : ℝ) *
        (z ^ k * deriv^[k] Work.FTS.Nonlinear.FstarPkg.Hz z)|
      ≤ (Work.Spaces.bell m : ℝ) * (C₀ * (z / (1 + z) ^ 2)) := hsum
    _ ≤ 15 * (C₀ * (z / (1 + z) ^ 2)) := mul_le_mul_of_nonneg_right hbell hMnn
    _ ≤ (100 * C₀ + 1) * (z / (1 + z) ^ 2) := by
        have h15 : (15 : ℝ) * C₀ ≤ 100 * C₀ + 1 := by nlinarith
        calc (15 : ℝ) * (C₀ * (z / (1 + z) ^ 2))
            = (15 * C₀) * (z / (1 + z) ^ 2) := by ring
          _ ≤ (100 * C₀ + 1) * (z / (1 + z) ^ 2) :=
              mul_le_mul_of_nonneg_right h15 hw

end Work.FTS.Nonlinear.Pieces.RNP.row19
