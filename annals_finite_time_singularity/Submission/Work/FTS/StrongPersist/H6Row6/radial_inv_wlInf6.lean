import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Nonlinear.FstarPkg.c2mInv_points

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `c/(1+z) ∈ 𝒲^{6,∞}`

The radial profile `z ↦ c/(1+z)` (a pure function of `z`, with no angular dependence)
belongs to `𝒲^{6,∞}` for every constant `c` and every exponent `α`; indeed the weight
`(1+z)^k` exactly cancels all but one power of `(1+z)` in the `k`-th `z`-derivative:

  `∂_z^k (c/(1+z)) = (-1)^k k! c (1+z)^{-(k+1)}`,  hence
  `|(1+z)^k ∂_z^k (c/(1+z))| ≤ k! |c|`.

The angular half of `WlInfMem` is trivial: the function does not depend on `θ`, so
`D_θ^j (c/(1+z)) = 0` for every `j ≥ 1` and each of the mixed suprema is that of the
zero function.

The closed form of `∂_z^k (1+z)^{-1}` is reused from
`Work.FTS.Nonlinear.FstarPkg` (`nInvClosed`, `iter_deriv_nInvClosed`,
`nInvClosed_weighted`), where it was developed for the profile `c2m(θ)·2α/(1+z)`.
-/

namespace Work.FTS.StrongPersist.H6Row6

/-- The `k`-th plain `z`-derivative of `z ↦ c/(1+z)` in closed form, for `z > -1`:
`(−1)^k k! c (1+z)^{−(k+1)}`, written through `FstarPkg.nInvClosed`. -/
private lemma pzIter_radialInv (c : ℝ) (k : ℕ) (z θ : ℝ) (hz : -1 < z) :
    Work.Spaces.pzIter k (fun z θ : ℝ => c / (1 + z)) z θ
      = c * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z := by
  have hfun : (fun z θ : ℝ => c / (1 + z))
      = (fun z θ : ℝ => (fun _ : ℝ => c) θ * (fun z : ℝ => (1 + z)⁻¹) z) := by
    funext z θ
    simp [div_eq_mul_inv]
  rw [hfun]
  rw [Work.Spaces.pzIter_decomp]
  rw [Work.FTS.Nonlinear.FstarPkg.iter_deriv_nInvClosed k z hz]

/-- The weighted `z`-bound: `|(1+z)^k ∂_z^k (c/(1+z))| ≤ k! · |c|` on the half-line `z ≥ 0`. -/
private lemma radialInv_z_bound (c : ℝ) (k : ℕ) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz) :
    |(z + 1) ^ k * Work.Spaces.pzIter k (fun z θ : ℝ => c / (1 + z)) z θ|
      ≤ |c| * (k.factorial : ℝ) := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : -1 < z := by linarith
  rw [pzIter_radialInv c k z θ hz1]
  rw [show (z + 1) ^ k * (c * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z)
      = c * ((z + 1) ^ k * Work.FTS.Nonlinear.FstarPkg.nInvClosed k z) by ring]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (Work.FTS.Nonlinear.FstarPkg.nInvClosed_weighted k z hz0) (abs_nonneg c)

/-- Every `z`-iterate of the zero function is the zero function. -/
private lemma pzIter_zero_fun (k : ℕ) :
    Work.Spaces.pzIter k (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => (0 : ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.pz]

/-- The angular content of `z ↦ c/(1+z)` is empty: `D_θ^j (c/(1+z)) = 0` for every `j ≥ 1`. -/
private lemma DthIter_radial_eq_zero (c : ℝ) : ∀ j : ℕ, 1 ≤ j →
    Work.Spaces.DthIter j (fun z θ : ℝ => c / (1 + z)) = fun _ _ => (0 : ℝ) := by
  intro j
  induction j with
  | zero => intro hj; exact absurd hj (by omega)
  | succ j ih =>
    intro hj
    cases j with
    | zero =>
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]
    | succ j =>
      have hih : Work.Spaces.DthIter (j + 1) (fun z θ : ℝ => c / (1 + z))
          = fun _ _ => (0 : ℝ) := ih (by omega)
      rw [Work.Spaces.DthIter_succ, hih]
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]

theorem radial_inv_wlInf6 (c : ℝ) : ∀ α : ℝ, 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 6 (fun z θ : ℝ => c / (1 + z)) := by
  intro α hα hα1
  constructor
  · intro k hk
    refine ⟨|c| * (k.factorial : ℝ), ?_⟩
    rintro y ⟨z, hz, θ, hθ, rfl⟩
    exact radialInv_z_bound c k z θ hz
  · intro j hj k hk hj1 hjk
    refine ⟨0, ?_⟩
    rintro y ⟨z, hz, θ, hθ, rfl⟩
    have hzero : (z + 1) ^ k * Work.Spaces.pzIter k
        (Work.Spaces.DthIter j (fun z θ : ℝ => c / (1 + z))) z θ
        * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) = 0 := by
      rw [DthIter_radial_eq_zero c j hj1, pzIter_zero_fun]
      simp
    have hbeta : (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ : ℝ => c / (1 + z))) z θ
          * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) z θ
        = (z + 1) ^ k * Work.Spaces.pzIter k
          (Work.Spaces.DthIter j (fun z θ : ℝ => c / (1 + z))) z θ
          * Real.sin (2 * θ) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) := rfl
    rw [hbeta, hzero, abs_zero]

end Work.FTS.StrongPersist.H6Row6
