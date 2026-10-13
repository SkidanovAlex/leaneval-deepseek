import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.WProductRule

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz.Aux

theorem abs_pzIter2_le_sqrt {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Work.Spaces.pzIter 2 F z θ|
      ≤ (2 / z ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ) := by
  -- `sin(2θ) > 0` at an interior angle, so all the weights below are honest.
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hz2 : 0 < z ^ 2 := by positivity
  -- The two weight factors `w z` and `1 / sin(2θ)^{η/2}` are both `≥ 1`, so the
  -- weighted summands of `HkIntegrand` dominate the unweighted ones.
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, le_div_iff₀ hz2]
    nlinarith [sq_nonneg z, hz]
  have hsle1 : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hsin) (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hc : 1 ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div (Real.rpow_pos_of_pos hsin _)]
    exact le_trans hsle1 hw1
  -- A single weighted `D_z`-summand is bounded by the whole integrand.
  have hterm2 := Work.Spaces.sq_le_HkIntegrand_z α 2 F z θ 2 (le_refl 2)
  have hterm1 := Work.Spaces.sq_le_HkIntegrand_z α 2 F z θ 1 (by norm_num)
  have hsq2 : (Work.Spaces.DzIter 2 F z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 2 F z θ := by
    have h1 : (Work.Spaces.DzIter 2 F z θ) ^ 2
        ≤ (Work.Spaces.DzIter 2 F z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [mul_pow]
      simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ hc (n := 2))
        (sq_nonneg (Work.Spaces.DzIter 2 F z θ))
    linarith
  have hsq1 : (Work.Spaces.DzIter 1 F z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 2 F z θ := by
    have h1 : (Work.Spaces.DzIter 1 F z θ) ^ 2
        ≤ (Work.Spaces.DzIter 1 F z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      rw [mul_pow]
      simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ hc (n := 2))
        (sq_nonneg (Work.Spaces.DzIter 1 F z θ))
    linarith
  have hA : |Work.Spaces.DzIter 2 F z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ) :=
    calc |Work.Spaces.DzIter 2 F z θ|
          = Real.sqrt ((Work.Spaces.DzIter 2 F z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ) := Real.sqrt_le_sqrt hsq2
  have hB : |Work.Spaces.DzIter 1 F z θ| ≤ Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ) :=
    calc |Work.Spaces.DzIter 1 F z θ|
          = Real.sqrt ((Work.Spaces.DzIter 1 F z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ) := Real.sqrt_le_sqrt hsq1
  -- The product rule `D_z² = z ∂_z + z² ∂_z²` on the smooth `z`-slice.
  have hdz : HasDerivAt (fun t : ℝ => Work.Spaces.pzIter 1 F t θ)
      (Work.Spaces.pzIter 2 F z θ) z := hsm.hasDerivAt_slice_pzIter 1 hθ hz
  have hmul : HasDerivAt (fun t : ℝ => t * Work.Spaces.pzIter 1 F t θ)
      (1 * Work.Spaces.pzIter 1 F z θ + z * Work.Spaces.pzIter 2 F z θ) z :=
    (hasDerivAt_id z).mul hdz
  have hpz : Work.Spaces.pz (Work.Spaces.DzIter 1 F) z θ
      = deriv (fun t : ℝ => t * Work.Spaces.pzIter 1 F t θ) z := by
    show deriv (fun t : ℝ => Work.Spaces.DzIter 1 F t θ) z = _
    rw [show (fun t : ℝ => Work.Spaces.DzIter 1 F t θ)
        = fun t : ℝ => t * Work.Spaces.pzIter 1 F t θ from funext fun t => rfl]
  have hDz2 : Work.Spaces.DzIter 2 F z θ
      = z * Work.Spaces.pzIter 1 F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
    show z * Work.Spaces.pz (Work.Spaces.DzIter 1 F) z θ = _
    rw [hpz, hmul.deriv]
    ring
  have hDz1 : Work.Spaces.DzIter 1 F z θ = z * Work.Spaces.pzIter 1 F z θ := rfl
  -- Hence `z² ∂_z²F = D_z²F - D_zF`, and both terms are `≤ √(HkIntegrand)`.
  have hkey : Work.Spaces.pzIter 2 F z θ * z ^ 2
      = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := by
    rw [hDz2, hDz1]; ring
  have habs : |Work.Spaces.pzIter 2 F z θ * z ^ 2|
      ≤ 2 * Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ) := by
    rw [hkey]
    calc |Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ|
        ≤ |Work.Spaces.DzIter 2 F z θ - 0| + |0 - Work.Spaces.DzIter 1 F z θ| :=
          abs_sub_le _ _ _
      _ = |Work.Spaces.DzIter 2 F z θ| + |Work.Spaces.DzIter 1 F z θ| := by
            rw [sub_zero, zero_sub, abs_neg]
      _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ)
            + Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ) := add_le_add hA hB
      _ = 2 * Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ) := by ring
  have hmulabs : |Work.Spaces.pzIter 2 F z θ * z ^ 2|
      = |Work.Spaces.pzIter 2 F z θ| * z ^ 2 := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hz2)]
  have habs' : |Work.Spaces.pzIter 2 F z θ| * z ^ 2
      ≤ 2 * Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ) := by
    rw [← hmulabs]; exact habs
  have hfin : |Work.Spaces.pzIter 2 F z θ|
      ≤ (2 * Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ)) / z ^ 2 := by
    rw [le_div_iff₀ hz2]; exact habs'
  calc |Work.Spaces.pzIter 2 F z θ|
      ≤ (2 * Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ)) / z ^ 2 := hfin
    _ = (2 / z ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 2 F z θ) := by ring

end Work.FTS.ClassCHon.Zpz.Aux
