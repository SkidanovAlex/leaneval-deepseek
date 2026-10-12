import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseC3QAll.estQ3fourADefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseC3QAll.sum_abs_kA1_le`

The `kA1`-sum of FS `eq:EstimateQ3Tilde4` (the `χ̂²`-tail, which is not seen by
the low-momentum localisation `f_L`):

  `∑_{s ≠ 0} |kA1(s)| ≤ ρ_zℓ³(K₀a)·K₀(K_ℓK_L)^{-M}`,

since `kA1(s) = (1-f_L(s))·ρ_zℓ³Ŵ₁ω(0)·χ̂²(s)`, and

* `|1-f_L(s)| = 1-f_L(s)` (`0 ≤ f_L ≤ 1`),
* `ρ_zℓ³ = z² ≥ 0` and `0 ≤ Ŵ₁ω(0) ≤ K₀a` (`Q3KernelFSAll`),
* `∑_{s≠0} (1-f_L(s))|χ̂²(s)| ≤ K₀(K_ℓK_L)^{-M}` is the field
  `Q3KernelFSAll.tail_hatChiSq`.
-/

open scoped BigOperators

namespace Work.BoseC3QAll

theorem sum_abs_kA1_le (K₀ : ℝ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (hK : Work.BoseC3QAll.Q3KernelFSAll K₀ F T E) (hv : Work.BoseB7.FSParamsView E) :
    ∑ s ∈ Work.BoseB7.excited Mode, |Work.BoseC3QAll.kA1 F E s|
      ≤ E.rho * E.ell ^ 3 * (K₀ * E.aScat) * (K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) := by
  -- `ρ_zℓ³ = z²`, hence `ρ_zℓ³ ≥ 0`; with `Ŵ₁ω(0) ≥ 0` the common weight is `≥ 0`.
  have hz : E.rho * E.ell ^ 3 = E.z ^ 2 := (Work.BoseB7.zsq_eq E hv).symm
  have hc : 0 ≤ E.rho * E.ell ^ 3 * E.W1omega0 := by
    rw [hz]; exact mul_nonneg (sq_nonneg _) hK.W1omega0_nonneg
  -- `K₀ ≥ 0` (from `0 ≤ Ŵ₁ω(0) ≤ K₀·a` and `a > 0`).
  have hK0 : 0 ≤ K₀ := by
    have h : 0 ≤ K₀ * E.aScat := le_trans hK.W1omega0_nonneg hK.W1omega0_le
    exact nonneg_of_mul_nonneg_right (by rw [mul_comm]; exact h) hv.a_pos
  -- The `s`-th term, with `|1-f_L(s)| = 1-f_L(s)` (`f_L ≤ 1`) and the weight positive.
  have hh : ∀ s, |Work.BoseC3QAll.kA1 F E s|
      = (E.rho * E.ell ^ 3 * E.W1omega0) * ((1 - E.fL s) * |E.hatChiSq s|) := by
    intro s
    rw [Work.BoseC3QAll.kA1, abs_mul, abs_mul, abs_of_nonneg (by linarith [hK.fL_le_one s]),
      abs_of_nonneg hc]
    ring
  have h1 : ∑ s ∈ Work.BoseB7.excited Mode, |Work.BoseC3QAll.kA1 F E s|
      = (E.rho * E.ell ^ 3 * E.W1omega0)
        * ∑ s ∈ Work.BoseB7.excited Mode, ((1 - E.fL s) * |E.hatChiSq s|) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => hh s)
  -- `Q3KernelFSAll.tail_hatChiSq`, with the two factors commuted.
  have h2 : ∑ s ∈ Work.BoseB7.excited Mode, ((1 - E.fL s) * |E.hatChiSq s|)
      ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ)) :=
    le_of_eq_of_le (Finset.sum_congr rfl (fun s _ => mul_comm _ _)) hK.tail_hatChiSq
  have h3 : 0 ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ)) := by
    refine mul_nonneg hK0 (le_of_lt ?_)
    exact Real.rpow_pos_of_pos (mul_pos (lt_of_lt_of_le zero_lt_one hv.one_le_Kl)
      (lt_of_lt_of_le zero_lt_one hv.one_le_KL)) _
  -- `Ŵ₁ω(0) ≤ K₀a`, with `ρ_zℓ³ = z² ≥ 0`.
  have h4 : E.rho * E.ell ^ 3 * E.W1omega0 ≤ E.rho * E.ell ^ 3 * (K₀ * E.aScat) := by
    rw [hz]; exact mul_le_mul_of_nonneg_left hK.W1omega0_le (sq_nonneg _)
  calc ∑ s ∈ Work.BoseB7.excited Mode, |Work.BoseC3QAll.kA1 F E s|
      = (E.rho * E.ell ^ 3 * E.W1omega0)
        * ∑ s ∈ Work.BoseB7.excited Mode, ((1 - E.fL s) * |E.hatChiSq s|) := h1
    _ ≤ (E.rho * E.ell ^ 3 * E.W1omega0) * (K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ ≤ E.rho * E.ell ^ 3 * (K₀ * E.aScat) * (K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) :=
        mul_le_mul_of_nonneg_right h4 h3

end Work.BoseC3QAll
