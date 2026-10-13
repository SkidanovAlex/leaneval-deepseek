/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `η`-weighted angular `L²` energy is bounded by the `sin (2θ)` bound

The `i = 0` summand of the angular functional `Ptheta α m` is

  `Hη u = ∫_θ u(θ)² sin(2θ)^{-η}`,  `η = 99/100`,

an integral over `Iθ = [0, π/2]` against the weight `sEta θ = sin(2θ)^{-η}`, which blows up
like `θ^{-η}` at the two endpoints.

`Heta_le_of_sin_bound` shows that a *pointwise* bound `|u θ| ≤ K sin(2θ)` on `Iθ` — the bound
produced by Newton–Leibniz from a derivative bound together with the vanishing of `u` at the
endpoints — integrates against that singular weight to give the endpoint-independent constant
`K² π/2`.  The point of the exponent `η = 99/100 < 1` is exactly that

  `sin(2θ)² · sin(2θ)^{-η} = sin(2θ)^{2-η} ≤ 1`  on `Iθ`,

since `2 - η = 101/100 ≥ 0` and `0 ≤ sin(2θ) ≤ 1`.  No constant other than `π/2` (the length
of `Iθ`) is lost.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.SliceCoercDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Work.FTS.EllipticEst.TT

/-- `sin(2θ)² · sin(2θ)^{-η} ≤ 1` on `Iθ`, because `η = 99/100` makes the combined exponent
`2 - η = 101/100` nonnegative while `0 ≤ sin (2θ) ≤ 1` there. -/
theorem sin_sq_mul_sEta_le_one {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ 2 * sEta θ ≤ 1 := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hne : (-(Work.Spaces.eta) : ℝ) ≠ 0 := by rw [Work.Spaces.eta]; norm_num
  rcases eq_or_lt_of_le hs0 with h | h
  · -- `sin (2θ) = 0`: both factors vanish (`0 ^ x = 0` for `x ≠ 0`).
    rw [sEta, ← h, Real.zero_rpow hne]
    norm_num
  · -- `sin (2θ) > 0`: combine the exponents and use `0 ≤ sin ≤ 1`.
    rw [sEta, ← Real.rpow_natCast (Real.sin (2 * θ)) 2,
      ← Real.rpow_add h ((2 : ℕ) : ℝ) (-(Work.Spaces.eta))]
    apply Real.rpow_le_one hs0 hs1
    rw [Work.Spaces.eta]; norm_num

/-- The `η`-weighted angular `L²` energy `Hη u = ∫_θ u² sin(2θ)^{-η}` of a function obeying
the pointwise bound `|u θ| ≤ K sin(2θ)` on `Iθ` is at most `K² π/2`, the `K²`-multiple of the
length of `Iθ`.  (`K ≥ 0` is what makes `K sin(2θ)` an upper bound for `|u θ|` compatible with
the squaring step.) -/
theorem Heta_le_of_sin_bound (u : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ θ ∈ Work.Spaces.Iθ, |u θ| ≤ K * Real.sin (2 * θ)) :
    Work.FTS.EllipticEst.TT.Hη u ≤ K ^ 2 * (Real.pi / 2) := by
  rw [Hη]
  -- Pointwise: `u² · sin(2θ)^{-η} ≤ K²` on `Iθ`.
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2 * sEta θ ≤ K ^ 2 := by
    intro θ hθ
    have habs := h θ hθ
    have hsq : (u θ) ^ 2 ≤ (K * Real.sin (2 * θ)) ^ 2 := by
      calc (u θ) ^ 2 = |u θ| ^ 2 := (sq_abs _).symm
        _ ≤ (K * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    calc (u θ) ^ 2 * sEta θ
        ≤ (K * Real.sin (2 * θ)) ^ 2 * sEta θ :=
          mul_le_mul_of_nonneg_right hsq (sEta_nonneg hθ)
      _ = K ^ 2 * ((Real.sin (2 * θ)) ^ 2 * sEta θ) := by ring
      _ ≤ K ^ 2 * 1 := mul_le_mul_of_nonneg_left (sin_sq_mul_sEta_le_one hθ) (pow_nonneg hK 2)
      _ = K ^ 2 := mul_one (K ^ 2)
  have hIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl]
    exact measurableSet_Icc
  have hfin : volume Work.Spaces.Iθ < ⊤ := by
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  -- Bound the integral of the (possibly non-measurable!) integrand by `K² · |Iθ|`.
  have hmain : ‖∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * sEta θ‖
      ≤ K ^ 2 * (volume.real Work.Spaces.Iθ) :=
    norm_setIntegral_le_of_norm_le_const hfin (fun θ hθ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))]
      exact hpt θ hθ)
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * sEta θ :=
    setIntegral_nonneg hIθ (fun θ hθ => mul_nonneg (sq_nonneg _) (sEta_nonneg hθ))
  rw [Real.norm_eq_abs, abs_of_nonneg hnn] at hmain
  -- `|Iθ| = π/2`.
  have hvol : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def,
      show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  rw [hvol] at hmain
  exact hmain

end Work.FTS.EllipticEst.TT
