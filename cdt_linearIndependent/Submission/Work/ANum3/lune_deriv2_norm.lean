import Mathlib
import Submission.Work.ANum3.ZcertDefs
import Submission.Work.ANum2.lune_second_deriv_bound

/-!
# The exact modulus of the second derivative of the lune map at `c = 36/5`

For `c > 1` the lune map of Calegari--Dimitrov--Tang (arXiv:2408.15403, eq.
`(firstgobble)`) is

`lune c z = (z·B − B + √(R z))/(2C)`,  `B = 1 + c²`,  `C = c² − 1`,
`R z = luneR c z = B²(1+z)² − 16c²z`,

with `R' = 2B²(1+z) − 16c²` and `R'' = 2B²` (`Work.ANum2.luneRd`,
`Work.ANum2.hasDerivAt_luneRd`).  On the open unit disc the radicand avoids the
branch cut (`Work.APsi.luneR_slitPlane_of_lt`), so the principal square root
`u = √R` is holomorphic and `Work.ANum2.lune_deriv2_aux` gives the second
derivative.

Two algebraic facts turn that formula into a closed form:

* `4B²·R z − (R' z)² = 64c²((1+c²)² − 4c²) = 64c²(c²−1)²` is *constant*
  (`lune_quad_const_local`);
* with `u = (R z)^{1/2}`, the principal-branch rewritings
  `R^{−1/2} = u⁻¹`, `R^{−3/2} = (u³)⁻¹` are legitimate.

Hence `(lune c)''(z)·u³ = 8c²((1+c²)² − 4c²)/C`, and taking moduli, since
`‖u‖² = ‖R z‖` so that `‖u‖ = √‖R z‖`,

`‖(lune c)''(z)‖·‖R z‖·√‖R z‖ = 8c²(c²−1)²/(c²−1) = 8c²(c²−1)`.

This is the "constant times `|R|^{-3/2}`" shape of the second-derivative bound
used by the `luneM2B` certificate (`Submission/Work/ANum3/luneM2B_sound.lean`).
-/

namespace Work.ANum3

open Submission.CDTPlan Complex Work.APsi

noncomputable section

/-- **The structural identity of the lune radicand** at `c = 36/5`: the combination
`4(1+c²)²·R − (R')²` is the constant `64c²(c²−1)²`. -/
private lemma lune_quad_const_local (z : ℂ) :
    4 * (1 + (((36 : ℝ) / 5 : ℝ) : ℂ) ^ 2) ^ 2 * luneR (36 / 5) z
        - (Work.ANum2.luneRd (36 / 5) z) ^ 2
      = ((64 * (36 / 5 : ℝ) ^ 2 *
            ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2) : ℝ) : ℂ) := by
  simp only [luneR, Work.ANum2.luneRd]
  push_cast
  ring

/-- **Closed form of the second derivative.**  Writing `u = √(R z)` for the principal square
root of the lune radicand, on the open unit disc
`(lune (36/5))''(z)·u³ = 8c²((1+c²)²−4c²)/(c²−1)` with `c = 36/5`. -/
private lemma lune_deriv2_closed (z : ℂ) (hz : ‖z‖ < 1) :
    deriv (deriv (lune (36 / 5))) z * ((luneR (36 / 5) z) ^ (1 / 2 : ℂ)) ^ 3
      = ((8 * (36 / 5 : ℝ) ^ 2 *
            ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2) /
          ((36 / 5 : ℝ) ^ 2 - 1) : ℝ) : ℂ) := by
  have hc : (1 : ℝ) < 36 / 5 := by norm_num
  have hmem : luneR (36 / 5) z ∈ slitPlane := luneR_slitPlane_of_lt hc hz
  have hRne : luneR (36 / 5) z ≠ 0 := slitPlane_ne_zero hmem
  set u : ℂ := (luneR (36 / 5) z) ^ (1 / 2 : ℂ) with hu
  have hu2 : u ^ 2 = luneR (36 / 5) z := by rw [hu]; exact cpow_half_sq _
  have hu_ne : u ≠ 0 := by
    intro h
    exact hRne (by rw [← hu2, h]; ring)
  -- principal-branch rewritings of the negative powers
  have hp1 : (luneR (36 / 5) z) ^ (-(1 / 2) : ℂ) = u⁻¹ := by
    rw [Complex.cpow_neg, hu]
  have hp3 : (luneR (36 / 5) z) ^ (-(3 / 2) : ℂ) = (u ^ 3)⁻¹ := by
    rw [Complex.cpow_neg]
    congr 1
    have h : (3 / 2 : ℂ) = 1 / 2 + 1 := by norm_num
    rw [h, Complex.cpow_add (1 / 2 : ℂ) 1 hRne, Complex.cpow_one]
    rw [← hu, ← hu2]
    ring
  have hd := Work.ANum2.lune_deriv2_aux (36 / 5) hc z hz
  rw [hp1, hp3] at hd
  rw [hd]
  have hC : luneC (36 / 5) ≠ 0 := luneC_ne_zero hc
  have hstep : ((1 / 2 : ℂ) * ((-(1 / 2 : ℂ)) * (u ^ 3)⁻¹ * (Work.ANum2.luneRd (36 / 5) z) ^ 2
        + u⁻¹ * (2 * (1 + (((36 : ℝ) / 5 : ℝ) : ℂ) ^ 2) ^ 2))) / (2 * luneC (36 / 5)) * u ^ 3
      = ((1 / 2 : ℂ) * ((-(1 / 2 : ℂ)) * (Work.ANum2.luneRd (36 / 5) z) ^ 2
          + u ^ 2 * (2 * (1 + (((36 : ℝ) / 5 : ℝ) : ℂ) ^ 2) ^ 2))) / (2 * luneC (36 / 5)) := by
    field_simp
  rw [hstep]
  rw [hu2]
  have hk : -(1 / 2 : ℂ) * (Work.ANum2.luneRd (36 / 5) z) ^ 2
        + luneR (36 / 5) z * (2 * (1 + (((36 : ℝ) / 5 : ℝ) : ℂ) ^ 2) ^ 2)
      = (1 / 2) * (((64 : ℝ) * (36 / 5) ^ 2 *
            ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2) : ℝ) : ℂ) := by
    rw [← lune_quad_const_local z]
    ring
  rw [hk]
  have hCv : luneC (36 / 5) = (((36 / 5 : ℝ) ^ 2 - 1 : ℝ) : ℂ) := by
    simp only [luneC, luneCr]
  rw [hCv]
  norm_num

theorem lune_deriv2_norm (z : ℂ) (hz : ‖z‖ < 1) :
    ‖deriv (deriv (Submission.CDTPlan.lune (36 / 5))) z‖
        * (‖Work.APsi.luneR (36 / 5) z‖ * Real.sqrt ‖Work.APsi.luneR (36 / 5) z‖)
      = 8 * (36 / 5 : ℝ) ^ 2 * ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2)
          / ((36 / 5 : ℝ) ^ 2 - 1) := by
  have hK : (0 : ℝ) ≤ 8 * (36 / 5 : ℝ) ^ 2 *
      ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2) / ((36 / 5 : ℝ) ^ 2 - 1) := by
    norm_num
  have hkey := lune_deriv2_closed z hz
  have h2 : ‖deriv (deriv (lune (36 / 5))) z * ((luneR (36 / 5) z) ^ (1 / 2 : ℂ)) ^ 3‖
      = ‖((8 * (36 / 5 : ℝ) ^ 2 *
            ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2) /
          ((36 / 5 : ℝ) ^ 2 - 1) : ℝ) : ℂ)‖ := by
    rw [hkey]
  rw [norm_mul, norm_pow] at h2
  have hsq : ‖(luneR (36 / 5) z) ^ (1 / 2 : ℂ)‖ ^ 2 = ‖luneR (36 / 5) z‖ := by
    rw [← norm_pow, cpow_half_sq]
  have hsqrt : ‖(luneR (36 / 5) z) ^ (1 / 2 : ℂ)‖ = Real.sqrt ‖luneR (36 / 5) z‖ :=
    ((Real.sqrt_eq_iff_eq_sq (norm_nonneg _) (norm_nonneg _)).mpr hsq.symm).symm
  have hu3 : ‖(luneR (36 / 5) z) ^ (1 / 2 : ℂ)‖ ^ 3
      = ‖luneR (36 / 5) z‖ * Real.sqrt ‖luneR (36 / 5) z‖ := by
    rw [hsqrt]
    have hs := Real.sq_sqrt (norm_nonneg (luneR (36 / 5) z))
    nlinarith [Real.sqrt_nonneg ‖luneR (36 / 5) z‖]
  rw [hu3] at h2
  have hnormK : ‖((8 * (36 / 5 : ℝ) ^ 2 *
        ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2) /
        ((36 / 5 : ℝ) ^ 2 - 1) : ℝ) : ℂ)‖
      = 8 * (36 / 5 : ℝ) ^ 2 * ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2)
          / ((36 / 5 : ℝ) ^ 2 - 1) := by
    have h := RCLike.norm_ofReal (K := ℂ)
      (8 * (36 / 5 : ℝ) ^ 2 * ((1 + (36 / 5 : ℝ) ^ 2) ^ 2 - 4 * (36 / 5 : ℝ) ^ 2)
        / ((36 / 5 : ℝ) ^ 2 - 1))
    rw [abs_of_nonneg hK] at h
    exact h
  rw [h2]
  exact hnormK

end

end Work.ANum3
