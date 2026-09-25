/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The one-coordinate radial extension is the flat Seeley extension in the log chart

For `j : Fin n` with `ρ j > 0` and a point `z` with `z j ≠ 0`, the radial Seeley extension in the
`j`-th coordinate agrees with the ordinary Seeley extension of the pulled-back function, evaluated
in the logarithmic chart:

`radialExt n ρ a b j G z = seeleyExt a b (flatPull n ρ j G) (polarChart n ρ j z)`.

The mathematics is the change of variable `t = log (ρ j / ‖z j‖)`.  The fiberwise point map
`flatPoint n ρ j (w, t)` has its `j`-th coordinate on the ray spanned by `w j` at radius
`ρ j * exp (-t)`, while

* `flatPoint n ρ j (polarChart n ρ j z) = z`: the chart is a section of the fiber map (the point of
  modulus `ρ j * exp (-log (ρ j / ‖z j‖)) = ‖z j‖` on the ray of `z j` is `z j` again), and
* `flatPoint n ρ j (z, -(b m) * log (ρ j / ‖z j‖)) = Function.update z j (polarRefl n ρ b m j z)`
  for `‖z j‖ ≥ ρ j`: the `j`-th coordinate of the reflected point has modulus
  `ρ j * exp (b m * log (ρ j / ‖z j‖)) = ρ j * (ρ j / ‖z j‖) ^ (b m)`
  and argument that of `z j`, i.e. it equals `z j * (ρ j / ‖z j‖) ^ (b m + 1)`, exactly the
  reflected coordinate `polarRefl`;

while the two cutoff factors coincide (`polarChi` is `1` inside and `seeleyCut (b m * t)` outside,
and `seeleyCut` is even, so it does not matter that the Seeley term evaluates the cutoff at
`-(b m) * t`).
-/
import Mathlib
import Submission.Work.NN.Final.PolarDefs
import Submission.Work.NN.Final.PolarRegions
import Submission.Work.NN.Final.SeeleyDefs

namespace Work.NN.Final

/-- The Seeley cutoff is even: it only depends on the distance to the origin. -/
private lemma seeleyCut_neg (t : ℝ) : seeleyCut (-t) = seeleyCut t := ContDiffBump.neg _ _

/-- The logarithmic chart is a section of the fiber map: sending `z` to `(z, log (ρ j / ‖z j‖))`
and then back to the point of modulus `ρ j * exp (-t)` on the ray of `z j` returns `z`. -/
private lemma flatPoint_polarChart {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} (hρ : 0 < ρ j)
    {z : Fin n → ℂ} (hz : z j ≠ 0) :
    flatPoint n ρ j (polarChart n ρ j z) = z := by
  rw [flatPoint, polarChart_apply, Function.update_eq_self_iff]
  have hr : 0 < ‖z j‖ := norm_pos_iff.mpr hz
  have hx : 0 < ρ j / ‖z j‖ := div_pos hρ hr
  have hexp : Real.exp (-Real.log (ρ j / ‖z j‖)) = (ρ j / ‖z j‖)⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hx]
  have h2 : ρ j * (ρ j / ‖z j‖)⁻¹ / ‖z j‖ = 1 := by
    rw [inv_div]
    field_simp
  rw [hexp, h2, Complex.ofReal_one, one_mul]

/-- The reflected point of the flat picture over `z` at the reflected level
`-(b m) * log (ρ j / ‖z j‖)` is the point whose `j`-th coordinate is the reflected coordinate
`polarRefl n ρ b m j z`, the transverse coordinates being unchanged. -/
private lemma flatPoint_update_polarRefl {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} (hρ : 0 < ρ j)
    (b : ℕ → ℝ) {z : Fin n → ℂ} (hlt : ρ j < ‖z j‖) (m : ℕ) :
    flatPoint n ρ j (z, -(b m) * Real.log (ρ j / ‖z j‖))
      = Function.update z j (polarRefl n ρ b m j z) := by
  rw [flatPoint]
  congr 1
  rw [polarRefl_of_not_lt m j (not_lt.mpr (le_of_lt hlt))]
  have hr : 0 < ‖z j‖ := lt_trans hρ hlt
  have hx : 0 < ρ j / ‖z j‖ := div_pos hρ hr
  -- the modulus of the `j`-th coordinate: `ρ j * exp (b m * log (ρ j / ‖z j‖))`
  have hexp : Real.exp (-(-(b m) * Real.log (ρ j / ‖z j‖))) = (ρ j / ‖z j‖) ^ (b m) := by
    rw [show -(-(b m) * Real.log (ρ j / ‖z j‖)) = b m * Real.log (ρ j / ‖z j‖) by ring]
    rw [Real.rpow_def_of_pos hx, mul_comm]
  have hcoef : ρ j * (ρ j / ‖z j‖) ^ (b m) / ‖z j‖ = (ρ j / ‖z j‖) ^ (b m + 1) := by
    rw [← div_mul_eq_mul_div, mul_comm, ← Real.rpow_add_one hx.ne']
  rw [hexp, hcoef]
  ring

theorem radialExt_seeleyExt_flat {n : ℕ} {ρ : Fin n → ℝ} (j : Fin n) (hρ : 0 < ρ j) (a b : ℕ → ℝ)
    (G : (Fin n → ℂ) → ℂ) {z : Fin n → ℂ} (hz : z j ≠ 0) :
    Work.NN.Final.radialExt n ρ a b j G z
      = Work.NN.Final.seeleyExt a b (Work.NN.Final.flatPull n ρ j G)
          (Work.NN.Final.polarChart n ρ j z) := by
  by_cases hle : ‖z j‖ ≤ ρ j
  · -- inside (or on) the boundary face: both sides evaluate `G` at `z`
    have hr : 0 < ‖z j‖ := norm_pos_iff.mpr hz
    have hp : 0 ≤ (polarChart n ρ j z).2 := by
      rw [polarChart_apply]
      exact Real.log_nonneg (by rw [le_div_iff₀ hr]; simpa using hle)
    rw [radialExt_of_le hle, seeleyExt_of_nonneg a b (flatPull n ρ j G) hp, polarChart_apply,
      flatPull_apply, ← polarChart_apply, flatPoint_polarChart hρ hz]
  · -- outside: both sides are the Seeley sum, and the terms agree
    have hlt : ρ j < ‖z j‖ := lt_of_not_ge hle
    have hneg : (polarChart n ρ j z).2 < 0 := by
      rw [polarChart_apply]
      exact Real.log_neg (div_pos hρ (lt_trans hρ hlt))
        (by rw [div_lt_one (lt_trans hρ hlt)]; exact hlt)
    rw [radialExt_of_gt hlt, seeleyExt_of_neg a b (flatPull n ρ j G) hneg, polarChart_apply,
      seeleySum]
    refine tsum_congr fun m => ?_
    rw [radialTerm, seeleyTerm_apply, flatPull_apply]
    dsimp only
    rw [polarChi_of_not_lt m j (not_lt.mpr (le_of_lt hlt)), flatPoint_update_polarRefl hρ b hlt m]
    rw [show -(b m) * Real.log (ρ j / ‖z j‖) = -(b m * Real.log (ρ j / ‖z j‖)) by ring,
      seeleyCut_neg]

end Work.NN.Final
