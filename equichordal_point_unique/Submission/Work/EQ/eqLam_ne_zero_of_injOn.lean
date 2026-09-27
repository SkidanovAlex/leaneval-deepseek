import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.germC_facts

namespace Work.EQ

open Complex Metric Set

/-- If `eqLam a = 0` then the linearising parameter of `germC` is the zero map, so the whole
stable germ collapses onto the axis `y = 0`: for every `u` the second coordinate of `germC a h u`
vanishes. Indeed `(eqLam a : ℂ) = 0` makes the function `v ↦ h ((eqLam a : ℂ) * v)` constant,
hence its `dslope` at `0` is `0`, and that factor multiplies the `y`-coordinate. -/
lemma germC_snd_eq_zero_of_eqLam_eq_zero {a : ℝ} {h : ℂ → ℂ} (hL : eqLam a = 0) (u : ℂ) :
    (germC a h u).2 = 0 := by
  have hLC : (eqLam a : ℂ) = 0 := by rw [hL]; norm_num
  have hfun : (fun v : ℂ => h ((eqLam a : ℂ) * v)) = fun _ : ℂ => h 0 := by
    funext v; rw [hLC, zero_mul]
  have hA : dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 u = 0 := by
    rw [hfun]
    rcases eq_or_ne u 0 with rfl | hune
    · rw [dslope_same, deriv_const]
    · rw [dslope_of_ne _ hune, slope_def_field]; simp
  show (a * u * dslope h 0 u * dslope (fun v : ℂ => h ((eqLam a : ℂ) * v)) 0 u /
      dslope (fun v : ℂ => h ((eqLam a : ℂ) * v) - h v) 0 u) = 0
  rw [hA, mul_zero, zero_div]

/-- The eigenvalue `eqLam a` of the equichordal half-map cannot vanish when the second
coordinate of the germ `germC a h` is injective on a ball of positive radius: if `eqLam a = 0`
then that coordinate is identically zero, so it is constant on any such ball. -/
theorem eqLam_ne_zero_of_injOn {a : ℝ} {h : ℂ → ℂ} {ρg : ℝ} (hρg : 0 < ρg)
    (hinj : Set.InjOn (fun u => (germC a h u).2) (Metric.ball (0 : ℂ) ρg)) :
    eqLam a ≠ 0 := by
  intro hL
  have hy : ∀ u : ℂ, (germC a h u).2 = 0 := fun u => germC_snd_eq_zero_of_eqLam_eq_zero hL u
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρg := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; simpa using hρg
  have hmem1 : ((ρg / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ρg := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < ρg / 2)]
    linarith
  have hne : ((ρg / 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [Complex.ofReal_ne_zero]; linarith
  exact hne (hinj hmem0 hmem1 (by simp only [hy])).symm

end Work.EQ
