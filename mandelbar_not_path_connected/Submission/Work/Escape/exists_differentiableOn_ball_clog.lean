import Mathlib
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Holomorphic logarithms on balls

Given a function `g : ℂ → ℂ` that is holomorphic and nowhere zero on a ball `Metric.ball c r`,
we construct a holomorphic branch `L` of `clog`, i.e. `exp (L z) = g z` for all `z` in the ball,
normalized by `Re (L z) = log ‖g z‖`.

The construction is the standard one: a ball is contractible (hence simply connected), so
Mathlib's covering-space machinery (`Complex.exists_continuousOn_eqOn_exp_comp`) produces a
*continuous* branch `L`.  A continuous logarithm of a holomorphic function is automatically
holomorphic: locally near a point `z₀` one writes `g = exp ∘ Φ` with `Φ` holomorphic (using the
principal branch of `clog`), and then `f - Φ` is continuous with `exp (f - Φ) = 1`, hence takes
values in the discrete set `2πiℤ`; being close to `0`, it must vanish.  This is
`continuousOn_exp_eq_differentiableOn` below.
-/

open Filter
open scoped Topology

noncomputable section

namespace Work.Escape

/-- If `exp (L z) = g z`, then the real part of `L z` is the logarithm of `‖g z‖`. -/
theorem re_eq_log_norm_of_exp_eq {L g : ℂ → ℂ} {z : ℂ} (h : Complex.exp (L z) = g z) :
    (L z).re = Real.log ‖g z‖ := by
  have hnorm : ‖g z‖ = Real.exp (L z).re := by
    rw [← h, Complex.norm_exp]
  rw [hnorm, Real.log_exp]

/-- A continuous logarithm of a holomorphic nowhere vanishing function is holomorphic.

This is the local statement that a continuous lift of `exp` along a holomorphic map is again
holomorphic, proved by comparing with the local holomorphic logarithm `Complex.log (g z / g z₀)`
near a point `z₀ ∈ U`. -/
theorem continuousOn_exp_eq_differentiableOn {U : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : DifferentiableOn ℂ g U)
    (hne : ∀ z ∈ U, g z ≠ 0) (h : ∀ z ∈ U, Complex.exp (f z) = g z) :
    DifferentiableOn ℂ f U := by
  intro z₀ hz₀
  have hnU : U ∈ 𝓝 z₀ := hU.mem_nhds hz₀
  have hg_at : DifferentiableAt ℂ g z₀ := (hg z₀ hz₀).differentiableAt hnU
  have hf_at : ContinuousAt f z₀ := hf.continuousAt hnU
  have hg₀ : g z₀ ≠ 0 := hne z₀ hz₀
  -- a candidate holomorphic logarithm near `z₀`
  set Φ : ℂ → ℂ := fun z => Complex.log (g z / g z₀) + f z₀ with hΦdef
  have hdivval : g z₀ / g z₀ = 1 := div_self hg₀
  have hgz₀ : g z₀ / g z₀ ∈ Complex.slitPlane := by
    rw [hdivval]; exact Complex.one_mem_slitPlane
  have hΦ_at : DifferentiableAt ℂ Φ z₀ := by
    rw [hΦdef]
    have h1 : DifferentiableAt ℂ (fun z => Complex.log (g z / g z₀)) z₀ :=
      (hg_at.div_const (g z₀)).clog hgz₀
    exact h1.add_const (f z₀)
  have hΦz₀ : Φ z₀ = f z₀ := by
    rw [hΦdef]; simp [hdivval]
  have hslit : ∀ᶠ z in 𝓝 z₀, g z / g z₀ ∈ Complex.slitPlane := by
    have hmem : Complex.slitPlane ∈ 𝓝 ((fun z => g z / g z₀) z₀) := by
      rw [show (fun z => g z / g z₀) z₀ = 1 from hdivval]
      exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
    exact (hg_at.continuousAt.div_const (g z₀)).preimage_mem_nhds hmem
  -- `f` agrees with `Φ` in a neighbourhood of `z₀`
  have hev : ∀ᶠ z in 𝓝 z₀, f z = Φ z := by
    have hA : ∀ᶠ z in 𝓝 z₀, Complex.exp (f z - Φ z) = 1 := by
      filter_upwards [hnU, hslit] with z hzU hslitz
      have hexp : Complex.exp (Φ z) = g z := by
        rw [hΦdef, Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero hslitz),
          h z₀ hz₀, div_mul_cancel₀ (g z) hg₀]
      rw [Complex.exp_sub, h z hzU, hexp, div_self (hne z hzU)]
    have hB : ∀ᶠ z in 𝓝 z₀, ‖f z - Φ z‖ < 1 := by
      have hcont : ContinuousAt (fun z => f z - Φ z) z₀ := hf_at.sub hΦ_at.continuousAt
      have ht := Metric.tendsto_nhds.mp hcont.tendsto (1 : ℝ) (by norm_num)
      simpa [hΦz₀, dist_eq_norm] using ht
    filter_upwards [hA, hB] with z he hlt
    -- `f z - Φ z` lies in `2πiℤ`, yet has modulus `< 1`, so it vanishes
    have habs : |(f z - Φ z).im| < 1 := lt_of_le_of_lt (Complex.abs_im_le_norm _) hlt
    have hl := Complex.log_exp (x := f z - Φ z)
      (by linarith [neg_abs_le (f z - Φ z).im, habs, Real.pi_gt_three])
      (by linarith [le_abs_self (f z - Φ z).im, habs, Real.pi_gt_three])
    rw [he, Complex.log_one] at hl
    exact (sub_eq_zero.mp hl.symm)
  exact (hΦ_at.congr_of_eventuallyEq hev).differentiableWithinAt

/-- A holomorphic, nowhere vanishing function on a ball admits a holomorphic logarithm, whose
real part is `log ‖g z‖`. -/
theorem exists_differentiableOn_ball_clog {g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hg : DifferentiableOn ℂ g (Metric.ball c r)) (hne : ∀ z ∈ Metric.ball c r, g z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (Metric.ball c r) ∧
      (∀ z ∈ Metric.ball c r, Complex.exp (L z) = g z) ∧
      (∀ z ∈ Metric.ball c r, (L z).re = Real.log ‖g z‖) := by
  rcases le_or_gt r 0 with hr | hr
  · -- the ball is empty
    refine ⟨fun _ => 0, differentiableOn_const (𝕜 := ℂ) (0 : ℂ), ?_, ?_⟩ <;>
      · intro z hz
        have h1 : dist z c < r := Metric.mem_ball.mp hz
        have h2 : (0 : ℝ) ≤ dist z c := dist_nonneg
        linarith
  · -- the ball is contractible, hence simply connected
    have hUo : IsOpen (Metric.ball c r) := Metric.isOpen_ball
    have hUsc : IsSimplyConnected (Metric.ball c r) :=
      @SimplyConnectedSpace.ofContractible (Metric.ball c r) inferInstance
        (Metric.contractibleSpace_ball hr)
    have hgcont : ContinuousOn g (Metric.ball c r) := hg.continuousOn
    have h0 : (0 : ℂ) ∉ g '' Metric.ball c r := by
      rintro ⟨z, hz, hz0⟩
      exact hne z hz hz0
    obtain ⟨L, hLcont, hLexp⟩ :=
      Complex.exists_continuousOn_eqOn_exp_comp hUsc hUo hgcont h0
    exact ⟨L,
      continuousOn_exp_eq_differentiableOn hUo hLcont hg hne (fun z hz => hLexp hz),
      fun z hz => hLexp hz,
      fun z hz => re_eq_log_norm_of_exp_eq (hLexp hz)⟩

end Work.Escape
