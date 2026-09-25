import Mathlib
import Submission.Work.NN.Core.Defs
import Submission.Work.NN.Core.Solver
import Submission.Work.NN.Core.lipschitzOn_ball_of_contDiffAt_one

namespace Work.NN.Core

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff Topology

variable {n : ℕ}

/-! ### The datum `∂̄_J z_j` as a perturbation term

On the reference structure `stdOf T` the coordinate functions `z_j` are holomorphic, so the
linearisation `dbar_linearization` identifies `∂̄_J z_j` with the perturbation term
`dbarPert (J - stdOf T) z_j`.  Since `z_j` is *linear*, this term is `dbarPert A z_j(y) =
(i/2)·(dz_j ∘ A y)` with `dz_j` the constant linear map `tupleDeriv T` followed by a
coordinate projection; hence both the size of `∂̄_J z_j` and its increments are controlled by
those of the perturbation `A = J - stdOf T`. -/

/-- `∂̄_J z_j` is the perturbation term of the linearisation. -/
lemma dbar_zvec_eq_dbarPert (T : E n ≃L[ℝ] F n) (J : E n → E n →L[ℝ] E n) (j : Fin n)
    (y : E n) :
    dbar J (fun z => zvec T z j) y
      = dbarPert (perturbation J T) (zcoord T j) y := by
  change dbar J (zcoord T j) y = dbarPert (perturbation J T) (zcoord T j) y
  rw [dbar_linearization T J (zcoord T j) y]
  have hstd : dbar (stdOf T) (zcoord T j) y = 0 := by
    rw [dbar_eq_zero_iff]
    exact fun w => zcoord_hol T j y w
  rw [hstd, zero_add]
  rfl

/-- Pointwise bound for `∂̄_J z_j` in terms of the perturbation `A = J - stdOf T`. -/
lemma norm_dbar_zvec_le (T : E n ≃L[ℝ] F n) (J : E n → E n →L[ℝ] E n) (j : Fin n) (y : E n) :
    ‖dbar J (fun z => zvec T z j) y‖
      ≤ (1 / 2) * ‖tupleDeriv T‖ * ‖perturbation J T y‖ := by
  rw [dbar_zvec_eq_dbarPert]
  calc ‖dbarPert (perturbation J T) (zcoord T j) y‖
      ≤ (1 / 2) * ‖fderiv ℝ (zcoord T j) y‖ * ‖perturbation J T y‖ :=
        dbarPert_norm_le _ _ _
    _ ≤ (1 / 2) * ‖tupleDeriv T‖ * ‖perturbation J T y‖ := by
        rw [fderiv_zcoord T j y]
        gcongr
        exact proj_comp_norm_le (tupleDeriv T) j

/-- The increment of `∂̄_J z_j` in terms of the increment of the perturbation.  Since `dz_j` is
constant, only the perturbation contributes. -/
lemma dbar_zvec_sub (T : E n ≃L[ℝ] F n) (J : E n → E n →L[ℝ] E n) (j : Fin n) (y y' : E n) :
    dbar J (fun z => zvec T z j) y - dbar J (fun z => zvec T z j) y'
      = (Complex.I / 2) •
          (((ContinuousLinearMap.proj j).comp (tupleDeriv T)).comp
            (perturbation J T y - perturbation J T y')) := by
  rw [dbar_zvec_eq_dbarPert T J j y, dbar_zvec_eq_dbarPert T J j y']
  simp only [dbarPert]
  rw [fderiv_zcoord T j y, fderiv_zcoord T j y']
  ext v
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply, map_sub, smul_eq_mul,
    tupleDeriv]
  ring

/-- Hölder bound for `∂̄_J z_j` in terms of the Lipschitz bound for the perturbation. -/
lemma norm_dbar_zvec_sub_le (T : E n ≃L[ℝ] F n) (J : E n → E n →L[ℝ] E n) (j : Fin n)
    (y y' : E n) :
    ‖dbar J (fun z => zvec T z j) y - dbar J (fun z => zvec T z j) y'‖
      ≤ (1 / 2) * ‖tupleDeriv T‖ * ‖perturbation J T y - perturbation J T y'‖ := by
  rw [dbar_zvec_sub]
  calc ‖(Complex.I / 2) •
        (((ContinuousLinearMap.proj j).comp (tupleDeriv T)).comp
          (perturbation J T y - perturbation J T y'))‖
      = (1 / 2) * ‖((ContinuousLinearMap.proj j).comp (tupleDeriv T)).comp
          (perturbation J T y - perturbation J T y')‖ := by
        rw [norm_smul, norm_I_div_two]
    _ ≤ (1 / 2) * (‖(ContinuousLinearMap.proj j).comp (tupleDeriv T)‖ *
          ‖perturbation J T y - perturbation J T y'‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (1 / 2) * (‖tupleDeriv T‖ * ‖perturbation J T y - perturbation J T y'‖) := by
        gcongr
        exact proj_comp_norm_le (tupleDeriv T) j
    _ = (1 / 2) * ‖tupleDeriv T‖ * ‖perturbation J T y - perturbation J T y'‖ := by ring

/-- Interpolation inequality for the Hölder estimate: with `0 < α < 1`, `c ≥ 0` and
`c (2ρ)^{1-α} ≤ η`, on the scale `‖y - y'‖ ≤ 2ρ` the Lipschitz bound `c ‖y - y'‖` for the
perturbation is dominated by the Hölder bound `η ‖y - y'‖^α`. -/
lemma nn_mul_le_mul_rpow {α c η ρ t : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hc : 0 ≤ c)
    (_hη : 0 < η) (hkey : c * (2 * ρ) ^ (1 - α) ≤ η) (ht0 : 0 ≤ t) (ht : t ≤ 2 * ρ) :
    c * t ≤ η * t ^ α := by
  rcases eq_or_lt_of_le ht0 with h | htpos
  · rw [← h, Real.zero_rpow (ne_of_gt hα0), mul_zero, mul_zero]
  · have hβ : 0 < 1 - α := by linarith
    have h1 : t ^ (1 - α) ≤ (2 * ρ) ^ (1 - α) := Real.rpow_le_rpow ht0 ht hβ.le
    have h2 : t ^ α * t ^ (1 - α) = t := by
      rw [← Real.rpow_add htpos, show α + (1 - α) = 1 by ring, Real.rpow_one]
    have h3 : t ^ α * t ^ (1 - α) ≤ t ^ α * (2 * ρ) ^ (1 - α) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht0 α)
    calc c * t = c * (t ^ α * t ^ (1 - α)) := by rw [h2]
      _ ≤ c * (t ^ α * (2 * ρ) ^ (1 - α)) := mul_le_mul_of_nonneg_left h3 hc
      _ = (c * (2 * ρ) ^ (1 - α)) * t ^ α := by ring
      _ ≤ η * t ^ α := mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg ht0 α)

/-- The datum `∂̄_J z_j` is uniformly `C^{0,α}`-small on a small ball.

If `J 0` is the transport `stdOf T` of the standard complex structure (so that the perturbation
`A = J - stdOf T` vanishes at `0`) and `A` is `C¹` at `0`, then for every `η > 0` there is `r > 0`
with

  `‖∂̄_J z_j(y)‖ ≤ η` and `‖∂̄_J z_j(y) - ∂̄_J z_j(y')‖ ≤ η ‖y - y'‖^α`

for all `j`, all `y, y' ∈ ball 0 r` and every `0 < α < 1`.  In other words the Hölder datum bound
`DbarDataBound J (zvec T) α (ball 0 r) η` of `Work.NN.Core.Solver` holds on a small enough ball.

This is what makes the smallness hypothesis `C₀ δ ‖tupleDerivInv T‖ < 1` of the analytic core
satisfiable: `∂̄_J z_j = (i/2) dz_j ∘ (J - stdOf T)`, and on a ball of radius `r` one has
`sup ‖A‖ ≲ r` and `[A]_{α} ≲ r^{1-α}`, both tending to `0` with `r`. -/
theorem exists_dbarDataBound {n : ℕ} {T : E n ≃L[ℝ] F n} {J : E n → E n →L[ℝ] E n}
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hT : ∀ v : E n, T (J 0 v) = Complex.I • T v)
    (hA : ContDiffAt ℝ 1 (perturbation J T) 0) :
    ∀ η : ℝ, 0 < η → ∃ r : ℝ, 0 < r ∧
      DbarDataBound J (zvec T) α (Metric.ball (0 : E n) r) η := by
  intro η hη
  -- the perturbation vanishes at the origin
  have hA0 : perturbation J T 0 = 0 := by
    ext v : 1
    rw [perturbation_apply]
    exact sub_eq_zero.mpr (T.injective (by rw [hT v, stdOf_intertwine]))
  -- hence it is Lipschitz on a small ball, with a uniform bound on its values
  obtain ⟨r₀, C, hr₀, hC, hsupA, hlipA⟩ :=
    lipschitzOn_ball_of_contDiffAt_one hA hA0
  -- the constant multiplying the size of the perturbation in the datum bound
  set M : ℝ := (1 / 2) * ‖tupleDeriv T‖ * C with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hM1pos : 0 < M + 1 := by linarith
  -- the small radius: small enough for the sup bound, for the Hölder bound and for `2ρ ≤ 1`
  set ρ : ℝ := min r₀ (min (1 / 2) (min (η / (M + 1)) ((η / (M + 1)) ^ (1 / (1 - α)) / 2)))
    with hρdef
  have hquotpos : 0 < η / (M + 1) := div_pos hη hM1pos
  have hpowpos : 0 < (η / (M + 1)) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos hquotpos _
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min hr₀ (lt_min (by norm_num) (lt_min hquotpos (by positivity)))
  have hρr₀ : ρ ≤ r₀ := by rw [hρdef]; exact min_le_left _ _
  have hρhalf : ρ ≤ 1 / 2 := by
    rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρη : ρ ≤ η / (M + 1) := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρpow : 2 * ρ ≤ (η / (M + 1)) ^ (1 / (1 - α)) := by
    have h : ρ ≤ (η / (M + 1)) ^ (1 / (1 - α)) / 2 := by
      rw [hρdef]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    linarith
  have h2ρ1 : 2 * ρ ≤ 1 := by linarith
  have h2ρpos : 0 < 2 * ρ := by linarith
  -- the key estimates `M ρ ≤ η` and `M (2ρ)^{1-α} ≤ η`
  have hfrac : M / (M + 1) ≤ 1 := by
    rw [div_le_iff₀ hM1pos]; linarith
  have hMquot : M * (η / (M + 1)) ≤ η := by
    calc M * (η / (M + 1)) = η * (M / (M + 1)) := by ring
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left hfrac hη.le
      _ = η := by ring
  have hMρ : M * ρ ≤ η := le_trans (mul_le_mul_of_nonneg_left hρη hMnn) hMquot
  have hkey : M * (2 * ρ) ^ (1 - α) ≤ η := by
    have hβ : 0 < 1 - α := by linarith
    have hstep : (2 * ρ) ^ (1 - α) ≤ η / (M + 1) := by
      calc (2 * ρ) ^ (1 - α) ≤ ((η / (M + 1)) ^ (1 / (1 - α))) ^ (1 - α) :=
            Real.rpow_le_rpow h2ρpos.le hρpow hβ.le
        _ = η / (M + 1) := by
            rw [← Real.rpow_mul hquotpos.le, div_mul_cancel₀ 1 (ne_of_gt hβ), Real.rpow_one]
    exact le_trans (mul_le_mul_of_nonneg_left hstep hMnn) hMquot
  refine ⟨ρ, hρpos, ?_, ?_⟩
  · -- the sup bound
    intro j y hy
    have hyρ : ‖y‖ < ρ := by simpa [Metric.mem_ball, dist_zero_right] using hy
    have hyr₀ : ‖y‖ < r₀ := lt_of_lt_of_le hyρ hρr₀
    calc ‖dbar J (fun z => zvec T z j) y‖
        ≤ (1 / 2) * ‖tupleDeriv T‖ * ‖perturbation J T y‖ := norm_dbar_zvec_le T J j y
      _ ≤ (1 / 2) * ‖tupleDeriv T‖ * (C * ‖y‖) := by
          gcongr
          exact hsupA y hyr₀
      _ = M * ‖y‖ := by rw [hMdef]; ring
      _ ≤ M * ρ := mul_le_mul_of_nonneg_left hyρ.le hMnn
      _ ≤ η := hMρ
  · -- the Hölder bound
    intro j y y' hy hy'
    have hyρ : ‖y‖ < ρ := by simpa [Metric.mem_ball, dist_zero_right] using hy
    have hy'ρ : ‖y'‖ < ρ := by simpa [Metric.mem_ball, dist_zero_right] using hy'
    have hyr₀ : ‖y‖ < r₀ := lt_of_lt_of_le hyρ hρr₀
    have hy'r₀ : ‖y'‖ < r₀ := lt_of_lt_of_le hy'ρ hρr₀
    have ht2ρ : ‖y - y'‖ ≤ 2 * ρ := by
      calc ‖y - y'‖ ≤ ‖y‖ + ‖y'‖ := norm_sub_le _ _
        _ ≤ 2 * ρ := by linarith
    have hbound : ‖dbar J (fun z => zvec T z j) y - dbar J (fun z => zvec T z j) y'‖
        ≤ M * ‖y - y'‖ := by
      calc ‖dbar J (fun z => zvec T z j) y - dbar J (fun z => zvec T z j) y'‖
          ≤ (1 / 2) * ‖tupleDeriv T‖ * ‖perturbation J T y - perturbation J T y'‖ :=
            norm_dbar_zvec_sub_le T J j y y'
        _ ≤ (1 / 2) * ‖tupleDeriv T‖ * (C * ‖y - y'‖) := by
            gcongr
            exact hlipA y y' hyr₀ hy'r₀
        _ = M * ‖y - y'‖ := by rw [hMdef]; ring
    exact le_trans hbound
      (nn_mul_le_mul_rpow hα0 hα1 hMnn hη hkey (norm_nonneg _) ht2ρ)

end Work.NN.Core
