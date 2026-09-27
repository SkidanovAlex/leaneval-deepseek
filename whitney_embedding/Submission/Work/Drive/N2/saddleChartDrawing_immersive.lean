import Mathlib
import Submission.Work.Drive.N2.saddleWindowBlock
import Submission.Work.Drive.N2.saddleModelPsi

/-!
# The saddle chart drawing is immersive on the levels of the saddle

`Work.Drive.N2.saddleChartDrawing_immersive`: let `Z : M → ℂ` be a local coordinate of a saddle chart
of a surface (a smooth map with injective differential on an open set `U`), and let
`y ↦ ((Z y) ^ 2).re` be the level function of the saddle.  Then the "drawing"

  `y ↦ cE3 (saddlePsi η δ (Z y))`  (`cE3 : ℂ → ℝ³` the inclusion `w ↦ (re w, im w, 0)`)

is immersive in the level directions of the saddle: a tangent vector `v` that is killed both by the
differential of the level function and by the differential of the drawing is zero.

The point is that on `ℂ` the two model differentials have a trivial common kernel:
`d ((ζ ^ 2).re) z` is a non-zero real functional with kernel `ℝ ∙ (I * conj z)` for `z ≠ 0`, and the
`Ψ`-half kills the direction `I * conj z` (`Work.Drive.N2.fderiv_saddlePsi_ne_zero`, which makes `Ψ`
immersive along the level curves `{Re z² = const}`); at `z = 0`, where the first differential
vanishes, `Ψ` is the identity in a neighbourhood of `0`, so the second differential is the injective
map `cE3`.  Injectivity of the differential of `Z` finishes the argument.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function

/-! ### The two model differentials on `ℂ` have a trivial common kernel -/

/-- `2 z · (i z̄) = 2 ‖z‖² · i`, in particular of vanishing real part. -/
private lemma two_z_mul_I_conj (z : ℂ) :
    2 * z * (Complex.I * (starRingEnd ℂ) z) = ((2 * Complex.normSq z : ℝ) : ℂ) * Complex.I := by
  rw [show 2 * z * (Complex.I * (starRingEnd ℂ) z)
      = 2 * Complex.I * (z * (starRingEnd ℂ) z) by ring]
  rw [Complex.mul_conj]
  push_cast
  ring

/-- `2 z · (i (i z̄)) = -2 ‖z‖²`. -/
private lemma two_z_mul_I_I_conj (z : ℂ) :
    2 * z * (Complex.I * (Complex.I * (starRingEnd ℂ) z)) = ((-2 * Complex.normSq z : ℝ) : ℂ) := by
  rw [show 2 * z * (Complex.I * (Complex.I * (starRingEnd ℂ) z))
      = -2 * (z * (starRingEnd ℂ) z) by
    rw [← mul_assoc Complex.I Complex.I (starRingEnd ℂ z), Complex.I_mul_I]; ring]
  rw [Complex.mul_conj]
  push_cast
  ring

/-- The direction `i z̄` is tangent to the level curves of `Re z²`. -/
private lemma fderiv_sq_re_apply_I_conj (z : ℂ) :
    (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) z) (Complex.I * (starRingEnd ℂ) z) = 0 := by
  rw [fderiv_sq_re_apply, two_z_mul_I_conj]
  simp

theorem fderiv_sq_re_apply_I_I_conj (z : ℂ) :
    (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) z) (Complex.I * (Complex.I * (starRingEnd ℂ) z))
      = -2 * Complex.normSq z := by
  rw [fderiv_sq_re_apply, two_z_mul_I_I_conj]
  simp

/-- Decomposition of `w` in the real basis `(v, i v)` of `ℂ` (`v ≠ 0`). -/
private lemma eq_re_smul_add_im_smul (w v : ℂ) (hv : v ≠ 0) :
    w = (w / v).re • v + (w / v).im • (Complex.I * v) := by
  have key : ((w / v).re : ℂ) * v + ((w / v).im : ℂ) * (Complex.I * v) = w := by
    calc ((w / v).re : ℂ) * v + ((w / v).im : ℂ) * (Complex.I * v)
        = (((w / v).re : ℂ) + ((w / v).im : ℂ) * Complex.I) * v := by ring
      _ = (w / v) * v := by rw [Complex.re_add_im]
      _ = w := div_mul_cancel₀ w hv
  rw [Complex.real_smul, Complex.real_smul]
  exact key.symm

/-- Chain rule for the drawing `ζ ↦ cE3 (Ψ ζ)` (the outer map being linear). -/
private lemma fderiv_cE3_saddlePsi_apply {η δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (z u : ℂ) :
    (fderiv ℝ (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) z) u
      = cE3 ((fderiv ℝ (saddlePsi η δ) z) u) := by
  have hdiff : DifferentiableAt ℝ (saddlePsi η δ) z :=
    ((contDiff_saddlePsi η δ hδ hδ₂).differentiable (by simp)).differentiableAt
  have hcomp : fderiv ℝ ((⇑cE3) ∘ (saddlePsi η δ)) z
      = cE3.comp (fderiv ℝ (saddlePsi η δ) z) := by
    rw [fderiv_comp (𝕜 := ℝ) z (g := ⇑cE3) (f := saddlePsi η δ) cE3.differentiableAt hdiff]
    rw [cE3.hasFDerivAt.fderiv]
  rw [show (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) = (⇑cE3) ∘ (saddlePsi η δ) from rfl, hcomp,
    ContinuousLinearMap.comp_apply]

/-- The drawing is immersive in the level direction `i z̄` (`z ≠ 0`). -/
private lemma fderiv_cE3_saddlePsi_I_conj_ne_zero {η δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2)
    {z : ℂ} (hz : z ≠ 0) :
    (fderiv ℝ (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) z) (Complex.I * (starRingEnd ℂ) z) ≠ 0 := by
  rw [fderiv_cE3_saddlePsi_apply hδ hδ₂]
  intro h
  exact fderiv_saddlePsi_ne_zero hδ hδ₂ z hz (cE3_injective (by simpa using h))

/-- **The model statement.**  For `z : ℂ`, the differentials of the level function `ζ ↦ (ζ ^ 2).re`
and of the drawing `ζ ↦ cE3 (saddlePsi η δ ζ)` have a trivial common kernel at `z`. -/
theorem saddleKernel_triv {η δ : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (z w : ℂ)
    (h1 : (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) z) w = 0)
    (h2 : (fderiv ℝ (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) z) w = 0) : w = 0 := by
  by_cases hz : z = 0
  · -- at `0` the first differential vanishes, but `Ψ` is the identity near `0`
    subst hz
    have hr : (0:ℝ) < (2 - 4 * δ) / 4 := by linarith
    have hD2 : fderiv ℝ (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) 0 = cE3 := by
      have hev : (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) =ᶠ[𝓝 (0:ℂ)] (⇑cE3) := by
        filter_upwards [Metric.ball_mem_nhds (0:ℂ) hr] with ζ hζ
        rw [Metric.mem_ball, dist_zero_right] at hζ
        simp [saddlePsi_eq_self_of_norm_lt hδ hδ₂ hζ]
      rw [hev.fderiv_eq]
      exact cE3.hasFDerivAt.fderiv
    rw [hD2] at h2
    exact cE3_injective (by simpa using h2)
  · -- otherwise `ker d(Re z²) = ℝ ∙ (i z̄)`, on which the drawing is immersive
    set v : ℂ := Complex.I * (starRingEnd ℂ) z with hv
    have hvne : v ≠ 0 := by
      rw [hv]
      exact mul_ne_zero Complex.I_ne_zero (by simpa using hz)
    have hD1v : (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) z) v = 0 := by
      rw [hv]; exact fderiv_sq_re_apply_I_conj z
    have hD1Iv : (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) z) (Complex.I * v) = -2 * Complex.normSq z := by
      rw [hv]; exact fderiv_sq_re_apply_I_I_conj z
    have hD2v : (fderiv ℝ (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) z) v ≠ 0 := by
      rw [hv]; exact fderiv_cE3_saddlePsi_I_conj_ne_zero hδ hδ₂ hz
    have hdec := eq_re_smul_add_im_smul w v hvne
    -- the first differential reads off the `i v`-coefficient
    have him0 : (w / v).im = 0 := by
      have h := h1
      rw [hdec] at h
      rw [map_add, map_smul, map_smul, hD1v, hD1Iv] at h
      have h' : (w / v).im * (-2 * Complex.normSq z) = 0 := by simpa using h
      have hns : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact h''
      · exact absurd h'' (mul_ne_zero (by norm_num) hns)
    have hzero : (w / v).im • (Complex.I * v) = 0 := by rw [him0, zero_smul]
    have hw : w = (w / v).re • v := by
      calc w = (w / v).re • v + (w / v).im • (Complex.I * v) := hdec
        _ = (w / v).re • v + 0 := by rw [hzero]
        _ = (w / v).re • v := add_zero _
    have h2' : (w / v).re • ((fderiv ℝ (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) z) v) = 0 := by
      rw [hw, map_smul] at h2
      exact h2
    rcases smul_eq_zero.mp h2' with h | h
    · rw [h, zero_smul] at hw
      exact hw
    · exact absurd h hD2v

/-! ### The chart statement -/

theorem saddleChartDrawing_immersive {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M] (U : Set M) (hU : IsOpen U) (Z : M → ℂ) (hZsm : ContMDiffOn (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z U) (hZimm : ∀ x ∈ U, Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℂ) Z x)) {η δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10) : ∀ x ∈ U, ∀ v : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) x, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ) (fun y : M => ((Z y) ^ 2).re) x v = 0 → mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (fun y : M => Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z y))) x v = 0 → v = 0 := by
  intro x hx v h1 h2
  have hδ₂ : δ < 1 / 2 := by linarith
  have hZx : MDifferentiableAt (𝓡 2) (𝓘(ℝ,ℂ)) Z x :=
    (hZsm.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hq : MDifferentiableAt (𝓘(ℝ,ℂ)) (𝓘(ℝ,ℝ)) (fun ζ : ℂ => (ζ ^ 2).re) (Z x) :=
    (mdifferentiableAt_iff_differentiableAt (𝕜 := ℝ)).mpr (by fun_prop)
  have hg : MDifferentiableAt (𝓘(ℝ,ℂ)) (𝓡 3) (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) (Z x) := by
    have hC : ContDiff ℝ ∞ (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) :=
      cE3.contDiff.comp (contDiff_saddlePsi η δ hδ hδ₂)
    exact (hC.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  -- the chain rule at `x`, applied to the two composed maps
  have e1 := mfderiv_comp_apply (f := Z) (g := fun ζ : ℂ => (ζ ^ 2).re) x hq hZx v
  have e2 := mfderiv_comp_apply (f := Z) (g := fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) x hg hZx v
  have h1' : mfderiv (𝓡 2) (𝓘(ℝ,ℝ)) ((fun ζ : ℂ => (ζ ^ 2).re) ∘ Z) x v = 0 := h1
  rw [e1] at h1'
  have h1'' : (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) (Z x)) (mfderiv (𝓡 2) (𝓘(ℝ,ℂ)) Z x v) = 0 := by
    rw [mfderiv_eq_fderiv] at h1'
    exact h1'
  have h2' : mfderiv (𝓡 2) (𝓡 3) ((fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) ∘ Z) x v = 0 := h2
  rw [e2] at h2'
  have h2'' : (fderiv ℝ (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) (Z x))
      (mfderiv (𝓡 2) (𝓘(ℝ,ℂ)) Z x v) = 0 := by
    rw [mfderiv_eq_fderiv] at h2'
    exact h2'
  -- the model statement, and injectivity of the differential of `Z`
  have hw0 : mfderiv (𝓡 2) (𝓘(ℝ,ℂ)) Z x v = 0 :=
    saddleKernel_triv hδ hδ₂ (Z x) _ h1'' h2''
  exact hZimm x hx (by rw [hw0, map_zero])

end Work.Drive.N2
