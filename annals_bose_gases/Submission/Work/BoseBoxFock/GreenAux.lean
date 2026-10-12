import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.AliasClosedAux
import Submission.Work.BoseBoxFock.GreenDefs
import Submission.Work.BoseFixR.LocaliseProof.GradientIBP
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.GreenAux` — Green's second identity on `ℝ³` and the autocorrelation facts

This module supplies the analytic ingredients of the logarithmic peel
`Work.BoseBoxFock.integral_laplacian_autocorr_mul_invNorm_two_eq_log`:

## 1. Green's second identity

The workspace already proves Green's *first* identity
(`Work.BoseFixR.LocaliseProof.GradientIBP`)

    ∫ f·Δg = −∫ ⟪∇f, ∇g⟫      (`f ∈ C¹` with compact support, `g ∈ C²`).

Since the boundary term `∮ (f ∂ₙg)` of the punctured-domain computation also vanishes when the
*second* function is the compactly supported one, the same identity holds with the roles swapped:

    `gradientIBP_right : ∫ Δh·W = −∫ ⟪∇h, ∇W⟫`   (`h ∈ C²` compactly supported, `W ∈ C¹`).

Subtracting the two gives **Green's second identity** in the form used here:

    `laplacian_mul_swap : ∫ h·ΔW = ∫ Δh·W`   (`h ∈ C²` compactly supported, `W ∈ C²`),

i.e. the Laplacian is self-adjoint on `C²_c` against *any* `C²` function (no support hypothesis on
`W`): this is what lets the singular kernel `log‖·−z‖` be regularised and then pushed to the limit.

## 2. The autocorrelation of a smooth compactly supported `g`

`autocorr g` is a convolution, hence `C^∞` and compactly supported; its real part `𝒢 = re ∘ autocorr`
is the compactly supported smooth function to which the peel is applied.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators Topology
open Submission

namespace Work.BoseBoxFock.Green

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 2000000

/-! ## 1. The autocorrelation: smoothness and compact support -/

/-- `autocorr` as a convolution with the real-bilinear product `ℂ × ℂ → ℂ`, so that the level of
smoothness obtained is smoothness over `ℝ`. -/
theorem autocorr_eq_convolution_real (g : E3 → ℂ) :
    autocorr g = convolution g (fun v : E3 => (starRingEnd ℂ) (g (-v)))
      (ContinuousLinearMap.mul ℝ ℂ) volume := by
  funext u
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp [neg_sub]

theorem contDiff_star_neg {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) :
    ContDiff ℝ (⊤ : ENat) (fun v : E3 => (starRingEnd ℂ) (g (-v))) := by
  have h1 : ContDiff ℝ (⊤ : ENat) (fun v : E3 => g (-v)) :=
    hg.comp contDiff_neg
  exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp h1

/-- `autocorr g` is `C^∞` when `g` is. -/
theorem autocorr_contDiff {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) : ContDiff ℝ (⊤ : ENat) (autocorr g) := by
  have hL : LocallyIntegrable g volume := hg.continuous.locallyIntegrable
  have h := (hasCompactSupport_star_neg hgc).contDiff_convolution_right
    (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume) hL (contDiff_star_neg hg)
  rwa [← autocorr_eq_convolution_real g] at h

/-- `autocorr g` has compact support when `g` does. -/
theorem hasCompactSupport_autocorr {g : E3 → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport (autocorr g) := by
  have h := hgc.convolution (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
    (hasCompactSupport_star_neg hgc)
  rwa [← autocorr_eq_convolution_real g] at h

/-- The real part `𝒢 = re ∘ autocorr` of the autocorrelation is `C^∞`. -/
theorem reAutocorr_contDiff {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    ContDiff ℝ (⊤ : ENat) (fun u : E3 => (autocorr g u).re) :=
  Complex.reCLM.contDiff.comp (autocorr_contDiff hg hgc)

/-- The real part `𝒢 = re ∘ autocorr` has compact support. -/
theorem reAutocorr_hasCompactSupport {g : E3 → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport (fun u : E3 => (autocorr g u).re) :=
  (hasCompactSupport_autocorr hgc).comp_left (g := Complex.re) (by simp)

/-! ## 2. The Laplacian: coordinate form, translation and support -/

/-- `lapPt` is `Laplacian.laplacian` (the coordinate sum is the trace of the second derivative in
the standard orthonormal basis). -/
theorem lapPt_eq_laplacian {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) :
    lapPt f = Laplacian.laplacian f := by
  funext x
  rw [Work.BoseFixR.LocaliseProof.laplacian_eq_sum_dir hf x]
  rfl

/-- **The Laplacian commutes with translations.** -/
theorem laplacian_comp_sub (K : E3 → ℝ) (z : E3) :
    Laplacian.laplacian (fun y => K (y - z)) = fun x => Laplacian.laplacian K (x - z) := by
  funext x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := fun y => K (y - z))
      (EuclideanSpace.basisFun (Fin 3) ℝ),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := K)
      (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hshift : (fun y : E3 => K (y - z)) = fun y : E3 => K ((-z) + y) := by
    funext y
    rw [sub_eq_add_neg, add_comm]
  rw [hshift, iteratedFDeriv_comp_add_left]
  have hxz : (-z) + x = x - z := by rw [sub_eq_add_neg, add_comm]
  rw [hxz]

/-- The Laplacian of a `C^∞` function is `C^∞` (indeed, the Laplacian lowers the smoothness
index by two; we only need the `C^∞` case). -/
theorem contDiff_laplacian {f : E3 → ℝ} (hf : ContDiff ℝ (⊤ : ENat) f) :
    ContDiff ℝ (⊤ : ENat) (Laplacian.laplacian f) := by
  have h2 : ContDiff ℝ 2 f := hf.of_le (by decide)
  rw [funext fun x => Work.BoseFixR.LocaliseProof.laplacian_eq_sum_dir h2 x]
  refine ContDiff.sum fun k _ => ?_
  have hP : ContDiff ℝ (⊤ : ENat) (fun y : E3 => fderiv ℝ f y (BoseGases.kcStdBasis k)) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  exact (hP.fderiv_right (by simp)).clm_apply contDiff_const

/-- The Laplacian of a compactly supported `C²` function has compact support (its support is
contained in the support of the function). -/
theorem hasCompactSupport_laplacian {f : E3 → ℝ} (hf : ContDiff ℝ 2 f)
    (hcs : HasCompactSupport f) : HasCompactSupport (Laplacian.laplacian f) := by
  refine HasCompactSupport.of_support_subset_isCompact hcs fun x hx => ?_
  rw [Function.mem_support] at hx
  by_contra hx'
  apply hx
  rw [funext fun y => Work.BoseFixR.LocaliseProof.laplacian_eq_sum_dir hf y]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hsub : tsupport (fun y : E3 => fderiv ℝ f y (BoseGases.kcStdBasis k)) ⊆ tsupport f :=
    closure_minimal (fun y hy => by
      rw [Function.mem_support] at hy
      by_contra hy'
      exact hy (by rw [fderiv_of_notMem_tsupport ℝ hy']; rfl)) (isClosed_tsupport f)
  have hfx : fderiv ℝ (fun y : E3 => fderiv ℝ f y (BoseGases.kcStdBasis k)) x = 0 :=
    fderiv_of_notMem_tsupport ℝ fun h => hx' (hsub h)
  rw [hfx]
  simp

/-! ## 3. Green's first identity with the compact support on the second function -/

/-- **Green's first identity, compact support on the second factor.**  For `h` of class `C²` with
compact support and `W` of class `C¹` (no support condition),

    ∫ Δh·W = −∫ ⟪∇h, ∇W⟫ .

The boundary terms of the punctured-domain computation vanish because `∂ₖh` has compact support;
nothing is required of `W` beyond `C¹`. -/
theorem gradientIBP_right {h W : E3 → ℝ} (hh : ContDiff ℝ 2 h) (hhcs : HasCompactSupport h)
    (hW : ContDiff ℝ 1 W) :
    ∫ x, Laplacian.laplacian h x * W x
      = -(∫ x, inner ℝ (gradient h x) (gradient W x)) := by
  have hk : ∀ k : Fin 3,
      (∫ x, fderiv ℝ (fun y => fderiv ℝ h y (BoseGases.kcStdBasis k)) x (BoseGases.kcStdBasis k)
          * W x)
        = -(∫ x, fderiv ℝ h x (BoseGases.kcStdBasis k) * fderiv ℝ W x
            (BoseGases.kcStdBasis k)) := by
    intro k
    have hPcd : ContDiff ℝ 1 (fun y : E3 => fderiv ℝ h y (BoseGases.kcStdBasis k)) :=
      (hh.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hGcd : ContDiff ℝ 1 (fun x : E3 => fderiv ℝ h x (BoseGases.kcStdBasis k) * W x) :=
      hPcd.mul hW
    have hGcs : HasCompactSupport (fun x : E3 => fderiv ℝ h x (BoseGases.kcStdBasis k) * W x) :=
      (hhcs.fderiv_apply ℝ (BoseGases.kcStdBasis k)).mul_right
    have hFTC : (∫ x, fderiv ℝ (fun x : E3 => fderiv ℝ h x (BoseGases.kcStdBasis k) * W x) x
        (BoseGases.kcStdBasis k)) = 0 :=
      Work.BoseFixR.LocaliseProof.integral_fderiv_kcStdBasis_eq_zero hGcd hGcs k
    have hpt : ∀ x : E3,
        fderiv ℝ (fun x : E3 => fderiv ℝ h x (BoseGases.kcStdBasis k) * W x) x
            (BoseGases.kcStdBasis k)
          = fderiv ℝ h x (BoseGases.kcStdBasis k) * fderiv ℝ W x (BoseGases.kcStdBasis k)
            + fderiv ℝ (fun y => fderiv ℝ h y (BoseGases.kcStdBasis k)) x
                (BoseGases.kcStdBasis k) * W x := by
      intro x
      have hfun : (fun x : E3 => fderiv ℝ h x (BoseGases.kcStdBasis k) * W x)
          = (fun y : E3 => fderiv ℝ h y (BoseGases.kcStdBasis k)) * W := rfl
      rw [hfun, fderiv_mul (hPcd.differentiable (by norm_num) x)
        (hW.differentiable (by norm_num) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    have hintA : Integrable (fun x : E3 =>
        fderiv ℝ h x (BoseGases.kcStdBasis k) * fderiv ℝ W x (BoseGases.kcStdBasis k)) :=
      Continuous.integrable_of_hasCompactSupport
        (hPcd.continuous.mul ((hW.continuous_fderiv (by norm_num)).clm_apply continuous_const))
        ((hhcs.fderiv_apply ℝ (BoseGases.kcStdBasis k)).mul_right)
    have hintB : Integrable (fun x : E3 =>
        fderiv ℝ (fun y => fderiv ℝ h y (BoseGases.kcStdBasis k)) x (BoseGases.kcStdBasis k)
          * W x) :=
      Continuous.integrable_of_hasCompactSupport
        (((hPcd.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hW.continuous)
        (((hhcs.fderiv_apply ℝ (BoseGases.kcStdBasis k)).fderiv_apply ℝ
          (BoseGases.kcStdBasis k)).mul_right)
    have hsum0 : (∫ x, (fderiv ℝ h x (BoseGases.kcStdBasis k) * fderiv ℝ W x
          (BoseGases.kcStdBasis k)
        + fderiv ℝ (fun y => fderiv ℝ h y (BoseGases.kcStdBasis k)) x (BoseGases.kcStdBasis k)
            * W x)) = 0 := by
      rw [← hFTC]
      exact integral_congr_ae (Eventually.of_forall fun x => (hpt x).symm)
    rw [integral_add hintA hintB] at hsum0
    linarith
  have hLHS : (∫ x, Laplacian.laplacian h x * W x)
      = ∑ k : Fin 3,
          ∫ x, fderiv ℝ (fun y => fderiv ℝ h y (BoseGases.kcStdBasis k)) x
            (BoseGases.kcStdBasis k) * W x := by
    have hpt1 : (fun x : E3 => Laplacian.laplacian h x * W x)
        = fun x => (∑ k : Fin 3,
            fderiv ℝ (fun y => fderiv ℝ h y (BoseGases.kcStdBasis k)) x
              (BoseGases.kcStdBasis k)) * W x := by
      funext x
      rw [Work.BoseFixR.LocaliseProof.laplacian_eq_sum_dir hh x]
    have hpt2 : (fun x : E3 => (∑ k : Fin 3,
            fderiv ℝ (fun y => fderiv ℝ h y (BoseGases.kcStdBasis k)) x
              (BoseGases.kcStdBasis k)) * W x)
        = fun x => ∑ k : Fin 3,
            fderiv ℝ (fun y => fderiv ℝ h y (BoseGases.kcStdBasis k)) x
              (BoseGases.kcStdBasis k) * W x := by
      funext x
      rw [Finset.sum_mul]
    rw [hpt1, hpt2, integral_finsetSum]
    intro k _
    have hPcd : ContDiff ℝ 1 (fun y : E3 => fderiv ℝ h y (BoseGases.kcStdBasis k)) :=
      (hh.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact Continuous.integrable_of_hasCompactSupport
      (((hPcd.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hW.continuous)
      (((hhcs.fderiv_apply ℝ (BoseGases.kcStdBasis k)).fderiv_apply ℝ
        (BoseGases.kcStdBasis k)).mul_right)
  have hRHS : (∫ x, inner ℝ (gradient h x) (gradient W x))
      = ∑ k : Fin 3,
          ∫ x, fderiv ℝ h x (BoseGases.kcStdBasis k) * fderiv ℝ W x
            (BoseGases.kcStdBasis k) := by
    have hpt : (fun x : E3 => inner ℝ (gradient h x) (gradient W x))
        = fun x => ∑ k : Fin 3,
            fderiv ℝ h x (BoseGases.kcStdBasis k) * fderiv ℝ W x (BoseGases.kcStdBasis k) := by
      funext x
      rw [Work.BoseFixR.LocaliseProof.inner_eq_sum_kcStdBasis]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [inner_gradient_left, inner_gradient_left]
    rw [hpt, integral_finsetSum]
    intro k _
    have hPcd : ContDiff ℝ 1 (fun y : E3 => fderiv ℝ h y (BoseGases.kcStdBasis k)) :=
      (hh.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact Continuous.integrable_of_hasCompactSupport
      (hPcd.continuous.mul ((hW.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      ((hhcs.fderiv_apply ℝ (BoseGases.kcStdBasis k)).mul_right)
  rw [hLHS, hRHS, Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_neg_distrib]

/-- **Green's second identity on `ℝ³`.**  For `h` of class `C²` with compact support and any `W`
of class `C²`,

    ∫ h·ΔW = ∫ Δh·W .

Both sides equal `−∫ ⟪∇h, ∇W⟫`: the left by `GradientIBP` (compact support on `h`), the right by
`gradientIBP_right`. -/
theorem laplacian_mul_swap {h W : E3 → ℝ} (hh : ContDiff ℝ 2 h) (hhcs : HasCompactSupport h)
    (hW : ContDiff ℝ 2 W) :
    ∫ x, h x * Laplacian.laplacian W x = ∫ x, Laplacian.laplacian h x * W x := by
  rw [Work.BoseFixR.LocaliseProof.GradientIBP (hh.of_le (by norm_num)) hhcs hW,
    gradientIBP_right hh hhcs (hW.of_le (by norm_num))]

end Work.BoseBoxFock.Green
