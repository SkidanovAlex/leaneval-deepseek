import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Alpha4.Assembly
import Submission.Work.FTS.EllipticEst.Alpha4.Cut
import Submission.Work.FTS.EllipticEst.ZCuts.zCut_props
import Submission.Work.FTS.EllipticEst.interpol_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false

/-! ## Outer integrability of the cut slices

For a `SmoothOpenθ` function `G` (smooth on the open strip `(0,∞) × (-1, π/2+1)`, in
particular on a neighbourhood of the closed box `[δ,R] × [0,π/2]`), the `z`-slices of the
mixed iterates `D_z^j ∂_θ^i G` are bounded on the box, so every product of two of them,
integrated in `θ` against the integrable weight `σ θ = sin(2θ)^{-η}`, is bounded on the
support `[1/k², k²]` of the logarithmic cut-off `ζ = zc φ k`.  Multiplying by the bounded
weight `w²` and by `ζ` (which vanishes off the compact support) gives an integrable function
of `z` on `Iz = [0,∞)`.

This is the variant of `integrable_outer_cut_mixed` (which handles the *un-scaled* angular
operator `D_θ = sin(2θ) ∂_θ`, i.e. `mixed j i G = D_z^j D_θ^i G`) needed for the *plain*
angular derivatives `∂_θ^i G` that occur in the slices of the interpolation estimate. -/

theorem integrable_outer_cut_pthDz_pair {k : ℕ} (hk2 : 2 ≤ k) {φ : ℝ → ℝ} {K : ℝ}
    (hφK : Work.FTS.EllipticEst.IsZCut φ K) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G) (j₁ i₁ j₂ i₂ : ℕ) :
    MeasureTheory.Integrable
      (fun z => (zc φ k z) * (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.DzIter j₁ (Work.Spaces.pthIter i₁ G) z θ)
              * (Work.Spaces.DzIter j₂ (Work.Spaces.pthIter i₂ G) z θ)
              * Work.FTS.EllipticEst.thEta θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  obtain ⟨hζcd, hζzero, -, -, -⟩ := ZCuts.zCut_props hφK k hk2
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk2
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [hkR]
  have hab : (1 : ℝ) / (k : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [hk4]
  have hζsupp : ∀ z, z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) → zc φ k z = 0 :=
    fun z hz => zc_eq_zero_of_notMem hk1 (fun z' hz' hz'' => hζzero z' hz' hz'') hz
  have hcdζ : ContDiffOn ℝ 1 (zc φ k) (Set.Ioi 0) := zc_contDiffOn hζcd
  have hbox : ContinuousOn (Function.uncurry (fun z θ => zc φ k z *
      (Work.Spaces.DzIter j₁ (Work.Spaces.pthIter i₁ G) z θ
        * Work.Spaces.DzIter j₂ (Work.Spaces.pthIter i₂ G) z θ)))
      (Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ×ˢ Work.Spaces.Iθ) :=
    ContinuousOn.mul
      ((hcdζ.continuousOn).comp continuousOn_fst
        (fun p hp => lt_of_lt_of_le (by positivity) hp.1.1))
      ((continuousOn_box_pthDz (a := 1 / (k : ℝ) ^ 2) (b := (k : ℝ) ^ 2) hG j₁ i₁
          (by positivity)).mul
        (continuousOn_box_pthDz (a := 1 / (k : ℝ) ^ 2) (b := (k : ℝ) ^ 2) hG j₂ i₂
          (by positivity)))
  have hcont : ContinuousOn (Function.uncurry (fun z θ => zc φ k z *
      (Work.Spaces.DzIter j₁ (Work.Spaces.pthIter i₁ G) z θ
        * Work.Spaces.DzIter j₂ (Work.Spaces.pthIter i₂ G) z θ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ContinuousOn.mul
      ((hcdζ.continuousOn).comp continuousOn_fst (fun p hp => hp.1))
      ((continuousOn_quad_pthDz hG j₁ i₁).mul (continuousOn_quad_pthDz hG j₂ i₂))
  obtain ⟨Mb, -, hMb⟩ := Work.FTS.EllipticEst.ThetaU.exists_bound_box (δ := 1 / (k : ℝ) ^ 2)
    (R := (k : ℝ) ^ 2) (by positivity) hab hbox
  have h := Work.FTS.EllipticEst.ThetaU.integrable_outer_of_bound (δ := 1 / (k : ℝ) ^ 2)
    (R := (k : ℝ) ^ 2) (by positivity)
    (F := fun z θ => zc φ k z * (Work.Spaces.DzIter j₁ (Work.Spaces.pthIter i₁ G) z θ
        * Work.Spaces.DzIter j₂ (Work.Spaces.pthIter i₂ G) z θ)) hcont
    (fun z hz θ => by rw [hζsupp z hz]; ring)
    ⟨Mb, fun z hz θ hθ => hMb z hz θ hθ⟩
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (zc φ k z *
      (Work.Spaces.DzIter j₁ (Work.Spaces.pthIter i₁ G) z θ
        * Work.Spaces.DzIter j₂ (Work.Spaces.pthIter i₂ G) z θ))
      * Work.FTS.EllipticEst.thEta θ)
    = (zc φ k z) * (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter j₁ (Work.Spaces.pthIter i₁ G) z θ
            * Work.Spaces.DzIter j₂ (Work.Spaces.pthIter i₂ G) z θ)
            * Work.FTS.EllipticEst.thEta θ)
  rw [show (∫ θ in Work.Spaces.Iθ, (zc φ k z *
        (Work.Spaces.DzIter j₁ (Work.Spaces.pthIter i₁ G) z θ
          * Work.Spaces.DzIter j₂ (Work.Spaces.pthIter i₂ G) z θ))
        * Work.FTS.EllipticEst.thEta θ)
      = (zc φ k z) * (∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter j₁ (Work.Spaces.pthIter i₁ G) z θ
            * Work.Spaces.DzIter j₂ (Work.Spaces.pthIter i₂ G) z θ)
            * Work.FTS.EllipticEst.thEta θ) from by
    rw [show (fun θ => (zc φ k z *
          (Work.Spaces.DzIter j₁ (Work.Spaces.pthIter i₁ G) z θ
            * Work.Spaces.DzIter j₂ (Work.Spaces.pthIter i₂ G) z θ))
          * Work.FTS.EllipticEst.thEta θ)
        = fun θ => ((Work.Spaces.DzIter j₁ (Work.Spaces.pthIter i₁ G) z θ
            * Work.Spaces.DzIter j₂ (Work.Spaces.pthIter i₂ G) z θ)
            * Work.FTS.EllipticEst.thEta θ) * (zc φ k z) from by funext θ; ring,
      MeasureTheory.integral_mul_const]
    ring]
  ring

theorem cut_slices_integrable {k : ℕ} (hk2 : 2 ≤ k) {φ : ℝ → ℝ} {K : ℝ}
    (hφK : Work.FTS.EllipticEst.IsZCut φ K) {G : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) :
    MeasureTheory.Integrable
        (fun z => Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      MeasureTheory.Integrable
        (fun z => Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
              * Work.FTS.EllipticEst.thEta θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
      MeasureTheory.Integrable
        (fun z => Work.FTS.EllipticEst.Alpha4.zc φ k z * (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dz G z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hG : Work.FTS.EllipticEst.ThetaU.SmoothOpenθ G := hsm
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pow_two, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
      using integrable_outer_cut_pthDz_pair hk2 hφK hG 1 1 1 1
  · simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
      using integrable_outer_cut_pthDz_pair hk2 hφK hG 1 0 1 2
  · simpa only [pow_two, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
      Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
      using integrable_outer_cut_pthDz_pair hk2 hφK hG 1 0 1 0

end Work.FTS.EllipticEst.Alpha4
