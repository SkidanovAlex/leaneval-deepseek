import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.PkgJets.thetaBound
import Submission.Work.FTS_EllLimOK.ProducerH.thetaDivCos_aux
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

/-- **The per-slice bound for the explicit singular part `Θ α g / cos θ`.**  For `g` of class `C`,
`∫_θ HkIntegrand α 0 (Θ α g / cos θ) z θ ≤ C (1 + 1/z) (Xn6 α g)²` for every `z > 0`.
Route: `Θ α g z θ / cos θ = (1/(2α)) sin θ * L12 g z`, so the slice equals
`(1/(4α²)) (L12 g z)² w(z)² ∫_θ sin²θ sin(2θ)^{-η}dθ`; it therefore suffices to show
`(L12 g z)² w(z)² ≤ C (1 + 1/z) (Xn6 α g)²`, which is the mean value estimate applied to
`t ↦ (L12 g t)² w(t)²` on `[z,2z]`:
`(L12 g z)²w(z)² ≤ (1/z)∫_z^{2z}(L12 g t)²w(t)²dt + ∫_z^{2z}|d/dt((L12 g t)²w(t)²)|dt`,
with `∂_t L12 g = -FK g/t` (`L12_classC_facts`, `L12dens = FK/z`), `|w'/w| ≤ 2/t`, so
`|d/dt((L12 g)²w²)| ≤ (6/t)[(L12 g)²w² + (FK g)²w²]`; the global bounds
`∫(L12 g)²w² ≤ 107 BK² HkSq α 4 g` (`Work.FTS_EllLimOK.PkgJets.L12_w_sq_bound` together with
`FK_w_sq_bound`) and `∫(FK g)²w² ≤ BK² HkSq α 4 g`, plus `HkSq α 4 g ≤ HkSq α 6 g = (Xn6 α g)²`
(`HkSq_mono_le`), finish. -/
theorem thetaDivCos_slice {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0
            (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) z θ)
          ≤ C * (1 + 1 / z) * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
  -- the angular factor `Jη = ∫_θ sin(2θ)^{-η}`
  set J : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hJ
  have hJnn : 0 ≤ J := by
    rw [hJ]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
    exact Real.rpow_nonneg
      (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  set A : ℝ := (1 / (4 * α)) ^ 2 * 4 * J with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨A * (2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ A * (2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1) :=
      mul_nonneg hA0 (by positivity)
    linarith
  intro g hg z hz
  -- the two inputs: the angular estimate and the radial mean-value estimate
  have hslice := theta_slice_le hα g z
  have hrad := L12_w_sq_pointwise_aux hg z hz
  -- `HkSq α 4 g ≤ (Xn6 α g)²`
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS_EllLimOK.PkgJets.HkMem_mono_le hg.reg (by norm_num) hg.mem
  have hX6 : Work.Spaces.HkSq α 4 g ≤ (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
    have h := Work.FTS_EllLimOK.PkgJets.HkSq_mono_le (α := α) (f := g) (m := 4) (k := 6)
      (by norm_num) hmem6
    have h6 : Work.Spaces.HkSq α 6 g = (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
      show Work.Spaces.HkSq α 6 g = (Work.Spaces.HkNorm α 6 g) ^ 2
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 g)]
    linarith [h, h6.le]
  have hT2 : 0 ≤ (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := sq_nonneg _
  have h11 : 0 ≤ 1 + 1 / z := by
    have : 0 < 1 / z := one_div_pos.mpr hz
    linarith
  -- the slice bound, against the radial majorant
  have hmain : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0
          (fun z θ => Work.Construction.Theta α g z θ / Real.cos θ) z θ)
      ≤ A * (2000 * Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g / z) :=
    le_trans hslice (mul_le_mul_of_nonneg_left hrad hA0)
  -- the radial majorant against the claimed right-hand side
  have h1 : A * (2000 * Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g / z)
      ≤ A * ((2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1) * (1 + 1 / z)
          * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hA0
    have hz1 : 1 / z ≤ 1 + 1 / z := by linarith
    calc 2000 * Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g / z
        = (2000 * Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g) * (1 / z) := by ring
      _ ≤ (2000 * Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g) * (1 + 1 / z) :=
          mul_le_mul_of_nonneg_left hz1
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Work.Spaces.HkSq_nonneg α 4 g))
      _ ≤ (2000 * Work.FTS.GalBasis.cc.BK ^ 2 * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2)
            * (1 + 1 / z) := by
          have h2 : 2000 * Work.FTS.GalBasis.cc.BK ^ 2 * Work.Spaces.HkSq α 4 g
              ≤ 2000 * Work.FTS.GalBasis.cc.BK ^ 2 * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 :=
            mul_le_mul_of_nonneg_left hX6 (mul_nonneg (by norm_num) (sq_nonneg _))
          exact mul_le_mul_of_nonneg_right h2 h11
      _ ≤ ((2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1)
            * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2) * (1 + 1 / z) := by
          refine mul_le_mul_of_nonneg_right ?_ h11
          nlinarith [hT2]
      _ = (2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1) * (1 + 1 / z)
            * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by ring
  have h2 : A * ((2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1) * (1 + 1 / z)
        * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2)
      ≤ (A * (2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1) + 1) * (1 + 1 / z)
        * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by
    have hle : A * (2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1)
        ≤ A * (2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1) + 1 := by linarith
    have h0 : 0 ≤ (1 + 1 / z) * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := mul_nonneg h11 hT2
    calc A * ((2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1) * (1 + 1 / z)
          * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2)
        = (A * (2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1))
            * ((1 + 1 / z) * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2) := by ring
      _ ≤ (A * (2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1) + 1)
            * ((1 + 1 / z) * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2) :=
          mul_le_mul_of_nonneg_right hle h0
      _ = (A * (2000 * Work.FTS.GalBasis.cc.BK ^ 2 + 1) + 1) * (1 + 1 / z)
            * (Work.FTS.StrongGlobal.Xn6 α g) ^ 2 := by ring
  exact le_trans hmain (le_trans h1 h2)

end Work.FTS_EllLimOK.ProducerH
