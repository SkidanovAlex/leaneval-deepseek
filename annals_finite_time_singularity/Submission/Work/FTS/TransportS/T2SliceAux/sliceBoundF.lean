import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.OpenPkg.ProdOpen.PwOpen
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2SliceAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `sin(2·)^{-γ}`-weighted square of the mixed slot `D_z^bD_θf`, for `b ≤ 3`, is dominated
by the `ℋ⁴`-integrand of `f` (the slot `(i,j) = (1,b)` of the mixed sum, with `1 + b ≤ 4`,
padded by `(w z)² ≥ 1` at `z > 0`). -/
theorem mixed_one_slice_le {α : ℝ} {f : ℝ → ℝ → ℝ} {b : ℕ} (hb : b ≤ 3) {z σ : ℝ}
    (hz : 0 < z) (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed b 1 f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
  have hw1 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
    nlinarith [Work.H2.T1Q.one_le_w_of_pos hz]
  have hsnn : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hsin.le _
  calc (Work.Spaces.mixed b 1 f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.mixed b 1 f z σ) ^ 2
        * (1 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ ≤ (Work.Spaces.mixed b 1 f z σ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [one_mul]
        exact le_mul_of_one_le_left hsnn hw1
    _ = (Work.Spaces.mixed b 1 f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z σ hsin]
    _ ≤ Work.Spaces.HkIntegrand α 4 f z σ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z σ 1 b (by norm_num) (by omega)

/-- `f`-side slice bound: for `SmoothOpen f` and `HkMem α 4 f`, every `D_z^b f` with `b ≤ 3`
is bounded on each open `θ`-slice at a fixed `z > 0`.

Route (adapt `Work.H2.T1Q.sup_DzIter_three_le`, which is the `b = 3` case for `SmoothQuad`):
for `h := fun θ => DzIter b f z θ` use `Work.FTS.OpenPkg.ProdOpen.sob_theta_mean`; its two
hypotheses are
`∫_θ h² < ∞` (from the pure slot `∫_θ (h·w/sin(2θ)^{η/2})² < ∞`, i.e. `hmem.1 z hz.le` with
`Work.Spaces.sq_le_HkIntegrand_z α 4 f z · b`) and
`∫_θ (deriv h)² sin(2θ)^{2-γ} < ∞`, which equals `∫_θ (mixed b 1 f z θ)² sin(2θ)^{-γ}`
(use `Work.FTS.OpenPkg.ProdOpen.mixed_succ_eq_sin_pth` / `deriv_mixed_weight`, or the
`SmoothOpen`-class `D_θ`-commutation lemmas in `TransportS/SupDzAux/SdaAux.lean`) and follows
from the mixed slot `1 + b ≤ 4` of `hmem.1 z hz.le`. -/
theorem sliceBoundF (α : ℝ) (f : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ z : ℝ, 0 < z → ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℕ, b ≤ 3 →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.Spaces.DzIter b f z θ| ≤ K := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.OpenPkg.ProdOpen.sob_theta_mean
  intro z hz
  set J : ℝ := ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ with hJ
  have hgnn : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := by
    have hg : 0 < Work.Spaces.gam α - 1 := by
      rw [Work.Spaces.gam_sub_one]; linarith
    exact inv_nonneg.mpr hg.le
  -- ## the pointwise square bound, uniform in `b ≤ 3`
  have hcore : ∀ b : ℕ, b ≤ 3 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.DzIter b f z θ) ^ 2 ≤ C * (J + (Work.Spaces.gam α - 1)⁻¹ * J) := by
    intro b hb θ hθ
    have hcurry := (hf.DzIter b).curry_θ hz
    have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (fun θ' : ℝ => Work.Spaces.DzIter b f z θ')
          (deriv (fun θ' : ℝ => Work.Spaces.DzIter b f z θ') x) x :=
      fun x hx => ((hcurry.differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hx)).hasDerivAt
    have hcont : ContinuousOn (deriv (fun θ' : ℝ => Work.Spaces.DzIter b f z θ'))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h : ContinuousOn (fun σ : ℝ => Work.Spaces.pth (Work.Spaces.DzIter b f) z σ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hf.DzIter b).pth.curry_θ hz).continuousOn
      simpa only [Work.Spaces.pth] using h
    -- ## the two a.e. facts on the angular slices
    have haeEq : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
        (deriv (fun θ' : ℝ => Work.Spaces.DzIter b f z θ') σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
          = (Work.Spaces.mixed b 1 f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
      simpa only [Nat.zero_add, Work.Spaces.mixed_zero_right] using
        (Work.FTS.OpenPkg.ProdOpen.deriv_mixed_weight α hf b 0 hz hσ)
    have haeBd : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.mixed b 1 f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
      filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
      exact mixed_one_slice_le hb hz hσ
    -- ## integrability of the two slice functions
    have hint1 : IntegrableOn (fun σ : ℝ => (Work.Spaces.DzIter b f z σ) ^ 2)
        Work.Spaces.Iθ := by
      refine Integrable.mono' (hmem.1 z hz.le)
        (Work.H2.T1Q.aesm_Iθ_of_continuousOn (hcurry.continuousOn.pow 2)) ?_
      filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [Work.Spaces.mixed_zero_right] using
        Work.H2.T1Q.mixed_sq_le_HkIntegrand α hα f b 0 (by omega) hz hσ.1 hσ.2
    have hint2 : IntegrableOn
        (fun σ : ℝ => (deriv (fun θ' : ℝ => Work.Spaces.DzIter b f z θ') σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      refine Integrable.mono' (hmem.1 z hz.le) ?_ ?_
      · refine Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_
        have hbase : Continuous fun σ : ℝ => Real.sin (2 * σ) := by fun_prop
        exact (((hf.DzIter b).pth.curry_θ hz).continuousOn.pow 2).mul
          (hbase.continuousOn.rpow_const
            (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ))))
      · filter_upwards [haeEq, haeBd, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ he hbd hσ
        have hnn : 0 ≤ (deriv (fun θ' : ℝ => Work.Spaces.DzIter b f z θ') σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) :=
          mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ).le _)
        calc ‖(deriv (fun θ' : ℝ => Work.Spaces.DzIter b f z θ') σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)‖
            = (deriv (fun θ' : ℝ => Work.Spaces.DzIter b f z θ') σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := Real.norm_of_nonneg hnn
          _ = (Work.Spaces.mixed b 1 f z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := he
          _ ≤ Work.Spaces.HkIntegrand α 4 f z σ := hbd
    -- ## the two integral bounds
    have hM1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z σ) ^ 2) ≤ J := by
      have h1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z σ) ^ 2)
          ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ :=
        MeasureTheory.integral_mono_ae (μ := volume.restrict Work.Spaces.Iθ) hint1
          (hmem.1 z hz.le) (by
            filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
            simpa only [Work.Spaces.mixed_zero_right] using
              Work.H2.T1Q.mixed_sq_le_HkIntegrand α hα f b 0 (by omega) hz hσ.1 hσ.2)
      rw [← hJ] at h1
      exact h1
    have hM2 : (∫ σ in Work.Spaces.Iθ,
        (deriv (fun θ' : ℝ => Work.Spaces.DzIter b f z θ') σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) ≤ J := by
      have hone : (∫ σ in Work.Spaces.Iθ,
          (deriv (fun θ' : ℝ => Work.Spaces.DzIter b f z θ') σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
          = ∫ σ in Work.Spaces.Iθ,
              (Work.Spaces.mixed b 1 f z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
        MeasureTheory.integral_congr_ae haeEq
      have h1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b 1 f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
          ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z σ :=
        MeasureTheory.integral_mono_ae (μ := volume.restrict Work.Spaces.Iθ)
          (Work.FTS.OpenPkg.ProdOpen.integrableOn_slice_neg_gam hα hf hmem b 1 le_rfl
            (by omega) hz)
          (hmem.1 z hz.le) haeBd
      rw [← hJ] at h1
      rw [hone]
      exact h1
    -- ## the mean-term inequality
    have hmain := hC α (fun θ' : ℝ => Work.Spaces.DzIter b f z θ') θ hα hα1 hθ
      hder hcont hint1 hint2
    have hstep : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * ∫ σ in Work.Spaces.Iθ,
              (deriv (fun θ' : ℝ => Work.Spaces.DzIter b f z θ') σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        ≤ J + (Work.Spaces.gam α - 1)⁻¹ * J :=
      add_le_add hM1 (mul_le_mul_of_nonneg_left hM2 hgnn)
    exact le_trans hmain (mul_le_mul_of_nonneg_left hstep hCpos.le)
  refine ⟨Real.sqrt (C * (J + (Work.Spaces.gam α - 1)⁻¹ * J)), Real.sqrt_nonneg _, ?_⟩
  intro b hb θ hθ
  calc |Work.Spaces.DzIter b f z θ|
      = Real.sqrt ((Work.Spaces.DzIter b f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (C * (J + (Work.Spaces.gam α - 1)⁻¹ * J)) :=
        Real.sqrt_le_sqrt (hcore b hb θ hθ)

end Work.FTS.TransportS.T2SliceAux
