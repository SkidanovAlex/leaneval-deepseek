/-
# `dzIter_w_mean_le5` — the mean-term form of the radial `D_z`-slot bound at level 5

This is the `4 ↦ 5` shift of the *proved* `Work.FTS.OpenPkg.WProdWin.dzIter_w_mean_le` and the
`6 ↦ 5` shift of the *proved* `Work.FTS.StrongPersist.H6Rows.wprod6.dzIter_w_mean_le6`: the
same proof, with `HkMem α 4 → HkMem α 5` (hence `d ≤ 3 → d ≤ 4`, since the `g`-slot `mixed d 1 g`
needs `1 + d ≤ 5`) and `HkIntegrand α 4 → HkIntegrand α 5`.

The only level-specific ingredient of the level-4/level-6 proofs is the domination of a single
mixed slot by the level-`k` integrand; here that is supplied by `dzIter_sq_le_HkIntegrand5`
below, a direct consequence of the level-generic `Work.Spaces.sq_le_HkIntegrand_z`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.H5.WProd5.Gmaj5
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.OpenPkg.ProdOpen.PwOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.SlicesOpen
import Submission.Work.FTS.H2.WPQ.Defs
import Submission.Work.H2.T1Q.PwBdQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5.WProd5

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- The squared radial slot `(D_z^d g)²` of order `d ≤ 5` is dominated by the level-`5`
integrand, on the open quadrant: `HkIntegrand α 5 g` contains the term
`(D_z^d g · w/ sin(2θ)^{η/2})²` and the multiplier is `≥ 1`
(`w z ≥ 1` and `sin(2θ)^{η/2} ≤ 1`). -/
private theorem dzIter_sq_le_HkIntegrand5 {α : ℝ} {g : ℝ → ℝ → ℝ} {d : ℕ} (hd : d ≤ 5)
    {z σ : ℝ} (hz : 0 < z) (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.DzIter d g z σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 5 g z σ := by
  have hsin : 0 < Real.sin (2 * σ) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hσ.1], by linarith [hσ.2, Real.pi_pos]⟩
  have hspos : 0 < (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hsin _
  have hsle : (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one hsin.le (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
  have hz2 : 0 < z ^ 2 := by positivity
  have hw : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div hz2]
    nlinarith
  have hmul : 1 ≤ Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    linarith
  calc (Work.Spaces.DzIter d g z σ) ^ 2
      ≤ (Work.Spaces.DzIter d g z σ) ^ 2
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hmul)
    _ = (Work.Spaces.DzIter d g z σ
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 5 g z σ :=
        Work.Spaces.sq_le_HkIntegrand_z α 5 g z σ d (by omega)

/-- **The mean-term form of the radial `D_z`-slot bound at level `5`.**

The literal `4 ↦ 5` shift of the *proved* `Work.FTS.OpenPkg.WProdWin.dzIter_w_mean_le`
(`Submission/Work/FTS/OpenPkg/WProdWin/dzIter_w_mean_le.lean`), and at the same time the
`6 ↦ 5` shift of the *proved* `Work.FTS.StrongPersist.H6Rows.WProd6.dzIter_w_mean_le6`
(`Submission/Work/FTS/StrongPersist/H6Rows/wprod6/dzIter_w_mean_le6.lean`): the same proof with
`HkMem α 4 → HkMem α 5` (so `d ≤ 3 → d ≤ 4`, since the `g`-slot `mixed d 1 g` needs
`1 + d ≤ 5`), and `HkIntegrand α 4 → HkIntegrand α 5`. -/
theorem dzIter_w_mean_le5 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g : ℝ → ℝ → ℝ) (d : ℕ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 5 g → d ≤ 4 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
        ≤ C * ((Work.Spaces.w z) ^ 2
              * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
            + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.OpenPkg.ProdOpen.sob_theta_mean
  refine ⟨C, hCpos, ?_⟩
  intro α g d hα hα1 hF hmem hd z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hwpos : 0 < Work.Spaces.w z := Work.FTS.OpenPkg.ProdOpen.w_pos_of_pos hz
  have hwne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwpos.ne'
  -- the angular slice `h = D_z^d g (z, ·)` and its weighted derivative square
  set F : ℝ → ℝ := fun σ : ℝ =>
    (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) with hFdef
  -- ### smoothness of the slice
  have hcurry := (hF.DzIter d).curry_θ hz
  have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun σ' : ℝ => Work.Spaces.DzIter d g z σ')
        (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') x) x :=
    fun x hx => ((hcurry.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hcont : ContinuousOn (deriv (fun σ' : ℝ => Work.Spaces.DzIter d g z σ'))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : ContinuousOn (fun σ : ℝ => Work.Spaces.pth (Work.Spaces.DzIter d g) z σ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hF.DzIter d).pth.curry_θ hz).continuousOn
    simpa only [Work.Spaces.pth] using h
  -- ### the a.e. identification of the derivative square with the mixed slot `(d,1)`
  have haeEq : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
      F σ = (Work.Spaces.mixed d 1 g z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    have h := Work.FTS.OpenPkg.ProdOpen.deriv_mixed_weight α hF d 0 hz hσ
    simpa only [hFdef, Nat.zero_add, Work.Spaces.mixed_zero_right] using h
  -- ### the weight identity: `(w z)² · (mixed d 1 g)² sin^{-γ} = (mixed d 1 g · W)²`
  have hkey : ∀ σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed d 1 g z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
        = (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2 := by
    intro σ hσ
    have hsin := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
    rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z σ hsin]
    ring
  have haeW : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w z) ^ 2 * F σ
        = (Work.Spaces.mixed d 1 g z σ * Work.Spaces.Wt α z σ) ^ 2 := by
    filter_upwards [haeEq, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ he hσ
    rw [he, hkey σ hσ]
  -- ### integrability of the two slice functions
  have hint1 : IntegrableOn (fun σ : ℝ => (Work.Spaces.DzIter d g z σ) ^ 2)
      Work.Spaces.Iθ := by
    refine Integrable.mono' (hmem.1 z hz.le)
      (Work.H2.T1Q.aesm_Iθ_of_continuousOn (hcurry.continuousOn.pow 2)) ?_
    filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact dzIter_sq_le_HkIntegrand5 (by omega) hz hσ
  have hint2 : IntegrableOn F Work.Spaces.Iθ := by
    refine Integrable.mono' ((hmem.1 z hz.le).const_mul ((Work.Spaces.w z) ^ 2)⁻¹) ?_ ?_
    · rw [hFdef]
      refine Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_
      have hbase : Continuous fun σ : ℝ => Real.sin (2 * σ) := by fun_prop
      exact (((hF.DzIter d).pth.curry_θ hz).continuousOn.pow 2).mul
        (hbase.continuousOn.rpow_const
          (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ))))
    · filter_upwards [haeEq, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ he hσ
      have hsin := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
      have hnn : 0 ≤ F σ := by
        rw [he]
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
      rw [Real.norm_of_nonneg hnn, he]
      have hX : (Work.Spaces.mixed d 1 g z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          = ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2
              * ((Work.Spaces.mixed d 1 g z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hwne, one_mul]
      rw [hX]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (sq_nonneg (Work.Spaces.w z)))
      rw [hkey σ hσ]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z σ 1 d (by norm_num) (by omega)
  -- ### the exact value of the derivative term: `(w z)² ∫ F = Aang α g d z`
  have hAang : (Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, F σ)
      = Work.FTS.H2.WPQ.Aang α g d z := by
    have hstep : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 * F σ)
        = (Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, F σ) :=
      MeasureTheory.integral_const_mul (μ := volume.restrict Work.Spaces.Iθ) _ _
    rw [← hstep, Work.FTS.H2.WPQ.Aang]
    exact MeasureTheory.integral_congr_ae haeW
  -- ### the angular inequality and the assembly
  have hmain := hC α (fun σ' : ℝ => Work.Spaces.DzIter d g z σ') θ hα hα1 hθ
    hder hcont hint1 hint2
  have hmain' : (Work.Spaces.DzIter d g z θ) ^ 2
      ≤ C * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * (∫ σ in Work.Spaces.Iθ, F σ)) := by
    simpa only [hFdef] using hmain
  calc (Work.Spaces.DzIter d g z θ * Work.Spaces.w z) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter d g z θ) ^ 2 := by ring
    _ ≤ (Work.Spaces.w z) ^ 2 * (C * ((∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * (∫ σ in Work.Spaces.Iθ, F σ))) :=
        mul_le_mul_of_nonneg_left hmain' (sq_nonneg _)
    _ = C * ((Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * ((Work.Spaces.w z) ^ 2
              * (∫ σ in Work.Spaces.Iθ, F σ))) := by ring
    _ = C * ((Work.Spaces.w z) ^ 2 * (∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter d g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * Work.FTS.H2.WPQ.Aang α g d z) := by rw [hAang]

end Work.FTS.StrongEps.H5.WProd5
