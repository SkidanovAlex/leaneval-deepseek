/-
Auxiliary lemmas for `Work.FTS.TransportS.t2Slice` (the `θ`-slice integrability of the
easy part `Heasy` of the `D_z`-transport pairing in the open-quadrant hypothesis class).

Contents:

* `gamSlotLe`: the `sin(2θ)^{-γ}`-weighted square of a mixed slot of order `≤ 5` is dominated by
  the `ℋ⁵`-integrand;
* `sliceBoundF'`, `sliceBoundG'`: the pointwise boundedness of the `θ`-slices of the pure
  `f`-derivatives of order `≤ 3` resp. of all `g`-derivatives of order `≤ 4`, from the
  mean-term `θ`-Sobolev inequality `Work.FTS.OpenPkg.ProdOpen.sob_theta_mean`;
* `easyZ_sq_int'`, `easyM_sq_int'`: the squared blocks `EasyZ f g i` and `EasyM α f g j i` of
  `Heasy` are integrable on the `θ`-slice.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.T2SliceAux.sliceBoundF
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.OpenPkg.ProdOpen.PwOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.HkSq_terms

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

/-! ## The mixed slot with the `sin(2θ)^{-γ}` weight -/

/-- On the open angular interval, the `sin(2θ)^{-γ}`-weighted square of a mixed slot of order
`≤ 5` is dominated by the `ℋ⁵`-integrand of `g`. -/
theorem gamSlotLe {α : ℝ} {g : ℝ → ℝ → ℝ} {a b : ℕ} (ha : 1 ≤ a) (hab : a + b ≤ 5)
    {z σ : ℝ} (hz : 0 < z) (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed b a g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.Spaces.HkIntegrand α 5 g z σ := by
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
  have hw1 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
    nlinarith [Work.H2.T1Q.one_le_w_of_pos hz]
  have hsnn : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hsin.le _
  calc (Work.Spaces.mixed b a g z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.mixed b a g z σ) ^ 2
        * (1 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ ≤ (Work.Spaces.mixed b a g z σ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [one_mul]
        exact le_mul_of_one_le_left hsnn hw1
    _ = (Work.Spaces.mixed b a g z σ * Work.Spaces.Wt α z σ) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z σ hsin]
    _ ≤ Work.Spaces.HkIntegrand α 5 g z σ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z σ a b ha (by omega)

/-- The unweighted square of a mixed slot of order `≤ 5` is dominated by the `ℋ⁵`-integrand
of `g` (on the open angular interval). -/
theorem meanSlotLe {α : ℝ} {g : ℝ → ℝ → ℝ} {a b : ℕ} (hα : 0 < α) (hab : a + b ≤ 5)
    {z σ : ℝ} (hz : 0 < z) (hσ : σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    (Work.Spaces.mixed b a g z σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 5 g z σ := by
  have hsin : 0 < Real.sin (2 * σ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ
  have hw1 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
    nlinarith [Work.H2.T1Q.one_le_w_of_pos hz]
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [Work.Spaces.mixed_zero_right]
    have hs1 : Real.sin (2 * σ) ≤ 1 := Real.sin_le_one _
    have h1 : (1 : ℝ) ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) :=
      Work.H2.T1Q.one_le_rpow_neg hsin hs1 Work.Spaces.eta_nonneg
    have hrew : (Work.Spaces.DzIter b g z σ
          * (Work.Spaces.w z / (Real.sin (2 * σ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter b g z σ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_pow, Work.H2.T1Q.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * σ))
        Work.Spaces.eta hsin]
      ring
    have hz2 := Work.Spaces.sq_le_HkIntegrand_z α 5 g z σ b (by omega)
    rw [hrew] at hz2
    calc (Work.Spaces.DzIter b g z σ) ^ 2
        ≤ (Work.Spaces.DzIter b g z σ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) := by
          have h2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) := by nlinarith [hw1, h1]
          calc (Work.Spaces.DzIter b g z σ) ^ 2
              = (Work.Spaces.DzIter b g z σ) ^ 2 * 1 := by ring
            _ ≤ (Work.Spaces.DzIter b g z σ) ^ 2
                  * ((Work.Spaces.w z) ^ 2
                      * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta))) :=
                mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
            _ = (Work.Spaces.DzIter b g z σ) ^ 2 * (Work.Spaces.w z) ^ 2
                  * (Real.sin (2 * σ)) ^ (-(Work.Spaces.eta)) := by ring
      _ ≤ Work.Spaces.HkIntegrand α 5 g z σ := hz2
  · calc (Work.Spaces.mixed b a g z σ) ^ 2
        = (Work.Spaces.mixed b a g z σ) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.mixed b a g z σ) ^ 2 * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_left hw1 (sq_nonneg _)
      _ ≤ (Work.Spaces.mixed b a g z σ) ^ 2 * (Work.Spaces.Wt α z σ) ^ 2 :=
          mul_le_mul_of_nonneg_left (Work.H2.T1Q.w_sq_le_Wt_sq α hα
            ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩ hsin) (sq_nonneg _)
      _ = (Work.Spaces.mixed b a g z σ * Work.Spaces.Wt α z σ) ^ 2 := (mul_pow _ _ 2).symm
      _ ≤ Work.Spaces.HkIntegrand α 5 g z σ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z σ a b ha (by omega)

/-! ## The `g`-side slice bound -/

/-- `g`-side slice bound: for `SmoothOpen g` and `HkMem α 5 g`, every `D_z^b D_θ^a g` with
`a + b ≤ 4` is bounded on each open `θ`-slice at a fixed `z > 0`. -/
theorem sliceBoundG' (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 5 g) :
    ∀ z : ℝ, 0 < z → ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℕ, a + b ≤ 4 →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |Work.Spaces.mixed b a g z θ| ≤ K := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.OpenPkg.ProdOpen.sob_theta_mean
  intro z hz
  set J : ℝ := ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 g z σ with hJ
  have hgnn : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ := by
    have hg1 : 0 < Work.Spaces.gam α - 1 := by
      rw [Work.Spaces.gam_sub_one]; linarith
    exact inv_nonneg.mpr hg1.le
  have hcore : ∀ a b : ℕ, a + b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.mixed b a g z θ) ^ 2 ≤ C * (J + (Work.Spaces.gam α - 1)⁻¹ * J) := by
    intro a b hab θ hθ
    have hcurry := (hg.mixed b a).curry_θ hz
    have hder : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed b a g z θ')
          (deriv (fun θ' : ℝ => Work.Spaces.mixed b a g z θ') x) x :=
      fun x hx => ((hcurry.differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hx)).hasDerivAt
    have hcont : ContinuousOn (deriv (fun θ' : ℝ => Work.Spaces.mixed b a g z θ'))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h : ContinuousOn (fun σ : ℝ => Work.Spaces.pth (Work.Spaces.mixed b a g) z σ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := ((hg.mixed b a).pth.curry_θ hz).continuousOn
      simpa only [Work.Spaces.pth] using h
    have haeEq : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
        (deriv (fun θ' : ℝ => Work.Spaces.mixed b a g z θ') σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
          = (Work.Spaces.mixed b (a + 1) g z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by
      filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
      exact Work.FTS.OpenPkg.ProdOpen.deriv_mixed_weight α hg b a hz hσ
    have haeBd : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.mixed b (a + 1) g z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          ≤ Work.Spaces.HkIntegrand α 5 g z σ := by
      filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
      exact gamSlotLe (a := a + 1) (b := b) (by omega) (by omega) hz hσ
    have hint1 : IntegrableOn (fun σ : ℝ => (Work.Spaces.mixed b a g z σ) ^ 2)
        Work.Spaces.Iθ := by
      refine Integrable.mono' (hmem.1 z hz.le)
        (Work.H2.T1Q.aesm_Iθ_of_continuousOn (hcurry.continuousOn.pow 2)) ?_
      filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact meanSlotLe (a := a) (b := b) hα (by omega) hz hσ
    have hint2 : IntegrableOn
        (fun σ : ℝ => (deriv (fun θ' : ℝ => Work.Spaces.mixed b a g z θ') σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      refine Integrable.mono' (hmem.1 z hz.le) ?_ ?_
      · refine Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_
        have hbase : Continuous fun σ : ℝ => Real.sin (2 * σ) := by fun_prop
        exact (((hg.mixed b a).pth.curry_θ hz).continuousOn.pow 2).mul
          (hbase.continuousOn.rpow_const
            (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ))))
      · filter_upwards [haeEq, haeBd, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ he hbd hσ
        have hnn : 0 ≤ (deriv (fun θ' : ℝ => Work.Spaces.mixed b a g z θ') σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) :=
          mul_nonneg (sq_nonneg _)
            (Real.rpow_nonneg (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ).le _)
        calc ‖(deriv (fun θ' : ℝ => Work.Spaces.mixed b a g z θ') σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)‖
            = (deriv (fun θ' : ℝ => Work.Spaces.mixed b a g z θ') σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) := Real.norm_of_nonneg hnn
          _ = (Work.Spaces.mixed b (a + 1) g z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := he
          _ ≤ Work.Spaces.HkIntegrand α 5 g z σ := hbd
    have hM1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a g z σ) ^ 2) ≤ J := by
      have h1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a g z σ) ^ 2)
          ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 g z σ :=
        MeasureTheory.integral_mono_ae (μ := volume.restrict Work.Spaces.Iθ) hint1
          (hmem.1 z hz.le) (by
            filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hσ
            exact meanSlotLe (a := a) (b := b) hα (by omega) hz hσ)
      rw [← hJ] at h1
      exact h1
    have hM2 : (∫ σ in Work.Spaces.Iθ,
        (deriv (fun θ' : ℝ => Work.Spaces.mixed b a g z θ') σ) ^ 2
          * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) ≤ J := by
      have hone : (∫ σ in Work.Spaces.Iθ,
          (deriv (fun θ' : ℝ => Work.Spaces.mixed b a g z θ') σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
          = ∫ σ in Work.Spaces.Iθ,
              (Work.Spaces.mixed b (a + 1) g z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
        MeasureTheory.integral_congr_ae haeEq
      have hint' : IntegrableOn
          (fun σ : ℝ => (Work.Spaces.mixed b (a + 1) g z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
        Integrable.mono' (hmem.1 z hz.le)
          (Work.H2.T1Q.aesm_Iθ_of_continuousOn
            (((hg.mixed b (a + 1)).curry_θ hz).continuousOn.pow 2 |>.mul
              (by
                have hbase : Continuous fun σ : ℝ => Real.sin (2 * σ) := by fun_prop
                exact hbase.continuousOn.rpow_const
                  (fun σ hσ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ))))))
          (by
            filter_upwards [haeBd, Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with σ hbd hσ
            have hnn : 0 ≤ (Work.Spaces.mixed b (a + 1) g z σ) ^ 2
                * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
              mul_nonneg (sq_nonneg _)
                (Real.rpow_nonneg (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hσ).le _)
            rwa [Real.norm_of_nonneg hnn])
      have h1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b (a + 1) g z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
          ≤ ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 5 g z σ :=
        MeasureTheory.integral_mono_ae (μ := volume.restrict Work.Spaces.Iθ)
          hint' (hmem.1 z hz.le) haeBd
      rw [← hJ] at h1
      rw [hone]
      exact h1
    have hmain := hC α (fun θ' : ℝ => Work.Spaces.mixed b a g z θ') θ hα hα1 hθ
      hder hcont hint1 hint2
    have hstep : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.mixed b a g z σ) ^ 2)
          + (Work.Spaces.gam α - 1)⁻¹ * ∫ σ in Work.Spaces.Iθ,
              (deriv (fun θ' : ℝ => Work.Spaces.mixed b a g z θ') σ) ^ 2
                * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
        ≤ J + (Work.Spaces.gam α - 1)⁻¹ * J :=
      add_le_add hM1 (mul_le_mul_of_nonneg_left hM2 hgnn)
    exact le_trans hmain (mul_le_mul_of_nonneg_left hstep hCpos.le)
  refine ⟨Real.sqrt (C * (J + (Work.Spaces.gam α - 1)⁻¹ * J)), Real.sqrt_nonneg _, ?_⟩
  intro a b hab θ hθ
  calc |Work.Spaces.mixed b a g z θ|
      = Real.sqrt ((Work.Spaces.mixed b a g z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (C * (J + (Work.Spaces.gam α - 1)⁻¹ * J)) :=
        Real.sqrt_le_sqrt (hcore a b hab θ hθ)

/-! ## The slots of `HkIntegrand` on a slice -/

/-- The pure slot `D_z^j u` with the weight `sin(2θ)^{-η}` is integrable on the slice. -/
theorem pureSlotOn {α : ℝ} {k : ℕ} {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hmem : Work.Spaces.HkMem α k u) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter j u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ := by
  refine Integrable.mono' (hmem.1 z hz.le)
    (Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_) ?_
  · have hbase : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
    exact (((hu.DzIter j).curry_θ hz).continuousOn.pow 2).mul
      (hbase.continuousOn.rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ))))
  · filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
    have hsin : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ
    have hnn : 0 ≤ (Work.Spaces.DzIter j u z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
    rw [Real.norm_of_nonneg hnn]
    have hw1 : (1 : ℝ) ≤ Work.Spaces.w z := Work.H2.T1Q.one_le_w_of_pos hz
    have hw2 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
    have hrew : (Work.Spaces.DzIter j u z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter j u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [mul_pow, Work.H2.T1Q.div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ))
        Work.Spaces.eta hsin]
      ring
    have hkey := Work.Spaces.sq_le_HkIntegrand_z α k u z θ j hj
    rw [hrew] at hkey
    calc (Work.Spaces.DzIter j u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        = (Work.Spaces.DzIter j u z θ) ^ 2 * 1
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring
      _ ≤ (Work.Spaces.DzIter j u z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hsin.le _)
          exact mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
      _ ≤ Work.Spaces.HkIntegrand α k u z θ := hkey

/-- The mixed slot `D_z^bD_θ^a u` with the weight `sin(2θ)^{-γ}` is integrable on the slice. -/
theorem mixedSlotOn {α : ℝ} {k : ℕ} {u : ℝ → ℝ → ℝ} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hmem : Work.Spaces.HkMem α k u) (a b : ℕ) (ha : 1 ≤ a) (hab : a + b ≤ k)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed b a u z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  refine Integrable.mono' (hmem.1 z hz.le)
    (Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_) ?_
  · have hbase : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
    exact (((hu.mixed b a).curry_θ hz).continuousOn.pow 2).mul
      (hbase.continuousOn.rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ))))
  · filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
    have hsin : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ
    have hnn : 0 ≤ (Work.Spaces.mixed b a u z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
    rw [Real.norm_of_nonneg hnn]
    have hw1 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
      nlinarith [Work.H2.T1Q.one_le_w_of_pos hz]
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg hsin.le _
    calc (Work.Spaces.mixed b a u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Work.Spaces.mixed b a u z θ) ^ 2
          * (1 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ ≤ (Work.Spaces.mixed b a u z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          rw [one_mul]
          exact le_mul_of_one_le_left hsnn hw1
      _ = (Work.Spaces.mixed b a u z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α z θ hsin]
      _ ≤ Work.Spaces.HkIntegrand α k u z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α k u z θ a b ha hab

/-! ## The pointwise AM–GM bound for `Heasy` -/

/-- `2|a·b| ≤ a² + b²`. -/
theorem two_mul_abs_mul_le (a b : ℝ) : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- The same bound for an `if`-guarded product. -/
theorem two_mul_ite_abs_mul_le (c : Prop) [Decidable c] (a b : ℝ) :
    2 * |(if c then a * b else 0)| ≤ (if c then a ^ 2 else 0) + (if c then b ^ 2 else 0) := by
  by_cases h : c
  · rw [if_pos h, if_pos h, if_pos h]
    exact two_mul_abs_mul_le a b
  · rw [if_neg h, if_neg h, if_neg h]
    norm_num

/-- The algebra of the `EasyU`/`HkIntegrand` decomposition (without divisions). -/
theorem sum_split (s t : Finset ℕ) (F G : ℕ → ℝ) (H K : ℕ → ℕ → ℝ) :
    (∑ i ∈ s, (F i + G i)) + (∑ i ∈ s, ∑ j ∈ t, (H i j + K i j))
      = ((∑ i ∈ s, F i) + ∑ i ∈ s, ∑ j ∈ t, H i j)
        + ((∑ i ∈ s, G i) + ∑ i ∈ s, ∑ j ∈ t, K i j) := by
  have hF : (∑ i ∈ s, (F i + G i)) = ∑ i ∈ s, F i + ∑ i ∈ s, G i := Finset.sum_add_distrib
  have hH : (∑ i ∈ s, ∑ j ∈ t, (H i j + K i j))
      = (∑ i ∈ s, ∑ j ∈ t, H i j) + ∑ i ∈ s, ∑ j ∈ t, K i j := by
    have hinner : ∀ i, (∑ j ∈ t, (H i j + K i j)) = (∑ j ∈ t, H i j) + ∑ j ∈ t, K i j :=
      fun i => Finset.sum_add_distrib
    calc (∑ i ∈ s, ∑ j ∈ t, (H i j + K i j))
        = ∑ i ∈ s, ((∑ j ∈ t, H i j) + ∑ j ∈ t, K i j) := Finset.sum_congr rfl fun i _ => hinner i
      _ = (∑ i ∈ s, ∑ j ∈ t, H i j) + ∑ i ∈ s, ∑ j ∈ t, K i j := Finset.sum_add_distrib
  rw [hF, hH]
  ring

/-- On the open angular interval, the easy part of the pairing is dominated by half the sum of
the easy energy `EasyU α f g` and the `ℋ⁴`-integrand of `g`. -/
theorem heasy_abs_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Work.FTS.H2.Heasy α f g z θ|
      ≤ ((Work.FTS.H2.EasyU α f g z θ + Work.Spaces.HkIntegrand α 4 g z θ) / 2) := by
  have hZ : 2 * |∑ i ∈ Finset.range 5,
      Work.FTS.H2.EasyZ f g i z θ * Work.FTS.H2.GblkZ g i z θ|
      ≤ ∑ i ∈ Finset.range 5,
          ((Work.FTS.H2.EasyZ f g i z θ) ^ 2 + (Work.FTS.H2.GblkZ g i z θ) ^ 2) := by
    have h1 : |∑ i ∈ Finset.range 5,
        Work.FTS.H2.EasyZ f g i z θ * Work.FTS.H2.GblkZ g i z θ|
        ≤ ∑ i ∈ Finset.range 5,
          |Work.FTS.H2.EasyZ f g i z θ * Work.FTS.H2.GblkZ g i z θ| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : (2 : ℝ) * (∑ i ∈ Finset.range 5,
          |Work.FTS.H2.EasyZ f g i z θ * Work.FTS.H2.GblkZ g i z θ|)
        ≤ ∑ i ∈ Finset.range 5,
          ((Work.FTS.H2.EasyZ f g i z θ) ^ 2 + (Work.FTS.H2.GblkZ g i z θ) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => two_mul_abs_mul_le _ _
    calc 2 * |∑ i ∈ Finset.range 5,
          Work.FTS.H2.EasyZ f g i z θ * Work.FTS.H2.GblkZ g i z θ|
        ≤ 2 * (∑ i ∈ Finset.range 5,
          |Work.FTS.H2.EasyZ f g i z θ * Work.FTS.H2.GblkZ g i z θ|) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ _ := h2
  have hM : 2 * |∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          Work.FTS.H2.EasyM α f g j i z θ * Work.FTS.H2.GblkM α g j i z θ else 0)|
      ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          ((if 1 ≤ i ∧ i + j ≤ 4 then (Work.FTS.H2.EasyM α f g j i z θ) ^ 2 else 0)
            + (if 1 ≤ i ∧ i + j ≤ 4 then (Work.FTS.H2.GblkM α g j i z θ) ^ 2 else 0)) := by
    have h1 : |∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          Work.FTS.H2.EasyM α f g j i z θ * Work.FTS.H2.GblkM α g j i z θ else 0)|
        ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          |(if 1 ≤ i ∧ i + j ≤ 4 then
            Work.FTS.H2.EasyM α f g j i z θ * Work.FTS.H2.GblkM α g j i z θ else 0)| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
      exact Finset.abs_sum_le_sum_abs _ _
    have h2 : (2 : ℝ) * (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          |(if 1 ≤ i ∧ i + j ≤ 4 then
            Work.FTS.H2.EasyM α f g j i z θ * Work.FTS.H2.GblkM α g j i z θ else 0)|)
        ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          ((if 1 ≤ i ∧ i + j ≤ 4 then (Work.FTS.H2.EasyM α f g j i z θ) ^ 2 else 0)
            + (if 1 ≤ i ∧ i + j ≤ 4 then (Work.FTS.H2.GblkM α g j i z θ) ^ 2 else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => two_mul_ite_abs_mul_le _ _ _
    calc 2 * |∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            Work.FTS.H2.EasyM α f g j i z θ * Work.FTS.H2.GblkM α g j i z θ else 0)|
        ≤ 2 * (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          |(if 1 ≤ i ∧ i + j ≤ 4 then
            Work.FTS.H2.EasyM α f g j i z θ * Work.FTS.H2.GblkM α g j i z θ else 0)|) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ ≤ _ := h2
  have hmain : 2 * |Work.FTS.H2.Heasy α f g z θ|
      ≤ Work.FTS.H2.EasyU α f g z θ + Work.Spaces.HkIntegrand α 4 g z θ := by
    rw [Work.FTS.H2.HeasyBlocksId α f g z θ hθ]
    calc 2 * |(∑ i ∈ Finset.range 5,
            Work.FTS.H2.EasyZ f g i z θ * Work.FTS.H2.GblkZ g i z θ)
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then
                Work.FTS.H2.EasyM α f g j i z θ * Work.FTS.H2.GblkM α g j i z θ else 0)|
        ≤ 2 * (|∑ i ∈ Finset.range 5,
              Work.FTS.H2.EasyZ f g i z θ * Work.FTS.H2.GblkZ g i z θ|
            + |∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then
                Work.FTS.H2.EasyM α f g j i z θ * Work.FTS.H2.GblkM α g j i z θ else 0)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
      _ = 2 * |∑ i ∈ Finset.range 5,
              Work.FTS.H2.EasyZ f g i z θ * Work.FTS.H2.GblkZ g i z θ|
            + 2 * |∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then
                Work.FTS.H2.EasyM α f g j i z θ * Work.FTS.H2.GblkM α g j i z θ else 0)| := by
          ring
      _ ≤ _ := add_le_add hZ hM
      _ = Work.FTS.H2.EasyU α f g z θ + Work.Spaces.HkIntegrand α 4 g z θ := by
          rw [Work.FTS.H2.EasyU, Work.FTS.H2.HkIntegrand_eq_blocks]
          exact sum_split _ _ _ _ _ _
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by
    rw [mul_comm]
    exact hmain)

theorem smoothOpen_mul {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * g z θ) :=
  ContDiffOn.mul hf hg

/-- `D_z^n (D_z g) = D_z^{n+1} g`. -/
theorem DzIter_Dz (n : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter n (Work.Spaces.Dz g) = Work.Spaces.DzIter (n + 1) g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show Work.Spaces.Dz (Work.Spaces.DzIter k (Work.Spaces.Dz g))
        = Work.Spaces.Dz (Work.Spaces.DzIter (k + 1) g)
      rw [ih]

/-- A product `F² G² W` with bounded `F`, nonnegative `W` and integrable `G² W` is integrable. -/
theorem integrableOn_sq_mul_sq_of_bound {F G W : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), |F θ| ≤ K)
    (hW : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ W θ)
    (hG : MeasureTheory.IntegrableOn (fun θ => (G θ) ^ 2 * W θ) Work.Spaces.Iθ)
    (haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (F θ) ^ 2 * (G θ) ^ 2 * W θ) (volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (fun θ => (F θ) ^ 2 * (G θ) ^ 2 * W θ) Work.Spaces.Iθ := by
  refine MeasureTheory.Integrable.mono' (hG.const_mul (K ^ 2)) haesm ?_
  filter_upwards [hF, hW] with θ hFθ hWθ
  have hsq : (F θ) ^ 2 ≤ K ^ 2 := by
    have h := abs_le.mp hFθ
    nlinarith [h.1, h.2]
  have hnn : 0 ≤ (F θ) ^ 2 * (G θ) ^ 2 * W θ := by positivity
  rw [Real.norm_of_nonneg hnn]
  calc (F θ) ^ 2 * (G θ) ^ 2 * W θ = (F θ) ^ 2 * ((G θ) ^ 2 * W θ) := by ring
    _ ≤ K ^ 2 * ((G θ) ^ 2 * W θ) := mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = K ^ 2 * ((G θ) ^ 2 * W θ) := rfl

/-- A single summand `(D_z^b f)² (D_z^{i+1-b} g)² w² sin(2θ)^{-η}` of the `D_z`-block
expansion, `b ≤ i ≤ 4`, is integrable on the slice. -/
theorem easyZ_term_int {f g : ℝ → ℝ → ℝ} {Kf Kg : ℝ} {z : ℝ} (hz : 0 < z) (hKf : 0 ≤ Kf)
    (hKg : 0 ≤ Kg)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hFb : ∀ b : ℕ, b ≤ 3 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter b f z θ| ≤ Kf)
    (hGb : ∀ j : ℕ, j ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter j g z θ| ≤ Kg)
    (hFs : ∀ b : ℕ, b ≤ 4 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ)
    (hGs : ∀ j : ℕ, j ≤ 5 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter j g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ)
    (b i : ℕ) (hb : b ≤ i) (hi : i ≤ 4) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2
        * (Work.Spaces.DzIter (i + 1 - b) g z θ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
      Work.Spaces.Iθ := by
  by_cases hb3 : b ≤ 3
  · refine integrableOn_sq_mul_sq_of_bound (K := Kf) hKf ?_ ?_ ?_ ?_
    · filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
      exact hFb b hb3 θ hθ
    · filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ).le _)
    · refine ((hGs (i + 1 - b) (by omega)).mul_const ((Work.Spaces.w z) ^ 2)).congr ?_
      filter_upwards with θ
      ring
    · refine Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_
      have hbase : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
      exact ((((hf.DzIter b).curry_θ hz).continuousOn.pow 2).mul
        (((hg.DzIter (i + 1 - b)).curry_θ hz).continuousOn.pow 2)).mul
        (continuousOn_const.mul (hbase.continuousOn.rpow_const
          (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ)))))
  · have hb4 : b = 4 := by omega
    have hi4 : i = 4 := by omega
    subst hb4
    subst hi4
    have hstep : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 1 g z θ) ^ 2
        * (Work.Spaces.DzIter 4 f z θ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        Work.Spaces.Iθ := by
      refine integrableOn_sq_mul_sq_of_bound (F := fun θ => Work.Spaces.DzIter 1 g z θ)
        (G := fun θ => Work.Spaces.DzIter 4 f z θ)
        (W := fun θ => (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (K := Kg) hKg ?_ ?_ ?_ ?_
      · filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
        exact hGb 1 (by norm_num) θ hθ
      · filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
        exact mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ).le _)
      · refine ((hFs 4 (by norm_num)).mul_const ((Work.Spaces.w z) ^ 2)).congr ?_
        filter_upwards with θ
        ring
      · refine Work.H2.T1Q.aesm_Iθ_of_continuousOn ?_
        have hbase : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
        exact ((((hg.DzIter 1).curry_θ hz).continuousOn.pow 2).mul
          (((hf.DzIter 4).curry_θ hz).continuousOn.pow 2)).mul
          (continuousOn_const.mul (hbase.continuousOn.rpow_const
            (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ)))))
    refine hstep.congr ?_
    filter_upwards with θ
    ring

/-- The dominating sum of the `D_z`-block expansion is integrable on the slice. -/
theorem easyZ_dom_int {f g : ℝ → ℝ → ℝ} {Kf Kg : ℝ} {z : ℝ} (hz : 0 < z) (hKf : 0 ≤ Kf)
    (hKg : 0 ≤ Kg)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hFb : ∀ b : ℕ, b ≤ 3 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter b f z θ| ≤ Kf)
    (hGb : ∀ j : ℕ, j ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter j g z θ| ≤ Kg)
    (hFs : ∀ b : ℕ, b ≤ 4 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ)
    (hGs : ∀ j : ℕ, j ≤ 5 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter j g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ)
    (i : ℕ) (hi : i ≤ 4) :
    MeasureTheory.IntegrableOn (fun θ => ∑ b ∈ Finset.range (i + 1),
        ((i.choose b : ℝ)) ^ 2
          * ((Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.DzIter (i + 1 - b) g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
      Work.Spaces.Iθ := by
  refine MeasureTheory.integrable_finsetSum _ fun b hb => ?_
  have hb' : b ≤ i := by have := Finset.mem_range.mp hb; omega
  exact (easyZ_term_int hz hKf hKg hf hg hFb hGb hFs hGs b i hb' hi).const_mul
    ((i.choose b : ℝ) ^ 2)

/-- The pointwise Cauchy–Schwarz bound for the `D_z`-block. -/
theorem easyZ_pt {f g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (i : ℕ) (hi : i ≤ 4) :
    (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) ^ 2
          * ((Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.DzIter (i + 1 - b) g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
  have hs : 0 ≤ Real.sin (2 * θ) := (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ).le
  have hW : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs _)
  have hexp : Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
      = ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (i + 1 - b) g z θ) := by
    rw [Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz i f (Work.Spaces.Dz g) hf hg.Dz z θ hz hθ.1 hθ.2]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' : b ≤ i := by have := Finset.mem_range.mp hb; omega
    have h1 : i - b + 1 = i + 1 - b := by omega
    rw [show Work.Spaces.DzIter (i - b) (Work.Spaces.Dz g) z θ
        = Work.Spaces.DzIter (i - b + 1) g z θ from
      congrFun (congrFun (DzIter_Dz (i - b) g) z) θ, h1]
  have hCS : (∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) *
        (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (i + 1 - b) g z θ)) ^ 2
      ≤ ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) ^ 2
            * ((Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.DzIter (i + 1 - b) g z θ) ^ 2)) := by
    have h0 : (∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (i + 1 - b) g z θ)) ^ 2
        ≤ ((Finset.range (i + 1)).card : ℝ) * ∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ)) * (Work.Spaces.DzIter b f z θ
              * Work.Spaces.DzIter (i + 1 - b) g z θ)) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h1 : (∑ b ∈ Finset.range (i + 1),
            (((i.choose b : ℝ)) * (Work.Spaces.DzIter b f z θ
              * Work.Spaces.DzIter (i + 1 - b) g z θ)) ^ 2)
        = ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ) ^ 2
            * ((Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.DzIter (i + 1 - b) g z θ) ^ 2)) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [Finset.card_range, h1, Nat.cast_add, Nat.cast_one] at h0
    exact h0

  rw [hexp]
  calc (∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) *
        (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (i + 1 - b) g z θ)) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ (((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1),
          ((i.choose b : ℝ) ^ 2
            * ((Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.DzIter (i + 1 - b) g z θ) ^ 2)))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul_of_nonneg_right hCS hW
    _ = ((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) ^ 2
          * ((Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.DzIter (i + 1 - b) g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring

/-- **The square of the `D_z`-block `EasyZ f g i` is integrable on the `θ`-slice** (`i ≤ 4`). -/
theorem easyZ_sq_int' (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg : ℝ) (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {z : ℝ} (hz : 0 < z)
    (hFb : ∀ b : ℕ, b ≤ 3 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter b f z θ| ≤ Kf)
    (hGb : ∀ j : ℕ, j ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.DzIter j g z θ| ≤ Kg)
    (hFs : ∀ b : ℕ, b ≤ 4 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ)
    (hGs : ∀ j : ℕ, j ≤ 5 → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter j g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ)
    (i : ℕ) (hi : i ≤ 4) :
    MeasureTheory.IntegrableOn (fun θ => (Work.FTS.H2.EasyZ f g i z θ) ^ 2) Work.Spaces.Iθ := by
  have whCont : ContinuousOn (fun θ => Work.FTS.H2.Whz z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hbase : Continuous fun θ : ℝ => Real.sin (2 * θ) := by fun_prop
    simp only [Work.FTS.H2.Whz]
    exact continuousOn_const.div
      (hbase.continuousOn.rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ))))
      (fun θ hθ => ne_of_gt (Real.rpow_pos_of_pos
        (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ) _))
  by_cases hi3 : i ≤ 3
  · have hEZ : Work.FTS.H2.EasyZ f g i
        = fun z θ => Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
            * Work.FTS.H2.Whz z θ := by
      rw [Work.FTS.H2.EasyZ]
      exact if_pos hi3
    have hdom : MeasureTheory.IntegrableOn (fun θ => ((i : ℝ) + 1) *
        ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) ^ 2
          * ((Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.DzIter (i + 1 - b) g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
        Work.Spaces.Iθ :=
      (easyZ_dom_int hz hKf hKg hf hg hFb hGb hFs hGs i hi).const_mul ((i : ℝ) + 1)
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · have h1 : ContinuousOn (fun θ => Work.Spaces.DzIter i
          (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        (((smoothOpen_mul hf hg.Dz).DzIter i).curry_θ hz).continuousOn
      have hfun : (fun θ => (Work.FTS.H2.EasyZ f g i z θ) ^ 2)
          = fun θ => (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
              * Work.FTS.H2.Whz z θ) ^ 2 := by
        funext θ
        exact congrArg (· ^ 2) (congrFun (congrFun hEZ z) θ)
      rw [hfun]
      exact Work.H2.T1Q.aesm_Iθ_of_continuousOn ((h1.mul whCont).pow 2)
    · filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hEZ, mul_pow,
        Work.FTS.H2.hbi_Whz_sq z θ (Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ).le]
      exact easyZ_pt hz hθ hf hg i hi
  · have hi4 : i = 4 := by omega
    have hEZ4 : Work.FTS.H2.EasyZ f g i
        = fun z θ => (Work.Spaces.DzIter 4 (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
            - f z θ * Work.Spaces.DzIter 5 g z θ) * Work.FTS.H2.Whz z θ := by
      rw [Work.FTS.H2.EasyZ]
      exact if_neg hi3
    have hdom1 : MeasureTheory.IntegrableOn (fun θ => 2 * (((i : ℝ) + 1) *
        ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) ^ 2
          * ((Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.DzIter (i + 1 - b) g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))))
        Work.Spaces.Iθ :=
      ((easyZ_dom_int hz hKf hKg hf hg hFb hGb hFs hGs i hi).const_mul ((i : ℝ) + 1)).const_mul 2
    have hdom2 : MeasureTheory.IntegrableOn (fun θ => 2 * (Kf ^ 2 *
        ((Work.Spaces.DzIter 5 g z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))))
        Work.Spaces.Iθ := by
      have h0 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 5 g z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
          Work.Spaces.Iθ := by
        refine ((hGs 5 (by norm_num)).mul_const ((Work.Spaces.w z) ^ 2)).congr ?_
        filter_upwards with θ
        ring
      exact (h0.const_mul (Kf ^ 2)).const_mul 2
    refine MeasureTheory.Integrable.mono' (hdom1.add hdom2) ?_ ?_
    · have h1 : ContinuousOn (fun θ => Work.Spaces.DzIter 4
          (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        (((smoothOpen_mul hf hg.Dz).DzIter 4).curry_θ hz).continuousOn
      have h2 : ContinuousOn (fun θ => f z θ * Work.Spaces.DzIter 5 g z θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        ((hf.curry_θ hz).continuousOn).mul (((hg.DzIter 5).curry_θ hz).continuousOn)
      have hfun : (fun θ => (Work.FTS.H2.EasyZ f g i z θ) ^ 2)
          = fun θ => ((Work.Spaces.DzIter 4 (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
              - f z θ * Work.Spaces.DzIter 5 g z θ) * Work.FTS.H2.Whz z θ) ^ 2 := by
        funext θ
        exact congrArg (· ^ 2) (congrFun (congrFun hEZ4 z) θ)
      rw [hfun]
      exact Work.H2.T1Q.aesm_Iθ_of_continuousOn (((h1.sub h2).mul whCont).pow 2)
    · filter_upwards [Work.FTS.OpenPkg.ProdOpen.ae_mem_Ioo_Iθ] with θ hθ
      have hsin : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ
      have hW : 0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin.le _)
      have h4i : Work.Spaces.DzIter 4 (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
          = Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ := by rw [hi4]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hEZ4, mul_pow,
        Work.FTS.H2.hbi_Whz_sq z θ hsin.le, h4i]
      have hpt := easyZ_pt (f := f) (g := g) hz hθ hf hg i hi
      have hfbd : |f z θ| ≤ Kf := hFb 0 (by norm_num) θ hθ
      have h1 : 2 * (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ 2 * (((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) ^ 2
              * ((Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.DzIter (i + 1 - b) g z θ) ^ 2
                  * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))) := by
        linarith [hpt]
      have h2 : 2 * (f z θ * Work.Spaces.DzIter 5 g z θ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ 2 * (Kf ^ 2 * ((Work.Spaces.DzIter 5 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))) := by
        have habs := abs_le.mp hfbd
        have hf2 : (f z θ) ^ 2 ≤ Kf ^ 2 := by nlinarith [habs.1, habs.2]
        calc 2 * (f z θ * Work.Spaces.DzIter 5 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            = 2 * ((f z θ) ^ 2 * ((Work.Spaces.DzIter 5 g z θ) ^ 2
                * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))) := by ring
          _ ≤ 2 * (Kf ^ 2 * ((Work.Spaces.DzIter 5 g z θ) ^ 2
                * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact mul_le_mul_of_nonneg_right hf2 (mul_nonneg (sq_nonneg _) hW)
      have hsq : (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
            - f z θ * Work.Spaces.DzIter 5 g z θ) ^ 2
          ≤ 2 * (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ) ^ 2
            + 2 * (f z θ * Work.Spaces.DzIter 5 g z θ) ^ 2 := by
        nlinarith [sq_nonneg (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
          + f z θ * Work.Spaces.DzIter 5 g z θ)]
      calc (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
            - f z θ * Work.Spaces.DzIter 5 g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          ≤ (2 * (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ) ^ 2
              + 2 * (f z θ * Work.Spaces.DzIter 5 g z θ) ^ 2)
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :=
            mul_le_mul_of_nonneg_right hsq hW
        _ = 2 * (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + 2 * (f z θ * Work.Spaces.DzIter 5 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
        _ ≤ 2 * (((i : ℝ) + 1) * ∑ b ∈ Finset.range (i + 1), ((i.choose b : ℝ)) ^ 2
              * ((Work.Spaces.DzIter b f z θ) ^ 2 * (Work.Spaces.DzIter (i + 1 - b) g z θ) ^ 2
                  * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))))
            + 2 * (Kf ^ 2 * ((Work.Spaces.DzIter 5 g z θ) ^ 2
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))) :=
            add_le_add h1 h2


end Work.FTS.TransportS.T2SliceAux
