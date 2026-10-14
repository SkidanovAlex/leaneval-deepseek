import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.HQ.BadsummandQ
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.Vocab
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Work.Spaces

/-! ## The two Hardy bounds of the exceptional slot, in the interior class

`Work.Spaces.bt_f_bound`/`bt_g_bound` give these for `Spaces.SmoothNbhd` functions
(analyticity on a neighbourhood of the closed quadrant) with `VanishTheta`/`DecayInZ`; below
they are proved in the interior class `Work.FTS.Nonlin.RegQ` from the two one-dimensional Hardy
inequalities `Work.FTS.H2.HQ.HardyThetaQ` (angular) and `Work.FTS.H2.HQ.HardyZQ` (radial), the
boundary limits of `BdryTraces` (`Work.FTS.H2.HQ.BdryTraces.tendsto_theta_zero`,
`...tendsto_atTop_zero`) and the weight algebra `Work.FTS.H2.HQ.Wt_sq_quad`.

The `f`-side is the angular Hardy inequality applied to the `θ`-slice of `D_z^j f`
(`Work.FTS.H2.HQ.DthDzIterComm` identifies its derivative with the slot `mixed j 1 f`); the
`g`-side is the radial Hardy inequality applied to the `z`-slice of `D_θ g` (the identity
`mixed 1 1 g = D_z D_θ g` is definitional). -/

/-- The `D_θ`-Hardy bound for `D_z^j f` (the `f`-side of the exceptional slot). -/
def ThetaHardy (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) : Prop :=
  ∀ z ∈ Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
    (DzIter j f z θ) ^ 2 * (w z) ^ 2 ≤
      (100 / (gam α - 1)) * MeasureTheory.integral (MeasureTheory.volume.restrict Iθ)
        (fun s => (mixed j 1 f z s * Wt α z s) ^ 2)

/-- The radial Hardy bound for `D_θ g` (the `g`-side of the exceptional slot). -/
def RadialHardy (α : ℝ) (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ θ ∈ Iθ,
    MeasureTheory.IntegrableOn (fun z' => (mixed 1 1 g z' θ * Wt α z' θ) ^ 2) Iz →
    ∀ z ∈ Iz,
      (Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) ≤
        MeasureTheory.integral (MeasureTheory.volume.restrict Iz)
          (fun z' => (mixed 1 1 g z' θ * Wt α z' θ) ^ 2)

/-- The `θ`-Hardy bound for `D_z^j f`, `j ≤ 3`. -/
theorem bt_f_bound_quad (α : ℝ) (f : ℝ → ℝ → ℝ) (j : ℕ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.Nonlin.RegQ α 4 f) (hj : j ≤ 3) : ThetaHardy α f j := by
  have hsq : Work.FTS.LocData.SmoothQuad f := hreg.1
  have hmem : HkMem α 4 f := hreg.2.1
  have hb : Work.FTS.Nonlin.BdryTraces α 4 f := hreg.2.2
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  have hγ2 : (2 : ℝ) - gam α ≠ 0 := by rw [gam]; linarith [hα1]
  have hgam2 : -(gam α / 2) ≠ 0 := by rw [gam]; linarith
  intro z hz θ hθ
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    have h0 : (DzIter j f 0 θ) ^ 2 * (w 0) ^ 2 = 0 := by simp [w]
    rw [h0]
    exact mul_nonneg (div_nonneg (by norm_num) hγ.le) (integral_nonneg fun s => sq_nonneg _)
  · have hu : Work.FTS.LocData.SmoothQuad (DzIter j f) := hsq.DzIter j
    have hlim : Filter.Tendsto (fun θ' => DzIter j f z θ') (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      Work.FTS.H2.HQ.BdryTraces.tendsto_theta_zero hα hb (a := 0) (b := j) (by omega) hzpos
    have hbase : MeasureTheory.IntegrableOn (fun σ => (mixed j 1 f z σ * Wt α z σ) ^ 2) Iθ :=
      Work.FTS.H2.HQ.integrableOn_slice_mixed_Wt_sq α f hsq hmem j 1 le_rfl (by omega) hz
    have hwne : (w z) ^ 2 ≠ 0 := by
      have hwz : w z ≠ 0 := by
        rw [w]
        exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hzpos))
      positivity
    have hpt : ∀ σ ∈ Iθ, ((w z) ^ 2)⁻¹ * (mixed j 1 f z σ * Wt α z σ) ^ 2
        = (pth (DzIter j f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α) := by
      intro σ hσ
      by_cases hσi : σ ∈ Set.Ioo 0 (π / 2)
      · have hsin : 0 < Real.sin (2 * σ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith [hσi.1])
            (by linarith [hσi.2, Real.pi_pos])
        have hcomm : Dth (DzIter j f) z σ = mixed j 1 f z σ :=
          Work.FTS.H2.HQ.DthDzIterComm j f hsq z hz σ hσi
        have hW : (Wt α z σ) ^ 2 = (w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)) :=
          Work.FTS.H2.HQ.Wt_sq_quad α z σ hσi
        have hpow : (Real.sin (2 * σ)) ^ (2 - gam α)
            = (Real.sin (2 * σ)) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α)) := by
          rw [show (2 : ℝ) - gam α = 2 + (-(gam α)) by ring, Real.rpow_add hsin,
            Real.rpow_two]
        have hwz : w z ≠ 0 := by
          rw [w]
          exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hzpos))
        have hexp : ((w z) ^ 2)⁻¹ * ((Real.sin (2 * σ)) ^ 2 * (pth (DzIter j f) z σ) ^ 2
              * ((w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α))))
            = (pth (DzIter j f) z σ) ^ 2 * ((Real.sin (2 * σ)) ^ 2
                * (Real.sin (2 * σ)) ^ (-(gam α))) := by
          rw [show ((w z) ^ 2)⁻¹ * ((Real.sin (2 * σ)) ^ 2 * (pth (DzIter j f) z σ) ^ 2
                * ((w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(gam α))))
              = ((pth (DzIter j f) z σ) ^ 2 * ((Real.sin (2 * σ)) ^ 2
                    * (Real.sin (2 * σ)) ^ (-(gam α))))
                  * (((w z) ^ 2)⁻¹ * (w z) ^ 2) from by ring,
            inv_mul_cancel₀ (pow_ne_zero 2 hwz), mul_one]
        rw [show (mixed j 1 f z σ * Wt α z σ) ^ 2
              = (mixed j 1 f z σ) ^ 2 * (Wt α z σ) ^ 2 from by rw [mul_pow], hW,
            ← hcomm, Dth, mul_pow]
        rw [hexp, ← hpow]
      · have hsin0 : Real.sin (2 * σ) = 0 := by
          rcases eq_or_lt_of_le hσ.1 with h | h
          · rw [← h]; simp
          · have h2 : σ = π / 2 := le_antisymm hσ.2 (le_of_not_gt fun hlt => hσi ⟨h, hlt⟩)
            rw [h2, show 2 * (π / 2) = π by ring, Real.sin_pi]
        have h1 : (Real.sin (2 * σ)) ^ (2 - gam α) = 0 := by
          rw [hsin0, Real.zero_rpow hγ2]
        have h2 : Wt α z σ = 0 := by
          rw [Wt, wTheta, hsin0, Real.zero_rpow hgam2, mul_zero]
        rw [h1, h2]
        simp
    have hint : MeasureTheory.IntegrableOn (fun σ => (pth (DzIter j f) z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - gam α)) Iθ :=
      MeasureTheory.IntegrableOn.congr_fun (hbase.const_mul ((w z) ^ 2)⁻¹) hpt measurableSet_Icc
    have hH := Work.FTS.H2.HQ.HardyThetaQ α hα hα1 (DzIter j f) z hu (by show (-1 : ℝ) < z; linarith) hlim hint θ hθ
    have hIeq : MeasureTheory.integral (MeasureTheory.volume.restrict Iθ)
        (fun σ => (pth (DzIter j f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
        = ((w z) ^ 2)⁻¹ * MeasureTheory.integral (MeasureTheory.volume.restrict Iθ)
            (fun σ => (mixed j 1 f z σ * Wt α z σ) ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
          (fun σ hσ => (hpt σ hσ).symm))
    calc (DzIter j f z θ) ^ 2 * (w z) ^ 2
        ≤ (100 / (gam α - 1)) * MeasureTheory.integral (MeasureTheory.volume.restrict Iθ)
            (fun σ => (pth (DzIter j f) z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - gam α))
            * (w z) ^ 2 :=
          mul_le_mul_of_nonneg_right hH (sq_nonneg _)
      _ = (100 / (gam α - 1)) * MeasureTheory.integral (MeasureTheory.volume.restrict Iθ)
            (fun σ => (mixed j 1 f z σ * Wt α z σ) ^ 2) := by
          rw [hIeq]
          have hcc : ((w z) ^ 2)⁻¹ * ((w z) ^ 2) = 1 := inv_mul_cancel₀ hwne
          calc (100 / (gam α - 1))
                * (((w z) ^ 2)⁻¹ * MeasureTheory.integral (MeasureTheory.volume.restrict Iθ)
                    (fun σ => (mixed j 1 f z σ * Wt α z σ) ^ 2)) * (w z) ^ 2
              = (100 / (gam α - 1)) * MeasureTheory.integral (MeasureTheory.volume.restrict Iθ)
                  (fun σ => (mixed j 1 f z σ * Wt α z σ) ^ 2)
                  * (((w z) ^ 2)⁻¹ * (w z) ^ 2) := by ring
            _ = (100 / (gam α - 1)) * MeasureTheory.integral (MeasureTheory.volume.restrict Iθ)
                  (fun σ => (mixed j 1 f z σ * Wt α z σ) ^ 2) := by rw [hcc, mul_one]

/-- The radial Hardy bound for `D_θ g`. -/
theorem bt_g_bound_quad (α : ℝ) (g : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.Nonlin.RegQ α 4 g) : RadialHardy α g := by
  have hsq : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : HkMem α 4 g := hreg.2.1
  have hb : Work.FTS.Nonlin.BdryTraces α 4 g := hreg.2.2
  have hgam2 : -(gam α / 2) ≠ 0 := by rw [gam]; linarith
  intro θ hθ hint z hz
  rcases eq_or_ne (Real.sin (2 * θ)) 0 with hsin0 | hsinne
  · have hD : Dth g z θ = 0 := by rw [Dth, hsin0, zero_mul]
    rw [hD]
    have hzero : (0 : ℝ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) = 0 := by
      rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    rw [hzero]
    exact integral_nonneg fun s => sq_nonneg _
  · have hθi : θ ∈ Set.Ioo 0 (π / 2) := by
      refine ⟨?_, ?_⟩
      · rcases eq_or_lt_of_le hθ.1 with h | h
        · exact absurd (by rw [← h]; simp) hsinne
        · exact h
      · rcases eq_or_lt_of_le hθ.2 with h | h
        · exact absurd (by rw [h, show 2 * (π / 2) = π by ring, Real.sin_pi]) hsinne
        · exact h
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθi.1]) (by linarith [hθi.2, Real.pi_pos])
    have hcd : ContDiffOn ℝ 1 (fun z' => mixed 0 1 g z' θ) (Set.Ioi 0) := by
      have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => mixed 0 1 g z' θ)
          (Set.Ioi (-1)) := (hsq.mixed 0 1).curry_z hθi
      exact (h1.mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0))).of_le (by simp)
    have hdec : Filter.Tendsto (fun z' => mixed 0 1 g z' θ) Filter.atTop (nhds 0) :=
      Work.FTS.H2.HQ.BdryTraces.tendsto_atTop_zero hb (a := 1) (b := 0) (by norm_num) hθi
    have hwid : ∀ s : ℝ, (s * deriv (fun z' => mixed 0 1 g z' θ) s) ^ 2 * (w s) ^ 2
        = (Real.sin (2 * θ)) ^ (gam α) * (mixed 1 1 g s θ * Wt α s θ) ^ 2 := by
      intro s
      have hW := Work.FTS.H2.HQ.Wt_sq_quad α s θ hθi
      have hDz : mixed 1 1 g s θ = s * deriv (fun z' => mixed 0 1 g z' θ) s := rfl
      have h3 : (mixed 1 1 g s θ * Wt α s θ) ^ 2
          = (s * deriv (fun z' => mixed 0 1 g z' θ) s) ^ 2 * (w s) ^ 2
              * (Real.sin (2 * θ)) ^ (-(gam α)) := by
        rw [mul_pow, hW, hDz]
        ring
      have h4 : (Real.sin (2 * θ)) ^ (gam α) * (Real.sin (2 * θ)) ^ (-(gam α)) = 1 := by
        rw [← Real.rpow_add hsinpos, show gam α + -(gam α) = 0 by ring, Real.rpow_zero]
      rw [h3]
      calc (s * deriv (fun z' => mixed 0 1 g z' θ) s) ^ 2 * (w s) ^ 2
          = ((s * deriv (fun z' => mixed 0 1 g z' θ) s) ^ 2 * (w s) ^ 2)
              * ((Real.sin (2 * θ)) ^ (gam α) * (Real.sin (2 * θ)) ^ (-(gam α))) := by
            rw [h4, mul_one]
        _ = (Real.sin (2 * θ)) ^ (gam α) * ((s * deriv (fun z' => mixed 0 1 g z' θ) s) ^ 2
              * (w s) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by ring
    have hInt : MeasureTheory.IntegrableOn
        (fun s => (s * deriv (fun z' => mixed 0 1 g z' θ) s) ^ 2 * (w s) ^ 2) Iz := by
      have h1 : MeasureTheory.IntegrableOn
          (fun s => (Real.sin (2 * θ)) ^ (gam α) * (mixed 1 1 g s θ * Wt α s θ) ^ 2) Iz :=
        hint.const_mul _
      exact MeasureTheory.IntegrableOn.congr_fun h1 (fun s _ => (hwid s).symm) measurableSet_Ici
    have hIntEq : MeasureTheory.integral (MeasureTheory.volume.restrict Iz)
        (fun s => (s * deriv (fun z' => mixed 0 1 g z' θ) s) ^ 2 * (w s) ^ 2)
        = (Real.sin (2 * θ)) ^ (gam α) * MeasureTheory.integral
            (MeasureTheory.volume.restrict Iz)
            (fun z' => (mixed 1 1 g z' θ * Wt α z' θ) ^ 2) := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun s _ => hwid s))
    have hcont : ContinuousAt (fun z' => mixed 0 1 g z' θ) 0 :=
      ((hsq.mixed 0 1).curry_z hθi).continuousOn.continuousAt
        (isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 0))
    have hkey : ∀ z' ∈ Set.Ioi (0 : ℝ), (mixed 0 1 g z' θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        ≤ MeasureTheory.integral (MeasureTheory.volume.restrict Iz)
            (fun z'' => (mixed 1 1 g z'' θ * Wt α z'' θ) ^ 2) := by
      intro z' hz'
      have hZ := Work.FTS.H2.HQ.HardyZQ (fun z'' => mixed 0 1 g z'' θ) hcd hdec hInt z' hz'
      rw [hIntEq] at hZ
      have hstep := mul_le_mul_of_nonneg_right hZ
        (Real.rpow_nonneg hsinpos.le (-(gam α)))
      calc (mixed 0 1 g z' θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
          ≤ ((Real.sin (2 * θ)) ^ (gam α) * MeasureTheory.integral
              (MeasureTheory.volume.restrict Iz)
              (fun z'' => (mixed 1 1 g z'' θ * Wt α z'' θ) ^ 2))
              * (Real.sin (2 * θ)) ^ (-(gam α)) := hstep
        _ = MeasureTheory.integral (MeasureTheory.volume.restrict Iz)
              (fun z'' => (mixed 1 1 g z'' θ * Wt α z'' θ) ^ 2) := by
            have h4sin : (Real.sin (2 * θ)) ^ (gam α)
                * (Real.sin (2 * θ)) ^ (-(gam α)) = 1 := by
              rw [← Real.rpow_add hsinpos, show gam α + -(gam α) = 0 by ring, Real.rpow_zero]
            rw [show (Real.sin (2 * θ)) ^ (gam α) * (MeasureTheory.integral
                  (MeasureTheory.volume.restrict Iz)
                  (fun z'' => (mixed 1 1 g z'' θ * Wt α z'' θ) ^ 2))
                  * (Real.sin (2 * θ)) ^ (-(gam α))
                = MeasureTheory.integral (MeasureTheory.volume.restrict Iz)
                    (fun z'' => (mixed 1 1 g z'' θ * Wt α z'' θ) ^ 2)
                    * ((Real.sin (2 * θ)) ^ (gam α) * (Real.sin (2 * θ)) ^ (-(gam α))) from by ring,
              h4sin, mul_one]
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have hlim2 : Filter.Tendsto (fun z' => (mixed 0 1 g z' θ) ^ 2) (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((mixed 0 1 g 0 θ) ^ 2)) :=
        (hcont.tendsto.mono_left nhdsWithin_le_nhds).pow 2
      have hev : ∀ᶠ z' in nhdsWithin 0 (Set.Ioi 0),
          (mixed 0 1 g z' θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
            ≤ MeasureTheory.integral (MeasureTheory.volume.restrict Iz)
                (fun z'' => (mixed 1 1 g z'' θ * Wt α z'' θ) ^ 2) := by
        filter_upwards [self_mem_nhdsWithin] with z' hz'
        exact hkey z' hz'
      have hlim3 : Filter.Tendsto (fun z' => (mixed 0 1 g z' θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(gam α))) (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((mixed 0 1 g 0 θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)))) :=
        hlim2.mul tendsto_const_nhds
      exact le_of_tendsto hlim3 hev
    · exact hkey z hzpos

private lemma integrableOn_finset_iSum {ι : Type*} (s : Finset ι) {φ : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, IntegrableOn (φ i) Iθ) : IntegrableOn (fun θ => ∑ i ∈ s, φ i θ) Iθ := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) Iθ)
  | insert a s ha ih =>
      have hfun : (fun θ => ∑ i ∈ insert a s, φ i θ)
          = (fun θ => φ a θ) + (fun θ => ∑ i ∈ s, φ i θ) := by
        funext θ; rw [Finset.sum_insert ha]; rfl
      rw [hfun]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- A finite sum of functions integrable on `Iz` is integrable on `Iz`. -/
private lemma integrableOn_finset_zSum {ι : Type*} (s : Finset ι) {φ : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, IntegrableOn (φ i) Iz) : IntegrableOn (fun z => ∑ i ∈ s, φ i z) Iz := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) Iz)
  | insert a s ha ih =>
      have hfun : (fun z => ∑ i ∈ insert a s, φ i z)
          = (fun z => φ a z) + (fun z => ∑ i ∈ s, φ i z) := by
        funext z; rw [Finset.sum_insert ha]; rfl
      rw [hfun]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))


/-- The `D_θ`-Hardy bound for `D_z^j f` (from `HQ/HardyThetaQ` + `BdryTraces`). -/
private theorem HProdQ_asm
    (hZ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ), 0 < α → α ≤ 1 →
      Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
      Work.FTS.H2.HQ.PwBd α f Cf → Work.FTS.H2.HQ.PwBd α g Cg → ∀ i ≤ 4,
        L2Mem (fun z θ => DzIter i (fun z θ => f z θ * g z θ) z θ
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2)))
        ∧ L2Sq (fun z θ => DzIter i (fun z θ => f z θ * g z θ) z θ
            * (w z / (Real.sin (2 * θ)) ^ (eta / 2)))
          ≤ C / (gam α - 1) * (Cf + Cg) * HkSq α 4 f * HkSq α 4 g)
    (hM : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ), 0 < α → α ≤ 1 →
      Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
      Work.FTS.H2.HQ.PwBd α f Cf → Work.FTS.H2.HQ.PwBd α g Cg →
      ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 4 → ¬ (j = 3 ∧ i = 1) →
        L2Mem (fun z θ => mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ)
        ∧ L2Sq (fun z θ => mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ)
          ≤ C / (gam α - 1) * (Cf + Cg) * HkSq α 4 f * HkSq α 4 g)
    (hBad : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Cf Cg : ℝ), 0 < α → α ≤ 1 →
      Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
      Work.FTS.H2.HQ.PwBd α f Cf → Work.FTS.H2.HQ.PwBd α g Cg →
      (L2Mem (fun z θ => DzIter 3 f z θ * Dth g z θ * Wt α z θ)
        ∧ L2Sq (fun z θ => DzIter 3 f z θ * Dth g z θ * Wt α z θ)
          ≤ 100 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g) →
      (L2Mem (fun z θ => Dth f z θ * DzIter 3 g z θ * Wt α z θ)
        ∧ L2Sq (fun z θ => Dth f z θ * DzIter 3 g z θ * Wt α z θ)
          ≤ 100 / (gam α - 1) * HkSq α 4 g * HkSq α 4 f) →
        L2Mem (fun z θ => mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ)
        ∧ L2Sq (fun z θ => mixed 3 1 (fun z θ => f z θ * g z θ) z θ * Wt α z θ)
          ≤ C / (gam α - 1) * (1 + Cf + Cg) * HkSq α 4 f * HkSq α 4 g)
    (hLinf : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ), 0 < α → α ≤ 1 →
      a + b ≤ 2 → Work.FTS.Nonlin.RegQ α 4 f → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < π / 2 →
        |mixed b a f z θ| ≤ C / Real.sqrt (gam α - 1) * Work.FTS.Nonlin.Xn α f)
    (hPkg : ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.LocData.SmoothQuad f → HkMem α 4 f →
      Work.FTS.LocData.SmoothQuad g → HkMem α 4 g →
      ThetaHardy α f 3 → RadialHardy α g →
        L2Mem (fun z θ => DzIter 3 f z θ * Dth g z θ * Wt α z θ)
        ∧ L2Sq (fun z θ => DzIter 3 f z θ * Dth g z θ * Wt α z θ)
          ≤ 100 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g)
    (hTf : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.Nonlin.RegQ α 4 f → ThetaHardy α f 3)
    (hTg : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.Nonlin.RegQ α 4 f → RadialHardy α f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
      0 < α → α ≤ 1 → Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
      HkMem α 4 (fun z θ => f z θ * g z θ)
        ∧ HkSq α 4 (fun z θ => f z θ * g z θ)
          ≤ C / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
  obtain ⟨Cz, hCz, hZ'⟩ := hZ
  obtain ⟨Cm, hCm, hM'⟩ := hM
  obtain ⟨Cb, hCb, hBad'⟩ := hBad
  obtain ⟨CL, hCL, hLinf'⟩ := hLinf
  have hCznn : 0 ≤ Cz := le_of_lt hCz
  have hCmnn : 0 ≤ Cm := le_of_lt hCm
  have hCbnn : 0 ≤ Cb := le_of_lt hCb
  have hCLnn : 0 ≤ CL := le_of_lt hCL
  let M : ℝ := max (Cz * (CL ^ 2 + CL ^ 2))
    (max (Cm * (CL ^ 2 + CL ^ 2)) (Cb * (1 + CL ^ 2 + CL ^ 2)))
  have hCFnn : 0 ≤ CL ^ 2 + CL ^ 2 := by positivity
  have hMnn : 0 ≤ M := by
    refine le_trans ?_ (le_max_left _ _)
    exact mul_nonneg hCznn hCFnn
  refine ⟨100 * M, by positivity, ?_⟩
  intro α f g hα hα1 hregf hregg
  have hsmf : Work.FTS.LocData.SmoothQuad f := hregf.1
  have hmemf : HkMem α 4 f := hregf.2.1
  have hbdryf : Work.FTS.Nonlin.BdryTraces α 4 f := hregf.2.2
  have hsmg : Work.FTS.LocData.SmoothQuad g := hregg.1
  have hmemg : HkMem α 4 g := hregg.2.1
  have hbdryg : Work.FTS.Nonlin.BdryTraces α 4 g := hregg.2.2
  have hγ : 0 < gam α - 1 := by rw [gam_sub_one]; linarith
  let FG : ℝ → ℝ → ℝ := fun z θ => f z θ * g z θ
  let Hw : ℝ → ℝ → ℝ := fun z θ => w z / (Real.sin (2 * θ)) ^ (eta / 2)
  let Zf : ℕ → ℝ → ℝ → ℝ := fun i z θ => DzIter i FG z θ * Hw z θ
  let Mf : ℕ → ℕ → ℝ → ℝ → ℝ := fun j i z θ => mixed j i FG z θ * Wt α z θ
  let K : ℝ := M / (gam α - 1) * HkSq α 4 f * HkSq α 4 g
  have hKnn : 0 ≤ K :=
    mul_nonneg (mul_nonneg (div_nonneg hMnn hγ.le) (HkSq_nonneg α 4 f)) (HkSq_nonneg α 4 g)
  -- the pointwise `L^∞`-bound packages of the interior Corollary
  have hpwf : Work.FTS.H2.HQ.PwBd α f (CL ^ 2) :=
    Work.FTS.H2.HQ.pwBd_of_pointwise α CL f hα hCLnn
      (fun b a hab z hz θ hθ0 hθ1 => hLinf' α f b a hα hα1 hab hregf z hz θ hθ0 hθ1)
  have hpwg : Work.FTS.H2.HQ.PwBd α g (CL ^ 2) :=
    Work.FTS.H2.HQ.pwBd_of_pointwise α CL g hα hCLnn
      (fun b a hab z hz θ hθ0 hθ1 => hLinf' α g b a hα hα1 hab hregg z hz θ hθ0 hθ1)
  -- the two bad-term packages
  have hbad1 : L2Mem (fun z θ => DzIter 3 f z θ * Dth g z θ * Wt α z θ)
      ∧ L2Sq (fun z θ => DzIter 3 f z θ * Dth g z θ * Wt α z θ)
        ≤ 100 / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
    hPkg α f g hα hα1 hsmf hmemf hsmg hmemg (hTf α f hα hα1 hregf) (hTg α g hα hα1 hregg)
  have hbad2 : L2Mem (fun z θ => Dth f z θ * DzIter 3 g z θ * Wt α z θ)
      ∧ L2Sq (fun z θ => Dth f z θ * DzIter 3 g z θ * Wt α z θ)
        ≤ 100 / (gam α - 1) * HkSq α 4 g * HkSq α 4 f := by
    obtain ⟨h1, h2⟩ :=
      hPkg α g f hα hα1 hsmg hmemg hsmf hmemf (hTf α g hα hα1 hregg) (hTg α f hα hα1 hregf)
    have heq : (fun z θ => Dth f z θ * DzIter 3 g z θ * Wt α z θ)
        = fun z θ => DzIter 3 g z θ * Dth f z θ * Wt α z θ := by
      funext z θ; ring
    rw [heq]
    exact ⟨h1, h2⟩
  -- the three summand bounds, all dominated by `K`
  have hZsummand : ∀ i ≤ 4, L2Mem (Zf i) ∧ L2Sq (Zf i) ≤ K := fun i hi => by
    obtain ⟨h1, h2⟩ := hZ' α f g (CL ^ 2) (CL ^ 2) hα hα1 hregf hregg hpwf hpwg i hi
    refine ⟨h1, le_trans h2 ?_⟩
    have hcoef : Cz * (CL ^ 2 + CL ^ 2) ≤ M := le_max_left _ _
    calc Cz / (gam α - 1) * (CL ^ 2 + CL ^ 2) * HkSq α 4 f * HkSq α 4 g
        = (Cz * (CL ^ 2 + CL ^ 2)) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring
      _ ≤ M / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoef hγ.le)
              (HkSq_nonneg α 4 f)) (HkSq_nonneg α 4 g)
      _ = K := rfl
  have hMsummand : ∀ j i, 1 ≤ i → i + j ≤ 4 → ¬ (j = 3 ∧ i = 1) →
      L2Mem (Mf j i) ∧ L2Sq (Mf j i) ≤ K := fun j i hi hij hne => by
    obtain ⟨h1, h2⟩ := hM' α f g (CL ^ 2) (CL ^ 2) hα hα1 hregf hregg hpwf hpwg j i hi hij hne
    refine ⟨h1, le_trans h2 ?_⟩
    have hcoef : Cm * (CL ^ 2 + CL ^ 2) ≤ M :=
      le_trans (le_max_left _ (Cb * (1 + CL ^ 2 + CL ^ 2)))
        (le_max_right (Cz * (CL ^ 2 + CL ^ 2)) _)
    calc Cm / (gam α - 1) * (CL ^ 2 + CL ^ 2) * HkSq α 4 f * HkSq α 4 g
        = (Cm * (CL ^ 2 + CL ^ 2)) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring
      _ ≤ M / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoef hγ.le)
              (HkSq_nonneg α 4 f)) (HkSq_nonneg α 4 g)
      _ = K := rfl
  have hBsummand : L2Mem (Mf 3 1) ∧ L2Sq (Mf 3 1) ≤ K := by
    obtain ⟨h1, h2⟩ := hBad' α f g (CL ^ 2) (CL ^ 2) hα hα1 hregf hregg hpwf hpwg hbad1 hbad2
    refine ⟨h1, le_trans h2 ?_⟩
    have hcoef : Cb * (1 + CL ^ 2 + CL ^ 2) ≤ M :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    calc Cb / (gam α - 1) * (1 + CL ^ 2 + CL ^ 2) * HkSq α 4 f * HkSq α 4 g
        = (Cb * (1 + CL ^ 2 + CL ^ 2)) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring
      _ ≤ M / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoef hγ.le)
              (HkSq_nonneg α 4 f)) (HkSq_nonneg α 4 g)
      _ = K := rfl
  have hZmem : ∀ i ≤ 4, ∀ z ∈ Iz, IntegrableOn (fun θ => (Zf i z θ) ^ 2) Iθ := by
    intro i hi z hz
    exact (hZsummand i hi).1.1 z hz
  have hZint : ∀ i ≤ 4, IntegrableOn (fun z => ∫ θ in Iθ, (Zf i z θ) ^ 2) Iz := by
    intro i hi
    exact (hZsummand i hi).1.2
  have hZbd : ∀ i ≤ 4, L2Sq (Zf i) ≤ K := fun i hi => (hZsummand i hi).2
  have hMmem : ∀ j i, 1 ≤ i → i + j ≤ 4 → ∀ z ∈ Iz,
      IntegrableOn (fun θ => (Mf j i z θ) ^ 2) Iθ := by
    intro j i hi hij z hz
    by_cases h31 : j = 3 ∧ i = 1
    · obtain ⟨rfl, rfl⟩ := h31; exact hBsummand.1.1 z hz
    · exact (hMsummand j i hi hij h31).1.1 z hz
  have hMint : ∀ j i, 1 ≤ i → i + j ≤ 4 →
      IntegrableOn (fun z => ∫ θ in Iθ, (Mf j i z θ) ^ 2) Iz := by
    intro j i hi hij
    by_cases h31 : j = 3 ∧ i = 1
    · obtain ⟨rfl, rfl⟩ := h31; exact hBsummand.1.2
    · exact (hMsummand j i hi hij h31).1.2
  have hMbd : ∀ j i, 1 ≤ i → i + j ≤ 4 → L2Sq (Mf j i) ≤ K := by
    intro j i hi hij
    by_cases h31 : j = 3 ∧ i = 1
    · obtain ⟨rfl, rfl⟩ := h31; exact hBsummand.2
    · exact (hMsummand j i hi hij h31).2
  have hZi : ∀ z ∈ Iz, ∀ i ∈ Finset.range 5, IntegrableOn (fun θ => (Zf i z θ) ^ 2) Iθ :=
    fun z hz i hi => hZmem i (by have h := Finset.mem_range.mp hi; omega) z hz
  have hMi : ∀ z ∈ Iz, ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      IntegrableOn (fun θ => (if 1 ≤ i ∧ i + j ≤ 4 then (Mf j i z θ) ^ 2 else 0)) Iθ := by
    intro z hz i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · exact (hMmem j i hc.1 (by omega) z hz).congr_fun
        (fun θ _ => by rw [if_pos hc]) measurableSet_Icc
    · exact integrableOn_zero.congr_fun (fun θ _ => by rw [if_neg hc]) measurableSet_Icc
  have hMzi : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      IntegrableOn (fun z => (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0)) Iz := by
    intro i hi j hj
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · exact (hMint j i hc.1 (by omega)).congr_fun
        (fun z _ => by rw [if_pos hc]) measurableSet_Ici
    · exact integrableOn_zero.congr_fun (fun z _ => by rw [if_neg hc]) measurableSet_Ici
  -- the numerical step, adapted to `K = M/(γ-1)·|f|²·|g|²`
  have hscalar : (30 : ℝ) * K ≤ 100 * M / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
    have hstep : (30 : ℝ) * M ≤ 100 * M := by linarith
    calc (30 : ℝ) * K
        = ((30 : ℝ) * M) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
          simp only [K]; ring
      _ ≤ (100 * M) / (gam α - 1) * HkSq α 4 f * HkSq α 4 g :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hstep hγ.le)
              (HkSq_nonneg α 4 f)) (HkSq_nonneg α 4 g)
      _ = 100 * M / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by ring
  -- the inner (θ-) decomposition
  have hinner_eq : ∀ z ∈ Iz, (∫ θ in Iθ, HkIntegrand α 4 FG z θ) =
      (∑ i ∈ Finset.range 5, ∫ θ in Iθ, (Zf i z θ) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0) := by
    intro z hz
    have hA : IntegrableOn (fun θ => ∑ i ∈ Finset.range 5, (Zf i z θ) ^ 2) Iθ :=
      integrableOn_finset_iSum _ fun i hi => hZi z hz i hi
    have hB : IntegrableOn (fun θ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then (Mf j i z θ) ^ 2 else 0)) Iθ :=
      integrableOn_finset_iSum _ fun i hi => integrableOn_finset_iSum _ fun j hj => hMi z hz i hi j hj
    have hstep1 : (∫ θ in Iθ, HkIntegrand α 4 FG z θ)
        = ∫ θ in Iθ, ((∑ i ∈ Finset.range 5, (Zf i z θ) ^ 2)
            + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
                (if 1 ≤ i ∧ i + j ≤ 4 then (Mf j i z θ) ^ 2 else 0)) := rfl
    have hstep2 : (∫ θ in Iθ, ((∑ i ∈ Finset.range 5, (Zf i z θ) ^ 2)
            + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
                (if 1 ≤ i ∧ i + j ≤ 4 then (Mf j i z θ) ^ 2 else 0)))
        = (∫ θ in Iθ, ∑ i ∈ Finset.range 5, (Zf i z θ) ^ 2)
          + ∫ θ in Iθ, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then (Mf j i z θ) ^ 2 else 0) :=
      MeasureTheory.integral_add hA hB
    have hstep3 : (∫ θ in Iθ, ∑ i ∈ Finset.range 5, (Zf i z θ) ^ 2)
          + ∫ θ in Iθ, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then (Mf j i z θ) ^ 2 else 0)
        = (∑ i ∈ Finset.range 5, ∫ θ in Iθ, (Zf i z θ) ^ 2)
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0) := by
      rw [MeasureTheory.integral_finsetSum (Finset.range 5) (fun i hi => hZi z hz i hi),
          MeasureTheory.integral_finsetSum (Finset.range 5)
            (fun i hi => integrableOn_finset_iSum _ fun j hj => hMi z hz i hi j hj)]
      have hcomp2 : (∑ i ∈ Finset.range 5, ∫ θ in Iθ, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then (Mf j i z θ) ^ 2 else 0))
          = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [MeasureTheory.integral_finsetSum (Finset.range 5) (fun j hj => hMi z hz i hi j hj)]
        refine Finset.sum_congr rfl fun j hj => ?_
        by_cases hc : 1 ≤ i ∧ i + j ≤ 4
        · rw [show (fun θ => (if 1 ≤ i ∧ i + j ≤ 4 then (Mf j i z θ) ^ 2 else 0))
              = fun θ => (Mf j i z θ) ^ 2
              from funext fun θ => if_pos hc]
          exact (if_pos hc).symm
        · rw [show (fun θ => (if 1 ≤ i ∧ i + j ≤ 4 then (Mf j i z θ) ^ 2 else 0))
              = fun _ => (0 : ℝ) from funext fun θ => if_neg hc, integral_zero]
          exact (if_neg hc).symm
      rw [hcomp2]
    exact hstep1.trans (hstep2.trans hstep3)
  -- the split of `HkSq`
  have hsplit : HkSq α 4 FG =
      (∑ i ∈ Finset.range 5, L2Sq (Zf i))
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then L2Sq (Mf j i) else 0) := by
    have hA : IntegrableOn (fun z => ∑ i ∈ Finset.range 5, ∫ θ in Iθ, (Zf i z θ) ^ 2) Iz :=
      integrableOn_finset_zSum _ fun i hi => hZint i (by have h := Finset.mem_range.mp hi; omega)
    have hB : IntegrableOn (fun z => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0)) Iz :=
      integrableOn_finset_zSum _ fun i hi => integrableOn_finset_zSum _ fun j hj => hMzi i hi j hj
    have hA' : ∀ i ∈ Finset.range 5, IntegrableOn (fun z => ∫ θ in Iθ, (Zf i z θ) ^ 2) Iz :=
      fun i hi => hZint i (by have h := Finset.mem_range.mp hi; omega)
    have hB' : ∀ i ∈ Finset.range 5, IntegrableOn (fun z => ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0)) Iz :=
      fun i hi => integrableOn_finset_zSum _ fun j hj => hMzi i hi j hj
    calc HkSq α 4 FG
        = ∫ z in Iz, (fun z => ∫ θ in Iθ, HkIntegrand α 4 FG z θ) z := rfl
      _ = ∫ z in Iz, ((∑ i ∈ Finset.range 5, ∫ θ in Iθ, (Zf i z θ) ^ 2)
            + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
                (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0)) :=
          MeasureTheory.setIntegral_congr_fun (s := Iz) (f := fun z => ∫ θ in Iθ, HkIntegrand α 4 FG z θ)
            measurableSet_Ici (fun z hz => hinner_eq z hz)
      _ = (∫ z in Iz, ∑ i ∈ Finset.range 5, ∫ θ in Iθ, (Zf i z θ) ^ 2)
          + ∫ z in Iz, ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0) :=
          MeasureTheory.integral_add hA hB
      _ = (∑ i ∈ Finset.range 5, ∫ z in Iz, ∫ θ in Iθ, (Zf i z θ) ^ 2)
          + ∑ i ∈ Finset.range 5, ∫ z in Iz, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0) := by
          rw [MeasureTheory.integral_finsetSum (Finset.range 5) hA',
              MeasureTheory.integral_finsetSum (Finset.range 5) hB']
      _ = (∑ i ∈ Finset.range 5, L2Sq (Zf i))
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then L2Sq (Mf j i) else 0) := by
          have hcomp1 : (∑ i ∈ Finset.range 5, ∫ z in Iz, ∫ θ in Iθ, (Zf i z θ) ^ 2)
              = ∑ i ∈ Finset.range 5, L2Sq (Zf i) :=
            Finset.sum_congr rfl fun i hi => rfl
          have hcomp2 : (∑ i ∈ Finset.range 5, ∫ z in Iz, ∑ j ∈ Finset.range 5,
                (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0))
              = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
                  (if 1 ≤ i ∧ i + j ≤ 4 then L2Sq (Mf j i) else 0) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [MeasureTheory.integral_finsetSum (Finset.range 5) (fun j hj => hMzi i hi j hj)]
            refine Finset.sum_congr rfl fun j hj => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ 4
            · rw [show (fun z => (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0))
                  = fun z => (∫ θ in Iθ, (Mf j i z θ) ^ 2)
                  from funext fun z => if_pos hc]
              exact (if_pos hc).symm
            · rw [show (fun z => (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0))
                  = fun _ => (0 : ℝ) from funext fun z => if_neg hc, integral_zero]
              exact (if_neg hc).symm
          rw [hcomp1, hcomp2]
  -- the bound
  have hbound : HkSq α 4 FG ≤ 100 * M / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := by
    rw [hsplit]
    have h1 : (∑ i ∈ Finset.range 5, L2Sq (Zf i)) ≤ ∑ i ∈ Finset.range 5, K :=
      Finset.sum_le_sum fun i hi =>
        hZbd i (by have h := Finset.mem_range.mp hi; omega)
    have h2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then L2Sq (Mf j i) else 0)) ≤
        ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, K := by
      refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · rw [if_pos hc]; exact hMbd j i hc.1 (by omega)
      · rw [if_neg hc]; exact hKnn
    have hsum2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, K) = 25 * K := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    calc (∑ i ∈ Finset.range 5, L2Sq (Zf i))
            + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
                (if 1 ≤ i ∧ i + j ≤ 4 then L2Sq (Mf j i) else 0)
        ≤ (∑ i ∈ Finset.range 5, K) + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, K :=
          add_le_add h1 h2
      _ = 5 * K + 25 * K := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
      _ = 30 * K := by ring
      _ ≤ 100 * M / (gam α - 1) * HkSq α 4 f * HkSq α 4 g := hscalar
  -- `HkMem`
  have hmemFG : HkMem α 4 FG := by
    constructor
    · intro z hz
      have hfun : (fun θ => HkIntegrand α 4 FG z θ)
          = fun θ => (∑ i ∈ Finset.range 5, (Zf i z θ) ^ 2) + ∑ i ∈ Finset.range 5,
              ∑ j ∈ Finset.range 5, (if 1 ≤ i ∧ i + j ≤ 4 then (Mf j i z θ) ^ 2 else 0) := rfl
      rw [hfun]
      exact (integrableOn_finset_iSum _ fun i hi => hZi z hz i hi).add
        (integrableOn_finset_iSum _ fun i hi =>
          integrableOn_finset_iSum _ fun j hj => hMi z hz i hi j hj)
    · have hsum : IntegrableOn (fun z => (∑ i ∈ Finset.range 5, ∫ θ in Iθ, (Zf i z θ) ^ 2)
          + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then (∫ θ in Iθ, (Mf j i z θ) ^ 2) else 0)) Iz :=
        (integrableOn_finset_zSum _ fun i hi =>
          hZint i (by have h := Finset.mem_range.mp hi; omega)).add
          (integrableOn_finset_zSum _ fun i hi => integrableOn_finset_zSum _ fun j hj =>
            hMzi i hi j hj)
      exact hsum.congr_fun (fun z hz => (hinner_eq z hz).symm) measurableSet_Ici
  exact ⟨hmemFG, hbound⟩

/-- Elgindi's `HProductRule` (tex 1068) in the *interior* class `Work.FTS.Nonlin.RegQ`. -/
theorem HProdQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
    Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
        ≤ C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g :=
  HProdQ_asm
    Work.FTS.H2.HQ.ZsummandQ
    Work.FTS.H2.HQ.MsummandQ
    Work.FTS.H2.HQ.BadsummandQ
    (by
      -- the interior Corollary `SecondDerivativesBounded`, with the two interior Hardy
      -- inequalities instantiated
      obtain ⟨C, hC, hL⟩ := Work.FTS.H2.HQ.LinfQpt
      exact ⟨C, hC, fun α f b a hα hα1 hab hreg z hz θ hθ0 hθ1 =>
        hL α f b a hα hα1 hab hreg
          (fun u z' hu hz' h0 hint =>
            Work.FTS.H2.HQ.HardyThetaQ α hα hα1 u z' hu hz' h0 hint)
          (fun v hcd hdec hint => Work.FTS.H2.HQ.HardyZQ v hcd hdec hint)
          z hz θ hθ0 hθ1⟩)
    (fun α f g hα hα1 hsmf hmemf hsmg hmemg hTf hTg =>
      Work.FTS.H2.HQ.BadPackageQ α f g hα hα1 hsmf hmemf hsmg hmemg hTf hTg)
    (fun α f hα hα1 hreg => bt_f_bound_quad α f 3 hα hα1 hreg (by norm_num))
    (fun α f hα hα1 hreg => bt_g_bound_quad α f hα hα1 hreg)

end Work.FTS.H2
