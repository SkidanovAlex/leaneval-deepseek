import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "Iθ" => Work.Spaces.Iθ
local notation "SS" => Work.FTS.EllipticEst.sEta
local notation "sg" => Work.Elliptic.sinCos2

/-! ## The angular weights `sEta = sin(2θ)^{-η}` and `sg = sinθcos²θ` -/

theorem ws_sEta_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ SS θ := by
  show 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  exact Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _


theorem ws_eta_nonneg : (0 : ℝ) ≤ Work.Spaces.eta := by norm_num [Work.Spaces.eta]

theorem ws_one_le_sEta {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : 1 ≤ SS θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have h := Real.rpow_le_rpow_of_nonpos hs (Real.sin_le_one (2 * θ))
    (neg_nonpos.mpr ws_eta_nonneg)
  rw [Real.one_rpow] at h
  exact h


theorem ws_sEta_integrableOn : MeasureTheory.IntegrableOn (fun θ => SS θ) Iθ :=
  (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
    (by norm_num [Work.Spaces.eta])).1

theorem ws_sEta_integral_nonneg : 0 ≤ ∫ θ in Iθ, SS θ :=
  MeasureTheory.integral_nonneg_of_ae <| by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    exact ws_sEta_nonneg hθ

theorem ws_sEta_integral_le : (∫ θ in Iθ, SS θ) ≤ 10000 := by
  have h := (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) (by norm_num [Work.Spaces.eta])
    (by norm_num [Work.Spaces.eta])).2
  have h2 : (100 : ℝ) / (-(Work.Spaces.eta) + 1) = 10000 := by norm_num [Work.Spaces.eta]
  rwa [h2] at h

theorem ws_vol_Iθ_ne_top : (MeasureTheory.volume Work.Spaces.Iθ) ≠ ⊤ := by
  have h : MeasureTheory.volume Work.Spaces.Iθ = ENNReal.ofReal (Real.pi / 2) := by
    show MeasureTheory.volume (Set.Icc 0 (Real.pi / 2)) = _
    rw [Real.volume_Icc]
    norm_num
  rw [h]; exact ENNReal.ofReal_ne_top

theorem ws_integral_one_Iθ : (∫ θ in Iθ, (1 : ℝ)) = Real.pi / 2 := by
  show (∫ θ in Set.Icc 0 (Real.pi / 2), (1 : ℝ)) = Real.pi / 2
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]
  rw [intervalIntegral.integral_const]
  ring

theorem ws_ae_mem_Ioo : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null (t := ({0, Real.pi / 2} : Set ℝ)) ?_ ?_
  · intro θ hθ
    simp only [Set.mem_setOf_eq] at hθ
    push_neg at hθ
    obtain ⟨hmem, hnot⟩ := hθ
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h0 : θ = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      by_contra hpi
      exact hnot ⟨lt_of_le_of_ne hmem.1 (Ne.symm h0), lt_of_le_of_ne hmem.2 hpi⟩
  · have hset : ({0, Real.pi / 2} : Set ℝ) = ({0} : Set ℝ) ∪ {Real.pi / 2} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton _)

theorem ws_sg_nonneg {θ : ℝ} (hθ : θ ∈ Iθ) : 0 ≤ sg θ := by
  rw [Work.Elliptic.sinCos2]
  exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])) (sq_nonneg _)

theorem ws_sg_le_one {θ : ℝ} (hθ : θ ∈ Iθ) : sg θ ≤ 1 := by
  rw [Work.Elliptic.sinCos2]
  nlinarith [Real.sin_le_one θ, Real.cos_sq_le_one θ, ws_sg_nonneg hθ,
    Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])]

/-- The exact identity `(a · (w/sin(2θ)^{η/2}))² = a² w² sin(2θ)^{-η}` on `Iθ`. -/
theorem ws_sq_div_sin (a w : ℝ) {θ : ℝ} (hθ : θ ∈ Iθ) :
    (a * (w / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = a ^ 2 * w ^ 2 * SS θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  show (a * (w / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = a ^ 2 * w ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]
    have h1 : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta])
    have h2 : (0 : ℝ) ^ (-(Work.Spaces.eta)) = 0 :=
      Real.zero_rpow (by norm_num [Work.Spaces.eta])
    rw [h1, h2]
    simp
  · have hsq : ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
        = (Real.sin (2 * θ)) ^ Work.Spaces.eta := by
      rw [sq, ← Real.rpow_add h]
      congr 1
      ring
    have hneg : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        = (((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)⁻¹ := by
      rw [hsq, Real.rpow_neg h.le]
    rw [hneg, mul_pow, div_pow, div_eq_mul_inv]
    ring

/-- `sEta` is continuous on the open quadrant. -/
theorem ws_contOn_sEta : ContinuousOn (fun p : ℝ × ℝ => SS p.2)
    Work.FTS.EllipticEst.Q0 := by
  show ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) _
  refine ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by have h := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.1
          show (0 : ℝ) < 2 * p.2
          linarith)
      (by have h := (Work.FTS.EllipticEst.mem_Q0.mp hp).2.2
          show 2 * p.2 < Real.pi
          linarith [Real.pi_pos]))))

/-! ## The angular energy `thetaE` -/

/-- The `θ`-energy of the family `X` at radius `s`: `∫_θ X(s,θ)² sin(2θ)^{-η}`. -/
def thetaE (X : ℝ → ℝ → ℝ) (s : ℝ) : ℝ := ∫ θ in Iθ, (X s θ) ^ 2 * SS θ

theorem thetaE_nonneg (X : ℝ → ℝ → ℝ) (s : ℝ) : 0 ≤ thetaE X s := by
  rw [thetaE]
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  exact mul_nonneg (sq_nonneg _) (ws_sEta_nonneg hθ)

/-- If `X(s,·)² ≤ M` on the open interval then `thetaE X s ≤ M · ∫ sEta`. -/
theorem thetaE_le_const {X : ℝ → ℝ → ℝ} {s M : ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (X s θ) ^ 2 ≤ M) :
    thetaE X s ≤ M * (∫ θ in Iθ, SS θ) := by
  rw [thetaE]
  have hS : MeasureTheory.IntegrableOn (fun θ => M * SS θ) Iθ :=
    ws_sEta_integrableOn.const_mul M
  have h0 : 0 ≤ᵐ[MeasureTheory.volume.restrict Iθ] (fun θ => (X s θ) ^ 2 * SS θ) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    exact mul_nonneg (sq_nonneg _) (ws_sEta_nonneg hθ)
  have hle : (fun θ => (X s θ) ^ 2 * SS θ) ≤ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => M * SS θ) := by
    filter_upwards [ws_ae_mem_Ioo] with θ hθ
    exact mul_le_mul_of_nonneg_right (h θ hθ)
      (ws_sEta_nonneg ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  calc (∫ θ in Iθ, (X s θ) ^ 2 * SS θ)
      ≤ ∫ θ in Iθ, M * SS θ := MeasureTheory.integral_mono_of_nonneg h0 hS hle
    _ = M * (∫ θ in Iθ, SS θ) := MeasureTheory.integral_const_mul M _

/-! ## Slices of `SmoothOpen` functions, and the `HkMem` slots -/

theorem ws_aesm_slice {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {u : ℝ} (hu : 0 < u) :
    MeasureTheory.AEStronglyMeasurable (fun θ => g u θ)
      (MeasureTheory.volume.restrict Iθ) :=
  Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hg.continuousOn hu

theorem ws_contDiffOn_slice {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    {u : ℝ} (hu : 0 < u) : ContDiffOn ℝ 2 (fun θ => g u θ) (Set.Ioo 0 (Real.pi / 2)) :=
  contDiffOn_iff_forall_nat_le.mp (hg.curry_θ hu) 2 le_top

theorem ws_pthIter_two_DzIter {g : ℝ → ℝ → ℝ} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pthIter 2 (Work.Spaces.DzIter i g) z θ
      = Work.Spaces.DzIter i (Work.Spaces.pthIter 2 g) z θ :=
  Work.EllipticEst.H2W.pthIter2_DzIter_comm hg i
    (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) from ⟨hz, hθ⟩)

/-- Every `D_z`-slot of an `ℋ^k`-function is `θ`-integrable with weight `sEta`. -/
theorem ws_slot_slice {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) {u : ℝ} (hu : 0 < u) :
    MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter i g u θ) ^ 2 * SS θ) Iθ := by
  have hI : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter i g u θ
      * (Work.Spaces.w u / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) Iθ :=
    Work.FTS.EllipticEst.integrableOn_zSummand α k hs hm i hi (Set.mem_Ici.mpr hu.le)
  have hw0 : (Work.Spaces.w u) ^ 2 ≠ 0 := by
    have h1 : 1 ≤ Work.Spaces.w u := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  refine ((hI.mul_const ((Work.Spaces.w u) ^ 2)⁻¹).congr ?_)
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  rw [ws_sq_div_sin (Work.Spaces.DzIter i g u θ) (Work.Spaces.w u) hθ]
  rw [show Work.Spaces.DzIter i g u θ ^ 2 * Work.Spaces.w u ^ 2 * SS θ
        * (Work.Spaces.w u ^ 2)⁻¹
      = Work.Spaces.DzIter i g u θ ^ 2 * SS θ
        * ((Work.Spaces.w u ^ 2) * (Work.Spaces.w u ^ 2)⁻¹) from by ring,
    mul_inv_cancel₀ hw0, mul_one]

/-- The `θ`-energy of a slot is radially integrable. -/
theorem ws_thetaE_integrable {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hs : Work.FTS.EllipticEst.SmoothOpen g) (hm : Work.Spaces.HkMem α k g)
    (i : ℕ) (hi : i ≤ k) {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun u => thetaE (Work.Spaces.DzIter i g) u) (Set.Ioc a b) := by
  have hIz := Work.FTS.EllipticEst.integrableOn_slice_Iz α k hs hm i hi
  have hcongr : (fun s => ∫ θ in Iθ, (Work.Spaces.DzIter i g s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun s => (Work.Spaces.w s) ^ 2 * thetaE (Work.Spaces.DzIter i g) s) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with s _
    show (∫ θ in Iθ, (Work.Spaces.DzIter i g s θ
        * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (Work.Spaces.w s) ^ 2 * (∫ θ in Iθ, (Work.Spaces.DzIter i g s θ) ^ 2 * SS θ)
    calc (∫ θ in Iθ, (Work.Spaces.DzIter i g s θ
          * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∫ θ in Iθ, (Work.Spaces.w s) ^ 2 * ((Work.Spaces.DzIter i g s θ) ^ 2 * SS θ) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
          rw [ws_sq_div_sin (Work.Spaces.DzIter i g s θ) (Work.Spaces.w s) hθ]
          ring
      _ = (Work.Spaces.w s) ^ 2 * (∫ θ in Iθ, (Work.Spaces.DzIter i g s θ) ^ 2 * SS θ) :=
          MeasureTheory.integral_const_mul _ _
  have hW : MeasureTheory.IntegrableOn
      (fun s => (Work.Spaces.w s) ^ 2 * thetaE (Work.Spaces.DzIter i g) s) (Set.Ioc a b) :=
    MeasureTheory.IntegrableOn.mono_set (hIz.congr hcongr)
      (fun s hs => Set.mem_Ici.mpr (le_of_lt (lt_trans ha hs.1)))
  have hw1 : ∀ s ∈ Set.Ioc a b, 1 ≤ (Work.Spaces.w s) ^ 2 := by
    intro s hs
    have hs0 : 0 < s := lt_trans ha hs.1
    have h1 : 1 ≤ Work.Spaces.w s := by
      rw [Work.Spaces.w, le_div_iff₀ (pow_pos hs0 2)]
      nlinarith
    nlinarith
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun u => thetaE (Work.Spaces.DzIter i g) u)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter i g p.1 p.2) ^ 2 * SS p.2)
        Work.FTS.EllipticEst.Q0 :=
      ((hs.DzIter i).continuousOn.pow 2).mul ws_contOn_sEta
    have h := (Work.FTS.EllipticEst.aesm_uncurry_restrict_open _ hcont
      (b := b) (le_of_lt ha)).integral_prod_right'
      (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
      (ν := MeasureTheory.volume.restrict Iθ)
    simpa only [thetaE, Function.uncurry_apply_pair] using h
  refine hW.mono' haesm ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with s hs
  have h0 : 0 ≤ thetaE (Work.Spaces.DzIter i g) s := thetaE_nonneg _ _
  rw [Real.norm_of_nonneg h0]
  nlinarith [hw1 s hs]

/-! ## The `sg`-moment is dominated by the `sEta`-energy -/

theorem ws_absMoment {g : ℝ → ℝ}
    (hgm : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Iθ))
    (hg : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * SS θ) Iθ) :
    MeasureTheory.IntegrableOn (fun θ => g θ * sg θ) Iθ ∧
      (∫ θ in Iθ, |g θ| * sg θ) ≤ Real.pi / 2 + ∫ θ in Iθ, (g θ) ^ 2 * SS θ := by
  have hpt : ∀ θ ∈ Iθ, |g θ| * sg θ ≤ (g θ) ^ 2 * SS θ + 1 := by
    intro θ hθ
    have hsg0 : 0 ≤ sg θ := ws_sg_nonneg hθ
    have hy : 2 * (|g θ| * sg θ) ≤ (g θ) ^ 2 + 1 := by
      have h1 : (sg θ) ^ 2 ≤ 1 := by nlinarith [ws_sg_le_one hθ, hsg0]
      have h2 : 2 * |g θ| * sg θ ≤ (|g θ|) ^ 2 + (sg θ) ^ 2 := by
        nlinarith [sq_nonneg (|g θ| - sg θ)]
      rw [sq_abs] at h2
      linarith
    rcases eq_or_lt_of_le (Work.Spaces.sin_two_nonneg_of_Iθ hθ) with hz | hpos
    · have hσ : sg θ = 0 := by
        have h3 : Real.sin θ * Real.cos θ = 0 := by
          have h4 := Real.sin_two_mul θ
          rw [show Real.sin (2 * θ) = 0 from hz.symm] at h4
          linarith
        rcases mul_eq_zero.mp h3 with hh | hh
        · show Real.sin θ * Real.cos θ ^ 2 = 0
          rw [hh]; ring
        · show Real.sin θ * Real.cos θ ^ 2 = 0
          rw [hh]; ring
      rw [hσ, mul_zero]
      have h2 : (0 : ℝ) ≤ (g θ) ^ 2 * SS θ := mul_nonneg (sq_nonneg _) (ws_sEta_nonneg hθ)
      linarith
    · have hθ0 : 0 < θ := by
        rcases lt_or_eq_of_le hθ.1 with h | h
        · exact h
        · rw [← h] at hpos
          simp only [mul_zero, Real.sin_zero] at hpos
          exact absurd hpos (lt_irrefl 0)
      have hθ2 : θ < Real.pi / 2 := by
        rcases lt_or_eq_of_le hθ.2 with h | h
        · exact h
        · rw [h] at hpos
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi] at hpos
          exact absurd hpos (lt_irrefl 0)
      have hsin1 : 1 ≤ SS θ := ws_one_le_sEta ⟨hθ0, hθ2⟩
      have h3 : 2 * (|g θ| * sg θ) ≤ (g θ) ^ 2 * SS θ + 1 := by
        have h4 : (g θ) ^ 2 * 1 ≤ (g θ) ^ 2 * SS θ :=
          mul_le_mul_of_nonneg_left hsin1 (sq_nonneg _)
        linarith
      have h5 : 0 ≤ |g θ| * sg θ := mul_nonneg (abs_nonneg _) hsg0
      linarith
  have hdom : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * SS θ + 1) Iθ :=
    hg.add (MeasureTheory.integrableOn_const ws_vol_Iθ_ne_top)
  have hsl : MeasureTheory.IntegrableOn (fun θ => g θ * sg θ) Iθ := by
    refine MeasureTheory.Integrable.mono' hdom (hgm.mul ?_) ?_
    · show MeasureTheory.AEStronglyMeasurable (fun θ => Real.sin θ * Real.cos θ ^ 2) _
      exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ws_sg_nonneg hθ)]
      exact hpt θ hθ
  refine ⟨hsl, ?_⟩
  have habs : MeasureTheory.IntegrableOn (fun θ => |g θ| * sg θ) Iθ :=
    hsl.norm.congr (by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ws_sg_nonneg hθ)])
  have h2 : (∫ θ in Iθ, |g θ| * sg θ)
      ≤ ∫ θ in Iθ, ((g θ) ^ 2 * SS θ + 1) :=
    MeasureTheory.integral_mono_ae habs hdom
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt θ hθ))
  have h3 : (∫ θ in Iθ, ((g θ) ^ 2 * SS θ + 1))
      = (∫ θ in Iθ, (g θ) ^ 2 * SS θ) + Real.pi / 2 := by
    rw [MeasureTheory.integral_add hg (MeasureTheory.integrableOn_const ws_vol_Iθ_ne_top),
      ws_integral_one_Iθ]
  rw [h3] at h2
  linarith [h2]

/-! ## The fundamental theorem of calculus on the open interval -/

theorem ws_ftc {v : ℝ → ℝ} (hv : ContDiffOn ℝ 1 v (Set.Ioo 0 (Real.pi / 2)))
    {a b : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (hb : b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    v b - v a = ∫ s in a..b, deriv v s := by
  have key : ∀ {c d : ℝ}, c ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      d ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → c ≤ d →
      v d - v c = ∫ s in c..d, deriv v s := by
    intro c d hc hd hcd
    have hsub : Set.Icc c d ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun z hz =>
      ⟨lt_of_lt_of_le hc.1 hz.1, lt_of_le_of_lt hz.2 hd.2⟩
    have hder : ∀ x ∈ Set.Ioo c d, HasDerivAt v (deriv v x) x := fun x hx =>
      (((hv.contDiffAt (isOpen_Ioo.mem_nhds
        (hsub ⟨le_of_lt hx.1, le_of_lt hx.2⟩)))).differentiableAt (by norm_num)).hasDerivAt
    have hcd2 : ContinuousOn (deriv v) (Set.uIcc c d) := by
      rw [Set.uIcc_of_le hcd]
      exact ((hv.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)).continuousOn.mono
        (fun z hz => hsub hz))
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcd
      (fun z hz => ((hv.contDiffAt (isOpen_Ioo.mem_nhds (hsub hz))).continuousAt).continuousWithinAt)
      hder hcd2.intervalIntegrable).symm
  rcases le_total a b with hle | hle
  · exact key ha hb hle
  · have h1 : v a - v b = ∫ s in b..a, deriv v s := key hb ha hle
    rw [intervalIntegral.integral_symm (a := b) (b := a), ← h1]
    ring

/-- **Weighted Cauchy–Schwarz over a subinterval.**  If `g` is square integrable on `(a,b]` and
`∫_{(a,b]} g² sEta ≤ E`, then `(∫_a^b g)² ≤ E · π/2`. -/
theorem ws_sq_integral_le {g : ℝ → ℝ} {a b E : ℝ} (hab : a ≤ b)
    (ha : 0 < a) (hb : b < Real.pi / 2) (hE0 : 0 ≤ E)
    (hg2 : MeasureTheory.IntegrableOn (fun s => (g s) ^ 2) (Set.Ioc a b))
    (hg : MeasureTheory.IntegrableOn (fun s => (g s) ^ 2 * SS s) (Set.Ioc a b))
    (hEbound : (∫ s in Set.Ioc a b, (g s) ^ 2 * SS s) ≤ E) :
    (∫ s in a..b, g s) ^ 2 ≤ E * (Real.pi / 2) := by
  have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc a b) :=
    MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (by simp)
  have hσi : MeasureTheory.IntegrableOn (fun s : ℝ => (1 : ℝ)⁻¹) (Set.Ioc a b) := by
    rw [inv_one]; exact hone
  have hcs := interval_integral_sq_le_mul hab (f := g) (σ := fun _ : ℝ => (1 : ℝ))
    (fun s _ => one_pos) (by simpa only [mul_one] using hg2) hσi
  have h1 : (∫ s in Set.Ioc a b, (g s) ^ 2) ≤ E := by
    have h2 : (∫ s in Set.Ioc a b, (g s) ^ 2) ≤ ∫ s in Set.Ioc a b, (g s) ^ 2 * SS s := by
      refine MeasureTheory.integral_mono_ae hg2 hg ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with s hs
      have h3 : 1 ≤ SS s := ws_one_le_sEta ⟨lt_trans ha hs.1, lt_of_le_of_lt hs.2 hb⟩
      nlinarith [sq_nonneg (g s)]
    linarith
  have h3 : (∫ s in a..b, g s) ^ 2
      ≤ (∫ s in Set.Ioc a b, (g s) ^ 2) * (b - a) := by
    have h4 : (∫ s in a..b, (g s) ^ 2 * 1) = ∫ s in Set.Ioc a b, (g s) ^ 2 := by
      rw [intervalIntegral.integral_of_le hab]
      simp
    have h5 : (∫ s in a..b, (1 : ℝ)⁻¹) = b - a := by
      rw [inv_one, intervalIntegral.integral_const]
      ring
    rw [h4, h5] at hcs
    exact hcs
  have h6 : 0 ≤ b - a := by linarith
  calc (∫ s in a..b, g s) ^ 2 ≤ (∫ s in Set.Ioc a b, (g s) ^ 2) * (b - a) := h3
    _ ≤ E * (Real.pi / 2) := by
        refine mul_le_mul h1 ?_ h6 hE0
        linarith [Real.pi_pos, hb, ha]


/-! ## The pointwise slice bound -/

theorem ws_slice_pointwise_le {v : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Ioo 0 (Real.pi / 2)))
    (hE : MeasureTheory.IntegrableOn (fun s => (deriv (fun t => deriv v t) s) ^ 2 * SS s) Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (v θ) ^ 2 ≤ 2 * (v (Real.pi / 4)) ^ 2
        + 4 * Real.pi ^ 2 * (1 + (∫ s in Iθ, SS s))
            * (1 + (deriv v (Real.pi / 4)) ^ 2
              + (∫ s in Iθ, (deriv (fun t => deriv v t) s) ^ 2 * SS s)) := by
  have hq0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hq : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hqI : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hq0, hq⟩
  set S : ℝ := ∫ s in Iθ, SS s with hSdef
  set E : ℝ := ∫ s in Iθ, (deriv (fun t => deriv v t) s) ^ 2 * SS s with hEdef
  have hS0 : 0 ≤ S := by rw [hSdef]; exact ws_sEta_integral_nonneg
  have hE0 : 0 ≤ E := by
    rw [hEdef]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with s hs
    exact mul_nonneg (sq_nonneg _) (ws_sEta_nonneg hs)
  have hv2_meas : MeasureTheory.AEStronglyMeasurable
      (fun s => (deriv (fun t => deriv v t) s) ^ 2)
      (MeasureTheory.volume.restrict Iθ) :=
    ((measurable_deriv (fun t => deriv v t)).pow_const 2).aestronglyMeasurable
  have hsqrt : Real.sqrt (E * (Real.pi / 2)) = Real.sqrt E * Real.sqrt (Real.pi / 2) :=
    Real.sqrt_mul hE0 _
  -- the oscillation bound on `v'`
  have hosc : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv v θ - deriv v (Real.pi / 4)| ≤ Real.sqrt E * Real.sqrt (Real.pi / 2) := by
    intro θ hθ
    have hv1 : ContDiffOn ℝ 1 (deriv v) (Set.Ioo 0 (Real.pi / 2)) :=
      hv.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
    have hftc := ws_ftc hv1 hqI hθ
    have hmain : ∀ {a b : ℝ}, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
        b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → a ≤ b →
        |∫ s in a..b, deriv (fun t => deriv v t) s|
          ≤ Real.sqrt E * Real.sqrt (Real.pi / 2) := by
      intro a b ha hb hab
      have hsub : Set.Ioc a b ⊆ Iθ := fun s hs =>
        ⟨le_of_lt (lt_trans ha.1 hs.1), le_of_lt (lt_of_le_of_lt hs.2 hb.2)⟩
      have hσ1 : ∀ s ∈ Set.Ioc a b, 1 ≤ SS s := fun s hs =>
        ws_one_le_sEta ⟨lt_trans ha.1 hs.1, lt_of_le_of_lt hs.2 hb.2⟩
      have hg : MeasureTheory.IntegrableOn
          (fun s => (deriv (fun t => deriv v t) s) ^ 2 * SS s) (Set.Ioc a b) :=
        hE.mono_set (fun s hs => hsub hs)
      have hg2 : MeasureTheory.IntegrableOn
          (fun s => (deriv (fun t => deriv v t) s) ^ 2) (Set.Ioc a b) := by
        refine MeasureTheory.Integrable.mono' hg
          (hv2_meas.mono_measure ?_) ?_
        · exact MeasureTheory.Measure.restrict_mono (fun s hs => hsub hs) le_rfl
        · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with s hs
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          nlinarith [sq_nonneg (deriv (fun t => deriv v t) s), hσ1 s hs]
      have hEb : (∫ s in Set.Ioc a b, (deriv (fun t => deriv v t) s) ^ 2 * SS s) ≤ E := by
        rw [hEdef]
        exact MeasureTheory.setIntegral_mono_set hE
          (by filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc]
                with s hs
              exact mul_nonneg (sq_nonneg _) (ws_sEta_nonneg hs))
          (Filter.Eventually.of_forall fun s hs => hsub hs)
      have hsq := ws_sq_integral_le hab ha.1 hb.2 hE0 hg2 hg hEb
      have h1 : Real.sqrt ((∫ s in a..b, deriv (fun t => deriv v t) s) ^ 2)
          ≤ Real.sqrt (E * (Real.pi / 2)) := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq_eq_abs, hsqrt] at h1
      exact h1
    rcases le_total (Real.pi / 4) θ with hle | hle
    · rw [hftc]; exact hmain hqI hθ hle
    · have h2 : deriv v θ - deriv v (Real.pi / 4)
          = -(∫ s in θ..Real.pi / 4, deriv (fun t => deriv v t) s) := by
        rw [hftc, intervalIntegral.integral_symm (a := θ) (b := Real.pi / 4)]
      rw [h2, abs_neg]
      exact hmain hθ hqI hle
  -- the value bound
  intro θ hθ
  set B : ℝ := |deriv v (Real.pi / 4)| + Real.sqrt E * Real.sqrt (Real.pi / 2) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    positivity
  have hBpt : ∀ s ∈ Set.uIoc (Real.pi / 4) θ, ‖deriv v s‖ ≤ B := by
    intro s hs
    rw [Set.uIoc] at hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      have h1 : s ∈ Set.Ioc (min (Real.pi / 4) θ) (max (Real.pi / 4) θ) := hs
      rw [Set.mem_Ioc] at h1
      exact ⟨lt_trans (lt_min hq0 hθ.1) h1.1, lt_of_le_of_lt h1.2 (max_lt hq hθ.2)⟩
    rw [Real.norm_eq_abs, hBdef]
    have h1 := hosc s hs'
    have h2 : |deriv v s| ≤ |deriv v (Real.pi / 4)|
        + |deriv v s - deriv v (Real.pi / 4)| := by
      have := abs_add_le (deriv v (Real.pi / 4)) (deriv v s - deriv v (Real.pi / 4))
      simpa [sub_eq_add_neg, add_comm] using this
    linarith
  have hftcv : v θ - v (Real.pi / 4) = ∫ s in Real.pi / 4..θ, deriv v s :=
    ws_ftc (hv.of_le (by norm_num)) hqI hθ
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (f := deriv v) (C := B) hBpt
  have h1 : |v θ - v (Real.pi / 4)| ≤ B * (Real.pi / 2) := by
    rw [← hftcv, Real.norm_eq_abs] at hnorm
    refine hnorm.trans (mul_le_mul_of_nonneg_left ?_ hB0)
    rw [abs_sub_le_iff]
    constructor <;> linarith [hθ.1, hθ.2, hq0, hq, Real.pi_pos]
  have h2 : (v θ) ^ 2 ≤ 2 * (v (Real.pi / 4)) ^ 2 + 2 * (B * (Real.pi / 2)) ^ 2 := by
    have h6 : (v θ) ^ 2
        ≤ 2 * (v (Real.pi / 4)) ^ 2 + 2 * (v θ - v (Real.pi / 4)) ^ 2 := by
      nlinarith [sq_nonneg (v (Real.pi / 4) - (v θ - v (Real.pi / 4)))]
    have h7 : (v θ - v (Real.pi / 4)) ^ 2 ≤ (B * (Real.pi / 2)) ^ 2 := by
      have h8 : 0 ≤ B * (Real.pi / 2) := mul_nonneg hB0 (by positivity)
      nlinarith [h1, sq_abs (v θ - v (Real.pi / 4)),
        abs_nonneg (v θ - v (Real.pi / 4)), h8]
    linarith
  have hB2 : B ^ 2 ≤ 2 * (deriv v (Real.pi / 4)) ^ 2 + Real.pi * E := by
    have hy : (Real.sqrt E * Real.sqrt (Real.pi / 2)) ^ 2 = E * (Real.pi / 2) := by
      rw [mul_pow, Real.sq_sqrt hE0, Real.sq_sqrt (by positivity)]
    have hsqa : (|deriv v (Real.pi / 4)|) ^ 2 = (deriv v (Real.pi / 4)) ^ 2 := sq_abs _
    have h4 : 0 ≤ Real.sqrt E * Real.sqrt (Real.pi / 2) := by positivity
    rw [hBdef]
    nlinarith [hy, hsqa, h4, abs_nonneg (deriv v (Real.pi / 4)),
      sq_nonneg (|deriv v (Real.pi / 4)| - Real.sqrt E * Real.sqrt (Real.pi / 2))]
  have h5 : 2 * (B * (Real.pi / 2)) ^ 2
      ≤ 4 * Real.pi ^ 2 * (1 + S) * (1 + (deriv v (Real.pi / 4)) ^ 2 + E) := by
    have h11 : (0 : ℝ) < Real.pi := Real.pi_pos
    have h12 : Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
    have hS1 : (1 : ℝ) ≤ 1 + S := by linarith
    have hX : (1 : ℝ) + (deriv v (Real.pi / 4)) ^ 2 + E
        ≤ (1 + S) * (1 + (deriv v (Real.pi / 4)) ^ 2 + E) := by
      nlinarith [hS1, sq_nonneg (deriv v (Real.pi / 4)), hE0, hS0]
    have h6 : 2 * (B * (Real.pi / 2)) ^ 2 = B ^ 2 * Real.pi ^ 2 / 2 := by ring
    have h7 : B ^ 2 * Real.pi ^ 2 / 2
        ≤ (2 * (deriv v (Real.pi / 4)) ^ 2 + Real.pi * E) * Real.pi ^ 2 / 2 :=
      by
        nlinarith [mul_le_mul_of_nonneg_right hB2 (by positivity : (0:ℝ) ≤ Real.pi ^ 2 / 2)]
    have h8 : (2 * (deriv v (Real.pi / 4)) ^ 2 + Real.pi * E) * Real.pi ^ 2 / 2
        ≤ 4 * Real.pi ^ 2 * (1 + S) * (1 + (deriv v (Real.pi / 4)) ^ 2 + E) := by
      have hi : (deriv v (Real.pi / 4)) ^ 2
          ≤ (1 + S) * (1 + (deriv v (Real.pi / 4)) ^ 2 + E) := by
        have h1 : (deriv v (Real.pi / 4)) ^ 2
            ≤ 1 + (deriv v (Real.pi / 4)) ^ 2 + E := by
          nlinarith [sq_nonneg (deriv v (Real.pi / 4)), hE0]
        linarith [h1, hX]
      have hii : E ≤ (1 + S) * (1 + (deriv v (Real.pi / 4)) ^ 2 + E) := by
        have h1 : E ≤ 1 + (deriv v (Real.pi / 4)) ^ 2 + E := by
          nlinarith [sq_nonneg (deriv v (Real.pi / 4)), hE0]
        linarith [h1, hX]
      have hp3 : Real.pi ^ 3 / 2 ≤ 4 * Real.pi ^ 2 := by nlinarith [h11, h12]
      have hA : Real.pi ^ 2 * (deriv v (Real.pi / 4)) ^ 2
          ≤ 4 * Real.pi ^ 2 * ((1 + S) * (1 + (deriv v (Real.pi / 4)) ^ 2 + E)) := by
        have h1 : Real.pi ^ 2 * (deriv v (Real.pi / 4)) ^ 2
            ≤ Real.pi ^ 2 * ((1 + S) * (1 + (deriv v (Real.pi / 4)) ^ 2 + E)) :=
          mul_le_mul_of_nonneg_left hi (by positivity)
        nlinarith [h1, h11]
      have hB : Real.pi ^ 3 / 2 * E
          ≤ 4 * Real.pi ^ 2 * ((1 + S) * (1 + (deriv v (Real.pi / 4)) ^ 2 + E)) := by
        have h1 : Real.pi ^ 3 / 2 * E
            ≤ Real.pi ^ 3 / 2 * ((1 + S) * (1 + (deriv v (Real.pi / 4)) ^ 2 + E)) :=
          mul_le_mul_of_nonneg_left hii (by positivity)
        nlinarith [h1, hp3]
      have hL : (2 * (deriv v (Real.pi / 4)) ^ 2 + Real.pi * E) * Real.pi ^ 2 / 2
          = Real.pi ^ 2 * (deriv v (Real.pi / 4)) ^ 2 + Real.pi ^ 3 / 2 * E := by ring
      rw [hL]
      nlinarith [hA, hB]
    linarith [h6, h7, h8]
  linarith [h2, h5]


/-! ## The affine bound for the `θ`-energy of `Ψ` -/


end Work.FTS.EllipticEst.remov
