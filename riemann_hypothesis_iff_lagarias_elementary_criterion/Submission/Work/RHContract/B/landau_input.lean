import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.B.landau_mellin_local
import Submission.Work.RHContract.B.continuation_neg
import Submission.Work.RHContract.B.continuation_zero
import Submission.Work.RHContract.B.h2Minus_unbounded
import Submission.Work.RHContract.B.mellin_psiTail
import Submission.Work.RHContract.B.Phi_secondDeriv
import Submission.Work.RHContract.B.mellin_analytic
import Submission.Work.RHContract.B.mellin_analytic_abs
import Submission.Work.RHContract.B.no_cont_of_zeta_zero
import Submission.Work.RHContract.B.G_analytic_zero

open MeasureTheory Filter
open scoped Topology Interval

namespace Work.RHContract.B

noncomputable section

private def psiKer (t : ℝ) : ℝ := (Chebyshev.psi t - t) * Work.RHContract.kW t

private lemma psiKer_meas : Measurable psiKer := by
  have hψ : Measurable Chebyshev.psi := Chebyshev.psi_mono.measurable
  have hk : Measurable Work.RHContract.kW := by unfold Work.RHContract.kW; fun_prop
  exact (hψ.sub measurable_id).mul hk

private lemma psiKer_abs_le {t : ℝ} (ht : 2 ≤ t) :
    |psiKer t| ≤ 4 * (Real.log 4 + 4) / t := by
  have ht0 : 0 < t := by linarith
  have h1 : |Chebyshev.psi t - t| ≤ (Real.log 4 + 4) * t := abs_psi_sub_id_le ht0.le
  have h2 : |Work.RHContract.kW t| ≤ 4 / t ^ 2 := abs_kW_le ht
  rw [psiKer, abs_mul]
  calc |Chebyshev.psi t - t| * |Work.RHContract.kW t|
      ≤ ((Real.log 4 + 4) * t) * (4 / t ^ 2) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 4 * (Real.log 4 + 4) / t := by field_simp

private lemma integrableOn_psiKer : IntegrableOn psiKer (Set.Ioi 2) :=
  Work.RHContract.Identity.TailInt.integrableOn_psi_sub_id_mul_kW le_rfl

private lemma psiTail_abs_le {x : ℝ} (hx : 2 ≤ x) :
    |Work.RHContract.psiTail x| ≤ ∫ t in Set.Ioi 2, |psiKer t| := by
  have hpsi : Work.RHContract.psiTail x = ∫ t in Set.Ioi x, psiKer t := by
    rw [Work.RHContract.psiTail]; rfl
  rw [hpsi]
  have h1 : |∫ t in Set.Ioi x, psiKer t| ≤ ∫ t in Set.Ioi x, |psiKer t| := by
    simpa only [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (fun t : ℝ => psiKer t)
  refine h1.trans ?_
  refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
  · exact integrableOn_psiKer.norm
  · exact Filter.Eventually.of_forall fun t => abs_nonneg (psiKer t)
  · exact Filter.Eventually.of_forall fun t ht => Set.Ioi_subset_Ioi hx ht

private def psiKerCut (t : ℝ) : ℝ := (Set.Ici 2).indicator psiKer t

private lemma psiKerCut_meas : Measurable psiKerCut :=
  psiKer_meas.indicator measurableSet_Ici

private lemma psiKerCut_bound (t : ℝ) : |psiKerCut t| ≤ 2 * (Real.log 4 + 4) := by
  by_cases ht : t ∈ Set.Ici (2:ℝ)
  · have ht2 : (2:ℝ) ≤ t := ht
    rw [psiKerCut, Set.indicator_of_mem ht]
    have h := psiKer_abs_le ht2
    have ht0 : 0 < t := by linarith
    have h2 : 4 * (Real.log 4 + 4) / t ≤ 2 * (Real.log 4 + 4) := by
      rw [div_le_iff₀ ht0]
      nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 4)]
    linarith
  · rw [psiKerCut, Set.indicator_of_notMem ht, abs_zero]; positivity

private lemma psiKerCut_int (a b : ℝ) : IntervalIntegrable psiKerCut volume a b := by
  refine MeasureTheory.IntegrableOn.intervalIntegrable ?_
  refine MeasureTheory.Measure.integrableOn_of_bounded ?_ psiKerCut_meas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => psiKerCut_bound t)
  exact isCompact_uIcc.measure_lt_top.ne

private lemma psiKerCut_cont : Continuous (fun x : ℝ => ∫ t in (2:ℝ)..x, psiKerCut t) :=
  intervalIntegral.continuous_primitive psiKerCut_int 2

private def Klandau : ℝ := ∫ t in Set.Ioi 2, psiKer t

private lemma psiTail_eq_K {x : ℝ} (hx : 2 ≤ x) :
    Work.RHContract.psiTail x = Klandau - ∫ t in (2:ℝ)..x, psiKerCut t := by
  have hsub : (∫ t in Set.Ioi (2:ℝ), psiKer t ∂volume) - (∫ t in Set.Ioi x, psiKer t ∂volume)
      = ∫ t in (2:ℝ)..x, psiKer t ∂volume :=
    intervalIntegral.integral_Ioi_sub_Ioi integrableOn_psiKer hx
  have hcongr : (∫ t in (2:ℝ)..x, psiKer t ∂volume)
      = ∫ t in (2:ℝ)..x, psiKerCut t ∂volume := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    rw [psiKerCut, Set.indicator_of_mem (Set.mem_Ici.mpr ht.1)]
  have hpsi : Work.RHContract.psiTail x = ∫ t in Set.Ioi x, psiKer t := by
    rw [Work.RHContract.psiTail]; rfl
  rw [hpsi, Klandau, ← hcongr, ← hsub]
  ring

private def landauF (β : ℝ) (x : ℝ) : ℝ :=
  if 2 < x then (Klandau - ∫ t in (2:ℝ)..x, psiKerCut t) + 2 * x ^ (-β) else 0

private lemma landauF_meas (β : ℝ) : Measurable (landauF β) := by
  unfold landauF
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  have h1 : Continuous (fun x : ℝ => Klandau - ∫ t in (2:ℝ)..x, psiKerCut t) :=
    continuous_const.sub psiKerCut_cont
  have h2 : Measurable (fun x : ℝ => 2 * x ^ (-β)) := by measurability
  exact h1.measurable.add h2

private lemma landauF_zero (β : ℝ) : ∀ x : ℝ, x < 2 → landauF β x = 0 := by
  intro x hx
  unfold landauF
  rw [if_neg (by linarith)]

private lemma landauF_eq (β : ℝ) {x : ℝ} (hx : 2 < x) :
    landauF β x = Work.RHContract.psiTail x + 2 * x ^ (-β) := by
  unfold landauF
  rw [if_pos hx, psiTail_eq_K hx.le]

private lemma landauF_indicator_eq (β : ℝ) (s : ℂ) :
    (Set.Ioi (1:ℝ)).indicator (fun x : ℝ => (landauF β x : ℂ) * (x : ℂ) ^ (-s - 1))
      = (Set.Ioi (2:ℝ)).indicator (fun x : ℝ => (landauF β x : ℂ) * (x : ℂ) ^ (-s - 1)) := by
  funext t
  by_cases ht : (2:ℝ) < t
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht),
      Set.indicator_of_mem (Set.mem_Ioi.mpr (by linarith))]
  · have h0 : landauF β t = 0 := by unfold landauF; rw [if_neg ht]
    by_cases ht1 : (1:ℝ) < t
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht1),
        Set.indicator_of_notMem (fun h => ht (Set.mem_Ioi.mp h)), h0, Complex.ofReal_zero, zero_mul]
    · rw [Set.indicator_of_notMem (fun h => ht1 (Set.mem_Ioi.mp h)),
        Set.indicator_of_notMem (fun h => ht (Set.mem_Ioi.mp h))]

private lemma landauF_indicator_eq_real (β a : ℝ) :
    (Set.Ioi (1:ℝ)).indicator (fun x : ℝ => landauF β x * x ^ (-a - 1))
      = (Set.Ioi (2:ℝ)).indicator (fun x : ℝ => landauF β x * x ^ (-a - 1)) := by
  funext t
  by_cases ht : (2:ℝ) < t
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht),
      Set.indicator_of_mem (Set.mem_Ioi.mpr (by linarith))]
  · have h0 : landauF β t = 0 := by unfold landauF; rw [if_neg ht]
    by_cases ht1 : (1:ℝ) < t
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr ht1),
        Set.indicator_of_notMem (fun h => ht (Set.mem_Ioi.mp h)), h0, zero_mul]
    · rw [Set.indicator_of_notMem (fun h => ht1 (Set.mem_Ioi.mp h)),
        Set.indicator_of_notMem (fun h => ht (Set.mem_Ioi.mp h))]

private lemma psiTail_caestronglyMeasurable :
    AEStronglyMeasurable (fun x : ℝ => (Work.RHContract.psiTail x : ℂ))
      (volume.restrict (Set.Ioi 2)) := by
  have hcont : Continuous fun x : ℝ => ((Klandau - ∫ t in (2:ℝ)..x, psiKerCut t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.sub psiKerCut_cont)
  refine hcont.aestronglyMeasurable.congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  rw [psiTail_eq_K (le_of_lt hx)]

private lemma integrableOn_psiTail_cpow (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (Work.RHContract.psiTail x : ℂ) * (x : ℂ) ^ (-s - 1))
      (Set.Ioi 2) := by
  have hA : IntegrableOn (fun x : ℝ => (∫ t in Set.Ioi 2, |psiKer t|) * x ^ (-s.re - 1))
      (Set.Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num : (0:ℝ) < 2)).const_mul _
  have hcontc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Set.Ioi 2) := by
    intro x hx
    have hx' : (2:ℝ) < x := hx
    exact (Complex.continuousAt_ofReal_cpow_const x (-s - 1)
      (Or.inr (by linarith : x ≠ 0))).continuousWithinAt
  refine MeasureTheory.Integrable.mono' hA
    (psiTail_caestronglyMeasurable.mul (hcontc.aestronglyMeasurable measurableSet_Ioi)) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hx2 : (2:ℝ) < x := hx
  have hx0 : (0:ℝ) < x := by linarith
  have hb := psiTail_abs_le hx2.le
  have hnorm : ‖(x : ℂ) ^ (-s - 1)‖ = x ^ (-s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      show (-s - 1 : ℂ).re = -s.re - 1 from by simp]
  have hcast : ‖((Work.RHContract.psiTail x : ℝ) : ℂ)‖ = |Work.RHContract.psiTail x| := by simp
  rw [norm_mul, hnorm, hcast]
  exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hx0.le _)

private lemma integral_two_rpow (β : ℝ) (hβ : 0 < β) (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ in Set.Ioi 2, (2:ℂ) * (x : ℂ) ^ (-s - (β:ℂ) - 1)
      = 2 * (2:ℂ) ^ (-(s + β)) / (s + β) := by
  have hb : (-s - (β:ℂ) - 1 : ℂ).re < -1 := by
    rw [show (-s - (β:ℂ) - 1 : ℂ) = -(s + (β:ℂ) + 1) from by ring]
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  rw [MeasureTheory.integral_const_mul, integral_Ioi_cpow_of_lt hb (by norm_num : (0:ℝ) < 2)]
  have h1 : (-s - (β:ℂ) - 1 + 1 : ℂ) = -(s + (β:ℂ)) := by ring
  rw [h1, neg_div_neg_eq]
  simp only [Complex.ofReal_ofNat]
  ring

/-- The `H` of the Landau step is analytic wherever its Mellin input is. -/
private lemma aux_analytic (β : ℝ) (M : ℂ → ℂ) (c : ℝ) (hc : -β ≤ c)
    (hM : ∀ s : ℂ, c < s.re → AnalyticAt ℂ M s) :
    AnalyticOn ℂ (fun s : ℂ => (2:ℂ) ^ (-s) * (Work.RHContract.psiTail 2 : ℂ) - s * M s
        + s * 2 * (2:ℂ) ^ (-(s + β)) / (s + β)) {s : ℂ | c < s.re} := by
  intro s hs
  have hs' : c < s.re := hs
  have hscb : (s + β).re ≠ 0 := by
    have h : (0:ℝ) < s.re + β := by linarith [hc, hs']
    have h' : (s + β).re = s.re + β := by simp
    rw [h']; linarith
  have hsb : s + β ≠ 0 := fun h => hscb (by rw [h]; simp)
  have h1 : AnalyticAt ℂ (fun s : ℂ => (2:ℂ) ^ (-s) * (Work.RHContract.psiTail 2 : ℂ)) s :=
    (AnalyticAt.cpow (analyticAt_const (v := (2:ℂ))) analyticAt_id.neg
      (by norm_num [Complex.mem_slitPlane_iff])).mul analyticAt_const
  have h3 : AnalyticAt ℂ (fun s : ℂ => (2:ℂ) ^ (-(s + β))) s :=
    AnalyticAt.cpow (analyticAt_const (v := (2:ℂ))) (analyticAt_id.add analyticAt_const).neg
      (by norm_num [Complex.mem_slitPlane_iff])
  have h4 : AnalyticAt ℂ (fun s : ℂ => s * 2 * (2:ℂ) ^ (-(s + β)) / (s + β)) s :=
    (((analyticAt_id.mul analyticAt_const).mul h3).div (analyticAt_id.add analyticAt_const) hsb)
  exact ((h1.sub (analyticAt_id.mul (hM s hs'))).add h4).analyticWithinAt

theorem landau_input : Work.RHContract.LandauInput := by
  classical
  intro hnrh
  obtain ⟨ρ, hζρ, hb1, hb2, htriv, hne1⟩ :=
    Commons.NumberTheory.Robin.not_rh_exists_nontrivial_zero_gt_half hnrh
  have hζ₁ρ : riemannZeta₁ ρ = 0 := by
    have h := riemannZeta_eq_inv_sub_mul hne1
    have h' : (ρ - 1)⁻¹ * riemannZeta₁ ρ = 0 := by rw [← h]; exact hζρ
    exact (mul_eq_zero.mp h').resolve_left (inv_ne_zero (sub_ne_zero.mpr hne1))
  set β : ℝ := (3/2 - ρ.re) / 2 with hβdef
  have hβpos : 0 < β := by rw [hβdef]; linarith
  have hβhalf : β < 1/2 := by rw [hβdef]; linarith
  have hβgt : 1 - ρ.re < β := by rw [hβdef]; linarith
  refine ⟨β, hβpos, hβhalf, ?_⟩
  intro x₀
  by_contra hcon
  push_neg at hcon
  set X : ℝ := max x₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXx₀ : x₀ ≤ X := le_max_left _ _
  set f : ℝ → ℝ := landauF β with hfdef
  have hf_meas : Measurable f := by rw [hfdef]; exact landauF_meas β
  have hf_eq : ∀ x : ℝ, 2 < x → f x = Work.RHContract.psiTail x + 2 * x ^ (-β) := by
    intro x hx; rw [hfdef]; exact landauF_eq β hx
  have hf_nonneg : ∀ x : ℝ, X ≤ x → 0 ≤ f x := by
    intro x hx
    by_cases h2 : 2 < x
    · rw [hf_eq x h2]
      have := hcon x (le_trans hXx₀ hx)
      linarith
    · have hx2 : x = 2 := le_antisymm (le_of_not_gt h2) (le_trans hX2 hx)
      rw [hx2, hfdef]
      unfold landauF
      rw [if_neg (by norm_num : ¬ ((2:ℝ) < 2))]
  have hC : ∃ Cf : ℝ, 0 < Cf ∧ ∀ x : ℝ, 2 ≤ x → |f x| ≤ Cf := by
    refine ⟨(∫ t in Set.Ioi 2, |psiKer t|) + 2 * 2 ^ (-β) + 1, by positivity, fun x hx => ?_⟩
    by_cases h2 : 2 < x
    · rw [hf_eq x h2]
      have h1 := psiTail_abs_le hx
      have h2' : x ^ (-β) ≤ 2 ^ (-β) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith)
      have h4 : |2 * x ^ (-β)| = 2 * x ^ (-β) := by
        rw [abs_of_nonneg]; positivity
      have h5 := abs_add_le (Work.RHContract.psiTail x) (2 * x ^ (-β))
      rw [h4] at h5
      linarith
    · have hx2 : x = 2 := le_antisymm (le_of_not_gt h2) hx
      rw [hx2, hfdef]
      unfold landauF
      rw [if_neg (by norm_num : ¬ ((2:ℝ) < 2)), abs_zero]
      positivity
  obtain ⟨Cf, hCfpos, hCf⟩ := hC
  set Mfun : ℂ → ℂ := fun s => ∫ x in Set.Ioi 2, (f x : ℂ) * (x : ℂ) ^ (-s - 1) with hMdef
  set T : Set ℝ := {a : ℝ | IntegrableOn (fun x : ℝ => f x * x ^ (-a - 1)) (Set.Ioi 2)} with hTdef
  have hT_up : ∀ a b : ℝ, a ∈ T → a ≤ b → b ∈ T := by
    intro a b ha hab
    rw [hTdef] at ha ⊢
    refine MeasureTheory.Integrable.mono' ha.norm
      (hf_meas.mul (by measurability)).aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hx2 : (2:ℝ) < x := hx
    have hxb : x ^ (-b - 1) ≤ x ^ (-a - 1) := by
      rw [Real.rpow_le_rpow_left_iff (by linarith : (1:ℝ) < x)]
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact mul_le_mul_of_nonneg_left hxb (abs_nonneg _)
  have hT_pos : ∀ ε : ℝ, 0 < ε → ε ∈ T := by
    intro ε hε
    rw [hTdef]
    have hb : IntegrableOn (fun x : ℝ => Cf * x ^ (-ε - 1)) (Set.Ioi 2) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num : (0:ℝ) < 2)).const_mul Cf
    refine MeasureTheory.Integrable.mono' hb
      (hf_meas.mul (by measurability)).aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hx2 : (2:ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact mul_le_mul_of_nonneg_right (hCf x (le_of_lt hx2)) (Real.rpow_nonneg (by linarith) _)
  have hM_eq : ∀ s : ℂ, 0 < s.re → Mfun s
      = ((2:ℂ) ^ (-s) * (Work.RHContract.psiTail 2 : ℂ) - Work.RHContract.Landau.Phi s) / s
        + 2 * (2:ℂ) ^ (-(s + β)) / (s + β) := by
    intro s hs
    show (∫ x in Set.Ioi 2, (f x : ℂ) * (x : ℂ) ^ (-s - 1)) = _
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
    have hsb : s + β ≠ 0 := by
      intro h
      have h' : (s + β).re = s.re + β := by simp
      rw [h] at h'; simp at h'; linarith
    have hA := integrableOn_psiTail_cpow s hs
    have hB : IntegrableOn (fun x : ℝ => (2:ℂ) * (x : ℂ) ^ (-s - (β:ℂ) - 1)) (Set.Ioi 2) := by
      refine (integrableOn_Ioi_cpow_of_lt ?_ (by norm_num : (0:ℝ) < 2)).const_mul _
      rw [show (-s - (β:ℂ) - 1 : ℂ) = -(s + (β:ℂ) + 1) from by ring]
      simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
      linarith
    have hae : (fun x : ℝ => (f x : ℂ) * (x : ℂ) ^ (-s - 1))
        =ᵐ[volume.restrict (Set.Ioi 2)]
        (fun x : ℝ => (Work.RHContract.psiTail x : ℂ) * (x : ℂ) ^ (-s - 1)
          + (2:ℂ) * (x : ℂ) ^ (-s - (β:ℂ) - 1)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have hx2 : (2:ℝ) < x := hx
      have hx0 : (0:ℝ) < x := by linarith
      rw [hf_eq x hx2]
      have hcast : ((Work.RHContract.psiTail x + 2 * x ^ (-β) : ℝ) : ℂ)
          = (Work.RHContract.psiTail x : ℂ) + 2 * (x : ℂ) ^ (-(β : ℂ)) := by
        rw [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
          Complex.ofReal_cpow hx0.le, Complex.ofReal_neg]
      have hmul : (x : ℂ) ^ (-(β : ℂ)) * (x : ℂ) ^ (-s - 1)
          = (x : ℂ) ^ (-s - (β:ℂ) - 1) := by
        rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx0.ne')]
        congr 1
        ring
      rw [hcast, add_mul, mul_assoc, hmul]
    rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_add hA hB,
      mellin_psiTail s hs, integral_two_rpow β hβpos s hs]
  let H : ℂ → ℂ := fun s => (2:ℂ) ^ (-s) * (Work.RHContract.psiTail 2 : ℂ) - s * Mfun s
      + s * 2 * (2:ℂ) ^ (-(s + β)) / (s + β)
  have hH_Φ : ∀ s : ℂ, 0 < s.re → H s = Work.RHContract.Landau.Phi s := by
    intro s hs
    have hM := hM_eq s hs
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
    have hsb : s + β ≠ 0 := by
      intro h
      have h' : (s + β).re = s.re + β := by simp
      rw [h] at h'; simp at h'; linarith
    simp only [H]
    rw [hM]
    field_simp
    ring
  have hIoi1 : ∀ s : ℂ, (∫ x in Set.Ioi 1, (f x : ℂ) * (x : ℂ) ^ (-s - 1)) = Mfun s := by
    intro s
    show (∫ x in Set.Ioi 1, (f x : ℂ) * (x : ℂ) ^ (-s - 1))
        = ∫ x in Set.Ioi 2, (f x : ℂ) * (x : ℂ) ^ (-s - 1)
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_indicator measurableSet_Ioi]
    congr 1
    rw [hfdef]
    exact landauF_indicator_eq β s
  by_cases hcase : ∃ a : ℝ, a < ρ.re - 1 ∧ a ∈ T
  · -- CASE A
    obtain ⟨a, ha_lt, ha_mem⟩ := hcase
    have hM_an : AnalyticOn ℂ Mfun {s : ℂ | a < s.re} := by
      rw [hMdef]; exact mellin_analytic_abs f hf_meas a (by rwa [hTdef] at ha_mem)
    have hH_an : AnalyticOn ℂ H {s : ℂ | max a (-β) < s.re} := by
      have : H = (fun s : ℂ => (2:ℂ) ^ (-s) * (Work.RHContract.psiTail 2 : ℂ) - s * Mfun s
          + s * 2 * (2:ℂ) ^ (-(s + β)) / (s + β)) := rfl
      rw [this]
      refine aux_analytic β Mfun (max a (-β)) (le_max_right _ _) ?_
      intro s hs
      have hs' : a < s.re := lt_of_le_of_lt (le_max_left _ _) hs
      exact hM_an.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs')
    exact no_cont_of_zeta_zero ρ hζ₁ρ hb1 hb2
      ⟨H, max a (-β), max_lt ha_lt (by linarith), hH_an, hH_Φ⟩
  · -- CASE B
    push_neg at hcase
    have hTle : ∀ a : ℝ, a < ρ.re - 1 → a ∉ T := fun a ha haT => hcase a ha haT
    have hTBdd : BddBelow T := ⟨ρ.re - 1, fun a ha => by
      by_contra h; push_neg at h; exact hTle a h ha⟩
    have hTne : T.Nonempty := ⟨1, hT_pos 1 (by norm_num)⟩
    set σ : ℝ := sInf T with hσdef
    have hσge : ρ.re - 1 ≤ σ := le_csInf hTne (fun a ha => by
      by_contra h; push_neg at h; exact hTle a h ha)
    have hσle : σ ≤ 0 := by
      by_contra h
      have hpos : 0 < σ := lt_of_not_ge h
      have hεT : σ / 2 ∈ T := hT_pos (σ/2) (by linarith)
      have : σ ≤ σ / 2 := by rw [hσdef]; exact csInf_le hTBdd hεT
      linarith
    have hσgt : -(1/2 : ℝ) < σ := lt_of_lt_of_le (by linarith) hσge
    have hH_an : AnalyticOn ℂ H {s : ℂ | σ < s.re} := by
      have : H = (fun s : ℂ => (2:ℂ) ^ (-s) * (Work.RHContract.psiTail 2 : ℂ) - s * Mfun s
          + s * 2 * (2:ℂ) ^ (-(s + β)) / (s + β)) := rfl
      rw [this]
      refine aux_analytic β Mfun σ (by linarith) ?_
      intro s hs
      have hs' : σ < s.re := hs
      obtain ⟨b, hbT, hbs⟩ := (csInf_lt_iff hTBdd hTne).mp (by rw [← hσdef]; exact hs')
      have hb_an : AnalyticOn ℂ Mfun {t : ℂ | b < t.re} := by
        rw [hMdef]; exact mellin_analytic_abs f hf_meas b (by rwa [hTdef] at hbT)
      exact hb_an.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hbs)
    have hint : ∀ a : ℝ, σ < a → IntegrableOn (fun x : ℝ => f x * x ^ (-a - 1)) (Set.Ioi 1) := by
      intro a ha
      have hat : a ∈ T := by
        obtain ⟨b, hbT, hba⟩ := (csInf_lt_iff hTBdd hTne).mp (by rw [← hσdef]; exact ha)
        exact hT_up b a hbT hba.le
      rw [hTdef] at hat
      change IntegrableOn (fun x : ℝ => f x * x ^ (-a - 1)) (Set.Ioi 2) at hat
      rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioi] at hat ⊢
      rwa [show (Set.Ioi (2:ℝ)).indicator (fun x : ℝ => f x * x ^ (-a - 1))
          = (Set.Ioi (1:ℝ)).indicator (fun x : ℝ => f x * x ^ (-a - 1)) from by
        rw [hfdef]; exact (landauF_indicator_eq_real β a).symm] at hat
    rcases lt_or_eq_of_le hσle with hσlt | hσeq
    · -- σ < 0
      obtain ⟨r, hr, Φt, hΦt_an, hΦt_eq⟩ := continuation_neg σ hσgt hσlt H hH_an hH_Φ
      set m : ℝ := min r (min (σ + β) (-σ)) with hmdef
      have hmr : m ≤ r := min_le_left _ _
      have hmsb : m ≤ σ + β := le_trans (min_le_right _ _) (min_le_left _ _)
      have hmns : m ≤ -σ := le_trans (min_le_right _ _) (min_le_right _ _)
      have hmpos : 0 < m := lt_min hr (lt_min (by linarith) (by linarith))
      set r' : ℝ := m / 2 with hr'def
      have hr'pos : 0 < r' := by rw [hr'def]; linarith
      have hr'r : r' < r := by rw [hr'def]; linarith
      have hr'sb : r' < σ + β := by rw [hr'def]; linarith
      have hr'ns : r' < -σ := by rw [hr'def]; linarith
      set G : ℂ → ℂ := fun s => if s ∈ Metric.ball (σ:ℂ) r' then
          ((2:ℂ) ^ (-s) * (Work.RHContract.psiTail 2 : ℂ) - Φt s) / s
            + 2 * (2:ℂ) ^ (-(s + β)) / (s + β)
        else Mfun s with hGdef
      have hG_an : AnalyticOn ℂ G (Metric.ball (σ:ℂ) r') := by
        intro s hs
        have hsr : ‖s - (σ:ℂ)‖ < r' := by
          rw [Metric.mem_ball, dist_eq_norm] at hs; exact hs
        have h1 : |s.re - σ| ≤ ‖s - (σ:ℂ)‖ := by
          have h := Complex.abs_re_le_norm (s - (σ:ℂ))
          rwa [Complex.sub_re, Complex.ofReal_re] at h
        have hsre : s.re < 0 := by
          have hlt := abs_lt.mp (lt_of_le_of_lt h1 (lt_trans hsr hr'ns))
          linarith [hlt.1, hlt.2]
        have hsb : s + β ≠ 0 := by
          intro h
          have h2 : (s + β).re = 0 := by rw [h]; simp
          have h3 : (s + β).re = s.re + β := by simp
          have hlt := abs_lt.mp (lt_of_le_of_lt h1 (lt_trans hsr hr'sb))
          linarith [hlt.1, hlt.2, h2, h3]
        have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
        have hΦr : AnalyticAt ℂ Φt s := hΦt_an.analyticAt
          (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (le_of_lt hr'r) hs))
        have hexpr : AnalyticAt ℂ (fun w : ℂ =>
            ((2:ℂ) ^ (-w) * (Work.RHContract.psiTail 2 : ℂ) - Φt w) / w
              + 2 * (2:ℂ) ^ (-(w + β)) / (w + β)) s := by
          have hAa : AnalyticAt ℂ (fun w : ℂ => (2:ℂ) ^ (-w)
              * (Work.RHContract.psiTail 2 : ℂ) - Φt w) s :=
            (((analyticAt_const (v := (2:ℂ))).cpow analyticAt_id.neg
              (by norm_num [Complex.mem_slitPlane_iff])).mul analyticAt_const).sub hΦr
          have hBb : AnalyticAt ℂ (fun w : ℂ => 2 * (2:ℂ) ^ (-(w + β)) / (w + β)) s :=
            (((analyticAt_const (v := (2:ℂ))).mul ((analyticAt_const (v := (2:ℂ))).cpow
              (analyticAt_id.add analyticAt_const).neg
              (by norm_num [Complex.mem_slitPlane_iff]))).div
              (analyticAt_id.add analyticAt_const) hsb)
          exact (hAa.div analyticAt_id hs0).add hBb
        refine (hexpr.congr ?_).analyticWithinAt
        filter_upwards [Metric.isOpen_ball.mem_nhds hs] with w hw
        simp only [hGdef, if_pos hw]
      have hG_eq : ∀ s : ℂ, σ < s.re →
          G s = ∫ x in Set.Ioi 1, (f x : ℂ) * (x : ℂ) ^ (-s - 1) := by
        intro s hs
        rw [hIoi1 s]
        by_cases hb : s ∈ Metric.ball (σ:ℂ) r'
        · have hsr : ‖s - (σ:ℂ)‖ < r' := by
            rw [Metric.mem_ball, dist_eq_norm] at hb; exact hb
          have h1 : |s.re - σ| ≤ ‖s - (σ:ℂ)‖ := by
            have h := Complex.abs_re_le_norm (s - (σ:ℂ))
            rwa [Complex.sub_re, Complex.ofReal_re] at h
          have hsre : s.re < 0 := by
            have hlt := abs_lt.mp (lt_of_le_of_lt h1 (lt_trans hsr hr'ns))
            linarith [hlt.1, hlt.2]
          have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
          have hsb : s + β ≠ 0 := by
            intro h
            have h2 : (s + β).re = 0 := by rw [h]; simp
            have h3 : (s + β).re = s.re + β := by simp
            have hlt := abs_lt.mp (lt_of_le_of_lt h1 (lt_trans hsr hr'sb))
            linarith [hlt.1, hlt.2, h2, h3]
          simp only [hGdef, if_pos hb]
          have hΦ : Φt s = H s := hΦt_eq s hs
          simp only [H] at hΦ
          rw [hΦ]
          field_simp
          ring
        · simp only [hGdef, if_neg hb]
      obtain ⟨a', ha'lt, ha'int⟩ := landau_mellin_local f X σ r' (by linarith) hr'pos hf_meas
        hf_nonneg hint ⟨G, hG_an, hG_eq⟩
      have ha'T : a' ∈ T := by
        rw [hTdef]
        change IntegrableOn (fun x : ℝ => f x * x ^ (-a' - 1)) (Set.Ioi 2)
        rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioi] at ha'int ⊢
        rwa [show (Set.Ioi (1:ℝ)).indicator (fun x : ℝ => f x * x ^ (-a' - 1))
            = (Set.Ioi (2:ℝ)).indicator (fun x : ℝ => f x * x ^ (-a' - 1)) from by
          rw [hfdef]; exact landauF_indicator_eq_real β a'] at ha'int
      have hcs := csInf_le hTBdd ha'T
      rw [← hσdef] at hcs
      linarith
    · -- σ = 0
      have hσ0 : σ = 0 := hσeq
      have hH_an0 : AnalyticOn ℂ H {s : ℂ | 0 < s.re} := by rw [← hσ0]; exact hH_an
      obtain ⟨r, hr, Φt, hΦt_an, hΦt_eq⟩ := continuation_zero H hH_an0 hH_Φ
      obtain ⟨r₂, hr₂pos, hr₂β, G, hG_an, hG_eq0⟩ :=
        G_analytic_zero β 2 hβpos r hr Φt hΦt_an
          (fun s _ hspos => by rw [hΦt_eq s hspos, hH_Φ s hspos])
      have hG_eq : ∀ s : ℂ, σ < s.re → G s = ∫ x in Set.Ioi 1, (f x : ℂ) * (x : ℂ) ^ (-s - 1) := by
        intro s hs
        have hs0 : (0:ℝ) < s.re := by rw [← hσ0]; exact hs
        rw [hG_eq0 s hs0, hIoi1 s]
        have hΦ : Φt s = H s := hΦt_eq s hs0
        simp only [H] at hΦ
        rw [hΦ]
        have hne : s ≠ 0 := fun h => by rw [h] at hs0; simp at hs0
        have hsb : s + β ≠ 0 := by
          intro h
          have h2 : (s + β).re = s.re + β := by simp
          rw [h] at h2; simp at h2; linarith
        field_simp
        simp only [Complex.ofReal_ofNat]
        ring
      obtain ⟨a', ha'lt, ha'int⟩ := landau_mellin_local f X σ r₂ (by linarith) hr₂pos hf_meas
        hf_nonneg hint ⟨G, by rw [hσ0]; exact hG_an, hG_eq⟩
      have ha'T : a' ∈ T := by
        rw [hTdef]
        change IntegrableOn (fun x : ℝ => f x * x ^ (-a' - 1)) (Set.Ioi 2)
        rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioi] at ha'int ⊢
        rwa [show (Set.Ioi (1:ℝ)).indicator (fun x : ℝ => f x * x ^ (-a' - 1))
            = (Set.Ioi (2:ℝ)).indicator (fun x : ℝ => f x * x ^ (-a' - 1)) from by
          rw [hfdef]; exact landauF_indicator_eq_real β a'] at ha'int
      have hcs := csInf_le hTBdd ha'T
      rw [← hσdef] at hcs
      linarith

end

end Work.RHContract.B
