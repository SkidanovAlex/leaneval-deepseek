import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Prop.levelTopSlotsTwoPlumb

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TopSlotTwoFts

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Elementary: `((a - b)·c)² ≤ 2(a·c)² + 2(b·c)²`. -/
theorem sub_sq_mul_le (a b c : ℝ) : ((a - b) * c) ^ 2 ≤ 2 * (a * c) ^ 2 + 2 * (b * c) ^ 2 := by
  nlinarith [sq_nonneg ((a - b) * c + 2 * (b * c)), sq_nonneg (a * c), sq_nonneg (b * c),
    sq_nonneg c]

/-! ## Endpoint limits from continuity on the closed interval -/

theorem tendsto_left_zero_of_continuousOn {f : ℝ → ℝ}
    (hc : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) :
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have h2 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Icc 0 (Real.pi / 2))) (nhds 0) := by
    have h1 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Icc 0 (Real.pi / 2)))
        (nhds (f 0)) :=
      hc.continuousWithinAt (Set.left_mem_Icc.mpr (by positivity))
    rwa [h0] at h1
  refine h2.mono_left ?_
  have hmem : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    (Filter.le_def.mp nhdsWithin_le_nhds) _
      (Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))
  calc nhdsWithin (0 : ℝ) (Set.Ioi 0)
      = nhdsWithin (0 : ℝ) (Set.Ioi 0 ∩ Set.Iio (Real.pi / 2)) :=
        (nhdsWithin_inter_of_mem' hmem).symm
    _ ≤ nhdsWithin (0 : ℝ) (Set.Icc 0 (Real.pi / 2)) :=
        nhdsWithin_mono _ (fun t ht => ⟨ht.1.le, ht.2.le⟩)

theorem tendsto_right_zero_of_continuousOn {f : ℝ → ℝ}
    (hc : ContinuousOn f (Set.Icc 0 (Real.pi / 2))) (h1 : f (Real.pi / 2) = 0) :
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have h2 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Icc 0 (Real.pi / 2))) (nhds 0) := by
    have h1' : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Icc 0 (Real.pi / 2)))
        (nhds (f (Real.pi / 2))) :=
      hc.continuousWithinAt (Set.right_mem_Icc.mpr (by positivity))
    rwa [h1] at h1'
  refine h2.mono_left ?_
  have hmem : Set.Ioi (0 : ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    (Filter.le_def.mp nhdsWithin_le_nhds) _
      (Ioi_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))
  calc nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))
      = nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2) ∩ Set.Ioi 0) :=
        (nhdsWithin_inter_of_mem' hmem).symm
    _ ≤ nhdsWithin (Real.pi / 2) (Set.Icc 0 (Real.pi / 2)) :=
        nhdsWithin_mono _ (fun t ht => ⟨ht.2.le, ht.1.le⟩)

/-! ## The `HkIntegrand α 0` integral in slice form -/

theorem integral_HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = (Work.Spaces.w z) ^ 2
        * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from ?_,
    MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
  rw [hkIntegrand_zero_eq_mul α g z θ hθ]
  ring

/-! ## The a.e. slice Poincaré for `A` -/

theorem Aft_slice_poincare {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {C : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hC : ∀ u : ℝ → ℝ, (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn
          (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ C * ∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DthIter 2 (Aft Ψ) z θ
          * Work.Spaces.Wt α z θ) ^ 2)
        ≤ (2 + 8 * C) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) z θ) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hshift : Work.FTS.EllipticEst.TT.EllWeakPos α 1
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
    Work.FTS.EllipticEst.Cores.Pieces.TL2.weakShiftTwoOne (k := 2) (by norm_num) h
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz]
    exact Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici.symm
  rw [hcongr]
  have hleft2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ContinuousOn (fun θ => Work.Spaces.DzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) ∧
        Work.Spaces.DzIter 2 Ψ z 0 = 0 ∧
        Work.Spaces.DzIter 2 Ψ z (Real.pi / 2) = 0 := by
    filter_upwards [SliceRegularShiftTwoAe hα hα4 h] with z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.1⟩
  have hleft1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ContinuousOn (fun θ => Work.Spaces.DzIter 1 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) ∧
        Work.Spaces.DzIter 1 Ψ z 0 = 0 ∧
        Work.Spaces.DzIter 1 Ψ z (Real.pi / 2) = 0 := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => ?_
    obtain ⟨h1, h2, h3, -⟩ := Work.FTS.EllipticEst.remov.weakSliceRegular 1 (by norm_num)
      α (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) hα hα4 hshift z hz
    exact ⟨h1, h2, h3⟩
  have hcomb : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      0 < z ∧ (ContinuousOn (fun θ => Work.Spaces.DzIter 2 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) ∧
          Work.Spaces.DzIter 2 Ψ z 0 = 0 ∧ Work.Spaces.DzIter 2 Ψ z (Real.pi / 2) = 0) ∧
        (ContinuousOn (fun θ => Work.Spaces.DzIter 1 Ψ z θ) (Set.Icc 0 (Real.pi / 2)) ∧
          Work.Spaces.DzIter 1 Ψ z 0 = 0 ∧ Work.Spaces.DzIter 1 Ψ z (Real.pi / 2) = 0) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi, hleft2, hleft1] with z hz hz2 hz1
    exact ⟨hz, hz2, hz1⟩
  refine hcomb.mono ?_
  intro z hz
  obtain ⟨hzpos, ⟨h2c, h2a, h2b⟩, ⟨h1c, h1a, h1b⟩⟩ := hz
  -- the endpoint limits of the slice of `A Ψ`
  have hmemn : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    have hmem : Set.Iio (Real.pi / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      (Filter.le_def.mp nhdsWithin_le_nhds) _
        (Iio_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))
    have hthis := self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ) ∩ Set.Iio (Real.pi / 2))
      (a := (0 : ℝ))
    rw [nhdsWithin_inter_of_mem' hmem] at hthis
    have hEq : Set.Ioi (0 : ℝ) ∩ Set.Iio (Real.pi / 2) = Set.Ioo 0 (Real.pi / 2) := rfl
    rwa [hEq] at hthis
  have hmemp : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈
      nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    have hmem : Set.Ioi (0 : ℝ) ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
      (Filter.le_def.mp nhdsWithin_le_nhds) _
        (Ioi_mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))
    have hthis := self_mem_nhdsWithin (s := Set.Iio (Real.pi / 2) ∩ Set.Ioi (0 : ℝ))
      (a := (Real.pi / 2))
    rw [nhdsWithin_inter_of_mem' hmem] at hthis
    have hEq : Set.Iio (Real.pi / 2) ∩ Set.Ioi (0 : ℝ) = Set.Ioo 0 (Real.pi / 2) := by
      rw [Set.inter_comm]; rfl
    rwa [hEq] at hthis
  have hevl : (fun θ => Aft Ψ z θ) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun θ => Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ) := by
    filter_upwards [hmemn] with θ hθ
    exact Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz hsm hzpos hθ
  have hevr : (fun θ => Aft Ψ z θ) =ᶠ[nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))]
      (fun θ => Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ) := by
    filter_upwards [hmemp] with θ hθ
    exact Work.FTS.EllipticEst.DzAmgm.Qop_eq_Dz2_sub_Dz hsm hzpos hθ
  have hl : Filter.Tendsto (fun θ => Aft Ψ z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h' : Filter.Tendsto (fun θ => Work.Spaces.DzIter 2 Ψ z θ
        - Work.Spaces.DzIter 1 Ψ z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hh := (tendsto_left_zero_of_continuousOn h2c h2a).sub
        (tendsto_left_zero_of_continuousOn h1c h1a)
      simpa using hh
    exact Filter.Tendsto.congr' hevl.symm h'
  have hr : Filter.Tendsto (fun θ => Aft Ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have h' : Filter.Tendsto (fun θ => Work.Spaces.DzIter 2 Ψ z θ
        - Work.Spaces.DzIter 1 Ψ z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds 0) := by
      have hh := (tendsto_right_zero_of_continuousOn h2c h2b).sub
        (tendsto_right_zero_of_continuousOn h1c h1b)
      simpa using hh
    exact Filter.Tendsto.congr' hevr.symm h'
  -- the integrability of the second derivative
  have hwpos : 0 < Work.Spaces.w z := by
    rw [Work.Spaces.w]
    exact div_pos (by positivity) (by positivity)
  have hint : MeasureTheory.IntegrableOn (fun θ =>
      (deriv (deriv (fun θ => Aft Ψ z θ)) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    refine (((integrableOn_hk0_pthIter2_Aft h hsm hzpos).const_mul
      ((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    show ((Work.Spaces.w z) ^ 2)⁻¹
        * Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) z θ
      = (deriv (deriv (fun θ => Aft Ψ z θ)) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [hkIntegrand_zero_eq_mul α _ z θ hθ]
    have hAB : Work.Spaces.pthIter 2 (Aft Ψ) z θ = deriv (deriv (fun θ => Aft Ψ z θ)) θ := rfl
    rw [hAB]
    field_simp
  -- the slice Poincaré
  have hP := hC (fun θ => Aft Ψ z θ) (smoothOpen_slices (smoothOpen_Aft hsm) hzpos)
    hl hr hint
  -- the inner pointwise comparison
  have hint1 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 1 (Aft Ψ)) z θ)
      Work.Spaces.Iθ := by
    refine (((hP.1).const_mul ((Work.Spaces.w z) ^ 2))).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
    show (Work.Spaces.w z) ^ 2
        * ((deriv (fun θ => Aft Ψ z θ) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 1 (Aft Ψ)) z θ
    rw [hkIntegrand_zero_eq_mul α _ z θ hθ]
    have hAB : Work.Spaces.pthIter 1 (Aft Ψ) z θ = deriv (fun θ => Aft Ψ z θ) θ := rfl
    rw [hAB]
    ring
  have hint2 : MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) z θ)
      Work.Spaces.Iθ :=
    integrableOn_hk0_pthIter2_Aft h hsm hzpos
  have hle := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun θ => sq_nonneg _)
    ((hint2.const_mul 2).add (hint1.const_mul 8))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
      Aft_pointwise α hα hα4 hsm (Set.mem_Ici.mpr hzpos.le) hθ)
  have hpoinc : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 1 (Aft Ψ)) z θ)
      ≤ C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) z θ) := by
    have e1 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 1 (Aft Ψ)) z θ)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ => Aft Ψ z θ) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      rw [integral_HkIntegrand_zero_eq]
      congr 1
    have e2 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) z θ)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (deriv (deriv (fun θ => Aft Ψ z θ)) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
      rw [integral_HkIntegrand_zero_eq]
      congr 1
    rw [e1, e2]
    nlinarith [hP.2, sq_nonneg (Work.Spaces.w z)]
  calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DthIter 2 (Aft Ψ) z θ
          * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (2 * Work.Spaces.HkIntegrand α 0
            (Work.Spaces.pthIter 2 (Aft Ψ)) z θ
          + 8 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 1 (Aft Ψ)) z θ) := hle
    _ = 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.Spaces.pthIter 2 (Aft Ψ)) z θ)
          + 8 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.Spaces.pthIter 1 (Aft Ψ)) z θ) := by
        rw [MeasureTheory.integral_add (hint2.const_mul 2) (hint1.const_mul 8),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.Spaces.pthIter 2 (Aft Ψ)) z θ)
          + 8 * (C * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.Spaces.pthIter 2 (Aft Ψ)) z θ) := by
        have h2nn : (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.Spaces.pthIter 2 (Aft Ψ)) z θ :=
          integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ
        linarith [hpoinc, h2nn]
    _ = (2 + 8 * C) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.Spaces.pthIter 2 (Aft Ψ)) z θ) := by ring

/-! ## The reduction of `Tk α 2 A` to `HkSq α 0 (∂_θ²A)` -/

theorem Tk_Aft_le_pure {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {C : ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hC : ∀ u : ℝ → ℝ, (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn
          (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ C * ∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) :
    Work.FTS.EllipticEst.remov.Step.Tk α 2 (Aft Ψ)
      ≤ (2 + 8 * C) * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hae := Aft_slice_poincare hα hα4 h hC
  rw [Work.FTS.EllipticEst.remov.Step.Tk, Work.Spaces.HkSq]
  have hle := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _)
    ((integrable_hk0_pthIter2_Aft h hsm).const_mul (2 + 8 * C)) hae
  rwa [MeasureTheory.integral_const_mul] at hle

/-! ## `HkSq α 0 (∂_θ²A)` in terms of the shifted slots -/

theorem HkSq_pthIter2_Aft_le {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aft Ψ))
      ≤ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
        + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) := by
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz]
    exact Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici.symm
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq, Work.Spaces.HkSq]
  have hI2 : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    integrable_hk0_pthIter2_DzIter (j := 2) h hsm (le_refl 2)
  have hI1 : MeasureTheory.Integrable (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    integrable_hk0_pthIter2_DzIter (j := 1) h hsm (by norm_num)
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) z θ)
        ≤ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) z θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ) := by
    rw [hcongr]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => ?_
    have hp : ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) z θ
          ≤ 2 * Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) z θ
            + 2 * Work.Spaces.HkIntegrand α 0
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ := by
      intro θ hθ
      by_cases hs : Real.sin (2 * θ) = 0
      · rw [hkIntegrand_zero_eq_zero _ hs, hkIntegrand_zero_eq_zero _ hs,
          hkIntegrand_zero_eq_zero _ hs]
        norm_num
      · have hθ' := mem_Ioo_of_mem_Iθ_of_sin_ne hθ hs
        have hid : Work.Spaces.pthIter 2 (Aft Ψ) z θ
            = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ
              - Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ :=
          pthIter2_Aft_eq hsm hz hθ'
        rw [Work.FTS.EllipticEst.Cores.hkIntegrand_zero_eq,
          Work.FTS.EllipticEst.Cores.hkIntegrand_zero_eq,
          Work.FTS.EllipticEst.Cores.hkIntegrand_zero_eq, hid,
          Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hsm 2 hz hθ',
          Work.FTS.EllipticEst.remov.ws_pthIter_two_DzIter hsm 1 hz hθ']
        exact sub_sq_mul_le _ _ _
    have hle := MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      (((integrableOn_hk0_pthIter2_DzIter (j := 2) h hsm (le_refl 2) hz).const_mul 2).add
        ((integrableOn_hk0_pthIter2_DzIter (j := 1) h hsm (by norm_num) hz).const_mul 2))
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hp)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (Work.Spaces.pthIter 2 (Aft Ψ)) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, (2 * Work.Spaces.HkIntegrand α 0
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) z θ
            + 2 * Work.Spaces.HkIntegrand α 0
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ) := hle
      _ = 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) z θ)
            + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ) := by
          rw [MeasureTheory.integral_add
              ((integrableOn_hk0_pthIter2_DzIter (j := 2) h hsm (le_refl 2) hz).const_mul 2)
              ((integrableOn_hk0_pthIter2_DzIter (j := 1) h hsm (by norm_num) hz).const_mul 2),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
        (Work.Spaces.pthIter 2 (Aft Ψ)) z θ)
      ≤ ∫ z in Work.Spaces.Iz, (2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) z θ)
            + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
              (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ)) :=
        MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall fun z => integral_nonneg fun θ =>
            Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
          ((hI2.const_mul 2).add (hI1.const_mul 2)) hpt
    _ = 2 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ)) z θ)
          + 2 * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ) := by
        rw [MeasureTheory.integral_add (hI2.const_mul 2) (hI1.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## The A-slot theorem -/

/-- **The level-`2` `A`-slot**: `Tk α 2 (z²∂_z²Ψ) ≤ C HkSq α 2 F`. -/
theorem Tk_A_le (h0 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllWeak0 C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      Work.FTS.EllipticEst.remov.Step.Tk α 2 (Aft Ψ)
        ≤ C * Work.Spaces.HkSq α 2 F := by
  obtain ⟨CPs, hCPspos, hPs⟩ := Work.FTS.EllipticEst.H2W.sliceEtaPoincare
  have hC : ∀ u : ℝ → ℝ, (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn
          (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ ∧
        (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          ≤ CPs * ∫ θ in Work.Spaces.Iθ,
              (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    fun u hu hl hr hint =>
      ⟨(hPs u hu hl hr hint).2.1, (hPs u hu hl hr hint).2.2.2⟩
  obtain ⟨CZ, hCZpos, hZ⟩ := ShiftZeroSlots2 h0
  refine ⟨(2 + 8 * CPs) * (4 * CZ) + 1, by positivity, fun α F Ψ hα hα4 h => ?_⟩
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hTk := Tk_Aft_le_pure hα hα4 h hC
  have hHk := HkSq_pthIter2_Aft_le (α := α) h hsm
  have hG2 := hZ α F Ψ hα hα4 h 2 (by norm_num)
  have hG1 := hZ α F Ψ hα hα4 h 1 (by norm_num)
  have hHK : 0 ≤ Work.Spaces.HkSq α 2 F := Work.Spaces.HkSq_nonneg α 2 F
  have hCPs : (0 : ℝ) ≤ CPs := hCPspos.le
  have hCZ : (0 : ℝ) ≤ CZ := hCZpos.le
  have hz1 : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
    mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
  have hz2 : 0 ≤ α ^ 4 * Work.Spaces.HkSq α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) :=
    mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg α 0 _)
  have hG2' : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
      ≤ CZ * Work.Spaces.HkSq α 2 F := by linarith [hG2, hz2]
  have hG1' : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
      ≤ CZ * Work.Spaces.HkSq α 2 F := by linarith [hG1, hz1]
  have hP2 : Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aft Ψ))
      ≤ 4 * CZ * Work.Spaces.HkSq α 2 F := by
    have : 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ))
        + 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ 4 * CZ * Work.Spaces.HkSq α 2 F := by
      nlinarith [hG2', hG1', hHK, hCZ]
    linarith [hHk, this]
  have hfin : Work.FTS.EllipticEst.remov.Step.Tk α 2 (Aft Ψ)
      ≤ (2 + 8 * CPs) * (4 * CZ) * Work.Spaces.HkSq α 2 F := by
    have hstep : (2 + 8 * CPs) * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aft Ψ))
        ≤ (2 + 8 * CPs) * (4 * CZ * Work.Spaces.HkSq α 2 F) :=
      mul_le_mul_of_nonneg_left hP2 (by positivity)
    calc Work.FTS.EllipticEst.remov.Step.Tk α 2 (Aft Ψ)
        ≤ (2 + 8 * CPs) * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 (Aft Ψ)) := hTk
      _ ≤ (2 + 8 * CPs) * (4 * CZ * Work.Spaces.HkSq α 2 F) := hstep
      _ = (2 + 8 * CPs) * (4 * CZ) * Work.Spaces.HkSq α 2 F := by ring
  calc Work.FTS.EllipticEst.remov.Step.Tk α 2 (Aft Ψ)
      ≤ (2 + 8 * CPs) * (4 * CZ) * Work.Spaces.HkSq α 2 F := hfin
    _ ≤ ((2 + 8 * CPs) * (4 * CZ) + 1) * Work.Spaces.HkSq α 2 F := by
        nlinarith [hHK]

end

end Work.FTS.EllipticEst.TopSlotTwoFts
