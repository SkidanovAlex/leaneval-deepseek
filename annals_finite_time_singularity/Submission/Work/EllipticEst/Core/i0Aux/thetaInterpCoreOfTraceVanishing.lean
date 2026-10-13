import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit
import Submission.Work.FTS.EllipticEst.Honest.sliceInterp
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.MainScratch
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.endpointParamLeftW
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.endpointParamRightW
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrals
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.ibpSurr
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.csThEta
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.integralSqSub
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrableFull
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvHypBundle
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.sScaleBounds
import Submission.Work.FTS.EllipticEst.AngAWeak.corrSlice_limits

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit true
set_option maxHeartbeats 4000000

namespace Work.EllipticEst.Core.i0Aux

theorem thetaInterpCoreOfTraceVanishing
    (TV : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ → ℝ,
      ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
                * (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))))

    (htr : ∃ F₀ F₁ : ℝ,
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀)
      ∧ Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁)) :

    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    f 0 = 0 → f (Real.pi / 2) = 0 →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  obtain ⟨CTV, hCTVpos, hTV⟩ := TV
  obtain ⟨ψ, Cb, hbump⟩ := TVRed.bumpExists
  have hCbpos : 0 < Cb := hbump.C_pos
  have hψcd : ContDiff ℝ 2 ψ := hbump.contDiff
  set K1 : ℝ := 1000 * (Cb + 1) ^ 2 * 201 with hK1
  set K2 : ℝ := 1000 * (Cb + 1) ^ 2 * 3204 with hK2
  have hK1nn : 0 ≤ K1 := by rw [hK1]; positivity
  have hK2nn : 0 ≤ K2 := by rw [hK2]; positivity
  refine ⟨CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
    + 4 * Real.sqrt K2 + 1, by positivity, ?_⟩
  intro f hf hf0 hfpi hP hA hE
  obtain ⟨K0, hK0pos, hSL⟩ := Work.EllipticEst.Core.sliceBoundaryLimit
  have hf1 : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) := hf.of_le (by norm_num)
  have hAoo : IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := tvc_integrableOn_Ioo_of_Iθ hA
  obtain ⟨hLft, hRgt⟩ := hSL f hf1 hAoo
  obtain ⟨F₀, hF₀t, -⟩ := hLft
  obtain ⟨F₁, hF₁t, -⟩ := hRgt
  have hPoo : IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := tvc_integrableOn_Ioo_of_Iθ hP
  have hEoo : IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := tvc_integrableOn_Ioo_of_Iθ hE
  have hPoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = ∫ x in Work.Spaces.Iθ, (f x) ^ 2 * Work.FTS.EllipticEst.thEta x :=
    (tvc_setIntegral_Iθ_eq_Ioo _).symm
  have hEoo_eq : (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = ∫ x in Work.Spaces.Iθ, (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x :=
    (tvc_setIntegral_Iθ_eq_Ioo _).symm
  by_cases hP0 : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) = 0
  · -- ### degenerate case: the two traces vanish, so `TV` applies to `f` itself
    have hF₀0 : F₀ = 0 := by
      have hbd : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          F₀ ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
        intro t ht
        have h := TVRed.endpointParamLeftW f F₀ t ht.1 ht.2 hf hF₀t hEoo hPoo
        have hz : (∫ x in Set.Ioo 0 (Real.pi / 2),
            (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) = 0 := by
          rw [hPoo_eq]; exact hP0
        rw [hz, mul_zero, add_zero] at h
        exact h
      have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          F₀ ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
            (isOpen_Iio.mem_nhds (by rw [Set.mem_Iio]; exact half_pos Real.pi_pos)), self_mem_nhdsWithin]
          with t ht hpos
        exact hbd t ⟨hpos, ht⟩
      have htend : Tendsto (fun t : ℝ => 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h1 : Tendsto (fun t : ℝ => t ^ (3 + Work.Spaces.eta))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
          Work.FTS.EllipticEst.AngAWeak.tendsto_rpow_nhdsGT_zero
            (by rw [Work.Spaces.eta]; norm_num)
        simpa using ((h1.const_mul 2).mul_const _)
      have hle : F₀ ^ 2 ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds htend hev
      exact (sq_eq_zero_iff).mp (le_antisymm hle (sq_nonneg F₀))
    have hF₁0 : F₁ = 0 := by
      have hbd : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          F₁ ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
        intro t ht
        have h := TVRed.endpointParamRightW f F₁ t ht.1 ht.2 hf hF₁t hEoo hPoo
        have hz : (∫ x in Set.Ioo 0 (Real.pi / 2),
            (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) = 0 := by
          rw [hPoo_eq]; exact hP0
        rw [hz, mul_zero, add_zero] at h
        exact h
      have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          F₁ ^ 2 ≤ 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
            (isOpen_Iio.mem_nhds (by rw [Set.mem_Iio]; exact half_pos Real.pi_pos)), self_mem_nhdsWithin]
          with t ht hpos
        exact hbd t ⟨hpos, ht⟩
      have htend : Tendsto (fun t : ℝ => 2 * t ^ (3 + Work.Spaces.eta)
            * (∫ x in Set.Ioo 0 (Real.pi / 2),
                (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        have h1 : Tendsto (fun t : ℝ => t ^ (3 + Work.Spaces.eta))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
          Work.FTS.EllipticEst.AngAWeak.tendsto_rpow_nhdsGT_zero
            (by rw [Work.Spaces.eta]; norm_num)
        simpa using ((h1.const_mul 2).mul_const _)
      have hle : F₁ ^ 2 ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds htend hev
      exact (sq_eq_zero_iff).mp (le_antisymm hle (sq_nonneg F₁))
    have ht0 : Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := hF₀t; rw [hF₀0] at h; exact h
    have ht1 : Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h := hF₁t; rw [hF₁0] at h; exact h
    have hTVf := hTV f hf ht0 ht1 hP hA hE
    have hsum0 : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * (∫ θ in Work.Spaces.Iθ,
                (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) = 0 := by
      rw [hP0, zero_mul, Real.sqrt_zero, add_zero]
    have hTVf' : (∫ θ in Work.Spaces.Iθ,
        (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) ≤ 0 := by
      have h2 : CTV * ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
              * (∫ θ in Work.Spaces.Iθ,
                  (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))) = 0 := by
        rw [hsum0, mul_zero]
      rw [h2] at hTVf
      exact hTVf
    rw [hsum0, mul_zero]
    exact hTVf'
  · -- ### main case
    have hPnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    have hPpos : 0 < ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
      lt_of_le_of_ne hPnn (Ne.symm hP0)
    have hEnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    set P : ℝ := ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hPdef
    set E : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hEdef
    set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ with hAdef
    have hPpos' : 0 < P := hPpos
    have hEnn' : 0 ≤ E := hEnn
    have hLpos : 0 < sScale P E := sScale_pos hPpos' hEnn'
    have hLhalf : sScale P E ≤ 1 / 2 := sScale_le_half hPpos' hEnn'
    have hLpi : sScale P E ≤ Real.pi / 4 := by nlinarith [hLhalf, Real.pi_gt_three]
    have hLlt : sScale P E < Real.pi / 2 := by nlinarith [hLhalf, Real.pi_gt_three]
    have hF0b : F₀ ^ 2 ≤ 2 * (sScale P E) ^ (3 + Work.Spaces.eta) * E
        + 100 * (sScale P E) ^ (Work.Spaces.eta - 1) * P := by
      have h := TVRed.endpointParamLeftW f F₀ (sScale P E) hLpos hLlt hf hF₀t hEoo hPoo
      have hJE : (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) = E :=
        hEoo_eq.trans hEdef.symm
      have hXP : (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) = P :=
        hPoo_eq.trans hPdef.symm
      rwa [hJE, hXP] at h
    have hF1b : F₁ ^ 2 ≤ 2 * (sScale P E) ^ (3 + Work.Spaces.eta) * E
        + 100 * (sScale P E) ^ (Work.Spaces.eta - 1) * P := by
      have h := TVRed.endpointParamRightW f F₁ (sScale P E) hLpos hLlt hf hF₁t hEoo hPoo
      have hJE : (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) x) ^ 2 * Work.FTS.EllipticEst.thEta x) = E :=
        hEoo_eq.trans hEdef.symm
      have hXP : (∫ x in Set.Ioo 0 (Real.pi / 2), (f x) ^ 2 * Work.FTS.EllipticEst.thEta x) = P :=
        hPoo_eq.trans hPdef.symm
      rwa [hJE, hXP] at h
    have hSb : F₀ ^ 2 + F₁ ^ 2 ≤ 4 * (sScale P E) ^ (3 + Work.Spaces.eta) * E
        + 200 * (sScale P E) ^ (Work.Spaces.eta - 1) * P := by linarith
    obtain ⟨hArith1, hArith2⟩ := TVRed.sScaleBounds hPpos' hEnn' hCbpos hSb
    obtain ⟨hX1b, hX2b, hX3b, hX4b⟩ :=
      TVRed.surrIntegrals (ψ := ψ) (C := Cb) (F₀ := F₀) (F₁ := F₁) (L := sScale P E)
        hbump hLpos hLpi
    have hN1 : (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) ≤ K1 * P := by
      have h1 : 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
          * (sScale P E) ^ (1 - Work.Spaces.eta) ≤ K1 * P := by
        rw [hK1]; exact hArith1
      exact le_trans hX1b h1
    have hN2 : (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) ≤ K2 * (P + E) := by
      have h1 : 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
          * (sScale P E) ^ (-(3 + Work.Spaces.eta)) ≤ K2 * (P + E) := by
        rw [hK2]; exact hArith2
      exact le_trans hX3b h1
    have hN3 : (∫ θ in Work.Spaces.Iθ, (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ) ^ 2
        * (qTh θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) ≤ K2 * (P + E) := by
      have h1 : 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2)
          * (sScale P E) ^ (-(3 + Work.Spaces.eta)) ≤ K2 * (P + E) := by
        rw [hK2]; exact hArith2
      exact le_trans hX4b h1
    obtain ⟨hℓ2int, hℓ1int, hℓ2int', hℓq2int⟩ :=
      TVRed.tvh_surr_integrable4 (ψ := ψ) (C := Cb) (F₀ := F₀) (F₁ := F₁) (L := sScale P E)
        hbump hLpos hLpi
    obtain ⟨hgC2, hglim0, hglim1, hgPint, hgAint, hgEint⟩ :=
      TVRed.tvHypBundle (ψ := ψ) (C := Cb) (F₀ := F₀) (F₁ := F₁) (L := sScale P E)
        hbump hLpos hLpi hf hF₀t hF₁t hP hA hE
    have hℓq2int' : IntegrableOn
        (fun θ : ℝ => (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
      refine hℓq2int.congr ?_
      filter_upwards with θ
      ring
    have hG1b : (∫ θ in Work.Spaces.Iθ,
        (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ (2 + 2 * K1) * P := by
      have h := tvc_g1_bound (F₀ := F₀) (F₁ := F₁) (L := sScale P E) (ne_of_gt hLpos)
        hψcd hP hℓ2int hgPint
      have h2 : 2 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 2 * (∫ θ in Work.Spaces.Iθ, (surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) ≤ (2 + 2 * K1) * P := by
        rw [← hPdef]
        linarith [hN1]
      linarith
    have hG2b : (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) ≤ (2 + 2 * K2) * (P + E) := by
      have h := tvc_g2_bound (F₀ := F₀) (F₁ := F₁) (L := sScale P E) (ne_of_gt hLpos)
        hψcd hf hE hℓ2int' hgEint
      have h2 : 2 * (∫ θ in Work.Spaces.Iθ,
            (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + 2 * (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) ≤ (2 + 2 * K2) * (P + E) := by
        rw [← hEdef]
        linarith [hN2]
      linarith
    have hTVg := hTV (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)
      hgC2 hglim0 hglim1 hgPint hgAint hgEint
    have hibp := TVRed.ibpSurr (ψ := ψ) (C := Cb) (F₀ := F₀) (F₁ := F₁)
      (L := sScale P E) hbump hLpos hLpi hf
    set X2 : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      with hX2def
    set X3 : ℝ := ∫ θ in Work.Spaces.Iθ,
      (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ with hX3def
    set Y : ℝ := ∫ θ in Work.Spaces.Iθ, deriv f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ
      * Work.FTS.EllipticEst.thEta θ with hYdef
    have hX2le : X2 ≤ K2 * (P + E) := by rw [hX2def]; exact hN2
    have hX3eq : X3 = ∫ θ in Work.Spaces.Iθ,
        (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ) ^ 2 * (qTh θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
      rw [hX3def]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      ring
    have hX3le : X3 ≤ K2 * (P + E) := by rw [hX3eq]; exact hN3
    have hX2nn : 0 ≤ X2 := by
      rw [hX2def]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    have hX3nn : 0 ≤ X3 := by
      rw [hX3def]
      exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    -- Cauchy-Schwarz for the two IBP terms
    have hcs1 := TVRed.csThEta (g := f)
      (h := fun θ : ℝ => deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ) hP hℓ2int'
    have hcs2 := TVRed.csThEta (g := f)
      (h := fun θ : ℝ => deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ) hP hℓq2int'
    have hZ1 : |∫ θ in Work.Spaces.Iθ,
        f θ * deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ
          * Work.FTS.EllipticEst.thEta θ| ≤ Real.sqrt (P * X2) := by
      refine tvc_abs_le_sqrt (mul_nonneg hPpos'.le hX2nn) ?_
      have h := hcs1
      rw [← hPdef, ← hX2def] at h
      exact h
    have hZ2' : |∫ θ in Work.Spaces.Iθ,
        f θ * (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ)
          * Work.FTS.EllipticEst.thEta θ| ≤ Real.sqrt (P * X3) := by
      refine tvc_abs_le_sqrt (mul_nonneg hPpos'.le hX3nn) ?_
      have h := hcs2
      rw [← hPdef, ← hX3def] at h
      exact h
    have hZ2 : |∫ θ in Work.Spaces.Iθ,
        f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ
          * Work.FTS.EllipticEst.thEta θ| ≤ Real.sqrt (P * X3) := by
      rw [show (∫ θ in Work.Spaces.Iθ, f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ
            * qTh θ * Work.FTS.EllipticEst.thEta θ)
          = (∫ θ in Work.Spaces.Iθ, f θ * (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ)
              * Work.FTS.EllipticEst.thEta θ) from ?_]
      · exact hZ2'
      · refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
        ring
    have hYle : Y ≤ Real.sqrt (P * X2) + Real.sqrt (P * X3) := by
      have h := hibp
      rw [hYdef]
      calc (∫ θ in Work.Spaces.Iθ, deriv f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ
            * Work.FTS.EllipticEst.thEta θ)
          = - (∫ θ in Work.Spaces.Iθ,
                f θ * deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ
                  * Work.FTS.EllipticEst.thEta θ)
            + (∫ θ in Work.Spaces.Iθ,
                f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ
                  * Work.FTS.EllipticEst.thEta θ) := h
        _ ≤ |∫ θ in Work.Spaces.Iθ,
                f θ * deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ
                  * Work.FTS.EllipticEst.thEta θ|
              + |∫ θ in Work.Spaces.Iθ,
                f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ
                  * Work.FTS.EllipticEst.thEta θ| := by
            have h1 := neg_le_abs (∫ θ in Work.Spaces.Iθ,
              f θ * deriv (deriv (surrFun ψ F₀ F₁ (sScale P E))) θ
                * Work.FTS.EllipticEst.thEta θ)
            have h2 := le_abs_self (∫ θ in Work.Spaces.Iθ,
              f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ * qTh θ
                * Work.FTS.EllipticEst.thEta θ)
            linarith
        _ ≤ Real.sqrt (P * X2) + Real.sqrt (P * X3) := add_le_add hZ1 hZ2
    -- the exponential-scale comparison
    have hsq1 : Real.sqrt (P * X2) ≤ Real.sqrt K2 * (P + Real.sqrt (P * E)) := by
      have h1 : P * X2 ≤ K2 * (P * (P + E)) := by
        have h3 : P * X2 ≤ P * (K2 * (P + E)) := mul_le_mul_of_nonneg_left hX2le hPpos'.le
        linarith
      calc Real.sqrt (P * X2) ≤ Real.sqrt (K2 * (P * (P + E))) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt K2 * Real.sqrt (P * (P + E)) := by
            rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ K2)]
        _ ≤ Real.sqrt K2 * (P + Real.sqrt (P * E)) :=
            mul_le_mul_of_nonneg_left (tvc_sqrt_mul_le hPpos'.le hEnn') (Real.sqrt_nonneg _)
    have hsq2 : Real.sqrt (P * X3) ≤ Real.sqrt K2 * (P + Real.sqrt (P * E)) := by
      have h1 : P * X3 ≤ K2 * (P * (P + E)) := by
        have h3 : P * X3 ≤ P * (K2 * (P + E)) := mul_le_mul_of_nonneg_left hX3le hPpos'.le
        linarith
      calc Real.sqrt (P * X3) ≤ Real.sqrt (K2 * (P * (P + E))) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt K2 * Real.sqrt (P * (P + E)) := by
            rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ K2)]
        _ ≤ Real.sqrt K2 * (P + Real.sqrt (P * E)) :=
            mul_le_mul_of_nonneg_left (tvc_sqrt_mul_le hPpos'.le hEnn') (Real.sqrt_nonneg _)
    -- the TV bound on `g`
    have hG1nn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    have hG2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
    have hGprod : Real.sqrt ((∫ θ in Work.Spaces.Iθ,
          (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ))
        ≤ Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)) := by
      have h1 : (∫ θ in Work.Spaces.Iθ,
            (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          * (∫ θ in Work.Spaces.Iθ,
            (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
          ≤ ((2 + 2 * K1) * (2 + 2 * K2)) * (P * (P + E)) := by
        have h4 : (∫ θ in Work.Spaces.Iθ,
              (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)
            ≤ ((2 + 2 * K1) * P) * ((2 + 2 * K2) * (P + E)) :=
          mul_le_mul hG1b hG2b hG2nn (by nlinarith [hPpos'.le, hK1nn, hK1])
        linarith [h4]
      calc Real.sqrt ((∫ θ in Work.Spaces.Iθ,
              (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ))
          ≤ Real.sqrt (((2 + 2 * K1) * (2 + 2 * K2)) * (P * (P + E))) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * Real.sqrt (P * (P + E)) := by
            rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (2 + 2 * K1) * (2 + 2 * K2))]
        _ ≤ Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)) :=
            mul_le_mul_of_nonneg_left (tvc_sqrt_mul_le hPpos'.le hEnn') (Real.sqrt_nonneg _)
    -- assemble
    have hTVg' : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        ≤ CTV * ((2 + 2 * K1) * P
            + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E))) := by
      refine le_trans hTVg ?_
      have h2 : (∫ θ in Work.Spaces.Iθ,
            (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          ≤ (2 + 2 * K1) * P := hG1b
      have h3 : (∫ θ in Work.Spaces.Iθ,
            (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          + Real.sqrt ((∫ θ in Work.Spaces.Iθ,
              (f θ - surrFun ψ F₀ F₁ (sScale P E) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
            * (∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ)) θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ))
          ≤ (2 + 2 * K1) * P
            + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)) := by
        linarith [h2, hGprod]
      exact mul_le_mul_of_nonneg_left h3 hCTVpos.le
    -- the `A ≤ A(g) + 2Y` relation
    have hcross : IntegrableOn (fun θ : ℝ =>
        deriv f θ * deriv (surrFun ψ F₀ F₁ (sScale P E)) θ
          * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
      tvc_integrableOn_cross (ψ := ψ) (F₀ := F₀) (F₁ := F₁) (L := sScale P E) hψcd hA hℓ1int
    have hAg_eq : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ)
        = A - 2 * Y + (∫ θ in Work.Spaces.Iθ,
            (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
      have h := tvc_derivg2_eq (F₀ := F₀) (F₁ := F₁) (L := sScale P E) (ne_of_gt hLpos)
        hψcd hf hA hℓ1int hcross
      rw [hAdef, hYdef]
      exact h
    have hArel : A ≤ (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ : ℝ => f θ - surrFun ψ F₀ F₁ (sScale P E) θ) θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) + 2 * Y := by
      have hℓ1nn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          (deriv (surrFun ψ F₀ F₁ (sScale P E)) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
        MeasureTheory.setIntegral_nonneg measurableSet_Icc
          (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))
      linarith [hAg_eq, hℓ1nn]
    -- final assembly
    have hYbound : Y ≤ 2 * Real.sqrt K2 * (P + Real.sqrt (P * E)) := by
      linarith [hYle, hsq1, hsq2]
    have hmain : A ≤ (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
        + 4 * Real.sqrt K2 + 1) * (P + Real.sqrt (P * E)) := by
      have h1 : A ≤ CTV * ((2 + 2 * K1) * P
          + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)))
          + 2 * (2 * Real.sqrt K2 * (P + Real.sqrt (P * E))) := by
        linarith [hArel, hTVg', hYbound]
      have h2 : CTV * ((2 + 2 * K1) * P
          + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)))
          + 2 * (2 * Real.sqrt K2 * (P + Real.sqrt (P * E)))
          ≤ (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
            + 4 * Real.sqrt K2 + 1) * (P + Real.sqrt (P * E)) := by
        have h4 : 0 ≤ P + Real.sqrt (P * E) :=
          add_nonneg hPpos'.le (Real.sqrt_nonneg _)
        have h5 : CTV * ((2 + 2 * K1) * P
              + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)))
            + 2 * (2 * Real.sqrt K2 * (P + Real.sqrt (P * E)))
            ≤ (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
              + 4 * Real.sqrt K2) * (P + Real.sqrt (P * E)) := by
          have hprod : 0 ≤ CTV * (2 + 2 * K1) * Real.sqrt (P * E) :=
            mul_nonneg (by positivity) (Real.sqrt_nonneg _)
          have hexp : (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
                + 4 * Real.sqrt K2) * (P + Real.sqrt (P * E))
              = CTV * (2 + 2 * K1) * P + CTV * (2 + 2 * K1) * Real.sqrt (P * E)
                + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * P
                + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * Real.sqrt (P * E)
                + 4 * Real.sqrt K2 * P + 4 * Real.sqrt K2 * Real.sqrt (P * E) := by ring
          rw [hexp]
          linarith [hprod]
        calc CTV * ((2 + 2 * K1) * P
              + Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2)) * (P + Real.sqrt (P * E)))
            + 2 * (2 * Real.sqrt K2 * (P + Real.sqrt (P * E)))
            ≤ (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
              + 4 * Real.sqrt K2) * (P + Real.sqrt (P * E)) := h5
          _ ≤ (CTV * (2 + 2 * K1) + CTV * Real.sqrt ((2 + 2 * K1) * (2 + 2 * K2))
              + 4 * Real.sqrt K2 + 1) * (P + Real.sqrt (P * E)) := by
              nlinarith [h4]
      exact le_trans h1 h2
    rw [hAdef, hPdef, hEdef]
    exact hmain


end Work.EllipticEst.Core.i0Aux
