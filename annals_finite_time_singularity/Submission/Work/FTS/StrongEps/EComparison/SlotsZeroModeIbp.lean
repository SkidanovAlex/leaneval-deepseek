/-
# `SlotsZeroModeIbp` - the per-`n` self-adjointness identity and the boundary layers

Part of `Work.FTS.StrongEps.EComparison.SlotsZeroModeODE`; see `SlotsZeroModeMain` for the
overview.  Contents:

* `perN_zero` - the proved `bslOp_ibp` identity applied to the cut-off test function
  `rho (x) (chi_n (x) e_m)`, in iterated-integral form;
* the boundary-layer estimates `layer_slice_le`, `layer_integral_le` and `tendsto_delta_rpow`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.bslOp_ibp
import Submission.Work.FTS.ClassC.psiTrunc_uncurry_smooth
import Submission.Work.FTS.H2.ModalSolR.PerModeBasic
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeMain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The per-`n` integration-by-parts identity -/

/-- **The `bslOp_ibp` identity for the cut-off test function**, in the iterated (Fubini) form
that matches the target statement. -/
theorem perN_zero {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hsol : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < π / 2 → Work.Elliptic.bslOp α Φ z θ = 0)
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) (hρc : HasCompactSupport ρ) (hρs : tsupport ρ ⊆ Set.Ioi 0)
    (hCut : CutFacts m) (n : ℕ) :
    (∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
      Φ z θ * Work.Elliptic.bslOp α (modeTest m ρ n) z θ
        * (z ^ ((5 - α) / α) * Real.cos θ)) = 0 := by
  classical
  have hφ := modeTest_contDiff (m := m) (n := n) hρ hCut
  have hφc := modeTest_hasCompactSupport (m := m) (n := n) hρc hCut
  have hφs := modeTest_tsupport_subset_Q0 (m := m) (n := n) hρs hCut
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, hbox⟩ :=
    Work.EllipticEst.ModalSolution.box_of_compactSupport hφc hφs
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc hp.2.1,
      lt_of_le_of_lt hp.2.2 hd⟩
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen Φ :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mpr (fun k => hsm k)
  have htestsm : Work.FTS.EllipticEst.SmoothOpen (modeTest m ρ n) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mpr (fun k => (hφ k).contDiffOn)
  have h1 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => Φ p.1 p.2
      * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0 := by
    refine integrableOn_Q0_of_box ha hab.le hc hcd.le hd (fun p hp => ?_) ?_
    · rw [Work.FTS.H2.ModalSolR.bslOp_eq_zero_off_box (α := α) hbox hp]
      ring
    · exact ((hΦsm.continuousOn.mono hKsub).mul
        ((continuousOn_bslOp_of_smoothOpen htestsm).mono hKsub)).mul
          ((continuousOn_weight α).mono hKsub)
  have h2 : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      (Work.Elliptic.bslOp α Φ p.1 p.2) * (modeTest m ρ n) p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) Work.FTS.EllipticEst.Q0 := by
    refine (integrableOn_zero (s := Work.FTS.EllipticEst.Q0)).congr_fun
      (fun p hp => ?_) Work.FTS.EllipticEst.isOpen_Q0.measurableSet
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    rw [hsol p.1 hz p.2 hθ0 hθ1, zero_mul, zero_mul]
  have hibp := Work.EllipticEst.ModalSolution.bslOp_ibp α (u := Φ) (φ := modeTest m ρ n)
    hsm hφ hφc hφs h1 h2
  have hR : (∫ p in Work.FTS.EllipticEst.Q0, (Work.Elliptic.bslOp α Φ p.1 p.2)
      * (modeTest m ρ n) p.1 p.2 * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = 0 := by
    have hcongr := MeasureTheory.setIntegral_congr_fun (μ := volume)
      (f := fun p : ℝ × ℝ => (Work.Elliptic.bslOp α Φ p.1 p.2) * (modeTest m ρ n) p.1 p.2
        * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) (g := fun _ => (0 : ℝ))
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet (fun p hp => by
        obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        show (Work.Elliptic.bslOp α Φ p.1 p.2) * (modeTest m ρ n) p.1 p.2
          * (p.1 ^ ((5 - α) / α) * Real.cos p.2) = 0
        rw [hsol p.1 hz p.2 hθ0 hθ1]
        ring)
    rw [hcongr]
    simp
  have hkey : (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
      * Work.Elliptic.bslOp α (modeTest m ρ n) p.1 p.2
      * (p.1 ^ ((5 - α) / α) * Real.cos p.2)) = 0 := by
    rw [hibp, hR]
  have hprod : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (π / 2),
      Φ z θ * Work.Elliptic.bslOp α (modeTest m ρ n) z θ
        * (z ^ ((5 - α) / α) * Real.cos θ)) = 0 := by
    have h := hkey
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] at h
    rw [Work.FTS.EllipticEst.Q0] at h
    have hint := h1
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] at hint
    rw [Work.FTS.EllipticEst.Q0] at hint
    rw [MeasureTheory.setIntegral_prod _ hint] at h
    exact h
  rw [show (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (π / 2),
      Φ z θ * Work.Elliptic.bslOp α (modeTest m ρ n) z θ
        * (z ^ ((5 - α) / α) * Real.cos θ))
      = ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
      Φ z θ * Work.Elliptic.bslOp α (modeTest m ρ n) z θ
        * (z ^ ((5 - α) / α) * Real.cos θ) from by
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => ?_)
    change (∫ θ in Set.Ioo 0 (π / 2), Φ z θ * Work.Elliptic.bslOp α (modeTest m ρ n) z θ
        * (z ^ ((5 - α) / α) * Real.cos θ))
      = ∫ θ in Set.Icc 0 (π / 2), Φ z θ * Work.Elliptic.bslOp α (modeTest m ρ n) z θ
        * (z ^ ((5 - α) / α) * Real.cos θ)
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]] at hprod
  exact hprod

/-! ## The boundary layers -/

lemma indicator_one_nonneg {A : Set ℝ} (θ : ℝ) : 0 ≤ A.indicator (fun _ => (1 : ℝ)) θ := by
  classical
  rw [Set.indicator_apply]; split_ifs <;> norm_num

lemma indicator_one_le_one {A : Set ℝ} (θ : ℝ) : A.indicator (fun _ => (1 : ℝ)) θ ≤ 1 := by
  classical
  rw [Set.indicator_apply]; split_ifs <;> norm_num

theorem layer_eq_union (n : ℕ) :
    layer n = Set.Ioo 0 (2 * delta n) ∪ Set.Ioo (π / 2 - 2 * delta n) (π / 2) := rfl

/-- The indicator of a measurable set, as a `[0,1]`-valued multiplier, preserves integrability. -/
theorem integrableOn_mul_indicator {f : ℝ → ℝ} {s A : Set ℝ} (hf : MeasureTheory.IntegrableOn f s)
    (hA : MeasurableSet A) (hf0 : ∀ x, 0 ≤ f x) :
    MeasureTheory.IntegrableOn (fun θ => f θ * A.indicator (fun _ => (1 : ℝ)) θ) s := by
  rw [MeasureTheory.IntegrableOn] at hf ⊢
  refine Integrable.mono' hf (hf.aestronglyMeasurable.mul
    (Measurable.aestronglyMeasurable (measurable_const.indicator hA))) ?_
  filter_upwards with θ
  rw [Real.norm_of_nonneg (mul_nonneg (hf0 θ)
    (indicator_one_nonneg θ))]
  calc f θ * A.indicator (fun _ => (1 : ℝ)) θ ≤ f θ * 1 :=
        mul_le_mul_of_nonneg_left (indicator_one_le_one θ) (hf0 θ)
    _ = f θ := mul_one _

/-- Integrate against the indicator of a set contained in the domain. -/
theorem setIntegral_mul_indicator {f : ℝ → ℝ} {A s : Set ℝ} (hA : MeasurableSet A)
    (hsub : A ⊆ s) :
    (∫ θ in s, f θ * A.indicator (fun _ => (1 : ℝ)) θ) = ∫ θ in A, f θ := by
  rw [show (fun θ => f θ * A.indicator (fun _ => (1 : ℝ)) θ) = A.indicator (fun θ => f θ) from by
    funext θ
    by_cases h : θ ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]]
  rw [MeasureTheory.setIntegral_indicator hA, Set.inter_eq_right.mpr hsub]

theorem layer_left_subset_Iθ {n : ℕ} (hn : 2 * delta n ≤ π / 4) :
    Set.Ioo 0 (2 * delta n) ⊆ Work.Spaces.Iθ := fun θ hθ =>
  ⟨le_of_lt hθ.1, by linarith [hθ.2, hn, Real.pi_pos]⟩

theorem layer_right_subset_Iθ {n : ℕ} (hn : 2 * delta n ≤ π / 4) :
    Set.Ioo (π / 2 - 2 * delta n) (π / 2) ⊆ Work.Spaces.Iθ := fun θ hθ =>
  ⟨by linarith [hθ.1, hn, Real.pi_pos], le_of_lt hθ.2⟩

/-- **The per-slice layer bound**: the part of `∫_θ |Φ|` sitting in the layer is controlled by
`√(sliceEnergy Φ z)·δ^{(3+η)/2}`. -/
theorem layer_slice_le {Φ : ℝ → ℝ → ℝ} {C : ℝ}
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hC : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (π / 4),
      (∫ θ in Set.Ioo 0 δ, |Φ z θ|
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)) ∧
      (∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)))
    {z : ℝ} (hz : 0 < z) {n : ℕ} (hn0 : 0 < 2 * delta n)
    (hn1 : 2 * delta n ≤ π / 4) :
    (∫ θ in Work.Spaces.Iθ, |Φ z θ| * layerInd n θ)
      ≤ 2 * C * Real.sqrt (sliceEnergy Φ z) * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2) := by
  obtain ⟨hAb, hBb⟩ := hC z (Set.mem_Ioi.mpr hz) (2 * delta n) ⟨hn0, hn1⟩
  have hAmeas : MeasurableSet (Set.Ioo 0 (2 * delta n)) := measurableSet_Ioo
  have hBmeas : MeasurableSet (Set.Ioo (π / 2 - 2 * delta n) (π / 2)) := measurableSet_Ioo
  have hint := hΦint z (Set.mem_Ioi.mpr hz)
  have h1 : MeasureTheory.IntegrableOn
      (fun θ => |Φ z θ| * (Set.Ioo 0 (2 * delta n)).indicator (fun _ => (1 : ℝ)) θ)
      Work.Spaces.Iθ := integrableOn_mul_indicator hint hAmeas (fun θ => abs_nonneg _)
  have h2 : MeasureTheory.IntegrableOn
      (fun θ => |Φ z θ| * (Set.Ioo (π / 2 - 2 * delta n) (π / 2)).indicator (fun _ => (1 : ℝ)) θ)
      Work.Spaces.Iθ := integrableOn_mul_indicator hint hBmeas (fun θ => abs_nonneg _)
  have hpt : ∀ θ : ℝ, |Φ z θ| * layerInd n θ
      ≤ |Φ z θ| * (Set.Ioo 0 (2 * delta n)).indicator (fun _ => (1 : ℝ)) θ
        + |Φ z θ| * (Set.Ioo (π / 2 - 2 * delta n) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
    intro θ
    by_cases h : θ ∈ layer n
    · have hge : 1 ≤ (Set.Ioo 0 (2 * delta n)).indicator (fun _ => (1 : ℝ)) θ
          + (Set.Ioo (π / 2 - 2 * delta n) (π / 2)).indicator (fun _ => (1 : ℝ)) θ := by
        rw [layer_eq_union] at h
        rcases h with h | h
        · rw [Set.indicator_of_mem h]
          linarith [indicator_one_nonneg (A := Set.Ioo (π / 2 - 2 * delta n) (π / 2)) θ]
        · rw [Set.indicator_of_mem h]
          linarith [indicator_one_nonneg (A := Set.Ioo 0 (2 * delta n)) θ]
      rw [layerInd, Set.indicator_of_mem h, mul_one]
      nlinarith [abs_nonneg (Φ z θ), hge,
        indicator_one_nonneg (A := Set.Ioo 0 (2 * delta n)) θ,
        indicator_one_nonneg (A := Set.Ioo (π / 2 - 2 * delta n) (π / 2)) θ]
    · rw [layerInd, Set.indicator_of_notMem h, mul_zero]
      exact add_nonneg (mul_nonneg (abs_nonneg _) (indicator_one_nonneg _))
        (mul_nonneg (abs_nonneg _) (indicator_one_nonneg _))
  have hsum : MeasureTheory.IntegrableOn (fun θ => |Φ z θ|
      * (Set.Ioo 0 (2 * delta n)).indicator (fun _ => (1 : ℝ)) θ
      + |Φ z θ| * (Set.Ioo (π / 2 - 2 * delta n) (π / 2)).indicator (fun _ => (1 : ℝ)) θ)
      Work.Spaces.Iθ := h1.add h2
  refine (integral_mono_of_nonneg (Eventually.of_forall fun θ => mul_nonneg (abs_nonneg _)
      (indicator_one_nonneg θ)) hsum (Eventually.of_forall hpt)).trans ?_
  have hsum' : (∫ θ in Work.Spaces.Iθ, |Φ z θ|
      * (Set.Ioo 0 (2 * delta n)).indicator (fun _ => (1 : ℝ)) θ
      + |Φ z θ| * (Set.Ioo (π / 2 - 2 * delta n) (π / 2)).indicator (fun _ => (1 : ℝ)) θ)
      = (∫ θ in Set.Ioo 0 (2 * delta n), |Φ z θ|)
        + ∫ θ in Set.Ioo (π / 2 - 2 * delta n) (π / 2), |Φ z θ| := by
    rw [MeasureTheory.integral_add h1 h2,
      setIntegral_mul_indicator hAmeas (layer_left_subset_Iθ hn1),
      setIntegral_mul_indicator hBmeas (layer_right_subset_Iθ hn1)]
  rw [hsum']
  linarith

/-- **The layer integral over a compact `z`-range**. -/
theorem layer_integral_le {Φ : ℝ → ℝ → ℝ} {C : ℝ} {a b : ℝ}
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hC : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (π / 4),
      (∫ θ in Set.Ioo 0 δ, |Φ z θ|
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)) ∧
      (∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|
          ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)))
    (hEint : MeasureTheory.IntegrableOn (fun z => Real.sqrt (sliceEnergy Φ z)) (Set.Icc a b))
    (ha : 0 < a) {n : ℕ} (hn0 : 0 < 2 * delta n) (hn1 : 2 * delta n ≤ π / 4) :
    (∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ, |Φ z θ| * layerInd n θ)
      ≤ 2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)
          * (∫ z in Set.Icc a b, Real.sqrt (sliceEnergy Φ z)) := by
  have hmono : (∫ z in Set.Icc a b, ∫ θ in Work.Spaces.Iθ, |Φ z θ| * layerInd n θ)
      ≤ ∫ z in Set.Icc a b,
          2 * C * Real.sqrt (sliceEnergy Φ z) * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => integral_nonneg fun θ =>
      mul_nonneg (abs_nonneg _) (indicator_one_nonneg θ))
      ?_ (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun z hz => ?_)
    · have h0 := hEint.integrable.const_mul
          (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2))
      exact h0.congr (Eventually.of_forall fun z => by ring)
    · exact layer_slice_le hΦint hC (lt_of_lt_of_le ha hz.1) hn0 hn1
  refine hmono.trans ?_
  rw [show (fun z => 2 * C * Real.sqrt (sliceEnergy Φ z)
        * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2))
      = fun z => (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2))
          * Real.sqrt (sliceEnergy Φ z) from by funext z; ring]
  rw [MeasureTheory.integral_const_mul]

/-- `δ_n^s → 0` for every `s > 0`. -/
theorem tendsto_delta_rpow {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => (delta n) ^ s) atTop (𝓝 0) := by
  have hcomp : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := (tendsto_rpow_neg_atTop hs).comp hcomp
  refine h.congr' ?_
  filter_upwards with n
  rw [Function.comp_apply, delta, one_div]
  exact (Real.rpow_neg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) s).trans
    (Real.inv_rpow (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) s).symm

end Work.FTS.StrongEps.EComparison
