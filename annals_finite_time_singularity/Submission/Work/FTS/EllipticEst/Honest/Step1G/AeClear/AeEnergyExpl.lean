import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs
import Submission.Work.FTS.EllipticEst.Honest.hksq_eq_w2_sliceIntegral
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.Honest.Step1G.AeClear.AeCutEnergyV2
import Submission.Work.FTS.EllipticEst.H2W.AeProof.FnLintegralLeHkSq
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeCutErr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
noncomputable section
open scoped Real Topology BigOperators ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

theorem restrict_Iz_eq_Ioi' : MeasureTheory.volume.restrict Work.Spaces.Iz
    = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm

theorem cut_mono (n : ℕ) (z : ℝ) :
    Work.FTS.EllipticEst.cut n z ≤ Work.FTS.EllipticEst.cut (n + 1) z := by
  rcases le_or_gt 0 z with hz | hz
  · have h1 : ((n:ℝ)+1) * z - 1 ≤ ((n:ℝ)+1+1) * z - 1 := by nlinarith
    have h2 : z / ((n:ℝ)+1+1) - 2 ≤ z / ((n:ℝ)+1) - 2 := by
      have h2' : (0:ℝ) < (n:ℝ)+1 := by linarith
      have h4 : z / ((n:ℝ)+1+1) ≤ z / ((n:ℝ)+1) :=
        div_le_div_of_nonneg_left hz h2' (by linarith)
      linarith
    have ha : Real.smoothTransition (((n:ℝ)+1) * z - 1)
        ≤ Real.smoothTransition (((n:ℝ)+1+1) * z - 1) := Real.smoothTransition.monotone h1
    have hb : (1 - Real.smoothTransition (z / ((n:ℝ)+1) - 2)) ≤
        (1 - Real.smoothTransition (z / ((n:ℝ)+1+1) - 2)) := by
      have := Real.smoothTransition.monotone h2
      linarith
    have hb0 : (0:ℝ) ≤ 1 - Real.smoothTransition (z / ((n:ℝ)+1) - 2) :=
      sub_nonneg.mpr (Real.smoothTransition.le_one _)
    have ha0 : (0:ℝ) ≤ Real.smoothTransition (((n:ℝ)+1) * z - 1) :=
      Real.smoothTransition.nonneg _
    simp only [Work.FTS.EllipticEst.cut]
    push_cast
    exact mul_le_mul ha hb hb0 (le_trans ha0 ha)
  · have h1 : ((n:ℝ)+1) * z - 1 < 0 := by
      have : (0:ℝ) < (n:ℝ)+1 := by positivity
      nlinarith
    have hzero : Real.smoothTransition (((n:ℝ)+1) * z - 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos h1.le
    have hnc : Work.FTS.EllipticEst.cut n z = 0 := by
      simp only [Work.FTS.EllipticEst.cut]
      push_cast
      rw [hzero, zero_mul]
    rw [hnc]
    exact Work.FTS.EllipticEst.cut_nonneg _ _

theorem cut_tendsto_one {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z) Filter.atTop (nhds 1) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventually_atTop.mpr ⟨Nat.ceil (2 / z) + Nat.ceil z, fun n hn => ?_⟩
  have hnc : (Nat.ceil (2 / z) : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (Nat.le_add_right _ _) hn
  have hzc : (Nat.ceil z : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (Nat.le_add_left _ _) hn
  have h2z : 2 / z ≤ (n : ℝ) := le_trans (Nat.le_ceil _) hnc
  have hz2 : z ≤ (n : ℝ) := le_trans (Nat.le_ceil _) hzc
  have h2n : 2 ≤ (n : ℝ) * z := by rw [div_le_iff₀ hz] at h2z; linarith
  have hA : 2 / ((n : ℝ) + 1) ≤ z := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)]
    nlinarith
  have hB : z ≤ 2 * ((n : ℝ) + 1) := by nlinarith
  exact (Work.FTS.EllipticEst.cut_eq_one_of_mem n hA hB).symm

/-- **The sup over the cut-off family**: for a nonnegative a.e.-measurable `g` on `Iz`,
`⨆_n ∫⁻_z ofReal (cut n z) * g z = ∫⁻_z g z`. -/
theorem iSup_cut_mul {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    (⨆ n : ℕ, ∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (Work.FTS.EllipticEst.cut n z) * g z)
      = ∫⁻ z in Work.Spaces.Iz, g z := by
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun z => ENNReal.ofReal (Work.FTS.EllipticEst.cut n z) * g z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    intro n
    exact ((ENNReal.measurable_ofReal.comp
      ((Work.FTS.EllipticEst.cut_contDiff n).continuous.measurable)).aemeasurable).mul hg
  have hmono : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Monotone (fun n : ℕ => ENNReal.ofReal (Work.FTS.EllipticEst.cut n z) * g z) := by
    refine Filter.Eventually.of_forall fun z m n hmn => ?_
    refine mul_le_mul_of_nonneg_right ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ g z)
    refine ENNReal.ofReal_le_ofReal ?_
    exact Nat.le_induction le_rfl (fun k _ hk => le_trans hk (cut_mono k z)) n hmn
  have hlim : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (Work.FTS.EllipticEst.cut n z) * g z)
        Filter.atTop (nhds (g z)) := by
    rw [restrict_Iz_eq_Ioi']
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun z hz => ?_)
    -- `cut n z = 1` for all large `n`
    have hN : ∃ N : ℕ, ∀ n ≥ N, Work.FTS.EllipticEst.cut n z = 1 := by
      refine ⟨Nat.ceil (2 / z) + Nat.ceil z, fun n hn => ?_⟩
      have hnc : (Nat.ceil (2 / z) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast le_trans (Nat.le_add_right _ _) hn
      have hzc : (Nat.ceil z : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast le_trans (Nat.le_add_left _ _) hn
      have h2z : 2 / z ≤ (n : ℝ) := le_trans (Nat.le_ceil _) hnc
      have hz2 : z ≤ (n : ℝ) := le_trans (Nat.le_ceil _) hzc
      have h2n : 2 ≤ (n : ℝ) * z := by rw [div_le_iff₀ hz] at h2z; linarith
      refine Work.FTS.EllipticEst.cut_eq_one_of_mem n ?_ ?_
      · rw [div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)]; nlinarith
      · nlinarith
    obtain ⟨N, hN⟩ := hN
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_atTop.mpr ⟨N, hN⟩] with n hn
    simp [hn]
  have htend := MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hlim
  have hmonoL : Monotone (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal (Work.FTS.EllipticEst.cut n z) * g z) := by
    intro m n hmn
    refine lintegral_mono fun z => ?_
    refine mul_le_mul_of_nonneg_right ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ g z)
    refine ENNReal.ofReal_le_ofReal ?_
    exact Nat.le_induction le_rfl (fun k _ hk => le_trans hk (cut_mono k z)) n hmn
  exact iSup_eq_of_tendsto hmonoL htend

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

theorem iSup_le_of_eventually {u : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hmono : Monotone u)
    (h : ∀ᶠ n in Filter.atTop, u n ≤ c) : (⨆ n, u n) ≤ c := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  refine iSup_le fun n => ?_
  exact le_trans (hmono (Nat.le_add_right n N)) (hN (n + N) (Nat.le_add_left N n))

theorem cut_hasCompactSupport (n : ℕ) : HasCompactSupport (Work.FTS.EllipticEst.cut n) := by
  have hsub : Function.support (Work.FTS.EllipticEst.cut n) ⊆
      Set.Icc (1 / ((n + 1 : ℕ) : ℝ)) (3 * ((n + 1 : ℕ) : ℝ)) := by
    intro z hz
    simp only [Function.mem_support] at hz
    by_contra hc
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hc
    rcases hc with hc | hc
    · refine hz (Work.FTS.EllipticEst.cut_apply_zero_of_le n ?_)
      push_cast at hc ⊢
      exact le_of_lt hc
    · refine hz (Work.FTS.EllipticEst.cut_apply_zero_of_ge n ?_)
      push_cast at hc ⊢
      exact le_of_lt hc
  have hts : tsupport (Work.FTS.EllipticEst.cut n) ⊆
      Set.Icc (1 / ((n + 1 : ℕ) : ℝ)) (3 * ((n + 1 : ℕ) : ℝ)) :=
    closure_minimal hsub isClosed_Icc
  exact IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hts

theorem cut_contDiff_two (n : ℕ) : ContDiff ℝ 2 (Work.FTS.EllipticEst.cut n) :=
  (Work.FTS.EllipticEst.cut_contDiff n).of_le (by
    rw [Work.Stability.smoothOrder]
    exact WithTop.coe_le_coe.mpr le_top)

theorem cut_zero_of_nonpos (n : ℕ) {z : ℝ} (hz : z ≤ 0) : Work.FTS.EllipticEst.cut n z = 0 :=
  Work.FTS.EllipticEst.cut_apply_zero_of_le n (le_trans hz (by positivity))

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

theorem w_sq_measurable' : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
  have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h]
  exact (Measurable.div ((measurable_const.add measurable_id).pow_const 2)
    (measurable_id.pow_const 2)).pow_const 2

/-- The measurability of the two target integrands. -/
theorem gA_aemeasurable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEMeasurable (fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (Work.FTS.EllipticEst.SmoothOpen.pz hSO).continuousOn
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.1 * Work.Spaces.pz u p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (continuousOn_fst.mul hpz).pow 2
  have h1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 * Work.Spaces.pz u p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).aemeasurable.ennreal_ofReal
  have h2 := h1.lintegral_prod_right'
  have hw : AEMeasurable (fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (w_sq_measurable').aemeasurable.ennreal_ofReal
  exact hw.mul h2

theorem gB_aemeasurable {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEMeasurable (fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hpth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (Work.FTS.EllipticEst.SmoothOpen.pth hSO).continuousOn
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pth u p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hpth.pow 2
  have h1 : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((Work.Spaces.pth u p.1 p.2) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).aemeasurable.ennreal_ofReal
  have h2 := h1.lintegral_prod_right'
  have hw : AEMeasurable (fun z : ℝ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (w_sq_measurable').aemeasurable.ennreal_ofReal
  exact hw.mul h2

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

/-- `sEta` is nonnegative on `Iθ`. -/
theorem sEta_nonneg' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.FTS.EllipticEst.sEta θ := by
  rw [Work.FTS.EllipticEst.sEta]
  refine Real.rpow_nonneg ?_ _
  refine Real.sin_nonneg_of_mem_Icc ⟨?_, ?_⟩ <;> linarith [hθ.1, hθ.2, Real.pi_pos]

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

/-- `P z = ∫_θ (u z θ)^2` is a.e.-strongly measurable. -/
theorem P_aesm {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u := Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (u p.1 p.2) ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hSO.continuousOn).comp (by fun_prop) (fun p hp => hp)).pow 2
  exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

/-- `ofReal (∫ f) ≤ ∫⁻ ofReal f` for a nonnegative a.e.-strongly-measurable `f` on `Iθ`. -/
theorem ofReal_integral_le_lintegral {f : ℝ → ℝ}
    (hae : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (h0 : ∀ θ, 0 ≤ f θ) :
    ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, f θ)
      ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f θ) := by
  rcases eq_or_ne (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (f θ)) ⊤ with h | h
  · rw [h]; exact le_top
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hae
        (Filter.Eventually.of_forall h0)).mp h)
      (Filter.Eventually.of_forall h0)]

/-- **The final step**: a monotone family of truncated inequalities with a vanishing error
gives the limiting inequality. -/
theorem final_step {a : ℝ} {A B : ℝ≥0∞} {An Bn : ℕ → ℝ≥0∞} {R : ℝ≥0∞} {e : ℕ → ℝ}
    (hAmono : Monotone An) (hBmono : Monotone Bn)
    (hA : (⨆ n, An n) = A) (hB : (⨆ n, Bn n) = B)
    (hineq : ∀ n, ENNReal.ofReal a * An n + Bn n ≤ R + ENNReal.ofReal (e n))
    (herr : Filter.Tendsto e Filter.atTop (nhds 0)) (he0 : ∀ n, 0 ≤ e n) :
    ENNReal.ofReal a * A + B ≤ R := by
  have hadd : ∀ (c : ℝ≥0∞) (g : ℕ → ℝ≥0∞), c + (⨆ i, g i) = ⨆ i, (c + g i) := by
    intro c g
    rw [add_comm, ENNReal.iSup_add]
    exact iSup_congr fun i => add_comm _ _
  have hsup : (⨆ n, (ENNReal.ofReal a * An n + Bn n)) = ENNReal.ofReal a * A + B := by
    rw [← hA, ← hB]
    refine le_antisymm ?_ ?_
    · refine iSup_le fun n => ?_
      exact add_le_add (mul_le_mul_of_nonneg_left (le_iSup (f := An) n) (by positivity)) (le_iSup (f := Bn) n)
    · have h1 : ENNReal.ofReal a * (⨆ n, An n) + (⨆ n, Bn n)
          = ⨆ m, ⨆ n, (ENNReal.ofReal a * An m + Bn n) := by
        rw [ENNReal.mul_iSup]
        rw [ENNReal.iSup_add]
        exact iSup_congr fun m => hadd (ENNReal.ofReal a * An m) Bn
      rw [h1]
      refine iSup_le fun m => iSup_le fun n => ?_
      refine le_trans (add_le_add (mul_le_mul_of_nonneg_left (hAmono (le_max_left m n))
        (by positivity)) (hBmono (le_max_right m n))) ?_
      exact le_iSup (f := fun k => ENNReal.ofReal a * An k + Bn k) (max m n)
  have htend : Filter.Tendsto (fun n => ENNReal.ofReal a * An n + Bn n) Filter.atTop
      (nhds (ENNReal.ofReal a * A + B)) := by
    rw [← hsup]
    exact tendsto_atTop_iSup (fun m n hmn => add_le_add
      (mul_le_mul_of_nonneg_left (hAmono hmn) (by positivity)) (hBmono hmn))
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hRlt => ?_
  have hεpos : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  refine le_of_tendsto htend ?_
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 herr) (ε:ℝ) hεpos
  refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  refine le_trans (hineq n) (add_le_add le_rfl ?_)
  have h1 : dist (e n) 0 < (ε:ℝ) := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (he0 n)] at h1
  rw [ENNReal.coe_nnreal_eq]
  exact ENNReal.ofReal_le_ofReal (by linarith [h1])

end Work.FTS.EllipticEst.H2W.AeProof

namespace Work.FTS.EllipticEst.H2W.AeProof
set_option autoImplicit false
set_option linter.unusedVariables false

theorem AeEnergyExpl (α : ℝ) (u G : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)))
    (hL0 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hLπ : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)))
      + (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
    ≤ ENNReal.ofReal (13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)))
        * (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
      + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := by
  set Kn : ℝ := 13 / 2 + (3 * α ^ 2 + (3 / 2) * α * (5 + α)) with hKn
  have hKpos : 0 < Kn := by rw [hKn]; nlinarith [sq_nonneg α, h.1, h.2.1]
  set Mc : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)) with hMc
  set Ac : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2)) with hAc
  set Bc : ℝ≥0∞ := ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
      * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)) with hBc
  have hgoal : ENNReal.ofReal (α ^ 2) * Ac + Bc
      ≤ ENNReal.ofReal Kn * Mc
        + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) := by
    by_cases hMtop : Mc = ⊤
    · have hR : ENNReal.ofReal Kn * Mc
          + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G) = ⊤ := by
        rw [hMtop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hKpos), top_add]
      rw [hR]; exact le_top
    · have hMlt : Mc < ⊤ := lt_top_iff_ne_top.mpr hMtop
      -- the θ-profile `P`
      set P : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 with hPdef
      -- the sup identities
      have hptA : ∀ (n : ℕ) (z : ℝ), ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))
          = ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
            * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2))) := by
        intro n z
        have h1 : ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
            = ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
              * ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * ENNReal.ofReal (z ^ 2) := by
          rw [show Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2
              = Work.FTS.EllipticEst.cut n z * ((Work.Spaces.w z) ^ 2 * z ^ 2) from by ring]
          rw [ENNReal.ofReal_mul (Work.FTS.EllipticEst.cut_nonneg n z),
            ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
          ring
        have h2 : ENNReal.ofReal (z ^ 2) * (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))
            = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2) := by
          rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (z ^ 2))
            (fun θ => ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)) ENNReal.ofReal_ne_top]
          refine lintegral_congr fun θ => ?_
          rw [← ENNReal.ofReal_mul (sq_nonneg z)]
          congr 1
          ring
        rw [h1]
        rw [show ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
              * ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * ENNReal.ofReal (z ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))
            = ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
              * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                * (ENNReal.ofReal (z ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))))
            from by ring]
        rw [h2]
      have hAsup : (⨆ n : ℕ, ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))) = Ac := by
        have hcongr : (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
            = fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
                  * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                    * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((z * Work.Spaces.pz u z θ) ^ 2))) := by
          funext n
          exact lintegral_congr fun z => hptA n z
        rw [hcongr, iSup_cut_mul (gA_aemeasurable h), hAc]
      have hptB : ∀ (n : ℕ) (z : ℝ), ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))
          = ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
            * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
        intro n z
        rw [ENNReal.ofReal_mul (Work.FTS.EllipticEst.cut_nonneg n z)]
        ring
      have hBsup : (⨆ n : ℕ, ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) = Bc := by
        have hcongr : (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
            = fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)
                  * (ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
                    * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
          funext n
          exact lintegral_congr fun z => hptB n z
        rw [hcongr, iSup_cut_mul (gB_aemeasurable h), hBc]
      -- the monotonicity
      have hcutmono : Monotone (fun n : ℕ => fun z : ℝ => ENNReal.ofReal (Work.FTS.EllipticEst.cut n z)) :=
        fun m n hmn z => ENNReal.ofReal_le_ofReal
          (Nat.le_induction le_rfl (fun k _ hk => le_trans hk (cut_mono k z)) n hmn)
      have hAmono : Monotone (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2))) := by
        intro m n hmn
        refine lintegral_mono fun z => ?_
        rw [hptA n z, hptA m z]
        exact mul_le_mul_of_nonneg_right (hcutmono hmn z) (bot_le : (⊥ : ℝ≥0∞) ≤ _)
      have hBmono : Monotone (fun n : ℕ => ∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
              * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2))) := by
        intro m n hmn
        refine lintegral_mono fun z => ?_
        rw [hptB n z, hptB m z]
        exact mul_le_mul_of_nonneg_right (hcutmono hmn z) (bot_le : (⊥ : ℝ≥0∞) ≤ _)
      -- the crux for each `n`
      have hcrux : ∀ n : ℕ,
          ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2 * z ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pz u z θ) ^ 2)))
            + (∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((Work.Spaces.pth u z θ) ^ 2)))
          ≤ ENNReal.ofReal Kn * (∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
            + ENNReal.ofReal (1 / 2) * (∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
            + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
                  (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                      * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                    + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                      * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
                + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                    |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z)) := by
        intro n
        have hMcut : (∫⁻ z in Work.Spaces.Iz,
              ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2))) ≠ ⊤ := by
          refine ne_top_of_le_ne_top hMtop (lintegral_mono fun z => ?_)
          refine mul_le_mul_of_nonneg_right ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ _)
          exact ENNReal.ofReal_le_ofReal (by
            have h1 := Work.FTS.EllipticEst.cut_le_one n z
            have h2 : (0:ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
            nlinarith)
        have hcutδ : ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → Work.FTS.EllipticEst.cut n z = 0 :=
          ⟨1 / ((n : ℝ) + 1), by
            have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
            exact div_pos one_pos h,
            fun z hz => Work.FTS.EllipticEst.cut_apply_zero_of_le n hz⟩
        have hres := AeCutEnergyV2 α u G h hC hL0 hLπ (Work.FTS.EllipticEst.cut n)
          (cut_contDiff_two n) (cut_hasCompactSupport n) (fun z hz => cut_zero_of_nonpos n hz)
          (Work.FTS.EllipticEst.cut_nonneg n) (Work.FTS.EllipticEst.cut_le_one n) hcutδ hMcut
        rw [hKn]
        exact hres
      -- ### the properties of `P`
      have hE0P : ∀ z : ℝ, 0 ≤ P z := by
        intro z; rw [hPdef]; exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
      have hslice_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          MeasureTheory.AEStronglyMeasurable (fun θ => (u z θ) ^ 2)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        rw [restrict_Iz_eq_Ioi']
        refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall fun z hz => ?_)
        have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
          Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
        have h1 : ContinuousOn (fun θ => (u z θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
          ((Work.FTS.EllipticEst.SmoothOpen.curry_θ hSO hz).continuousOn).pow 2
        have h2 : MeasureTheory.AEStronglyMeasurable (fun θ => (u z θ) ^ 2)
            (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
          h1.aestronglyMeasurable measurableSet_Ioo
        rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := Real.pi / 2))]
        exact h2
      have hcmp : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          ENNReal.ofReal (P z) ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2) := by
        filter_upwards [hslice_ae] with z hz
        rw [hPdef]
        exact ofReal_integral_le_lintegral hz (fun θ => sq_nonneg _)
      have hw2P : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * P z)) ≠ ⊤ := by
        have h1 : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * P z))
            = ∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal ((Work.Spaces.w z) ^ 2) * ENNReal.ofReal (P z) := by
          refine lintegral_congr fun z => ?_
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
        rw [h1]
        refine ne_top_of_le_ne_top hMtop ?_
        rw [hMc]
        refine lintegral_mono_ae ?_
        filter_upwards [hcmp] with z hz
        exact mul_le_mul_of_nonneg_left hz (bot_le : (⊥ : ℝ≥0∞) ≤ _)
      have hPmeas : MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 * P z)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        (w_sq_measurable'.aestronglyMeasurable).mul (P_aesm h)
      have hE2 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * P z)
          Work.Spaces.Iz :=
        (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hPmeas
          (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hE0P z))).mp hw2P
      have hE1 : MeasureTheory.IntegrableOn P Work.Spaces.Iz := by
        refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (P_aesm h)
          (Filter.Eventually.of_forall hE0P)).mp ?_
        refine ne_top_of_le_ne_top hw2P (lintegral_mono_ae ?_)
        have h0 : ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 := by
          rw [MeasureTheory.ae_iff]; simp
        rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
        filter_upwards [h0] with z hz hzI
        have hz0 : (0:ℝ) < z := lt_of_le_of_ne hzI (Ne.symm hz)
        rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (hE0P z))]
        have hw : (1:ℝ) ≤ (Work.Spaces.w z) ^ 2 := by
          rw [Work.Spaces.w, div_pow, le_div_iff₀ (by positivity : (0:ℝ) < (z^2)^2)]
          have h1 : (0:ℝ) ≤ 1 + z := by linarith
          have h2 : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith [h1]
          calc (1:ℝ) * (z ^ 2) ^ 2 = (z ^ 2) ^ 2 := by ring
            _ ≤ ((1 + z) ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg z) h2 2
        nlinarith [hE0P z, hw]
      -- the nonnegativity of the two error integrals
      have hErrA0 : ∀ n : ℕ, 0 ≤ (∫ z in Work.Spaces.Iz,
            (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
              + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z) := by
        intro n
        exact MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z _ => by
          have hPz := hE0P z
          have h1 : (0:ℝ) ≤ 2 * |deriv (Work.FTS.EllipticEst.cut n) z|
              * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
              + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                * (z ^ 2 * (Work.Spaces.w z) ^ 2) := by positivity
          exact mul_nonneg h1 hPz
      have hErrB0 : ∀ n : ℕ, 0 ≤ (∫ z in Work.Spaces.Iz,
            |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z) := by
        intro n
        exact MeasureTheory.setIntegral_nonneg measurableSet_Ici fun z hz => by
          have hPz := hE0P z
          exact mul_nonneg (mul_nonneg (abs_nonneg _)
            (mul_nonneg hz (sq_nonneg _))) hPz
      -- the error convergence
      have herr : Filter.Tendsto (fun n : ℕ => (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                  * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                  * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
            + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z))
          Filter.atTop (nhds 0) := by
        have hsum := AeCutErr P hE0P (P_aesm h) hE1 hE2
        set Cst : ℝ := max (α ^ 2 / 2) (α * (5 + α) / 2) with hCst
        have hCst0 : 0 ≤ Cst := by rw [hCst]; exact le_max_of_le_left (by positivity)
        have hg : Filter.Tendsto (fun n : ℕ => Cst * ((∫ z in Work.Spaces.Iz,
              (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                  * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                  * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
            + (∫ z in Work.Spaces.Iz,
                |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z)))
            Filter.atTop (nhds 0) := by
          have := hsum.const_mul Cst
          simpa using this
        refine squeeze_zero (f := fun n : ℕ => (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                  * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                  * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
            + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z))
          (g := fun n : ℕ => Cst * ((∫ z in Work.Spaces.Iz,
              (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                  * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                  * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
            + (∫ z in Work.Spaces.Iz,
                |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z)))
          (fun n => ?_)
          (fun n => ?_) hg
        · have h1 := hErrA0 n
          have h2 := hErrB0 n
          have h3 : (0:ℝ) ≤ α ^ 2 / 2 := by positivity
          have h4 : (0:ℝ) ≤ α * (5 + α) / 2 := by nlinarith [h.1, h.2.1]
          nlinarith [mul_nonneg h3 h1, mul_nonneg h4 h2]
        · have h1 := hErrA0 n
          have h2 := hErrB0 n
          have h3 : (0:ℝ) ≤ α ^ 2 / 2 := by positivity
          have h4 : (0:ℝ) ≤ α * (5 + α) / 2 := by nlinarith [h.1, h.2.1]
          have h5 : α ^ 2 / 2 ≤ Cst := by rw [hCst]; exact le_max_left _ _
          have h6 : α * (5 + α) / 2 ≤ Cst := by rw [hCst]; exact le_max_right _ _
          nlinarith [mul_le_mul_of_nonneg_right h5 h1, mul_le_mul_of_nonneg_right h6 h2,
            mul_nonneg hCst0 h1, mul_nonneg hCst0 h2]
      have he0 : ∀ n : ℕ, 0 ≤ (α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
              (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                  * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                  * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
            + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z) := by
        intro n
        have h1 := hErrA0 n
        have h2 := hErrB0 n
        have h3 : (0:ℝ) ≤ α ^ 2 / 2 := by positivity
        have h4 : (0:ℝ) ≤ α * (5 + α) / 2 := by nlinarith [h.1, h.2.1]
        nlinarith [mul_nonneg h3 h1, mul_nonneg h4 h2]
      -- the RHS bound
      have hRHS : ∀ n : ℕ,
          ENNReal.ofReal Kn * (∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((u z θ) ^ 2)))
            + ENNReal.ofReal (1 / 2) * (∫⁻ z in Work.Spaces.Iz,
                ENNReal.ofReal (Work.FTS.EllipticEst.cut n z * (Work.Spaces.w z) ^ 2)
                  * (∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal ((G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
            + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
                  (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                      * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                    + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                      * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
                + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                    |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z))
          ≤ ENNReal.ofReal Kn * Mc
            + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Work.Spaces.HkSq α 0 G)
            + ENNReal.ofReal ((α ^ 2 / 2) * (∫ z in Work.Spaces.Iz,
                  (2 * |deriv (Work.FTS.EllipticEst.cut n) z|
                      * |deriv (fun z => z ^ 2 * (Work.Spaces.w z) ^ 2) z|
                    + |deriv (deriv (Work.FTS.EllipticEst.cut n)) z|
                      * (z ^ 2 * (Work.Spaces.w z) ^ 2)) * P z)
                + (α * (5 + α) / 2) * (∫ z in Work.Spaces.Iz,
                    |deriv (Work.FTS.EllipticEst.cut n) z| * (z * (Work.Spaces.w z) ^ 2) * P z)) := by
        intro n
        refine add_le_add (add_le_add ?_ ?_) le_rfl
        · refine mul_le_mul_of_nonneg_left ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ _)
          rw [hMc]
          refine lintegral_mono fun z => ?_
          refine mul_le_mul_of_nonneg_right ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ _)
          exact ENNReal.ofReal_le_ofReal (by
            have h1 := Work.FTS.EllipticEst.cut_le_one n z
            have h2 : (0:ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
            nlinarith)
        · refine mul_le_mul_of_nonneg_left ?_ (bot_le : (⊥ : ℝ≥0∞) ≤ _)
          exact FnLintegralLeHkSq h.memG (Work.FTS.EllipticEst.cut n)
            (Work.FTS.EllipticEst.cut_nonneg n) (Work.FTS.EllipticEst.cut_le_one n)
      refine final_step (a := α ^ 2) hAmono hBmono hAsup hBsup ?_ herr he0
      intro n
      exact le_trans (hcrux n) (hRHS n)
  rwa [hAc, hBc, hMc, hKn] at hgoal

end Work.FTS.EllipticEst.H2W.AeProof
