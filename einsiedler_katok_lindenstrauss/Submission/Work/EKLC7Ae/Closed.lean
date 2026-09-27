import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLRelCross.continuous_lintegral_comp_mul
import Submission.Work.EKLRelCross.exists_compact_nhds_comp_mul_support
import Submission.Work.EKLProd.measure_ext_of_cc
import Submission.Work.EKLC7Ae.Endgame

/-!
# `Work.EKLC7Ae.Closed` — the quasi-invariance set of a Radon measure on `SL₃(ℝ)` is closed

For a non-zero measure `σ` on `SL₃(ℝ)` finite on compact sets, the set

`QuasiInvLeft σ = {u | ∃ c ≠ 0, c ≠ ⊤, σ.map (g ↦ u * g) = c • σ}`

is closed.  This is the input that upgrades quasi-invariance from a countable dense set of
multipliers to the whole subgroup `U` in `Work.EKLC7Ae.aeHaar_of_shape_propor`.

The proof is the standard one by test functions: for `f : C_c(SL₃(ℝ), ℝ≥0)` put
`Phi σ f u = ∫⁻ x, ↑(f (u * x)) ∂σ`.  Each `u ↦ Phi σ f u` is continuous (dominated convergence),
so the "test locus" `K = {u | ∀ f g, Phi σ f u * Phi σ g 1 = Phi σ g u * Phi σ f 1}` is closed;
and `u` is quasi-invariant if and only if `Phi σ f u = c * Phi σ f 1` for all `f`, which is
exactly the defining condition of `K`.  The last equivalence uses that a non-zero Radon measure
has a compactly supported continuous test function with non-zero integral, and that two Radon
measures with equal integrals against all `C_c` functions coincide
(`Work.EKLProd.measure_ext_of_cc`).
-/

namespace Work.EKLC7Ae

open MeasureTheory Filter Topology
open scoped ENNReal NNReal CompactlySupported
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## 1. The test functional and its continuity -/

/-- The `σ`-mass of the left translate by `u` of a compactly supported continuous test function. -/
def Phi (σ : MeasureTheory.Measure SL3) (f : C_c(SL3, ℝ≥0)) (u : SL3) : ℝ≥0∞ :=
  ∫⁻ x, ((f (u * x) : ℝ≥0) : ℝ≥0∞) ∂σ

/-- `Phi σ f u` is the integral of `f` against the push-forward of `σ` by left translation. -/
theorem Phi_map (σ : MeasureTheory.Measure SL3) (f : C_c(SL3, ℝ≥0)) (u : SL3) :
    Phi σ f u = ∫⁻ y, ((f y : ℝ≥0) : ℝ≥0∞) ∂(σ.map (fun g : SL3 => u * g)) := by
  rw [Phi]
  exact (MeasureTheory.lintegral_map (f := fun y : SL3 => ((f y : ℝ≥0) : ℝ≥0∞))
    (g := fun g : SL3 => u * g) (ENNReal.continuous_coe.comp f.continuous).measurable
    (continuous_const.mul continuous_id).measurable).symm

@[simp]
theorem Phi_one (σ : MeasureTheory.Measure SL3) (f : C_c(SL3, ℝ≥0)) :
    Phi σ f 1 = ∫⁻ x, ((f x : ℝ≥0) : ℝ≥0∞) ∂σ := by
  rw [Phi]
  simp

/-- A compactly supported continuous `ℝ≥0`-valued function is bounded. -/
theorem exists_bound_cc (f : C_c(SL3, ℝ≥0)) : ∃ C : ℝ≥0, ∀ x, f x ≤ C := by
  have hKc : IsCompact (tsupport (fun x : SL3 => (f x : ℝ≥0))) := f.hasCompactSupport'
  have hbdd : BddAbove ((fun x : SL3 => (f x : ℝ≥0)) '' tsupport (fun x : SL3 => (f x : ℝ≥0))) :=
    (hKc.image f.continuous).bddAbove
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨C, fun x => ?_⟩
  by_cases hx : f x = 0
  · rw [hx]; simp
  · exact hC ⟨x, subset_tsupport _ (Function.mem_support.mpr hx), rfl⟩

/-- `∫⁻ ↑f ∂σ` is finite for `σ` finite on compact sets. -/
theorem lintegral_cc_lt_top (σ : MeasureTheory.Measure SL3)
    (hσ : MeasureTheory.IsFiniteMeasureOnCompacts σ) (f : C_c(SL3, ℝ≥0)) :
    ∫⁻ x, ((f x : ℝ≥0) : ℝ≥0∞) ∂σ < ⊤ := by
  haveI := hσ
  obtain ⟨C, hC⟩ := exists_bound_cc f
  set K : Set SL3 := tsupport (fun x : SL3 => (f x : ℝ≥0)) with hK
  have hKc : IsCompact K := f.hasCompactSupport'
  have hle : ∀ x, ((f x : ℝ≥0) : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (K.indicator (1 : SL3 → ℝ≥0∞) x) := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]; exact_mod_cast hC x
    · have h0 : f x = 0 := by
        by_contra hne
        exact hx (subset_tsupport _ (Function.mem_support.mpr hne))
      rw [h0]; simp
  calc ∫⁻ x, ((f x : ℝ≥0) : ℝ≥0∞) ∂σ
      ≤ ∫⁻ x, (C : ℝ≥0∞) * (K.indicator (1 : SL3 → ℝ≥0∞) x) ∂σ :=
        MeasureTheory.lintegral_mono hle
    _ = (C : ℝ≥0∞) * ∫⁻ x, (K.indicator (1 : SL3 → ℝ≥0∞) x) ∂σ := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    _ = (C : ℝ≥0∞) * σ K := by
        rw [MeasureTheory.lintegral_indicator_one hKc.isClosed.measurableSet]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (hσ.lt_top_of_isCompact hKc)

/-- `Phi σ f u` is finite. -/
theorem Phi_lt_top (σ : MeasureTheory.Measure SL3) (hσ : MeasureTheory.IsFiniteMeasureOnCompacts σ)
    (f : C_c(SL3, ℝ≥0)) (u : SL3) : Phi σ f u < ⊤ := by
  haveI := hσ
  rw [Phi_map]
  have h := MeasureTheory.Measure.IsFiniteMeasureOnCompacts.map σ (Homeomorph.mulLeft u)
  exact lintegral_cc_lt_top (σ.map (fun g : SL3 => u * g)) h f

/-- **Continuity of the test functional**: dominated convergence. -/
theorem continuous_lintegral_comp_mul_bound (σ : MeasureTheory.Measure SL3)
    (hσ : MeasureTheory.IsFiniteMeasureOnCompacts σ) (F : SL3 → ℝ≥0∞) (hF : Continuous F)
    (hFs : HasCompactSupport F) (C : ℝ≥0) (hC : ∀ x, F x ≤ (C : ℝ≥0∞)) :
    Continuous (fun w : SL3 => ∫⁻ x, F (w * x) ∂σ) := by
  haveI := hσ
  rw [continuous_iff_continuousAt]
  intro w₀
  obtain ⟨B, U, hBcomp, hU, hBU⟩ :=
    Work.EKLRelCross.exists_compact_nhds_comp_mul_support F hFs w₀
  refine MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
    (μ := σ) (l := 𝓝 w₀) (F := fun w x => F (w * x)) (f := fun x => F (w₀ * x))
    (fun x => (C : ℝ≥0∞) * B.indicator (1 : SL3 → ℝ≥0∞) x) ?_ ?_ ?_ ?_
  · filter_upwards with w
    exact (hF.comp (continuous_const.mul continuous_id)).measurable
  · filter_upwards [hU] with w hw
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]; exact hC (w * x)
    · rw [Set.indicator_of_notMem hx, mul_zero]
      exact le_of_eq (by by_contra hne; exact hx (hBU w hw x hne))
  · refine ne_of_lt ?_
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top,
      MeasureTheory.lintegral_indicator_one hBcomp.isClosed.measurableSet]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hσ.lt_top_of_isCompact hBcomp)
  · filter_upwards with x
    exact (hF.comp (continuous_id.mul continuous_const)).continuousAt

/-- `u ↦ Phi σ f u` is continuous. -/
theorem Phi_cont (σ : MeasureTheory.Measure SL3) (hσ : MeasureTheory.IsFiniteMeasureOnCompacts σ)
    (f : C_c(SL3, ℝ≥0)) : Continuous (fun u : SL3 => Phi σ f u) := by
  obtain ⟨C, hC⟩ := exists_bound_cc f
  have hF : Continuous (fun x : SL3 => ((f x : ℝ≥0) : ℝ≥0∞)) :=
    ENNReal.continuous_coe.comp f.continuous
  have hFs : HasCompactSupport (fun x : SL3 => ((f x : ℝ≥0) : ℝ≥0∞)) := by
    refine HasCompactSupport.of_support_subset_isCompact f.hasCompactSupport' ?_
    intro x hx
    simp only [Function.mem_support] at hx
    exact subset_tsupport _ (Function.mem_support.mpr fun h0 => hx (by simpa using h0))
  have key := continuous_lintegral_comp_mul_bound σ hσ (fun x : SL3 => ((f x : ℝ≥0) : ℝ≥0∞))
    hF hFs C (fun x => by exact_mod_cast hC x)
  simpa only [Phi] using key

/-! ## 2. `ℝ≥0`-valued truncations of real test functions -/

/-- The `ℝ≥0`-valued truncation `x ↦ max (g x) 0` of a compactly supported continuous real
function, as a compactly supported continuous `ℝ≥0`-valued function. -/
def ccNNReal (g : C_c(SL3, ℝ)) : C_c(SL3, ℝ≥0) :=
  ⟨⟨fun x => (g x).toNNReal, continuous_real_toNNReal.comp g.continuous⟩,
    g.hasCompactSupport.mono (fun x hx => by
      simp only [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by rw [h0]; simp))⟩

theorem ccNNReal_coe (g : C_c(SL3, ℝ)) (x : SL3) :
    ((ccNNReal g x : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (g x) := by
  show (((g x).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (g x)
  rw [← ENNReal.ofReal_coe_nnreal (p := (g x).toNNReal), Real.coe_toNNReal']
  by_cases h : 0 ≤ g x
  · rw [max_eq_left h]
  · rw [max_eq_right (le_of_lt (not_le.mp h)),
      ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp h)), ENNReal.ofReal_zero]

/-- A non-zero measure has a compactly supported continuous test function with non-zero integral. -/
theorem exists_Phi_ne_zero (σ : MeasureTheory.Measure SL3)
    (hσ : MeasureTheory.IsFiniteMeasureOnCompacts σ) (hσ0 : σ ≠ 0) :
    ∃ f : C_c(SL3, ℝ≥0), Phi σ f 1 ≠ 0 := by
  haveI := hσ
  obtain ⟨K, hKc, hKnz⟩ := Measure.InnerRegular.exists_isCompact_not_null.mpr hσ0
  obtain ⟨f, hfK, -, hfs, hf01⟩ :=
    exists_continuous_one_zero_of_isCompact hKc isClosed_empty (by simp)
  refine ⟨⟨⟨fun x => (f x).toNNReal, continuous_real_toNNReal.comp f.continuous⟩,
    hfs.mono (fun x hx => by
      simp only [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by rw [h0]; simp))⟩, ?_⟩
  rw [Phi_one]
  have hle : ∀ x, K.indicator (1 : SL3 → ℝ≥0∞) x ≤ (((f x).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, hfK hx]
      simp
    · rw [Set.indicator_of_notMem hx]; simp
  refine ne_of_gt (lt_of_lt_of_le ?_ (MeasureTheory.lintegral_mono hle))
  rw [MeasureTheory.lintegral_indicator_one hKc.isClosed.measurableSet]
  exact pos_iff_ne_zero.mpr hKnz

/-! ## 3. Measure equality from `C_c`-integrals -/

/-- Two Radon measures with equal `ℝ≥0`-valued `C_c`-integrals are equal. -/
theorem measure_eq_of_forall_lintegral_cc_eq (μ ν : MeasureTheory.Measure SL3)
    (hμ : MeasureTheory.IsFiniteMeasureOnCompacts μ)
    (hν : MeasureTheory.IsFiniteMeasureOnCompacts ν)
    (h : ∀ f : C_c(SL3, ℝ≥0),
      ∫⁻ x, ((f x : ℝ≥0) : ℝ≥0∞) ∂μ = ∫⁻ x, ((f x : ℝ≥0) : ℝ≥0∞) ∂ν) : μ = ν := by
  haveI := hμ
  haveI := hν
  haveI : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  haveI : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  refine Measure.ext_of_integral_eq_on_compactlySupported fun g => ?_
  have hgμ : Integrable (⇑g) μ := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hgν : Integrable (⇑g) ν := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  rw [MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgμ,
    MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgν]
  congr 1
  · have key := h (ccNNReal g)
    rw [MeasureTheory.lintegral_congr (μ := μ) (fun x => ccNNReal_coe g x)] at key
    rw [MeasureTheory.lintegral_congr (μ := ν) (fun x => ccNNReal_coe g x)] at key
    rw [key]
  · have hcoe : ∀ x : SL3, ((ccNNReal (-g) x : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (-(g x)) := by
      intro x
      rw [ccNNReal_coe]
      rfl
    have key := h (ccNNReal (-g))
    rw [MeasureTheory.lintegral_congr (μ := μ) hcoe] at key
    rw [MeasureTheory.lintegral_congr (μ := ν) hcoe] at key
    rw [key]

/-! ## 4. The quasi-invariance set is closed -/

/-- The set of multipliers `u` for which `σ.map (g ↦ u * g)` is a finite non-zero multiple of
`σ` is closed. -/
theorem isClosed_quasiInvLeft (σ : MeasureTheory.Measure SL3)
    (hσ : MeasureTheory.IsFiniteMeasureOnCompacts σ) (hσ0 : σ ≠ 0) :
    IsClosed (QuasiInvLeft σ) := by
  classical
  haveI := hσ
  set K : Set SL3 := {u : SL3 | ∀ f g : C_c(SL3, ℝ≥0),
    Phi σ f u * Phi σ g 1 = Phi σ g u * Phi σ f 1} with hK
  have hKclosed : IsClosed K := by
    rw [hK]
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun f => isClosed_iInter fun g => ?_
    have h1 : Continuous (fun u : SL3 => Phi σ f u * Phi σ g 1) :=
      (ENNReal.continuous_mul_const (a := Phi σ g 1) (Phi_lt_top σ hσ g 1).ne).comp
        (Phi_cont σ hσ f)
    have h2 : Continuous (fun u : SL3 => Phi σ g u * Phi σ f 1) :=
      (ENNReal.continuous_mul_const (a := Phi σ f 1) (Phi_lt_top σ hσ f 1).ne).comp
        (Phi_cont σ hσ g)
    exact isClosed_eq h1 h2
  have hTK : QuasiInvLeft σ = K := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro u ⟨c, hc0, hct, hc⟩ f g
      have key : ∀ f : C_c(SL3, ℝ≥0), Phi σ f u = c * Phi σ f 1 := by
        intro f
        rw [Phi_map σ f u, hc, MeasureTheory.lintegral_smul_measure, Phi_one σ f, smul_eq_mul]
      rw [key f, key g, mul_assoc, mul_assoc, mul_comm (Phi σ f 1) (Phi σ g 1)]
    · intro u hu
      obtain ⟨f₀, hf₀⟩ := exists_Phi_ne_zero σ hσ hσ0
      have hf₀pos : 0 < Phi σ f₀ 1 :=
        lt_of_le_of_ne (by positivity) (Ne.symm hf₀)
      have hf₀lt : Phi σ f₀ 1 < ⊤ := Phi_lt_top σ hσ f₀ 1
      set c : ℝ≥0∞ := Phi σ f₀ u * (Phi σ f₀ 1)⁻¹ with hc
      have key : ∀ f : C_c(SL3, ℝ≥0), Phi σ f u = c * Phi σ f 1 := by
        intro f
        have h1 := hu f f₀
        calc Phi σ f u = Phi σ f u * Phi σ f₀ 1 * (Phi σ f₀ 1)⁻¹ :=
              (ENNReal.mul_inv_cancel_right hf₀ hf₀lt.ne).symm
          _ = Phi σ f₀ u * Phi σ f 1 * (Phi σ f₀ 1)⁻¹ := by rw [h1]
          _ = c * Phi σ f 1 := by
              rw [hc]
              simp only [mul_assoc, mul_comm, mul_left_comm]
      have hc_top : c ≠ ⊤ := by
        rw [hc]
        exact (ENNReal.mul_lt_top (Phi_lt_top σ hσ f₀ u) (ENNReal.inv_lt_top.mpr hf₀pos)).ne
      have hmap_eq : σ.map (fun g : SL3 => u * g) = c • σ := by
        refine measure_eq_of_forall_lintegral_cc_eq (μ := σ.map (fun g : SL3 => u * g))
          (ν := c • σ)
          (MeasureTheory.Measure.IsFiniteMeasureOnCompacts.map σ (Homeomorph.mulLeft u))
          (MeasureTheory.IsFiniteMeasureOnCompacts.smul σ hc_top) (fun f => ?_)
        rw [← Phi_map σ f u, key f, MeasureTheory.lintegral_smul_measure, ← Phi_one σ f,
          smul_eq_mul]
      have hc_pos : c ≠ 0 := by
        intro hczero
        have hσzero : σ = 0 := by
          have h1 : σ.map (fun g : SL3 => u * g) = 0 := by rw [hmap_eq, hczero, zero_smul]
          have h2 : (σ.map (fun g : SL3 => u * g)).map (fun g : SL3 => u⁻¹ * g) = σ := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            have h3 : ((fun g : SL3 => u⁻¹ * g) ∘ (fun g : SL3 => u * g)) = id := by
              funext g; simp
            rw [h3, Measure.map_id]
          rw [h1, Measure.map_zero] at h2
          exact h2.symm
        exact hσ0 hσzero
      exact ⟨c, hc_pos, hc_top, hmap_eq⟩
  rw [hTK]
  exact hKclosed

end

end Work.EKLC7Ae
