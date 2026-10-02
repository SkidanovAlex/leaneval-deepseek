import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.QC

open MeasureTheory
open scoped ENNReal

/-! ## Auxiliary lemmas

The Wirtinger derivatives are built from the real Fréchet derivative, which is a
measurable function of the base point, so `dz g` and `dzbar g` are measurable.
On an *open* set `U`, the Lipschitz bound `LipschitzOnWith K g U` controls
`‖fderiv ℝ g x‖` at every point `x ∈ U` (the junk value `0` where `g` is not
differentiable is harmless), whence `‖dz g x‖ ≤ K` and `‖dzbar g x‖ ≤ K` on `U`.
A measurable function bounded on `U` is then locally integrable on `U` and
locally square integrable on `U`. -/

lemma measurable_dz (g : ℂ → ℂ) : Measurable (Work.MRMT.dz g) := by
  unfold Work.MRMT.dz
  fun_prop

lemma measurable_dzbar (g : ℂ → ℂ) : Measurable (Work.MRMT.dzbar g) := by
  unfold Work.MRMT.dzbar
  fun_prop

lemma norm_dz_le_of_norm_fderiv_le {g : ℂ → ℂ} {z : ℂ} {C : ℝ}
    (h : ‖fderiv ℝ g z‖ ≤ C) : ‖Work.MRMT.dz g z‖ ≤ C := by
  have h1 : ‖fderiv ℝ g z 1‖ ≤ C := by
    calc ‖fderiv ℝ g z 1‖ ≤ ‖fderiv ℝ g z‖ * ‖(1:ℂ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ g z‖ := by simp
      _ ≤ C := h
  have h2 : ‖Complex.I * fderiv ℝ g z Complex.I‖ ≤ C := by
    rw [norm_mul]
    simp only [Complex.norm_I, one_mul]
    calc ‖fderiv ℝ g z Complex.I‖ ≤ ‖fderiv ℝ g z‖ * ‖Complex.I‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ g z‖ := by simp
      _ ≤ C := h
  rw [Work.MRMT.dz, norm_div]
  have h3 : ‖fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I‖ ≤ 2 * C := by
    calc _ ≤ ‖fderiv ℝ g z 1‖ + ‖Complex.I * fderiv ℝ g z Complex.I‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add h1 h2
      _ = 2 * C := by ring
  have : ‖(2:ℂ)‖ = (2:ℝ) := by norm_num
  rw [this]
  linarith

lemma norm_dzbar_le_of_norm_fderiv_le {g : ℂ → ℂ} {z : ℂ} {C : ℝ}
    (h : ‖fderiv ℝ g z‖ ≤ C) : ‖Work.MRMT.dzbar g z‖ ≤ C := by
  have h1 : ‖fderiv ℝ g z 1‖ ≤ C := by
    calc ‖fderiv ℝ g z 1‖ ≤ ‖fderiv ℝ g z‖ * ‖(1:ℂ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ g z‖ := by simp
      _ ≤ C := h
  have h2 : ‖Complex.I * fderiv ℝ g z Complex.I‖ ≤ C := by
    rw [norm_mul]
    simp only [Complex.norm_I, one_mul]
    calc ‖fderiv ℝ g z Complex.I‖ ≤ ‖fderiv ℝ g z‖ * ‖Complex.I‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ g z‖ := by simp
      _ ≤ C := h
  rw [Work.MRMT.dzbar, norm_div]
  have h3 : ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ 2 * C := by
    calc _ ≤ ‖fderiv ℝ g z 1‖ + ‖Complex.I * fderiv ℝ g z Complex.I‖ := norm_add_le _ _
      _ ≤ C + C := add_le_add h1 h2
      _ = 2 * C := by ring
  have : ‖(2:ℂ)‖ = (2:ℝ) := by norm_num
  rw [this]
  linarith

/-- A measurable complex-valued function that is bounded on an open set `U` is
locally integrable on `U`. -/
lemma locallyIntegrableOn_of_measurable_of_bound {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : Measurable f) {C : ℝ} (hb : ∀ z ∈ U, ‖f z‖ ≤ C) :
    LocallyIntegrableOn f U (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  intro x hx
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  refine ⟨Metric.closedBall x (ε/2), ?_, ?_⟩
  · exact (Filter.le_def.mp nhdsWithin_le_nhds) (Metric.closedBall x (ε/2))
      (Metric.closedBall_mem_nhds x (by linarith))
  · apply IntegrableOn.of_bound
      (measure_closedBall_lt_top (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
        (x := x) (r := ε/2)) hf.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
      (Metric.isClosed_closedBall.measurableSet)] with z hz
    exact hb z (hεU (Metric.closedBall_subset_ball (by linarith) hz))

/-- A measurable complex-valued function that is bounded on a measurable set `U`
is locally square integrable on `U`. -/
lemma memL2LocOn_of_measurable_of_bound {f : ℂ → ℂ} {U : Set ℂ}
    (hUm : MeasurableSet U) (hf : Measurable f) {C : ℝ} (hb : ∀ z ∈ U, ‖f z‖ ≤ C) :
    Work.MRMT.MemL2LocOn f U := by
  intro Kc hKc
  have hfin : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (Kc ∩ U) < ∞ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hKc.measure_lt_top
  apply IntegrableOn.of_bound hfin (hf.norm.pow_const 2).aestronglyMeasurable (C^2)
  filter_upwards [ae_restrict_mem (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hKc.measurableSet.inter hUm)] with z hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb z hz.2) 2

theorem locallyIntegrableOn_dz_of_lipschitzOnWith {g : ℂ → ℂ} {U : Set ℂ} {K : NNReal}
    (hU : IsOpen U) (hg : LipschitzOnWith K g U) :
    (LocallyIntegrableOn (Work.MRMT.dz g) U (MeasureTheory.volume : MeasureTheory.Measure ℂ) ∧
      Work.MRMT.MemL2LocOn (Work.MRMT.dz g) U) ∧
    (LocallyIntegrableOn (Work.MRMT.dzbar g) U (MeasureTheory.volume : MeasureTheory.Measure ℂ) ∧
      Work.MRMT.MemL2LocOn (Work.MRMT.dzbar g) U) := by
  have hbd_dz : ∀ z ∈ U, ‖Work.MRMT.dz g z‖ ≤ (K : ℝ) := fun z hz =>
    norm_dz_le_of_norm_fderiv_le (norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds hz) hg)
  have hbd_dzbar : ∀ z ∈ U, ‖Work.MRMT.dzbar g z‖ ≤ (K : ℝ) := fun z hz =>
    norm_dzbar_le_of_norm_fderiv_le (norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds hz) hg)
  exact ⟨⟨locallyIntegrableOn_of_measurable_of_bound hU (measurable_dz g) hbd_dz,
      memL2LocOn_of_measurable_of_bound hU.measurableSet (measurable_dz g) hbd_dz⟩,
    ⟨locallyIntegrableOn_of_measurable_of_bound hU (measurable_dzbar g) hbd_dzbar,
      memL2LocOn_of_measurable_of_bound hU.measurableSet (measurable_dzbar g) hbd_dzbar⟩⟩

end Work.MRMT.QC
