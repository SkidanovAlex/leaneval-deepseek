import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found.PLWD2

open MeasureTheory Filter Topology
open scoped ENNReal

/-- If `u n → D` in `L²(ν)` then `D ∈ L²(ν)` (a limit in `eLpNorm` of an `L²` sequence is `L²`). -/
theorem memLp_of_tendsto_eLpNorm_two_sub {ν : MeasureTheory.Measure ℂ} {u : ℕ → ℂ → ℂ}
    {D : ℂ → ℂ}
    (hu : ∀ n, MeasureTheory.MemLp (u n) 2 ν)
    (hcon : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun z => u n z - D z) 2 ν)
      Filter.atTop (nhds 0)) :
    MeasureTheory.MemLp D 2 ν := by
  obtain ⟨N, hN⟩ : ∃ N, MeasureTheory.eLpNorm (fun z => u N z - D z) 2 ν < ∞ :=
    ((tendsto_order.1 hcon).2 _ ENNReal.zero_lt_top).exists
  rw [show D = (u N) - (u N - D) by ext z; simp only [Pi.sub_apply]; ring]
  exact MeasureTheory.MemLp.sub (hu N) hN

/-- Dominated convergence in `L²`: if `f n → 0` a.e. and `‖f n‖ ≤ ‖h‖` a.e. with `h ∈ L²`, then
`eLpNorm (f n) 2 ν → 0`. -/
theorem eLpNorm_two_tendsto_of_dominated {ν : MeasureTheory.Measure ℂ} {f : ℕ → ℂ → ℂ}
    {h : ℂ → ℂ}
    (hf : ∀ n, MeasureTheory.AEStronglyMeasurable (f n) ν)
    (hh : MeasureTheory.MemLp h 2 ν)
    (hbound : ∀ n, ∀ᵐ z ∂ν, ‖f n z‖ ≤ ‖h z‖)
    (hlim : ∀ᵐ z ∂ν, Filter.Tendsto (fun n => f n z) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f n) 2 ν) Filter.atTop (nhds 0) := by
  have hFmeas : ∀ n, AEMeasurable (fun z => ‖f n z‖ₑ ^ (2:ℝ)) ν := fun n =>
    (ENNReal.continuous_rpow_const (y := 2)).measurable.comp_aemeasurable ((hf n).enorm)
  have hboundint : ∫⁻ z, ‖h z‖ₑ ^ (2:ℝ) ∂ν ≠ ∞ := by
    have hlt : ∫⁻ z, ‖h z‖ₑ ^ (2:ℝ) ∂ν < ∞ := by
      have h := MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (μ := ν) (f := h)
        (p := 2) (by norm_num) (by norm_num) hh
      simpa [ENNReal.toReal_ofNat] using h
    exact hlt.ne
  have hboundae : ∀ n, (fun z => ‖f n z‖ₑ ^ (2:ℝ)) ≤ᵐ[ν] (fun z => ‖h z‖ₑ ^ (2:ℝ)) := by
    intro n
    filter_upwards [hbound n] with z hz
    exact ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.mpr hz) (by norm_num)
  have hlimae : ∀ᵐ z ∂ν, Filter.Tendsto (fun n => ‖f n z‖ₑ ^ (2:ℝ)) Filter.atTop (nhds 0) := by
    filter_upwards [hlim] with z hz
    have h1 : Filter.Tendsto (fun n => ‖f n z‖ₑ) Filter.atTop (nhds (0:ℝ≥0∞)) := by
      simpa using hz.enorm
    have h2 := h1.ennrpow_const (2:ℝ)
    simpa using h2
  have hI : Filter.Tendsto (fun n => ∫⁻ z, ‖f n z‖ₑ ^ (2:ℝ) ∂ν) Filter.atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_lintegral_of_dominated_convergence' (μ := ν)
      (F := fun n z => ‖f n z‖ₑ ^ (2:ℝ)) (f := fun _ => (0:ℝ≥0∞)) (fun z => ‖h z‖ₑ ^ (2:ℝ))
      hFmeas hboundae hboundint hlimae
    simpa using h
  have hfin : ∀ n, MeasureTheory.eLpNorm (f n) 2 ν = (∫⁻ z, ‖f n z‖ₑ ^ (2:ℝ) ∂ν) ^ (1/2:ℝ) := by
    intro n
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (f := f n) (μ := ν)
      (by norm_num) (by norm_num) (hf n)]
    simp [ENNReal.toReal_ofNat]
  have hfinal : Filter.Tendsto (fun n => (∫⁻ z, ‖f n z‖ₑ ^ (2:ℝ) ∂ν) ^ (1/2:ℝ))
      Filter.atTop (nhds 0) := by
    have h := hI.ennrpow_const (1/2:ℝ)
    simpa using h
  simpa [hfin] using hfinal

theorem eLpNorm_mul_sub_tendsto {μ : ℂ → ℂ} {μn : ℕ → ℂ → ℂ} {u : ℕ → ℂ → ℂ} {D : ℂ → ℂ}
    {K : Set ℂ} {k : ℝ} (hk : 0 ≤ k)
    (hu : ∀ n, MeasureTheory.MemLp (u n) 2 ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict K))
    (hcon : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun z => u n z - D z) 2
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict K)) Filter.atTop (nhds 0))
    (hμnmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (μn n) (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hμnbdd : ∀ n z, ‖μn n z‖ ≤ k)
    (hμmeas : MeasureTheory.AEStronglyMeasurable μ (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hμbdd : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    (hμtend : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds (μ z))) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun z => μn n z * u n z - μ z * D z) 2
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict K)) Filter.atTop (nhds 0) := by
  let ν : MeasureTheory.Measure ℂ := (MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict K
  have hD : MeasureTheory.MemLp D 2 ν := memLp_of_tendsto_eLpNorm_two_sub hu hcon
  have hμn_meas_ν : ∀ n, MeasureTheory.AEStronglyMeasurable (μn n) ν := fun n => (hμnmeas n).restrict
  have hμ_meas_ν : MeasureTheory.AEStronglyMeasurable μ ν := hμmeas.restrict
  have hμbdd_ν : ∀ᵐ z ∂ν, ‖μ z‖ ≤ k := (ae_mono Measure.restrict_le_self) hμbdd
  have hμtend_ν : ∀ᵐ z ∂ν, Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds (μ z)) :=
    (ae_mono Measure.restrict_le_self) hμtend
  let An : ℕ → ℂ → ℂ := fun n z => μn n z * (u n z - D z)
  let Bn : ℕ → ℂ → ℂ := fun n z => (μn n z - μ z) * D z
  have hA : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (An n) 2 ν) Filter.atTop (nhds 0) := by
    have hAle : ∀ n, MeasureTheory.eLpNorm (An n) 2 ν ≤
        ENNReal.ofReal k * MeasureTheory.eLpNorm (fun z => u n z - D z) 2 ν := by
      intro n
      have haes : MeasureTheory.AEStronglyMeasurable (An n) ν :=
        (hμn_meas_ν n).mul (((hu n).aestronglyMeasurable).sub hD.aestronglyMeasurable)
      have hbnd : ∀ᵐ z ∂ν, ‖An n z‖ ≤ k * ‖u n z - D z‖ :=
        Filter.Eventually.of_forall fun z => by
          show ‖μn n z * (u n z - D z)‖ ≤ k * ‖u n z - D z‖
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hμnbdd n z) (norm_nonneg _)
      exact MeasureTheory.eLpNorm_le_mul_eLpNorm_of_ae_le_mul haes hbnd 2
    have hlim : Filter.Tendsto
        (fun n => ENNReal.ofReal k * MeasureTheory.eLpNorm (fun z => u n z - D z) 2 ν)
        Filter.atTop (nhds 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal k) hcon
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h
    have hzero : ∀ n, (0:ℝ≥0∞) ≤ MeasureTheory.eLpNorm (An n) 2 ν := fun n => zero_le
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
      (h := fun n => ENNReal.ofReal k * MeasureTheory.eLpNorm (fun z => u n z - D z) 2 ν)
      tendsto_const_nhds hlim hzero hAle
  have hB : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Bn n) 2 ν) Filter.atTop (nhds 0) := by
    have hf' : ∀ n, MeasureTheory.AEStronglyMeasurable (Bn n) ν := fun n =>
      ((hμn_meas_ν n).sub hμ_meas_ν).mul hD.aestronglyMeasurable
    have hh' : MeasureTheory.MemLp (fun z => ((2*k:ℝ):ℂ) * D z) 2 ν :=
      hD.const_mul ((2*k:ℝ):ℂ)
    have hbnd' : ∀ n, ∀ᵐ z ∂ν, ‖Bn n z‖ ≤ ‖((2*k:ℝ):ℂ) * D z‖ := by
      intro n
      filter_upwards [hμbdd_ν] with z hz
      show ‖(μn n z - μ z) * D z‖ ≤ ‖((2*k:ℝ):ℂ) * D z‖
      rw [norm_mul, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc ‖μn n z - μ z‖ ≤ ‖μn n z‖ + ‖μ z‖ := norm_sub_le _ _
        _ ≤ k + k := add_le_add (hμnbdd n z) hz
        _ = 2*k := by ring
        _ = |2*k| := (abs_of_nonneg (by linarith)).symm
        _ = ‖((2*k:ℝ):ℂ)‖ := (RCLike.norm_ofReal (K := ℂ) (2*k)).symm
    have hlim' : ∀ᵐ z ∂ν, Filter.Tendsto (fun n => Bn n z) Filter.atTop (nhds 0) := by
      filter_upwards [hμtend_ν] with z hz
      change Filter.Tendsto (fun n => (μn n z - μ z) * D z) Filter.atTop (nhds 0)
      have h1 : Filter.Tendsto (fun n => μn n z - μ z) Filter.atTop (nhds (μ z - μ z)) :=
        hz.sub tendsto_const_nhds
      have h2 : Filter.Tendsto (fun n => (μn n z - μ z) * D z) Filter.atTop
          (nhds ((μ z - μ z) * D z)) := h1.mul tendsto_const_nhds
      simpa using h2
    exact eLpNorm_two_tendsto_of_dominated hf' hh' hbnd' hlim'
  have hdecomp : ∀ n, (fun z => μn n z * u n z - μ z * D z) = An n + Bn n := by
    intro n
    funext z
    show μn n z * u n z - μ z * D z
      = μn n z * (u n z - D z) + (μn n z - μ z) * D z
    ring
  have hgoal : ∀ n, MeasureTheory.eLpNorm (fun z => μn n z * u n z - μ z * D z) 2 ν ≤
      MeasureTheory.eLpNorm (An n) 2 ν + MeasureTheory.eLpNorm (Bn n) 2 ν := by
    intro n
    rw [hdecomp n]
    exact MeasureTheory.eLpNorm_add_le (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hupper : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (An n) 2 ν + MeasureTheory.eLpNorm (Bn n) 2 ν)
      Filter.atTop (nhds 0) := by
    have h := hA.add hB
    simpa using h
  have hzero : ∀ n, (0:ℝ≥0∞) ≤
      MeasureTheory.eLpNorm (fun z => μn n z * u n z - μ z * D z) 2 ν := fun n => zero_le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0:ℝ≥0∞))
    (h := fun n => MeasureTheory.eLpNorm (An n) 2 ν + MeasureTheory.eLpNorm (Bn n) 2 ν)
    tendsto_const_nhds hupper hzero hgoal

end Work.MRMT.Found.PLWD2
