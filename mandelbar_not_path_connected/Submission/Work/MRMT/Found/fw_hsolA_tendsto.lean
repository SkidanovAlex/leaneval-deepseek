import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.hsolA_spec

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-! ## Helper lemmas for `fw_hsolA_tendsto`

`hsolA μ` is the `L²` solution of the Ahlfors–Bers equation `h = μ (1 + S h)`.  The
file proves the continuity of `μ ↦ hsolA μ` in `L²` under an a.e. converging, uniformly
bounded and uniformly compactly supported family `μn n → μ'`.

The skeleton is the resolvent identity `hsolA μ = toLp μ + M_μ (S (hsolA μ))` together
with the quantitative stability estimate
`(1-k) ‖hsolA μ - hsolA ν‖ ≤ ‖toLp(μ-ν)‖ + ‖(M_μ - M_ν) (S (hsolA ν))‖`.
-/

/-- `‖g‖²` for `g ∈ L²(ℂ)` is the integral of the squared norm of the representative. -/
lemma Lp_norm_sq_eq_integral (g : Lp ℂ 2 (volume : Measure ℂ)) :
    ‖g‖ ^ 2 = ∫ z, ‖(g : ℂ → ℂ) z‖ ^ 2 := by
  rw [Lp.norm_def]
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (p := 2) (f := (g : ℂ → ℂ)) (by norm_num)
    (by norm_num) (Lp.memLp g)]
  rw [show ((2 : ℝ≥0∞).toReal) = 2 by norm_num, show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num,
    ENNReal.toReal_ofReal (by positivity), ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two]

/-- `mulL2 μ` is bounded by `k` when `‖μ‖ ≤ k` a.e. -/
lemma mulL2_norm_le_mul {μ : ℂ → ℂ} (hm : AEStronglyMeasurable μ (volume : Measure ℂ))
    (h1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1) {k : ℝ}
    (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k) (g : Lp ℂ 2 (volume : Measure ℂ)) :
    ‖mulL2 μ hm h1 g‖ ≤ k * ‖g‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul (c := k) ?_
  filter_upwards [mulL2_apply_ae μ hm h1 g, hb] with z hz hkz
  rw [hz, norm_mul]
  exact mul_le_mul_of_nonneg_right hkz (norm_nonneg _)

/-- The resolvent identity, in the form `hsolA μ = toLp μ + M_μ (S (hsolA μ))`. -/
lemma hsolA_resolvent {μ : ℂ → ℂ} (hμ : Admissible μ) (hLp : MemLp μ 2 (volume : Measure ℂ))
    {k : ℝ} (hk : k < 1) (hb : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hb1 : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1) :
    hsolA μ hμ hLp = hLp.toLp μ +
      ((mulL2 μ hμ.meas hb1).comp beurlingL2) (hsolA μ hμ hLp) := by
  rw [Lp.ext_iff]
  have hspec := (hsolA_spec hμ hLp hk hb).1
  have h2 := Lp.coeFn_add (hLp.toLp μ)
    (((mulL2 μ hμ.meas hb1).comp beurlingL2) (hsolA μ hμ hLp))
  have h3 := mulL2_apply_ae μ hμ.meas hb1 (beurlingL2 (hsolA μ hμ hLp))
  have h4 := MemLp.coeFn_toLp hLp
  filter_upwards [hspec, h2, h3, h4] with z hz1 hz2 hz3 hz4
  simp only [ContinuousLinearMap.comp_apply, Pi.add_apply] at hz2 ⊢
  rw [hz2, hz3, hz4, hz1]
  ring

/-- Quantitative stability of `hsolA` in the coefficient: subtracting the two resolvent
identities gives `(1-k) ‖hsolA μ - hsolA ν‖ ≤ ‖toLp(μ-ν)‖ + ‖(M_μ - M_ν) (S (hsolA ν))‖`. -/
lemma hsolA_diff_norm_le {μ ν : ℂ → ℂ} (hμ : Admissible μ) (hν : Admissible ν)
    (hLpμ : MemLp μ 2 (volume : Measure ℂ)) (hLpν : MemLp ν 2 (volume : Measure ℂ))
    {k : ℝ} (hk : k < 1) (hbμ : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hbν : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ k)
    (hb1μ : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ 1)
    (hb1ν : ∀ᵐ z ∂(volume : Measure ℂ), ‖ν z‖ ≤ 1) :
    (1 - k) * ‖hsolA μ hμ hLpμ - hsolA ν hν hLpν‖ ≤
      ‖hLpμ.toLp μ - hLpν.toLp ν‖ +
      ‖((mulL2 μ hμ.meas hb1μ).comp beurlingL2) (hsolA ν hν hLpν) -
        ((mulL2 ν hν.meas hb1ν).comp beurlingL2) (hsolA ν hν hLpν)‖ := by
  set Pμ : Lp ℂ 2 (volume : Measure ℂ) := hLpμ.toLp μ with hPμdef
  set Pν : Lp ℂ 2 (volume : Measure ℂ) := hLpν.toLp ν with hPνdef
  set Sμ : Lp ℂ 2 (volume : Measure ℂ) := hsolA μ hμ hLpμ with hSμdef
  set Sν : Lp ℂ 2 (volume : Measure ℂ) := hsolA ν hν hLpν with hSνdef
  set Tμ : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    (mulL2 μ hμ.meas hb1μ).comp beurlingL2 with hTμdef
  set Tν : Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    (mulL2 ν hν.meas hb1ν).comp beurlingL2 with hTνdef
  have hresμ : Sμ = Pμ + Tμ Sμ := by
    rw [hSμdef, hPμdef, hTμdef]
    exact hsolA_resolvent hμ hLpμ hk hbμ hb1μ
  have hresν : Sν = Pν + Tν Sν := by
    rw [hSνdef, hPνdef, hTνdef]
    exact hsolA_resolvent hν hLpν hk hbν hb1ν
  have key : Sμ - Sν = (Pμ - Pν) + Tμ (Sμ - Sν) + (Tμ Sν - Tν Sν) := by
    conv_lhs => rw [hresμ, hresν]
    simp only [map_sub]
    abel
  have h1 : ‖Sμ - Sν‖ ≤ ‖Pμ - Pν‖ + ‖Tμ (Sμ - Sν)‖ + ‖Tμ Sν - Tν Sν‖ := by
    conv_lhs => rw [key]
    have ha := norm_add_le (Pμ - Pν) (Tμ (Sμ - Sν))
    have hb := norm_add_le ((Pμ - Pν) + Tμ (Sμ - Sν)) (Tμ Sν - Tν Sν)
    linarith
  have h2 : ‖Tμ (Sμ - Sν)‖ ≤ k * ‖Sμ - Sν‖ := by
    rw [hTμdef, ContinuousLinearMap.comp_apply]
    calc ‖(mulL2 μ hμ.meas hb1μ) (beurlingL2 (Sμ - Sν))‖
        ≤ k * ‖beurlingL2 (Sμ - Sν)‖ := mulL2_norm_le_mul (k := k) hμ.meas hb1μ hbμ _
      _ = k * ‖Sμ - Sν‖ := by rw [norm_beurlingL2]
  have h3 : ‖Sμ - Sν‖ ≤ ‖Pμ - Pν‖ + k * ‖Sμ - Sν‖ + ‖Tμ Sν - Tν Sν‖ := by
    linarith [h1, h2]
  have h4 : (1 - k) * ‖Sμ - Sν‖ ≤ ‖Pμ - Pν‖ + ‖Tμ Sν - Tν Sν‖ := by
    have h5 : (1 - k) * ‖Sμ - Sν‖ = ‖Sμ - Sν‖ - k * ‖Sμ - Sν‖ := by ring
    rw [h5]; linarith [h3]
  exact h4

/-- Dominated convergence: if `μn n → μ'` a.e., with a uniform bound `k` and a common
compact support (through the ball of radius `M`), then `∫ ‖μn n - μ'‖² → 0`. -/
lemma tendsto_integral_normSq_sub_of_tendsto_ae_bound
    {μ' : ℂ → ℂ} {μn : ℕ → ℂ → ℂ} {k M : ℝ}
    (hmeas' : AEStronglyMeasurable μ' (volume : Measure ℂ))
    (hmeasn : ∀ n, AEStronglyMeasurable (μn n) (volume : Measure ℂ))
    (hb' : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ' z‖ ≤ k)
    (hbn : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ), ‖μn n z‖ ≤ k)
    (hMn : ∀ n, ∀ z : ℂ, μn n z ≠ 0 → ‖z‖ ≤ M)
    (hM' : ∀ z : ℂ, M < ‖z‖ → μ' z = 0)
    (hconv : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => μn n z) atTop (𝓝 (μ' z))) :
    Tendsto (fun n => ∫ z, ‖μn n z - μ' z‖ ^ 2) atTop (𝓝 0) := by
  set s : Set ℂ := Metric.closedBall 0 M with hsdef
  have hsmeas : MeasurableSet s := measurableSet_closedBall
  have hfin : (volume : Measure ℂ) s ≠ ∞ :=
    (isCompact_closedBall (0 : ℂ) M).measure_lt_top.ne
  have hind : Integrable (s.indicator (fun _ => (1 : ℝ))) (volume : Measure ℂ) :=
    (integrable_indicator_iff hsmeas).2 (integrableOn_const hfin (by simp))
  have key := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℂ)) (G := ℝ)
    (F := fun n z => ‖μn n z - μ' z‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun z => (2 * k) ^ 2 * s.indicator (fun _ => (1 : ℝ)) z)
    (fun n => ((hmeasn n).sub hmeas').norm.pow 2)
    (hind.const_mul _)
    (fun n => by
      filter_upwards [hbn n, hb'] with z hzk hz'k
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      by_cases hz : z ∈ s
      · have h1 : ‖μn n z - μ' z‖ ≤ 2 * k := by
          calc ‖μn n z - μ' z‖ ≤ ‖μn n z‖ + ‖μ' z‖ := norm_sub_le _ _
            _ ≤ k + k := add_le_add hzk hz'k
            _ = 2 * k := by ring
        have h2 : ‖μn n z - μ' z‖ ^ 2 ≤ (2 * k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        simpa [Set.indicator_of_mem hz] using h2
      · have hz' : M < ‖z‖ := by
          have : ¬ (dist z 0 ≤ M) := by
            intro h
            exact hz (by rw [hsdef, Metric.mem_closedBall]; exact h)
          rw [dist_zero_right] at this
          exact lt_of_not_ge this
        have hμ'0 : μ' z = 0 := hM' z hz'
        have hμn0 : μn n z = 0 := by
          by_contra hne
          exact absurd (hMn n z hne) (not_le.mpr hz')
        simp [Set.indicator_of_notMem hz, hμn0, hμ'0])
    (by
      filter_upwards [hconv] with z hz
      have h1 : Tendsto (fun n => μn n z - μ' z) atTop (𝓝 (μ' z - μ' z)) :=
        hz.sub tendsto_const_nhds
      have h2 : Tendsto (fun n => μn n z - μ' z) atTop (𝓝 0) := by simpa using h1
      have h3 := h2.norm.pow 2
      simpa using h3)
  simpa using key

/-- Dominated convergence: if `μn n → μ'` a.e. with a uniform bound `k`, then
`∫ ‖(μn n - μ') · w‖² → 0` for any fixed `w ∈ L²`. -/
lemma tendsto_integral_normSq_sub_mul_of_tendsto_ae_bound
    {μ' : ℂ → ℂ} {μn : ℕ → ℂ → ℂ} {k : ℝ}
    (hmeas' : AEStronglyMeasurable μ' (volume : Measure ℂ))
    (hmeasn : ∀ n, AEStronglyMeasurable (μn n) (volume : Measure ℂ))
    (hb' : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ' z‖ ≤ k)
    (hbn : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ), ‖μn n z‖ ≤ k)
    (hconv : ∀ᵐ z ∂(volume : Measure ℂ),
      Tendsto (fun n => μn n z) atTop (𝓝 (μ' z)))
    {w : ℂ → ℂ} (hw : MemLp w 2 (volume : Measure ℂ)) :
    Tendsto (fun n => ∫ z, ‖(μn n z - μ' z) * w z‖ ^ 2) atTop (𝓝 0) := by
  have hwi : Integrable (fun z => ‖w z‖ ^ 2) (volume : Measure ℂ) :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).1 hw
  have key := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℂ)) (G := ℝ)
    (F := fun n z => ‖(μn n z - μ' z) * w z‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun z => (2 * k) ^ 2 * ‖w z‖ ^ 2)
    (fun n => (((hmeasn n).sub hmeas').mul hw.aestronglyMeasurable).norm.pow 2)
    (hwi.const_mul _)
    (fun n => by
      filter_upwards [hbn n, hb'] with z hzk hz'k
      rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have h1 : ‖μn n z - μ' z‖ ≤ 2 * k := by
        calc ‖μn n z - μ' z‖ ≤ ‖μn n z‖ + ‖μ' z‖ := norm_sub_le _ _
          _ ≤ k + k := add_le_add hzk hz'k
          _ = 2 * k := by ring
      have h2 : ‖μn n z - μ' z‖ ^ 2 ≤ (2 * k) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
    (by
      filter_upwards [hconv] with z hz
      have h1 : Tendsto (fun n => μn n z - μ' z) atTop (𝓝 (μ' z - μ' z)) :=
        hz.sub tendsto_const_nhds
      have h1' : Tendsto (fun n => μn n z - μ' z) atTop (𝓝 0) := by simpa using h1
      have h2 : Tendsto (fun n => (μn n z - μ' z) * w z) atTop (𝓝 (0 * w z)) :=
        h1'.mul tendsto_const_nhds
      have h3 : Tendsto (fun n => (μn n z - μ' z) * w z) atTop (𝓝 0) := by simpa using h2
      simpa using h3.norm.pow 2)
  simpa using key


theorem fw_hsolA_tendsto {μ μ' : ℂ → ℂ} {μn : ℕ → ℂ → ℂ} {k M : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hAdm' : Work.MRMT.Found.Admissible μ')
    (hLp' : MeasureTheory.MemLp μ' 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hAdmn : ∀ n, Work.MRMT.Found.Admissible (μn n))
    (hLpn : ∀ n, MeasureTheory.MemLp (μn n) 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hbn : ∀ n, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μn n z‖ ≤ k)
    (hb' : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ' z‖ ≤ k)
    (hMn : ∀ n, ∀ z : ℂ, μn n z ≠ 0 → ‖z‖ ≤ M)
    (hM' : ∀ z : ℂ, M < ‖z‖ → μ' z = 0)
    (hconv : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds (μ' z))) :
    Filter.Tendsto (fun n => ∫ z, ‖((Work.MRMT.Found.hsolA (μn n) (hAdmn n) (hLpn n) :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z
      - ((Work.MRMT.Found.hsolA μ' hAdm' hLp' :
        MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) : ℂ → ℂ) z‖ ^ 2)
      Filter.atTop (nhds 0) := by
  have hb1n : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ), ‖μn n z‖ ≤ 1 := fun n => by
    filter_upwards [hbn n] with z hz; linarith
  have hb1' : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ' z‖ ≤ 1 := by
    filter_upwards [hb'] with z hz; linarith
  set S' : ℂ → ℂ := ((beurlingL2 (hsolA μ' hAdm' hLp') : Lp ℂ 2 (volume : Measure ℂ)) : ℂ → ℂ)
    with hS'def
  have hS'mem : MemLp S' 2 (volume : Measure ℂ) := by
    rw [hS'def]; exact Lp.memLp (beurlingL2 (hsolA μ' hAdm' hLp'))
  -- the two dominated-convergence integrals
  have hAint : Tendsto (fun n => ∫ z, ‖μn n z - μ' z‖ ^ 2) atTop (𝓝 0) :=
    tendsto_integral_normSq_sub_of_tendsto_ae_bound hAdm'.meas (fun n => (hAdmn n).meas)
      hb' hbn hMn hM' hconv
  have hBint : Tendsto (fun n => ∫ z, ‖(μn n z - μ' z) * S' z‖ ^ 2) atTop (𝓝 0) :=
    tendsto_integral_normSq_sub_mul_of_tendsto_ae_bound hAdm'.meas (fun n => (hAdmn n).meas)
      hb' hbn hconv hS'mem
  -- the per-`n` stability bound
  have hstep : ∀ n, (1 - k) * ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA μ' hAdm' hLp'‖ ≤
      Real.sqrt (∫ z, ‖μn n z - μ' z‖ ^ 2) + Real.sqrt (∫ z, ‖(μn n z - μ' z) * S' z‖ ^ 2) := by
    intro n
    have hD := hsolA_diff_norm_le (hAdmn n) hAdm' (hLpn n) hLp' hk1 (hbn n) hb' (hb1n n) hb1'
    have hPQ : ‖(hLpn n).toLp (μn n) - hLp'.toLp μ'‖
        = Real.sqrt (∫ z, ‖μn n z - μ' z‖ ^ 2) := by
      have hsq : ‖(hLpn n).toLp (μn n) - hLp'.toLp μ'‖ ^ 2
          = ∫ z, ‖μn n z - μ' z‖ ^ 2 := by
        rw [← MemLp.toLp_sub (hLpn n) hLp', Lp_norm_sq_eq_integral]
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp ((hLpn n).sub hLp')] with z hz
        rw [hz]; simp only [Pi.sub_apply]
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    have hTV : ‖((mulL2 (μn n) (hAdmn n).meas (hb1n n)).comp beurlingL2) (hsolA μ' hAdm' hLp')
          - ((mulL2 μ' hAdm'.meas hb1').comp beurlingL2) (hsolA μ' hAdm' hLp')‖
        = Real.sqrt (∫ z, ‖(μn n z - μ' z) * S' z‖ ^ 2) := by
      have hsq : ‖((mulL2 (μn n) (hAdmn n).meas (hb1n n)).comp beurlingL2) (hsolA μ' hAdm' hLp')
            - ((mulL2 μ' hAdm'.meas hb1').comp beurlingL2) (hsolA μ' hAdm' hLp')‖ ^ 2
          = ∫ z, ‖(μn n z - μ' z) * S' z‖ ^ 2 := by
        rw [Lp_norm_sq_eq_integral]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub
            (((mulL2 (μn n) (hAdmn n).meas (hb1n n)).comp beurlingL2) (hsolA μ' hAdm' hLp'))
            (((mulL2 μ' hAdm'.meas hb1').comp beurlingL2) (hsolA μ' hAdm' hLp')),
          mulL2_apply_ae (μn n) (hAdmn n).meas (hb1n n) (beurlingL2 (hsolA μ' hAdm' hLp')),
          mulL2_apply_ae μ' hAdm'.meas hb1' (beurlingL2 (hsolA μ' hAdm' hLp'))]
          with z hz1 hz2 hz3
        rw [← hS'def] at hz2 hz3
        simp only [ContinuousLinearMap.comp_apply, Pi.sub_apply] at hz1 hz2 hz3 ⊢
        rw [hz1, hz2, hz3]
        have hcomm : (μn n z - μ' z) * S' z = μn n z * S' z - μ' z * S' z := by ring
        rw [hcomm]
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    rw [hPQ, hTV] at hD
    exact hD
  have hsqrtA : Tendsto (fun n => Real.sqrt (∫ z, ‖μn n z - μ' z‖ ^ 2)) atTop (𝓝 0) := by
    simpa using hAint.sqrt
  have hsqrtB : Tendsto (fun n => Real.sqrt (∫ z, ‖(μn n z - μ' z) * S' z‖ ^ 2)) atTop (𝓝 0) := by
    simpa using hBint.sqrt
  have hsum : Tendsto (fun n => Real.sqrt (∫ z, ‖μn n z - μ' z‖ ^ 2)
      + Real.sqrt (∫ z, ‖(μn n z - μ' z) * S' z‖ ^ 2)) atTop (𝓝 0) := by
    have := hsqrtA.add hsqrtB
    simpa using this
  have hnorm : Tendsto (fun n => ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA μ' hAdm' hLp'‖)
      atTop (𝓝 0) := by
    refine squeeze_zero
      (g := fun n => (Real.sqrt (∫ z, ‖μn n z - μ' z‖ ^ 2)
        + Real.sqrt (∫ z, ‖(μn n z - μ' z) * S' z‖ ^ 2)) / (1 - k))
      (fun n => norm_nonneg _) (fun n => ?_) ?_
    · have hkpos : (0 : ℝ) < 1 - k := by linarith
      rw [le_div_iff₀ hkpos]
      have hh := hstep n
      rw [mul_comm] at hh
      exact hh
    · have := hsum.div_const (1 - k)
      simpa using this
  have hnorm2 : Tendsto (fun n => ‖hsolA (μn n) (hAdmn n) (hLpn n) - hsolA μ' hAdm' hLp'‖ ^ 2)
      atTop (𝓝 0) := by
    simpa using hnorm.pow 2
  refine hnorm2.congr' (Eventually.of_forall (fun n => ?_))
  rw [Lp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hsolA (μn n) (hAdmn n) (hLpn n)) (hsolA μ' hAdm' hLp')]
    with z hz
  rw [hz]
  simp only [Pi.sub_apply]

end Work.MRMT.Found
