import Mathlib
import Submission.Work.Mostow.BdExt.bdMap
import Submission.Work.Mostow.BdExt.rayLawCosines

/-!
# Continuity of the boundary extension of a quasi-isometry

The boundary map `bdMap n Φ : Sph n → Sph n` of a quasi-isometry `Φ` is continuous on the
boundary sphere, *given* the quantitative comparison estimate `hcmp` for pairs of points
`ξ, ξ' ∈ Sph n` whose geodesic rays stay within distance `1` up to hyperbolic level `T`:

`dist (bdMap Φ ξ') (bdMap Φ ξ) ≤ C₆ * (exp (-(T/(2K))) + 1/sinh ((T-C)/K - lvl (Φ 0)))`.

The content of this file is the purely topological/real-analytic step: for fixed `ξ` the map
`ξ' ↦ hdist (ray ξ' T) (ray ξ T)` is continuous and vanishes at `ξ' = ξ`, so on a whole
neighbourhood of `ξ` the hypothesis of `hcmp` is available at the level `T`; and the right-hand
side of `hcmp` can be made smaller than any prescribed `ε > 0` by taking `T` large.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow Filter

noncomputable section

/-- `Real.sinh` tends to `+∞` at `+∞`. -/
lemma tendsto_sinh_atTop : Filter.Tendsto Real.sinh Filter.atTop Filter.atTop := by
  refine Monotone.tendsto_atTop_atTop Real.sinh_strictMono.monotone fun b => ⟨max b 0, ?_⟩
  exact le_trans (le_max_left b 0) (Real.self_le_sinh_iff.mpr (le_max_right b 0))

/-- For `K > 0` and any `ε > 0` the expression
`C₆ * (exp (-(T/(2K))) + 1/sinh ((T-C)/K - L))` is eventually below `ε` as `T → +∞`, and this
happens for some `T ≥ T₀`. -/
lemma existsBoundExpSinh (K C L T₀ ε C₆ : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∃ T : ℝ, T₀ ≤ T ∧
      C₆ * (Real.exp (-(T / (2 * K))) + 1 / Real.sinh ((T - C) / K - L)) < ε := by
  have hK2 : (0 : ℝ) < 2 * K := by linarith
  have hlin : Filter.Tendsto (fun T : ℝ => T / (2 * K)) Filter.atTop Filter.atTop := by
    simpa [div_eq_mul_inv] using Filter.Tendsto.atTop_mul_const (inv_pos.mpr hK2) tendsto_id
  have hexp : Filter.Tendsto (fun T : ℝ => Real.exp (-(T / (2 * K)))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
  have harg : Filter.Tendsto (fun T : ℝ => (T - C) / K - L) Filter.atTop Filter.atTop := by
    apply Monotone.tendsto_atTop_atTop
    · intro x y hxy
      have h2 : (x - C) / K ≤ (y - C) / K :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt hK)
      linarith
    · intro b
      refine ⟨C + K * (L + b), ?_⟩
      have h : (C + K * (L + b) - C) / K - L = b := by
        field_simp
        ring
      linarith [h]
  have hsinh : Filter.Tendsto (fun T : ℝ => Real.sinh ((T - C) / K - L)) Filter.atTop
      Filter.atTop :=
    tendsto_sinh_atTop.comp harg
  have hinv : Filter.Tendsto (fun T : ℝ => 1 / Real.sinh ((T - C) / K - L)) Filter.atTop
      (nhds 0) := by
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hsinh
  have hsum : Filter.Tendsto
      (fun T : ℝ => Real.exp (-(T / (2 * K))) + 1 / Real.sinh ((T - C) / K - L))
      Filter.atTop (nhds 0) := by
    simpa using hexp.add hinv
  have hbound : Filter.Tendsto
      (fun T : ℝ => C₆ * (Real.exp (-(T / (2 * K))) + 1 / Real.sinh ((T - C) / K - L)))
      Filter.atTop (nhds 0) := by
    simpa using hsum.const_mul C₆
  obtain ⟨T, hlt, hge⟩ :=
    ((hbound.eventually (Iio_mem_nhds hε)).and (eventually_ge_atTop T₀)).exists
  exact ⟨T, hge, hlt⟩

/-- **Continuity of the boundary extension.**  If the boundary map of `Φ` satisfies the
uniform comparison estimate `hcmp`, then it is continuous on the boundary sphere. -/
theorem bdMapCont (n : ℕ) (hI : Submission.Mostow.HypIsometryProp n)
    (Φ : Submission.Mostow.E n → Submission.Mostow.E n) (K C T₀ C₆ : ℝ)
    (hK : 0 < K) (hT₀ : 0 ≤ T₀) (hC₆ : 0 ≤ C₆)
    (hcmp : ∀ (ξ ξ' : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
        (hξ' : ξ' ∈ Submission.Mostow.Sph n)
        (T : ℝ), T₀ ≤ T → Submission.Mostow.hdist (Work.Mostow.BdExt.ray ξ' T) (Work.Mostow.BdExt.ray ξ T) ≤ 1 →
        dist (Work.Mostow.BdExt.bdMap n Φ ξ') (Work.Mostow.BdExt.bdMap n Φ ξ) ≤
          C₆ * (Real.exp (-(T / (2 * K))) +
            1 / Real.sinh ((T - C) / K - Work.Mostow.BdExt.lvl (Φ 0)))) :
    ContinuousOn (fun ξ : Submission.Mostow.E n => Work.Mostow.BdExt.bdMap n Φ ξ)
      (Submission.Mostow.Sph n) := by
  rw [Metric.continuousOn_iff]
  intro ξ hξ ε hε
  obtain ⟨T, hTT₀, hTε⟩ := existsBoundExpSinh K C (lvl (Φ 0)) T₀ ε C₆ hK hε
  -- continuity of `ξ' ↦ hdist (ray ξ' T) (ray ξ T)`, which vanishes at `ξ' = ξ`
  have hc : Continuous (fun p : E n × E n => hdist p.1 p.2) := hI.2.2.2.2.1
  have hray : Continuous (fun ξ' : E n => ray ξ' T) := by
    have h : (fun ξ' : E n => ray ξ' T) = fun ξ' : E n => (Real.sinh T) • ξ' := rfl
    rw [h]
    exact (continuous_const : Continuous fun _ : E n => Real.sinh T).smul continuous_id
  have hpair : Continuous (fun ξ' : E n => (ray ξ' T, ray ξ T)) :=
    hray.prodMk continuous_const
  have hcomp := hc.comp hpair
  have hgcont : Continuous (fun ξ' : E n => hdist (ray ξ' T) (ray ξ T)) := hcomp
  have hg0 : hdist (ray ξ T) (ray ξ T) = 0 := (hI.2.2.1 (ray ξ T) (ray ξ T)).mpr rfl
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuous_iff.mp hgcont ξ 1 one_pos)
  refine ⟨δ, hδpos, fun ξ' hξ' hξ'δ => ?_⟩
  -- on the `δ`-neighbourhood of `ξ` the rays to `ξ'` and `ξ` are within distance `1` at level `T`
  have h1 : dist (hdist (ray ξ' T) (ray ξ T)) (hdist (ray ξ T) (ray ξ T)) < 1 := hδ ξ' hξ'δ
  rw [hg0, Real.dist_eq, sub_zero] at h1
  have hray1 : hdist (ray ξ' T) (ray ξ T) ≤ 1 := by
    have hlt : hdist (ray ξ' T) (ray ξ T) < 1 := (abs_lt.mp h1).2
    linarith
  exact lt_of_le_of_lt (hcmp ξ ξ' hξ hξ' T hTT₀ hray1) hTε

end

end Work.Mostow.BdExt
