import Mathlib
import Submission.Work.LandLeaves.Snail.exists_continuous_log_of_path

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The drift of a snail path

A continuous logarithm `L` of a forward path `q` of a germ `f` at a fixed point
(`f 0 = 0`, `f (q t) = q (t + 1)`, `q t → 0`) drifts by the multiplier: the increments
`L (t+1) - L t` converge to a logarithm of `deriv f 0`.

The proof is the standard "sheet" argument.  Since `q (t+1) / q t → deriv f 0 ≠ 0`, the
ratio eventually stays in a fixed disc `U` not containing `0`; on `U` we choose an
explicit continuous branch `ℓ` of the logarithm (`ℓ w = log (deriv f 0) + log (w / λ)`),
and `D t = L (t+1) - L t` satisfies `exp (D t) = q (t+1)/q t = exp (ℓ (q (t+1)/q t))`.
The two continuous lifts `D` and `ℓ ∘ (q (·+1)/q ·)` of the same path therefore differ by a
continuous function into the discrete set `2πiℤ = exp ⁻¹' {1}`, which is constant on the
preconnected interval `[T, ∞)`; the conclusion follows.
-/

open Filter
open scoped Topology

namespace Work.LandLeaves.Snail

/-- Two points of `exp ⁻¹' {1}` of distance `< π` are equal: distinct elements of `2πiℤ`
are at distance a positive multiple of `2π`. -/
private lemma exp_eq_one_of_norm_sub_lt_pi {y z : ℂ} (hy : Complex.exp y = 1)
    (hz : Complex.exp z = 1) (h : ‖z - y‖ < Real.pi) : z = y := by
  have hsub : Complex.exp (z - y) = 1 := by rw [Complex.exp_sub, hz, hy, div_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hsub
  rw [hn] at h
  by_cases hn0 : n = 0
  · rw [hn0, Int.cast_zero, zero_mul] at hn; exact sub_eq_zero.mp hn
  · exfalso
    have h1 : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
      rw [Complex.norm_intCast, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
    have h2 : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one]; norm_num
    have hle : (2 * Real.pi) ≤ ‖(n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ := by
      rw [norm_mul, h2]
      calc 2 * Real.pi = 1 * (2 * Real.pi) := by ring
        _ ≤ ‖(n : ℂ)‖ * (2 * Real.pi) := by gcongr
    linarith [Real.pi_pos]

/-- The set `2πiℤ = exp ⁻¹' {1}` is a discrete subset of `ℂ`. -/
private lemma isDiscrete_exp_preimage_one : IsDiscrete (Complex.exp ⁻¹' {1}) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  refine ⟨Metric.ball y Real.pi, Metric.isOpen_ball, ?_⟩
  ext z
  rw [Set.mem_inter_iff, Metric.mem_ball, dist_eq_norm, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hz1⟩
    exact exp_eq_one_of_norm_sub_lt_pi hy hz1 hz
  · rintro rfl
    exact ⟨by simp [Real.pi_pos], hy⟩

theorem exists_drift_of_snail {f : ℂ → ℂ} {q : ℝ → ℂ} {L : ℝ → ℂ}
    (hLc : ContinuousOn L (Set.Ici 0)) (hL : ∀ t ∈ Set.Ici (0 : ℝ), Complex.exp (L t) = q t)
    (hf : AnalyticAt ℂ f 0) (hfix : f 0 = 0) (hder : deriv f 0 ≠ 0)
    (hqne : ∀ t ∈ Set.Ici (0 : ℝ), q t ≠ 0)
    (hshift : ∀ t ∈ Set.Ici (0 : ℝ), f (q t) = q (t + 1))
    (hlim : Filter.Tendsto q Filter.atTop (nhds 0)) :
    ∃ c : ℂ, Complex.exp c = deriv f 0 ∧
      Filter.Tendsto (fun t : ℝ => L (t + 1) - L t) Filter.atTop (nhds c) := by
  classical
  -- `f z / z → deriv f 0` as `z → 0` within `{0}ᶜ`.
  have hslope : Tendsto (fun z : ℂ => f z / z) (𝓝[≠] (0 : ℂ)) (𝓝 (deriv f 0)) := by
    have hd : HasDerivAt f (deriv f 0) 0 := hf.differentiableAt.hasDerivAt
    have hfun : (fun z : ℂ => f z / z) = slope f 0 := by
      funext z; simp [slope, hfix, div_eq_mul_inv, mul_comm]
    rw [hfun]; exact hd.tendsto_slope
  -- The ratio `r t = q (t+1) / q t` converges to the multiplier.
  set r : ℝ → ℂ := fun t => q (t + 1) / q t with hr_def
  have hr : Tendsto r atTop (𝓝 (deriv f 0)) := by
    have hq_ne : Tendsto q atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hlim, by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        exact hqne t (by simpa using ht)⟩
    refine (hslope.comp hq_ne).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simp only [Function.comp_apply, hr_def]
    rw [hshift t (by simpa using ht)]
  set lam : ℂ := deriv f 0 with hlam
  have hlamne : lam ≠ 0 := by rw [hlam]; exact hder
  have hrlam : Tendsto r atTop (𝓝 lam) := by rw [hlam]; exact hr
  set c₀ : ℂ := Complex.log lam with hc₀
  have hexpc₀ : Complex.exp c₀ = lam := by rw [hc₀, Complex.exp_log hlamne]
  -- Choose `T ≥ 0` beyond which `r` stays in the disc `ball lam (‖lam‖/2) ∌ 0`.
  have hU_nhds : Metric.ball lam (‖lam‖ / 2) ∈ 𝓝 lam :=
    Metric.ball_mem_nhds lam (half_pos (norm_pos_iff.mpr hlamne))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hrlam.eventually hU_nhds)
  set T : ℝ := max T₀ 0 with hT
  have hT0 : 0 ≤ T := le_max_right _ _
  have hTle : T₀ ≤ T := le_max_left _ _
  have hUT : ∀ t, T ≤ t → r t ∈ Metric.ball lam (‖lam‖ / 2) :=
    fun t ht => hT₀ t (le_trans hTle ht)
  have hTS : Set.Ici T ⊆ Set.Ici (0 : ℝ) := Set.Ici_subset_Ici.mpr hT0
  -- A continuous branch of the logarithm near `lam`.
  set ℓ : ℂ → ℂ := fun w => c₀ + Complex.log (w / lam) with hℓ
  have hℓ_exp : ∀ w, w ≠ 0 → Complex.exp (ℓ w) = w := by
    intro w hw
    simp only [hℓ]
    rw [Complex.exp_add, hexpc₀, Complex.exp_log (div_ne_zero hw hlamne)]
    field_simp
  have hℓcont : ContinuousAt ℓ lam := by
    have h1 : ContinuousAt (fun w : ℂ => w / lam) lam := continuousAt_id.div_const lam
    have h2 : ContinuousAt (fun w : ℂ => Complex.log (w / lam)) lam :=
      h1.clog (by rw [div_self hlamne]; exact Complex.one_mem_slitPlane)
    have h3 : ContinuousAt (fun w : ℂ => c₀ + Complex.log (w / lam)) lam :=
      continuousAt_const.add h2
    simpa only [hℓ] using h3
  -- On `[T, ∞)` the ratio `r` lands in the slit plane after scaling by `lam`.
  have hslit : ∀ t, T ≤ t → r t / lam ∈ Complex.slitPlane := by
    intro t ht
    have hmem := hUT t ht
    rw [Metric.mem_ball, dist_eq_norm] at hmem
    have hdiv : ‖r t / lam - 1‖ < 1 / 2 := by
      have h : r t / lam - 1 = (r t - lam) / lam := by
        rw [← div_self hlamne]; ring
      rw [h, norm_div, div_lt_iff₀ (norm_pos_iff.mpr hlamne)]
      linarith
    have hz : -(1 / 2 : ℝ) < (r t / lam - 1).re := by
      have hab := (abs_le.mp (Complex.abs_re_le_norm (r t / lam - 1))).1
      linarith
    have hre : (r t / lam).re = 1 + (r t / lam - 1).re := by simp
    change 0 < (r t / lam).re ∨ (r t / lam).im ≠ 0
    left
    linarith
  -- The drift `D t = L (t+1) - L t` and its continuity on `[0, ∞)`, hence on `[T, ∞)`.
  set D : ℝ → ℂ := fun t => L (t + 1) - L t with hD
  have hshiftC : Continuous (fun t : ℝ => t + 1) := continuous_id.add continuous_const
  have hD1 : ContinuousOn (fun t : ℝ => L (t + 1)) (Set.Ici 0) :=
    hLc.comp hshiftC.continuousOn (by intro t ht; simp only [Set.mem_Ici] at ht ⊢; linarith)
  have hD0 : ContinuousOn D (Set.Ici 0) := by
    rw [hD]; exact hD1.sub hLc
  have hq_cont : ContinuousOn q (Set.Ici 0) :=
    ContinuousOn.congr ((Complex.continuous_exp.continuousOn).comp hLc (fun _ _ => Set.mem_univ _))
      (fun t ht => (hL t ht).symm)
  have hq1_cont : ContinuousOn (fun t : ℝ => q (t + 1)) (Set.Ici 0) :=
    hq_cont.comp hshiftC.continuousOn (by intro t ht; simp only [Set.mem_Ici] at ht ⊢; linarith)
  have hr_cont : ContinuousOn r (Set.Ici 0) := by
    rw [hr_def]; exact hq1_cont.div hq_cont (fun t ht => hqne t ht)
  have hrS : ContinuousOn r (Set.Ici T) := hr_cont.mono hTS
  have hrlamS : ContinuousOn (fun t : ℝ => r t / lam) (Set.Ici T) := hrS.div_const lam
  have hlogS : ContinuousOn (fun t : ℝ => Complex.log (r t / lam)) (Set.Ici T) :=
    hrlamS.clog hslit
  have hℓrS : ContinuousOn (fun t : ℝ => ℓ (r t)) (Set.Ici T) := by
    rw [hℓ]
    exact (continuousOn_const (c := c₀)).add hlogS
  have hG_cont : ContinuousOn (fun t : ℝ => D t - ℓ (r t)) (Set.Ici T) :=
    (hD0.mono hTS).sub hℓrS
  -- `exp (D t - ℓ (r t)) = 1` on `[T, ∞)`.
  have hGT : ∀ t ∈ Set.Ici T, Complex.exp (D t - ℓ (r t)) = 1 := by
    intro t ht
    have ht0 : t ∈ Set.Ici (0 : ℝ) := hTS ht
    have ht10 : t + 1 ∈ Set.Ici (0 : ℝ) := by simp only [Set.mem_Ici] at ht0 ⊢; linarith
    have hDt : Complex.exp (D t) = r t := by
      simp only [hD]
      rw [Complex.exp_sub, hL (t + 1) ht10, hL t ht0, hr_def]
    have hrt_ne : r t ≠ 0 := by
      intro h0
      have hb := hUT t ht
      rw [h0, Metric.mem_ball, dist_eq_norm] at hb
      simp only [zero_sub, norm_neg] at hb
      linarith [norm_nonneg lam]
    rw [Complex.exp_sub, hDt, hℓ_exp (r t) hrt_ne]
    exact div_self hrt_ne
  -- The difference is constant on the preconnected interval `[T, ∞)`.
  have hGconst : ∀ t ∈ Set.Ici T, D t - ℓ (r t) = D T - ℓ (r T) := by
    intro t ht
    have hpre : IsPreconnected (Set.Ici T) := isPreconnected_Ici
    refine hpre.constant_of_mapsTo isDiscrete_exp_preimage_one hG_cont ?_ ht
      (Set.mem_Ici.mpr le_rfl)
    intro s hs
    simpa using hGT s hs
  refine ⟨ℓ lam + (D T - ℓ (r T)), ?_, ?_⟩
  · -- `exp` of the limit is the multiplier.
    rw [Complex.exp_add, hℓ_exp lam hlamne]
    have hg1 : Complex.exp (D T - ℓ (r T)) = 1 := hGT T (Set.mem_Ici.mpr le_rfl)
    rw [hg1, mul_one, hlam]
  · -- Convergence of the drift.
    have hℓr_tendsto : Tendsto (fun t : ℝ => ℓ (r t)) atTop (𝓝 (ℓ lam)) :=
      hℓcont.tendsto.comp hrlam
    have hD_eq : (fun t : ℝ => ℓ (r t) + (D T - ℓ (r T))) =ᶠ[atTop] D := by
      filter_upwards [eventually_ge_atTop T] with t ht
      have hc := hGconst t (Set.mem_Ici.mpr ht)
      rw [← sub_add_cancel (D t) (ℓ (r t)), hc, add_comm]
    have hfin := (hℓr_tendsto.add_const (D T - ℓ (r T))).congr' hD_eq
    simpa only [hD] using hfin

end Work.LandLeaves.Snail
