import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.BoseBoxFock.aliasImageIdentity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.AliasClosedAux` — the closed-ball support/decay lemmas of the aliasing chapter

The closed-ball (`tsupport g ⊆ closedBall 0 (ℓ/2)`) class of states — the class of the admissible
states `g = χ_Λ·h` — differs from the open-ball class of the corpus (`tsupport g ⊆ ball 0 (ℓ/2)`)
in exactly one structural way: the translates of `supp g` now *touch* on the sphere
`{‖u‖ = ℓ}` (`u = ℓ • latVec m`, `‖m‖ = 1`) instead of being disjoint.  The overlap there is a
single point, a null set, so every statement of the open-ball chapter still holds — but the
*pointwise* support arguments of the corpus (which produce a strict inequality contradiction) no
longer apply, and the vanishing at the touching point must be recovered by a limiting argument.

This file supplies the three facts on which the whole closed-ball chapter rests:

* `autocorr_eq_zero_of_lt_norm_closed` — the strict pointwise vanishing (`ℓ < ‖u‖`), the direct
  analogue of `AliasAux.autocorr_eq_zero_of_le_norm` (the same contradiction, now with `≤`);
* `autocorr_eq_zero_of_le_norm_closed` — the **full** vanishing `ℓ ≤ ‖u‖ ⟹ autocorr g u = 0`,
  obtained from the strict one by continuity along `δ ↦ (1+δ) • u` (this is where the touching
  case `‖u‖ = ℓ` is handled: the strict statement holds for every `(1+δ)u`, `δ > 0`);
* `autocorr_lens_bound` — the **lens (volume-of-overlap) decay**
  `‖autocorr g u‖ ≤ C·(ℓ² − ‖u‖²)^{3/2}` for `‖u‖ ≤ ℓ`: the intersection
  `B(0,ℓ/2) ∩ B(u,ℓ/2)` is contained in the ball `B(u/2, ½√(ℓ²−‖u‖²))` (parallelogram identity),
  so its volume is `≲ (ℓ² − ‖u‖²)^{3/2}`.  This is the quantitative input replacing the *strict
  support gap* of `imageW_lens_bound.exists_tsupport_subset_closedBall` (which fails at `R = ℓ/2`)
  in the `ℝ≥0∞`-summability of the image series: it gives, for the touching images `‖m‖ = 1`,
  `∫_{B(0,ℓ)} (ℓ²−‖u‖²)^{3/2} ‖u − ℓm‖^{−4} du < ∞` via
  `(ℓ²−‖u‖²)^{3/2} ≤ (2ℓ)^{3/2}‖u − ℓm‖^{3/2}` (hence an integrand `‖·‖^{−5/2}`, locally
  integrable in `ℝ³`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Real BigOperators Topology

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 4000000

/-- The closed ball `closedBall 0 (ℓ/2)` is compact, hence a smooth `g` supported there has
compact support. -/
theorem hasCompactSupport_of_closedBall {ℓ : ℝ} {g : E3 → ℂ}
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) : HasCompactSupport g :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E3) (ℓ / 2))
    (fun x hx => hgsupp (subset_closure hx))

/-- **Strict pointwise vanishing of the autocorrelation.**  For `g` smooth with
`tsupport g ⊆ closedBall 0 (ℓ/2)` and `ℓ < ‖u‖`, the two balls `B(0,ℓ/2)` and `B(u,ℓ/2)` are
disjoint (a common point `x` would give `‖u‖ ≤ ‖x‖ + ‖x − u‖ ≤ ℓ`), so the integrand of
`autocorr g u` vanishes identically. -/
theorem autocorr_eq_zero_of_lt_norm_closed {ℓ : ℝ} (_hℓ : 0 < ℓ)
    {g : E3 → ℂ} (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) {u : E3}
    (hu : ℓ < ‖u‖) : autocorr g u = 0 := by
  have hzero : ∀ x, g x * starRingEnd ℂ (g (x - u)) = 0 := by
    intro x
    by_contra h
    have hx : g x ≠ 0 := fun hx0 => h (by simp [hx0])
    have hy : g (x - u) ≠ 0 := fun hy0 => h (by simp [hy0])
    have hxmem : x ∈ Metric.closedBall (0 : E3) (ℓ / 2) :=
      hgsupp (subset_closure (Function.mem_support.mpr hx))
    have hymem : x - u ∈ Metric.closedBall (0 : E3) (ℓ / 2) :=
      hgsupp (subset_closure (Function.mem_support.mpr hy))
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hxmem hymem
    have h1 : ‖u‖ ≤ ‖x - u‖ + ‖x‖ := by
      have h2 : ‖u‖ ≤ ‖u - x‖ + ‖x‖ := by
        have := norm_add_le (u - x) x
        simpa using this
      simpa [norm_sub_rev u x] using h2
    linarith
  rw [autocorr, show (fun x : E3 => g x * starRingEnd ℂ (g (x - u))) = fun _ => 0 from
    funext hzero]
  simp

/-- **Pointwise vanishing of the autocorrelation at and beyond the touching radius.**  For `g`
smooth with `tsupport g ⊆ closedBall 0 (ℓ/2)` and `ℓ ≤ ‖u‖`, `autocorr g u = 0`.
The strict case is `autocorr_eq_zero_of_lt_norm_closed`; the boundary case `‖u‖ = ℓ` is obtained by
continuity, along `δ ↦ (1 + δ) • u → u`, from the strict statements at `(1+δ) • u`. -/
theorem autocorr_eq_zero_of_le_norm_closed {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) {u : E3} (hu : ℓ ≤ ‖u‖) :
    autocorr g u = 0 := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_closedBall hgsupp
  have hcont : Continuous (fun δ : ℝ => autocorr g ((1 + δ) • u)) := by
    have hcont1 : Continuous (fun δ : ℝ => (1 + δ) • u) := by
      have h : Continuous (fun δ : ℝ => (1 : ℝ) • u + δ • u) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa [add_smul] using h
    exact (autocorr_continuous hg hgc).comp hcont1
  have hzero : ∀ δ : ℝ, 0 < δ → autocorr g ((1 + δ) • u) = 0 := by
    intro δ hδ
    apply autocorr_eq_zero_of_lt_norm_closed hℓ hgsupp
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 1 + δ)]
    nlinarith
  have h1 : Tendsto (fun δ : ℝ => autocorr g ((1 + δ) • u)) (𝓝[>] (0 : ℝ))
      (𝓝 (autocorr g u)) := by
    have := hcont.continuousAt.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
    simpa using this
  have h2 : Tendsto (fun δ : ℝ => autocorr g ((1 + δ) • u)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (hzero δ hδ).symm)
  exact tendsto_nhds_unique h1 h2

/-- **The autocorrelation kernel vanishes at every nonzero lattice image.**  Closed-ball twin of
`aliasKernel_latVec_eq_zero`; in particular the touching images (`‖latVec m‖ = 1`) are covered,
which the open-ball proof cannot reach. -/
theorem aliasKernel_latVec_eq_zero_closed {ℓ : ℝ} (hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2))
    {m : Fin 3 → ℤ} (hm : m ≠ 0) : aliasKernel g (ℓ • latVec m) = 0 := by
  have hge : ℓ ≤ ‖ℓ • latVec m‖ := by
    rw [norm_smul, Real.norm_of_nonneg hℓ.le]
    calc ℓ = ℓ * 1 := (mul_one ℓ).symm
      _ ≤ ℓ * ‖latVec m‖ :=
          mul_le_mul_of_nonneg_left (one_le_norm_latVec hm) hℓ.le
  have h := autocorr_eq_zero_of_le_norm_closed hℓ hg hgsupp hge
  simp only [aliasKernel, h, Complex.zero_re]

/-- **The lens (overlap-volume) decay of the autocorrelation.**  For `g` smooth with
`tsupport g ⊆ closedBall 0 (ℓ/2)` there is `C ≥ 0` with

    ‖autocorr g u‖ ≤ C·(ℓ² − ‖u‖²)^{3/2}     for all `‖u‖ ≤ ℓ`.

Proof: `‖autocorr g u‖ ≤ ∫_x ‖g x‖‖g(x−u)‖ ≤ ‖g‖_∞²·vol(tsupport g ∩ (u + tsupport g))`, and the
parallelogram identity gives
`tsupport g ∩ (u + tsupport g) ⊆ closedBall (u/2) (½√(ℓ² − ‖u‖²))`. -/
theorem autocorr_lens_bound {ℓ : ℝ} (_hℓ : 0 < ℓ) {g : E3 → ℂ}
    (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E3, ‖u‖ ≤ ℓ →
      ‖autocorr g u‖ ≤ C * (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ) := by
  have hK : IsCompact (tsupport g) := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_tsupport g, Metric.isBounded_closedBall.subset hgsupp⟩
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hg.continuous.continuousOn
  set Cg : ℝ := max C₀ 0 with hCg
  have hCg0 : 0 ≤ Cg := le_max_right _ _
  have hCglob : ∀ x : E3, ‖g x‖ ≤ Cg := by
    intro x
    by_cases hx : g x = 0
    · rw [hx, norm_zero]; exact hCg0
    · exact le_trans (hC₀ x (subset_closure (Function.mem_support.mpr hx))) (le_max_left _ _)
  set V₁ : ℝ := (volume : Measure E3).real (Metric.ball (0 : E3) 1) with hV₁
  have hV1 : 0 ≤ V₁ := by rw [hV₁]; exact measureReal_nonneg
  refine ⟨Cg ^ 2 * V₁, by positivity, fun u hu => ?_⟩
  set w : E3 := (2 : ℝ)⁻¹ • u with hw
  set r : ℝ := Real.sqrt ((ℓ ^ 2 - ‖u‖ ^ 2) / 4) with hr
  have hnn : 0 ≤ ℓ ^ 2 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u, hu]
  have hmem : ∀ x : E3, x ∈ tsupport g → x - u ∈ tsupport g →
      x ∈ Metric.closedBall w r := by
    intro x hx hy
    have hx1 : ‖x‖ ≤ ℓ / 2 := by
      have h := hgsupp hx; rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hy1 : ‖x - u‖ ≤ ℓ / 2 := by
      have h := hgsupp hy; rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hx2 : ‖x‖ ^ 2 ≤ (ℓ / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx1 2
    have hy2 : ‖x - u‖ ^ 2 ≤ (ℓ / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg (x - u)) hy1 2
    have h2 : ‖x - w‖ ^ 2 ≤ r ^ 2 := by
      rw [hr, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (ℓ ^ 2 - ‖u‖ ^ 2) / 4)]
      have hpar := parallelogram_law_with_norm ℝ (x - w) w
      have h1 : x - w + w = x := sub_add_cancel _ _
      have h3 : x - w - w = x - u := by
        rw [hw, sub_sub, ← add_smul]
        norm_num
      rw [h1, h3] at hpar
      have hw2 : ‖w‖ ^ 2 = ‖u‖ ^ 2 / 4 := by
        rw [hw, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
        ring
      have hkey : 2 * ‖x - w‖ ^ 2 = ‖x‖ ^ 2 + ‖x - u‖ ^ 2 - ‖u‖ ^ 2 / 2 := by
        rw [hw2] at hpar; linarith
      nlinarith [hkey, hx2, hy2]
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖x - w‖ = Real.sqrt (‖x - w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt h2
      _ = r := Real.sqrt_sq (Real.sqrt_nonneg _)
  have hpt : ∀ x : E3, ‖g x * starRingEnd ℂ (g (x - u))‖ ≤
      Cg ^ 2 * (Metric.closedBall w r).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall w r
    · rw [Set.indicator_of_mem hx, mul_one, norm_mul, Complex.norm_conj]
      calc ‖g x‖ * ‖g (x - u)‖ ≤ Cg * Cg :=
            mul_le_mul (hCglob x) (hCglob (x - u)) (norm_nonneg _) hCg0
        _ = Cg ^ 2 := by ring
    · rw [Set.indicator_of_notMem hx, mul_zero]
      by_contra hne
      have hx0 : g x ≠ 0 := fun h => hne (by simp [h])
      have hy0 : g (x - u) ≠ 0 := fun h => hne (by simp [h])
      exact hx (hmem x (subset_closure (Function.mem_support.mpr hx0))
        (subset_closure (Function.mem_support.mpr hy0)))
  have hmeasB : (volume : Measure E3) (Metric.closedBall w r) < ⊤ :=
    (isCompact_closedBall w r).measure_lt_top
  have hint : Integrable (fun x : E3 =>
      Cg ^ 2 * (Metric.closedBall w r).indicator (fun _ => (1 : ℝ)) x) := by
    refine Integrable.const_mul ?_ _
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (C := (1 : ℝ)) hmeasB.ne (by simp)
  have h1 : ‖autocorr g u‖ ≤ ∫ x : E3, ‖g x * starRingEnd ℂ (g (x - u))‖ := by
    rw [autocorr]
    exact norm_integral_le_integral_norm _
  have h2 : (∫ x : E3, ‖g x * starRingEnd ℂ (g (x - u))‖) ≤
      ∫ x : E3, Cg ^ 2 * (Metric.closedBall w r).indicator (fun _ => (1 : ℝ)) x :=
    integral_mono_of_nonneg (Eventually.of_forall (fun x => norm_nonneg _)) hint
      (Eventually.of_forall hpt)
  have hI : (∫ x : E3, (Metric.closedBall w r).indicator (fun _ => (1 : ℝ)) x)
      = volume.real (Metric.closedBall w r) :=
    integral_indicator_one (μ := volume) measurableSet_closedBall
  have h3 : (∫ x : E3, Cg ^ 2 * (Metric.closedBall w r).indicator (fun _ => (1 : ℝ)) x)
      = Cg ^ 2 * (volume.real (Metric.closedBall w r)) := by
    rw [MeasureTheory.integral_const_mul, hI]
  have hvr : (volume : Measure E3).real (Metric.closedBall w r)
      ≤ V₁ * (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ) := by
    have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
    have hr3 : r ^ 3 = (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ) * (1 / 4) ^ (3 / 2 : ℝ) := by
      rw [hr, Real.sqrt_eq_rpow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (ℓ ^ 2 - ‖u‖ ^ 2) / 4)]
      norm_num
      rw [Real.div_rpow hnn (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
      ring
    rw [Measure.real_def, Measure.addHaar_closedBall (μ := (volume : Measure E3)) w hr0,
      ENNReal.toReal_mul, finrank_euclideanSpace_fin]
    rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ r ^ 3)]
    rw [← Measure.real_def, ← hV₁, hr3]
    have h14 : (1 / 4 : ℝ) ^ (3 / 2 : ℝ) ≤ 1 := by
      calc (1 / 4 : ℝ) ^ (3 / 2 : ℝ) ≤ (1 : ℝ) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        _ = 1 := Real.one_rpow _
    calc ((ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ) * (1 / 4) ^ (3 / 2 : ℝ)) * V₁
        ≤ ((ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ) * 1) * V₁ := by
          refine mul_le_mul_of_nonneg_right ?_ hV1
          exact mul_le_mul_of_nonneg_left h14 (Real.rpow_nonneg hnn _)
      _ = V₁ * (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ) := by ring
  calc ‖autocorr g u‖ ≤ ∫ x : E3, ‖g x * starRingEnd ℂ (g (x - u))‖ := h1
    _ ≤ ∫ x : E3, Cg ^ 2 * (Metric.closedBall w r).indicator (fun _ => (1 : ℝ)) x := h2
    _ = Cg ^ 2 * (volume.real (Metric.closedBall w r)) := h3
    _ ≤ Cg ^ 2 * (V₁ * (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hvr (by positivity)
    _ = (Cg ^ 2 * V₁) * (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ) := by ring

/-- **The `‖m‖ = 1` decay.**  For `‖u‖ ≤ ℓ` and any `m` with `‖latVec m‖ ≥ 1` (in particular the
six touching images of the closed-ball chapter),

    (ℓ² − ‖u‖²)^{3/2} ≤ (2ℓ)^{3/2}·‖u − ℓ • latVec m‖^{3/2} .

This is the form in which the lens bound gives the integrability/`tsum`-finiteness of the image
series at the touching images: the singular weight `‖u − ℓm‖^{−4}` turns into the locally
integrable `‖·‖^{−5/2}`. -/
theorem rpow_lens_le_of_one_le_norm_latVec {ℓ : ℝ} (hℓ : 0 < ℓ) {u : E3}
    (hu : ‖u‖ ≤ ℓ) {m : Fin 3 → ℤ} (hm : 1 ≤ ‖latVec m‖) :
    (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ)
      ≤ (2 * ℓ) ^ (3 / 2 : ℝ) * ‖u - ℓ • latVec m‖ ^ (3 / 2 : ℝ) := by
  have hnn : 0 ≤ ℓ ^ 2 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u, hu]
  have hlm : ℓ ≤ ‖ℓ • latVec m‖ := by
    rw [norm_smul, Real.norm_of_nonneg hℓ.le]
    calc ℓ = ℓ * 1 := (mul_one ℓ).symm
      _ ≤ ℓ * ‖latVec m‖ := mul_le_mul_of_nonneg_left hm hℓ.le
  have hd : ℓ - ‖u‖ ≤ ‖u - ℓ • latVec m‖ := by
    have h1 : ‖ℓ • latVec m‖ ≤ ‖ℓ • latVec m - u‖ + ‖u‖ := by
      have := norm_add_le (ℓ • latVec m - u) u
      simpa using this
    rw [norm_sub_rev] at h1
    linarith
  have hd0 : 0 ≤ ℓ - ‖u‖ := by linarith [norm_nonneg u]
  have hfac : ℓ ^ 2 - ‖u‖ ^ 2 ≤ (2 * ℓ) * ‖u - ℓ • latVec m‖ := by
    have h2 : ℓ ^ 2 - ‖u‖ ^ 2 = (ℓ - ‖u‖) * (ℓ + ‖u‖) := by ring
    rw [h2]
    calc (ℓ - ‖u‖) * (ℓ + ‖u‖) ≤ ‖u - ℓ • latVec m‖ * (2 * ℓ) :=
          mul_le_mul hd (by linarith [norm_nonneg u]) (by linarith [norm_nonneg u]) (norm_nonneg _)
      _ = (2 * ℓ) * ‖u - ℓ • latVec m‖ := by ring
  calc (ℓ ^ 2 - ‖u‖ ^ 2) ^ (3 / 2 : ℝ)
      ≤ ((2 * ℓ) * ‖u - ℓ • latVec m‖) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hnn hfac (by norm_num)
    _ = (2 * ℓ) ^ (3 / 2 : ℝ) * ‖u - ℓ • latVec m‖ ^ (3 / 2 : ℝ) :=
        Real.mul_rpow (by positivity) (norm_nonneg _)

end Work.BoseBoxFock
