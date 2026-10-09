import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `ε`-thickening of a hyperplane has volume `O(ε)`

Let `E` be a finite-dimensional real normed space with an additive Haar measure `volume`,
`g : E →L[ℝ] ℝ` a nonzero linear functional and `R > 0`.  We prove that there is a constant
`C > 0` with

`volume (cthickening ε {x | g x = 0} ∩ closedBall 0 R) ≤ C * ε`  for all `0 < ε ≤ 1`.

The proof picks `v` with `g v = 1` and uses the linear equivalence
`e : ℝ × ker g ≃ E`, `(t, y) ↦ t • v + y`.  A point of the `ε`-thickening of the kernel
satisfies `|g x| ≤ ‖g‖ ε`, so the relevant set is contained in the image under `e` of the box
`[-(‖g‖ε), ‖g‖ε] × closedBall 0 (R + ‖g‖ ‖v‖)`; the volume of that box is a constant times `ε`
because the product Haar measure is a scalar multiple of `volume` pushed forward by `e`.
-/

namespace NK.NUV2.Geom

open MeasureTheory Metric
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- The linear equivalence `(t, y) ↦ t • v + y` from `ℝ × ker g` to `E`, when `g v = 1`. -/
noncomputable def hyperplaneEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E →L[ℝ] ℝ) (v : E) (hv : g v = 1) :
    (ℝ × (LinearMap.ker (g : E →ₗ[ℝ] ℝ))) ≃ₗ[ℝ] E := by
  let F : (ℝ × (LinearMap.ker (g : E →ₗ[ℝ] ℝ))) →ₗ[ℝ] E :=
    { toFun := fun p => p.1 • v + (p.2 : E)
      map_add' := by
        intro p q
        change (p.1 + q.1) • v + ((p.2 : E) + (q.2 : E)) =
          p.1 • v + (p.2 : E) + (q.1 • v + (q.2 : E))
        rw [add_smul]; abel
      map_smul' := by
        intro c p
        change (c * p.1) • v + (c • (p.2 : E)) = c • (p.1 • v + (p.2 : E))
        rw [smul_add, smul_smul] }
  let G : E →ₗ[ℝ] (ℝ × (LinearMap.ker (g : E →ₗ[ℝ] ℝ))) :=
    { toFun := fun x => (g x, ⟨x - g x • v, by
        change g (x - g x • v) = 0
        rw [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]⟩)
      map_add' := by
        intro x y
        apply Prod.ext
        · change g (x + y) = g x + g y
          rw [map_add]
        · apply Subtype.ext
          change (x + y) - g (x + y) • v = (x - g x • v) + (y - g y • v)
          rw [map_add, add_smul]
          abel
      map_smul' := by
        intro c x
        apply Prod.ext
        · change g (c • x) = c * g x
          rw [map_smul, smul_eq_mul]
        · apply Subtype.ext
          change (c • x) - g (c • x) • v = c • (x - g x • v)
          rw [map_smul, smul_sub, smul_smul, smul_eq_mul] }
  refine LinearEquiv.ofLinearMap F G ?_ ?_
  · ext x
    change g x • v + (x - g x • v) = x
    abel
  · apply LinearMap.ext
    intro p
    obtain ⟨t, y⟩ := p
    have hy : g (y : E) = 0 := y.2
    apply Prod.ext
    · change g (t • v + (y : E)) = t
      rw [map_add, map_smul, hv, smul_eq_mul, mul_one, hy, add_zero]
    · apply Subtype.ext
      change (t • v + (y : E)) - g (t • v + (y : E)) • v = (y : E)
      rw [map_add, map_smul, hv, smul_eq_mul, mul_one, hy, add_zero]
      abel

/-- A point of the `ε`-thickening of the kernel of a nonzero functional `g` satisfies
`|g x| ≤ ‖g‖ * ε`. -/
lemma abs_apply_le_norm_mul_of_mem_cthickening {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : E →L[ℝ] ℝ) (hg : g ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) {x : E}
    (hx : x ∈ Metric.cthickening ε {y : E | g y = 0}) : |g x| ≤ ‖g‖ * ε := by
  have hgnorm : 0 < ‖g‖ := norm_pos_iff.mpr hg
  rw [Metric.mem_cthickening_iff] at hx
  have key : ENNReal.ofReal (|g x| / ‖g‖) ≤ Metric.infEDist x {y : E | g y = 0} := by
    rw [Metric.le_infEDist]
    intro y hy
    have hy0 : g y = 0 := hy
    have h1 : |g x| ≤ ‖g‖ * ‖x - y‖ := by
      have h2 : g x = g (x - y) := by rw [map_sub, hy0, sub_zero]
      calc |g x| = ‖g (x - y)‖ := by rw [h2]; exact (Real.norm_eq_abs _).symm
        _ ≤ ‖g‖ * ‖x - y‖ := g.le_opNorm _
    have h2 : |g x| / ‖g‖ ≤ ‖x - y‖ := by
      rw [div_le_iff₀ hgnorm]; linarith
    rw [edist_dist, dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal h2
  have h3 : ENNReal.ofReal (|g x| / ‖g‖) ≤ ENNReal.ofReal ε := key.trans hx
  have h4 : |g x| / ‖g‖ ≤ ε := (ENNReal.ofReal_le_ofReal_iff hε).mp h3
  rw [div_le_iff₀ hgnorm] at h4
  linarith

theorem volume_cthickening_hyperplane_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureTheory.MeasureSpace E] [BorelSpace E]
    [MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure E)]
    (g : E →L[ℝ] ℝ) (hg : g ≠ 0) (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      MeasureTheory.volume (Metric.cthickening ε {x : E | g x = 0} ∩ Metric.closedBall 0 R)
        ≤ ENNReal.ofReal (C * ε) := by
  -- a vector `v` with `g v = 1`
  have hgx : ∃ x : E, g x ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hg (ContinuousLinearMap.ext h)
  obtain ⟨x0, hx0⟩ := hgx
  let v : E := (g x0)⁻¹ • x0
  have hv : g v = 1 := by
    simp only [v, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hx0
  let K := LinearMap.ker (g : E →ₗ[ℝ] ℝ)
  let e : (ℝ × K) ≃ₗ[ℝ] E := hyperplaneEquiv g v hv
  let ν : Measure (ℝ × K) := (volume : Measure ℝ).prod (Measure.addHaar : Measure K)
  haveI hν : Measure.IsAddHaarMeasure ν := inferInstance
  haveI hmap : Measure.IsAddHaarMeasure (ν.map e) := inferInstance
  let d : ℝ≥0 := Measure.addHaarScalarFactor (volume : Measure E) (ν.map e)
  have hvol : (volume : Measure E) = (d : ℝ≥0∞) • (ν.map e) :=
    Measure.isAddLeftInvariant_eq_smul (volume : Measure E) (ν.map e)
  have hdpos : 0 < d := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  let c : ℝ := ‖g‖
  have hcpos : 0 < c := norm_pos_iff.mpr hg
  let W : ℝ≥0∞ := (Measure.addHaar : Measure K) (Metric.closedBall (0 : K) (R + c * ‖v‖))
  have hWlt : W < ∞ := IsCompact.measure_lt_top (isCompact_closedBall (0 : K) (R + c * ‖v‖))
  set C : ℝ := (d : ℝ) * 2 * c * (W.toReal + 1) + 1 with hCdef
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hw0 : (0 : ℝ) ≤ W.toReal := ENNReal.toReal_nonneg
  refine ⟨C, ?_, ?_⟩
  · rw [hCdef]
    have h1 : (0 : ℝ) ≤ (d : ℝ) * 2 := mul_nonneg hd0 (by norm_num)
    have h2 : (0 : ℝ) ≤ (d : ℝ) * 2 * c := mul_nonneg h1 hcpos.le
    have h3 : (0 : ℝ) ≤ (d : ℝ) * 2 * c * (W.toReal + 1) := mul_nonneg h2 (by linarith)
    linarith
  · intro ε hε hε1
    have hSmeas : MeasurableSet
        (Metric.cthickening ε {x : E | g x = 0} ∩ Metric.closedBall 0 R) :=
      (Metric.isClosed_cthickening.inter Metric.isClosed_closedBall).measurableSet
    have hemeas : Measurable (e : ℝ × K → E) :=
      (LinearMap.continuous_of_finiteDimensional (e : ℝ × K →ₗ[ℝ] E)).measurable
    have hsub : e ⁻¹' (Metric.cthickening ε {x : E | g x = 0} ∩ Metric.closedBall 0 R) ⊆
        Set.Icc (-(c * ε)) (c * ε) ×ˢ Metric.closedBall (0 : K) (R + c * ‖v‖) := by
      intro p hp
      have hp1 : e p ∈ Metric.cthickening ε {x : E | g x = 0} := hp.1
      have hp2 : e p ∈ Metric.closedBall (0 : E) R := hp.2
      have hep : e p = p.1 • v + (p.2 : E) := rfl
      have hge : |g (e p)| ≤ c * ε := abs_apply_le_norm_mul_of_mem_cthickening g hg hε.le hp1
      have hgp : g (e p) = p.1 := by
        rw [hep, map_add, map_smul, hv, smul_eq_mul, mul_one]
        have hy : g (p.2 : E) = 0 := p.2.2
        rw [hy, add_zero]
      have hnorm : ‖e p‖ ≤ R := by
        have h := Metric.mem_closedBall.mp hp2
        rwa [dist_zero_right] at h
      refine ⟨?_, ?_⟩
      · rw [Set.mem_Icc, ← hgp]
        exact (abs_le.mp hge)
      · rw [Metric.mem_closedBall, dist_zero_right]
        change ‖(p.2 : E)‖ ≤ R + c * ‖v‖
        have h2 : |p.1| ≤ c * ε := by rw [← hgp]; exact hge
        have hy : (p.2 : E) = e p - p.1 • v := by rw [hep]; abel
        calc ‖(p.2 : E)‖ = ‖e p - p.1 • v‖ := by rw [hy]
          _ ≤ ‖e p‖ + ‖p.1 • v‖ := norm_sub_le _ _
          _ = ‖e p‖ + |p.1| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ R + c * ε * ‖v‖ := by
                have h3 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
                nlinarith
          _ ≤ R + c * ‖v‖ := by
                have h4 : c * ε * ‖v‖ ≤ c * ‖v‖ := by
                  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
                  nlinarith [hε1, hcpos.le]
                linarith
    have hd : (d : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) := ENNReal.coe_nnreal_eq d
    have h2ce : (0 : ℝ) ≤ 2 * (c * ε) := by nlinarith [hε.le, hcpos.le]
    have hdR : (0 : ℝ) ≤ (d : ℝ) := hd0
    calc (volume : Measure E)
            (Metric.cthickening ε {x : E | g x = 0} ∩ Metric.closedBall 0 R)
        = (d : ℝ≥0∞) * (ν (e ⁻¹'
            (Metric.cthickening ε {x : E | g x = 0} ∩ Metric.closedBall 0 R))) := by
          rw [hvol, Measure.smul_apply, smul_eq_mul, Measure.map_apply hemeas hSmeas]
      _ ≤ (d : ℝ≥0∞) * ν (Set.Icc (-(c * ε)) (c * ε) ×ˢ
            Metric.closedBall (0 : K) (R + c * ‖v‖)) := by
          exact mul_le_mul_of_nonneg_left (measure_mono hsub) (by positivity)
      _ = (d : ℝ≥0∞) * ((volume : Measure ℝ) (Set.Icc (-(c * ε)) (c * ε)) * W) := by
          rw [Measure.prod_prod]
      _ = (d : ℝ≥0∞) * (ENNReal.ofReal (2 * (c * ε)) * W) := by
          rw [Real.volume_Icc, show c * ε - (-(c * ε)) = 2 * (c * ε) by ring]
      _ ≤ ENNReal.ofReal (C * ε) := by
          have hconv : (d : ℝ≥0∞) * (ENNReal.ofReal (2 * (c * ε)) * W) =
              (d : ℝ≥0∞) * (ENNReal.ofReal (2 * (c * ε)) * ENNReal.ofReal W.toReal) := by
            rw [ENNReal.ofReal_toReal hWlt.ne]
          have hcomb : (d : ℝ≥0∞) * (ENNReal.ofReal (2 * (c * ε)) * ENNReal.ofReal W.toReal) =
              ENNReal.ofReal ((d : ℝ) * ((2 * (c * ε)) * W.toReal)) := by
            rw [hd, ENNReal.ofReal_mul hdR, ENNReal.ofReal_mul h2ce]
          calc (d : ℝ≥0∞) * (ENNReal.ofReal (2 * (c * ε)) * W)
              = (d : ℝ≥0∞) * (ENNReal.ofReal (2 * (c * ε)) * ENNReal.ofReal W.toReal) := hconv
            _ = ENNReal.ofReal ((d : ℝ) * ((2 * (c * ε)) * W.toReal)) := hcomb
            _ ≤ ENNReal.ofReal (C * ε) := by
                apply ENNReal.ofReal_le_ofReal
                rw [hCdef]
                nlinarith [hε.le, hcpos.le, hdR, hw0]

end NK.NUV2.Geom
