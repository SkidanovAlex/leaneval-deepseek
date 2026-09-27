import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Work.SimplyConnected.ABS.globalizedBarrier_dev
import Submission.Work.SimplyConnected.ABS.bouligandDatum

/-!
# The coherent subharmonic barrier at a regular frontier point

This file proves `Work.SimplyConnected.ABS.RegBouligand.coherentSubharmonicBarrier`: given a *local barrier*
`u` at a frontier point `p` of an open set `Ω` (superharmonic and `> 0` on `Ω ∩ V`, continuous on
`V`, `u p = 0`), there is a subharmonic `b < 0` on `Ω` with `b → 0` at `p`.

The proof is the classical Bouligand globalization in the form of Ivrii's *Perron's Method*
(Bouligand's Lemma 2), implemented with the Poisson integral of a bounded measurable datum on a
chart circle: for a fixed chart disc and a level `m`, the datum is a "ramp" of `u/m` supported on
the collar, whose Poisson extension `h` is harmonic and satisfies `u/m + h ≥ 1` near the collar
(so that the clamped glue `min (u/m + h) 1` is superharmonic), while `h` is as small as we please
at the centre.  Coherence over a sequence of shrinking chart discs gives the exact decay.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical
open MeasureTheory
open scoped Topology

namespace Work.SimplyConnected.ABS.RegBouligand

open Commons.Analysis.Complex.Harmonic

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Chart data for the barrier construction.**  If `V` is an open neighbourhood of `p` then
there is `ρ > 0` such that the closed Euclidean ball of radius `ρ` around `c p` lies in the target
of the chart `c := chartAt ℂ p` and the corresponding closed chart disc lies in `V`. -/
theorem exists_chartClosedBall_subset_nhds {V : Set X} (hVo : IsOpen V) {p : X} (hpV : p ∈ V) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target ∧
      Submission.chartClosedBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ ⊆ V := by
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let a : ℂ := c p
  have hxsrc : p ∈ c.source := mem_chart_source ℂ p
  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ :=
    Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source hxsrc))
  have hpV' : V ∈ nhds (c.symm a) := by
    rw [c.left_inv hxsrc]
    exact hVo.mem_nhds hpV
  obtain ⟨ρ₂', hρ₂', hρ₂'sub⟩ :=
    Metric.mem_nhds_iff.mp
      ((c.continuousAt_symm (c.map_source hxsrc)).preimage_mem_nhds hpV')
  refine ⟨min ρ₁ ρ₂' / 2, half_pos (lt_min hρ₁ hρ₂'), ?_, ?_⟩
  · intro z hz
    refine hρ₁sub ?_
    have hz' : ‖z - a‖ ≤ min ρ₁ ρ₂' / 2 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [Metric.mem_ball, dist_eq_norm]
    have : min ρ₁ ρ₂' / 2 < ρ₁ := by
      have := min_le_left ρ₁ ρ₂'
      linarith
    linarith
  · intro x hx
    obtain ⟨hxs, hxc⟩ := hx
    have hx' : ‖c x - a‖ ≤ min ρ₁ ρ₂' / 2 := by
      have h := Metric.mem_closedBall.mp hxc
      rwa [dist_eq_norm] at h
    have hlt : ‖c x - a‖ < ρ₂' := by
      have := min_le_right ρ₁ ρ₂'
      linarith
    have hmem : c x ∈ Metric.ball a ρ₂' := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hlt
    have := hρ₂'sub hmem
    have h2 : c.symm (c x) = x := c.left_inv hxs
    rw [Set.mem_preimage] at this
    rwa [h2] at this

/-! ## The Bouligand ramp and datum -/

/-- The **Bouligand ramp**: `t ↦ max 0 (min 1 (1 + δ - t))`.  It equals `1` for `t ≤ δ`, decreases
linearly to `0` at `t = 1 + δ`, and satisfies `1 + δ - t ≤ ramp t` for the range used below. -/
def bouligandRamp (δ : ℝ) (t : ℝ) : ℝ := max 0 (min 1 (1 + δ - t))

theorem bouligandRamp_nonneg (δ t : ℝ) : 0 ≤ bouligandRamp δ t := le_max_left _ _

theorem bouligandRamp_le_one (δ t : ℝ) : bouligandRamp δ t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem bouligandRamp_mono {δ t₁ t₂ : ℝ} (h : t₂ ≤ t₁) :
    bouligandRamp δ t₁ ≤ bouligandRamp δ t₂ :=
  max_le_max le_rfl (min_le_min le_rfl (by linarith))

theorem bouligandRamp_of_le {δ t : ℝ} (h : t ≤ δ) : bouligandRamp δ t = 1 := by
  rw [bouligandRamp, min_eq_left (by linarith), max_eq_right zero_le_one]

theorem bouligandRamp_of_ge {δ t : ℝ} (h : 1 + δ ≤ t) : bouligandRamp δ t = 0 := by
  have h1 : min (1:ℝ) (1 + δ - t) = 1 + δ - t := min_eq_right (by linarith)
  have h2 : (0:ℝ) = max 0 (1 + δ - t) := (max_eq_left (by linarith)).symm
  rw [bouligandRamp, h1]
  exact h2.symm

theorem bouligandRamp_eq_of_mem {δ t : ℝ} (h : t ≤ δ) : bouligandRamp δ t = 1 :=
  bouligandRamp_of_le h

/-- The key inequality satisfied by the ramp: for `t ≥ 0`, `1 - t ≤ bouligandRamp δ t`. -/
theorem one_sub_le_bouligandRamp {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t) :
    1 - t ≤ bouligandRamp δ t := by
  rw [bouligandRamp]
  rcases le_total t δ with h | h
  · rw [min_eq_left (by linarith : (1:ℝ) ≤ 1 + δ - t), max_eq_right zero_le_one]
    linarith
  · rcases le_total t (1 + δ) with h2 | h2
    · have h1 : min (1:ℝ) (1 + δ - t) = 1 + δ - t := min_eq_right (by linarith)
      rw [h1, max_eq_right (by linarith : (0:ℝ) ≤ 1 + δ - t)]
      linarith
    · have h1 : min (1:ℝ) (1 + δ - t) = 1 + δ - t := min_eq_right (by linarith)
      rw [h1, max_eq_left (by linarith : (1:ℝ) + δ - t ≤ 0)]
      linarith


/-! ## The collar map and its geometry

For `0 < ρ' ≤ ρ` with `Metric.closedBall a ρ ⊆ c.target`, the map `w ↦ c.symm (a + ρ' * w)`
sends the unit circle onto (part of) the chart sphere `chartSphere c a ρ'`. -/

section Collar

variable {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}

/-- The **collar map** attached to a chart and a radius: `w ↦ c.symm (a + ρ * w)`.  On the unit
circle it parametrises the chart sphere of radius `ρ`. -/
def collarMap (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) (w : ℂ) : X :=
  c.symm (a + ρ * w)

theorem norm_rho'_mul {ρ' : ℝ} (hρ' : 0 < ρ') {w : ℂ} (hw : ‖w‖ = 1) : ‖(ρ' : ℂ) * w‖ = ρ' := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ', hw, mul_one]

theorem collarMap_mem_target {ρ ρ' : ℝ} (hρ' : 0 < ρ')
    (hsub : Metric.closedBall a ρ ⊆ c.target) (hρ'ρ : ρ' ≤ ρ) {w : ℂ} (hw : ‖w‖ = 1) :
    a + ρ' * w ∈ c.target := by
  refine hsub ?_
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  rw [norm_rho'_mul hρ' hw]
  exact hρ'ρ

theorem collarMap_mem_source {ρ ρ' : ℝ} (hρ' : 0 < ρ')
    (hsub : Metric.closedBall a ρ ⊆ c.target) (hρ'ρ : ρ' ≤ ρ) {w : ℂ} (hw : ‖w‖ = 1) :
    collarMap c a ρ' w ∈ c.source :=
  c.map_target (collarMap_mem_target hρ' hsub hρ'ρ hw)

theorem collarMap_apply {ρ ρ' : ℝ} (hρ' : 0 < ρ')
    (hsub : Metric.closedBall a ρ ⊆ c.target) (hρ'ρ : ρ' ≤ ρ) {w : ℂ} (hw : ‖w‖ = 1) :
    c (collarMap c a ρ' w) = a + ρ' * w :=
  c.right_inv (collarMap_mem_target hρ' hsub hρ'ρ hw)

theorem collarMap_mem_chartSphere {ρ ρ' : ℝ} (hρ' : 0 < ρ')
    (hsub : Metric.closedBall a ρ ⊆ c.target) (hρ'ρ : ρ' ≤ ρ) {w : ℂ} (hw : ‖w‖ = 1) :
    collarMap c a ρ' w ∈ Submission.chartSphere c a ρ' := by
  refine ⟨collarMap_mem_source hρ' hsub hρ'ρ hw, ?_⟩
  rw [Set.mem_preimage, collarMap_apply hρ' hsub hρ'ρ hw, Metric.mem_sphere, dist_eq_norm,
    add_sub_cancel_left, norm_rho'_mul hρ' hw]

theorem abs_rho'_mul_lt {ρ' : ℝ} (hρ' : 0 < ρ') {w : ℂ} (hw : ‖w‖ < 1) :
    ‖(ρ' : ℂ) * w‖ < ρ' := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ']
  calc ρ' * ‖w‖ < ρ' * 1 := mul_lt_mul_of_pos_left hw hρ'
    _ = ρ' := mul_one ρ'

theorem collarMap_mem_chartBall {ρ ρ' : ℝ} (hρ' : 0 < ρ')
    (hsub : Metric.closedBall a ρ ⊆ c.target) (hρ'ρ : ρ' ≤ ρ) {w : ℂ} (hw : ‖w‖ < 1) :
    collarMap c a ρ' w ∈ Submission.chartBall c a ρ' := by
  have hlt := abs_rho'_mul_lt hρ' hw
  have htgt : a + ρ' * w ∈ c.target := by
    refine hsub ?_
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact le_trans (le_of_lt hlt) hρ'ρ
  refine ⟨c.map_target htgt, ?_⟩
  rw [collarMap, Set.mem_preimage, c.right_inv htgt, Metric.mem_ball, dist_eq_norm,
    add_sub_cancel_left]
  exact hlt

/-- The collar map is continuous on the unit disc. -/
theorem continuousOn_collarMap_closedBall {ρ ρ' : ℝ} (hρ' : 0 < ρ')
    (hsub : Metric.closedBall a ρ ⊆ c.target) (hρ'ρ : ρ' ≤ ρ) :
    ContinuousOn (fun w : ℂ => c.symm (a + ρ' * w)) (Metric.closedBall (0 : ℂ) 1) := by
  have hmaps : MapsTo (fun w : ℂ => a + ρ' * w) (Metric.closedBall (0 : ℂ) 1) c.target := by
    intro w hw
    refine hsub ?_
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ']
    have hw' : ‖w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    nlinarith [hρ'.le]
  have hcont : ContinuousOn (fun w : ℂ => a + ρ' * w) (Metric.closedBall (0 : ℂ) 1) :=
    ((continuous_const.add (continuous_const.mul continuous_id)) :
      Continuous (fun w : ℂ => a + ρ' * w)).continuousOn
  exact c.continuousOn_symm.comp hcont hmaps

end Collar


/-! ## The Bouligand datum and its Poisson extension

For `Ω`, a chart `c`, a centre `a`, a radius `ρ'`, a level `m` and a slack `δ` we write
`D(w) = ramp δ (u (collarMap c a ρ' w) / m)` on the collar `Ω ∩ ∂Δ` and `0` off `Ω`.  Its Poisson
integral on the unit circle is the harmonic correction of the Bouligand construction. -/

section Datum

variable {Ω : Set X} {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ' m δ : ℝ} {u : X → ℝ}

/-- The **Bouligand datum**: the ramp of `u / m` on the collar `Ω`, and `0` outside `Ω`. -/
def bouligandDatum (Ω : Set X) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ' m δ : ℝ)
    (u : X → ℝ) : ℂ → ℝ :=
  fun w => if collarMap c a ρ' w ∈ Ω then bouligandRamp δ (u (collarMap c a ρ' w) / m) else 0

theorem bouligandDatum_nonneg (Ω : Set X) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ' m δ : ℝ)
    (u : X → ℝ) (w : ℂ) : 0 ≤ bouligandDatum Ω c a ρ' m δ u w := by
  rw [bouligandDatum]
  split
  · exact bouligandRamp_nonneg _ _
  · exact le_refl 0

theorem bouligandDatum_le_one (Ω : Set X) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ' m δ : ℝ)
    (u : X → ℝ) (w : ℂ) : bouligandDatum Ω c a ρ' m δ u w ≤ 1 := by
  rw [bouligandDatum]
  split
  · exact bouligandRamp_le_one _ _
  · norm_num

/-- On the collar, the datum is the ramp of `u / m`. -/
theorem bouligandDatum_of_mem {ρ' : ℝ} {w : ℂ} (h : collarMap c a ρ' w ∈ Ω) :
    bouligandDatum Ω c a ρ' m δ u w = bouligandRamp δ (u (collarMap c a ρ' w) / m) := by
  rw [bouligandDatum, if_pos h]

/-- Off the collar, the datum vanishes. -/
theorem bouligandDatum_of_not_mem {ρ' : ℝ} {w : ℂ} (h : collarMap c a ρ' w ∉ Ω) :
    bouligandDatum Ω c a ρ' m δ u w = 0 := by
  rw [bouligandDatum, if_neg h]

/-- The datum vanishes where `u / m ≥ 1 + δ`. -/
theorem bouligandDatum_eq_zero_of_le {ρ' m δ : ℝ} (hm : 0 < m) {w : ℂ}
    (h : 1 + δ ≤ u (collarMap c a ρ' w) / m) :
    bouligandDatum Ω c a ρ' m δ u w = 0 := by
  by_cases hmem : collarMap c a ρ' w ∈ Ω
  · rw [bouligandDatum_of_mem hmem, bouligandRamp_of_ge h]
  · rw [bouligandDatum_of_not_mem hmem]

end Datum


/-! ## The Bouligand step: one level of the construction

For a chart ball `Δ = chartBall c a ρ'` with `chartClosedBall c a ρ' ⊆ V` and a level `m > 0` we
put

* `G m w := 1` if `collarMap c a ρ' w ∈ Ω` and `u (collarMap c a ρ' w) < m`, and `0` otherwise;
* `P m := poissonInt (G m) 1`, harmonic on the unit disc;
* `bStar m x := - min (u x) 1 / m - P m ((c x - a) / ρ')` on `Ω ∩ Δ`;
* `bStep m x := max (bStar m x) (-1)` on `Ω ∩ Δ` and `-1` off `Δ`.

The function `bStep m` is subharmonic on `Ω`, negative, equal to `-1` off `Δ`, and as close to `0`
at `p` as we wish once `m` is small. -/

section Step

variable {Ω V : Set X} {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ' m : ℝ} {u : X → ℝ}

/-- The **indicator datum** of the Bouligand step. -/
def bouligandIndicator (Ω : Set X) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ' m : ℝ)
    (u : X → ℝ) : ℂ → ℝ :=
  fun w => if collarMap c a ρ' w ∈ Ω ∧ u (collarMap c a ρ' w) < m then 1 else 0

theorem bouligandIndicator_nonneg (Ω : Set X) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ' m : ℝ)
    (u : X → ℝ) (w : ℂ) : 0 ≤ bouligandIndicator Ω c a ρ' m u w := by
  rw [bouligandIndicator]; split <;> norm_num

theorem bouligandIndicator_le_one (Ω : Set X) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ' m : ℝ)
    (u : X → ℝ) (w : ℂ) : bouligandIndicator Ω c a ρ' m u w ≤ 1 := by
  rw [bouligandIndicator]; split <;> norm_num

/-- On the "bad set" the indicator datum is `1`. -/
theorem bouligandIndicator_eq_one {w : ℂ}
    (h : collarMap c a ρ' w ∈ Ω ∧ u (collarMap c a ρ' w) < m) :
    bouligandIndicator Ω c a ρ' m u w = 1 := by
  rw [bouligandIndicator, if_pos h]

/-- Off the "bad set" the indicator datum vanishes. -/
theorem bouligandIndicator_eq_zero {w : ℂ}
    (h : ¬ (collarMap c a ρ' w ∈ Ω ∧ u (collarMap c a ρ' w) < m)) :
    bouligandIndicator Ω c a ρ' m u w = 0 := by
  rw [bouligandIndicator, if_neg h]

/-- The **Bouligand step function**: the clamped `bStar` on the chart ball, `-1` outside. -/
def bouligandStep (Ω : Set X) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ' m : ℝ) (u : X → ℝ) :
    X → ℝ :=
  fun x => if x ∈ Submission.chartBall c a ρ' then
      max (-(min (u x) 1) / m
        - poissonInt (bouligandIndicator Ω c a ρ' m u) 1 ((c x - a) / ρ')) (-1)
    else -1

theorem bouligandStep_of_not_mem (hΩo : IsOpen Ω)
    {x : X} (hx : x ∉ Submission.chartBall c a ρ') :
    bouligandStep Ω c a ρ' m u x = -1 := by
  rw [bouligandStep, if_neg hx]

end Step


/-! ## Continuity of the collar parametrisation and circle integrability of the datum -/

section Integrable

variable {Ω V : Set X} {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ ρ' m : ℝ} {u : X → ℝ}

/-- The parametrisation of the chart sphere by the unit circle is continuous. -/
theorem continuous_collarMap_circle (hρ' : 0 < ρ') (hsub : Metric.closedBall a ρ ⊆ c.target)
    (hρ'ρ : ρ' ≤ ρ) :
    Continuous (fun θ : ℝ => collarMap c a ρ' (circleMap (0 : ℂ) 1 θ)) := by
  have hmem : ∀ θ : ℝ, circleMap (0 : ℂ) 1 θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro θ
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    simp [circleMap, Complex.norm_exp_ofReal_mul_I]
  exact (continuousOn_collarMap_closedBall hρ' hsub hρ'ρ).comp_continuous
    (continuous_circleMap 0 1) hmem

/-- The unit-circle points of the collar have their `collarMap` image on the chart sphere, and the
latter lies in the closed chart ball, hence in `V`. -/
theorem collarMap_circle_mem_chartSphere (hρ' : 0 < ρ') (hsub : Metric.closedBall a ρ ⊆ c.target)
    (hρ'ρ : ρ' ≤ ρ) (θ : ℝ) :
    collarMap c a ρ' (circleMap (0 : ℂ) 1 θ) ∈ Submission.chartSphere c a ρ' := by
  refine collarMap_mem_chartSphere hρ' hsub hρ'ρ ?_
  simp [circleMap, Complex.norm_exp_ofReal_mul_I]

/-- The set of `θ` whose collar point is a "bad" point of `Ω` (inside `Ω` with `u < m`) is
measurable. -/
theorem measurableSet_badCollar (hρ' : 0 < ρ') (hsub : Metric.closedBall a ρ ⊆ c.target)
    (hρ'ρ : ρ' ≤ ρ) {Ω : Set X} (hΩo : IsOpen Ω) {V : Set X}
    (hucont : ContinuousOn u V)
    (hV : ∀ θ : ℝ, collarMap c a ρ' (circleMap (0 : ℂ) 1 θ) ∈ V) :
    MeasurableSet {θ : ℝ | collarMap c a ρ' (circleMap (0 : ℂ) 1 θ) ∈ Ω ∧
      u (collarMap c a ρ' (circleMap (0 : ℂ) 1 θ)) < m} := by
  have hc := continuous_collarMap_circle (c := c) (a := a) hρ' hsub hρ'ρ
  have h1 : IsOpen {θ : ℝ | collarMap c a ρ' (circleMap (0 : ℂ) 1 θ) ∈ Ω} :=
    hΩo.preimage hc
  have hu : Continuous (fun θ : ℝ => u (collarMap c a ρ' (circleMap (0 : ℂ) 1 θ))) :=
    hucont.comp_continuous hc hV
  have h2 : IsOpen {θ : ℝ | u (collarMap c a ρ' (circleMap (0 : ℂ) 1 θ)) < m} :=
    isOpen_lt hu continuous_const
  exact (h1.inter h2).measurableSet

/-- The circle integrability of the (complexified) indicator datum. -/
theorem circleIntegrable_bouligandIndicator (hρ' : 0 < ρ') (hsub : Metric.closedBall a ρ ⊆ c.target)
    (hρ'ρ : ρ' ≤ ρ) {Ω : Set X} (hΩo : IsOpen Ω) {V : Set X} (hucont : ContinuousOn u V)
    (hV : ∀ θ : ℝ, collarMap c a ρ' (circleMap (0 : ℂ) 1 θ) ∈ V) :
    CircleIntegrable (fun z : ℂ => (bouligandIndicator Ω c a ρ' m u z : ℂ)) 0 1 := by
  have hmeas := measurableSet_badCollar (m := m) (u := u) hρ' hsub hρ'ρ hΩo hucont hV
  set S : Set ℝ := {θ : ℝ | collarMap c a ρ' (circleMap (0 : ℂ) 1 θ) ∈ Ω ∧
    u (collarMap c a ρ' (circleMap (0 : ℂ) 1 θ)) < m} with hS
  have hSm : MeasurableSet S := hmeas
  have hfun : (fun θ : ℝ => (bouligandIndicator Ω c a ρ' m u (circleMap (0 : ℂ) 1 θ) : ℂ))
      = fun θ : ℝ => ((S.indicator (fun _ : ℝ => (1 : ℝ))) θ : ℂ) := by
    funext θ
    rw [bouligandIndicator]
    by_cases h : collarMap c a ρ' (circleMap (0 : ℂ) 1 θ) ∈ Ω ∧
        u (collarMap c a ρ' (circleMap (0 : ℂ) 1 θ)) < m
    · rw [if_pos h, Set.indicator_of_mem (by simpa [hS] using h)]
    · rw [if_neg h, Set.indicator_of_notMem (by simpa [hS] using h)]
  have hf : AEStronglyMeasurable
      (fun θ : ℝ => (bouligandIndicator Ω c a ρ' m u (circleMap (0 : ℂ) 1 θ) : ℂ)) volume := by
    rw [hfun]
    exact (Complex.continuous_ofReal.measurable.comp (measurable_const.indicator hSm)).aestronglyMeasurable
  have hbound : ∀ᵐ θ ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))),
      ‖(bouligandIndicator Ω c a ρ' m u (circleMap (0 : ℂ) 1 θ) : ℂ)‖ ≤ 1 := by
    filter_upwards with θ
    have h1 := bouligandIndicator_nonneg (Ω := Ω) (c := c) (a := a) (ρ' := ρ') (m := m) u
      (circleMap (0 : ℂ) 1 θ)
    have h2 := bouligandIndicator_le_one (Ω := Ω) (c := c) (a := a) (ρ' := ρ') (m := m) u
      (circleMap (0 : ℂ) 1 θ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, h2⟩
  rw [CircleIntegrable, intervalIntegrable_iff]
  rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
    (hf.mono_measure (MeasureTheory.Measure.restrict_le_self)) 1 hbound

end Integrable

/-! ## Status of this file (work in progress, continued next session)

Proved here and sorry-free: `exists_chartClosedBall_subset_nhds`, the ramp lemmas
(`bouligandRamp`, `one_sub_le_bouligandRamp`, ...), the collar geometry (`collarMap`,
`collarMap_mem_chartBall`, `continuousOn_collarMap_closedBall`, ...), the indicator datum
`bouligandIndicator` with its bounds, and its circle integrability
(`circleIntegrable_bouligandIndicator`).  Also proved this session, in a separate module:
`Work.Analysis.Poisson.poissonInt_tendsto_of_continuousWithinAt` (the Poisson integral tends to the
datum at a *continuity point* of the circle restriction).

Remaining (the Bouligand step, using the machinery of
`Work.SimplyConnected.ABS.bouligandDatum`, which establishes the collar limits and the *collar
inequality* `one_le_u_div_add_harmonicGlue`): the two-level construction
`bStar := -min(u,1)/m - harmonicGlue` clamped below at `-1`, its subharmonicity (the clamp below
`-1` makes the collar interface invisible: at points where `b = -1` the mean-value inequality is
automatic, and elsewhere a small enough chart ball lies in `Ω ∩ chartBall c a ρ`), its bounds, its
decay at `p` (mean-value formula at the centre plus the smallness of `{u < m}`), the coherence
(`exists_coherent_of_step`) and the assembly. -/


/-! ## Poisson-integral facts (local copies)

`Work.SimplyConnected.ABS.bouligandPoissonFacts` proves these too, but it re-declares
`poissonInt_nonneg`, which `...bouligandDatum` declares as well, so the two modules cannot be
imported together.  The two facts used below are restated here. -/

section PoissonFacts

/-- The Poisson integral of a *circle-integrable* datum is harmonic inside the disc. -/
theorem poissonInt_harmonicOnNhd_of_circleIntegrable' {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : CircleIntegrable (fun z : ℂ => (g z : ℂ)) 0 r) :
    InnerProductSpace.HarmonicOnNhd (Commons.Analysis.Complex.Harmonic.poissonInt g r)
      (Metric.ball (0 : ℂ) r) := by
  intro x hx
  let G : ℂ → ℂ := fun z => (g z : ℂ)
  have hg_int : CircleIntegrable g 0 r := Work.Analysis.Poisson.circleIntegrable_of_ofReal hg
  let F : ℂ → ℂ := fun w => Real.circleAverage (fun z : ℂ => herglotzRieszKernel 0 w z • G z) 0 r
  have hF_analytic : AnalyticOnNhd ℂ F (Metric.ball 0 r) :=
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul (f := G) (R := r) hg).mono
      (fun w hw hs => by
        rw [Metric.mem_sphere, dist_zero_right] at hs
        rw [Metric.mem_ball, dist_zero_right] at hw
        linarith [le_abs_self r])
  have hFx : AnalyticAt ℂ F x := hF_analytic x hx
  have hRe : InnerProductSpace.HarmonicAt (fun w : ℂ => (F w).re) x :=
    AnalyticAt.harmonicAt_re hFx
  have h_eq : (fun w : ℂ => (F w).re) =ᶠ[𝓝 x]
      Commons.Analysis.Complex.Harmonic.poissonInt g r := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with w hw
    calc (F w).re = Real.circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • g) 0 r :=
          re_circleAverage_herglotzRieszKernel_smul hg_int (fun hs => by
          rw [Metric.mem_sphere, dist_zero_right] at hs
          rw [Metric.mem_ball, dist_zero_right] at hw
          linarith [le_abs_self r])
      _ = Real.circleAverage (fun z : ℂ => poissonKernel 0 w z * g z) 0 r := by
          congr 1
          funext z
          simp [← poissonKernel_eq_re_herglotzRieszKernel (c := (0 : ℂ)) (w := w)]
  exact (InnerProductSpace.harmonicAt_congr_nhds h_eq.symm).mpr hRe

/-- The value of the Poisson integral at the centre is the circle average of the datum. -/
theorem poissonInt_apply_zero' {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) :
    Commons.Analysis.Complex.Harmonic.poissonInt g r 0 = Real.circleAverage g 0 r := by
  rw [Commons.Analysis.Complex.Harmonic.poissonInt]
  refine Real.circleAverage_congr_sphere (fun z hz => ?_)
  have hzr : ‖z‖ = r := by
    have h := Metric.mem_sphere.mp hz
    rwa [dist_eq_norm, sub_zero, abs_of_pos hr] at h
  show poissonKernel 0 0 z * g z = g z
  have hk : poissonKernel 0 0 z = 1 := by
    rw [Commons.Analysis.Complex.Harmonic.poissonKernel_circle_r (w := 0) (z := z) (r := r)
      (by simpa using hr) hzr]
    have h2 : ‖z - 0‖ = r := by simpa using hzr
    rw [h2]
    field_simp
    simp
  rw [hk, one_mul]

end PoissonFacts

/-- Constant functions are subharmonic on any set. -/
theorem subharmonicOnX_const_local (k : ℝ) (U : Set X) :
    Submission.SubharmonicOnX (fun _ : X => k) U := by
  have h := (Work.SimplyConnected.ABS.superharmonicOnX_const_dev (-k) U).neg
  simpa using h

/-- Multiplication by a nonnegative constant preserves subharmonicity (the library version
carries a spurious `PreconnectedSpace` assumption). -/
theorem subharmonicOnX_const_mul_local {u : X → ℝ} {U : Set X} {k : ℝ} (hk : 0 ≤ k)
    (hu : Submission.SubharmonicOnX u U) :
    Submission.SubharmonicOnX (fun x => k * u x) U := by
  refine ⟨hu.1.const_mul k, fun x hx => ?_⟩
  obtain ⟨hxsrc, ρ, hρ, htgt, hcont, hmvp⟩ := hu.2 x hx
  have hfun : (fun y : X => k * u y) ∘ (chartAt ℂ x).symm
      = fun w => k * ((u ∘ (chartAt ℂ x).symm) w) := rfl
  refine ⟨hxsrc, ρ, hρ, htgt, ?_, ?_⟩
  · rw [hfun]; exact hcont.const_mul k
  · intro p hp r hr hpr
    rw [hfun]
    have hca : Real.circleAverage (fun w : ℂ => k * ((u ∘ (chartAt ℂ x).symm) w)) p r
        = k * Real.circleAverage ((u ∘ (chartAt ℂ x).symm)) p r := by
      simpa using Real.circleAverage_fun_smul
        (f := (u ∘ (chartAt ℂ x).symm)) (a := k) (c := p) (R := r)
    rw [hca]
    exact mul_le_mul_of_nonneg_left (hmvp p hp r hr hpr) hk

/-! ## The clamped Bouligand step function

For a chart `c`, a centre `a`, a radius `ρ`, a *datum level* `δ` and a *clamp level* `m` we set

* `bStar x = -min (u x / m) 1 - harmonicGlue x` — the negative of the clamped local barrier,
  scaled by the clamp level, minus the harmonic glue;
* `bStepFn x = max (bStar x) (-1)` on `Ω ∩ chartBall c a ρ` and `-1` everywhere else.

`bStepFn` is subharmonic on `Ω`, negative there, `≤ 0` everywhere, equal to `-1` off the chart
ball and off `Ω`, and as close to `0` at `p` as we wish (small `δ`, hence small `m`). -/

section StepFn

variable {Ω V : Set X} {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ δ m : ℝ} {u : X → ℝ}

/-- The negative of the clamped local barrier at clamp level `m`, minus the harmonic glue. -/
def bStar (Ω : Set X) (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ δ m : ℝ) : X → ℝ :=
  fun x => -(min (u x / m) 1) + -(Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ x)

theorem bStar_apply (x : X) :
    bStar Ω u c a ρ δ m x =
      -(min (u x / m) 1) + -(Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ x) := rfl

/-- The clamped Bouligand step function: `max bStar (-1)` on `Ω ∩ chartBall c a ρ`, and `-1`
everywhere else. -/
def bStepFn (Ω : Set X) (u : X → ℝ) (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ δ m : ℝ) :
    X → ℝ :=
  fun x => if x ∈ Ω then
    (if x ∈ Submission.chartBall c a ρ then max (bStar Ω u c a ρ δ m x) (-1) else -1) else -1

theorem bStepFn_of_not_mem_Ω {x : X} (hx : x ∉ Ω) : bStepFn Ω u c a ρ δ m x = -1 := by
  rw [bStepFn, if_neg hx]

theorem bStepFn_of_mem_not_mem_ball {x : X} (hx : x ∈ Ω)
    (hx' : x ∉ Submission.chartBall c a ρ) : bStepFn Ω u c a ρ δ m x = -1 := by
  rw [bStepFn, if_pos hx, if_neg hx']

theorem bStepFn_of_mem_ball {x : X} (hx : x ∈ Ω) (hx' : x ∈ Submission.chartBall c a ρ) :
    bStepFn Ω u c a ρ δ m x = max (bStar Ω u c a ρ δ m x) (-1) := by
  rw [bStepFn, if_pos hx, if_pos hx']

theorem bStepFn_eq_neg_one_of_not_mem_ball {x : X} (hx' : x ∉ Submission.chartBall c a ρ) :
    bStepFn Ω u c a ρ δ m x = -1 := by
  rw [bStepFn]
  by_cases hx : x ∈ Ω
  · rw [if_pos hx, if_neg hx']
  · rw [if_neg hx]

/-! ### Chart-ball geometry -/

theorem chartBallC_eq_chartBall (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    Work.SimplyConnected.ABS.chartBallC c a ρ = Submission.chartBall c a ρ := by
  ext x
  simp [Work.SimplyConnected.ABS.chartBallC, Submission.chartBall, Metric.mem_ball, dist_eq_norm]

theorem chartBallC_isOpen (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) :
    IsOpen (Work.SimplyConnected.ABS.chartBallC c a ρ) := by
  rw [chartBallC_eq_chartBall]; exact Submission.chartBall_isOpen c a ρ

theorem chartBallC_mono {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) :
    Work.SimplyConnected.ABS.chartBallC c a ρ₁ ⊆ Work.SimplyConnected.ABS.chartBallC c a ρ₂ :=
  fun _ hx => ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

theorem chartBallC_subset_chartClosedBall :
    Work.SimplyConnected.ABS.chartBallC c a ρ ⊆ Submission.chartClosedBall c a ρ :=
  fun _ hx => ⟨hx.1, Metric.ball_subset_closedBall
    (by simpa [Metric.mem_ball, dist_eq_norm] using hx.2)⟩

theorem chartBall_subset_chartClosedBall :
    Submission.chartBall c a ρ ⊆ Submission.chartClosedBall c a ρ :=
  fun _ hx => ⟨hx.1, Metric.ball_subset_closedBall hx.2⟩

theorem chartClosedBall_mono {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) :
    Submission.chartClosedBall c a ρ₁ ⊆ Submission.chartClosedBall c a ρ₂ :=
  fun _ hx => ⟨hx.1, Metric.closedBall_subset_closedBall h hx.2⟩

theorem chartBall_mono {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) :
    Submission.chartBall c a ρ₁ ⊆ Submission.chartBall c a ρ₂ :=
  fun _ hx => ⟨hx.1, Metric.ball_subset_ball h hx.2⟩

/-- Every point of the collar `Ω ∩ frontier (chartBall c a ρ)` is a parametrised collar point. -/
theorem exists_collarPoint_eq {ξ : X} (hρ : 0 < ρ)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hcl : ξ ∈ closure (Submission.chartBall c a ρ))
    (hnb : ξ ∉ Submission.chartBall c a ρ) :
    ∃ θ : ℝ, Work.SimplyConnected.ABS.collarPoint c a ρ θ = ξ := by
  have hcc : ξ ∈ Submission.chartClosedBall c a ρ :=
    closure_minimal chartBall_subset_chartClosedBall
      (Submission.isClosed_chartClosedBall htgt) hcl
  obtain ⟨hsrc, hle⟩ := Submission.mem_chartClosedBall.mp hcc
  have hnormle : ‖c ξ - a‖ ≤ ρ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hle
  have hnotlt : ¬ ‖c ξ - a‖ < ρ := fun h =>
    hnb (Submission.mem_chartBall.mpr ⟨hsrc, by simpa [Metric.mem_ball, dist_eq_norm] using h⟩)
  have heq : ‖c ξ - a‖ = ρ := le_antisymm hnormle (le_of_not_gt hnotlt)
  have hρne : ((ρ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  refine ⟨Complex.arg ((c ξ - a) / ρ), ?_⟩
  have hwnorm : ‖(c ξ - a) / ρ‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, heq,
      div_self (ne_of_gt hρ)]
  have harg : Complex.exp (Complex.arg ((c ξ - a) / ρ) * Complex.I) = (c ξ - a) / ρ := by
    have h1 := Complex.norm_mul_exp_arg_mul_I ((c ξ - a) / ρ)
    rw [hwnorm] at h1
    simpa using h1
  have hcirc : circleMap (0 : ℂ) 1 (Complex.arg ((c ξ - a) / ρ)) = (c ξ - a) / ρ := by
    rw [circleMap]
    simpa using harg
  rw [Work.SimplyConnected.ABS.collarPoint, hcirc]
  have h2 : a + ρ * ((c ξ - a) / ρ) = c ξ := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hρne]
    ring
  rw [h2, c.left_inv hsrc]

/-! ### The harmonic glue -/

/-- The harmonic glue is nonnegative on the chart ball. -/
theorem harmonicGlue_nonneg (hΩo : IsOpen Ω) (hVo : IsOpen V) (hcont : ContinuousOn u V)
    (hρ : 0 < ρ) (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V) :
    ∀ x ∈ Work.SimplyConnected.ABS.chartBallC c a ρ,
      0 ≤ Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ x := by
  intro x hx
  have hw : ‖(c x - a) / ρ‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, div_lt_one hρ]
    exact hx.2
  exact Work.SimplyConnected.ABS.poissonInt_nonneg one_pos
    (Work.Analysis.Poisson.circleIntegrable_of_ofReal
      (Work.SimplyConnected.ABS.circleIntegrable_bouligandDatum (Ω := Ω) (V := V) (u := u)
        (c := c) (a := a) (ρ := ρ) (m := δ) hΩo hVo hcont hρ htgt hV))
    (fun z _ => Work.SimplyConnected.ABS.bouligandDatum_nonneg Ω u c a ρ δ z) hw

/-- The harmonic glue is harmonic on the chart ball (measured in the chart at `p`). -/
theorem harmonicOnX_harmonicGlue {p : X} {Ω : Set X} {u : X → ℝ} {ρ δ : ℝ} (hρ : 0 < ρ)
    (htgt : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target)
    (hg : CircleIntegrable (fun z : ℂ =>
      (Work.SimplyConnected.ABS.bouligandDatum Ω u (chartAt ℂ p) ((chartAt ℂ p) p) ρ δ z : ℂ))
      0 1) :
    Submission.HarmonicOnX
      (Work.SimplyConnected.ABS.harmonicGlue Ω u (chartAt ℂ p) ((chartAt ℂ p) p) ρ δ)
      (Work.SimplyConnected.ABS.chartBallC (chartAt ℂ p) ((chartAt ℂ p) p) ρ) := by
  intro x hx
  refine (Submission.HarmonicOnXAt_iff_chart (x := x) (y := p) hx.1).mpr ?_
  have hxtgt : (chartAt ℂ p) x ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source hx.1
  have hev : (Work.SimplyConnected.ABS.harmonicGlue Ω u (chartAt ℂ p) ((chartAt ℂ p) p) ρ δ ∘
        (chartAt ℂ p).symm)
      =ᶠ[𝓝 ((chartAt ℂ p) x)]
      (fun z : ℂ => Commons.Analysis.Complex.Harmonic.poissonInt
        (fun y : ℂ => Work.SimplyConnected.ABS.bouligandDatum Ω u (chartAt ℂ p)
          ((chartAt ℂ p) p) ρ δ y) 1 ((z - (chartAt ℂ p) p) / ρ)) := by
    filter_upwards [(chartAt ℂ p).open_target.eventually_mem hxtgt] with z hz
    simp only [Function.comp_apply, Work.SimplyConnected.ABS.harmonicGlue]
    rw [(chartAt ℂ p).right_inv hz]
  refine (InnerProductSpace.harmonicAt_congr_nhds hev).mpr ?_
  refine Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
    (f := fun z : ℂ => (z - (chartAt ℂ p) p) / ρ)
    (u := Commons.Analysis.Complex.Harmonic.poissonInt
      (fun y : ℂ => Work.SimplyConnected.ABS.bouligandDatum Ω u (chartAt ℂ p)
        ((chartAt ℂ p) p) ρ δ y) 1)
    (x := (chartAt ℂ p) x) ?_ ?_
  · exact (analyticAt_id.sub analyticAt_const).div_const
  · have hb : ‖((chartAt ℂ p) x - (chartAt ℂ p) p) / ρ‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, div_lt_one hρ]
      simpa [Metric.mem_ball, dist_eq_norm] using hx.2
    exact poissonInt_harmonicOnNhd_of_circleIntegrable' one_pos hg _
      (by simpa [Metric.mem_ball, dist_eq_norm] using hb)

/-! ### The collar case: the step function is locally `-1` on the collar -/

/-- **The collar case.**  At a parametrised collar point of `Ω`, the step function is eventually
equal to `-1`: this is where the collar inequality `1 ≤ u/m + glue` (and the clamp at `-1`)
makes the interface invisible. -/
theorem bStepFn_eventually_neg_one {θ : ℝ}
    (hΩ : Work.SimplyConnected.ABS.collarPoint c a ρ θ ∈ Ω)
    (hΩo : IsOpen Ω) (hVo : IsOpen V) (hcont : ContinuousOn u V) (hρ : 0 < ρ)
    (hm0 : 0 < m) (hmδ : m < δ)
    (hpos : ∀ x ∈ Ω, x ∈ V → 0 < u x)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V) :
    bStepFn Ω u c a ρ δ m =ᶠ[𝓝 (Work.SimplyConnected.ABS.collarPoint c a ρ θ)] fun _ => -1 := by
  classical
  have hcollar := Work.SimplyConnected.ABS.one_le_u_div_add_harmonicGlue (Ω := Ω) (V := V)
    (u := u) (c := c) (a := a) (ρ := ρ) (δ := δ) (m := m) hΩo hVo hcont hρ hm0 hmδ hpos htgt hV hΩ
  rw [nhdsWithin] at hcollar
  obtain ⟨t₁, ht₁, t₂, ht₂, heq⟩ := Filter.mem_inf_iff.mp hcollar
  have hP : t₁ ∩ t₂ ⊆
      {x : X | 1 ≤ u x / m + Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ x} :=
    le_of_eq heq.symm
  have ht₂' : ∀ y ∈ Work.SimplyConnected.ABS.chartBallC c a ρ, y ∈ t₂ :=
    fun y hy => Filter.mem_principal.mp ht₂ hy
  have hball : ∀ y ∈ t₁, y ∈ Work.SimplyConnected.ABS.chartBallC c a ρ →
      1 ≤ u y / m + Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ y :=
    fun y hy hyb => hP ⟨hy, ht₂' y hyb⟩
  have hglue_nn : ∀ y ∈ Work.SimplyConnected.ABS.chartBallC c a ρ,
      0 ≤ Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ y :=
    harmonicGlue_nonneg (Ω := Ω) (V := V) (u := u) (c := c) (a := a) (ρ := ρ) (δ := δ)
      hΩo hVo hcont hρ htgt hV
  refine Filter.eventuallyEq_of_mem ht₁ fun y hy => ?_
  by_cases hyΩ : y ∈ Ω
  · by_cases hyb : y ∈ Submission.chartBall c a ρ
    · have hybC : y ∈ Work.SimplyConnected.ABS.chartBallC c a ρ := by
        rwa [chartBallC_eq_chartBall]
      have hone := hball y hy hybC
      have hglue := hglue_nn y hybC
      rw [bStepFn_of_mem_ball hyΩ hyb, bStar_apply]
      refine max_eq_right ?_
      rcases le_total (u y / m) 1 with hle | hge
      · rw [min_eq_left hle]
        linarith
      · rw [min_eq_right hge]
        linarith
    · rw [bStepFn_of_mem_not_mem_ball hyΩ hyb]
  · rw [bStepFn_of_not_mem_Ω hyΩ]

/-- The collar case at an arbitrary collar point. -/
theorem bStepFn_eventually_neg_one_of_mem_collar {ξ : X}
    (hξΩ : ξ ∈ Ω) (hξcl : ξ ∈ closure (Submission.chartBall c a ρ))
    (hξnb : ξ ∉ Submission.chartBall c a ρ)
    (hΩo : IsOpen Ω) (hVo : IsOpen V) (hcont : ContinuousOn u V) (hρ : 0 < ρ)
    (hm0 : 0 < m) (hmδ : m < δ)
    (hpos : ∀ x ∈ Ω, x ∈ V → 0 < u x)
    (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hV : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V) :
    bStepFn Ω u c a ρ δ m =ᶠ[𝓝 ξ] fun _ => -1 := by
  obtain ⟨θ, hθ⟩ := exists_collarPoint_eq (c := c) (a := a) hρ htgt hξcl hξnb
  have hΩ : Work.SimplyConnected.ABS.collarPoint c a ρ θ ∈ Ω := by rw [hθ]; exact hξΩ
  have h := bStepFn_eventually_neg_one (Ω := Ω) (V := V) (c := c) (a := a) (ρ := ρ) (δ := δ)
    (m := m) (u := u) (θ := θ) hΩ hΩo hVo hcont hρ hm0 hmδ hpos htgt hV
  rwa [hθ] at h

/-! ### Subharmonicity of `bStar` -/

/-- `bStar` is subharmonic on the chart ball. -/
theorem subharmonicOnX_bStar (hm0 : 0 < m)
    (hmono : Submission.SuperharmonicOnX (fun y : X => u y / m) (Ω ∩ V))
    (hglue : Submission.HarmonicOnX (Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ)
      (Work.SimplyConnected.ABS.chartBallC c a ρ))
    (hballV : Work.SimplyConnected.ABS.chartBallC c a ρ ⊆ V) :
    Submission.SubharmonicOnX (bStar Ω u c a ρ δ m)
      (Ω ∩ Work.SimplyConnected.ABS.chartBallC c a ρ) := by
  have hUV : Ω ∩ Work.SimplyConnected.ABS.chartBallC c a ρ ⊆ Ω ∩ V :=
    fun x hx => ⟨hx.1, hballV hx.2⟩
  have hmono' : Submission.SuperharmonicOnX (fun y : X => u y / m)
      (Ω ∩ Work.SimplyConnected.ABS.chartBallC c a ρ) :=
    hmono.mono hUV (hmono.1.mono hUV)
  have hmin : Submission.SubharmonicOnX (fun y : X => -(min (u y / m) 1))
      (Ω ∩ Work.SimplyConnected.ABS.chartBallC c a ρ) :=
    (Work.SimplyConnected.ABS.SuperharmonicOnX.inf_const_dev hmono' 1).neg
  have hglue' : Submission.SubharmonicOnX
      (fun y : X => -(Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ y))
      (Ω ∩ Work.SimplyConnected.ABS.chartBallC c a ρ) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact ((hglue x hx.2).neg.continuousAt).continuousWithinAt
    · intro x hx
      exact ((hglue x hx.2).neg).subharmonic
  have hsum := hmin.add hglue'
  convert hsum using 1
  funext y
  rw [bStar_apply]

/-! ### Subharmonicity of the step function -/

/-- `bStepFn` is subharmonic at every point of `Ω`. -/
theorem subharmonicOnXAt_bStepFn (hΩo : IsOpen Ω)
    (hsub : Submission.SubharmonicOnX (bStar Ω u c a ρ δ m)
      (Ω ∩ Work.SimplyConnected.ABS.chartBallC c a ρ))
    (hcollar : ∀ x ∈ Ω, x ∈ closure (Submission.chartBall c a ρ) →
      x ∉ Submission.chartBall c a ρ → bStepFn Ω u c a ρ δ m =ᶠ[𝓝 x] fun _ => -1) :
    ∀ x ∈ Ω, Submission.SubharmonicOnXAt (bStepFn Ω u c a ρ δ m) x := by
  intro x hx
  by_cases hxb : x ∈ Submission.chartBall c a ρ
  · have hxbC : x ∈ Work.SimplyConnected.ABS.chartBallC c a ρ := by
      rwa [chartBallC_eq_chartBall]
    have hxU : x ∈ Ω ∩ Work.SimplyConnected.ABS.chartBallC c a ρ := ⟨hx, hxbC⟩
    have hev : bStepFn Ω u c a ρ δ m =ᶠ[𝓝 x]
        (fun y : X => max (bStar Ω u c a ρ δ m y) (-1 : ℝ)) := by
      refine Filter.eventually_of_mem
        ((hΩo.inter (chartBallC_isOpen c a ρ)).mem_nhds hxU) fun y hy => ?_
      have hyb : y ∈ Submission.chartBall c a ρ := by
        rw [← chartBallC_eq_chartBall]; exact hy.2
      rw [bStepFn_of_mem_ball hy.1 hyb]
    exact ((hsub.2 x hxU).sup ((subharmonicOnX_const_local (-1) Ω).2 x hx)).congr hev.symm
  · by_cases hxcl : x ∈ closure (Submission.chartBall c a ρ)
    · exact ((subharmonicOnX_const_local (-1) Ω).2 x hx).congr
        (hcollar x hx hxcl hxb).symm
    · have hev : bStepFn Ω u c a ρ δ m =ᶠ[𝓝 x] fun _ => (-1 : ℝ) := by
        refine Filter.eventually_of_mem (isClosed_closure.isOpen_compl.mem_nhds hxcl)
          (fun y hy => bStepFn_eq_neg_one_of_not_mem_ball
            (fun hyb => hy (subset_closure hyb)))
      exact ((subharmonicOnX_const_local (-1) Ω).2 x hx).congr hev.symm

/-- `bStepFn` is subharmonic on `Ω`. -/
theorem subharmonicOnX_bStepFn (hΩo : IsOpen Ω)
    (hsub : Submission.SubharmonicOnX (bStar Ω u c a ρ δ m)
      (Ω ∩ Work.SimplyConnected.ABS.chartBallC c a ρ))
    (hcollar : ∀ x ∈ Ω, x ∈ closure (Submission.chartBall c a ρ) →
      x ∉ Submission.chartBall c a ρ → bStepFn Ω u c a ρ δ m =ᶠ[𝓝 x] fun _ => -1) :
    Submission.SubharmonicOnX (bStepFn Ω u c a ρ δ m) Ω :=
  ⟨continuousOn_of_forall_continuousAt
      (fun x hx => (subharmonicOnXAt_bStepFn (Ω := Ω) (c := c) (a := a) (ρ := ρ)
        (δ := δ) (m := m) (u := u) hΩo hsub hcollar x hx).continuousAt),
    subharmonicOnXAt_bStepFn (Ω := Ω) (c := c) (a := a) (ρ := ρ) (δ := δ) (m := m)
      (u := u) hΩo hsub hcollar⟩

/-! ### Bounds and decay -/

/-- The step function is `≤ 0` everywhere. -/
theorem bStepFn_nonpos (hm0 : 0 < m) (hballV : Work.SimplyConnected.ABS.chartBallC c a ρ ⊆ V)
    (hpos : ∀ x ∈ Ω, x ∈ V → 0 < u x)
    (hglue_nn : ∀ x ∈ Work.SimplyConnected.ABS.chartBallC c a ρ,
      0 ≤ Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ x) :
    ∀ x : X, bStepFn Ω u c a ρ δ m x ≤ 0 := by
  intro x
  by_cases hxΩ : x ∈ Ω
  · by_cases hxb : x ∈ Submission.chartBall c a ρ
    · have hxbC : x ∈ Work.SimplyConnected.ABS.chartBallC c a ρ := by
        rwa [chartBallC_eq_chartBall]
      have hu : 0 < u x := hpos x hxΩ (hballV hxbC)
      have hglue := hglue_nn x hxbC
      rw [bStepFn_of_mem_ball hxΩ hxb, bStar_apply]
      refine max_le ?_ (by norm_num)
      have hmin : 0 ≤ min (u x / m) 1 := le_min (le_of_lt (div_pos hu hm0)) zero_le_one
      linarith
    · rw [bStepFn_of_mem_not_mem_ball hxΩ hxb]; norm_num
  · rw [bStepFn_of_not_mem_Ω hxΩ]; norm_num

/-- The step function is strictly negative on `Ω`. -/
theorem bStepFn_neg (hm0 : 0 < m) (hballV : Work.SimplyConnected.ABS.chartBallC c a ρ ⊆ V)
    (hpos : ∀ x ∈ Ω, x ∈ V → 0 < u x)
    (hglue_nn : ∀ x ∈ Work.SimplyConnected.ABS.chartBallC c a ρ,
      0 ≤ Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ x) :
    ∀ x ∈ Ω, bStepFn Ω u c a ρ δ m x < 0 := by
  intro x hxΩ
  by_cases hxb : x ∈ Submission.chartBall c a ρ
  · have hxbC : x ∈ Work.SimplyConnected.ABS.chartBallC c a ρ := by
      rwa [chartBallC_eq_chartBall]
    have hu : 0 < u x := hpos x hxΩ (hballV hxbC)
    have hglue := hglue_nn x hxbC
    rw [bStepFn_of_mem_ball hxΩ hxb, bStar_apply]
    refine max_lt ?_ (by norm_num)
    have hmin : 0 < min (u x / m) 1 := lt_min (div_pos hu hm0) one_pos
    linarith
  · rw [bStepFn_of_mem_not_mem_ball hxΩ hxb]; norm_num

/-- The decay of the step function at `p`. -/
theorem bStepFn_decay {p : X} {ε : ℝ} (hε : 0 < ε) (hm0 : 0 < m)
    (hpc : p ∈ Work.SimplyConnected.ABS.chartBallC c a ρ)
    (hVo : IsOpen V) (hpV : p ∈ V) (hcont : ContinuousOn u V) (hup : u p = 0)
    (hglue_cont : ContinuousAt (Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ) p)
    (hglue_small : Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ p < ε / 2) :
    ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, -ε < bStepFn Ω u c a ρ δ m x := by
  have h1 : ∀ᶠ x in 𝓝 p, Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ x < ε / 2 :=
    hglue_cont.eventually (isOpen_Iio.mem_nhds hglue_small)
  have hulim : Filter.Tendsto u (𝓝 p) (𝓝 0) := by
    have h : Filter.Tendsto u (𝓝 p) (𝓝 (u p)) := hcont.continuousAt (hVo.mem_nhds hpV)
    rwa [hup] at h
  have h2 : ∀ᶠ x in 𝓝 p, u x < m * (ε / 2) :=
    hulim.eventually (isOpen_Iio.mem_nhds (mul_pos hm0 (by linarith)))
  have h3 : ∀ᶠ x in 𝓝 p, x ∈ Work.SimplyConnected.ABS.chartBallC c a ρ :=
    (chartBallC_isOpen c a ρ).mem_nhds hpc
  refine ⟨{x | Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ x < ε / 2} ∩
      {x | u x < m * (ε / 2)} ∩ Work.SimplyConnected.ABS.chartBallC c a ρ,
    Filter.inter_mem (Filter.inter_mem h1 h2) h3, ?_⟩
  rintro x ⟨hxΩ, ⟨hx1, hx2⟩, hx3⟩
  have hxbC : x ∈ Work.SimplyConnected.ABS.chartBallC c a ρ := hx3
  have hxb : x ∈ Submission.chartBall c a ρ := by rwa [chartBallC_eq_chartBall] at hxbC
  rw [bStepFn_of_mem_ball hxΩ hxb, bStar_apply]
  have hmin : min (u x / m) 1 < ε / 2 := by
    have hle : min (u x / m) 1 ≤ u x / m := min_le_left _ _
    have hdiv : u x / m < ε / 2 := by
      rw [div_lt_iff₀ hm0]
      simpa [mul_comm] using hx2
    linarith
  have hx1' : Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ x < ε / 2 := by simpa using hx1
  have hneg : -ε < -(min (u x / m) 1) +
      -(Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ x) := by
    linarith
  exact lt_of_lt_of_le hneg (le_max_left _ _)

/-- **The Bouligand step.**  For every radius `ρ'` and every `ε > 0` there is a subharmonic `b ≤ 0`
on `Ω`, strictly negative on `Ω`, equal to `-1` off `Ω` and off the chart ball of radius `ρ'`
around `p`, and `> -ε` near `p` along `Ω`. -/
theorem exists_bouligandStep {p : X} (hΩo : IsOpen Ω) (hVo : IsOpen V) (hpV : p ∈ V)
    (hsup : Submission.SuperharmonicOnX u (Ω ∩ V)) (hpos : ∀ x ∈ Ω ∩ V, 0 < u x)
    (hcont : ContinuousOn u V) (hup : u p = 0) {ρ' ε : ℝ} (hρ' : 0 < ρ') (hε : 0 < ε) :
    ∃ b : X → ℝ, Submission.SubharmonicOnX b Ω ∧ (∀ x ∈ Ω, b x < 0) ∧
      (∀ x : X, x ∉ Ω → b x = -1) ∧
      (∀ x ∈ Ω, x ∉ Submission.chartBall (chartAt ℂ p) ((chartAt ℂ p) p) ρ' → b x = -1) ∧
      (∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, -ε < b x) := by
  classical
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let a : ℂ := c p
  obtain ⟨ρ₂, hρ₂, htgt₂, hV₂⟩ := exists_chartClosedBall_subset_nhds (p := p) hVo hpV
  have htgt₂' : Metric.closedBall a ρ₂ ⊆ c.target := htgt₂
  have hV₂' : Submission.chartClosedBall c a ρ₂ ⊆ V := hV₂
  set ρ : ℝ := min (ρ₂ / 2) ρ' with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) hρ'
  have hρρ₂ : ρ ≤ ρ₂ := le_trans (min_le_left _ _) (by linarith)
  have hρρ' : ρ ≤ ρ' := min_le_right _ _
  have htgt : Metric.closedBall a ρ ⊆ c.target :=
    (Metric.closedBall_subset_closedBall hρρ₂).trans htgt₂'
  have hballV : Work.SimplyConnected.ABS.chartBallC c a ρ ⊆ V :=
    (chartBallC_subset_chartClosedBall.trans (chartClosedBall_mono hρρ₂)).trans hV₂'
  have hVprop : ∀ w : ℂ, w ∈ Metric.sphere (0 : ℂ) 1 → c.symm (a + ρ * w) ∈ V := by
    intro w hw
    have hwn : ‖w‖ = 1 := by simpa using (Metric.mem_sphere.mp hw)
    have hmem : a + ρ * w ∈ Metric.closedBall a ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hρ, hwn, mul_one]
    have hsrc : c.symm (a + ρ * w) ∈ c.source := c.map_target (htgt hmem)
    have hcl : c.symm (a + ρ * w) ∈ Submission.chartClosedBall c a ρ₂ := by
      refine ⟨hsrc, ?_⟩
      show c (c.symm (a + ρ * w)) ∈ Metric.closedBall a ρ₂
      rw [c.right_inv (htgt hmem)]
      exact Metric.closedBall_subset_closedBall hρρ₂ hmem
    exact hV₂' hcl
  obtain ⟨δ, hδpos, hδlt⟩ := Work.SimplyConnected.ABS.exists_bouligandDatum_circleAverage_lt
    (Ω := Ω) (V := V) (u := u) (c := c) (a := a) (ρ := ρ) hΩo hcont hρ htgt hVprop
    (fun x hx hxV => hpos x ⟨hx, hxV⟩) (ε / 2) (by linarith)
  set m : ℝ := δ / 2 with hmdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  have hmδ : m < δ := by rw [hmdef]; linarith
  have hglue_nn : ∀ x ∈ Work.SimplyConnected.ABS.chartBallC c a ρ,
      0 ≤ Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ x :=
    harmonicGlue_nonneg (Ω := Ω) (V := V) (u := u) (c := c) (a := a) (ρ := ρ) (δ := δ)
      hΩo hVo hcont hρ htgt hVprop
  have hg : CircleIntegrable (fun z : ℂ =>
      (Work.SimplyConnected.ABS.bouligandDatum Ω u c a ρ δ z : ℂ)) 0 1 :=
    Work.SimplyConnected.ABS.circleIntegrable_bouligandDatum (Ω := Ω) (V := V) (u := u) (c := c)
      (a := a) (ρ := ρ) (m := δ) hΩo hVo hcont hρ htgt hVprop
  have hglue_harm : Submission.HarmonicOnX (Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ)
      (Work.SimplyConnected.ABS.chartBallC c a ρ) :=
    harmonicOnX_harmonicGlue (p := p) (Ω := Ω) (u := u) (ρ := ρ) (δ := δ) hρ htgt hg
  have hmono : Submission.SuperharmonicOnX (fun y : X => u y / m) (Ω ∩ V) := by
    have hsc := subharmonicOnX_const_mul_local (k := 1 / m) (le_of_lt (one_div_pos.mpr hm0))
      (u := fun y : X => -u y) hsup.neg
    convert hsc.neg using 1
    funext y
    ring
  have hpos' : ∀ x ∈ Ω, x ∈ V → 0 < u x := fun x hx hxV => hpos x ⟨hx, hxV⟩
  have hbstar := subharmonicOnX_bStar (Ω := Ω) (V := V) (c := c) (a := a) (ρ := ρ) (δ := δ)
    (m := m) (u := u) hm0 hmono hglue_harm hballV
  have hcollar : ∀ x ∈ Ω, x ∈ closure (Submission.chartBall c a ρ) →
      x ∉ Submission.chartBall c a ρ → bStepFn Ω u c a ρ δ m =ᶠ[𝓝 x] fun _ => -1 :=
    fun x hx hxcl hxnb => bStepFn_eventually_neg_one_of_mem_collar (Ω := Ω) (V := V) (c := c)
      (a := a) (ρ := ρ) (δ := δ) (m := m) (u := u) hx hxcl hxnb hΩo hVo hcont hρ hm0 hmδ hpos'
      htgt hVprop
  have hsub := subharmonicOnX_bStepFn (Ω := Ω) (c := c) (a := a) (ρ := ρ) (δ := δ)
    (m := m) (u := u) hΩo hbstar hcollar
  have hneg := bStepFn_neg (Ω := Ω) (V := V) (c := c) (a := a) (ρ := ρ) (δ := δ) (m := m)
    (u := u) hm0 hballV hpos' hglue_nn
  have hpc : p ∈ Work.SimplyConnected.ABS.chartBallC c a ρ := by
    refine ⟨mem_chart_source ℂ p, ?_⟩
    show ‖c p - a‖ < ρ
    rw [show c p = a from rfl, sub_self, norm_zero]
    exact hρ
  have hglue_cont : ContinuousAt (Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ) p :=
    (hglue_harm p hpc).continuousAt
  have hglue_small : Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ p < ε / 2 := by
    have h0 : Work.SimplyConnected.ABS.harmonicGlue Ω u c a ρ δ p =
        Real.circleAverage (fun w : ℂ =>
          Work.SimplyConnected.ABS.bouligandDatum Ω u c a ρ δ w) 0 1 := by
      simp only [Work.SimplyConnected.ABS.harmonicGlue]
      have hz : (c p - a) / ρ = 0 := by
        rw [show c p = a from rfl, sub_self, zero_div]
      rw [hz, poissonInt_apply_zero' one_pos]
    rw [h0]
    exact hδlt
  obtain ⟨N, hN, hNsub⟩ := bStepFn_decay (Ω := Ω) (V := V) (c := c) (a := a) (ρ := ρ)
    (δ := δ) (m := m) (u := u) (p := p) hε hm0 hpc hVo hpV hcont hup hglue_cont hglue_small
  refine ⟨bStepFn Ω u c a ρ δ m, hsub, hneg, ?_, ?_, ⟨N, hN, hNsub⟩⟩
  · intro x hxΩ
    exact bStepFn_of_not_mem_Ω hxΩ
  · intro x hxΩ hxρ'
    refine bStepFn_eq_neg_one_of_not_mem_ball (fun hxb => hxρ' ?_)
    exact chartBall_mono (c := c) (a := a) hρρ' hxb

end StepFn

/-! ## Coherence: from a step at every scale to a single coherent barrier

The Bouligand step produces, for every radius `ρ'` and every `ε > 0`, a subharmonic `b ≤ 0` on `Ω`
which is `-1` off `Ω` and off the chart ball of radius `ρ'`, and `> -ε` near `p`.  Taking the
running maxima of the steps at the scales `ρ/(n+2)` and the tolerances `1/(n+2)`, the pointwise
supremum is again subharmonic: near any given point of `Ω` only *finitely many* of the steps differ
from `-1` (the chart balls shrink to `p`), so the supremum agrees locally with a finite maximum.
It inherits the exact decay `b → 0` at `p` from the individual steps. -/

section Coherence

variable {Ω : Set X} {p : X} {c : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ}

/-- `runningMax f n = max (-1, f 0, …, f (n-1))`. -/
noncomputable def runningMax (f : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => fun _ => -1
  | n + 1 => fun x => max (runningMax f n x) (f n x)

@[simp] theorem runningMax_zero (f : ℕ → X → ℝ) : runningMax f 0 = fun _ => (-1 : ℝ) := rfl

theorem runningMax_succ (f : ℕ → X → ℝ) (n : ℕ) :
    runningMax f (n + 1) = fun x => max (runningMax f n x) (f n x) := rfl

theorem runningMax_le_succ (f : ℕ → X → ℝ) (n : ℕ) (x : X) :
    runningMax f n x ≤ runningMax f (n + 1) x := by
  rw [runningMax_succ]
  exact le_max_left _ _

theorem runningMax_mono (f : ℕ → X → ℝ) : Monotone (fun n => runningMax f n) := by
  intro n m hnm
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih => exact fun x => le_trans (ih x) (runningMax_le_succ f j x)

theorem runningMax_lower (f : ℕ → X → ℝ) (n : ℕ) (x : X) : -1 ≤ runningMax f n x := by
  induction n with
  | zero => rw [runningMax_zero]
  | succ j ih => rw [runningMax_succ]; exact le_trans ih (le_max_left _ _)

theorem runningMax_nonpos (f : ℕ → X → ℝ) (hf : ∀ n x, f n x ≤ 0) (n : ℕ) (x : X) :
    runningMax f n x ≤ 0 := by
  induction n with
  | zero => rw [runningMax_zero]; norm_num
  | succ j ih => rw [runningMax_succ]; exact max_le ih (hf j x)

theorem runningMax_lt_zero (f : ℕ → X → ℝ) {x : X} :
    ∀ n : ℕ, (∀ m, m < n → f m x < 0) → runningMax f n x < 0 := by
  intro n
  induction n with
  | zero => intro _; rw [runningMax_zero]; norm_num
  | succ j ih =>
      intro h
      rw [runningMax_succ]
      exact max_lt (ih (fun m hm => h m (Nat.lt_succ_of_lt hm))) (h j (Nat.lt_succ_self j))

theorem runningMax_stabilize (f : ℕ → X → ℝ) {k : ℕ} {x : X}
    (h : ∀ m, k ≤ m → f m x = -1) : ∀ n, k ≤ n → runningMax f n x = runningMax f k x := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
      rw [runningMax_succ]
      show max (runningMax f j x) (f j x) = runningMax f k x
      rw [ih, h j hj]
      exact max_eq_left (runningMax_lower f k x)

/-- **Coherence.**  A Bouligand step at every scale produces a single subharmonic barrier `b < 0`
on `Ω` that tends to `0` at `p`. -/
theorem exists_coherent_of_steps (hρ : 0 < ρ) (ha : a = c p) (hpsrc : p ∈ c.source)
    (hpΩ : p ∉ Ω) (htgt : Metric.closedBall a ρ ⊆ c.target)
    (hstep : ∀ ρ' ε : ℝ, 0 < ρ' → 0 < ε → ∃ b : X → ℝ,
      Submission.SubharmonicOnX b Ω ∧ (∀ x ∈ Ω, b x < 0) ∧ (∀ x : X, x ∉ Ω → b x = -1) ∧
      (∀ x ∈ Ω, x ∉ Submission.chartBall c a ρ' → b x = -1) ∧
      (∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, -ε < b x)) :
    ∃ b : X → ℝ, Submission.SubharmonicOnX b Ω ∧ (∀ x ∈ Ω, b x < 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, -ε < b x) := by
  classical
  have hstep' : ∀ n : ℕ, ∃ b : X → ℝ, Submission.SubharmonicOnX b Ω ∧
      (∀ x ∈ Ω, b x < 0) ∧ (∀ x : X, x ∉ Ω → b x = -1) ∧
      (∀ x ∈ Ω, x ∉ Submission.chartBall c a (ρ / ((n : ℝ) + 2)) → b x = -1) ∧
      (∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, -(1 / ((n : ℝ) + 2)) < b x) :=
    fun n => hstep (ρ / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 2)) (by positivity) (by positivity)
  choose f hf using hstep'
  have hfsub : ∀ n, Submission.SubharmonicOnX (f n) Ω := fun n => (hf n).1
  have hfneg : ∀ n, ∀ x ∈ Ω, f n x < 0 := fun n => (hf n).2.1
  have hfoutΩ : ∀ n, ∀ x : X, x ∉ Ω → f n x = -1 := fun n => (hf n).2.2.1
  have hfout : ∀ n : ℕ, ∀ x ∈ Ω, x ∉ Submission.chartBall c a (ρ / ((n : ℝ) + 2)) →
      f n x = -1 := fun n => (hf n).2.2.2.1
  have hfnear : ∀ n : ℕ, ∃ N : Set X, N ∈ nhds p ∧
      ∀ x ∈ Ω ∩ N, -(1 / ((n : ℝ) + 2)) < f n x := fun n => (hf n).2.2.2.2
  have hMsub : ∀ n, Submission.SubharmonicOnX (runningMax f n) Ω := by
    intro n
    induction n with
    | zero => rw [runningMax_zero]; exact subharmonicOnX_const_local (-1) Ω
    | succ j ih => rw [runningMax_succ]; exact ih.sup (hfsub j)
  have hfnonpos : ∀ n x, f n x ≤ 0 := by
    intro n x
    by_cases hx : x ∈ Ω
    · exact le_of_lt (hfneg n x hx)
    · rw [hfoutΩ n x hx]; norm_num
  have hMnonpos : ∀ n x, runningMax f n x ≤ 0 := fun n x => runningMax_nonpos f hfnonpos n x
  set B : X → ℝ := fun x => sSup (Set.range fun n => runningMax f n x) with hB
  have hBdd : ∀ x : X, BddAbove (Set.range fun n => runningMax f n x) := fun x =>
    ⟨0, by rintro _ ⟨n, rfl⟩; exact hMnonpos n x⟩
  -- locally only finitely many of the steps differ from `-1`
  have hloc : ∀ x ∈ Ω, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ N : ℕ,
      ∀ n, N ≤ n → ∀ y ∈ U, f n y = -1 := by
    intro x hx
    have hxp : x ≠ p := fun h => hpΩ (h ▸ hx)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, x ∉ Submission.chartClosedBall c a (ρ / ((N : ℝ) + 2)) := by
      by_cases hxs : x ∈ c.source
      · have hne : c x ≠ a := by
          intro h
          exact hxp (c.injOn hxs hpsrc (h.trans ha))
        have hnorm : 0 < ‖c x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        obtain ⟨n, hn⟩ := exists_nat_gt (ρ / ‖c x - a‖)
        refine ⟨n, fun hmem => ?_⟩
        have hle : ‖c x - a‖ ≤ ρ / ((n : ℝ) + 2) := by
          have h := Metric.mem_closedBall.mp hmem.2
          simpa [dist_eq_norm] using h
        have h2 : ρ / ‖c x - a‖ < (n : ℝ) + 2 :=
          lt_of_lt_of_le hn (by push_cast; linarith)
        rw [div_lt_iff₀ hnorm] at h2
        have h3 : ρ / ((n : ℝ) + 2) < ‖c x - a‖ := by
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2), mul_comm]
          exact h2
        linarith
      · exact ⟨0, fun hmem => hxs hmem.1⟩
    have hNle : ρ / ((N : ℝ) + 2) ≤ ρ := by
      have hc : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 2)]
      nlinarith [hρ, hc]
    refine ⟨(Submission.chartClosedBall c a (ρ / ((N : ℝ) + 2)))ᶜ, ?_, hN, ?_⟩
    · exact (Submission.isClosed_chartClosedBall
        ((Metric.closedBall_subset_closedBall hNle).trans htgt)).isOpen_compl
    · refine ⟨N, fun n hn y hy => ?_⟩
      by_cases hyΩ : y ∈ Ω
      · refine hfout n y hyΩ ?_
        intro hyb
        have h1 : ρ / ((n : ℝ) + 2) ≤ ρ / ((N : ℝ) + 2) := by
          have hNn : (N : ℝ) + 2 ≤ (n : ℝ) + 2 := by
            have hc : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
            linarith
          exact div_le_div_of_nonneg_left hρ.le (by positivity) hNn
        exact hy (chartClosedBall_mono h1 (chartBall_subset_chartClosedBall hyb))
      · exact hfoutΩ n y hyΩ
  have hAtB : ∀ x ∈ Ω, Submission.SubharmonicOnXAt B x := by
    intro x hx
    obtain ⟨U, hUo, hxU, N, hUN⟩ := hloc x hx
    have hev : B =ᶠ[𝓝 x] runningMax f N := by
      refine Filter.eventually_of_mem (hUo.mem_nhds hxU) fun y hy => ?_
      refine le_antisymm (csSup_le ⟨runningMax f 0 y, Set.mem_range_self 0⟩ ?_)
        (le_csSup (hBdd y) (Set.mem_range_self N))
      rintro _ ⟨n, rfl⟩
      rcases le_total n N with h | h
      · exact runningMax_mono f h y
      · exact le_of_eq (runningMax_stabilize f (fun m hm => hUN m hm y hy) n h)
    exact ((hMsub N).2 x hx).congr hev.symm
  have hBneg : ∀ x ∈ Ω, B x < 0 := by
    intro x hx
    obtain ⟨U, hUo, hxU, N, hUN⟩ := hloc x hx
    have heq : B x = runningMax f N x := by
      refine le_antisymm (csSup_le ⟨runningMax f 0 x, Set.mem_range_self 0⟩ ?_)
        (le_csSup (hBdd x) (Set.mem_range_self N))
      rintro _ ⟨n, rfl⟩
      rcases le_total n N with h | h
      · exact runningMax_mono f h x
      · exact le_of_eq (runningMax_stabilize f (fun m hm => hUN m hm x hxU) n h)
    rw [heq]
    refine runningMax_lt_zero f N fun m hm => hfneg m x hx
  refine ⟨B, ⟨?_, hAtB⟩, hBneg, ?_⟩
  · exact continuousOn_of_forall_continuousAt (fun x hx => (hAtB x hx).continuousAt)
  · intro ε hε
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / ((n : ℝ) + 2) < ε := by
      obtain ⟨n, hn⟩ := exists_nat_gt ε⁻¹
      refine ⟨n, ?_⟩
      have h2 : 1 < ((n : ℝ) + 2) * ε := by
        have h3 : (1 : ℝ) / ε < (n : ℝ) + 2 := by
          rw [one_div]
          linarith
        have := (div_lt_iff₀ hε).mp h3
        linarith
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
      linarith
    obtain ⟨N, hN, hNsub⟩ := hfnear n
    refine ⟨N, hN, fun x hx => ?_⟩
    have h1 : -(1 / ((n : ℝ) + 2)) < f n x := hNsub x hx
    have h2 : f n x ≤ runningMax f (n + 1) x := by
      rw [runningMax_succ]; exact le_max_right _ _
    have h3 : runningMax f (n + 1) x ≤ B x := le_csSup (hBdd x) (Set.mem_range_self (n + 1))
    linarith

end Coherence

/-! ## The target -/

theorem coherentSubharmonicBarrier {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {Ω : Set X} (hΩo : IsOpen Ω) {p : X} (hp : p ∈ frontier Ω)
    {u : X → ℝ} {V : Set X} (hVo : IsOpen V) (hpV : p ∈ V)
    (hsup : Submission.SuperharmonicOnX u (Ω ∩ V)) (hpos : ∀ x ∈ Ω ∩ V, 0 < u x)
    (hcont : ContinuousOn u V) (hup : u p = 0) :
    ∃ b : X → ℝ, Submission.SubharmonicOnX b Ω ∧ (∀ x ∈ Ω, b x < 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : Set X, N ∈ nhds p ∧ ∀ x ∈ Ω ∩ N, -ε < b x) := by
  classical
  obtain ⟨ρ₂, hρ₂, htgt₂, hV₂⟩ := exists_chartClosedBall_subset_nhds (p := p) hVo hpV
  have hpΩ : p ∉ Ω := by
    have h2 := hp
    rw [frontier, hΩo.interior_eq] at h2
    exact h2.2
  refine exists_coherent_of_steps (Ω := Ω) (p := p) (c := chartAt ℂ p)
    (a := (chartAt ℂ p) p) (ρ := ρ₂) hρ₂ rfl (mem_chart_source ℂ p) hpΩ ?_ ?_
  · exact htgt₂
  · intro ρ' ε hρ' hε
    exact exists_bouligandStep (p := p) hΩo hVo hpV hsup hpos hcont hup hρ' hε

end Work.SimplyConnected.ABS.RegBouligand
