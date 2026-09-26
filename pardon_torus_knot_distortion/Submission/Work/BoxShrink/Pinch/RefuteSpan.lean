import Submission.Work.BoxShrink.Pinch.Transport
import Submission.Work.BoxShrink.Pinch.winding_zero_of_lift_sin

/-!
# The span form of the residual is false: the halves of Pardon's pinch realise only a line

This module records an unconditional counterexample to the *span* form of the residual of the area,
i.e. to

  `WindingSpan P (boxRegion P s c σ) ≤ WindingSpan P (upperRegion P s c σ u ∪ lowerRegion P s c σ u)`

at the standard torus of revolution with `s = 9/5`, `c = 0`, `σ = swap 1 2`, `u = 0`.  There

* `meridianCurve_mem_boxRegion` — the curve `θ ↦ (cos θ, sin θ, 0)` (the curve of the parametrised
  inner equator, `Work.CoreTopology.longitudeCurve standard π`) lies in the region inside the box, and
  has winding vector `(1, 0)`; hence `(1, 0)` is realised in the box region;
* `fst_eq_zero_of_mem_halves_windingSpan` — **every** winding vector realised in either
  half-region has vanishing *first* coordinate, because a point of the upper half-region has
  `y = (2 + cos φ) sin θ > 0`, so `sin θ > 0` along every loop of that half, so the longitude
  parameter of its lift never leaves a window of length `π` (`eq_zero_of_cont_sin_pos`); the lower
  half is the same with the sign reversed;

so the span of the two half-regions is contained in the line `ℚ·(0,1)`, while that of the region
inside the box contains `(1,0)`: the inequality fails.  Consequently the per-loop transport form
`Work.BoxShrink.Pinch.RegionTransport` (which implies the inequality) fails as well, and so does
`Work.BoxShrink.Bubble.SlicePushOff`, of which it is the loop-level restatement
(`regionTransport_iff_slicePushOff`).

The numerical study in `EXP/` locates the configuration (`s = 1.8 = 9/5`), checks it against the two
published facts at `s = 3/2`, and shows that the `+1` dimension bound `PinchNoJump` and the
conclusion `BubbleHalf` are unaffected (they hold in every sampled configuration).  It also finds
the same failure with the *plane* trace inessential (a sheared torus, `s ≈ 1.6`), so restricting to
`W(planeTrace) = ⊥` does not rescue the span form: the residual must be the `+1` bound or
`BubbleHalf`.

The hypotheses of the *conclusion* of Pardon's Lemma 3 are therefore what has to be used: the trace
of the sphere and the slice are both inessential at every configuration where the residual is stated,
and at this configuration the sphere trace is inessential (numerically verified, not proved here)
while the halves realise only a line.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-- The standard configuration of this module: the standard torus of revolution, the box of size
`9/5`, centre `0`, permutation `swap 1 2`, and the plane `y = 0`. -/
abbrev s18 : ℝ := 9 / 5

theorem s18_pos : (0 : ℝ) < s18 := by norm_num [s18]

/-! ## The box norm at the standard configuration -/

theorem std_boxNorm_s18 (y : R3) : Submission.boxNorm 0 (Equiv.swap 1 2) y =
    max (max |y.ofLp 0| (|y.ofLp 2| / (2 : ℝ) ^ (1 / 3 : ℝ)))
      (|y.ofLp 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) := by
  unfold Submission.boxNorm
  simp [Equiv.swap_apply_def, Submission.boxSide]

/-! ## The inner equator lies in the region inside the box and realises `(1,0)` -/

/-- The parametrised inner equator `θ ↦ (cos θ, sin θ, 0)`, as a closed curve of the standard
torus. -/
theorem longitudeCurve_pi_apply (θ : ℝ) :
    (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi) θ =
      Work.Core.torusMap θ Real.pi := rfl

/-- **The inner equator lies in the region inside the box** at the standard configuration with
`s = 9/5`: its box norm is `max (|cos θ|, |sin θ| / 2^{2/3}) ≤ 1 < 9/5`. -/
theorem longitudeCurve_mem_boxRegion (θ : ℝ) :
    (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi) θ ∈
      Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) := by
  rw [Work.BoxShrink.Core.mem_boxRegion, Submission.mem_PBox_iff]
  refine ⟨?_, ?_⟩
  · exact Set.mem_range.mpr ⟨(θ, Real.pi), rfl⟩
  · show Submission.boxNorm 0 (Equiv.swap 1 2) (Work.Core.torusMap θ Real.pi) < s18
    have hcs : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have hsn : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have h2gt : (1 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    have hs : s18 = 9 / 5 := rfl
    rw [std_boxNorm_s18, torusMap_apply_zero, torusMap_apply_one, torusMap_apply_two,
      Real.cos_pi, Real.sin_pi]
    have h1 : |Real.cos θ| < (9 : ℝ) / 5 := by nlinarith
    have h2 : |Real.sin θ| / (2 : ℝ) ^ (2 / 3 : ℝ) < (9 : ℝ) / 5 := by
      rw [div_lt_iff₀ h2pos]; nlinarith
    norm_num
    exact ⟨h1, h2⟩

/-- The inner equator's winding vector is `(1,0)`. -/
theorem longitudeCurve_pi_winding :
    Work.SurgeryInvariance.windingOf Work.CoreTopology.standard
      (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi) = (1, 0) :=
  (Work.SurgeryInvariance.windingOf_eq Work.CoreTopology.standard
    (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi)
      (Work.CoreTopology.longitudeLift Work.CoreTopology.standard Real.pi)).trans
    (Work.CoreTopology.longitudeLift_winding Work.CoreTopology.standard Real.pi)

theorem longitudeCurve_pi_fst_winding :
    (Work.SurgeryInvariance.windingOf Work.CoreTopology.standard
      (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi)).1 = 1 := by
  rw [longitudeCurve_pi_winding]

/-- Hence `(1,0)` is realised in the region inside the box. -/
theorem oneZero_mem_boxRegion_windingSpan :
    (((1 : ℤ) : ℚ), ((0 : ℤ) : ℚ)) ∈ Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2)) := by
  apply Submodule.subset_span
  refine ⟨_, longitudeCurve_mem_boxRegion, ?_⟩
  rw [longitudeCurve_pi_winding]

/-! ## Every winding vector realised in a half-region has vanishing first coordinate -/

/-- **A loop of the upper half-region has vanishing first winding.**  A point of the upper
half-region has `y = (2 + cos φ) sin θ > 0`, so along a lift `(Θ, Φ)` of such a loop `sin (Θ t) > 0`
for all `t`; the longitude parameter therefore never leaves a window of length `π`, so its advance
over a period — an integer multiple of `2π` — vanishes (`eq_zero_of_cont_sin_pos`). -/
theorem fst_winding_eq_zero_of_mem_upperRegion {γ : Work.CoreTopology.ClosedCurve
    Work.CoreTopology.standard}
    (hγ : ∀ t : ℝ, γ t ∈
      Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) 0) :
    (Work.SurgeryInvariance.windingOf Work.CoreTopology.standard γ).1 = 0 := by
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf Work.CoreTopology.standard γ
  have hsin : ∀ t : ℝ, 0 < Real.sin (L.Θ t) := by
    intro t
    have hpos : 0 < (γ t).ofLp 1 := by
      have h := (Work.BoxShrink.Core.mem_upperRegion.mp (hγ t)).2.2
      simpa [Work.BoxShrink.Core.upperHalf, Equiv.swap_apply_def, WithLp.ofLp_toLp] using h
    have hval : (γ t).ofLp 1 = (2 + Real.cos (L.Φ t)) * Real.sin (L.Θ t) := by
      rw [← L.lifts t, standard_psi, torusMap_apply_one]
    rw [hval] at hpos
    have h2 : 0 < 2 + Real.cos (L.Φ t) := by linarith [Real.neg_one_le_cos (L.Φ t)]
    nlinarith
  have hspec := L.winding_spec
  have hm : (L.winding).1 = 0 :=
    eq_zero_of_cont_sin_pos L.contΘ hsin (by rw [hspec.1]; ring)
  rw [Work.SurgeryInvariance.windingOf_eq Work.CoreTopology.standard γ L, hm]

/-- **A loop of the lower half-region has vanishing first winding** (the same argument, with the
sign reversed: `y < 0` gives `sin (Θ t) < 0`, and the argument is applied to `-Θ`). -/
theorem fst_winding_eq_zero_of_mem_lowerRegion {γ : Work.CoreTopology.ClosedCurve
    Work.CoreTopology.standard}
    (hγ : ∀ t : ℝ, γ t ∈
      Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) 0) :
    (Work.SurgeryInvariance.windingOf Work.CoreTopology.standard γ).1 = 0 := by
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf Work.CoreTopology.standard γ
  have hsin : ∀ t : ℝ, 0 < Real.sin (-(L.Θ t)) := by
    intro t
    have hneg : (γ t).ofLp 1 < 0 := by
      have h := (Work.BoxShrink.Core.mem_lowerRegion.mp (hγ t)).2.2
      simpa [Work.BoxShrink.Core.lowerHalf, Equiv.swap_apply_def, WithLp.ofLp_toLp] using h
    have hval : (γ t).ofLp 1 = (2 + Real.cos (L.Φ t)) * Real.sin (L.Θ t) := by
      rw [← L.lifts t, standard_psi, torusMap_apply_one]
    rw [hval] at hneg
    have h2 : 0 < 2 + Real.cos (L.Φ t) := by linarith [Real.neg_one_le_cos (L.Φ t)]
    have h3 : Real.sin (L.Θ t) < 0 := by nlinarith
    simpa using neg_pos.mpr h3
  have hspec := L.winding_spec
  have hdiff : (-L.Θ) (2 * Real.pi) - (-L.Θ) 0 = ((-(L.winding).1 : ℤ) : ℝ) * (2 * Real.pi) := by
    simp only [Pi.neg_apply]
    rw [hspec.1]; push_cast; ring
  have hm : -(L.winding).1 = 0 :=
    eq_zero_of_cont_sin_pos (L.contΘ.neg) hsin hdiff
  rw [Work.SurgeryInvariance.windingOf_eq Work.CoreTopology.standard γ L]
  omega

/-- **The first coordinate vanishes on the whole winding span of the upper half-region.** -/
theorem fst_eq_zero_of_mem_windingSpan_upper {v : ℚ × ℚ}
    (hv : v ∈ Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) 0)) :
    v.1 = 0 := by
  have hle : Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) 0) ≤
      LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) := by
    rw [Work.SurgeryInvariance.WindingSpan]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨γ, hγ, rfl⟩
    exact LinearMap.mem_ker.mpr (by simpa using fst_winding_eq_zero_of_mem_upperRegion hγ)
  exact hle hv

/-- The same for the lower half-region. -/
theorem fst_eq_zero_of_mem_windingSpan_lower {v : ℚ × ℚ}
    (hv : v ∈ Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) 0)) :
    v.1 = 0 := by
  have hle : Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) 0) ≤
      LinearMap.ker (LinearMap.fst ℚ ℚ ℚ) := by
    rw [Work.SurgeryInvariance.WindingSpan]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨γ, hγ, rfl⟩
    exact LinearMap.mem_ker.mpr (by simpa using fst_winding_eq_zero_of_mem_lowerRegion hγ)
  exact hle hv

/-- **The span of the two half-regions lies in the line `ℚ·(0,1)`.** -/
theorem fst_eq_zero_of_mem_windingSpan_halves {v : ℚ × ℚ}
    (hv : v ∈ Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
      (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) 0 ∪
        Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) 0)) :
    v.1 = 0 := by
  rw [Work.SurgeryInvariance.Span.union_eq_sup
      (Work.BoxShrink.Core.isOpenInCarrier_upperRegion Work.CoreTopology.standard s18 0
        (Equiv.swap 1 2) 0)
      (Work.BoxShrink.Core.isOpenInCarrier_lowerRegion Work.CoreTopology.standard s18 0
        (Equiv.swap 1 2) 0)
      (Work.BoxShrink.Core.disjoint_upperRegion_lowerRegion Work.CoreTopology.standard s18 0
        (Equiv.swap 1 2) 0)] at hv
  rcases Submodule.mem_sup.mp hv with ⟨a, ha, b, hb, hab⟩
  rw [← hab]
  simp only [Prod.fst_add]
  rw [fst_eq_zero_of_mem_windingSpan_upper ha, fst_eq_zero_of_mem_windingSpan_lower hb, add_zero]

/-! ## The span inequality fails -/

/-- **The span form of the residual is false at the standard configuration with `s = 9/5`**: the
region inside the box realises `(1,0)` (the inner equator) while the union of the two half-regions
realises only classes with vanishing first coordinate. -/
theorem not_windingSpan_le_halves_standard :
    ¬ (Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2)) ≤
      Work.SurgeryInvariance.WindingSpan Work.CoreTopology.standard
        (Work.BoxShrink.Core.upperRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) 0 ∪
          Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) 0)) := by
  intro hle
  have h1 := hle oneZero_mem_boxRegion_windingSpan
  have h2 := fst_eq_zero_of_mem_windingSpan_halves h1
  norm_num at h2

/-- **The transport form of the push-off is false at the same configuration** (it implies the span
inequality). -/
theorem not_regionTransport_standard :
    ¬ RegionTransport Work.CoreTopology.standard s18 0 (Equiv.swap 1 2) 0 := fun h =>
  not_windingSpan_le_halves_standard (le_of_eq (windingSpan_eq_of_regionTransport h))


end

end Work.BoxShrink.Pinch
