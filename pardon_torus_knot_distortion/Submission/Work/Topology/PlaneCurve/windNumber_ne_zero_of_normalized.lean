import Mathlib
import Submission.Work.Topology.PlaneCurve.jordanRectSetup
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.atMostTwoNormalized
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic
import Submission.Work.Smooth.SphereJordan.shiftWitness
import Submission.Work.Topology.PlaneCurve.exists_bounded_component_of_rectSetup
import Submission.Work.Topology.PlaneCurve.CruxBoundedComponentClean

namespace Work.Topology.PlaneCurve

open Set

noncomputable section

/-!
# The winding number of the normalised explicit plane curve is non-zero

`γ : ℝ → ℂ` is continuous, `2π`-periodic, injective on `[0,2π)`, passes through `-1` and `1`,
and is otherwise contained in the rectangle `rectR = (-1,1) × (-2,2)`.

Maehara's free-window configuration (`Work.Smooth.SphereJordan.exists_windowConfig`) provides a
non-empty interval of the vertical segment `vSeg` which is free of the trace, together with the
arcs of the trace that separate it from the two "clusters" of crossings of the imaginary axis.
The present file records the elementary consequences of that configuration, which the proof of
the target needs:

* `window_midpoint_spec` — the window provides a point of `vSeg` off the trace;
* `window_crossings_confined` — all crossings of the imaginary axis by the trace lie in the two
  clusters `[j.im,k.im]` and `[m.im,l.im]`.

The target itself is proved from these.
-/

/-- **The free window of Maehara's argument provides a point of the vertical segment `vSeg` which
lies off the trace of `γ`.** -/
theorem window_midpoint_spec {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hsub : ∀ w ∈ Set.range γ, w ∈ rectR ∨ w = -1 ∨ w = 1)
    (hzero : γ 0 = -1) (hpos : 1 ∈ Set.range γ) :
    ∃ z : ℂ, z.re = 0 ∧ (∀ t : ℝ, γ t ≠ z) := by
  obtain ⟨l, m, k, j, δ₁, δ₂, hlJ, hmJ, hkJ, hjJ, hlSeg, hmSeg, hkSeg, hjSeg,
    hj2, hjk, hkm, hml, hl2, hwin, hjfree, hlfree, hδ₁J, hδ₁av, hδ₂J, hδ₂av⟩ :=
    Work.Smooth.SphereJordan.exists_windowConfig hγ hper hinj hsub hzero hpos
  refine ⟨⟨0, (k.im + m.im)/2⟩, rfl, ?_⟩
  have hzmem : (⟨0, (k.im + m.im)/2⟩ : ℂ) ∈ vSeg := by
    refine ⟨rfl, ?_, ?_⟩
    · have h1 : k.im < m.im := hkm
      have h2 : -2 < j.im := hj2
      have h3 : j.im ≤ k.im := hjk
      have hz : (⟨0, (k.im + m.im)/2⟩ : ℂ).im = (k.im + m.im)/2 := rfl
      rw [hz]; linarith
    · have h1 : k.im < m.im := hkm
      have h2 : m.im ≤ l.im := hml
      have h3 : l.im < 2 := hl2
      have hz : (⟨0, (k.im + m.im)/2⟩ : ℂ).im = (k.im + m.im)/2 := rfl
      rw [hz]; linarith
  have hz1 : k.im < (⟨0, (k.im + m.im)/2⟩ : ℂ).im := by
    have hz : (⟨0, (k.im + m.im)/2⟩ : ℂ).im = (k.im + m.im)/2 := rfl
    rw [hz]; linarith
  have hz2 : (⟨0, (k.im + m.im)/2⟩ : ℂ).im < m.im := by
    have hz : (⟨0, (k.im + m.im)/2⟩ : ℂ).im = (k.im + m.im)/2 := rfl
    rw [hz]; linarith
  intro t ht
  exact hwin _ hzmem hz1 hz2 ⟨t, ht⟩

/-- **The trace crosses the imaginary axis only inside the two clusters.**  This is the elementary
consequence of the freeness parts of the window configuration: the window `(k,m)` and the two rays
below `j` and above `l` are free of the trace. -/
theorem window_crossings_confined {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hsub : ∀ w ∈ Set.range γ, w ∈ rectR ∨ w = -1 ∨ w = 1)
    (hzero : γ 0 = -1) (hpos : 1 ∈ Set.range γ) :
    ∃ (j m k l : ℂ),
      j ∈ Set.range γ ∧ m ∈ Set.range γ ∧ k ∈ Set.range γ ∧ l ∈ Set.range γ ∧
      j ∈ vSeg ∧ m ∈ vSeg ∧ k ∈ vSeg ∧ l ∈ vSeg ∧
      j.im ≤ k.im ∧ k.im < m.im ∧ m.im ≤ l.im ∧
      (∀ t : ℝ, (γ t).re = 0 → (j.im ≤ (γ t).im ∧ (γ t).im ≤ k.im) ∨
        (m.im ≤ (γ t).im ∧ (γ t).im ≤ l.im)) := by
  obtain ⟨l, m, k, j, δ₁, δ₂, hlJ, hmJ, hkJ, hjJ, hlSeg, hmSeg, hkSeg, hjSeg,
    hj2, hjk, hkm, hml, hl2, hwin, hjfree, hlfree, hδ₁J, hδ₁av, hδ₂J, hδ₂av⟩ :=
    Work.Smooth.SphereJordan.exists_windowConfig hγ hper hinj hsub hzero hpos
  refine ⟨j, m, k, l, hjJ, hmJ, hkJ, hlJ, hjSeg, hmSeg, hkSeg, hlSeg, hjk, hkm, hml, ?_⟩
  intro t ht
  have hbox : γ t ∈ closedBox := range_subset_closedBox hsub ⟨t, rfl⟩
  have him2 : -2 ≤ (γ t).im ∧ (γ t).im ≤ 2 := abs_le.mp hbox.2
  have hmem : γ t ∈ vSeg := ⟨ht, him2.1, him2.2⟩
  rcases lt_or_ge (γ t).im j.im with h | h
  · exact absurd ⟨t, rfl⟩ (hjfree _ hmem h)
  rcases lt_or_ge k.im (γ t).im with h2 | h2
  · rcases lt_or_ge (γ t).im m.im with h3 | h3
    · exact absurd ⟨t, rfl⟩ (hwin _ hmem h2 h3)
    · exact Or.inr ⟨h3, le_of_not_gt (fun h4 => hlfree _ hmem h4 ⟨t, rfl⟩)⟩
  · exact Or.inl ⟨h, h2⟩

/-- The grid index of a value `x` with respect to the grid `v + 2πℤ`. -/
def gridIdx (v x : ℝ) : ℤ := ⌊(x - v) / (2 * Real.pi)⌋

theorem gridIdx_shift (v x : ℝ) (k : ℤ) :
    gridIdx v (x + 2 * Real.pi * k) = gridIdx v x + k := by
  unfold gridIdx
  have h : (x + 2 * Real.pi * (k : ℝ) - v) / (2 * Real.pi) = (x - v) / (2 * Real.pi) + (k : ℝ) := by
    field_simp; ring
  rw [h, Int.floor_add_intCast]

/-- If `x` is off the grid, a value within `2π` of a grid point is strictly between two
consecutive grid points. -/
theorem Ioo_of_abs_lt {v x : ℝ} {k : ℤ}
    (h : |x - (v + 2 * Real.pi * k)| < 2 * Real.pi) :
    (k : ℝ) - 1 < (x - v) / (2 * Real.pi) ∧ (x - v) / (2 * Real.pi) < (k : ℝ) + 1 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  constructor
  · rw [lt_div_iff₀ hπ]
    have : ((k:ℝ) - 1) * (2 * Real.pi) = 2 * Real.pi * k - 2 * Real.pi := by ring
    rw [this]; linarith
  · rw [div_lt_iff₀ hπ]
    have : ((k:ℝ) + 1) * (2 * Real.pi) = 2 * Real.pi * k + 2 * Real.pi := by ring
    rw [this]; linarith

theorem gridIdx_of_below {v x : ℝ} {k : ℤ}
    (h1 : (k : ℝ) - 1 < (x - v) / (2 * Real.pi)) (h2 : (x - v) / (2 * Real.pi) < (k : ℝ)) :
    gridIdx v x = k - 1 := by
  unfold gridIdx
  refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith

theorem gridIdx_of_above {v x : ℝ} {k : ℤ}
    (h1 : (k : ℝ) < (x - v) / (2 * Real.pi)) (h2 : (x - v) / (2 * Real.pi) < (k : ℝ) + 1) :
    gridIdx v x = k := by
  unfold gridIdx
  exact Int.floor_eq_iff.mpr ⟨le_of_lt h1, h2⟩


theorem div_lt_of_lt_zero {v x : ℝ} {k : ℤ} (h : x - (v + 2 * Real.pi * k) < 0) :
    (x - v) / (2 * Real.pi) < (k:ℝ) := by
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  rw [div_lt_iff₀ hπ]
  have : (k:ℝ) * (2 * Real.pi) = 2 * Real.pi * k := by ring
  linarith

theorem lt_div_of_gt_zero {v x : ℝ} {k : ℤ} (h : 0 < x - (v + 2 * Real.pi * k)) :
    (k:ℝ) < (x - v) / (2 * Real.pi) := by
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  rw [lt_div_iff₀ hπ]
  have : (k:ℝ) * (2 * Real.pi) = 2 * Real.pi * k := by ring
  linarith

/-- **At a clean crossing the grid index jumps by exactly one.** -/
theorem gridIdx_jump {v : ℝ} {f : ℝ → ℝ} {s : ℝ} {k : ℤ} {ε : ℝ} (hε : 0 < ε)
    (hδ : ∀ δ : ℝ, 0 < δ → δ < ε →
      |f (s - δ) - (v + 2 * Real.pi * k)| < 2 * Real.pi ∧
      |f (s + δ) - (v + 2 * Real.pi * k)| < 2 * Real.pi ∧
      (f (s - δ) - (v + 2 * Real.pi * k)) * (f (s + δ) - (v + 2 * Real.pi * k)) < 0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδε : δ < ε) :
    (gridIdx v (f (s - δ)) = k - 1 ∧ gridIdx v (f (s + δ)) = k) ∨
    (gridIdx v (f (s - δ)) = k ∧ gridIdx v (f (s + δ)) = k - 1) := by
  obtain ⟨h1, h2, h3⟩ := hδ δ hδ0 hδε
  have I1 := Ioo_of_abs_lt h1
  have I2 := Ioo_of_abs_lt h2
  rcases mul_neg_iff.mp h3 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · right
    exact ⟨gridIdx_of_above (lt_div_of_gt_zero ha) I1.2, gridIdx_of_below I2.1 (div_lt_of_lt_zero hb)⟩
  · left
    exact ⟨gridIdx_of_below I1.1 (div_lt_of_lt_zero ha), gridIdx_of_above (lt_div_of_gt_zero hb) I2.2⟩

/-- If `x` is off the grid, `gridIdx` is constant in a neighbourhood of `x`. -/
theorem gridIdx_eventually_const {v x : ℝ} (hx : ∀ k : ℤ, x ≠ v + 2 * Real.pi * k) :
    ∃ ε > 0, ∀ u : ℝ, |u - x| < ε → gridIdx v u = gridIdx v x := by
  set y : ℝ := (x - v) / (2 * Real.pi) with hy
  have hyZ : ∀ k : ℤ, y ≠ k := by
    intro k hk
    have h2 : x - v = 2 * Real.pi * (k:ℝ) := by
      have := congrArg (fun z => z * (2 * Real.pi)) hk
      rw [hy] at this
      field_simp at this
      linarith
    exact hx k (by linarith)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (k : ℝ) < y ∧ y < (k : ℝ) + 1 := by
    refine ⟨⌊y⌋, lt_of_le_of_ne (Int.floor_le y) (Ne.symm (hyZ ⌊y⌋)), ?_⟩
    simpa using Int.lt_floor_add_one y
  have hpos : 0 < min (y - k) (k + 1 - y) := lt_min (by linarith) (by linarith)
  refine ⟨min (y - k) (k + 1 - y) * (2 * Real.pi), by positivity, ?_⟩
  intro u hu
  have hu' : |(u - v) / (2 * Real.pi) - y| < min (y - k) (k + 1 - y) := by
    rw [hy]
    have h2 : (u - v) / (2 * Real.pi) - (x - v) / (2 * Real.pi) = (u - x) / (2 * Real.pi) := by ring
    rw [h2, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi), div_lt_iff₀ (by positivity)]
    linarith
  have h1 : (k : ℝ) < (u - v) / (2 * Real.pi) := by
    have := (abs_lt.mp hu').1
    have := min_le_left (y - k) (k + 1 - y)
    linarith
  have h2 : (u - v) / (2 * Real.pi) < (k : ℝ) + 1 := by
    have := (abs_lt.mp hu').2
    have := min_le_right (y - k) (k + 1 - y)
    linarith
  have hx0 : gridIdx v x = k := by
    unfold gridIdx
    rw [show (x - v) / (2 * Real.pi) = y from hy.symm]
    exact Int.floor_eq_iff.mpr ⟨hk.1.le, hk.2⟩
  have hu0 : gridIdx v u = k := by
    unfold gridIdx
    exact Int.floor_eq_iff.mpr ⟨h1.le, h2⟩
  rw [hx0, hu0]


/-! ## Auxiliary lemmas for the reduction to a non-zero winding number off the trace -/

/-- **Injectivity on one period excludes an internal shift.**  For `0 < θ < 2π` there is no `t`
with `γ t = γ (t + θ)`. -/
theorem periodic_ne_add {γ : ℝ → ℂ} (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ2 : θ < 2 * Real.pi) : ∀ t : ℝ, γ t ≠ γ (t + θ) := by
  intro t ht
  obtain ⟨k, hk⟩ := Work.Smooth.SphereJordan.exists_int_sub_eq_of_periodic_injOn hper hinj ht
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hk0 : k = 0 := by
    by_contra hkne
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hkne
    have h2 : θ = -(k : ℝ) * (2 * Real.pi) := by linarith
    have h3 : |θ| = |(k : ℝ)| * (2 * Real.pi) := by
      rw [h2, abs_mul, abs_neg, abs_of_pos hπ]
    have h4 : |θ| < 2 * Real.pi := by rw [abs_of_pos hθ0]; exact hθ2
    nlinarith
  rw [hk0] at hk
  simp only [Int.cast_zero, zero_mul] at hk
  linarith

/-- **The distance from the trace to a point off it is positive.** -/
theorem exists_pos_le_norm_sub {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) {z : ℂ} (hz : ∀ t : ℝ, γ t ≠ z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ε ≤ ‖γ t - z‖ := by
  have hK : IsCompact (Set.range γ) := isCompact_range_of_periodic hγ hper
  have hne : (Set.range γ).Nonempty := ⟨γ 0, 0, rfl⟩
  obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hne
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  refine ⟨‖w₀ - z‖, ?_, fun t => hmin ⟨t, rfl⟩⟩
  obtain ⟨t₀, ht₀⟩ := hw₀
  have hne' : w₀ ≠ z := fun h => hz t₀ (by rw [ht₀]; exact h)
  exact norm_pos_iff.mpr (sub_ne_zero.mpr hne')

/-- **The winding number is constant along complementary components.**  If `w` lies in the
connected component of `z` in the complement of the trace, the two winding numbers agree. -/
theorem windNumber_eq_of_mem_connectedComponentIn {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) {z w : ℂ} (hz : z ∉ Set.range γ)
    (hw : w ∈ connectedComponentIn (Set.range γ)ᶜ z) :
    Work.Smooth.SphereJordan.windNumber γ hγ z
      = Work.Smooth.SphereJordan.windNumber γ hγ w := by
  set U : Set ℂ := connectedComponentIn (Set.range γ)ᶜ z with hUdef
  have hzU : z ∈ U := mem_connectedComponentIn hz
  have hUcomp : U ⊆ (Set.range γ)ᶜ := connectedComponentIn_subset _ _
  have hloc : IsLocallyConstant
      (fun u : U => Work.Smooth.SphereJordan.windNumber γ hγ (u : ℂ)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro u
    have hu : (u : ℂ) ∉ Set.range γ := fun h => hUcomp u.2 h
    obtain ⟨ε, hε0, hε⟩ := exists_pos_le_norm_sub hγ hper (fun t ht => hu ⟨t, ht⟩)
    refine ⟨{v : U | (v : ℂ) ∈ Metric.ball (u : ℂ) ε},
      Metric.isOpen_ball.preimage continuous_subtype_val,
      Metric.mem_ball_self hε0, ?_⟩
    intro v hv
    have hv' : ‖(v : ℂ) - (u : ℂ)‖ < ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hv
    exact (Work.Smooth.SphereJordan.windNumber_eq_of_norm_lt hγ hper
      (z := (u : ℂ)) (w := (v : ℂ)) (ε := ε)
      (fun t ht => hu ⟨t, ht⟩) (fun t ht => hUcomp v.2 ⟨t, ht⟩) hv' hε).symm
  letI : PreconnectedSpace U := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  exact hloc.apply_eq_of_preconnectedSpace ⟨z, hzU⟩ ⟨w, hw⟩

/-- **A point of non-zero winding number yields one on the imaginary axis.**

If some point off the trace has non-zero winding number, then so does some point of the imaginary
axis.  (The component of the first point is bounded, hence its frontier is the whole trace, and a
connected set meeting the trace at `-1` and `1` must meet the axis.) -/
theorem exists_re_zero_windNumber_ne_zero_of_exists {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hzero : γ 0 = -1) (hpos : 1 ∈ Set.range γ)
    (hex : ∃ z : ℂ, z ∉ Set.range γ ∧
      Work.Smooth.SphereJordan.windNumber γ hγ z ≠ 0) :
    ∃ z : ℂ, z.re = 0 ∧ (∀ t : ℝ, γ t ≠ z) ∧
      Work.Smooth.SphereJordan.windNumber γ hγ z ≠ 0 := by
  obtain ⟨z₀, hz₀, hw₀⟩ := hex
  set U : Set ℂ := connectedComponentIn (Set.range γ)ᶜ z₀ with hUdef
  have hz₀U : z₀ ∈ U := mem_connectedComponentIn hz₀
  have hUcomp : U ⊆ (Set.range γ)ᶜ := connectedComponentIn_subset _ _
  -- a norm bound for the trace
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ t : ℝ, ‖γ t‖ ≤ R := by
    obtain ⟨R, hR⟩ := (isCompact_range_of_periodic hγ hper).isBounded.exists_norm_le
    exact ⟨R, fun t => hR (γ t) ⟨t, rfl⟩⟩
  have hR0 : 0 ≤ R := le_trans (norm_nonneg (γ 0)) (hR 0)
  -- the component of `z₀` is bounded: the winding number is constant on it and vanishes far away
  have hUnorm : ∀ u ∈ U, ‖u‖ ≤ R := by
    intro u hu
    by_contra hcon
    have hgt : R < ‖u‖ := not_le.mp hcon
    have h0 : Work.Smooth.SphereJordan.windNumber γ hγ u = 0 :=
      Work.Smooth.SphereJordan.windNumber_eq_zero_of_norm_gt hγ hper hR hgt
    have h1 : Work.Smooth.SphereJordan.windNumber γ hγ u
        = Work.Smooth.SphereJordan.windNumber γ hγ z₀ :=
      (windNumber_eq_of_mem_connectedComponentIn hγ hper (z := z₀) (w := u) hz₀ hu).symm
    rw [h0] at h1
    exact hw₀ h1.symm
  have hfar : (((R + 1 : ℝ)) : ℂ) ∈ (Set.range γ)ᶜ := by
    rintro ⟨t, ht⟩
    have h1 : ‖γ t‖ ≤ R := hR t
    rw [ht, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ R + 1)] at h1
    linarith
  have hUeq : U ≠ (Set.range γ)ᶜ := by
    intro heq
    have hmem : (((R + 1 : ℝ)) : ℂ) ∈ U := heq.symm ▸ hfar
    have h2 : ‖(((R + 1 : ℝ)) : ℂ)‖ ≤ R := hUnorm _ hmem
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ R + 1)] at h2
    linarith
  have hdis : ¬ IsPreconnected (Set.range γ)ᶜ := by
    intro hpre
    exact hUeq (hUdef.trans (hpre.connectedComponentIn hz₀))
  have hfront : frontier U = Set.range γ :=
    frontier_component_eq_range hγ hper hinj hdis z₀ hz₀
  -- a connected set meeting the trace at `-1` and at `1` meets the axis
  have haxis : ∃ z : ℂ, z ∈ U ∧ z.re = 0 := by
    by_contra hcon
    have hcon' : ∀ z : ℂ, z ∈ U → z.re ≠ 0 := by
      intro z hzU hzre
      exact hcon ⟨z, hzU, hzre⟩
    have hPcl : IsClosed {z : ℂ | 0 ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
    have hQcl : IsClosed {z : ℂ | z.re ≤ 0} := isClosed_le Complex.continuous_re continuous_const
    have hcover : U ⊆ {z : ℂ | 0 ≤ z.re} ∪ {z : ℂ | z.re ≤ 0} := by
      intro z _
      rcases le_total (0 : ℝ) z.re with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hinter : U ∩ ({z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.re ≤ 0}) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzU, h1, h2⟩
      exact hcon' z hzU (le_antisymm h2 h1)
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_connectedComponentIn (x := z₀) (F := (Set.range γ)ᶜ))
      {z : ℂ | 0 ≤ z.re} {z : ℂ | z.re ≤ 0} hPcl hQcl hcover hinter) with hA | hB
    · have h1 : (-1 : ℂ) ∈ frontier U := by rw [hfront]; exact ⟨0, hzero⟩
      have h2 : (-1 : ℂ) ∈ closure U := frontier_subset_closure h1
      have h3 : (-1 : ℂ) ∈ ({z : ℂ | 0 ≤ z.re} : Set ℂ) := closure_minimal hA hPcl h2
      have h4 : (0 : ℝ) ≤ (-1 : ℂ).re := h3
      norm_num at h4
    · have h1 : (1 : ℂ) ∈ frontier U := by rw [hfront]; exact hpos
      have h2 : (1 : ℂ) ∈ closure U := frontier_subset_closure h1
      have h3 : (1 : ℂ) ∈ ({z : ℂ | z.re ≤ 0} : Set ℂ) := closure_minimal hB hQcl h2
      have h4 : (1 : ℂ).re ≤ 0 := h3
      norm_num at h4
  obtain ⟨z, hzU, hzre⟩ := haxis
  have hweq : Work.Smooth.SphereJordan.windNumber γ hγ z₀
      = Work.Smooth.SphereJordan.windNumber γ hγ z :=
    windNumber_eq_of_mem_connectedComponentIn hγ hper (z := z₀) (w := z) hz₀ hzU
  exact ⟨z, hzre, fun t ht => hUcomp hzU ⟨t, ht⟩, by rw [← hweq]; exact hw₀⟩

/-- **The crux: some point off the trace has non-zero winding number** (rectangle setup).

The free window of Maehara's configuration provides a point `z` of the imaginary axis, off the
trace, whose complementary component is *bounded*; a bounded complementary component of a simple
closed plane curve is wound around non-trivially, which is the classical (and here available)
Jordan separation input. -/
theorem crux_windNumber_ne_zero_of_rectSetup {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hsub : ∀ w ∈ Set.range γ, w ∈ Work.Topology.PlaneCurve.rectR ∨ w = -1 ∨ w = 1)
    (hzero : γ 0 = -1) (hpos : 1 ∈ Set.range γ) :
    ∃ z : ℂ, z ∉ Set.range γ ∧ Work.Smooth.SphereJordan.windNumber γ hγ z ≠ 0 := by
  obtain ⟨z, -, hz, hbdd⟩ :=
    exists_bounded_component_of_rectSetup hγ hper hinj hsub hzero hpos
  exact ⟨z, hz,
    Work.Smooth.SphereJordan.windNumber_ne_zero_of_bounded_component hγ hper hinj hz hbdd⟩

theorem windNumber_ne_zero_of_normalized {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hsub : ∀ w ∈ Set.range γ, w ∈ Work.Topology.PlaneCurve.rectR ∨ w = -1 ∨ w = 1)
    (hzero : γ 0 = -1) (hpos : 1 ∈ Set.range γ) :
    ∃ z : ℂ, z.re = 0 ∧ (∀ t : ℝ, γ t ≠ z) ∧
      Work.Smooth.SphereJordan.windNumber γ hγ z ≠ 0 :=
  exists_re_zero_windNumber_ne_zero_of_exists hγ hper hinj hzero hpos
    (crux_windNumber_ne_zero_of_rectSetup hγ hper hinj hsub hzero hpos)

end

end Work.Topology.PlaneCurve
