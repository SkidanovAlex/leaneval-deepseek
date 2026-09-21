import Mathlib
import Submission.Work.OddRadon.RadialSystemAux
import Submission.Work.Geometry.Ulam.odd_radial_reconstruction

/-!
# Auxiliary lemmas for the `C¹` radial-system existence lemma

Two ingredients are isolated here.

* `radialLocalInv_ball_data` packages the local-inverse data for the two-power map
  `(R,r) ↦ (R^{2n+2}+r^{2n+2}, R^{2n+1}-r^{2n+1})` near `(1,1)`: a ball around the image point on
  which the local inverse is a genuine right inverse, stays close to `(1,1)`, is `C^∞` and has a
  bounded Fréchet derivative.
* `radialExtensionOf_hasDerivAt` computes the two-sided derivatives at `0` and `π/2` of the
  piecewise affine extension of a data function `A : ℝ → ℝ` that is only smooth on `[0,π/2]`:
  the extension is differentiable there with the one-sided derivatives of `A`, which are bounded
  by `ε` whenever `‖deriv A‖ < ε` on `[0,π/2]`.
-/

noncomputable section

open MeasureTheory Filter
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

section LocalInvData

/-- The local inverse of the two-power map, together with a ball on which its values, its
right-inverse property and the norm of its Fréchet derivative are controlled. -/
lemma radialLocalInv_ball_data (n : ℕ) :
    ∃ δ > 0, ∃ C > 0, ∃ u : Set (ℝ × ℝ),
      IsOpen u ∧ (Commons.Geometry.Ulam.radialMap n (1, 1)) ∈ u ∧
      Metric.ball (Commons.Geometry.Ulam.radialMap n (1, 1)) δ ⊆ u ∧
      ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (Commons.Geometry.Ulam.radialLocalInv n) u ∧
      (∀ z ∈ Metric.ball (Commons.Geometry.Ulam.radialMap n (1, 1)) δ,
        (Commons.Geometry.Ulam.radialLocalInv n) z ∈ Metric.ball (1, 1) (1 / 4) ∧
        Commons.Geometry.Ulam.radialMap n ((Commons.Geometry.Ulam.radialLocalInv n) z) = z ∧
        ‖fderiv ℝ (Commons.Geometry.Ulam.radialLocalInv n) z‖ ≤ C) := by
  set p0 : ℝ × ℝ := Commons.Geometry.Ulam.radialMap n (1, 1) with hp0
  set G : ℝ × ℝ → ℝ × ℝ := Commons.Geometry.Ulam.radialLocalInv n with hG
  obtain ⟨δ1, hδ1pos, hδ1⟩ := Commons.Geometry.Ulam.exists_radialLocalInv_right_inv_ball n
  have hGcont : ContinuousAt G p0 := (Commons.Geometry.Ulam.radialLocalInv_smooth n).continuousAt
  rw [Metric.continuousAt_iff] at hGcont
  obtain ⟨δ2, hδ2pos, hδ2⟩ := hGcont (1 / 4) (by norm_num)
  have hGclose : ∀ z, dist z p0 < δ2 → G z ∈ Metric.ball (1, 1) (1 / 4) := by
    intro z hz
    have h := hδ2 hz
    rw [Metric.mem_ball]
    rw [show G p0 = (1, 1) from by
      rw [hG, hp0]; exact Commons.Geometry.Ulam.radialLocalInv_apply_image n] at h
    exact h
  have hfdcont : ContinuousAt (fderiv ℝ G) p0 :=
    (Commons.Geometry.Ulam.radialLocalInv_smooth n).continuousAt_fderiv (by simp)
  rw [Metric.continuousAt_iff] at hfdcont
  obtain ⟨δ3, hδ3pos, hδ3⟩ := hfdcont 1 (by norm_num)
  obtain ⟨u0, hu0, hu0cont⟩ :=
    (Commons.Geometry.Ulam.radialLocalInv_analyticAt n).contDiffAt.contDiffOn
      (m := (((⊤ : ℕ∞) : WithTop ℕ∞))) le_top (fun _ => rfl)
  obtain ⟨δ4, hδ4pos, hδ4⟩ := Metric.mem_nhds_iff.mp hu0
  have hδ1le : min δ1 (min δ2 (min δ3 δ4)) ≤ δ1 := min_le_left _ _
  have hδ2le : min δ1 (min δ2 (min δ3 δ4)) ≤ δ2 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ3le : min δ1 (min δ2 (min δ3 δ4)) ≤ δ3 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ4le : min δ1 (min δ2 (min δ3 δ4)) ≤ δ4 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδmin : 0 < min δ1 (min δ2 (min δ3 δ4)) :=
    lt_min hδ1pos (lt_min hδ2pos (lt_min hδ3pos hδ4pos))
  refine ⟨min δ1 (min δ2 (min δ3 δ4)), hδmin, ‖fderiv ℝ G p0‖ + 1, by positivity,
    Metric.ball p0 δ4, Metric.isOpen_ball, Metric.mem_ball_self hδ4pos, ?_, ?_, ?_⟩
  · intro z hz
    rw [Metric.mem_ball] at hz
    rw [Metric.mem_ball]
    exact lt_of_lt_of_le hz hδ4le
  · refine hu0cont.mono ?_
    intro z hz
    exact hδ4 hz
  · intro z hz
    rw [Metric.mem_ball] at hz
    have h1 : dist z p0 < δ1 := lt_of_lt_of_le hz hδ1le
    have h2 : dist z p0 < δ2 := lt_of_lt_of_le hz hδ2le
    have h3 : dist z p0 < δ3 := lt_of_lt_of_le hz hδ3le
    refine ⟨hGclose z h2, ?_, ?_⟩
    · simpa [hG] using hδ1 z h1
    · have h4 := hδ3 h3
      rw [dist_eq_norm] at h4
      have h5 : ‖fderiv ℝ G z‖ < ‖fderiv ℝ G p0‖ + 1 := by
        calc ‖fderiv ℝ G z‖ ≤ ‖fderiv ℝ G p0‖ + ‖fderiv ℝ G z - fderiv ℝ G p0‖ :=
              norm_le_norm_add_norm_sub' _ _
          _ < ‖fderiv ℝ G p0‖ + 1 := by linarith
      exact le_of_lt h5

end LocalInvData

section Extension

/-- The piecewise affine extension of a function `A` that is smooth on `[0,π/2]` is
differentiable at the two endpoints, with the one-sided derivatives of `A` as derivatives, and
these are bounded by `ε` when `‖deriv A‖ ≤ ε` on the interval. -/
lemma radialExtensionOf_hasDerivAt (A : ℝ → ℝ) (ε : ℝ)
    (hA : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) A (Set.Icc 0 (Real.pi / 2)))
    (hε : ∀ α ∈ Set.Icc 0 (Real.pi / 2), |deriv A α| < ε) :
    HasDerivAt (radialExtensionOf A) (derivWithin A (Set.Icc 0 (Real.pi / 2)) 0) 0 ∧
    |derivWithin A (Set.Icc 0 (Real.pi / 2)) 0| ≤ ε ∧
    HasDerivAt (radialExtensionOf A) (derivWithin A (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2))
      (Real.pi / 2) ∧
    |derivWithin A (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2)| ≤ ε := by
  set s : Set ℝ := Set.Icc 0 (Real.pi / 2) with hs
  set m0 : ℝ := derivWithin A s 0 with hm0
  set m1 : ℝ := derivWithin A s (Real.pi / 2) with hm1
  have hpi : (0:ℝ) < Real.pi / 2 := by positivity
  have h0s : (0:ℝ) ∈ s := ⟨le_refl 0, le_of_lt hpi⟩
  have hpis : (Real.pi / 2) ∈ s := ⟨le_of_lt hpi, le_refl _⟩
  have hlevel : (((⊤ : ℕ∞) : WithTop ℕ∞)) ≠ 0 := by simp
  have hdiff : ∀ x ∈ s, HasDerivWithinAt A (derivWithin A s x) s x := fun x hx =>
    ((hA x hx).differentiableWithinAt hlevel).hasDerivWithinAt
  have hdw0 : HasDerivWithinAt A m0 s 0 := by
    rw [hm0]; exact hdiff 0 h0s
  have hdw1 : HasDerivWithinAt A m1 s (Real.pi / 2) := by
    rw [hm1]; exact hdiff _ hpis
  have hpt0 : ∀ x ∈ s \ {0}, ‖slope A 0 x‖ ≤ ε := by
    intro x hx
    obtain ⟨hxs, hxne⟩ := hx
    have hxpos : 0 < x := lt_of_le_of_ne hxs.1 (Ne.symm hxne)
    have hxle : x ≤ Real.pi / 2 := hxs.2
    obtain ⟨c, hc, hcder⟩ := exists_deriv_eq_slope A hxpos
      (hA.continuousOn.mono (fun y hy => ⟨hy.1, le_trans hy.2 hxle⟩))
      (fun y hy => ((hA.contDiffAt (Icc_mem_nhds hy.1 (lt_of_lt_of_le hy.2 hxle))).differentiableAt
        hlevel).differentiableWithinAt)
    have hcs : c ∈ s := ⟨le_of_lt hc.1, le_trans (le_of_lt hc.2) hxle⟩
    have hsl : slope A 0 x = deriv A c := by
      rw [hcder, slope_def_module, smul_eq_mul, div_eq_mul_inv]
      ring
    rw [hsl, Real.norm_eq_abs]
    exact le_of_lt (hε c hcs)
  have hpt1 : ∀ x ∈ s \ {Real.pi / 2}, ‖slope A (Real.pi / 2) x‖ ≤ ε := by
    intro x hx
    obtain ⟨hxs, hxne⟩ := hx
    have hxlt : x < Real.pi / 2 := lt_of_le_of_ne hxs.2 hxne
    obtain ⟨c, hc, hcder⟩ := exists_deriv_eq_slope A hxlt
      (hA.continuousOn.mono (fun y hy => ⟨le_trans hxs.1 hy.1, hy.2⟩))
      (fun y hy => ((hA.contDiffAt (Icc_mem_nhds (lt_of_le_of_lt hxs.1 hy.1) hy.2)).differentiableAt
        hlevel).differentiableWithinAt)
    have hcs : c ∈ s := ⟨le_trans hxs.1 (le_of_lt hc.1), le_of_lt hc.2⟩
    have hsl : slope A (Real.pi / 2) x = deriv A c := by
      rw [hcder, slope_def_module, smul_eq_mul,
        show A (Real.pi / 2) - A x = -(A x - A (Real.pi / 2)) by ring,
        show Real.pi / 2 - x = -(x - Real.pi / 2) by ring,
        neg_div, div_neg, neg_neg, div_eq_mul_inv]
      ring
    rw [hsl, Real.norm_eq_abs]
    exact le_of_lt (hε c hcs)
  have hne0 : (𝓝[s \ {0}] (0:ℝ)).NeBot := by
    rw [nhdsWithin_neBot]
    intro t ht
    obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp ht
    have hmin : 0 < min r (Real.pi / 2) := lt_min hrpos hpi
    have hw : 0 < min r (Real.pi / 2) / 2 := by linarith
    refine ⟨min r (Real.pi / 2) / 2, hr ?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hw]
      have h1 : min r (Real.pi / 2) / 2 ≤ r / 2 := by
        have := min_le_left r (Real.pi / 2); linarith
      linarith
    · refine ⟨⟨le_of_lt hw, ?_⟩, ne_of_gt hw⟩
      have h2 : min r (Real.pi / 2) / 2 ≤ Real.pi / 2 := by
        have := min_le_right r (Real.pi / 2); linarith
      exact h2
  have hb0 : |m0| ≤ ε := by
    have hslope : Tendsto (slope A 0) (𝓝[s \ {0}] 0) (𝓝 m0) := by
      rw [← hasDerivWithinAt_iff_tendsto_slope]
      exact hdw0
    have hev : ∀ᶠ x in 𝓝[s \ {0}] 0, ‖slope A 0 x‖ ≤ ε :=
      (Filter.eventually_principal.mpr hpt0).filter_mono inf_le_right
    have hne : (𝓝[s \ {0}] (0:ℝ)).NeBot := hne0
    have h := le_of_tendsto (hslope.norm) hev
    rwa [Real.norm_eq_abs] at h
  have hne1 : (𝓝[s \ {Real.pi / 2}] (Real.pi / 2)).NeBot := by
    rw [nhdsWithin_neBot]
    intro t ht
    obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp ht
    have hmin : 0 < min r (Real.pi / 2) := lt_min hrpos hpi
    have hw : 0 < min r (Real.pi / 2) / 2 := by linarith
    refine ⟨Real.pi / 2 - min r (Real.pi / 2) / 2, hr ?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      have h1 : min r (Real.pi / 2) / 2 ≤ r / 2 := by
        have := min_le_left r (Real.pi / 2); linarith
      constructor <;> linarith
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h2 : min r (Real.pi / 2) / 2 ≤ Real.pi / 2 := by
          have := min_le_right r (Real.pi / 2); linarith
        linarith
      · linarith
      · exact ne_of_lt (by linarith)
  have hb1 : |m1| ≤ ε := by
    have hslope : Tendsto (slope A (Real.pi / 2)) (𝓝[s \ {Real.pi / 2}] (Real.pi / 2)) (𝓝 m1) := by
      rw [← hasDerivWithinAt_iff_tendsto_slope]
      exact hdw1
    have hev : ∀ᶠ x in 𝓝[s \ {Real.pi / 2}] (Real.pi / 2), ‖slope A (Real.pi / 2) x‖ ≤ ε :=
      (Filter.eventually_principal.mpr hpt1).filter_mono inf_le_right
    have hne : (𝓝[s \ {Real.pi / 2}] (Real.pi / 2)).NeBot := hne1
    have h := le_of_tendsto (hslope.norm) hev
    rwa [Real.norm_eq_abs] at h
  have hAtil0 : HasDerivWithinAt (radialExtensionOf A) m0 (Set.Iic 0) 0 := by
    have hlin : HasDerivAt (fun x : ℝ => A 0 + m0 * x) m0 0 := by
      have h1 : HasDerivAt (fun x : ℝ => A 0 + m0 * x) (0 + m0 * 1) 0 :=
        (hasDerivAt_const (0:ℝ) (A 0)).add ((hasDerivAt_id (0:ℝ)).const_mul m0)
      simpa using h1
    refine hlin.hasDerivWithinAt.congr (fun y hy => ?_) ?_
    · rw [radialExtensionOf, radialDataExtend, if_pos (Set.mem_Iic.mp hy), hm0]
    · rw [radialExtensionOf, radialDataExtend, if_pos le_rfl, hm0]
  have hAtil0s : HasDerivWithinAt (radialExtensionOf A) m0 s 0 :=
    hdw0.congr (fun y hy => radialExtensionOf_eqOn A y hy) (radialExtensionOf_eqOn A 0 h0s)
  have hderiv0 : HasDerivAt (radialExtensionOf A) m0 0 := by
    refine (hAtil0.union hAtil0s).hasDerivAt ?_
    apply Filter.mem_of_superset (Iio_mem_nhds hpi)
    intro x hx
    by_cases h : x ≤ 0
    · exact Or.inl h
    · exact Or.inr ⟨le_of_lt (not_le.mp h), le_of_lt hx⟩
  have hAtil1 : HasDerivWithinAt (radialExtensionOf A) m1 (Set.Ici (Real.pi / 2)) (Real.pi / 2) := by
    have hlin : HasDerivAt (fun x : ℝ => A (Real.pi / 2) + m1 * (x - Real.pi / 2)) m1 (Real.pi / 2) := by
      have h1 : HasDerivAt (fun x : ℝ => x - Real.pi / 2) (1 - 0) (Real.pi / 2) :=
        (hasDerivAt_id (Real.pi / 2)).sub (hasDerivAt_const (Real.pi / 2) (Real.pi / 2))
      have h2 : HasDerivAt (fun x : ℝ => m1 * (x - Real.pi / 2)) (m1 * (1 - 0)) (Real.pi / 2) :=
        h1.const_mul m1
      have h3 : HasDerivAt (fun x : ℝ => A (Real.pi / 2) + m1 * (x - Real.pi / 2))
          (0 + m1 * (1 - 0)) (Real.pi / 2) :=
        (hasDerivAt_const (Real.pi / 2) (A (Real.pi / 2))).add h2
      rw [show (0:ℝ) + m1 * (1 - 0) = m1 by ring] at h3
      exact h3
    refine hlin.hasDerivWithinAt.congr (fun y hy => ?_) ?_
    · rw [radialExtensionOf, radialDataExtend]
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hy) with h | h
      · rw [if_neg (by linarith : ¬ y ≤ 0), if_pos (le_of_eq h.symm), hm1]
        rw [h]; ring
      · rw [if_neg (by linarith : ¬ y ≤ 0), if_neg (not_le.mpr h), hm1]
    · rw [radialExtensionOf, radialDataExtend, if_neg (by linarith : ¬ Real.pi / 2 ≤ 0),
        if_pos le_rfl, hm1]
      ring
  have hAtil1s : HasDerivWithinAt (radialExtensionOf A) m1 s (Real.pi / 2) :=
    hdw1.congr (fun y hy => radialExtensionOf_eqOn A y hy) (radialExtensionOf_eqOn A _ hpis)
  have hderiv1 : HasDerivAt (radialExtensionOf A) m1 (Real.pi / 2) := by
    refine (hAtil1.union hAtil1s).hasDerivAt ?_
    apply Filter.mem_of_superset (Ioi_mem_nhds hpi)
    intro x hx
    by_cases h : Real.pi / 2 ≤ x
    · exact Or.inl h
    · exact Or.inr ⟨le_of_lt hx, le_of_lt (not_le.mp h)⟩
  exact ⟨hderiv0, hb0, hderiv1, hb1⟩

end Extension

section DistRadialMap

/-- The distance from `(2 + a, b)` to the image point `radialMap n (1,1) = (2,0)`. -/
lemma dist_radialMap_pair (n : ℕ) (a b : ℝ) :
    dist ((2 + a, b) : ℝ × ℝ) (Commons.Geometry.Ulam.radialMap n (1, 1)) = max |a| |b| := by
  have h1 : (1:ℝ) ^ (2 * n + 2) + (1:ℝ) ^ (2 * n + 2) = 2 := by norm_num
  have h2 : (1:ℝ) ^ (2 * n + 1) - (1:ℝ) ^ (2 * n + 1) = 0 := by norm_num
  rw [Commons.Geometry.Ulam.radialMap, h1, h2]
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  congr 1
  · congr 1; ring
  · congr 1; ring

end DistRadialMap

end Work.OddRadon
