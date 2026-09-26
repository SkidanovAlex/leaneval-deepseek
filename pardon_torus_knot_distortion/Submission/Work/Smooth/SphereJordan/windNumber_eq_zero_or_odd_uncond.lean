import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic
import Submission.Work.Smooth.SphereJordan.exists_sqrt_curve_of_even_windNumber
import Submission.Work.Topology.PlaneCurve.compl_jordan_atMostTwo
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range

/-!
# The winding number of a simple closed plane curve is zero or odd

For a continuous `2π`-periodic curve `γ : ℝ → ℂ` injective on one period and a point `z` off its
trace, the winding number `windNumber γ hγ z` is either `0` or odd.

The proof is by contradiction: if the winding number were `2m` with `m ≠ 0`, the loop
`t ↦ γ(2πt) - z` would have even degree, hence a continuous square root `η` (a "half argument"
loop), see `exists_sqrt_curve_of_even_windNumber`.  The curve `η` is then a Jordan curve — because
`η s = -η t` implies `γ s = γ t` — but its winding number about `0` is `m ≠ 0`, so `0` lies in the
bounded component of its complement.  Finally a naive geometric argument (at most two components,
the frontier of a component, and the maximal radius along a ray) shows that a Jordan curve
enclosing the origin cannot be disjoint from its reflection, while `η s ≠ -η t` is exactly
disjointness of the trace from its reflection.
-/

namespace Work.Smooth.SphereJordan

open Set
open Classical

noncomputable section

/-! ## Elementary topological preliminaries -/

/-- **Local constancy of the winding number**: if `x` is off the trace of `γ`, there is a ball
about `x` on which the winding number is constant (and which avoids the trace). -/
theorem windNumber_eq_of_mem_ball {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) {x : ℂ} (hx : x ∉ Set.range γ) :
    ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      y ∉ Set.range γ ∧ windNumber γ hγ y = windNumber γ hγ x := by
  have hclosed : IsClosed (Set.range γ) :=
    (Work.Topology.PlaneCurve.isCompact_range_of_periodic hγ hper).isClosed
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl x hx
  refine ⟨δ, hδ, fun y hy => ⟨fun hyK => ?_, ?_⟩⟩
  · exact hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hy) hyK
  · refine windNumber_eq_of_segment hγ hper (x := y) (y := x)
      (fun t ht => ?_) (fun t ht => ?_) ?_
    · exact hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hy) ⟨t, ht⟩
    · exact hx ⟨t, ht⟩
    · intro t s hs hcon
      have h1 : (1 - s) * y + s * x - x = (1 - s) * (y - x) := by ring
      have h2 : ‖(1 - s) * y + s * x - x‖ < δ := by
        rw [h1, norm_mul]
        have hcast : (1 - (s : ℂ)) = (((1 - s : ℝ)) : ℂ) := by push_cast; ring
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
        have hs' : |1 - s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
        calc |1 - s| * ‖y - x‖ ≤ 1 * ‖y - x‖ := mul_le_mul_of_nonneg_right hs' (norm_nonneg _)
          _ = ‖y - x‖ := one_mul _
          _ < δ := hy
      exact hball (by rw [Metric.mem_ball, dist_eq_norm]; exact h2) ⟨t, hcon⟩

/-- **The winding number is constant on a preconnected subset of the complement of the trace.** -/
theorem windNumber_eq_of_preconnected_subset {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) {S : Set ℂ} (hS : IsPreconnected S)
    (hSK : S ⊆ (Set.range γ)ᶜ) {x : ℂ} (hx : x ∈ S) :
    ∀ y ∈ S, windNumber γ hγ y = windNumber γ hγ x := by
  have hball : ∀ p ∈ S, ∃ δ > 0, ∀ z : ℂ, ‖z - p‖ < δ →
      windNumber γ hγ z = windNumber γ hγ p := fun p hp => by
    obtain ⟨δ, hδ, h⟩ := windNumber_eq_of_mem_ball hγ hper (hSK hp)
    exact ⟨δ, hδ, fun z hz => (h z hz).2⟩
  let δ : ℂ → ℝ := fun p => if h : p ∈ S then (hball p h).choose else 1
  have hδpos : ∀ p ∈ S, 0 < δ p := by
    intro p hp
    have h : δ p = (hball p hp).choose := by
      show (if h : p ∈ S then (hball p h).choose else 1) = (hball p hp).choose
      rw [dif_pos hp]
    rw [h]
    exact (hball p hp).choose_spec.1
  have hδW : ∀ p ∈ S, ∀ z : ℂ, ‖z - p‖ < δ p → windNumber γ hγ z = windNumber γ hγ p := by
    intro p hp z hz
    have h : δ p = (hball p hp).choose := by
      show (if h : p ∈ S then (hball p h).choose else 1) = (hball p hp).choose
      rw [dif_pos hp]
    rw [h] at hz
    exact (hball p hp).choose_spec.2 z hz
  set A : Set ℂ := {z : ℂ | ∃ p ∈ S,
    windNumber γ hγ p = windNumber γ hγ x ∧ z ∈ Metric.ball p (δ p)} with hA
  set B : Set ℂ := {z : ℂ | ∃ p ∈ S,
    windNumber γ hγ p ≠ windNumber γ hγ x ∧ z ∈ Metric.ball p (δ p)} with hB
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨p, hpS, hpW, hzp⟩
    have hlt : ‖z - p‖ < δ p := by
      rw [Metric.mem_ball, dist_eq_norm] at hzp
      exact hzp
    refine Filter.mem_of_superset (Metric.ball_mem_nhds z (sub_pos.mpr hlt)) ?_
    intro z' hz'
    refine ⟨p, hpS, hpW, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz' ⊢
    rw [Metric.mem_ball, dist_eq_norm] at hzp
    have ht := norm_add_le (z' - z) (z - p)
    rw [show (z' - z) + (z - p) = z' - p by ring] at ht
    linarith
  have hBopen : IsOpen B := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨p, hpS, hpW, hzp⟩
    have hlt : ‖z - p‖ < δ p := by
      rw [Metric.mem_ball, dist_eq_norm] at hzp
      exact hzp
    refine Filter.mem_of_superset (Metric.ball_mem_nhds z (sub_pos.mpr hlt)) ?_
    intro z' hz'
    refine ⟨p, hpS, hpW, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz' ⊢
    rw [Metric.mem_ball, dist_eq_norm] at hzp
    have ht := norm_add_le (z' - z) (z - p)
    rw [show (z' - z) + (z - p) = z' - p by ring] at ht
    linarith
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro z ⟨p, hpS, hpW, hzp⟩ ⟨q, hqS, hqW, hzq⟩
    have h1 : windNumber γ hγ z = windNumber γ hγ p :=
      hδW p hpS z (by rwa [Metric.mem_ball, dist_eq_norm] at hzp)
    have h2 : windNumber γ hγ z = windNumber γ hγ q :=
      hδW q hqS z (by rwa [Metric.mem_ball, dist_eq_norm] at hzq)
    exact hqW (by rw [← h2, h1, hpW])
  have hcover : S ⊆ A ∪ B := by
    intro p hp
    by_cases hpW : windNumber γ hγ p = windNumber γ hγ x
    · exact Or.inl ⟨p, hp, hpW, by
        rw [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]; exact hδpos p hp⟩
    · exact Or.inr ⟨p, hp, hpW, by
        rw [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]; exact hδpos p hp⟩
  have hxnotB : x ∉ B := by
    rintro ⟨p, hpS, hpW, hxp⟩
    have h1 : windNumber γ hγ x = windNumber γ hγ p :=
      hδW p hpS x (by rwa [Metric.mem_ball, dist_eq_norm] at hxp)
    exact hpW h1.symm
  intro y hy
  rcases hS.subset_or_subset hAopen hBopen hdisj hcover with h | h
  · obtain ⟨p, hpS, hpW, hyp⟩ := h hy
    exact (hδW p hpS y (by rwa [Metric.mem_ball, dist_eq_norm] at hyp)).trans hpW
  · exact absurd (h hx) hxnotB

/-- The complement of the trace of a curve of non-zero winding number about `0` is not
preconnected. -/
theorem not_isPreconnected_compl_of_windNumber_ne_zero {κ : ℝ → ℂ} (hκ : Continuous κ)
    (hper : Function.Periodic κ (2 * Real.pi)) {R : ℝ} (hR : ∀ t : ℝ, ‖κ t‖ ≤ R) {w : ℂ}
    (hwR : R < ‖w‖) (h0 : (0 : ℂ) ∉ Set.range κ) (hW : windNumber κ hκ 0 ≠ 0) :
    ¬ IsPreconnected (Set.range κ)ᶜ := by
  intro hconn
  have hwK : w ∉ Set.range κ := by
    rintro ⟨t, ht⟩
    have h := hR t
    rw [ht] at h
    linarith
  have hconst := windNumber_eq_of_preconnected_subset hκ hper hconn (subset_refl _) h0 w hwK
  exact hW (by rw [← hconst]; exact windNumber_eq_zero_of_norm_gt hκ hper hR hwR)

/-- **Description of the two components of the complement.**  For a curve of non-zero winding
number about `0` and a far point `w`, every point off the trace lies in the component of `w` or in
the component of `0`. -/
theorem components_cover {κ : ℝ → ℂ} (hκ : Continuous κ)
    (hper : Function.Periodic κ (2 * Real.pi)) (hinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi)))
    {R : ℝ} (hR : ∀ t : ℝ, ‖κ t‖ ≤ R) {w : ℂ} (hwR : R < ‖w‖) (h0 : (0 : ℂ) ∉ Set.range κ)
    (hW : windNumber κ hκ 0 ≠ 0) {p : ℂ} (hp : p ∉ Set.range κ) :
    p ∈ connectedComponentIn (Set.range κ)ᶜ w ∪ connectedComponentIn (Set.range κ)ᶜ 0 := by
  have hwK : w ∉ Set.range κ := by
    rintro ⟨t, ht⟩
    have h := hR t
    rw [ht] at h
    linarith
  rcases Work.Topology.PlaneCurve.compl_jordan_atMostTwo hκ hper hinj h0 hwK hp with
    h | h | h
  · exfalso
    have h0U : (0 : ℂ) ∈ connectedComponentIn (Set.range κ)ᶜ w := by
      rw [← h]; exact mem_connectedComponentIn h0
    have hconst := windNumber_eq_of_preconnected_subset hκ hper
      isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) h0U w
      (mem_connectedComponentIn hwK)
    exact hW (by rw [← hconst]; exact windNumber_eq_zero_of_norm_gt hκ hper hR hwR)
  · exact Or.inr (h ▸ mem_connectedComponentIn hp)
  · exact Or.inl (h ▸ mem_connectedComponentIn hp)

/-- **The component of `0` is bounded**, in the sharp form that it lies in the ball of radius the
maximum of the norm of the curve. -/
theorem component_zero_bounded {κ : ℝ → ℂ} (hκ : Continuous κ)
    (hper : Function.Periodic κ (2 * Real.pi)) (hinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi)))
    {R : ℝ} (hR : ∀ t : ℝ, ‖κ t‖ ≤ R) {w : ℂ} (hwR : R < ‖w‖) (h0 : (0 : ℂ) ∉ Set.range κ)
    (hW : windNumber κ hκ 0 ≠ 0) {p : ℂ}
    (hp : p ∈ connectedComponentIn (Set.range κ)ᶜ 0) : ‖p‖ ≤ R := by
  by_contra hcon
  push_neg at hcon
  have hpc : p ∉ Set.range κ := connectedComponentIn_subset _ _ hp
  have hWp : windNumber κ hκ p = 0 := windNumber_eq_zero_of_norm_gt hκ hper hR hcon
  have hwK : w ∉ Set.range κ := by
    rintro ⟨t, ht⟩
    have h := hR t
    rw [ht] at h
    linarith
  rcases components_cover hκ hper hinj hR hwR h0 hW hpc with h | h
  · have heq : connectedComponentIn (Set.range κ)ᶜ 0 = connectedComponentIn (Set.range κ)ᶜ w := by
      rw [connectedComponentIn_eq hp, connectedComponentIn_eq h]
    have h0c : (0 : ℂ) ∈ connectedComponentIn (Set.range κ)ᶜ w := by
      rw [← heq]; exact mem_connectedComponentIn h0
    have hconst := windNumber_eq_of_preconnected_subset hκ hper
      isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) h0c w
      (mem_connectedComponentIn hwK)
    exact hW (by rw [← hconst]; exact windNumber_eq_zero_of_norm_gt hκ hper hR hwR)
  · have hconst := windNumber_eq_of_preconnected_subset hκ hper
      isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) hp (0 : ℂ)
      (mem_connectedComponentIn h0)
    exact hW (by rw [hconst, hWp])

/-- **A ray from the origin through a point of an open bounded set of which the trace is the
frontier must leave it.**  There is a point of the trace of `κ` on the ray strictly farther from
the origin than `p`. -/
theorem ray_exit {κ : ℝ → ℂ} {V : Set ℂ} (hVo : IsOpen V) (hVbdd : Bornology.IsBounded V)
    (hfr : frontier V = Set.range κ) {p : ℂ} (hpV : p ∈ V) (hp0 : p ≠ 0) :
    ∃ s : ℝ, ‖p‖ < s ∧ s • ((‖p‖)⁻¹ • p) ∈ Set.range κ := by
  set u : ℂ := (‖p‖)⁻¹ • p with hu
  have hpn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg p)]
    field_simp
  obtain ⟨B, hB⟩ := hVbdd.exists_norm_le
  have hcont : Continuous fun s : ℝ => s • u := continuous_id.smul continuous_const
  set A : Set ℝ := {s : ℝ | ‖p‖ ≤ s ∧ s • u ∉ V} with hA
  have hAclosed : IsClosed A := by
    rw [hA]
    exact isClosed_Ici.inter (hVo.isClosed_compl.preimage hcont)
  have hAne : A.Nonempty := by
    refine ⟨max B (‖p‖ + 1) + 1, ?_, ?_⟩
    · linarith [le_max_right B (‖p‖ + 1), norm_nonneg p]
    · intro hmem
      have h1 := hB _ hmem
      have h2 : ‖(max B (‖p‖ + 1) + 1) • u‖ = max B (‖p‖ + 1) + 1 := by
        rw [norm_smul, hu1, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [le_max_right B (‖p‖ + 1), norm_nonneg p])]
      rw [h2] at h1
      linarith [h1, le_max_left B (‖p‖ + 1)]
  have hAbdd : BddBelow A := ⟨‖p‖, fun s hs => hs.1⟩
  set s₀ : ℝ := sInf A with hs₀
  have hs₀A : s₀ ∈ A := hAclosed.csInf_mem hAne hAbdd
  have hs₀ge : ‖p‖ ≤ s₀ := hs₀A.1
  have hs₀notV : s₀ • u ∉ V := hs₀A.2
  have hne : ‖p‖ ≠ s₀ := by
    intro h
    refine hs₀notV ?_
    rw [← h, hu, smul_inv_smul₀ hpn]
    exact hpV
  have hgt : ‖p‖ < s₀ := lt_of_le_of_ne hs₀ge hne
  have hclos : s₀ • u ∈ closure V := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set s₁ : ℝ := s₀ - min (ε / 2) ((s₀ - ‖p‖) / 2) with hs₁
    have hminpos : 0 < min (ε / 2) ((s₀ - ‖p‖) / 2) := lt_min (by linarith) (by linarith)
    have hs₁lt : s₁ < s₀ := by rw [hs₁]; linarith
    have hs₁ge : ‖p‖ ≤ s₁ := by
      rw [hs₁]; have := min_le_right (ε / 2) ((s₀ - ‖p‖) / 2); linarith
    have hs₁V : s₁ • u ∈ V := by
      by_contra hc
      have hs₁A : s₁ ∈ A := ⟨hs₁ge, hc⟩
      have hle := csInf_le hAbdd hs₁A
      rw [← hs₀] at hle
      linarith
    have hnorm : ‖s₀ • u - s₁ • u‖ = s₀ - s₁ := by
      rw [← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), hu1, mul_one]
    refine ⟨s₁ • u, hs₁V, ?_⟩
    rw [dist_eq_norm, hnorm]
    have hsub : s₀ - s₁ = min (ε / 2) ((s₀ - ‖p‖) / 2) := by rw [hs₁]; ring
    rw [hsub]
    have hle := min_le_left (ε / 2) ((s₀ - ‖p‖) / 2)
    linarith
  have hfr' : s₀ • u ∈ frontier V := by
    rw [hVo.frontier_eq]
    exact ⟨hclos, hs₀notV⟩
  rw [hfr] at hfr'
  exact ⟨s₀, hgt, hfr'⟩

/-- The winding number about `0` of the pointwise negated curve is unchanged. -/
theorem windNumber_neg_zero {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (h0 : ∀ t : ℝ, γ t ≠ 0) :
    windNumber (fun t : ℝ => -(γ t)) hγ.neg 0 = windNumber γ hγ 0 := by
  set v : C(unitInterval, ℂ) := curveLoop (fun t : ℝ => γ t - 0) (hγ.sub continuous_const) with hv
  set w : C(unitInterval, ℂ) := curveLoop (fun t : ℝ => -(γ t) - 0) (hγ.neg.sub continuous_const)
    with hw
  have hvne : ∀ t, v t ≠ 0 := by
    intro t; rw [hv]
    show γ (2 * Real.pi * (t : ℝ)) - 0 ≠ 0
    rw [sub_zero]
    exact h0 _
  have hwne : ∀ t, w t ≠ 0 := by
    intro t; rw [hw]
    show -(γ (2 * Real.pi * (t : ℝ))) - 0 ≠ 0
    rw [sub_zero]
    exact neg_ne_zero.mpr (h0 _)
  have hgeom : γ (2 * Real.pi * ((0 : unitInterval) : ℝ))
      = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) := by
    have h0' : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by norm_num
    have h1' : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by norm_num
    rw [h0', h1']
    simpa using (hper 0).symm
  have hvloop : v 0 = v 1 := by
    rw [hv]
    show γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - 0
      = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - 0
    rw [hgeom]
  have hwloop : w 0 = w 1 := by
    rw [hw]
    show -(γ (2 * Real.pi * ((0 : unitInterval) : ℝ))) - 0
      = -(γ (2 * Real.pi * ((1 : unitInterval) : ℝ))) - 0
    rw [hgeom]
  let k : C(unitInterval, ℂ) := ContinuousMap.const unitInterval (-1 : ℂ)
  have hkne : ∀ t, k t ≠ 0 := by intro t; exact neg_ne_zero.mpr one_ne_zero
  have hkloop : k 0 = k 1 := rfl
  have hpoint : ∀ t : unitInterval, (k * v) t = w t := by
    intro t
    show (ContinuousMap.const unitInterval (-1 : ℂ)) t * v t = w t
    rw [hv, hw]
    show (-1 : ℂ) * (γ (2 * Real.pi * (t : ℝ)) - 0) = -(γ (2 * Real.pi * (t : ℝ))) - 0
    ring
  have hmul := loopIndex_mul k v hkne hvne hkloop hvloop
  have hcongr := loopIndex_congr hpoint (fun t => mul_ne_zero (hkne t) (hvne t)) hwne
    (by simp only [ContinuousMap.mul_apply]; rw [hkloop, hvloop]) hwloop
  have hkidx : loopIndex k = 0 := loopIndex_const (-1) (by norm_num)
  show loopIndex w = loopIndex v
  rw [← hcongr, hmul, hkidx, zero_add]

/-! ## A Jordan curve enclosing the origin meets its reflection -/

/-- **No antipodal-free loop encloses `0`.**  A continuous `2π`-periodic curve injective on one
period, avoiding `0`, with non-zero winding number about `0`, must contain a pair of antipodal
points. -/
theorem false_of_antipodalFree_of_windNumber_ne_zero {η : ℝ → ℂ} (hη : Continuous η)
    (hper : Function.Periodic η (2 * Real.pi)) (hinj : Set.InjOn η (Set.Ico 0 (2 * Real.pi)))
    (h0 : ∀ t : ℝ, η t ≠ 0) (hw : windNumber η hη 0 ≠ 0)
    (hanti : ∀ s t : ℝ, η s ≠ -η t) : False := by
  classical
  have h0K : (0 : ℂ) ∉ Set.range η := by
    rintro ⟨t, ht⟩
    exact h0 t ht
  obtain ⟨x₀, hx₀K, hx₀max⟩ :=
    (Work.Topology.PlaneCurve.isCompact_range_of_periodic hη hper).exists_isMaxOn
      ⟨η 0, ⟨0, rfl⟩⟩ continuous_norm.continuousOn
  obtain ⟨t₀, ht₀⟩ := hx₀K
  set R : ℝ := ‖η t₀‖ with hRdef
  have hR : ∀ t : ℝ, ‖η t‖ ≤ R := by
    intro t
    rw [hRdef, ht₀]
    exact hx₀max ⟨t, rfl⟩
  have hRμ : ∀ t : ℝ, ‖-η t‖ ≤ R := by
    intro t
    rw [norm_neg]
    exact hR t
  set w : ℂ := ((R + 1 : ℝ) : ℂ) with hwdef
  have hwn : ‖w‖ = R + 1 := by
    rw [hwdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hwR : R < ‖w‖ := by rw [hwn]; linarith
  have hwK : w ∉ Set.range η := by
    rintro ⟨t, ht⟩
    have h := hR t
    rw [ht, hwn] at h
    linarith
  have hwnegK : (-w) ∉ Set.range (fun t : ℝ => -η t) := by
    rintro ⟨t, ht⟩
    exact hwK ⟨t, neg_inj.mp ht⟩
  have hwμR : R < ‖(-w : ℂ)‖ := by rw [norm_neg]; exact hwR
  have hμc : Continuous fun t : ℝ => -η t := hη.neg
  have hμper : Function.Periodic (fun t : ℝ => -η t) (2 * Real.pi) := fun t => by
    simp only [hper t]
  have hμinj : Set.InjOn (fun t : ℝ => -η t) (Set.Ico 0 (2 * Real.pi)) :=
    fun a ha b hb hab => hinj ha hb (neg_inj.mp hab)
  have hμ0 : (0 : ℂ) ∉ Set.range (fun t : ℝ => -η t) := by
    rintro ⟨t, ht⟩
    exact h0 t (by simpa using ht)
  have hμ0' : ∀ t : ℝ, -η t ≠ 0 := fun t => neg_ne_zero.mpr (h0 t)
  have hWμ0 : windNumber (fun t : ℝ => -η t) hμc 0 ≠ 0 := by
    rw [windNumber_neg_zero hη hper h0]
    exact hw
  set U : Set ℂ := connectedComponentIn (Set.range η)ᶜ w with hUdef
  set V : Set ℂ := connectedComponentIn (Set.range η)ᶜ 0 with hVdef
  set U' : Set ℂ := connectedComponentIn (Set.range (fun t : ℝ => -η t))ᶜ (-w) with hU'def
  set V' : Set ℂ := connectedComponentIn (Set.range (fun t : ℝ => -η t))ᶜ 0 with hV'def
  have hKclosed : IsClosed (Set.range η) :=
    (Work.Topology.PlaneCurve.isCompact_range_of_periodic hη hper).isClosed
  have hμclosed : IsClosed (Set.range (fun t : ℝ => -η t)) :=
    (Work.Topology.PlaneCurve.isCompact_range_of_periodic hμc hμper).isClosed
  have hUo : IsOpen U := hKclosed.isOpen_compl.connectedComponentIn
  have hVo : IsOpen V := hKclosed.isOpen_compl.connectedComponentIn
  have hU'o : IsOpen U' := hμclosed.isOpen_compl.connectedComponentIn
  have hV'o : IsOpen V' := hμclosed.isOpen_compl.connectedComponentIn
  have hVmem : (0 : ℂ) ∈ V := mem_connectedComponentIn h0K
  have hV'mem : (0 : ℂ) ∈ V' := mem_connectedComponentIn hμ0
  have hUVne : U ≠ V := by
    intro heq
    have h0U : (0 : ℂ) ∈ U := by rw [heq]; exact hVmem
    have hconst := windNumber_eq_of_preconnected_subset hη hper
      isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) h0U w
      (mem_connectedComponentIn hwK)
    rw [← hconst] at hw
    exact hw (windNumber_eq_zero_of_norm_gt hη hper hR hwR)
  have hUVdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro p hpU hpV
    exact hUVne (by rw [hUdef, hVdef, connectedComponentIn_eq hpU, connectedComponentIn_eq hpV])
  have hU'V'ne : U' ≠ V' := by
    intro heq
    have h0U' : (0 : ℂ) ∈ U' := by rw [heq]; exact hV'mem
    have hconst := windNumber_eq_of_preconnected_subset hμc hμper
      isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) h0U' (-w)
      (mem_connectedComponentIn hwnegK)
    rw [← hconst] at hWμ0
    exact hWμ0 (windNumber_eq_zero_of_norm_gt hμc hμper hRμ hwμR)
  have hU'V'disj : Disjoint U' V' := by
    rw [Set.disjoint_left]
    intro p hpU hpV
    exact hU'V'ne (by rw [hU'def, hV'def, connectedComponentIn_eq hpU, connectedComponentIn_eq hpV])
  have hVbdd : ∀ p ∈ V, ‖p‖ ≤ R := fun p hp =>
    component_zero_bounded hη hper hinj hR hwR h0K hw hp
  have hV'bdd : ∀ p ∈ V', ‖p‖ ≤ R := fun p hp =>
    component_zero_bounded hμc hμper hμinj hRμ hwμR hμ0 hWμ0 hp
  have hVbd : Bornology.IsBounded V :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset (fun p hp => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hVbdd p hp)
  have hV'bd : Bornology.IsBounded V' :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset (fun p hp => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hV'bdd p hp)
  have hfr : frontier V = Set.range η :=
    Work.Topology.PlaneCurve.frontier_component_eq_range hη hper hinj
      (not_isPreconnected_compl_of_windNumber_ne_zero hη hper hR hwR h0K hw) 0 h0K
  have hfr' : frontier V' = Set.range (fun t : ℝ => -η t) :=
    Work.Topology.PlaneCurve.frontier_component_eq_range hμc hμper hμinj
      (not_isPreconnected_compl_of_windNumber_ne_zero hμc hμper hRμ hwμR hμ0 hWμ0) 0 hμ0
  have hdisjK : Disjoint (Set.range η) (Set.range (fun t : ℝ => -η t)) := by
    rw [Set.disjoint_left]
    rintro p ⟨s, hs⟩ ⟨t, ht⟩
    exact hanti s t (hs.trans ht.symm)
  have hnegKsub : Set.range (fun t : ℝ => -η t) ⊆ (Set.range η)ᶜ := fun p hp hpk =>
    (Set.disjoint_left.mp hdisjK) hpk hp
  have hKsub : Set.range η ⊆ (Set.range (fun t : ℝ => -η t))ᶜ := fun p hp hpk =>
    (Set.disjoint_left.mp hdisjK) hp hpk
  have hnegK : IsPreconnected (Set.range (fun t : ℝ => -η t)) :=
    isPreconnected_range hμc
  have hKpre : IsPreconnected (Set.range η) := isPreconnected_range hη
  have hucov : ∀ p : ℂ, p ∉ Set.range η → p ∈ U ∪ V := fun p hp =>
    components_cover hη hper hinj hR hwR h0K hw hp
  have hucov' : ∀ p : ℂ, p ∉ Set.range (fun t : ℝ => -η t) → p ∈ U' ∪ V' := fun p hp =>
    components_cover hμc hμper hμinj hRμ hwμR hμ0 hWμ0 hp
  rcases hnegK.subset_or_subset hUo hVo hUVdisj (fun p hp => hucov p (hnegKsub hp)) with
    hKU | hKV
  · rcases hKpre.subset_or_subset hU'o hV'o hU'V'disj (fun p hp => hucov' p (hKsub hp)) with
      hKU' | hKV'
    · -- `K ⊆ U'`, `-K ⊆ U`: the two bounded components coincide
      have hVpre : IsPreconnected V := isPreconnected_connectedComponentIn
      have hV'pre : IsPreconnected V' := isPreconnected_connectedComponentIn
      have hVsubV' : V ⊆ V' := by
        have hsub : V ⊆ U' ∪ V' := fun p hp =>
          hucov' p (fun hpk => (Set.disjoint_left.mp hUVdisj) (hKU hpk) hp)
        rcases hVpre.subset_or_subset hU'o hV'o hU'V'disj hsub with h | h
        · exact absurd (h hVmem) (fun h0U' => (Set.disjoint_left.mp hU'V'disj) h0U' hV'mem)
        · exact h
      have hV'subV : V' ⊆ V := by
        have hsub : V' ⊆ U ∪ V := fun p hp =>
          hucov p (fun hpk => (Set.disjoint_left.mp hU'V'disj) (hKU' hpk) hp)
        rcases hV'pre.subset_or_subset hUo hVo hUVdisj hsub with h | h
        · exact absurd (h hV'mem) (fun h0U => (Set.disjoint_left.mp hUVdisj) h0U hVmem)
        · exact h
      have heq : V = V' := Subset.antisymm hVsubV' hV'subV
      have hrange : Set.range η = Set.range (fun t : ℝ => -η t) := by
        rw [← hfr, ← hfr', heq]
      exact (Set.disjoint_left.mp hdisjK) ⟨0, rfl⟩ (by rw [← hrange]; exact ⟨0, rfl⟩)
    · -- `K ⊆ V'`, `-K ⊆ U`: the ray through a farthest point of `K` leaves `V'`
      have hpV' : η t₀ ∈ V' := hKV' ⟨t₀, rfl⟩
      have hpne : η t₀ ≠ 0 := h0 t₀
      obtain ⟨s, hsgt, hs⟩ := ray_exit hV'o hV'bd hfr' hpV' hpne
      obtain ⟨t, ht⟩ := hs
      have hnorm : ‖s • ((‖η t₀‖)⁻¹ • (η t₀))‖ = s := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by linarith [hsgt, norm_nonneg (η t₀)])]
        congr 1
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (η t₀)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hpne), mul_one]
      have hle : ‖s • ((‖η t₀‖)⁻¹ • (η t₀))‖ ≤ R := by
        rw [← ht]
        exact hRμ t
      rw [hnorm, hRdef] at hle
      linarith
  · -- `-K ⊆ V`: the ray through a farthest point of `-K` leaves `V`
    have hpV : -(η t₀) ∈ V := hKV ⟨t₀, rfl⟩
    have hpne : -(η t₀) ≠ 0 := neg_ne_zero.mpr (h0 t₀)
    obtain ⟨s, hsgt, hs⟩ := ray_exit hVo hVbd hfr hpV hpne
    obtain ⟨t, ht⟩ := hs
    have hnorm : ‖s • ((‖-(η t₀)‖)⁻¹ • (-(η t₀)))‖ = s := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hsgt, norm_nonneg (-(η t₀))])]
      congr 1
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (-(η t₀))),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hpne), mul_one]
    have hle : ‖s • ((‖-(η t₀)‖)⁻¹ • (-(η t₀)))‖ ≤ R := by
      rw [← ht]
      exact hR t
    rw [hnorm] at hle
    have hpR : ‖-(η t₀)‖ = R := by rw [norm_neg, hRdef]
    linarith

/-! ## The main statement -/

theorem windNumber_eq_zero_or_odd_uncond {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    {z : ℂ} (hz : ∀ t : ℝ, γ t ≠ z) :
    Work.Smooth.SphereJordan.windNumber γ hγ z = 0 ∨
      Odd (Work.Smooth.SphereJordan.windNumber γ hγ z) := by
  by_cases h0 : windNumber γ hγ z = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    by_contra hodd
    obtain ⟨k, hk⟩ : ∃ k : ℤ, windNumber γ hγ z = 2 * k := by
      obtain ⟨j, hj⟩ := Int.not_odd_iff_even.mp hodd
      exact ⟨j, by rw [hj]; ring⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact h0 hk
    obtain ⟨η, hsq, hne, hperη, hwindη⟩ :=
      exists_sqrt_curve_of_even_windNumber hγ hper hz hk
    have hinjη : Set.InjOn (fun t : ℝ => η t) (Set.Ico 0 (2 * Real.pi)) := by
      intro a ha b hb hab
      have h1 : η a * η a = η b * η b := congrArg (fun z : ℂ => z * z) hab
      rw [hsq a, hsq b] at h1
      have hγab : γ a = γ b := by
        have h2 : γ a - z + z = γ b - z + z := congrArg (fun w : ℂ => w + z) h1
        simpa using h2
      obtain ⟨n, hn⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj hγab
      have hlt : |a - b| < 2 * Real.pi := by
        rw [abs_lt]
        exact ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have hnz : n ≠ 0 := by omega
        have h3 : (1 : ℝ) ≤ |(n : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hnz
        have h4 : 2 * Real.pi ≤ |a - b| := by
          rw [hn, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          nlinarith [h3, Real.pi_pos]
        linarith
      · rw [hn0] at hn
        simp only [Int.cast_zero, zero_mul] at hn
        linarith
      · have hnz : n ≠ 0 := by omega
        have h3 : (1 : ℝ) ≤ |(n : ℝ)| := by
          rw [← Int.cast_abs]
          exact_mod_cast Int.one_le_abs hnz
        have h4 : 2 * Real.pi ≤ |a - b| := by
          rw [hn, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
          nlinarith [h3, Real.pi_pos]
        linarith
    have hantiη : ∀ s t : ℝ, η s ≠ -η t := by
      intro s t hst
      have h1 : η s * η s = η t * η t := by rw [hst]; ring
      rw [hsq s, hsq t] at h1
      have hγst : γ s = γ t := by
        have h2 : γ s - z + z = γ t - z + z := congrArg (fun w : ℂ => w + z) h1
        simpa using h2
      obtain ⟨n, hn⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj hγst
      have hs : s = t + (n : ℝ) * (2 * Real.pi) := by linarith [hn]
      have h2 : η s = η t := by
        rw [hs]
        exact (hperη.int_mul n) t
      rw [h2] at hst
      have h3 : η t = 0 := by linear_combination (1 / 2 : ℂ) * hst
      exact hne t h3
    exact false_of_antipodalFree_of_windNumber_ne_zero η.continuous hperη hinjη hne
      (by rw [hwindη]; exact hk0) hantiη

end

end Work.Smooth.SphereJordan
