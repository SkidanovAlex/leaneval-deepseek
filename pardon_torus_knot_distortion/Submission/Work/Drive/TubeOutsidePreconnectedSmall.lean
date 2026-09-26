import Mathlib
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.annulusPreconnected
import Submission.Work.SphereJordan.exteriorGermOfPlaneSchoenflies
import Submission.Work.Drive.TubeOutsideAux

/-!
# The outward tube of a plane Jordan curve is preconnected

For a simple closed plane curve `c : PlaneCurve` together with a Jordan–Schoenflies datum
`S : PlaneSchoenflies c` (`S.U` the unbounded side, `S.V` the bounded side, `closure S.V` the
closed disc bounded by the curve) and a radius `r > 0`, the *outward tube*

`tubeOutside c S r = {z : ℂ | Metric.infDist z (Set.range c.γ) < r ∧ z ∉ closure S.V}`

— the points outside the closed disc at distance `< r` from the trace — is preconnected.

In fact the tube is preconnected for *every* `r > 0` (`tubeOutside_preconnected`), so the statement
as requested holds with any positive `r₀`.

## Route

* `tubeOutside_germ` is the local connectedness of the exterior at a trace point: the germ lemma
  `Work.SphereJordan.exteriorGermOfPlaneSchoenflies` states that for every `ε > 0` the part of the
  unbounded side in a small ball around a trace point lies in a *single* component of the part in
  the `ε`-ball; taking `ε = r` turns this into the statement that the points of the tube in a small
  ball around a trace point all lie in a single component of the tube.
* `tubeOutside_accumulates`: the tube accumulates at every trace point (the trace is the frontier of
  `S.V`, and no trace point is interior to `closure S.V`).
* `tubeOutside_segment` / `tubeOutside_segment_close`: for a point `z` of the tube and a nearest
  trace point `q`, the open segment from `z` to `q` stays in the tube (a segment from `z`, which is
  outside the closed disc, to a point of `S.V` would cross the frontier `= trace`, giving a trace
  point strictly closer to `z` than `q`).
* With these, every component of the tube accumulates at a trace point, and by the germ property two
  components accumulating at the same trace point coincide.  The set of trace points whose local
  germ lies in the component of a fixed base point is open (`tubeOutside_germ`) and closed
  (`tubeOutside_accumulates`), and the trace is preconnected, so it is everything; every point of
  the tube then lies in that single component.
-/

namespace Work.Drive

open Set Metric

noncomputable section

variable {c : Work.Smooth.Jordan.PlaneCurve}

/-- **Accumulation.**  The outward tube meets every neighbourhood of every trace point. -/
theorem tubeOutside_accumulates (c : Work.Smooth.Jordan.PlaneCurve)
    (S : Work.Smooth.Jordan.PlaneSchoenflies c) {r : ℝ} (hr : 0 < r) {q : ℂ}
    (hq : q ∈ Set.range c.γ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ z : ℂ, z ∈ tubeOutside c S r ∧ dist z q < ρ := by
  have hqV : q ∉ S.V := by
    intro hV
    have h2 : q ∈ S.U ∪ S.V := Or.inr hV
    rw [S.toPlaneSeparation.union_eq] at h2
    exact h2 hq
  have hqint : q ∉ interior (closure S.V) := by
    rwa [Work.Smooth.SphereJordan.interior_closure_V_eq S]
  have hnear : ∃ y : ℂ, y ∉ closure S.V ∧ dist y q < min ρ r := by
    have hnotsub : ¬ (Metric.ball q (min ρ r) ⊆ closure S.V) := by
      intro hsub
      exact hqint (mem_interior_iff_mem_nhds.mpr
        (Metric.mem_nhds_iff.mpr ⟨min ρ r, lt_min hρ hr, hsub⟩))
    obtain ⟨y, hyb, hyc⟩ := Set.not_subset.mp hnotsub
    exact ⟨y, hyc, Metric.mem_ball.mp hyb⟩
  obtain ⟨y, hyc, hyd⟩ := hnear
  refine ⟨y, ⟨?_, hyc⟩, lt_of_lt_of_le hyd (min_le_left _ _)⟩
  rw [Metric.infDist_lt_iff (s := Set.range c.γ) ⟨c.γ 0, ⟨0, rfl⟩⟩]
  exact ⟨q, hq, lt_of_lt_of_le hyd (min_le_right _ _)⟩

/-- **The open segment to a nearest trace point stays in the tube.** -/
theorem tubeOutside_segment (c : Work.Smooth.Jordan.PlaneCurve)
    (S : Work.Smooth.Jordan.PlaneSchoenflies c) {r : ℝ} {z q : ℂ}
    (hz : z ∈ tubeOutside c S r) (hq : q ∈ Set.range c.γ)
    (hdist : Metric.infDist z (Set.range c.γ) = dist z q) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    z + t • (q - z) ∈ tubeOutside c S r := by
  set w : ℂ := z + t • (q - z) with hw
  have hzVc : z ∉ closure S.V := ((mem_tubeOutside S r z).mp hz).2
  have hzP : z ∉ Set.range c.γ := fun h => hzVc (trace_subset_closure_V S h)
  have hzC : Metric.infDist z (Set.range c.γ) < r := ((mem_tubeOutside S r z).mp hz).1
  have hcl : closure (Set.range c.γ) = Set.range c.γ := c.isCompact_trace.isClosed.closure_eq
  have hdpos : 0 < dist z q := by
    rw [← hdist]
    have hzcl : z ∉ closure (Set.range c.γ) := by rw [hcl]; exact hzP
    exact (Metric.infDist_pos_iff_notMem_closure (s := Set.range c.γ)
      ⟨c.γ 0, ⟨0, rfl⟩⟩).mp hzcl
  have hwd : dist z w < dist z q := by
    have h1 : w - z = t • (q - z) := by rw [hw]; ring
    have h2 : dist z w = t * dist z q := by
      rw [dist_eq_norm, norm_sub_rev, h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0,
        norm_sub_rev, dist_eq_norm]
    rw [h2]
    exact mul_lt_of_lt_one_left hdpos ht1
  have hwP : w ∉ Set.range c.γ := by
    intro hwP
    have h1 : Metric.infDist z (Set.range c.γ) ≤ dist z w := Metric.infDist_le_dist_of_mem hwP
    rw [hdist] at h1
    exact absurd hwd (not_lt.mpr h1)
  have hwV : w ∉ S.V := by
    intro hwV
    have hcont : Continuous (fun a : ℝ => z + a • (w - z)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hpre : IsPreconnected ((fun a : ℝ => z + a • (w - z)) '' Set.Icc (0 : ℝ) 1) :=
      isPreconnected_Icc.image _ hcont.continuousOn
    have h1 : (((fun a : ℝ => z + a • (w - z)) '' Set.Icc (0 : ℝ) 1) ∩ S.V).Nonempty := by
      refine ⟨w, ⟨?_, hwV⟩⟩
      exact ⟨1, ⟨zero_le_one, le_rfl⟩, by
        change z + (1 : ℝ) • (w - z) = w
        rw [one_smul]; abel⟩
    have h2 : (((fun a : ℝ => z + a • (w - z)) '' Set.Icc (0 : ℝ) 1) ∩ (S.V)ᶜ).Nonempty := by
      refine ⟨z, ⟨?_, ?_⟩⟩
      · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by
          change z + (0 : ℝ) • (w - z) = z
          rw [zero_smul, add_zero]⟩
      · exact fun hV => hzVc (subset_closure hV)
    obtain ⟨u, hu, hufr⟩ := nonempty_inter_frontier_of_preconnected hpre h1 h2
    obtain ⟨a, ha, hua⟩ := hu
    have huP : u ∈ Set.range c.γ := frontier_subset_trace S hufr
    have hle : dist z u ≤ dist z w := by
      rw [← hua]
      have h3 : z + a • (w - z) - z = a • (w - z) := by ring
      have h4 : dist z (z + a • (w - z)) = a * dist z w := by
        rw [dist_eq_norm, norm_sub_rev, h3, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1,
          norm_sub_rev, dist_eq_norm]
      rw [h4]
      calc a * dist z w ≤ 1 * dist z w := mul_le_mul_of_nonneg_right ha.2 dist_nonneg
        _ = dist z w := one_mul _
    have h5 : Metric.infDist z (Set.range c.γ) ≤ dist z u := Metric.infDist_le_dist_of_mem huP
    rw [hdist] at h5
    exact absurd hwd (not_lt.mpr (le_trans h5 hle))
  refine ⟨?_, ?_⟩
  · rw [Metric.infDist_lt_iff (s := Set.range c.γ) ⟨c.γ 0, ⟨0, rfl⟩⟩]
    refine ⟨q, hq, ?_⟩
    have h2 : dist w q = (1 - t) * dist z q := by
      rw [hw]
      have h1 : z + t • (q - z) - q = (1 - t) • (z - q) := by
        have h2 : z + t • (q - z) - q = (z - q) - t • (z - q) := by
          rw [show q - z = -(z - q) by ring, smul_neg]
          abel
        have h3 : (z - q) - t • (z - q) = (1 : ℝ) • (z - q) - t • (z - q) := by rw [one_smul]
        rw [h2, h3]
        exact (sub_smul 1 t (z - q)).symm
      rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t), dist_eq_norm]
    rw [h2]
    calc (1 - t) * dist z q ≤ 1 * dist z q := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ = dist z q := one_mul _
      _ < r := by rw [← hdist]; exact hzC
  · intro hclw
    rw [Work.Smooth.SphereJordan.closure_V_eq S] at hclw
    rcases hclw with h | h
    · exact hwV h
    · exact hwP h

/-- **The germ of the tube at a trace point.**  Any two points of the tube sufficiently close to a
trace point lie in a single component of the tube. -/
theorem tubeOutside_germ (c : Work.Smooth.Jordan.PlaneCurve)
    (S : Work.Smooth.Jordan.PlaneSchoenflies c) {r : ℝ} (hr : 0 < r) :
    ∀ q ∈ Set.range c.γ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ x y : ℂ,
      x ∈ tubeOutside c S r → y ∈ tubeOutside c S r →
      dist x q < ρ → dist y q < ρ →
        y ∈ connectedComponentIn (tubeOutside c S r) x := by
  intro q hq
  obtain ⟨θ₀, rfl⟩ := hq
  obtain ⟨ρ, hρ0, _hρr, hρ⟩ :=
    Work.SphereJordan.exteriorGermOfPlaneSchoenflies (γ := c) S (θ₀ := θ₀) (ε := r) hr
  refine ⟨ρ, hρ0, ?_⟩
  intro x y hx hy hxq hyq
  have hsub : Metric.ball (c.γ θ₀) r ∩ S.U ⊆ tubeOutside c S r := by
    rintro z ⟨hzb, hzU⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.infDist_lt_iff (s := Set.range c.γ) ⟨c.γ 0, ⟨0, rfl⟩⟩]
      exact ⟨c.γ θ₀, ⟨θ₀, rfl⟩, Metric.mem_ball.mp hzb⟩
    · rw [unboundedSide_eq_compl S] at hzU; exact hzU
  have hx' : x ∈ Metric.ball (c.γ θ₀) ρ ∩ S.U :=
    ⟨hxq, by rw [unboundedSide_eq_compl S]; exact ((mem_tubeOutside S r x).mp hx).2⟩
  have hy' : y ∈ Metric.ball (c.γ θ₀) ρ ∩ S.U :=
    ⟨hyq, by rw [unboundedSide_eq_compl S]; exact ((mem_tubeOutside S r y).mp hy).2⟩
  exact connectedComponentIn_mono x hsub (hρ x hx' hy')

/-- A point of the tube on the segment from `z` to its nearest trace point `q`, within `ρ` of `q`,
and connected to `z` inside the tube. -/
theorem tubeOutside_segment_close (c : Work.Smooth.Jordan.PlaneCurve)
    (S : Work.Smooth.Jordan.PlaneSchoenflies c) {r : ℝ} {z q : ℂ}
    (hz : z ∈ tubeOutside c S r) (hq : q ∈ Set.range c.γ)
    (hdist : Metric.infDist z (Set.range c.γ) = dist z q) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ w ∈ tubeOutside c S r, dist w q < ρ ∧ z ∈ connectedComponentIn (tubeOutside c S r) w := by
  have hzP : z ∉ Set.range c.γ := fun h =>
    ((mem_tubeOutside S r z).mp hz).2 (trace_subset_closure_V S h)
  have hcl : closure (Set.range c.γ) = Set.range c.γ := c.isCompact_trace.isClosed.closure_eq
  have hdpos : 0 < dist z q := by
    rw [← hdist]
    have hzcl : z ∉ closure (Set.range c.γ) := by rw [hcl]; exact hzP
    exact (Metric.infDist_pos_iff_notMem_closure (s := Set.range c.γ)
      ⟨c.γ 0, ⟨0, rfl⟩⟩).mp hzcl
  set d : ℝ := dist z q with hd
  have hdne : d ≠ 0 := ne_of_gt hdpos
  set t : ℝ := 1 - min ρ d / (2 * d) with ht
  have ht0 : 0 ≤ t := by
    have h1 : min ρ d ≤ d := min_le_right _ _
    have h2 : min ρ d / (2 * d) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * d)]
      linarith
    rw [ht]; linarith
  have ht1 : t < 1 := by
    have h1 : 0 < min ρ d := lt_min hρ hdpos
    have h2 : 0 < min ρ d / (2 * d) := div_pos h1 (by linarith)
    rw [ht]; linarith
  have hwA : z + t • (q - z) ∈ tubeOutside c S r := tubeOutside_segment c S hz hq hdist ht0 ht1
  refine ⟨z + t • (q - z), hwA, ?_, ?_⟩
  · have h1 : z + t • (q - z) - q = (1 - t) • (z - q) := by
      have h2 : z + t • (q - z) - q = (z - q) - t • (z - q) := by
        rw [show q - z = -(z - q) by ring, smul_neg]
        abel
      have h3 : (z - q) - t • (z - q) = (1 : ℝ) • (z - q) - t • (z - q) := by rw [one_smul]
      rw [h2, h3]
      exact (sub_smul 1 t (z - q)).symm
    have h2 : dist (z + t • (q - z)) q = (1 - t) * d := by
      rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t), hd, dist_eq_norm]
    have h3 : (1 - t) * d = min ρ d / 2 := by
      rw [ht]; field_simp; ring
    rw [h2, h3]
    have h4 : min ρ d / 2 < ρ := by
      have h5 : min ρ d ≤ ρ := min_le_left _ _
      linarith
    exact h4
  · have hcont : Continuous (fun a : ℝ => z + a • (q - z)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hpre : IsPreconnected ((fun a : ℝ => z + a • (q - z)) '' Set.Icc (0 : ℝ) t) :=
      isPreconnected_Icc.image _ hcont.continuousOn
    have hsub : (fun a : ℝ => z + a • (q - z)) '' Set.Icc (0 : ℝ) t ⊆ tubeOutside c S r := by
      rintro _ ⟨a, ha, rfl⟩
      exact tubeOutside_segment c S hz hq hdist ha.1 (lt_of_le_of_lt ha.2 ht1)
    have hmem : z + t • (q - z) ∈ (fun a : ℝ => z + a • (q - z)) '' Set.Icc (0 : ℝ) t := by
      refine ⟨t, ⟨ht0, le_rfl⟩, ?_⟩
      rfl
    have hzmem : z ∈ (fun a : ℝ => z + a • (q - z)) '' Set.Icc (0 : ℝ) t := by
      refine ⟨0, ⟨le_rfl, ht0⟩, ?_⟩
      change z + (0 : ℝ) • (q - z) = z
      rw [zero_smul, add_zero]
    exact IsPreconnected.subset_connectedComponentIn hpre hmem hsub hzmem

/-- A subset of a preconnected set that is open and closed in it, and nonempty, is everything. -/
theorem preconnected_clopen {P Sset : Set ℂ} (hP : IsPreconnected P) (hSP : Sset ⊆ P)
    (hopen : ∀ q ∈ Sset, ∃ δ : ℝ, 0 < δ ∧ ∀ q' ∈ P, dist q' q < δ → q' ∈ Sset)
    (hclosed : ∀ q ∈ P, (∀ δ : ℝ, 0 < δ → ∃ q' ∈ Sset, dist q' q < δ) → q ∈ Sset)
    (hne : Sset.Nonempty) : P ⊆ Sset := by
  have h1 : P ∩ closure Sset ⊆ Sset := by
    intro q ⟨hqP, hqcl⟩
    exact hclosed q hqP (fun δ hδ => by
      obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp hqcl δ hδ
      exact ⟨b, hb, by rwa [dist_comm]⟩)
  have h2 : P ∩ closure (P \ Sset) ⊆ P \ Sset := by
    rintro q ⟨hqP, hqcl⟩
    refine ⟨hqP, fun hqS => ?_⟩
    obtain ⟨δ, hδ0, hδ⟩ := hopen q hqS
    obtain ⟨q', hq', hd⟩ := Metric.mem_closure_iff.mp hqcl δ hδ0
    exact hq'.2 (hδ q' hq'.1 (by rwa [dist_comm]))
  have hcover : P ⊆ closure Sset ∪ closure (P \ Sset) := by
    intro q hq
    by_cases h : q ∈ Sset
    · exact Or.inl (subset_closure h)
    · exact Or.inr (subset_closure ⟨hq, h⟩)
  have hdisj : P ∩ (closure Sset ∩ closure (P \ Sset)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hqP, hq1, hq2⟩
    exact (h2 ⟨hqP, hq2⟩).2 (h1 ⟨hqP, hq1⟩)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hP) (closure Sset) (closure (P \ Sset))
      isClosed_closure isClosed_closure hcover hdisj with h | h
  · intro q hqP
    exact h1 ⟨hqP, h hqP⟩
  · exfalso
    obtain ⟨q, hqS⟩ := hne
    have hqP : q ∈ P := hSP hqS
    exact (h2 ⟨hqP, h hqP⟩).2 hqS

/-- **The outward tube is preconnected, for every positive radius.** -/
theorem tubeOutside_preconnected (c : Work.Smooth.Jordan.PlaneCurve)
    (S : Work.Smooth.Jordan.PlaneSchoenflies c) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (tubeOutside c S r) := by
  classical
  set F : Set ℂ := tubeOutside c S r with hF
  have hgerm : ∀ q ∈ Set.range c.γ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ x y : ℂ,
      x ∈ F → y ∈ F → dist x q < ρ → dist y q < ρ → y ∈ connectedComponentIn F x :=
    tubeOutside_germ c S hr
  have hacc : ∀ q ∈ Set.range c.γ, ∀ ρ : ℝ, 0 < ρ → ∃ z : ℂ, z ∈ F ∧ dist z q < ρ := by
    intro q hq ρ hρ
    obtain ⟨z, hz, hd⟩ := tubeOutside_accumulates c S hr hq hρ
    exact ⟨z, hz, hd⟩
  by_cases hne : F.Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    set C : Set ℂ := connectedComponentIn F z₀ with hC
    set Sset : Set ℂ := {q : ℂ | q ∈ Set.range c.γ ∧ ∃ ρ : ℝ, 0 < ρ ∧
        (∀ x y : ℂ, x ∈ F → y ∈ F → dist x q < ρ → dist y q < ρ → y ∈ connectedComponentIn F x) ∧
        (∀ x : ℂ, x ∈ F → dist x q < ρ → x ∈ C)} with hSset
    have hSsub : Sset ⊆ Set.range c.γ := fun q hq => hq.1
    have hopen : ∀ q ∈ Sset, ∃ δ : ℝ, 0 < δ ∧ ∀ q' ∈ Set.range c.γ, dist q' q < δ → q' ∈ Sset := by
      rintro q ⟨hqP, ρ, hρ0, hgood, hCsub⟩
      refine ⟨ρ / 2, by linarith, ?_⟩
      intro q' hq'P hd
      obtain ⟨ρ', hρ'0, hgood'⟩ := hgerm q' hq'P
      set ρ'' : ℝ := min ρ' (ρ / 2) with hρ''
      have hρ''0 : 0 < ρ'' := lt_min hρ'0 (by linarith)
      have hρ''le : ρ'' ≤ ρ / 2 := min_le_right _ _
      have hρ''le' : ρ'' ≤ ρ' := by rw [hρ'']; exact min_le_left _ _
      refine ⟨hq'P, ρ'', hρ''0, ?_, ?_⟩
      · intro x y hx hy hxq hyq
        exact hgood' x y hx hy (lt_of_lt_of_le hxq hρ''le') (lt_of_lt_of_le hyq hρ''le')
      · intro x hx hxq
        have h3 : dist x q < ρ := by
          calc dist x q ≤ dist x q' + dist q' q := dist_triangle _ _ _
            _ < ρ'' + ρ / 2 := add_lt_add_of_lt_of_lt hxq hd
            _ ≤ ρ / 2 + ρ / 2 := by linarith [hρ''le]
            _ = ρ := by ring
        exact hCsub x hx h3
    have hclosed : ∀ q ∈ Set.range c.γ,
        (∀ δ : ℝ, 0 < δ → ∃ q' ∈ Sset, dist q' q < δ) → q ∈ Sset := by
      intro q hqP hlim
      obtain ⟨ρ, hρ0, hgood⟩ := hgerm q hqP
      obtain ⟨q', ⟨hq'P, ρ', hρ'0, hgood', hCsub'⟩, hdqq'⟩ := hlim (ρ / 2) (by linarith)
      set ρ'' : ℝ := min ρ' (ρ / 2) with hρ''
      have hρ''0 : 0 < ρ'' := lt_min hρ'0 (by linarith)
      have hρ''le : ρ'' ≤ ρ / 2 := min_le_right _ _
      have hρ''le' : ρ'' ≤ ρ' := by rw [hρ'']; exact min_le_left _ _
      obtain ⟨z, hzF, hzd⟩ := hacc q' hq'P ρ'' hρ''0
      have hzC : z ∈ C := hCsub' z hzF (lt_of_lt_of_le hzd hρ''le')
      have hzq : dist z q < ρ := by
        calc dist z q ≤ dist z q' + dist q' q := dist_triangle _ _ _
          _ < ρ'' + ρ / 2 := add_lt_add_of_lt_of_lt hzd hdqq'
          _ ≤ ρ / 2 + ρ / 2 := by linarith [hρ''le]
          _ = ρ := by ring
      refine ⟨hqP, ρ, hρ0, hgood, ?_⟩
      intro x hxF hxq
      have h1 : connectedComponentIn F x = connectedComponentIn F z := by
        rw [connectedComponentIn_eq_of_mem hxF (hgood x z hxF hzF hxq hzq)]
      have h2 : connectedComponentIn F z = C := connectedComponentIn_eq_of_mem hz₀ hzC
      have h3 : connectedComponentIn F x = C := by rw [h1, h2]
      rw [← h3]
      exact mem_connectedComponentIn hxF
    have hSne : Sset.Nonempty := by
      obtain ⟨q, hqP, hdist⟩ := exists_nearest_of_compact c z₀
      obtain ⟨ρ, hρ0, hgood⟩ := hgerm q hqP
      obtain ⟨w, hwF, hwq, hz₀w⟩ := tubeOutside_segment_close c S hz₀ hqP hdist hρ0
      have hcomp : connectedComponentIn F w = C := by
        rw [hC]
        exact (connectedComponentIn_eq_of_mem hwF hz₀w).symm
      refine ⟨q, hqP, ρ, hρ0, hgood, ?_⟩
      intro x hxF hxq
      have h1 : connectedComponentIn F x = connectedComponentIn F w := by
        rw [connectedComponentIn_eq_of_mem hxF (hgood x w hxF hwF hxq hwq)]
      have h3 : connectedComponentIn F x = C := by rw [h1, hcomp]
      rw [← h3]
      exact mem_connectedComponentIn hxF
    have hPsub : Set.range c.γ ⊆ Sset :=
      preconnected_clopen (isPreconnected_range_of_curve c) hSsub hopen hclosed hSne
    have hsubC : F ⊆ C := by
      intro x hxF
      obtain ⟨q, hqP, hdist⟩ := exists_nearest_of_compact c x
      have hqS := hPsub hqP
      obtain ⟨ρ, hρ0, _hgood, hCsub⟩ := hqS.2
      obtain ⟨w, hwF, hwq, hxw⟩ := tubeOutside_segment_close c S hxF hqP hdist hρ0
      have hwC : w ∈ C := hCsub w hwF hwq
      have h1 : connectedComponentIn F w = connectedComponentIn F x :=
        (connectedComponentIn_eq_of_mem hwF hxw).symm
      have h2 : connectedComponentIn F w = C := connectedComponentIn_eq_of_mem hz₀ hwC
      have h3 : connectedComponentIn F x = C := by rw [← h1, h2]
      rw [← h3]
      exact mem_connectedComponentIn hxF
    have hFC : F = C := Set.Subset.antisymm hsubC (connectedComponentIn_subset F z₀)
    rw [hFC]
    exact isPreconnected_connectedComponentIn
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact isPreconnected_empty

/-- **Pardon's outward-tube lemma.**  For a simple closed plane curve with a Jordan–Schoenflies
datum, the outward tube of radius below some positive `r₀` is preconnected.  (The proof gives the
stronger statement that the tube is preconnected for *every* positive radius.) -/
theorem TubeOutsidePreconnectedSmall (c : Work.Smooth.Jordan.PlaneCurve)
    (S : Work.Smooth.Jordan.PlaneSchoenflies c) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      IsPreconnected {z : ℂ | Metric.infDist z (Set.range c.γ) < r ∧ z ∉ closure S.V} :=
  ⟨1, one_pos, fun _ hr _ => tubeOutside_preconnected c S hr⟩

end

end Work.Drive
