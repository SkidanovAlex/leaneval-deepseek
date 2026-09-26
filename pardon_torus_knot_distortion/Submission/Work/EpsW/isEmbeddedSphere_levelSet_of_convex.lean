import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.InnermostDisk.isEmbeddedSphere_sphere
import Submission.Work.InnermostDisk.isEmbeddedSphere_image_homeomorph

/-!
# Level sets of coercive convex functions on `ℝ³`

If `g : ℝ³ → ℝ` is convex and continuous and its sublevel set `{g < t}` is nonempty and
bounded, then the level set `{g = t}` is a topological `2`-sphere.

The reason is that `K = {g ≤ t}` is then a compact convex set with nonempty interior and
`frontier K = {g = t}`:

* `K` is convex (`ConvexOn.convex_le`), closed (`isClosed_le`) and bounded, because
  `K ⊆ closure {g < t}` (every `x` with `g x = t` is approached along the segment joining it to
  a point with `g < t`);
* `interior K = {g < t}`: the strict sublevel set is open and contained in `K`, and conversely
  if `g x = t` then the points `x + s • (x - y)` (where `g y < t`) satisfy `g > t` for `s > 0`,
  so such an `x` cannot be interior;
* hence `frontier K = K \ interior K = {g = t}`.

Finally `Mathlib`'s *gauge rescale* homeomorphism
`exists_homeomorph_image_interior_closure_frontier_eq_unitBall` carries `frontier K` to the
round unit sphere of `ℝ³`, and `Work.InnermostDisk.isEmbeddedSphere_image_homeomorph` turns
that into the statement that `{g = t}` is an embedded sphere.
-/

open Set Metric
open LeanEval.KnotTheory.PardonDistortion

namespace Work.EpsW

noncomputable section

/-- The defining inequality of a convex function on all of `ℝ³`, in multiplicative form. -/
private theorem convexOn_apply {g : R3 → ℝ} (hg : ConvexOn ℝ Set.univ g) {p q : R3} {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    g (u • p + v • q) ≤ u * g p + v * g q := by
  have := hg.2 (Set.mem_univ p) (Set.mem_univ q) hu hv huv
  simpa [smul_eq_mul] using this

/-- The sublevel set `{x | g x ≤ t}` of a convex function is convex. -/
theorem convex_setOf_le_of_convexOn {g : R3 → ℝ} (hg : ConvexOn ℝ Set.univ g) (t : ℝ) :
    Convex ℝ {x : R3 | g x ≤ t} := by
  simpa using hg.convex_le t

/-- The closure of the strict sublevel set `{g < t}` of a continuous convex function with
`{g < t}` nonempty is the sublevel set `{g ≤ t}`. -/
theorem closure_setOf_lt_of_convexOn {g : R3 → ℝ} (hg : ConvexOn ℝ Set.univ g)
    (hgc : Continuous g) {t : ℝ} (hne : ∃ x : R3, g x < t) :
    closure {x : R3 | g x < t} = {x : R3 | g x ≤ t} := by
  have hsub : {x : R3 | g x < t} ⊆ {x : R3 | g x ≤ t} := by
    intro x hx
    rw [Set.mem_ofPred_eq] at hx ⊢
    exact le_of_lt hx
  refine Subset.antisymm (closure_minimal hsub (isClosed_le hgc continuous_const)) ?_
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  rw [Set.mem_ofPred_eq] at hx
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact ⟨x, by rw [Set.mem_ofPred_eq]; exact hlt, by simpa using hε⟩
  · obtain ⟨y, hy⟩ := hne
    have hxy : x ≠ y := by intro h; rw [h] at heq; linarith
    have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    set c : ℝ := min (1 / 2) (ε / (2 * ‖x - y‖)) with hcdef
    have hcpos : 0 < c := lt_min (by norm_num) (by positivity)
    have hcle : c ≤ 1 / 2 := min_le_left _ _
    have hc2 : c * ‖x - y‖ < ε := by
      have h1 : c ≤ ε / (2 * ‖x - y‖) := min_le_right _ _
      calc c * ‖x - y‖ ≤ (ε / (2 * ‖x - y‖)) * ‖x - y‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ = ε / 2 := by field_simp
          _ < ε := by linarith
    refine ⟨(1 - c) • x + c • y, ?_, ?_⟩
    · rw [Set.mem_ofPred_eq]
      have hlt' : (1 - c) * g x + c * g y < t := by rw [heq]; nlinarith [hy, hcpos]
      have hle' := convexOn_apply (g := g) hg (p := x) (q := y) (u := 1 - c) (v := c)
        (by linarith) hcpos.le (by ring)
      exact lt_of_le_of_lt hle' hlt'
    · rw [dist_comm, dist_eq_norm]
      have hvec : (1 - c) • x + c • y - x = (-c) • (x - y) := by module
      rw [hvec, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hcpos]
      exact hc2

/-- The interior of the sublevel set `{g ≤ t}` of a continuous convex function with
`{g < t}` nonempty is the strict sublevel set `{g < t}`. -/
theorem interior_setOf_le_of_convexOn {g : R3 → ℝ} (hg : ConvexOn ℝ Set.univ g)
    (hgc : Continuous g) {t : ℝ} (hne : ∃ x : R3, g x < t) :
    interior {x : R3 | g x ≤ t} = {x : R3 | g x < t} := by
  have hsub : {x : R3 | g x < t} ⊆ {x : R3 | g x ≤ t} := by
    intro x hx
    rw [Set.mem_ofPred_eq] at hx ⊢
    exact le_of_lt hx
  refine Subset.antisymm ?_ (interior_maximal hsub (isOpen_lt hgc continuous_const))
  intro x hx
  have hxKmem : x ∈ {x : R3 | g x ≤ t} := interior_subset hx
  have hxK : g x ≤ t := hxKmem
  by_contra hlt
  have hxt : g x = t := le_antisymm hxK (not_lt.mp hlt)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨y, hy⟩ := hne
  have hxy : x ≠ y := by intro h; rw [h] at hxt; linarith
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  set s : ℝ := r / (2 * (‖x - y‖ + 1)) with hsdef
  have hspos : 0 < s := by rw [hsdef]; positivity
  have hslt : s * ‖x - y‖ < r := by
    rw [hsdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hr, norm_nonneg (x - y)]
  set z : R3 := x + s • (x - y) with hzdef
  have hzK : z ∈ {x : R3 | g x ≤ t} := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, hzdef]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    exact hslt
  have hza : (1 / (1 + s)) • z + (s / (1 + s)) • y = x := by
    have hb : (1 / (1 + s)) * s = s / (1 + s) := by field_simp
    have ha : (1 : ℝ) / (1 + s) + s / (1 + s) = 1 := by field_simp
    rw [hzdef, smul_add, smul_smul, hb, smul_sub, add_assoc, sub_add_cancel, ← add_smul, ha,
      one_smul]
  have hs1 : (0 : ℝ) < 1 + s := by linarith
  have ha : (0 : ℝ) ≤ 1 / (1 + s) := div_nonneg zero_le_one hs1.le
  have hbpos : (0 : ℝ) < s / (1 + s) := div_pos hspos hs1
  have hab : (1 : ℝ) / (1 + s) + s / (1 + s) = 1 := by
    rw [← add_div, div_self (ne_of_gt hs1)]
  have hres := hg.le_right_of_left_le' (x := z) (y := y) (a := 1 / (1 + s)) (b := s / (1 + s))
    (Set.mem_univ z) (Set.mem_univ y) ha hbpos hab (by rw [hza, hxt]; exact hzK)
  rw [hza, hxt] at hres
  linarith

/-- The frontier of the sublevel set `{g ≤ t}` of a continuous convex function with
`{g < t}` nonempty is the level set `{g = t}`. -/
theorem frontier_setOf_le_of_convexOn {g : R3 → ℝ} (hg : ConvexOn ℝ Set.univ g)
    (hgc : Continuous g) {t : ℝ} (hne : ∃ x : R3, g x < t) :
    frontier {x : R3 | g x ≤ t} = {x : R3 | g x = t} := by
  have hclosed : IsClosed {x : R3 | g x ≤ t} := isClosed_le hgc continuous_const
  rw [hclosed.frontier_eq, interior_setOf_le_of_convexOn hg hgc hne]
  ext x
  rw [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h1 (not_lt.mp h2)
  · intro h
    exact ⟨le_of_eq h, by rw [h]; exact lt_irrefl t⟩

/-- **The level set of a coercive convex function on `ℝ³` is an embedded `2`-sphere.**

`g` is convex and continuous on all of `ℝ³`; `{g < t}` is nonempty and bounded.  Then
`{g = t}` is the frontier of the compact convex body `{g ≤ t}`, hence the image of the round
`2`-sphere under a homeomorphism. -/
theorem isEmbeddedSphere_levelSet_of_convex {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ}
    (hg : ConvexOn ℝ Set.univ g) (hgc : Continuous g) {t : ℝ}
    (hne : ∃ x : LeanEval.KnotTheory.PardonDistortion.R3, g x < t)
    (hbdd : Bornology.IsBounded {x : LeanEval.KnotTheory.PardonDistortion.R3 | g x < t}) :
    Work.InnermostDisk.IsEmbeddedSphere {x : LeanEval.KnotTheory.PardonDistortion.R3 | g x = t} := by
  have hconv : Convex ℝ {x : R3 | g x ≤ t} := convex_setOf_le_of_convexOn hg t
  have hInt : interior {x : R3 | g x ≤ t} = {x : R3 | g x < t} :=
    interior_setOf_le_of_convexOn hg hgc hne
  have hIne : (interior {x : R3 | g x ≤ t}).Nonempty := by
    rw [hInt]
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, by rw [Set.mem_ofPred_eq]; exact hy⟩
  have hclos : closure {x : R3 | g x < t} = {x : R3 | g x ≤ t} :=
    closure_setOf_lt_of_convexOn hg hgc hne
  have hbddK : Bornology.IsBounded {x : R3 | g x ≤ t} := by
    rw [← hclos]; exact Metric.isBounded_closure_of_isBounded hbdd
  obtain ⟨h, -, -, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hIne hbddK
  have hfront : frontier {x : R3 | g x ≤ t} = {x : R3 | g x = t} :=
    frontier_setOf_le_of_convexOn hg hgc hne
  have hsphere : {x : R3 | g x = t} = h.symm '' Metric.sphere (0 : R3) 1 := by
    rw [← hfront, ← hfr]
    ext x
    constructor
    · intro hx
      exact ⟨h x, ⟨x, hx, rfl⟩, h.symm_apply_apply x⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hx
      obtain ⟨z, hz, hzy⟩ := hy
      rw [← hyx, ← hzy, Homeomorph.symm_apply_apply]
      exact hz
  rw [hsphere]
  exact Work.InnermostDisk.isEmbeddedSphere_image_homeomorph h.symm
    (Work.InnermostDisk.isEmbeddedSphere_sphere (0 : R3) one_pos)

end

end Work.EpsW
