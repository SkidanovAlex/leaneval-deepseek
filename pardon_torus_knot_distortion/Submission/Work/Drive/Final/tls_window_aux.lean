import Mathlib
import Submission.Work.Drive.Final.tls_defs
import Submission.Work.Drive.Mono.FrontierCorner_holds

/-!
# Elementary tools for `Work.Drive.Final.tls_window_dichotomy`

The window dichotomy compares the frontier of one level of the tilted sweep with the box sphere.
This module supplies the elementary half of it: the *interior* of the chunk
`closure (PBox) ∩ slab ∩ wall` is nonempty as soon as the chunk meets the open box.

* `Work.Drive.Final.not_parallel_innerSL` — `ℓ` is not a multiple of `⟪v,·⟫` when `ℓ ≠ 0`,
  `ℓ v = 0`, `v ≠ 0` (the hypothesis under which `ℓ` does not vanish on `ker ⟪v,·⟫`).
* `Work.Drive.Final.interior_closure_PBox` — the interior of the closed box is the open box.
* `Work.Drive.Final.interior_le_level` — the interior of the wall `{ℓ ≤ lam}` is `{ℓ < lam}`.
* `Work.Drive.Final.mem_interior_tlsChunk` — the interior of the chunk contains
  `PBox ∩ {|⟪v,·⟫ - a| < h} ∩ {ℓ < lam}`.
* `Work.Drive.Final.interior_tlsChunk_nonempty_of_point` — a point of the open box in the closed
  slab and below the wall can be pushed (a small move along `±v` and along a direction of
  `ker ⟪v,·⟫` on which `ℓ` decreases) into the interior of the chunk.
-/

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set

namespace Work.Drive.Final

noncomputable section

/-- `ℓ` is not a multiple of `⟪v,·⟫` when `ℓ ≠ 0`, `ℓ v = 0` and `v ≠ 0`. -/
lemma not_parallel_innerSL {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓ : ℓ ≠ 0) : ∀ t : ℝ, ℓ ≠ t • (innerSL ℝ) v := by
  intro t ht
  have h1 : (t • (innerSL ℝ) v) v = 0 := by rw [← ht]; exact hℓv
  rw [smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_eq_mul] at h1
  have h2 : t = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))
  rw [ht, h2, zero_smul] at hℓ
  exact hℓ rfl

/-- **The interior of the closed box is the open box.**  The interior of the closure of a convex
set with nonempty interior is its interior. -/
lemma interior_closure_PBox {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    interior (closure (Submission.PBox s c σ)) = Submission.PBox s c σ := by
  have hcv := Work.Topology.SphereSlicing.convex_PBox s c σ
  have hopen := Work.Topology.SphereSlicing.isOpen_PBox s c σ
  have hne : (interior (Submission.PBox s c σ)).Nonempty := by
    refine ⟨c, ?_⟩
    rw [hopen.interior_eq]
    intro i
    rw [sub_self, abs_zero]
    exact mul_pos (Submission.boxSide_pos i) hs
  rw [hcv.interior_closure_eq_interior_of_nonempty_interior hne, hopen.interior_eq]

/-- **The interior of the wall is the open wall**: `interior {ℓ ≤ lam} = {ℓ < lam}` for a nonzero
linear functional `ℓ`. -/
lemma interior_le_level {ℓ : R3 →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) (lam : ℝ) :
    interior {z : R3 | ℓ z ≤ lam} = {z : R3 | ℓ z < lam} := by
  have h1 : (interior {z : R3 | ℓ z ≤ lam} : Set R3) ⊆ {z : R3 | ℓ z < lam} := by
    intro y hy
    have hy' : y ∈ ({z : R3 | ℓ z ≤ lam} : Set R3) := interior_subset hy
    have hle : ℓ y ≤ lam := hy'
    by_contra hcon
    have hcon' : ¬ ℓ y < lam := hcon
    have heq : ℓ y = lam := le_antisymm hle (not_lt.mp hcon')
    obtain ⟨u, hu⟩ : ∃ u : R3, 0 < ℓ u := by
      obtain ⟨u, hu⟩ : ∃ u : R3, ℓ u ≠ 0 := by
        by_contra h
        exact hℓ (ContinuousLinearMap.ext (by simpa using h))
      rcases lt_or_gt_of_ne hu with h | h
      · exact ⟨-u, by rw [map_neg]; linarith⟩
      · exact ⟨u, h⟩
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
    have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
    set ε : ℝ := min (δ / (2 * (‖u‖ + 1))) 1 with hεdef
    have hεpos : 0 < ε := lt_min (div_pos hδpos (by positivity)) one_pos
    have hεle : ε ≤ δ / (2 * (‖u‖ + 1)) := min_le_left _ _
    have hlt : ‖ε • u‖ < δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hεpos]
      have h2 : (δ / (2 * (‖u‖ + 1))) * ‖u‖ < δ / 2 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * (‖u‖ + 1))]
        nlinarith [hu0, hδpos]
      have h3 : ε * ‖u‖ ≤ (δ / (2 * (‖u‖ + 1))) * ‖u‖ :=
        mul_le_mul_of_nonneg_right hεle hu0
      linarith
    have hmem : y + ε • u ∈ Metric.ball y δ := by
      rw [Metric.mem_ball, dist_eq_norm, show y + ε • u - y = ε • u by abel]
      exact hlt
    have h1' : y + ε • u ∈ ({z : R3 | ℓ z ≤ lam} : Set R3) := hδsub hmem
    have h1'' : ℓ (y + ε • u) ≤ lam := h1'
    have h2 : ℓ (y + ε • u) = lam + ε * ℓ u := by
      rw [map_add, map_smul, smul_eq_mul, heq]
    rw [h2] at h1''
    nlinarith [mul_pos hεpos hu]
  have h3 : ({z : R3 | ℓ z < lam} : Set R3) ⊆ interior {z : R3 | ℓ z ≤ lam} := by
    intro w hw
    refine interior_maximal (fun a ha => ?_) (isOpen_lt ℓ.continuous continuous_const) hw
    have ha' : ℓ a < lam := ha
    show a ∈ ({z : R3 | ℓ z ≤ lam} : Set R3)
    exact le_of_lt ha'
  exact le_antisymm h1 h3

/-- The interior of the chunk contains the open box cut by the open slab and the open wall. -/
lemma mem_interior_tlsChunk {s : ℝ} (hs : 0 < s) {c : R3} {σ : Equiv.Perm (Fin 3)} {u h lam : ℝ}
    {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓ : ℓ ≠ 0) {z : R3}
    (hz : z ∈ Submission.PBox s c σ)
    (hpz : |inner ℝ v z - (inner ℝ v c + u)| < h) (hℓz : ℓ z < lam) :
    z ∈ interior (tlsChunk s c σ u h lam v ℓ) := by
  simp only [tlsChunk, tlsSlab, tlsWall]
  rw [interior_inter, interior_inter, interior_closure_PBox hs c σ,
    Work.Drive.Mono.interior_closedSlab hv (inner ℝ v c + u) h, interior_le_level hℓ lam]
  exact ⟨⟨hz, hpz⟩, hℓz⟩

/-- **A point of the open box in the closed slab and below the wall can be moved into the
interior of the chunk.**  The move is a small displacement along `±v` (to make the slab
inequality strict) followed by a small displacement along a direction of `ker ⟪v,·⟫` on which
`ℓ` decreases (to make the wall inequality strict). -/
lemma interior_tlsChunk_nonempty_of_point {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u h lam : ℝ}
    {v : R3} {ℓ : R3 →L[ℝ] ℝ} (hs : 0 < s) (hh : 0 < h) (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) {z : R3} (hz : z ∈ Submission.PBox s c σ)
    (hpz : |inner ℝ v z - (inner ℝ v c + u)| ≤ h) (hℓz : ℓ z ≤ lam) :
    (interior (tlsChunk s c σ u h lam v ℓ)).Nonempty := by
  -- a direction of `ker ⟪v,·⟫` on which `ℓ` decreases
  obtain ⟨w, hwv, hwℓ⟩ :=
    Work.Drive.Mono.exists_ker_inner_ne hv (not_parallel_innerSL hv hℓv hℓne)
  -- a ball around `z` inside the open box
  obtain ⟨δ, hδpos, hδball⟩ :=
    Metric.mem_nhds_iff.mp ((Work.Topology.SphereSlicing.isOpen_PBox s c σ).mem_nhds hz)
  have hδ4 : (0 : ℝ) < δ / 4 := by linarith
  have hvpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  have hv2 : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  -- step along `v`
  set cc : ℝ := min (h / (2 * ‖v‖ ^ 2)) (δ / (4 * ‖v‖)) with hcc
  have hccpos : 0 < cc :=
    lt_min (div_pos hh (by positivity)) (div_pos hδpos (by positivity))
  have hcch : cc * ‖v‖ ^ 2 ≤ h / 2 := by
    have h1 : cc ≤ h / (2 * ‖v‖ ^ 2) := min_le_left _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hv2)
    have h3 : (h / (2 * ‖v‖ ^ 2)) * ‖v‖ ^ 2 = h / 2 := by field_simp
    linarith
  have hccn : cc * ‖v‖ ≤ δ / 4 := by
    have h1 : cc ≤ δ / (4 * ‖v‖) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hvpos)
    have h3 : (δ / (4 * ‖v‖)) * ‖v‖ = δ / 4 := by field_simp
    linarith
  -- step along `w`
  set dd : ℝ := min (1 / 2) (δ / (4 * (‖w‖ + 1))) with hdd
  have hddpos : 0 < dd := lt_min (by norm_num) (div_pos hδpos (by positivity))
  have hddle : dd ≤ δ / (4 * (‖w‖ + 1)) := min_le_right _ _
  have hwd : ‖dd • w‖ ≤ δ / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hddpos]
    calc dd * ‖w‖ ≤ (δ / (4 * (‖w‖ + 1))) * ‖w‖ :=
          mul_le_mul_of_nonneg_right hddle (norm_nonneg w)
      _ = δ * ‖w‖ / (4 * (‖w‖ + 1)) := by rw [div_mul_eq_mul_div]
      _ ≤ δ / 4 := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (‖w‖ + 1))]
          nlinarith [norm_nonneg w, hδpos]
  -- the two moves fit in the ball
  have hball : ∀ e : R3, ‖e‖ < δ → z + e ∈ Submission.PBox s c σ := by
    intro e he
    refine hδball ?_
    rw [Metric.mem_ball, dist_eq_norm, show z + e - z = e by abel]
    exact he
  -- the displacement along `v`, chosen so that the slab inequality becomes strict
  have ht : ∃ t : ℝ, |t| * ‖v‖ ≤ δ / 4 ∧
      |inner ℝ v z + t * ‖v‖ ^ 2 - (inner ℝ v c + u)| < h := by
    rcases lt_or_eq_of_le hpz with hlt | heq
    · exact ⟨0, by simp only [abs_zero, zero_mul]; linarith, by simpa using hlt⟩
    · rcases (abs_eq (le_trans (abs_nonneg _) hpz)).mp heq with hcase | hcase
      · refine ⟨-cc, ?_, ?_⟩
        · rw [abs_neg, abs_of_pos hccpos]; exact hccn
        · have h1 : inner ℝ v z + -cc * ‖v‖ ^ 2 - (inner ℝ v c + u) = h - cc * ‖v‖ ^ 2 := by
            linarith [hcase]
          rw [h1, abs_of_pos (by linarith [hcch, hh, hccpos, hv2])]
          have hpos : 0 < cc * ‖v‖ ^ 2 := mul_pos hccpos hv2
          linarith
      · refine ⟨cc, ?_, ?_⟩
        · rw [abs_of_pos hccpos]; exact hccn
        · have h1 : inner ℝ v z + cc * ‖v‖ ^ 2 - (inner ℝ v c + u) = cc * ‖v‖ ^ 2 - h := by
            linarith [hcase]
          rw [h1, abs_of_neg (by linarith [hcch, hh, hccpos, hv2])]
          have hpos : 0 < cc * ‖v‖ ^ 2 := mul_pos hccpos hv2
          linarith
  obtain ⟨t, htle, htp⟩ := ht
  -- the moved point
  have hnorm : ‖t • v + dd • w‖ < δ := by
    have h1 : ‖t • v + dd • w‖ ≤ ‖t • v‖ + ‖dd • w‖ := norm_add_le _ _
    rw [norm_smul, Real.norm_eq_abs] at h1
    linarith
  have hmem : z + (t • v + dd • w) ∈ Submission.PBox s c σ := hball _ hnorm
  have hpz' : |inner ℝ v (z + (t • v + dd • w)) - (inner ℝ v c + u)| < h := by
    have hlin : inner ℝ v (z + (t • v + dd • w)) = inner ℝ v z + t * ‖v‖ ^ 2 := by
      simp only [inner_add_right, real_inner_smul_right, hwv, mul_zero, add_zero,
        real_inner_self_eq_norm_sq]
    rw [hlin]
    exact htp
  have hℓz' : ℓ (z + (t • v + dd • w)) < lam := by
    have hlin : ℓ (z + (t • v + dd • w)) = ℓ z + (t * ℓ v + dd * ℓ w) := by
      rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hlin, hℓv, mul_zero, zero_add]
    linarith [mul_neg_of_pos_of_neg hddpos hwℓ, hℓz]
  exact ⟨z + (t • v + dd • w), mem_interior_tlsChunk hs hv hℓne hmem hpz' hℓz'⟩

end

end Work.Drive.Final
