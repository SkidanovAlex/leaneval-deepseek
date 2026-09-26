import Mathlib
import Submission.Work.Drive.Prelude

/-!
# Non-degenerate limits of quadrisecants

`Work.Drive.quadrisecantChord_of_tendsto_quadrisecants`: if a sequence of
smooth knots `r' n` converges uniformly (on the whole line, hence on the
parameter circle) to a smooth knot `r`, and each `r' n` has a quadrisecant
chord with parameters `(an n, bn n, zn n, wn n)` converging to a
**pairwise-distinct** limit quadruple `(a, b, z, w)`, then `r` itself has the
quadrisecant chord `(a, b, z, w)`: the two middle points `z, w` are strictly
inside the chord from `a` to `b`.

This is the *non-degenerate* half of the compactness argument in Kuperberg's
proof (the half that is actually true: degenerating limits may collapse two
parameters and then carry no information, cf. `Submission/QuadrisecantLimit.lean`).

The three elementary ingredients, all proved here:

* `qrc_uniform_knotMap_dist` — uniform convergence of `r' n → r` on `ℝ`
  descends to the parameter circle `AddCircle period` (via the representatives
  in `Ico 0 period` and `knotMap_eq_r`);
* `qrc_tendsto_knotMap` — hence `knotMap (r' n) (X n) → knotMap r x` whenever
  `X n → x`;
* `qrc_isMiddleOnChord_of_tendsto` — the strict middle condition survives the
  limit once the limiting parameters stay distinct: strict middle points are
  closed ("`z` lies on the closed chord" is the equality case of the triangle
  inequality, `dist_add_dist_eq_iff`, and so is closed under limits), and a
  point of the closed chord different from both endpoints lies in the **open**
  chord (`mem_openSegment_of_ne_left_right`, endpoints separated by injectivity
  of `knotMap r`).
-/

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Topology

namespace Work.Drive

/-- Uniform convergence of the curves on `ℝ` gives uniform convergence of the
induced maps on the parameter circle: the circle is covered by the
representatives in `Ico 0 period`, and `knotMap r` at the class of such a
representative is `r` there (`knotMap_eq_r`). -/
lemma qrc_uniform_knotMap_dist {r : ℝ → Space} (hr : IsSmoothKnot r)
    {r' : ℕ → ℝ → Space} (hr' : ∀ n, IsSmoothKnot (r' n))
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ t : ℝ, dist (r' n t) (r t) < δ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop, ∀ x : KnotParam, dist (knotMap (r' n) x) (knotMap r x) < δ := by
  filter_upwards [hconv δ hδ] with n hn
  intro x
  rcases knotMap_representative x with ⟨t, ht, hx⟩
  rw [← hx, knotMap_eq_r (hr' n) t, knotMap_eq_r hr t]
  exact hn t

/-- Pointwise convergence on the parameter circle: the induced knot maps of a
uniformly convergent sequence of curves converge at every convergent family of
circle parameters.  Split the distance through the intermediate point
`knotMap r (X n)` (triangle inequality): the first term is controlled by the
uniform convergence on the circle, the second by continuity of `knotMap r`. -/
lemma qrc_tendsto_knotMap {r : ℝ → Space} (hr : IsSmoothKnot r)
    {r' : ℕ → ℝ → Space} (hr' : ∀ n, IsSmoothKnot (r' n))
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ t : ℝ, dist (r' n t) (r t) < δ)
    {X : ℕ → KnotParam} {x : KnotParam}
    (hX : Tendsto X atTop (nhds x)) :
    Tendsto (fun n => knotMap (r' n) (X n)) atTop (nhds (knotMap r x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / 2 := by linarith
  have h1 : ∀ᶠ n in atTop,
      dist (knotMap (r' n) (X n)) (knotMap r (X n)) < ε / 2 := by
    filter_upwards [qrc_uniform_knotMap_dist hr hr' hconv hδ] with n hn
    exact hn (X n)
  have h2t : Tendsto (fun n => knotMap r (X n)) atTop (nhds (knotMap r x)) :=
    (hr.knotMap_continuous.tendsto x).comp hX
  have h2 : ∀ᶠ n in atTop, dist (knotMap r (X n)) (knotMap r x) < ε / 2 :=
    (Metric.tendsto_nhds.mp h2t) (ε / 2) hδ
  filter_upwards [h1, h2] with n hn1 hn2
  calc dist (knotMap (r' n) (X n)) (knotMap r x)
      ≤ dist (knotMap (r' n) (X n)) (knotMap r (X n))
        + dist (knotMap r (X n)) (knotMap r x) := dist_triangle _ _ _
    _ < ε := by linarith

/-- **The strict middle condition passes to a non-degenerate limit.**  If the
chord endpoints `A n, B n` tend to `a, b`, the middle parameters `Z n` tend to
`z ≠ a, b`, and each `Z n` is strictly between `A n` and `B n` on the curve
`r' n`, then `z` is strictly between `a` and `b` on the limit curve `r`.

Closedness: `Z n` on the chord gives the equality case
`dist (A n) (Z n) + dist (Z n) (B n) = dist (A n) (B n)` of the triangle
inequality (`dist_add_dist_eq_iff` through `mem_segment_iff_wbtw`); passing to
the limit (continuity of `dist`) gives the same equality for `a, z, b`, hence
`knotMap r z` lies on the closed chord.  Strictness: `z ≠ a, b` and injectivity
of `knotMap r` separate `knotMap r z` from both endpoints, and a non-endpoint of
a closed segment lies in the open segment (`mem_openSegment_of_ne_left_right`). -/
lemma qrc_isMiddleOnChord_of_tendsto {r : ℝ → Space} (hr : IsSmoothKnot r)
    {r' : ℕ → ℝ → Space} (hr' : ∀ n, IsSmoothKnot (r' n))
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ t : ℝ, dist (r' n t) (r t) < δ)
    {A B Z : ℕ → KnotParam} {a b z : KnotParam}
    (hA : Tendsto A atTop (nhds a)) (hB : Tendsto B atTop (nhds b))
    (hZ : Tendsto Z atTop (nhds z)) (hza : z ≠ a) (hzb : z ≠ b)
    (hmem : ∀ n, IsMiddleOnChord (r' n) (A n) (B n) (Z n)) :
    IsMiddleOnChord r a b z := by
  have hKA := qrc_tendsto_knotMap hr hr' hconv hA
  have hKB := qrc_tendsto_knotMap hr hr' hconv hB
  have hKZ := qrc_tendsto_knotMap hr hr' hconv hZ
  -- the closed-chord equality along the sequence
  have hFG : ∀ n, dist (knotMap (r' n) (A n)) (knotMap (r' n) (Z n))
      + dist (knotMap (r' n) (Z n)) (knotMap (r' n) (B n))
      = dist (knotMap (r' n) (A n)) (knotMap (r' n) (B n)) := by
    intro n
    have hseg : knotMap (r' n) (Z n) ∈
        segment ℝ (knotMap (r' n) (A n)) (knotMap (r' n) (B n)) :=
      openSegment_subset_segment ℝ _ _ (hmem n)
    rw [mem_segment_iff_wbtw] at hseg
    exact (dist_add_dist_eq_iff).mpr hseg
  let F : ℕ → ℝ := fun n => dist (knotMap (r' n) (A n)) (knotMap (r' n) (Z n))
      + dist (knotMap (r' n) (Z n)) (knotMap (r' n) (B n))
  let G : ℕ → ℝ := fun n => dist (knotMap (r' n) (A n)) (knotMap (r' n) (B n))
  have hF : Tendsto F atTop
      (nhds (dist (knotMap r a) (knotMap r z) + dist (knotMap r z) (knotMap r b))) := by
    have h1 : Tendsto (fun n => dist (knotMap (r' n) (A n)) (knotMap (r' n) (Z n)))
        atTop (nhds (dist (knotMap r a) (knotMap r z))) := hKA.dist hKZ
    have h2 : Tendsto (fun n => dist (knotMap (r' n) (Z n)) (knotMap (r' n) (B n)))
        atTop (nhds (dist (knotMap r z) (knotMap r b))) := hKZ.dist hKB
    simpa [F] using h1.add h2
  have hG : Tendsto G atTop (nhds (dist (knotMap r a) (knotMap r b))) := by
    simpa [G] using hKA.dist hKB
  have hGF : G = F := funext (fun n => (hFG n).symm)
  have hF' : Tendsto G atTop
      (nhds (dist (knotMap r a) (knotMap r z) + dist (knotMap r z) (knotMap r b))) := by
    rw [hGF]; exact hF
  have heq : dist (knotMap r a) (knotMap r z) + dist (knotMap r z) (knotMap r b)
      = dist (knotMap r a) (knotMap r b) := tendsto_nhds_unique hF' hG
  -- closed chord membership in the limit, then promotion to the open chord
  have hseg : knotMap r z ∈ segment ℝ (knotMap r a) (knotMap r b) := by
    rw [mem_segment_iff_wbtw]
    exact (dist_add_dist_eq_iff).mp heq
  unfold IsMiddleOnChord
  exact mem_openSegment_of_ne_left_right
    (fun h => hza ((knotMap_injective hr) h.symm))
    (fun h => hzb ((knotMap_injective hr) h.symm)) hseg

theorem quadrisecantChord_of_tendsto_quadrisecants {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {r' : ℕ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr' : ∀ n, LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot (r' n))
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in Filter.atTop, ∀ t : ℝ, dist (r' n t) (r t) < δ)
    {a b z w : AddCircle LeanEval.KnotTheory.Quadrisecant.period}
    (hdist : LeanEval.KnotTheory.Quadrisecant.QuadDistinct a b z w)
    {an bn zn wn : ℕ → AddCircle LeanEval.KnotTheory.Quadrisecant.period}
    (hmem : ∀ n, LeanEval.KnotTheory.Quadrisecant.QuadDistinct (an n) (bn n) (zn n) (wn n) ∧
      LeanEval.KnotTheory.Quadrisecant.IsMiddleOnChord (r' n) (an n) (bn n) (zn n) ∧
      LeanEval.KnotTheory.Quadrisecant.IsMiddleOnChord (r' n) (an n) (bn n) (wn n))
    (han : Filter.Tendsto an Filter.atTop (nhds a)) (hbn : Filter.Tendsto bn Filter.atTop (nhds b))
    (hzn : Filter.Tendsto zn Filter.atTop (nhds z)) (hwn : Filter.Tendsto wn Filter.atTop (nhds w)) :
    LeanEval.KnotTheory.Quadrisecant.QuadrisecantChord r := by
  have hd := hdist
  obtain ⟨hab, haz, haw, hbz, hbw, hzw⟩ := hd
  refine ⟨a, b, z, w, hdist, ?_, ?_⟩
  · exact qrc_isMiddleOnChord_of_tendsto hr hr' hconv han hbn hzn (Ne.symm haz) (Ne.symm hbz)
      (fun n => (hmem n).2.1)
  · exact qrc_isMiddleOnChord_of_tendsto hr hr' hconv han hbn hwn (Ne.symm haw) (Ne.symm hbw)
      (fun n => (hmem n).2.2)

end Work.Drive
