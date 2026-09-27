import Mathlib
import Submission.Work.Drive.PushDisc.asymChart

/-!
# The finger in the flattened chart: the frontier row

This is the first self-contained piece of the **finger-in-the-flattened-chart** step (the remaining
construction of the compact `n ≥ 3` case, after the lead's split: fix the chart from
`sheetOneFlatteningData`, then make the finger a graph over the `(x,v)`-window in that chart).

Setting.  `Φ` is the chart (the global diffeomorphism of `sheetOneFlatteningData`, in which the first
sheet is flat: `Φ (f x) ∈ sheetA`), and the finger is parametrised by `σ₂ : ℝ × ℝ^k → M` on the
`(x,v)`-window, with the **graph row**

    Φ (f (σ₂ p)) = (p.1, (g p).1, (g p).2, p.2),

i.e. the finger's image in the chart is the graph of `g` over the window.

`Work.Drive.PushDisc.frontier_row_of_graph` proves the **frontier row** of the interface from this:
every point of the frontier of the finger's image has `|x| = X''` or `‖v‖ = 1`.  The proof is
point-set: for `σ₂` continuous and injective on the *closed* window, the closure of the image of the
open window is the image of the closed window (compactness), so a frontier point is `σ₂ p` with `p` on
the window's boundary and not in the open window, and the graph row reads `p`'s coordinates off.

The remaining pieces of the finger step are the *existence* of the graph (transversality of the
finger's tangent planes to `ker (x,v)` = `{ξ | ξ.1 = 0 ∧ ξ.2.2.2 = 0}`; at the two double points this
is arranged by `Work.Drive.PushDisc.exists_linearEquiv_sheetA_two_planes`, the two-plane shear of
`Drive/PushDisc/sheetATwoPlaneShear.lean`), the openness row `hW₀o`, the smoothness of `g`, the core
`c` with its sign rows, and the Lipschitz row `hlip`.
-/

namespace Work.Drive.PushDisc

open Set Metric

/-- **The frontier row of the finger from the graph row.**  If `σ₂` is continuous and injective on the
closed window `[-X'', X''] × closedBall 0 1`, the finger's image is *open* (the row `hW₀o` of the
interface), and the chart coordinates of the finger are the graph of `g` there, then every point of
`frontier (σ₂ '' asymReg k X'')` has `|x| = X''` or `‖v‖ = 1`.

(The openness is needed: `frontier` is `closure \ interior`, so an interior point of the image would
not have its coordinates on the window's boundary.) -/
theorem frontier_row_of_graph {k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M)
    (g : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k))
    (X' X'' : ℝ) (hX'' : 1 < X'') (hX''X' : X'' ≤ X')
    (hW₀o : IsOpen (σ₂ '' asymReg k X''))
    (hσcont : ContinuousOn σ₂ (Set.Icc (-X'') X'' ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1))
    (hσinj : Set.InjOn σ₂ (Set.Icc (-X'') X'' ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1))
    (hgraph : ∀ p ∈ Set.Icc (-X'') X'' ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1,
      Φ (f (σ₂ p)) = (p.1, (g p).1, (g p).2, p.2)) :
    ∀ x ∈ frontier (σ₂ '' asymReg k X''),
      |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1 := by
  intro x hx
  -- the closed window is compact, so the image of the closed window is closed, and contains the
  -- image of the open window, hence its closure
  have hKc : IsCompact (Set.Icc (-X'') X'' ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hclsub : closure (σ₂ '' asymReg k X'')
      ⊆ σ₂ '' (Set.Icc (-X'') X'' ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) := by
    refine closure_minimal ?_ (hKc.image_of_continuousOn hσcont).isClosed
    refine Set.image_mono ?_
    intro p hp
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨ha, hb⟩ := abs_lt.mp hp1
    refine ⟨⟨le_of_lt ha, le_of_lt hb⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_of_lt hp2
  have hxcl : x ∈ closure (σ₂ '' asymReg k X'') := hx.1
  obtain ⟨p, hp, hpx⟩ := hclsub hxcl
  have hxnot : x ∉ σ₂ '' asymReg k X'' := by
    have h2 : x ∉ interior (σ₂ '' asymReg k X'') := hx.2
    rwa [hW₀o.interior_eq] at h2
  have hpnot : p ∉ asymReg k X'' := fun hpm => hxnot ⟨p, hpm, hpx⟩
  -- `p` is on the boundary of the closed window
  have hp1mem : -X'' ≤ p.1 ∧ p.1 ≤ X'' := by
    have := hp.1
    rw [Set.mem_Icc] at this
    exact this
  have hp2mem : ‖p.2‖ ≤ 1 := by
    have := hp.2
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
  have hnot : ¬(p.1 < X'' ∧ -X'' < p.1 ∧ ‖p.2‖ < 1) := by
    rintro ⟨h1, h2, h3⟩
    exact hpnot ⟨abs_lt.mpr ⟨h2, h1⟩, h3⟩
  have hpb : p.1 = -X'' ∨ p.1 = X'' ∨ ‖p.2‖ = 1 := by
    rcases lt_or_ge p.1 X'' with h | h
    · rcases lt_or_ge (-X'') p.1 with h2 | h2
      · right; right
        have : ¬ (‖p.2‖ < 1) := fun hlt => hnot ⟨h, h2, hlt⟩
        linarith
      · left; linarith
    · right; left; linarith
  have hgraphp := hgraph p hp
  rw [hpx] at hgraphp
  have hx1 : (Φ (f x)).1 = p.1 := by
    rw [hgraphp]
  have hxv : (Φ (f x)).2.2.2 = p.2 := by
    rw [hgraphp]
  rcases hpb with h | h | h
  · left
    rw [hx1, h, abs_neg, abs_of_pos (by linarith)]
  · left
    rw [hx1, h, abs_of_pos (by linarith)]
  · right
    rw [hxv, h]

end Work.Drive.PushDisc
