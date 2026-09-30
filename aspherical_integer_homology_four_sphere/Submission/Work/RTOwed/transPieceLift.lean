/-
# Lifting a piece of a fold transition to a pair of Voronoi pieces

The transition of two fold charts `Work.FoldInst.foldChart i` and `Work.FoldInst.foldChart j` is
defined on the set `Work.RTOwed.Trans i j` of chart values of `i` whose class lies in the source of
the chart `j`.  This file records the elementary *piece* statement: every such value is the value of
the chart `i` on a Voronoi piece `Dvor i r`, and the corresponding point of `Xbar` is carried by an
element of the pairing group `Gg` into a Voronoi piece `Dvor j s` of the class `j`.

The proof is a direct unfolding of the two definitions involved.  Membership in the transition
source is membership in the target of `foldChart i` (where the chart is inverted) together with
membership of the inverse value in the source of `foldChart j`; the target of a chart is the image
of its source (`image_source_eq_target`), and the sources are the unions of the Voronoi pieces
(`Work.FoldInst.foldChart_source`).  Finally two points of `Xbar` with the same class differ by an
element of `Ksub ⊆ Gg` — the defining relation of `Xbar` (`Quotient.eq`, `Work.FoldInst.rel`).
-/
import Mathlib
import Submission.Work.RTOwed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

theorem transPieceLift (i j : Fin 98) {z : Work.FoldInst.E4} (hz : z ∈ Work.RTOwed.Trans i j) :
    ∃ (r : Fin (Work.FoldInst.foldCodim i) → Bool) (s : Fin (Work.FoldInst.foldCodim j) → Bool)
      (γ : Work.FoldInst.Gg) (x : Work.FoldInst.Xbar),
      x ∈ Work.FoldInst.Dvor i r ∧ Work.FoldInst.actX γ x ∈ Work.FoldInst.Dvor j s ∧
        z = Work.FoldInst.foldTheta i r x.2.1 := by
  -- Unfold the source of the composite partial homeomorphism `(foldChart i).symm ≫ₕ foldChart j`.
  rw [Work.RTOwed.Trans, OpenPartialHomeomorph.trans_source] at hz
  obtain ⟨hzT, hzS⟩ := hz
  rw [OpenPartialHomeomorph.symm_source] at hzT
  -- The inverse image of `z` under `foldChart i` lies in the source of `foldChart i`.
  have hps : (Work.FoldInst.foldChart i).symm z ∈ (Work.FoldInst.foldChart i).source := by
    have hmem : (Work.FoldInst.foldChart i).symm z ∈
        (Work.FoldInst.foldChart i).symm '' (Work.FoldInst.foldChart i).symm.source :=
      ⟨z, hzT, rfl⟩
    rwa [OpenPartialHomeomorph.image_source_eq_target, OpenPartialHomeomorph.symm_target] at hmem
  -- Both sources are unions of Voronoi pieces.
  rw [Work.FoldInst.foldChart_source] at hps hzS
  obtain ⟨r, hp⟩ := Set.mem_iUnion.mp hps
  obtain ⟨x, hxr, hx⟩ := Set.mem_image _ _ _ |>.mp hp
  obtain ⟨s, hq⟩ := Set.mem_iUnion.mp hzS
  obtain ⟨y, hys, hy⟩ := Set.mem_image _ _ _ |>.mp hq
  -- Two points of `Xbar` with the same class differ by an element of the pairing group.
  have hrel : Work.FoldInst.rel x y := Quotient.eq.mp (hx.trans hy.symm)
  obtain ⟨γ, -, hγ⟩ := hrel
  refine ⟨r, s, γ, x, hxr, ?_, ?_⟩
  · rw [hγ]; exact hys
  · have hval : (Work.FoldInst.foldChart i) (Work.FoldInst.mk x) = z := by
      rw [hx]
      exact OpenPartialHomeomorph.right_inv (Work.FoldInst.foldChart i) hzT
    rw [← hval]
    exact Work.FoldInst.foldChart_apply i r x hxr

end Work.RTOwed
