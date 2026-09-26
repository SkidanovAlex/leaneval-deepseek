import Submission.Work.BoxShrink.Bubble.HalfDefs
import Submission.Work.BoxShrink.Bubble.Dichotomy
import Submission.Work.BoxShrink.Bubble.Refutation
import Submission.Work.BoxShrink.Bubble.not_containsEssentialLoop_sphereSet_swap
import Submission.Work.BoxShrink.Bubble.meridian_mem_upperRegion_swap
import Submission.Work.BoxShrink.Bubble.meridian_mem_lowerRegion_swap
import Submission.Work.BoxShrink.Bubble.longitude_mem_lowerRegion_swap

/-!
# The corrected interface, verified in a whole family of genuine pinch configurations

This file verifies the corrected interface `Work.BoxShrink.Bubble.BubbleHalf` (and, at the initial
sphere, Pardon's dichotomy) in the one-parameter family of box/plane configurations in which the
box genuinely cuts the standard torus of revolution and in which the old field already fails: the
standard torus, `c = 0`, `σ = Equiv.swap 1 2` (so the cut plane is the plane `{y = u}`), and any box
size `s ≥ 5/2`.  At `s = 5/2` and `u = 0` this is exactly the counterexample to the old field
(`Work.BoxShrink.Bubble.standard_counterexample`).

* `Work.BoxShrink.Bubble.not_containsEssentialLoop_sphereSet_swap` (delegated): the box sphere
  carries no essential loop, for every `s ≥ 5/2` (hence the hypothesis `hS` of the field holds);
* `Work.BoxShrink.Bubble.pardonDichotomy_boxRegion_swap`: **Pardon's dichotomy at the initial
  sphere** holds for every `s ≥ 5/2` — the `⊤` branch, since both the longitude `{z = -1}`
  (winding `(1,0)`) and the meridian `{p.1 = π/2}` (winding `(0,1)`) lie inside the box;
* `Work.BoxShrink.Bubble.meridian_mem_upperRegion_swap` (delegated) and
  `Work.BoxShrink.Bubble.meridian_mem_lowerRegion_swap` (delegated): the meridian `{p.1 = π/2}` lies
  in `upperRegion` when `u < 1`, and the meridian `{p.1 = -π/2}` lies in `lowerRegion` when
  `u > -1`.  These two cases cover every `u`, so
* **`Work.BoxShrink.Bubble.bubbleHalf_swap`**: for every `s ≥ 5/2` and every plane level `u`, the
  corrected conclusion holds — an essential loop of the region inside the box survives to one of the
  two half-regions — with no hypothesis on the slice at all.  In particular the *whole* family
  satisfies `BubbleHalf`, although at `s = 5/2`, `u = 0` the old field fails;
* `Work.BoxShrink.Bubble.longitude_mem_lowerRegion_swap` (delegated) records the companion fact that
  for `u > 1` the longitude `{p.2 = π}` (winding `(1,0)`) lies in `lowerRegion`;
* `Work.BoxShrink.Bubble.swapFamily_summary` collects the two hypotheses of the *corrected* input in
  the family, and `Work.BoxShrink.Bubble.bubbleHalf_swap_mapHomeomorph` transports the conclusion to
  the smooth torus `Work.CoreTopology.ParamTorus.mapHomeomorph idDiffeo.toHomeomorph` — the standard
  torus written in the form of the challenge's surfaces (`P = mapHomeomorph ψ.toHomeomorph`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Bubble

noncomputable section

/-- **The corrected conclusion holds in the whole family.**  For the standard torus, `c = 0`,
`σ = Equiv.swap 1 2` and every box size `s ≥ 5/2`, an essential loop of the region inside the box
survives to one of the two half-regions cut out by the plane `{y = u}` — for every plane level `u`.

The witnesses are the meridian circles of winding `(0,1)`: `{p.1 = π/2}` lies in `upperRegion` when
`u < 1` (its `y`-coordinate is `2 + cos p.2 ≥ 1`), and `{p.1 = -π/2}` lies in `lowerRegion` when
`u > -1` (its `y`-coordinate is `-(2 + cos p.2) ≤ -1`). -/
theorem bubbleHalf_swap (s : ℝ) (hs : 5 / 2 ≤ s) (u : ℝ) :
    BubbleHalf Work.CoreTopology.standard s 0 (Equiv.swap (1 : Fin 3) 2) u := by
  intro _
  rcases lt_or_ge u 1 with hu | hu
  · exact Or.inl ⟨_, Work.CoreTopology.meridianCurve_essential _ _,
      meridian_mem_upperRegion_swap s hs u hu⟩
  · exact Or.inr ⟨_, Work.CoreTopology.meridianCurve_essential _ _,
      meridian_mem_lowerRegion_swap s hs u (by linarith)⟩

/-- **The corrected conclusion in the family, for the smooth torus in the form of the challenge**:
the standard torus written as `ParamTorus.mapHomeomorph ψ.toHomeomorph` with `ψ` the identity
diffeomorphism. -/
theorem bubbleHalf_swap_mapHomeomorph (s : ℝ) (hs : 5 / 2 ≤ s) (u : ℝ) :
    BubbleHalf (Work.CoreTopology.ParamTorus.mapHomeomorph idDiffeo.toHomeomorph) s 0
      (Equiv.swap (1 : Fin 3) 2) u := by
  rw [mapHomeomorph_idDiffeo_eq_standard]
  exact bubbleHalf_swap s hs u

/-- **Both inputs of the corrected field, in the family**: the box sphere carries no essential loop
(the hypothesis `hS` of the field), and the region inside the box satisfies Pardon's dichotomy —
verified, in the whole family `s ≥ 5/2`, i.e. in the regime where the box genuinely cuts the surface
and where the old field already fails. -/
theorem swapFamily_summary (s : ℝ) (hs : 5 / 2 ≤ s) :
    (¬ Work.CoreTopology.standard.ContainsEssentialLoop
        (Work.BoxShrink.Core.sphereSet 0 (Equiv.swap (1 : Fin 3) 2) s)) ∧
      PardonDichotomy Work.CoreTopology.standard
        (Work.BoxShrink.Core.boxRegion Work.CoreTopology.standard s 0
          (Equiv.swap (1 : Fin 3) 2)) :=
  ⟨not_containsEssentialLoop_sphereSet_swap s hs, pardonDichotomy_boxRegion_swap s hs⟩

end

end Work.BoxShrink.Bubble
