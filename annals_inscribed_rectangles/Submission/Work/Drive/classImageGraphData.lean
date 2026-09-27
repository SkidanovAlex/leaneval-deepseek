import Mathlib
import Submission.Work.Drive.cutClassImage
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.rotLens_rotCapping_isAction
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.squareDisk
import Submission.Work.Drive.BoxParityDefs

/-!
# The graph data of the rotation family of class images

For a continuous disk presentation `Q : ℂ → CappingSpace` of a plane, the design of the order route
sweeps the *rotated* presentations `Work.Drive.rotPresentation Q u` (`u : UnitAddCircle`) and reads the
rigidity of the cut against the **class image** `Work.Drive.classImage (rotPresentation Q u)` — the set
of projective classes of the points of the swept plane, i.e. of the image of the (connected, compact)
parameter box `unitBox 1`.

This file supplies the topological data of that family, which a continuous-selection argument on the
angle `u` needs:

* `Work.Drive.classImageGraphData` — the *closed graph* property
  `{p | p.2 ∈ classImage (rotPresentation Q p.1)}` is closed in `UnitAddCircle × ℝP³`, each fibre
  `classImage (rotPresentation Q u)` is **preconnected**, and each fibre is **nonempty**.

All three clauses reduce to the single new analytic input, **joint continuity of the rotation action**
on the capping space
(`Work.Drive.continuous_rotCapping_uncurry : Continuous fun p : UnitAddCircle × CappingSpace =>
rotCapping p.1 p.2`), which is obtained by descending the explicit joint continuity of `rotSum` on the
two pieces `ConfigPiece ⊕ CapPiece` through the quotient map `Quotient.mk''` along
`Topology.IsQuotientMap.continuous_lift_prod_left` (this is why `UnitAddCircle` — a compact, hence
locally compact, space — is used in the second factor).

With it:

* the set above is the image of the **compact** set `univ ×ˢ unitBox 1` under the continuous map
  `p ↦ (p.1, (cappingSpaceHomeoProj (rotPresentation Q p.1 p.2)).2)`, hence compact, hence closed
  (the target is Hausdorff);
* preconnectedness is `Work.Drive.isPreconnected_classImage_of_continuous` applied to the continuity
  of `rotPresentation Q u = rotCapping u ∘ diskPlane Q`;
* nonemptiness is the nonemptiness of the box.

Everything is `sorry`-free and rests only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Work.Drive

open Set

noncomputable section

/-! ## Joint continuity of the rotation action -/

/-- **Joint continuity of `rotSum` on the two pieces of the capping.**  Descending happens in the
quotient step below; here we only need the explicit coordinate formula, which is continuous in the
rotation parameter `v` and the piece point simultaneously.  The two pieces are handled separately and
glued along the homeomorphism `Homeomorph.prodSumDistrib`. -/
theorem continuous_rotSum_uncurry :
    Continuous (fun q : UnitAddCircle × (ConfigPiece ⊕ CapPiece) => rotSum q.1 q.2) := by
  have h1 : Continuous (fun r : UnitAddCircle × ConfigPiece => rotSum r.1 (Sum.inl r.2)) := by
    show Continuous (fun r : UnitAddCircle × ConfigPiece => Sum.inl (rotConfig r.1 r.2))
    exact continuous_inl.comp (by unfold rotConfig; fun_prop)
  have h2 : Continuous (fun r : UnitAddCircle × CapPiece => rotSum r.1 (Sum.inr r.2)) := by
    show Continuous (fun r : UnitAddCircle × CapPiece => Sum.inr (rotCap r.1 r.2))
    exact continuous_inr.comp (by unfold rotCap; fun_prop)
  have h := h1.sumElim h2
  have h3 : (fun q : UnitAddCircle × (ConfigPiece ⊕ CapPiece) => rotSum q.1 q.2) =
      Sum.elim (fun r : UnitAddCircle × ConfigPiece => rotSum r.1 (Sum.inl r.2))
        (fun r : UnitAddCircle × CapPiece => rotSum r.1 (Sum.inr r.2)) ∘
      (Homeomorph.prodSumDistrib (X := UnitAddCircle) (Y := ConfigPiece) (Z := CapPiece)) := by
    funext q
    rcases q with ⟨v, (p | p)⟩ <;> rfl
  rw [h3]
  exact h.comp (Homeomorph.prodSumDistrib).continuous

/-- **Joint continuity of the rotation action on the capping space.**  The rotation `rotCapping` is
descended from `rotSum` along the quotient map `Quotient.mk''`; since `UnitAddCircle` is locally
compact, `Topology.IsQuotientMap.continuous_lift_prod_left` upgrades the continuity of the composite
to the continuity of the descended map.  (Only the *fixed*-`v` continuity was available before; the
joint statement is what makes the class-image correspondence a closed graph.) -/
theorem continuous_rotCapping_uncurry :
    Continuous (fun p : UnitAddCircle × CappingSpace => rotCapping p.1 p.2) := by
  have hg : Continuous (fun p : (ConfigPiece ⊕ CapPiece) × UnitAddCircle =>
      rotCapping p.2 (Quotient.mk'' p.1)) := by
    have hcomp : Continuous (fun p : (ConfigPiece ⊕ CapPiece) × UnitAddCircle =>
        Quotient.mk'' (rotSum p.2 p.1)) :=
      continuous_cappingMk.comp (continuous_rotSum_uncurry.comp continuous_swap)
    exact hcomp.congr (fun p => by rw [rotCapping_mk])
  have hmain : Continuous (fun q : CappingSpace × UnitAddCircle => rotCapping q.2 q.1) :=
    Topology.IsQuotientMap.continuous_lift_prod_left isQuotientMap_quotient_mk' hg
  exact hmain.comp continuous_swap

/-! ## The rotated presentation and its continuity -/

/-- **The rotated presentation in the capping space.**  The disk presentation of the rotated plane is
the rotation of the disk presentation of the plane: both sides reduce to
`rotCapping u (Q (sqDisk (foldBox y)))`. -/
theorem rotPresentation_apply_rotCapping (Q : ℂ → CappingSpace) (u : UnitAddCircle)
    (y : EuclideanSpace ℝ (Fin 2)) :
    rotPresentation Q u y = rotCapping u (diskPlane Q y) := rfl

/-- The disk presentation of a continuous plane presentation is continuous (it is
`Q ∘ sqDisk ∘ foldBox`). -/
theorem continuous_diskPlane_of_continuous (Q : ℂ → CappingSpace) (hQ : Continuous Q) :
    Continuous (diskPlane Q) := by
  have h : diskPlane Q = fun y : EuclideanSpace ℝ (Fin 2) => Q (sqDisk (foldBox y)) := by
    funext y; rw [diskPlane_apply]
  rw [h]
  exact hQ.comp (sqDisk_contDiff.continuous.comp (foldBox_contMDiff.continuous))

/-- **Every rotated presentation is continuous**: `rotPresentation Q u = rotCapping u ∘ diskPlane Q`. -/
theorem continuous_rotPresentation (Q : ℂ → CappingSpace) (hQ : Continuous Q)
    (u : UnitAddCircle) : Continuous (rotPresentation Q u) := by
  have h : rotPresentation Q u = fun y : EuclideanSpace ℝ (Fin 2) =>
      rotCapping u (diskPlane Q y) := by
    funext y; rw [rotPresentation_apply_rotCapping]
  rw [h]
  exact (continuous_rotCapping u).comp (continuous_diskPlane_of_continuous Q hQ)

/-- **The class image of any presentation is nonempty** — it is the image of the nonempty box. -/
theorem classImage_nonempty (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    (classImage P).Nonempty :=
  ⟨_, mem_classImage.mpr ⟨0, fun i => by simp, rfl⟩⟩

/-! ## The graph data -/

/-- **The graph data of the rotation family of class images.**  For a continuous disk presentation `Q`
of a plane:

* the graph `{p | p.2 ∈ classImage (rotPresentation Q p.1)}` of the class-image correspondence is
  **closed** in `UnitAddCircle × ℝP³` (it is the image of the compact set `univ ×ˢ [0,1]²` under the
  continuous map `p ↦ (p.1, (cappingSpaceHomeoProj (rotPresentation Q p.1 p.2)).2)`);
* every fibre `classImage (rotPresentation Q u)` is **preconnected** (continuous image of the convex,
  hence preconnected, box);
* every fibre is **nonempty**.

This is the topological input a continuous-selection argument on the angle needs: closed graph plus
preconnected, nonempty fibres. -/
theorem classImageGraphData (Q : ℂ → CappingSpace) (hQ : Continuous Q) :
    IsClosed {p : UnitAddCircle × Projectivization ℝ (Eucl 3) |
        p.2 ∈ classImage (rotPresentation Q p.1)} ∧
      (∀ u : UnitAddCircle, IsPreconnected (classImage (rotPresentation Q u))) ∧
      (∀ u : UnitAddCircle, (classImage (rotPresentation Q u)).Nonempty) := by
  refine ⟨?_, ?_, ?_⟩
  · have hF : Continuous (fun p : UnitAddCircle × EuclideanSpace ℝ (Fin 2) =>
        (p.1, (cappingSpaceHomeoProj (rotPresentation Q p.1 p.2)).2)) := by
      refine Continuous.prodMk continuous_fst ?_
      refine (continuous_snd.comp cappingSpaceHomeoProj.continuous).comp ?_
      have h : (fun p : UnitAddCircle × EuclideanSpace ℝ (Fin 2) => rotPresentation Q p.1 p.2)
          = (fun q : UnitAddCircle × CappingSpace => rotCapping q.1 q.2) ∘
            (fun p : UnitAddCircle × EuclideanSpace ℝ (Fin 2) => (p.1, diskPlane Q p.2)) := by
        funext p
        show rotCapping p.1 (diskPlane Q p.2) = rotCapping p.1 (diskPlane Q p.2)
        rfl
      rw [h]
      exact continuous_rotCapping_uncurry.comp
        (continuous_fst.prodMk ((continuous_diskPlane_of_continuous Q hQ).comp continuous_snd))
    have himg : {p : UnitAddCircle × Projectivization ℝ (Eucl 3) |
        p.2 ∈ classImage (rotPresentation Q p.1)} =
        (fun p : UnitAddCircle × EuclideanSpace ℝ (Fin 2) =>
          (p.1, (cappingSpaceHomeoProj (rotPresentation Q p.1 p.2)).2)) ''
          (Set.univ ×ˢ Submission.Drive.unitBox 1) := by
      ext p
      constructor
      · rintro hp
        obtain ⟨y, hy, hq⟩ := (mem_classImage (P := rotPresentation Q p.1)).mp hp
        refine ⟨(p.1, y), ⟨Set.mem_univ _, hy⟩, ?_⟩
        simp only [hq, Prod.mk.eta]
      · rintro ⟨q, hq, hqp⟩
        obtain ⟨-, hy⟩ := hq
        have h1 : q.1 = p.1 := congrArg Prod.fst hqp
        have h2 : (cappingSpaceHomeoProj (rotPresentation Q q.1 q.2)).2 = p.2 :=
          congrArg Prod.snd hqp
        refine (mem_classImage (P := rotPresentation Q p.1)).mpr ⟨q.2, hy, ?_⟩
        rw [← h1]
        exact h2
    rw [himg]
    exact ((isCompact_univ.prod (isCompact_unitBox 1)).image hF).isClosed
  · intro u
    exact isPreconnected_classImage_of_continuous _ (continuous_rotPresentation Q hQ u)
  · intro u
    exact classImage_nonempty _

end

end Work.Drive
