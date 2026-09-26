import Submission.Work.Smooth.SphereJordan.Basic
import Submission.Work.Topology.SphereSlicing.All

/-!
# Pulling the intersection curves of a slice disc back to the model disc

`Work.Topology.SphereSlicing.SliceDisc P` is an embedded disc in `ℝ³` (the image of an injective
continuous map `e : 𝔻 → ℝ³`), whose interior meets the surface `F = P.carrier` along finitely many
pairwise disjoint inessential simple closed curves `curves i` of `F`, each contained in the image of
`e`.

Pardon's "innermost in the surface" step is proved by pulling these curves back along `e` to simple
closed curves *in the model disc* `𝔻 ⊆ ℂ`, where the planar Jordan–Schoenflies theorem and the
planar two-disc theorem apply.  This file provides that pull-back and its API:

* `SliceDiscInv` — the inverse of `e` on its image (continuous, `e` being a closed embedding of a
  compact space into a Hausdorff space);
* `SliceDiscPullback` — the pulled-back curve as a map `ℝ → 𝔻`;
* `pullbackSphereCurve` — the same curve, as a simple closed curve of the Riemann sphere
  (`IsSimpleClosedCurve`), as consumed by `Work.Smooth.SphereJordan.planeTwoDiscs`;
* the identity `e (SliceDiscPullback D i t) = (D.curves i).γ t` which transports everything proved
  in the model disc back to `ℝ³`.
-/

open Set
open Topology
open LeanEval.KnotTheory.PardonDistortion
open Work.CoreTopology

namespace Work.Smooth.SphereJordan

noncomputable section

variable {P : ParamTorus}

/-- The parametrising embedding of a slice disc is a **closed embedding**: its domain `𝔻` is compact
and its target `ℝ³` is Hausdorff. -/
theorem isClosedEmbedding_sliceDisc (D : Work.Topology.SphereSlicing.SliceDisc P) :
    IsClosedEmbedding ⇑D.e := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap D.e.continuous D.inj ?_
  intro s hs
  exact (hs.isCompact.image D.e.continuous).isClosed

/-- The inverse of the parametrising embedding, on its image. -/
noncomputable def SliceDiscInv (D : Work.Topology.SphereSlicing.SliceDisc P) (y : Set.range D.e) :
    Disc := Classical.choose y.2

theorem SliceDiscInv_spec (D : Work.Topology.SphereSlicing.SliceDisc P)
    (y : Set.range D.e) : D.e (SliceDiscInv D y) = y := Classical.choose_spec y.2

theorem SliceDiscInv_continuous (D : Work.Topology.SphereSlicing.SliceDisc P) :
    Continuous (SliceDiscInv D) := by
  have hemb : IsEmbedding ⇑D.e := (isClosedEmbedding_sliceDisc D).isEmbedding
  let φ : Disc ≃ₜ Set.range D.e := hemb.toHomeomorph
  have hφ : ∀ x : Disc, φ x = ⟨D.e x, Set.mem_range_self x⟩ := fun x => rfl
  have hEq : SliceDiscInv D = ⇑φ.symm := by
    funext y
    apply D.inj
    have h1 : (φ (φ.symm y) : Set.range D.e) = y := Homeomorph.apply_symm_apply φ y
    have h2 : D.e (φ.symm y) = (y : R3) := congrArg Subtype.val h1
    rw [SliceDiscInv_spec]
    exact h2.symm
  rw [hEq]
  exact φ.symm.continuous

/-- **The curve of a slice disc, pulled back to the model disc** along the parametrising
embedding. -/
noncomputable def SliceDiscPullback (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) :
    ℝ → Disc :=
  fun t => SliceDiscInv D ⟨(D.curves i).γ t, D.curves_subset i ⟨t, rfl⟩⟩

/-- The defining property of the pull-back: it maps back to the curve. -/
theorem SliceDiscPullback_spec (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) (t : ℝ) :
    D.e (SliceDiscPullback D i t) = (D.curves i).γ t := SliceDiscInv_spec D _

theorem SliceDiscPullback_continuous (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) :
    Continuous (SliceDiscPullback D i) :=
  (SliceDiscInv_continuous D).comp
    (Continuous.subtype_mk (D.curves i).cont (fun t => D.curves_subset i ⟨t, rfl⟩))

theorem SliceDiscPullback_periodic (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) :
    Function.Periodic (SliceDiscPullback D i) (2 * Real.pi) := by
  intro t
  apply D.inj
  rw [SliceDiscPullback_spec, SliceDiscPullback_spec, (D.curves i).periodic t]

theorem SliceDiscPullback_injOn (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) :
    Set.InjOn (SliceDiscPullback D i) (Set.Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  apply D.curves_simple i ha hb
  rw [← SliceDiscPullback_spec D i a, ← SliceDiscPullback_spec D i b, hab]

theorem SliceDiscPullback_norm_le_one (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι)
    (t : ℝ) : ‖((SliceDiscPullback D i t : Disc) : ℂ)‖ ≤ 1 := by
  have h : dist ((SliceDiscPullback D i t : Disc) : ℂ) 0 ≤ 1 := (SliceDiscPullback D i t).2
  rwa [dist_eq_norm, sub_zero] at h

/-- **The pull-back as a simple closed curve of the Riemann sphere**, in the vocabulary of
`planeTwoDiscs`. -/
noncomputable def pullbackSphereCurve (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) :
    ℝ → RiemannSphere :=
  fun t => ((SliceDiscPullback D i t : Disc) : ℂ)

theorem pullbackSphereCurve_ne_infty (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι)
    (t : ℝ) : pullbackSphereCurve D i t ≠ infty := OnePoint.coe_ne_infty _

theorem isSimpleClosedCurve_pullbackSphereCurve
    (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) :
    IsSimpleClosedCurve (pullbackSphereCurve D i) :=
  ⟨OnePoint.continuous_coe.comp (continuous_subtype_val.comp (SliceDiscPullback_continuous D i)),
    fun t => congrArg (fun z : Disc => ((z : ℂ) : RiemannSphere)) (SliceDiscPullback_periodic D i t),
    fun a ha b hb hab => SliceDiscPullback_injOn D i ha hb (Subtype.ext (OnePoint.coe_injective hab))⟩


/-- **The pull-back as a plane curve**, in the form consumed by
`Work.Smooth.SphereJordan.planeTwoDiscs`. -/
noncomputable def pullbackPlaneCurve (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) :
    ℝ → ℂ :=
  fun t => ((SliceDiscPullback D i t : Disc) : ℂ)

theorem pullbackPlaneCurve_continuous (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) :
    Continuous (pullbackPlaneCurve D i) :=
  continuous_subtype_val.comp (SliceDiscPullback_continuous D i)

theorem pullbackPlaneCurve_periodic (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) :
    Function.Periodic (pullbackPlaneCurve D i) (2 * Real.pi) :=
  fun t => congrArg (fun z : Disc => (z : ℂ)) (SliceDiscPullback_periodic D i t)

theorem pullbackPlaneCurve_injOn (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) :
    Set.InjOn (pullbackPlaneCurve D i) (Set.Ico 0 (2 * Real.pi)) :=
  fun a ha b hb hab => SliceDiscPullback_injOn D i ha hb (Subtype.ext hab)

theorem pullbackPlaneCurve_norm_le_one (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι)
    (t : ℝ) : ‖pullbackPlaneCurve D i t‖ ≤ 1 :=
  SliceDiscPullback_norm_le_one D i t

theorem pullbackSphereCurve_eq_coe (D : Work.Topology.SphereSlicing.SliceDisc P) (i : D.ι) (t : ℝ) :
    pullbackSphereCurve D i t = (pullbackPlaneCurve D i t : RiemannSphere) := rfl

end

end Work.Smooth.SphereJordan
