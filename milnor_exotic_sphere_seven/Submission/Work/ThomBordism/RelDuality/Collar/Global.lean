import Mathlib
import Submission.Work.ThomBordism.RelDuality.Collar.Defs
import Submission.Work.Surgery.Collar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# From the local collar property to a collar

`Submission/Work/ThomBordism/RelDuality/Collar/Defs.lean` introduces the composite family
`fam L t : M → M` of a list of local pushes (`PushDatum.localMap`) with a common time parameter,
together with `CoversBnd` (the regions of the data cover the boundary).

This file isolates the two remaining ingredients of a collar of a compact `C¹` `9`-manifold with
boundary `M` in the form in which they can be attacked separately:

* `LocalCollarData L` — **the local collar property** of the family: at every boundary point `y₀`
  there is an open neighbourhood `V` and a height `ε > 0` such that the family restricts to an open
  embedding of `(bnd M ∩ V) × [0,ε)` into `M` (this is the analytic content of the collar
  neighbourhood theorem for the family — the local form of the inverse function theorem, see
  `fam_localCollar`);

* from it, two global statements: the existence of a *uniform strip* on which the family is an open
  embedding (`exists_strip_isOpenEmbedding`), obtained from `LocalCollarData` by compactness of the
  boundary together with the injectivity of the family for small times; and the construction of the
  collar itself (`hasCollar_of_strip`) by reparametrising the strip.

The family pushes every boundary point strictly into the interior (`fam_isInteriorPoint_of_mem_bnd`),
so the resulting collar is a collar in the usual sense.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open scoped Topology Manifold
open Function Set

namespace Work.ThomBordism.RelDuality

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace 9) M]

/-- **The local collar property of the family.**  At every boundary point the family restricts to an
open embedding of a half-neighbourhood of the point (in `bnd M × [0,∞)`) into `M`. -/
def LocalCollarData (L : List (PushDatum M)) : Prop :=
  ∀ y₀ : M, y₀ ∈ bnd M → ∃ (V : Set M) (_ : IsOpen V) (_ : y₀ ∈ V) (ε : ℝ) (_ : 0 < ε),
    Topology.IsOpenEmbedding (fun p : {y : M // y ∈ bnd M ∧ y ∈ V} ×
      {t : ℝ // 0 ≤ t ∧ t < ε} => fam L p.2 p.1)

/-- The strip map of the family: the family restricted to `bnd M × [0,δ)`. -/
def stripMap (L : List (PushDatum M)) (δ : ℝ) :
    {y : M // y ∈ bnd M} × {t : ℝ // 0 ≤ t ∧ t < δ} → M :=
  fun p => fam L p.2.1 p.1.1

/-- The strip map is continuous. -/
theorem stripMap_continuous (L : List (PushDatum M)) (δ : ℝ) :
    Continuous (stripMap L δ) := by
  have h : Continuous fun p : {y : M // y ∈ bnd M} × {t : ℝ // 0 ≤ t ∧ t < δ} =>
      (fam L p.2.1 p.1.1 : M) :=
    (fam_continuous L).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  exact h

/-- The strip map agrees with the family. -/
theorem stripMap_apply (L : List (PushDatum M)) (δ : ℝ)
    (p : {y : M // y ∈ bnd M} × {t : ℝ // 0 ≤ t ∧ t < δ}) :
    stripMap L δ p = fam L p.2.1 p.1.1 := rfl

/-- **The existence of a coarse cover of the boundary by push data.**  For a compact `M` the regions
of the push data at the points of a finite set cover all of `M`, hence in particular the boundary. -/
theorem exists_coversBnd [IsManifold (modelWithCornersEuclideanHalfSpace 9) 1 M]
    [CompactSpace M] : ∃ L : List (PushDatum M), CoversBnd L := by
  classical
  obtain ⟨S, hS⟩ := (isCompact_univ (X := M)).elim_finite_subcover
    (fun y : M => (PushDatum.ofPoint y).region)
    (fun y => PushDatum.isOpen_region (PushDatum.ofPoint y))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, PushDatum.mem_region_ofPoint x⟩)
  refine ⟨S.toList.map (fun z : M => PushDatum.ofPoint z), fun y _ => ?_⟩
  have hy := hS (Set.mem_univ y)
  simp only [Set.mem_iUnion, exists_prop] at hy
  obtain ⟨z, hzS, hyz⟩ := hy
  exact ⟨PushDatum.ofPoint z,
    List.mem_map_of_mem (f := fun z : M => PushDatum.ofPoint z) (Finset.mem_toList.mpr hzS), hyz⟩

end

end Work.ThomBordism.RelDuality
