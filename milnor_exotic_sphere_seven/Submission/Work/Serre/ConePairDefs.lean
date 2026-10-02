import Mathlib
import Submission.Work.StemsB.CylMapGen
import Submission.Work.StemsB.Fibrations
import Submission.Work.Thom.Cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-! ## The fibre pair of the mapping cylinder, and the restriction map -/

/-- The fibre of the retraction of the mapping cylinder of `q` over the point `b`. -/
def coneFibre {X B : Type} [TopologicalSpace X] [TopologicalSpace B] (q : C(X, B)) (b : B) :
    Set (cyl q) :=
  (cylRetract q) ⁻¹' {b}

/-- The part of the bottom copy of the mapping cylinder lying over `b`. -/
def coneFibreBot {X B : Type} [TopologicalSpace X] [TopologicalSpace B] (q : C(X, B)) (b : B) :
    Set ↥(coneFibre q b) :=
  {x | (x : cyl q) ∈ Set.range (cylIncl q)}

/-- The inclusion of the fibre pair of the mapping cylinder into the mapping-cylinder pair. -/
def coneFibreIncl {X B : Type} [TopologicalSpace X] [TopologicalSpace B] (q : C(X, B)) (b : B) :
    C(↥(coneFibre q b), cyl q) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- **The restriction of relative cohomology to the fibre of the mapping cylinder over `b`.** -/
def coneFibreRes {X B : Type} [TopologicalSpace X] [TopologicalSpace B] (q : C(X, B)) (b : B)
    (n : ℕ) :
    Work.Thom.RelCoh ℚ n (cyl q) (Set.range (cylIncl q)) →ₗ[ℚ]
      Work.Thom.RelCoh ℚ n ↥(coneFibre q b) (coneFibreBot q b) :=
  (Work.Thom.relCohMap (coneFibreIncl q b) (coneFibreBot q b) (Set.range (cylIncl q))
    (fun _ hx => hx) ℚ n).hom

/-- The restriction of a map of pairs to a sub-pair. -/
def restrictPairGen {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y']
    (A : Set X') (B : Set Y') (g : C(X', Y')) (hg : Set.MapsTo g A B) : C(↥A, ↥B) where
  toFun x := ⟨g x.1, hg x.2⟩
  continuous_toFun := Continuous.subtype_mk (g.continuous.comp continuous_subtype_val)
    (fun x => hg x.2)

@[simp]
theorem restrictPairGen_coe {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y']
    (A : Set X') (B : Set Y') (g : C(X', Y')) (hg : Set.MapsTo g A B) (x : ↥A) :
    ((restrictPairGen A B g hg) x : Y') = g x.1 := rfl

/-! ## The map of mapping cylinders induced by the pullback square of a path -/

/-- **The map of mapping cylinders induced by the pullback square of the path `p`**:
it is the identity on the interval coordinate, `pullbackFst` on the source coordinate and `p` on
the target coordinate. -/
def pathPsi {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (p : C(unitInterval, B)) :
    C(cyl (Work.StemsB.pullbackSnd q p), cyl q) :=
  Work.StemsB.cylMapGen (Work.StemsB.pullbackSnd q p) q (Work.StemsB.pullbackFst q p) p
    (fun z => z.2.symm)

/-- `pathPsi` carries the fibre over `t` into the fibre over `p t`. -/
theorem pathPsi_mapsTo_fibre {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval) :
    Set.MapsTo (pathPsi q p) (coneFibre (Work.StemsB.pullbackSnd q p) t) (coneFibre q (p t)) :=
  fun z hz => Work.StemsB.cylMapGen_mapsTo_fibre (Work.StemsB.pullbackSnd q p) q
    (Work.StemsB.pullbackFst q p) p (fun z => z.2.symm) hz

/-- `pathPsi` carries the bottom copy into the bottom copy. -/
theorem pathPsi_mapsTo_range {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (p : C(unitInterval, B)) :
    Set.MapsTo (pathPsi q p) (Set.range (cylIncl (Work.StemsB.pullbackSnd q p)))
      (Set.range (cylIncl q)) :=
  fun z hz => Work.StemsB.cylMapGen_mapsTo_range (Work.StemsB.pullbackSnd q p) q
    (Work.StemsB.pullbackFst q p) p (fun z => z.2.symm) hz

/-- **The restriction of `pathPsi` to the fibre over `t`**, as a map of fibre pairs. -/
def pathPsiFibre {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval) :
    C(↥(coneFibre (Work.StemsB.pullbackSnd q p) t), ↥(coneFibre q (p t))) :=
  restrictPairGen (coneFibre (Work.StemsB.pullbackSnd q p) t) (coneFibre q (p t))
    (pathPsi q p) (pathPsi_mapsTo_fibre q p t)

/-- `pathPsiFibre` carries the bottom copy over `t` into the bottom copy over `p t`. -/
theorem pathPsiFibre_mapsTo_bot {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval) :
    Set.MapsTo (pathPsiFibre q p t) (coneFibreBot (Work.StemsB.pullbackSnd q p) t)
      (coneFibreBot q (p t)) :=
  fun z hz => pathPsi_mapsTo_range q p hz

/-- **The fibre inclusion followed by `pathPsi` is `pathPsiFibre` followed by the fibre
inclusion.** -/
theorem coneFibreIncl_comp_pathPsiFibre {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    (q : C(X, B)) (p : C(unitInterval, B)) (t : unitInterval) :
    (coneFibreIncl q (p t)).comp (pathPsiFibre q p t) =
      (pathPsi q p).comp (coneFibreIncl (Work.StemsB.pullbackSnd q p) t) := by
  apply ContinuousMap.ext
  intro z
  rfl

end

end Work.Serre
