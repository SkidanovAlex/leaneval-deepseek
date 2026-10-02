import Mathlib
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.Thom.realThomClassOf_natural
import Submission.Work.ThomBordism.tautologicalClassSensitivity
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.coorientationRef
import Submission.Work.ThomBordism.tautologicalBundleHoriO
import Submission.Work.ThomBordism.frameEval_realThomClassOf

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory

/-!
# The tube-level objects for the normal reading of the canonical class

The last mile compares the restriction of the canonical class
`Ucan = gtdUWith E ND G hgm (realThomClassOf …)` to the tube with the pullback of the standard
generator `stdModelGen k` along the *coordinate reading* of the normal vector, in the σ-corrected
frame `Gauss.gframe` of the normal datum.  This file supplies the objects of that comparison:
the foot map of the tube, the part of the tube lying over a chart of the normal datum, its
punctured part, and the inclusion of the first into the normal total space.
-/

namespace Work.ThomBordism.KeyLocal

noncomputable section

open Work.Tubular Work.ThomBordism.PontryaginThom

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The foot map of the tube**: the projection of the tube inverse `C.inv`. -/
def tubeFoot (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) : C(↥C.U, V.pt) :=
  ⟨fun y => NormalTotal.proj (C.inv y.1),
    (NormalTotal.continuous_proj E).comp
      (C.continuousOn_inv.comp_continuous continuous_subtype_val (fun y => y.2))⟩

@[simp] theorem tubeFoot_apply (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (y : ↥C.U) : tubeFoot E C y = NormalTotal.proj (C.inv y.1) := rfl

/-- The tube inverse as a map into the normal total space, on the whole closed tube. -/
def tubeInv (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε) :
    C(↥C.U, TopCat.of (NormalTotal E)) :=
  ⟨fun y => C.inv y.1,
    C.continuousOn_inv.comp_continuous continuous_subtype_val (fun y => y.2)⟩

/-- **The part of the tube over the base set of the normal-datum chart `i`.** -/
def tubeBaseSet (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) : Set ↥C.U :=
  {y | tubeFoot E C y ∈ ND.D.baseSet i}

theorem mem_tubeBaseSet (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (y : ↥C.U) :
    y ∈ tubeBaseSet E C ND i ↔ NormalTotal.proj (C.inv y.1) ∈ ND.D.baseSet i := Iff.rfl

/-- **The punctured part of `tubeBaseSet`**: the points whose tube inverse is not on the zero
section. -/
def tubeBaseSetPunct (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) : Set ↥(tubeBaseSet E C ND i) :=
  {y | C.inv y.1.1 ∈ normalNonzero E}

theorem mem_tubeBaseSetPunct (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (y : ↥(tubeBaseSet E C ND i)) :
    y ∈ tubeBaseSetPunct E C ND i ↔ C.inv y.1.1 ∈ normalNonzero E := Iff.rfl

/-- **The inclusion of `tubeBaseSet` into the normal total space** (through the tube inverse), as a
map of pairs `(tubeBaseSet, tubeBaseSetPunct) → (ν, ν∖0)`. -/
def tubeBaseSetIncl (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    C(↥(tubeBaseSet E C ND i), TopCat.of (NormalTotal E)) :=
  ⟨fun y => C.inv y.1.1,
    C.continuousOn_inv.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.1.2)⟩

@[simp] theorem tubeBaseSetIncl_apply (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (y : ↥(tubeBaseSet E C ND i)) :
    tubeBaseSetIncl E C ND i y = C.inv y.1.1 := rfl

theorem tubeBaseSetIncl_mem (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    ∀ y ∈ tubeBaseSetPunct E C ND i, tubeBaseSetIncl E C ND i y ∈ normalNonzero E :=
  fun y hy => hy

/-- **The normal coordinate reading of the tube** in the σ-corrected frame of the normal datum at
the chart `i`: the coordinate map whose pullback of `stdModelGen k` is compared with the
restriction of the canonical class. -/
def tubeNormCoord (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k)
    (y : ↥(tubeBaseSet E C ND i)) : EuclideanSpace ℝ (Fin k) :=
  Work.ThomBordism.readFrame (Gauss.gframe E ND i (NormalTotal.proj (C.inv y.1.1)))
    (NormalTotal.vec (C.inv y.1.1))


/-- The punctured-at-`x` stalk of the normal total space: the set of points whose foot is not `x`.
This is the relative set of the degree-`8` class `π^*(o_x)` of the tangential reading. -/
def normalPunctAt (E : EmbeddingData V (8 + k)) (x : V.pt) : Set (NormalTotal E) :=
  {p | NormalTotal.proj p ≠ x}

/-- **The tangential punctured set of the tube**: the tube points whose foot is not `x`. -/
def tubeFootPunct (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    Set ↥(tubeBaseSet E C ND i) :=
  {y | tubeFoot E C y.1 ≠ x}

/-- **The foot of the tube, as a map into the chart source `src V i.1`** of the tangent chart of
the normal-datum chart `i`. -/
def tubeFootSrc (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    C(↥(tubeBaseSet E C ND i), ↥(FrameSigns.src V i.1)) :=
  ⟨fun y => ⟨tubeFoot E C (y : ↥C.U),
      ND.baseSet_sub i.1 i.2 (tubeFoot E C (y : ↥C.U)) y.2⟩,
    Continuous.subtype_mk ((tubeFoot E C).continuous.comp continuous_subtype_val)
      (fun y => ND.baseSet_sub i.1 i.2 (tubeFoot E C (y : ↥C.U)) y.2)⟩

theorem tubeFootSrc_val (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) (y : ↥(tubeBaseSet E C ND i)) :
    ((tubeFootSrc E C ND i y : ↥(FrameSigns.src V i.1)) : V.pt) = tubeFoot E C (y : ↥C.U) := rfl

theorem tubeFootSrc_mem (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : TubeChart E ε)
    (ND : NormalData V k E.e) (i : CoverIdx V k) {x : V.pt} :
    ∀ y ∈ tubeFootPunct E C ND i x,
      (tubeFootSrc E C ND i y : V.pt) ≠ x := by
  intro y hy
  rw [tubeFootSrc_val]
  exact hy

end

end Work.ThomBordism.KeyLocal
