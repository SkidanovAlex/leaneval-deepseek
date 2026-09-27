import Mathlib
import Submission.Work.Drive.encodedEndData
import Submission.Work.Drive.encodedGeneric

/-!
# The class-row interface of the ends clause (`NOTES_LEAD_hodd_blockT6.md` §1, §3, §2.5)

`Work.Drive.ClassRowsAt Q a c' φ cl hcl t` is the bundle of the five **t-dependent** class-level rows
of the lead's §3 stage-1 table, at the design parameter `t : ℝ¹²` and the fixed linear data `(φ, cl)`:

* `PairReg P̂₁P̂₂`, `PairReg lin₀P̂₂` — the two pair rows against the second perturbed design block;
* `EndTripleReg {P̂₀,P̂₁,P̂₂}`, `EndTripleReg {lin₀,P̂₁,P̂₂}`, `EndTripleReg {lin₁,lin₀,P̂₂}` — the three
  end-triple rows that involve the perturbed design blocks,

where `P̂ k = planeClassMap (pertDesignPlane Q a c' t k)` and `lin k = planeClassMap (linPlaneOf φ cl hcl k)`.

`Work.Drive.ClassRowsStatic φ cl hcl` is the corresponding **t-independent** pair: the two rows in which
only the three linear disk models `lin 0, lin 1, lin 2` occur (`PairReg lin₀lin₁`,
`EndTripleReg {lin₂,lin₀,lin₁}`).  These can therefore be discharged *together with* the choice of
`(φ, cl)` — the shape in which the φ-chooser delivers them (`Work.Drive.exists_linPlaneCharts_hgen` +
`Work.Drive.endTripleReg_linPlaneCharts_uncond`).

The two bundles are *literally* the seven class-level hypotheses of
`Work.Drive.hasClassLinearization_of_endData` (§2.5), so that the assembly of
`Work.Drive.exists_classRowFamily` is the pairing of a producer of `R` with the fixed linear data.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.projCharted

noncomputable section

/-- The design angles `u = ![0, a, a + c']` of the triple. -/
def designAngles (a c' : UnitAddCircle) : Fin 3 → UnitAddCircle := ![0, a, a + c']

@[simp] lemma designAngles_zero (a c' : UnitAddCircle) : designAngles a c' 0 = 0 := rfl
@[simp] lemma designAngles_one (a c' : UnitAddCircle) : designAngles a c' 1 = a := rfl
@[simp] lemma designAngles_two (a c' : UnitAddCircle) : designAngles a c' 2 = a + c' := rfl


/-- A real representative of an angle (`ℝ/ℤ`). -/
def angleRep (w : UnitAddCircle) : ℝ := Quotient.out w

@[simp] lemma angleRep_coe (w : UnitAddCircle) : ((angleRep w : ℝ) : UnitAddCircle) = w :=
  Quotient.out_eq w

/-- The real representatives of the design angles `![0, a, a + c']`, for the producers that take the
rotation angles of `rotPresentation` as *real* numbers. -/
def designAnglesReal (a c' : UnitAddCircle) : Fin 3 → ℝ := ![0, angleRep a, angleRep (a + c')]

lemma designAnglesReal_coe (a c' : UnitAddCircle) (k : Fin 3) :
    ((designAnglesReal a c' k : ℝ) : UnitAddCircle) = designAngles a c' k := by
  fin_cases k <;> simp [designAnglesReal, designAngles]

/-- The `k`-th **perturbed design plane** of the triple at parameter `t`: the chart perturbation of
`blk k t` applied to the rotated presentation of the chart. -/
def pertDesignPlane (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin 12)) (k : Fin 3) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun y => chartPert ((blk k) t) (rotPresentation Q (designAngles a c' k) y)

/-- The `k`-th **linear disk model** at the level `cl`. -/
def linPlaneOf (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) (k : Fin 3) :
    EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  diskPlane (linPlaneChart (φ k) cl hcl)

/-- **The five `t`-dependent class rows of the design's triple**, at the parameter `t`. -/
def ClassRowsAt (Q : ℂ → CappingSpace) (a c' : UnitAddCircle)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl)
    (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  PairReg (planeClassMap (pertDesignPlane Q a c' t 1))
      (planeClassMap (pertDesignPlane Q a c' t 2)) ∧
    PairReg (planeClassMap (linPlaneOf φ cl hcl 0))
      (planeClassMap (pertDesignPlane Q a c' t 2)) ∧
    EndTripleReg (planeClassMap (pertDesignPlane Q a c' t 0))
      (planeClassMap (pertDesignPlane Q a c' t 1))
      (planeClassMap (pertDesignPlane Q a c' t 2)) ∧
    EndTripleReg (planeClassMap (linPlaneOf φ cl hcl 0))
      (planeClassMap (pertDesignPlane Q a c' t 1))
      (planeClassMap (pertDesignPlane Q a c' t 2)) ∧
    EndTripleReg (planeClassMap (linPlaneOf φ cl hcl 1))
      (planeClassMap (linPlaneOf φ cl hcl 0))
      (planeClassMap (pertDesignPlane Q a c' t 2))

/-- **The two `t`-independent class rows** of the three linear disk models. -/
def ClassRowsStatic (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (cl : ℝ) (hcl : 0 < cl) : Prop :=
  PairReg (planeClassMap (linPlaneOf φ cl hcl 0))
      (planeClassMap (linPlaneOf φ cl hcl 1)) ∧
    EndTripleReg (planeClassMap (linPlaneOf φ cl hcl 2))
      (planeClassMap (linPlaneOf φ cl hcl 0))
      (planeClassMap (linPlaneOf φ cl hcl 1))

end

end Work.Drive
