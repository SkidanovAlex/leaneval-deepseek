import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotT.functionField_baseChange_map

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Artin–Schreier LAM node: the ambient field `M = L(E)` over the two-root field `L`
(general base field `K`)

Port of `Submission/Work/MotV5/LamAS/asML.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace Work.MotC5N3.LamAS

open WeierstrassCurve WeierstrassCurve.Affine

variable {𝕜 : Type} [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K]

/-- The two-root Artin–Schreier field `L = K⟮asRoot f₁, asRoot f₂⟯ ⊆ KbA K`. -/
noncomputable def asL2 (f₁ f₂ : K) : IntermediateField K (KbA K) :=
  IntermediateField.adjoin K
    ({asRoot f₁, asRoot f₂} : Set (KbA K))

theorem asRoot_mem_asL2_left (f₁ f₂ : K) : asRoot f₁ ∈ asL2 f₁ f₂ :=
  IntermediateField.subset_adjoin _ _ (by simp [asL2])

theorem asRoot_mem_asL2_right (f₁ f₂ : K) : asRoot f₂ ∈ asL2 f₁ f₂ :=
  IntermediateField.subset_adjoin _ _ (by simp [asL2])

instance asL2_isScalarTower (f₁ f₂ : K) :
    IsScalarTower 𝕜 ↥(asL2 f₁ f₂) (KbA K) :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply 𝕜 K ↥(asL2 f₁ f₂) x,
      ← IsScalarTower.algebraMap_apply K ↥(asL2 f₁ f₂) (KbA K)
        ((algebraMap 𝕜 K) x),
      ← IsScalarTower.algebraMap_apply 𝕜 K (KbA K) x])

/-- The inclusion `L ⊆ KbA K` as a `𝕜`-algebra homomorphism. -/
noncomputable def asInc (f₁ f₂ : K) : ↥(asL2 f₁ f₂) →ₐ[𝕜] KbA K where
  toFun := algebraMap ↥(asL2 f₁ f₂) (KbA K)
  map_one' := map_one _
  map_mul' := fun _ _ => map_mul _ _ _
  map_zero' := map_zero _
  map_add' := fun _ _ => map_add _ _ _
  commutes' := fun c => IsScalarTower.algebraMap_apply 𝕜 ↥(asL2 f₁ f₂) (KbA K) c

/-- The base-changed Klein model over `L`. -/
noncomputable abbrev asE2 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    WeierstrassCurve ↥(asL2 f₁ f₂) :=
  D.E.baseChange ↥(asL2 f₁ f₂)

/-- **The ambient field `M = L(E)`** of the Artin–Schreier LAM node. -/
noncomputable abbrev asML (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) : Type :=
  Affine.FunctionField (asE2 D f₁ f₂)

noncomputable instance asML_isScalarTower (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    IsScalarTower K ↥(asL2 f₁ f₂) (asML D f₁ f₂) :=
  IsScalarTower.of_algebraMap_eq (fun x => rfl)

/-- The `𝕜`-linear base-change map `M = L(E) → KbA K(E) = OmA K D`. -/
noncomputable def asIota0 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    asML D f₁ f₂ →ₐ[𝕜] OmA K D :=
  (Work.MotT.functionField_baseChange_map 𝕜 D.E ↥(asL2 f₁ f₂) (KbA K)
    (asInc f₁ f₂)).choose

theorem asIota0_algebraMap (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K)
    (l : ↥(asL2 f₁ f₂)) :
    asIota0 D f₁ f₂ (algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) l) =
      algebraMap (KbA K) (OmA K D) l :=
  (Work.MotT.functionField_baseChange_map 𝕜 D.E ↥(asL2 f₁ f₂) (KbA K)
    (asInc f₁ f₂)).choose_spec.1 l

theorem asIota0_genX (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    asIota0 D f₁ f₂ (Work.MotV.genX (asE2 D f₁ f₂)) =
      Work.MotV.genX (D.E.baseChange (KbA K)) :=
  (Work.MotT.functionField_baseChange_map 𝕜 D.E ↥(asL2 f₁ f₂) (KbA K)
    (asInc f₁ f₂)).choose_spec.2.1

theorem asIota0_genY (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    asIota0 D f₁ f₂ (Work.MotV.genY (asE2 D f₁ f₂)) =
      Work.MotV.genY (D.E.baseChange (KbA K)) :=
  (Work.MotT.functionField_baseChange_map 𝕜 D.E ↥(asL2 f₁ f₂) (KbA K)
    (asInc f₁ f₂)).choose_spec.2.2.1

theorem asIota0_injective (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    Function.Injective (asIota0 D f₁ f₂) :=
  (Work.MotT.functionField_baseChange_map 𝕜 D.E ↥(asL2 f₁ f₂) (KbA K)
    (asInc f₁ f₂)).choose_spec.2.2.2 (fun a b hab => Subtype.ext hab)

/-- **The `K`-linear base-change map `M = L(E) → KbA K(E) = OmA K D`.** -/
noncomputable def asIota (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    asML D f₁ f₂ →ₐ[K] OmA K D where
  toFun := asIota0 D f₁ f₂
  map_one' := map_one _
  map_mul' := fun _ _ => map_mul _ _ _
  map_zero' := map_zero _
  map_add' := fun _ _ => map_add _ _ _
  commutes' := fun c => by
    have h1 : (algebraMap K (asML D f₁ f₂)) c =
        (algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂))
          ((algebraMap K ↥(asL2 f₁ f₂)) c) :=
      IsScalarTower.algebraMap_apply K ↥(asL2 f₁ f₂) (asML D f₁ f₂) c
    rw [h1, asIota0_algebraMap]
    rw [IsScalarTower.algebraMap_apply K (KbA K) (OmA K D) c]
    exact congrArg (algebraMap (KbA K) (OmA K D))
      (IsScalarTower.algebraMap_apply K ↥(asL2 f₁ f₂) (KbA K) c).symm

@[simp]
theorem asIota_apply (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) (x : asML D f₁ f₂) :
    asIota D f₁ f₂ x = asIota0 D f₁ f₂ x := rfl

theorem asIota_algebraMap (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K)
    (l : ↥(asL2 f₁ f₂)) :
    asIota D f₁ f₂ (algebraMap ↥(asL2 f₁ f₂) (asML D f₁ f₂) l) =
      algebraMap (KbA K) (OmA K D) l :=
  asIota0_algebraMap D f₁ f₂ l

theorem asIota_genX (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    asIota D f₁ f₂ (Work.MotV.genX (asE2 D f₁ f₂)) =
      Work.MotV.genX (D.E.baseChange (KbA K)) :=
  asIota0_genX D f₁ f₂

theorem asIota_genY (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    asIota D f₁ f₂ (Work.MotV.genY (asE2 D f₁ f₂)) =
      Work.MotV.genY (D.E.baseChange (KbA K)) :=
  asIota0_genY D f₁ f₂

theorem asIota_injective (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    Function.Injective (asIota D f₁ f₂) :=
  asIota0_injective D f₁ f₂

/-- The Klein coordinates of the `L`-model, viewed in `M = L(E)`. -/
noncomputable def asKleinCoordM (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) (i : Fin 5) :
    asML D f₁ f₂ :=
  Work.MotV.kleinCoord D ↥(asL2 f₁ f₂) i

/-- The Klein field of the `L`-model, inside `M = L(E)`. -/
noncomputable def asKleinFieldM (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    IntermediateField K (asML D f₁ f₂) :=
  IntermediateField.adjoin K
    (Set.range (fun i : Fin 5 => asKleinCoordM D f₁ f₂ i / asKleinCoordM D f₁ f₂ 0))

/-- The image of `L` inside `M = L(E)`. -/
noncomputable def asLImageM (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    IntermediateField K (asML D f₁ f₂) :=
  (IsScalarTower.toAlgHom K ↥(asL2 f₁ f₂) (asML D f₁ f₂)).fieldRange

end Work.MotC5N3.LamAS
