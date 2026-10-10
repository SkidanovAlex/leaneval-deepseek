import Mathlib
import Submission.Work.MotV5.ASTwistData
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.RigAS.twistFieldTrue_sup_asRoot
import Submission.Work.MotT.extend_algEquiv_of_linearDisjoint
import Submission.Work.MotT.functionField_baseChange_map
import Submission.Work.MotV5.Nodes.shiftOf_eq_transAlgEquiv
import Submission.Work.MotV5.LamAS.Setup
import Submission.Work.MotV5.LamAS.asRootField_galois_basic
import Submission.Work.MotV5.kleinField_eq_adjoin_genXY
import Submission.Work.MotC2.aut_functionField

set_option linter.unusedVariables false -- v435-speed

/-!
# The Artin–Schreier LAM node: the ambient field `M = L(E)` over the two-root field `L`

Set-up of the ambient model of the Artin–Schreier LAM argument
(`Work.MotV5.Nodes.lam_AS`).  With `K = 𝕜(t) = RatFunc 𝕜`, `Kb 𝕜 = AlgebraicClosure K`,
`W_i = asRoot f_i` and

* `L := K⟮W₁, W₂⟯ ⊆ Kb` (the two-root Artin–Schreier field),
* `M := L(E)` the function field of the Klein model base changed to `L`,
* `Ω := kleinField D ⊔ LImage D L ⊆ Om D = Kb(E)` the image of `M` in the algebraic-closure model,

the node runs C2 (`Work.MotC2.aut_functionField`) over `L` — so that the point it produces is
`L`-rational, which is what makes the final Galois descent work — inside `M`, and the twisted
Galois actions `σS ^ (χ_i γ) ∘ γ̃` on `M`.

## Contents

* `asL2`, `asE2`, `asML` — the fields `L`, `E_L` and `M = L(E)`;
* `asIota0` (`𝕜`-linear) and `asIota` (`K`-linear) — the base-change map `M → Kb(E) = Om D`, with
  `asIota_algebraMap`, `asIota_genX`, `asIota_genY` and `asIota_injective`;
* `asKleinCoordM`, `asKleinFieldM`, `asLImageM` — the Klein coordinates of the `L`-model, and the
  two factors `κ(E) · L` of `M`, with the identities `asIota_map_asKleinFieldM`,
  `asIota_map_asLImageM`, `asKleinFieldM_eq_adjoin_genXY`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace Work.MotV5.LamAS

open WeierstrassCurve WeierstrassCurve.Affine

variable {𝕜 : Type} [Field 𝕜]

/-- The two-root Artin–Schreier field `L = K⟮asRoot f₁, asRoot f₂⟯ ⊆ Kb 𝕜`. -/
noncomputable def asL2 (f₁ f₂ : RatFunc 𝕜) : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜) :=
  IntermediateField.adjoin (RatFunc 𝕜)
    ({Work.MotV5.asRoot f₁, Work.MotV5.asRoot f₂} : Set (Work.MotV.Kb 𝕜))

theorem asRoot_mem_asL2_left (f₁ f₂ : RatFunc 𝕜) : Work.MotV5.asRoot f₁ ∈ asL2 f₁ f₂ :=
  IntermediateField.subset_adjoin _ _ (by simp [asL2])

theorem asRoot_mem_asL2_right (f₁ f₂ : RatFunc 𝕜) : Work.MotV5.asRoot f₂ ∈ asL2 f₁ f₂ :=
  IntermediateField.subset_adjoin _ _ (by simp [asL2])

instance asL2_isScalarTower (f₁ f₂ : RatFunc 𝕜) :
    IsScalarTower 𝕜 ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜) :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) x,
      ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)
        ((algebraMap 𝕜 (RatFunc 𝕜)) x),
      ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜) x])

/-- The inclusion `L ⊆ Kb 𝕜` as a `𝕜`-algebra homomorphism. -/
noncomputable def asInc (f₁ f₂ : RatFunc 𝕜) : ↥(asL2 (𝕜 := 𝕜) f₁ f₂) →ₐ[𝕜] Work.MotV.Kb 𝕜 where
  toFun := algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)
  map_one' := map_one _
  map_mul' := fun _ _ => map_mul _ _ _
  map_zero' := map_zero _
  map_add' := fun _ _ => map_add _ _ _
  commutes' := fun c => IsScalarTower.algebraMap_apply 𝕜 ↥(asL2 (𝕜 := 𝕜) f₁ f₂)
    (Work.MotV.Kb 𝕜) c

/-- The base-changed Klein model over `L`. -/
noncomputable abbrev asE2 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    WeierstrassCurve ↥(asL2 (𝕜 := 𝕜) f₁ f₂) :=
  D.E.baseChange ↥(asL2 (𝕜 := 𝕜) f₁ f₂)

/-- **The ambient field `M = L(E)`** of the Artin–Schreier LAM node. -/
noncomputable abbrev asML (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) : Type :=
  Affine.FunctionField (asE2 D f₁ f₂)

noncomputable instance asML_isScalarTower (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    IsScalarTower (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) :=
  IsScalarTower.of_algebraMap_eq (fun x => rfl)

/-- The `𝕜`-linear base-change map `M = L(E) → Kb(E) = Om D`. -/
noncomputable def asIota0 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    asML D f₁ f₂ →ₐ[𝕜] Work.MotV.Om D :=
  (Work.MotT.functionField_baseChange_map 𝕜 D.E ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)
    (asInc f₁ f₂)).choose

theorem asIota0_algebraMap (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asIota0 D f₁ f₂ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l) =
      algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) l :=
  (Work.MotT.functionField_baseChange_map 𝕜 D.E ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)
    (asInc f₁ f₂)).choose_spec.1 l

theorem asIota0_genX (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    asIota0 D f₁ f₂ (Work.MotV.genX (asE2 D f₁ f₂)) =
      Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜)) :=
  (Work.MotT.functionField_baseChange_map 𝕜 D.E ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)
    (asInc f₁ f₂)).choose_spec.2.1

theorem asIota0_genY (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    asIota0 D f₁ f₂ (Work.MotV.genY (asE2 D f₁ f₂)) =
      Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜)) :=
  (Work.MotT.functionField_baseChange_map 𝕜 D.E ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)
    (asInc f₁ f₂)).choose_spec.2.2.1

theorem asIota0_injective (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    Function.Injective (asIota0 D f₁ f₂) :=
  (Work.MotT.functionField_baseChange_map 𝕜 D.E ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (Work.MotV.Kb 𝕜)
    (asInc f₁ f₂)).choose_spec.2.2.2 (fun a b hab => Subtype.ext hab)

/-- **The `K`-linear base-change map `M = L(E) → Kb(E) = Om D`.**  (The `𝕜`-linear map `asIota0`
is automatically `K`-linear: it sends the constants of `L` by the inclusion, hence the constants of
`K` by the inclusion.) -/
noncomputable def asIota (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    asML D f₁ f₂ →ₐ[RatFunc 𝕜] Work.MotV.Om D where
  toFun := asIota0 D f₁ f₂
  map_one' := map_one _
  map_mul' := fun _ _ => map_mul _ _ _
  map_zero' := map_zero _
  map_add' := fun _ _ => map_add _ _ _
  commutes' := fun c => by
    have h1 : (algebraMap (RatFunc 𝕜) (asML D f₁ f₂)) c =
        (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂))
          ((algebraMap (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) c) :=
      IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) c
    rw [h1, asIota0_algebraMap]
    rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c]
    congr 1

@[simp]
theorem asIota_apply (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) (x : asML D f₁ f₂) :
    asIota D f₁ f₂ x = asIota0 D f₁ f₂ x := rfl

theorem asIota_algebraMap (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜)
    (l : ↥(asL2 (𝕜 := 𝕜) f₁ f₂)) :
    asIota D f₁ f₂ (algebraMap ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂) l) =
      algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) l :=
  asIota0_algebraMap D f₁ f₂ l

theorem asIota_genX (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    asIota D f₁ f₂ (Work.MotV.genX (asE2 D f₁ f₂)) =
      Work.MotV.genX (D.E.baseChange (Work.MotV.Kb 𝕜)) :=
  asIota0_genX D f₁ f₂

theorem asIota_genY (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    asIota D f₁ f₂ (Work.MotV.genY (asE2 D f₁ f₂)) =
      Work.MotV.genY (D.E.baseChange (Work.MotV.Kb 𝕜)) :=
  asIota0_genY D f₁ f₂

theorem asIota_injective (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    Function.Injective (asIota D f₁ f₂) :=
  asIota0_injective D f₁ f₂

/-- The Klein coordinates of the `L`-model, viewed in `M = L(E)`. -/
noncomputable def asKleinCoordM (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) (i : Fin 5) :
    asML D f₁ f₂ :=
  Work.MotV.kleinCoord D ↥(asL2 (𝕜 := 𝕜) f₁ f₂) i

/-- The Klein field of the `L`-model, inside `M = L(E)`. -/
noncomputable def asKleinFieldM (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    IntermediateField (RatFunc 𝕜) (asML D f₁ f₂) :=
  IntermediateField.adjoin (RatFunc 𝕜)
    (Set.range (fun i : Fin 5 => asKleinCoordM D f₁ f₂ i / asKleinCoordM D f₁ f₂ 0))

/-- The image of `L` inside `M = L(E)`. -/
noncomputable def asLImageM (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : RatFunc 𝕜) :
    IntermediateField (RatFunc 𝕜) (asML D f₁ f₂) :=
  (IsScalarTower.toAlgHom (RatFunc 𝕜) ↥(asL2 (𝕜 := 𝕜) f₁ f₂) (asML D f₁ f₂)).fieldRange

end Work.MotV5.LamAS
