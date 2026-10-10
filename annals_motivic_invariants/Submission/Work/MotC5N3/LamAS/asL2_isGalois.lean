import Mathlib
import Submission.Work.MotC5N3.LamAS.asML
import Submission.Work.MotC5N3.LamAS.asRootField_galois_basic

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The two-root Artin–Schreier field is finite Galois over `K` (general base field)

Port of `Submission/Work/MotV5/LamAS/asL2_isGalois.lean`.
-/

namespace Work.MotC5N3.LamAS

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-- The single-root Artin–Schreier field `K⟮asRoot g⟯` is finite dimensional over `K`. -/
theorem asRootFieldAux_finiteDimensional {K : Type} [Field K] (g : K) :
    FiniteDimensional K
      ↥(IntermediateField.adjoin K ({asRoot g} : Set (KbA K))) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_asRoot g)

/-- `asL2 f₁ f₂` is the compositum of the two single-root fields. -/
theorem asL2_eq_sup {K : Type} [Field K] (f₁ f₂ : K) :
    asL2 f₁ f₂ =
      IntermediateField.adjoin K ({asRoot f₁} : Set (KbA K)) ⊔
        IntermediateField.adjoin K ({asRoot f₂} : Set (KbA K)) := by
  have hset : ({asRoot f₁, asRoot f₂} : Set (KbA K))
      = ({asRoot f₁} : Set (KbA K)) ∪ {asRoot f₂} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  rw [asL2, hset, IntermediateField.adjoin_union]

/-- The two-root Artin–Schreier field `L = K⟮asRoot f₁, asRoot f₂⟯` is a finite Galois extension
of `K`. -/
theorem asL2_isGalois (K : Type) [Field K] [CharP K 5] (f₁ f₂ : K) :
    IsGalois K ↥(asL2 f₁ f₂) ∧
      FiniteDimensional K ↥(asL2 f₁ f₂) := by
  rw [asL2_eq_sup]
  let A : IntermediateField K (KbA K) :=
    IntermediateField.adjoin K ({asRoot f₁} : Set (KbA K))
  let B : IntermediateField K (KbA K) :=
    IntermediateField.adjoin K ({asRoot f₂} : Set (KbA K))
  haveI : FiniteDimensional K ↥A := asRootFieldAux_finiteDimensional f₁
  haveI : FiniteDimensional K ↥B := asRootFieldAux_finiteDimensional f₂
  haveI : IsGalois K ↥A := isGalois_asRootFieldAux f₁
  haveI : IsGalois K ↥B := isGalois_asRootFieldAux f₂
  haveI : FiniteDimensional K ↥(A ⊔ B) := inferInstance
  haveI : Normal K ↥(A ⊔ B) := inferInstance
  haveI : Algebra.IsSeparable K ↥(A ⊔ B) := inferInstance
  exact ⟨⟨⟩, inferInstance⟩

end Work.MotC5N3.LamAS
