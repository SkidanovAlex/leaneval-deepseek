import Mathlib
import Submission.Work.MotV5.LamAS.asML
import Submission.Work.MotV5.LamAS.asRootField_galois_basic

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The two-root Artin–Schreier field is finite Galois over `K = 𝕜(t)`

`L = asL2 f₁ f₂ = K⟮asRoot f₁, asRoot f₂⟯` is the compositum of the two single-root Artin–Schreier
fields `K⟮asRoot fᵢ⟯`, each of which is a splitting field of the *separable* polynomial
`X⁵ - X - fᵢ` over `K = RatFunc 𝕜` (`isGalois_asRootFieldAux`).  A compositum of finite Galois
extensions is finite Galois, so `L/K` is finite Galois.

Note that no hypothesis on `f₁, f₂` is needed: `X⁵ - X - fᵢ` is separable for *every* `fᵢ`
(its derivative is the unit `-1`), and `K⟮asRoot fᵢ⟯` is a splitting field of it (the remaining
roots are `asRoot fᵢ + k`, `k ∈ 𝔽₅`).  Both `Normal.sup` and `Algebra.IsSeparable` for a
compositum are instances.
-/

namespace Work.MotV5.LamAS

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

/-- The single-root Artin–Schreier field `K⟮asRoot g⟯` is finite dimensional over `K`. -/
theorem asRootFieldAux_finiteDimensional {𝕜 : Type} [Field 𝕜] (g : RatFunc 𝕜) :
    FiniteDimensional (RatFunc 𝕜)
      ↥(IntermediateField.adjoin (RatFunc 𝕜) ({Work.MotV5.asRoot g} : Set (Work.MotV.Kb 𝕜))) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_asRoot g)

/-- `asL2 f₁ f₂` is the compositum of the two single-root fields. -/
theorem asL2_eq_sup {𝕜 : Type} [Field 𝕜] (f₁ f₂ : RatFunc 𝕜) :
    asL2 (𝕜 := 𝕜) f₁ f₂ =
      IntermediateField.adjoin (RatFunc 𝕜) ({Work.MotV5.asRoot f₁} : Set (Work.MotV.Kb 𝕜)) ⊔
        IntermediateField.adjoin (RatFunc 𝕜) ({Work.MotV5.asRoot f₂} : Set (Work.MotV.Kb 𝕜)) := by
  have hset : ({Work.MotV5.asRoot f₁, Work.MotV5.asRoot f₂} : Set (Work.MotV.Kb 𝕜))
      = ({Work.MotV5.asRoot f₁} : Set (Work.MotV.Kb 𝕜)) ∪ {Work.MotV5.asRoot f₂} := by
    ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  rw [asL2, hset, IntermediateField.adjoin_union]

/-- The two-root Artin–Schreier field `L = K⟮asRoot f₁, asRoot f₂⟯` is a finite Galois extension of `K = RatFunc 𝕜` (it is the compositum of the splitting fields of the separable polynomials `X⁵ - X - fᵢ`, whose roots are the `asRoot fᵢ + k`, `k ∈ 𝔽₅`). -/
theorem asL2_isGalois (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (f₁ f₂ : RatFunc 𝕜) :
    IsGalois (RatFunc 𝕜) ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) ∧
      FiniteDimensional (RatFunc 𝕜) ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂) := by
  rw [asL2_eq_sup]
  let A : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜) :=
    IntermediateField.adjoin (RatFunc 𝕜) ({Work.MotV5.asRoot f₁} : Set (Work.MotV.Kb 𝕜))
  let B : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜) :=
    IntermediateField.adjoin (RatFunc 𝕜) ({Work.MotV5.asRoot f₂} : Set (Work.MotV.Kb 𝕜))
  haveI : FiniteDimensional (RatFunc 𝕜) ↥A := asRootFieldAux_finiteDimensional f₁
  haveI : FiniteDimensional (RatFunc 𝕜) ↥B := asRootFieldAux_finiteDimensional f₂
  haveI : IsGalois (RatFunc 𝕜) ↥A := isGalois_asRootFieldAux f₁
  haveI : IsGalois (RatFunc 𝕜) ↥B := isGalois_asRootFieldAux f₂
  haveI : FiniteDimensional (RatFunc 𝕜) ↥(A ⊔ B) := inferInstance
  haveI : Normal (RatFunc 𝕜) ↥(A ⊔ B) := inferInstance
  haveI : Algebra.IsSeparable (RatFunc 𝕜) ↥(A ⊔ B) := inferInstance
  exact ⟨⟨⟩, inferInstance⟩

end Work.MotV5.LamAS
