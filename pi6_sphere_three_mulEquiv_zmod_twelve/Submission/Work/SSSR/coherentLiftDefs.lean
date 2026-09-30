import Mathlib
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.SSSR.sigmaVert_face
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial
noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The `0`-th vertex `v₀` of `Δ[n]`. -/
abbrev ssetVertex (n : ℕ) : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) _⦋0⦌ :=
  (SSet.stdSimplex.obj₀Equiv (n := n)).symm 0

/-- **The inclusion `Sing (p⁻¹b) ⟶ Δ[n] ⊗ Sing (p⁻¹b)`, `τ ↦ (v₀, τ)`.** -/
noncomputable def vertIncl (p : C(E, B)) (b : B) (n : ℕ) :
    Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b) ⟶
      ((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
        Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) :=
  CartesianMonoidalCategory.lift
    (SSet.const (X := Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (ssetVertex n)) (𝟙 _)

@[simp]
lemma vertIncl_fst (p : C(E, B)) (b : B) (n : ℕ) :
    vertIncl p b n ≫ SemiCartesianMonoidalCategory.fst _ _ =
      SSet.const (X := Work.SSSR.sSing (Work.SSSR.StemsB.fibre p b)) (ssetVertex n) :=
  CartesianMonoidalCategory.lift_fst _ _

@[simp]
lemma vertIncl_snd (p : C(E, B)) (b : B) (n : ℕ) :
    vertIncl p b n ≫ SemiCartesianMonoidalCategory.snd _ _ = 𝟙 _ :=
  CartesianMonoidalCategory.lift_snd _ _

end

end Work.SSSR
