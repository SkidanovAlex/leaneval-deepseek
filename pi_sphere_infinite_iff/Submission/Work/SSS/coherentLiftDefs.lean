import Mathlib
import Submission.Work.SSS.serreE1Defs
import Submission.Work.SSS.sigmaVert_face

/-!
# Vocabulary for the coherent lift family of a Serre fibration over a simplex

For a Serre fibration `p : E → B`, a base point `b : B` and a simplex `σ : Δ[n] ⟶ Sing B`, the
Eilenberg–Zilber chain map `C_*(F_b) ⟶ pieceAlong (sSingP p) σ` is built from a *simplicial* map

  `Φ^σ : Δ[n] ⊗ Sing (p⁻¹ b) ⟶ Sing E`

which is a lift of `pr₁ ≫ σ : Δ[n] ⊗ Sing (p⁻¹ b) ⟶ Sing B` and restricts to the inclusion of the
fibre on `{v₀} ⊗ Sing (p⁻¹ b)`.  Being simplicial, such a family is automatically coherent, which is
what makes the Eilenberg–Zilber boundary formula apply verbatim.

This file only records the vocabulary needed to *state* the existence of such a family
(`Work.SSS.exists_coherentLiftFamily`, proved elsewhere); the construction itself is the standard
induction on the dimension, gluing the families of the faces `d_jσ` (`j ≥ 1`) over the horn
`Λ[n,0] ⊗ Sing (p⁻¹ b)` and extending by the right lifting property of the Kan fibration `sSingP p`
against the anodyne extension `Sing (p⁻¹ b) ◁ Λ[n,0].ι`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The `0`-th vertex `v₀` of `Δ[n]`. -/
abbrev ssetVertex (n : ℕ) : (SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) _⦋0⦌ :=
  (SSet.stdSimplex.obj₀Equiv (n := n)).symm 0

/-- **The inclusion `Sing (p⁻¹b) ⟶ Δ[n] ⊗ Sing (p⁻¹b)`, `τ ↦ (v₀, τ)`.** -/
noncomputable def vertIncl (p : C(E, B)) (b : B) (n : ℕ) :
    Work.SSS.sSing (Work.StemsB.fibre p b) ⟶
      ((SSet.stdSimplex.obj (SimplexCategory.mk n) : SSet.{0}) ⊗
        Work.SSS.sSing (Work.StemsB.fibre p b)) :=
  CartesianMonoidalCategory.lift
    (SSet.const (X := Work.SSS.sSing (Work.StemsB.fibre p b)) (ssetVertex n)) (𝟙 _)

@[simp]
lemma vertIncl_fst (p : C(E, B)) (b : B) (n : ℕ) :
    vertIncl p b n ≫ SemiCartesianMonoidalCategory.fst _ _ =
      SSet.const (X := Work.SSS.sSing (Work.StemsB.fibre p b)) (ssetVertex n) :=
  CartesianMonoidalCategory.lift_fst _ _

@[simp]
lemma vertIncl_snd (p : C(E, B)) (b : B) (n : ℕ) :
    vertIncl p b n ≫ SemiCartesianMonoidalCategory.snd _ _ = 𝟙 _ :=
  CartesianMonoidalCategory.lift_snd _ _

end

end Work.SSS
