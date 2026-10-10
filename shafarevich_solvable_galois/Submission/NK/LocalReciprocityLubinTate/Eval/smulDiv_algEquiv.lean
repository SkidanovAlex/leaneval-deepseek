import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.LocalField.Basic
import Submission.NK.LocalReciprocityLubinTate.Eval.TorsionAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Eval

noncomputable section

universe u

open LTtorsionRing

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **Naturality of the torsion-point evaluation under `F`-algebra automorphisms.**  For
`x ∈ Λ_n` and `y ∈ T_n = 𝒪[F][T]/(f^{(n)}(T))`, the `F`-algebra automorphism `σ` of the
algebraic closure transports `evMap x y` to `evMap (σ x) y`:

  `σ (evMap x y) = evMap (σ x) y`.

The two sides are `𝒪[F]`-algebra homomorphisms `T_n → F̄` (the left one because `σ` fixes `F`,
hence `𝒪[F]`) which agree on the class `τ` of `T`, so they agree by `AdjoinRoot.ringHom_ext`;
this in turn reduces to `AlgEquiv.commutes` on the coefficients. -/
theorem evMap_comp_algEquiv
    (π : ↥(ValuativeRel.valuation F).integer) (q n : ℕ) (hq : 2 ≤ q)
    (x : AlgebraicClosure F) (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n)
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (hσx : σ x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n)
    (y : LTtorsionRing F π q n) :
    σ (evMap π q n hq x hx y) = evMap π q n hq (σ x) hσx y := by
  -- `σ ∘ evMap x` and `evMap (σ x)` are both `𝒪[F]`-algebra maps `T_n → F̄`; by uniqueness of
  -- the lift from `𝒪[F]` with `τ ↦ σ x` (`AdjoinRoot.ringHom_ext`) they coincide.
  have key : (((σ : AlgebraicClosure F ≃+* AlgebraicClosure F) :
        AlgebraicClosure F →+* AlgebraicClosure F)).comp (evMap π q n hq x hx)
      = evMap π q n hq (σ x) hσx := by
    apply AdjoinRoot.ringHom_ext (p := NK.LocalReciprocityLubinTate.LTpolyIter π q n)
    · -- the two composites agree on the base ring `𝒪[F]`: both reduce to `𝒪[F] → F ↪ F̄`,
      -- because `σ` is `F`-linear.
      rw [RingHom.comp_assoc]
      rw [show (evMap π q n hq x hx).comp
            (AdjoinRoot.of (NK.LocalReciprocityLubinTate.LTpolyIter π q n))
          = (algebraMap F (AlgebraicClosure F)).comp (algebraMap (O F) F) from by
        rw [evMap]; exact AdjoinRoot.lift_comp_of _]
      rw [show (evMap π q n hq (σ x) hσx).comp
            (AdjoinRoot.of (NK.LocalReciprocityLubinTate.LTpolyIter π q n))
          = (algebraMap F (AlgebraicClosure F)).comp (algebraMap (O F) F) from by
        rw [evMap]; exact AdjoinRoot.lift_comp_of _]
      rw [← RingHom.comp_assoc,
        show (((σ : AlgebraicClosure F ≃+* AlgebraicClosure F) :
            AlgebraicClosure F →+* AlgebraicClosure F)).comp (algebraMap F (AlgebraicClosure F))
              = algebraMap F (AlgebraicClosure F) from RingHom.ext fun r => σ.commutes r]
    · -- both send the class `τ` of `T` to `σ x`.
      show σ (evMap π q n hq x hx (LTtorsionRing.tau π q n))
          = evMap π q n hq (σ x) hσx (LTtorsionRing.tau π q n)
      rw [evMap_tau, evMap_tau]
  exact congr_fun (congr_arg DFunLike.coe key) y

/-- **The Galois action commutes with the `𝒪[F]`-action on `Λ_n`.**  For `x ∈ Λ_n` and an
`F`-algebra automorphism `σ` of `AlgebraicClosure F` with `σ x ∈ Λ_n`,

  `σ (a • x) = a • (σ x)`,

where `a • x = smulDiv π hπ q n hq M hx a = evMap x ([a]_n)` is the Lubin–Tate action of
`a ∈ 𝒪[F]` (`Eval/TorsionAction.lean`).  This says that `σ` is `𝒪[F]`-linear for the
`𝒪[F]`-module structure of Milne, *CFT*, §I.3 on `Λ_n`.

Both sides are evaluations of the same class `[a]_n = evalTau (M.action a)` of the ambient ring
`T_n`, so the statement is immediate from `evMap_comp_algEquiv`. -/
theorem smulDiv_algEquiv {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (q n : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (↥(ValuativeRel.valuation F).integer) π q)
    (x : AlgebraicClosure F) (hx : x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n)
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (hσx : σ x ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q n)
    (a : ↥(ValuativeRel.valuation F).integer) :
    σ (NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ q n hq M hx a)
      = NK.LocalReciprocityLubinTate.Eval.smulDiv π hπ q n hq M hσx a := by
  -- unfold `smulDiv` on both sides: it is `evMap` at the class `[a]_n`.
  show σ (evMap π q n hq x hx (actionTau π hπ q n hq M a))
      = evMap π q n hq (σ x) hσx (actionTau π hπ q n hq M a)
  exact evMap_comp_algEquiv π q n hq x hx σ hσx (actionTau π hπ q n hq M a)

end

end NK.LocalReciprocityLubinTate.Eval
