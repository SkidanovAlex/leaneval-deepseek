import Mathlib
import Submission.Work.Kunneth.Chapter
import Submission.Work.Cohomology.AlexanderWhitney

/-!
# Coefficient-generic Eilenberg–Zilber shuffle data

The Eilenberg–Zilber shuffle computations of `Submission/Work/Kunneth/` and
`Submission/Work/KunnethEZ/` are carried out over the coefficient ring `ℤ`.  The rational
Künneth-type statements of subproject SERRE need the analogous objects over an arbitrary
commutative ring `R` (in practice `R = ℚ`).  This file provides the definitions:

* `Work.Serre.ezCellGenR` — the shuffle cell `(σ ∘ a_S, τ ∘ b_S)` of the tensor product `X ⊗ Y`;
* `Work.Serre.ezGenR` — the shuffle chain of a pair of simplices, the sum over the shuffles `S` of
  `shufSign S • (cell S)`;
* `Work.Serre.ezShufR`, `Work.Serre.ezBilR` — the shuffle chain as a *bilinear* map on chains
  (the `R`-analogue of `Work.Cohomology.Kunneth.ezBil`), with the computation rules `ezShufR_ι`,
  `ezBilR_ι` and the value `ezBilR_gen` on generators.  Bilinearity is *definitional* here (it is
  the universal property of the chain complex), which is what lets the Kronecker rule be reduced to
  its value on generators;
* `Work.Serre.crossCochainR` — the cross product of two cochains,
  `(α × β)(x,y) = α(x_front) · β(y_back)` (the `R`-analogue of `Work.Kunneth.crossCochain`), with
  the computation rule `crossCochainR_apply` on a generating simplex.

The evaluation theorem — the analogue over `R` of `Work.Kunneth.crossCochain_ezGen`, i.e. the value
of `α × β` on the shuffle chain of a pair of simplices when `β` annihilates the degenerate
simplices of `Y` — is the next layer; see `Work.Serre.crossCochainR_ezGenR`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Serre

noncomputable section

open Work.Cohomology

variable (R : Type) [CommRing R]

/-- The shuffle cell of a pair of simplices: the pair `(σ ∘ a_S, τ ∘ b_S)` in `X ⊗ Y`. -/
abbrev ezCellGenR (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌)
    (S : Work.Cohomology.Crux33.PShuffle p q) : (X ⊗ Y) _⦋p + q⦌ :=
  (X.map (Work.Cohomology.Crux33.aHom S.1 S.2).op σ,
    Y.map (Work.Cohomology.Crux33.bHom S.1 S.2).op τ)

/-- **The Eilenberg–Zilber shuffle chain of a pair of simplices**, over `R`: the sum over the
`(p,q)`-shuffles of the corresponding shuffle cell, with the shuffle sign. -/
noncomputable def ezGenR (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    ((X ⊗ Y).chainComplex (ModuleCat.of R R)).X (p + q) :=
  ∑ S : Work.Cohomology.Crux33.PShuffle p q, Work.Cohomology.Crux33.shufSign S.1 •
    ((X ⊗ Y).ιChainComplex (R := ModuleCat.of R R) (ezCellGenR p q X Y σ τ S)).hom 1

/-- The shuffle chain as a linear map in the second variable, for a fixed simplex `σ` of `X`. -/
noncomputable def ezShufR (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) :
    (Y.chainComplex (ModuleCat.of R R)).X q ⟶
      ModuleCat.of R (((X ⊗ Y).chainComplex (ModuleCat.of R R)).X (p + q)) :=
  (Y.isColimitChainComplexXCofan (ModuleCat.of R R) q).desc
    (Cofan.mk (ModuleCat.of R (((X ⊗ Y).chainComplex (ModuleCat.of R R)).X (p + q)))
      (fun τ => ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (ezGenR R p q X Y σ τ))))

/-- **The shuffle chain as a bilinear map**: linear in the first variable (by the universal
property of the chain complex of `X`) with values in the linear maps in the second variable. -/
noncomputable def ezBilR (p q : ℕ) (X Y : SSet) :
    (X.chainComplex (ModuleCat.of R R)).X p ⟶
      ModuleCat.of R ((Y.chainComplex (ModuleCat.of R R)).X q →ₗ[R]
        ((X ⊗ Y).chainComplex (ModuleCat.of R R)).X (p + q)) :=
  (X.isColimitChainComplexXCofan (ModuleCat.of R R) p).desc
    (Cofan.mk (ModuleCat.of R ((Y.chainComplex (ModuleCat.of R R)).X q →ₗ[R]
        ((X ⊗ Y).chainComplex (ModuleCat.of R R)).X (p + q)))
      (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (ezShufR R p q X Y σ).hom)))

/-- The defining property of `ezShufR` on a generator. -/
lemma ezShufR_ι (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    Y.ιChainComplex (R := ModuleCat.of R R) τ ≫ ezShufR R p q X Y σ
      = ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (ezGenR R p q X Y σ τ)) :=
  Cofan.IsColimit.fac _ _ _

/-- The defining property of `ezBilR` on a generator. -/
lemma ezBilR_ι (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) :
    X.ιChainComplex (R := ModuleCat.of R R) σ ≫ ezBilR R p q X Y
      = ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (ezShufR R p q X Y σ).hom) :=
  Cofan.IsColimit.fac _ _ _

/-- **The value of the bilinear shuffle on a pair of generators** is the shuffle chain of the pair
of simplices. -/
lemma ezBilR_gen (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    (ezBilR R p q X Y).hom ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
      ((Y.ιChainComplex (R := ModuleCat.of R R) τ).hom 1) = ezGenR R p q X Y σ τ := by
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶
      ModuleCat.of R (((X ⊗ Y).chainComplex (ModuleCat.of R R)).X (p + q)))
      => g.hom (1 : R)) (ezShufR_ι R p q X Y σ τ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] at h2
  have h := congrArg (fun (g : ModuleCat.of R R ⟶
      ModuleCat.of R ((Y.chainComplex (ModuleCat.of R R)).X q →ₗ[R]
        ((X ⊗ Y).chainComplex (ModuleCat.of R R)).X (p + q)))
      => g.hom (1 : R)) (ezBilR_ι R p q X Y σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] at h
  rw [h, h2]

/-- The family of morphisms `R ⟶ R` whose coproduct descent is the cross product cochain. -/
noncomputable def crossCochainRFam (X Y : SSet) (p q : ℕ)
    (α : Cochain R X p) (β : Cochain R Y q) :
    (z : (X ⊗ Y) _⦋p + q⦌) → ModuleCat.of R R ⟶ ModuleCat.of R R :=
  fun z => ModuleCat.ofHom
    (LinearMap.toSpanSingleton R R
      (genEval R X α (frontFace X p (p + q) (Nat.le_add_right p q) z.1) *
        genEval R Y β (Work.Kunneth.backFaceLE Y q (p + q) (by omega) z.2)))

/-- **The cross product of two cochains** over `R`: the cochain on `X ⊗ Y` whose value on a simplex
`(x,y)` is `α(x_front) · β(y_back)`. -/
noncomputable def crossCochainR (X Y : SSet) (p q : ℕ)
    (α : Cochain R X p) (β : Cochain R Y q) : Cochain R (X ⊗ Y) (p + q) :=
  ModuleCat.Hom.hom (Cofan.IsColimit.desc
    ((X ⊗ Y).isColimitChainComplexXCofan (ModuleCat.of R R) (p + q))
    (crossCochainRFam R X Y p q α β))

end

end Work.Serre
