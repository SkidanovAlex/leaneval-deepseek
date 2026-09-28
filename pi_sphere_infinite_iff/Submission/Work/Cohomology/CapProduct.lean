import Mathlib
import Submission.Work.Cohomology.CupRing

/-!
# The cap product of a cochain with singular chains

The *cap product* of a degree-`n` cochain `α` with singular chains is the degree `-n` map
`C_{n+m}(X) ⟶ C_m(X)` defined on a generator (a singular simplex) `σ` by

  `σ ⌢ α = α(σ_front) • σ_back`,

where `σ_front` is the face of `σ` spanned by its first `n+1` vertices (`frontFace`) and `σ_back`
the face spanned by its last `m+1` vertices (`backFace`).  This is the Alexander–Whitney
counterpart of the cup product of `Submission/Work/Cohomology/AlexanderWhitney.lean`: the same
splitting `σ = σ_front ∪ σ_back` of the simplices is used, but the cochain is contracted with the
front part and the back part survives as a chain.

This file contains the definition and its value on generators; the properties (the boundary
formula, linearity in the cochain, the descent to a pairing `H^n(X) × H_{n+m}(X) → H_m(X)`, and
its compatibility with the cup product and the unit) are delegated, since they only depend on the
definitions here.

## Sign conventions

With the chain-level differential `d = Σ_i (-1)^i δ_i` (`ιChainComplex_d`) and the coboundary
`δα = α ∘ d` (`cochainDiff`, the plain transpose, *no* sign), the boundary formula reads

  `d (c ⌢ α) = (-1)^n • ((d c) ⌢ α - c ⌢ (δα))`   (for `deg c = n + (m+1)`),

so that for a cocycle `α` the map `c ↦ c ⌢ α` is a chain map up to the global sign `(-1)^n`, and
hence induces `H_{n+m}(X) ⟶ H_m(X)`.  (Specialised check: for `n = 0` this is
`d (c ⌢ α) = (d c) ⌢ α - c ⌢ (δα)`, the classical formula.)
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

/-- **The cap product** of a degree `n` cochain with the `(n+m)`-chains: the morphism of modules
`C_{n+m}(X) ⟶ C_m(X)` sending a generator `σ` to `α(σ_front) • σ_back`. -/
def capHom {n : ℕ} (α : Cochain R X n) (m : ℕ) :
    (X.chainComplex (ModuleCat.of R R)).X (n + m) ⟶ (X.chainComplex (ModuleCat.of R R)).X m :=
  (X.isColimitChainComplexXCofan (ModuleCat.of R R) (n + m)).desc
    (Cofan.mk ((X.chainComplex (ModuleCat.of R R)).X m)
      (fun σ : X _⦋n + m⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton R R
          (genEval R X α (frontFace X n (n + m) (Nat.le_add_right n m) σ))) ≫
        X.ιChainComplex (R := ModuleCat.of R R) (backFace X n m σ)))

/-- The cap product on a generator: `σ ⌢ α = α(σ_front) • σ_back`. -/
@[simp]
theorem ιChainComplex_capHom {n m : ℕ} (α : Cochain R X n) (σ : X _⦋n + m⦌) :
    X.ιChainComplex (R := ModuleCat.of R R) σ ≫ capHom R X α m =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R R
        (genEval R X α (frontFace X n (n + m) (Nat.le_add_right n m) σ))) ≫
      X.ιChainComplex (R := ModuleCat.of R R) (backFace X n m σ) :=
  Cofan.IsColimit.fac _ _ _

/-- **The cap product** of a degree `n` cochain with chains, as a linear map
`C_{n+m}(X) →ₗ C_m(X)`. -/
def cap {n : ℕ} (α : Cochain R X n) (m : ℕ) :
    (X.chainComplex (ModuleCat.of R R)).X (n + m) →ₗ[R]
      (X.chainComplex (ModuleCat.of R R)).X m :=
  (capHom R X α m).hom

/-- The cap product evaluated on a generator. -/
theorem cap_apply {n m : ℕ} (α : Cochain R X n) (σ : X _⦋n + m⦌) :
    cap R X α m (((X.ιChainComplex (R := ModuleCat.of R R) σ)).hom 1) =
      genEval R X α (frontFace X n (n + m) (Nat.le_add_right n m) σ) •
        (((X.ιChainComplex (R := ModuleCat.of R R) (backFace X n m σ))).hom 1) := by
  have h2 := congrArg
    (fun (g : ModuleCat.of R R ⟶ (X.chainComplex (ModuleCat.of R R)).X m) => g.hom 1)
    (ιChainComplex_capHom R X α σ)
  have h4 : (ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of R R) (backFace X n m σ)))
        ((ModuleCat.Hom.hom (ModuleCat.ofHom (LinearMap.toSpanSingleton R R
          (genEval R X α (frontFace X n (n + m) (Nat.le_add_right n m) σ))))) 1) =
      genEval R X α (frontFace X n (n + m) (Nat.le_add_right n m) σ) •
        (ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of R R) (backFace X n m σ))) 1 := by
    rw [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul, ← map_smul,
      smul_eq_mul, mul_one]
  simpa only [cap, ModuleCat.hom_comp, LinearMap.comp_apply, h4] using h2

/-- The degree transport `n + (m+1) = (n+1) + m` used in the boundary formula for the cap
product: the two associations of the sum of `n`, `1` and `m`. -/
theorem capIdx (n m : ℕ) : n + (m + 1) = (n + 1) + m :=
  ((Nat.add_assoc n 1 m).trans (congrArg (fun k : ℕ => n + k) (Nat.add_comm 1 m))).symm

end

end Work.Cohomology
