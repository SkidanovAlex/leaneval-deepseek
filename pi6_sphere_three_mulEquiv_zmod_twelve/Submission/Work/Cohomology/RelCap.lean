import Mathlib
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.CapProduct
import Submission.Work.Cohomology.Kronecker
import Submission.Work.Cohomology.cupNatural
import Submission.Work.Cohomology.relChainsProjective

/-!
# The relative cap product

For a topological space `X` and a subset `A ⊆ X`, a cochain `α ∈ C^n(X,A;R)` (i.e. a cochain
vanishing on chains supported in `A`, `Work.Cohomology.relKern`) kills the chains supported in `A`
under the cap product:

  `σ ⌢ α = α(σ_front) • σ_back = 0`  whenever the simplex `σ` lies in `A`,

because the front face of such a simplex also lies in `A` (`app_frontFace`).  Consequently the
absolute cap product `C_{n+m}(X) ⟶ C_m(X)` descends to the **relative cap product**

  `⌢ : C^n(X,A;R) ⟶ C_{n+m}(X,A;R) →ₗ C_m(X;R)`,

where `C_k(X,A;R) = C_k(X;R)/C_k(A;R)` is the quotient by the chains supported in `A`.  The
classical relative cap product `H^p(X,A) × H_q(X,A) → H_{q-p}(X)` is the descended pairing, which
is the algebraic input of Lefschetz duality (the self-intersection form on the middle cohomology
of a compact oriented manifold with boundary).

This file contains

* `relChainsModule` — the relative chains in a single degree;
* `genEval_eq_zero_of_mem_relKern` — a relative cochain vanishes on every simplex coming from `A`;
* `cap_chainMap_gen` and `capMap_comp_chainComplexMap` — the cap product with a relative cochain
  kills the chains supported in `A`;
* `relCapHalf` — the descended (relative) cap product, with its computation rules
  `cokernel_π_relCapHalf` and `relCapHalf_apply`;
* `relKronecker_cap_cup` — the relative cap/cup identity `β(c ⌢ α) = (α ⌣ β)(c)`.

Sign and degree conventions are those of `Submission/Work/Cohomology/CapProduct.lean`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R]

/-! ## Relative chains -/

/-- The module of relative `k`-chains `C_k(X,A;R)`: the quotient of the singular `k`-chains of `X`
by the chains supported in `A`. -/
abbrev relChainsModule (X : TopCat) (A : Set X) (k : ℕ) : ModuleCat R :=
  cokernel ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
    (ModuleCat.of R R)).f k)

/-- The singular `k`-chains of a topological space, as the chains of its singular simplicial set. -/
abbrev singChains (X : TopCat) (k : ℕ) : ModuleCat R :=
  ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X k

/-- **Over `ℤ` the relative chains of this file agree with the relative chain complex
`relChains`** of `Submission/Work/Cohomology/HomologyPairSequence.lean` (`relChains_cokernelIso`),
so the relative cap product below is available on that complex. -/
theorem relChainsModule_iso_relChains (X : TopCat) (A : Set X) (n : ℕ) :
    Nonempty (relChainsModule ℤ X A n ≅ (relChains X A).X n) :=
  ⟨(eqToIso (show relChainsModule ℤ X A n = cokernel ((inclChains X A).f n) from rfl)).symm
    ≪≫ (relChains_cokernelIso X A n).symm⟩

/-! ## The cap product kills chains supported in `A` -/

/-- A cochain that vanishes on `A` vanishes on every singular simplex of `X` that comes from `A`. -/
theorem genEval_eq_zero_of_mem_relKern (X : TopCat) (A : Set X) {n : ℕ}
    (α : Cochain R (TopCat.toSSet.obj X) n) (hα : α ∈ relKern R X A n)
    (τ : (TopCat.toSSet.obj (TopCat.of A)) _⦋n⦌) :
    genEval R (TopCat.toSSet.obj X) α ((TopCat.toSSet.map (subtypeIncl X A)).app _ τ) = 0 := by
  have h1 : ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
      (ModuleCat.of R R)).f n).hom.dualMap α = 0 := by
    have h := hα
    rw [relKern, LinearMap.mem_ker, restr, dualChainMap_f_hom, chainMap_f_eq] at h
    exact h
  have h2 : α (((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
      (ModuleCat.of R R)).f n).hom
      ((SSet.ιChainComplex (X := TopCat.toSSet.obj (TopCat.of A))
        (R := ModuleCat.of R R) τ).hom 1)) = 0 := by
    have h := LinearMap.congr_fun h1
      ((SSet.ιChainComplex (X := TopCat.toSSet.obj (TopCat.of A))
        (R := ModuleCat.of R R) τ).hom 1)
    simpa only [LinearMap.dualMap_apply, LinearMap.comp_apply, LinearMap.zero_apply] using h
  have h3 := SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (TopCat.of A))
    (Y := TopCat.toSSet.obj X) (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of R R) τ
  have h4 := congrArg (fun g => g.hom 1) h3
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h4
  rw [h4] at h2
  simpa only [genEval] using h2

/-- The front face of a simplex coming from `A` (of a higher-dimensional simplex coming from `A`)
is again a simplex coming from `A`, hence is killed by a relative cochain. -/
theorem genEval_frontFace_eq_zero (X : TopCat) (A : Set X) {n m : ℕ}
    (α : Cochain R (TopCat.toSSet.obj X) n) (hα : α ∈ relKern R X A n)
    (τ : (TopCat.toSSet.obj (TopCat.of A)) _⦋n + m⦌) :
    genEval R (TopCat.toSSet.obj X) α
      (frontFace (TopCat.toSSet.obj X) n (n + m) (Nat.le_add_right n m)
        ((TopCat.toSSet.map (subtypeIncl X A)).app _ τ)) = 0 := by
  rw [← app_frontFace]
  exact genEval_eq_zero_of_mem_relKern R X A α hα
    (frontFace (TopCat.toSSet.obj (TopCat.of A)) n (n + m) (Nat.le_add_right n m) τ)

/-- **The cap product of a relative cochain with a chain supported in `A` vanishes**, on
generators: the front face of a simplex lying in `A` is again a simplex lying in `A`. -/
theorem cap_chainMap_gen (X : TopCat) (A : Set X) {n m : ℕ} (α : relKern R X A n)
    (τ : (TopCat.toSSet.obj (TopCat.of A)) _⦋n + m⦌) :
    cap R (TopCat.toSSet.obj X) α.1 m
      (((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
          (ModuleCat.of R R)).f (n + m)).hom
        ((SSet.ιChainComplex (X := TopCat.toSSet.obj (TopCat.of A))
          (R := ModuleCat.of R R) τ).hom 1)) = 0 := by
  have h4 : ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
      (ModuleCat.of R R)).f (n + m)).hom
      ((SSet.ιChainComplex (X := TopCat.toSSet.obj (TopCat.of A))
        (R := ModuleCat.of R R) τ).hom 1)
      = (SSet.ιChainComplex (X := TopCat.toSSet.obj X) (R := ModuleCat.of R R)
          ((TopCat.toSSet.map (subtypeIncl X A)).app _ τ)).hom 1 := by
    have h3 := SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (TopCat.of A))
      (Y := TopCat.toSSet.obj X) (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of R R) τ
    have h4' := congrArg (fun g => g.hom 1) h3
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h4'
  rw [h4, cap_apply]
  rw [genEval_frontFace_eq_zero R X A α.1 α.2 τ]
  simp

/-- **The cap product with a relative cochain kills the chains supported in `A`.** -/
theorem capMap_comp_chainComplexMap (X : TopCat) (A : Set X) {n : ℕ}
    (α : relKern R X A n) (m : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of R R)).f (n + m) ≫
      capHom R (TopCat.toSSet.obj X) α.1 m = 0 := by
  apply SSet.chainComplex_hom_ext (C := ModuleCat R)
  intro τ
  rw [← Category.assoc]
  have hkey : (TopCat.toSSet.obj (TopCat.of A)).ιChainComplex τ ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of R R)).f (n + m) =
      (TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.map (subtypeIncl X A)).app _ τ) := by
    exact SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (TopCat.of A))
      (Y := TopCat.toSSet.obj X) (TopCat.toSSet.map (subtypeIncl X A)) (ModuleCat.of R R) τ
  rw [hkey, comp_zero]
  have hcap := ιChainComplex_capHom R (TopCat.toSSet.obj X) α.1
    ((TopCat.toSSet.map (subtypeIncl X A)).app _ τ)
  rw [hcap, genEval_frontFace_eq_zero R X A α.1 α.2 τ]
  simp

/-! ## The relative cap product -/

/-- **The relative cap product** at the chain level: the absolute cap product with a relative
cochain, factored through the quotient `C_{n+m}(X,A;R)` of the `(n+m)`-chains by those supported
in `A`. -/
noncomputable def relCapHalf (X : TopCat) (A : Set X) {n : ℕ}
    (α : relKern R X A n) (m : ℕ) :
    relChainsModule R X A (n + m) ⟶ singChains R X m :=
  cokernel.desc (f := (SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
      (ModuleCat.of R R)).f (n + m))
    (capHom R (TopCat.toSSet.obj X) α.1 m)
    (capMap_comp_chainComplexMap R X A α m)

/-- **The computation rule for the relative cap product**: composed with the quotient projection it
is the absolute cap product. -/
theorem cokernel_π_relCapHalf (X : TopCat) (A : Set X) {n : ℕ}
    (α : relKern R X A n) (m : ℕ) :
    cokernel.π ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of R R)).f (n + m)) ≫ relCapHalf R X A α m
      = capHom R (TopCat.toSSet.obj X) α.1 m :=
  cokernel.π_desc (f := (SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
      (ModuleCat.of R R)).f (n + m))
    (capHom R (TopCat.toSSet.obj X) α.1 m)
    (capMap_comp_chainComplexMap R X A α m)

/-- The relative cap product on a representing chain: it is the absolute cap product. -/
theorem relCapHalf_apply (X : TopCat) (A : Set X) {n m : ℕ} (α : relKern R X A n)
    (c : ↑(((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X (n + m))) :
    (relCapHalf R X A α m).hom
      (cokernel.π ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of R R)).f (n + m)) c)
      = cap R (TopCat.toSSet.obj X) α.1 m c := by
  have h : (cokernel.π ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of R R)).f (n + m)) ≫ relCapHalf R X A α m).hom c
      = (capHom R (TopCat.toSSet.obj X) α.1 m).hom c := by
    rw [cokernel_π_relCapHalf]
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, cap] using h

/-! ## The relative cap/cup identity -/

/-- **The relative cap/cup identity.**  For relative cochains `α ∈ C^n(X,A;R)`,
`β ∈ C^m(X,A;R)` and an `(n+m)`-chain `c` of `X`:

  `β(c ⌢ α) = (α ⌣ β)(c)`,

the relative form of `kronecker_cap_cup`.  Since `α` and `β` are relative cochains, this identity is
compatible with the quotient `C_*(X,A;R)`, so it descends to the pairing
`H^n(X,A;R) × H_{n+m}(X,A;R) → R`. -/
theorem relKronecker_cap_cup (X : TopCat) (A : Set X) {n m : ℕ}
    (α : relKern R X A n) (β : relKern R X A m)
    (c : ↑(((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X (n + m))) :
    kronecker R (TopCat.toSSet.obj X) (β.1 : Cochain R (TopCat.toSSet.obj X) m)
        (cap R (TopCat.toSSet.obj X) (α.1 : Cochain R (TopCat.toSSet.obj X) n) m c)
      = kronecker R (TopCat.toSSet.obj X)
        ((relCup R X A n m α β).1 : Cochain R (TopCat.toSSet.obj X) (n + m)) c := by
  have h := kronecker_cap_cup R (TopCat.toSSet.obj X) (m := n) (n := m)
    (α.1 : Cochain R (TopCat.toSSet.obj X) n) (β.1 : Cochain R (TopCat.toSSet.obj X) m) c
  simpa only [kronecker, relCup_coe] using h

end

end Work.Cohomology
