import Mathlib
import Submission.Work.Serre.ezShuffleRat

/-!
# The Kronecker rule for the cross product on the shuffle chain, over an arbitrary ring

This file proves the coefficient-generic (`R : CommRing`) form of the chain-level Kronecker rule

  `⟨α × β, shuffle(u,v)⟩ = α(u) · β(v)`

for the cross product `Work.Serre.crossCochainR` of two cochains and the Eilenberg–Zilber shuffle
chain `Work.Serre.ezBilR` of two chains, under the hypothesis that `β` annihilates the degenerate
`q`-simplices of `Y` (the usual normalization).  Over `ℤ` this is
`Work.Kunneth.crossCochain_ezChain` (`Submission/Work/Kunneth/CrossShuffle.lean`); the proof here
follows the same plan (a single exceptional shuffle survives the normalized cochain), with the
chain-level statement deduced from the generator-level one by bilinearity of `ezBilR`.

## Main results

* `genEvalDescApplyR` — the computation rule for a morphism out of the coproduct of copies of `R`;
* `crossCochainR_apply` — the value of the cross product on a generating simplex;
* `crossCochainR_ezCellGen` — its value on a single shuffle cell;
* `crossCochainR_ezGenR` — its value on the shuffle chain of a pair of generators;
* `crossCochainR_ezBilR` — **the chain-level Kronecker rule**.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Serre

noncomputable section

open Work.Cohomology
open Work.Cohomology.Crux33

variable (R : Type) [CommRing R]

/-- The computation rule for a morphism out of the coproduct of copies of `R` which is the singular
`n`-chains of a simplicial set, built with `IsColimit.desc`. -/
lemma genEvalDescApplyR (X : SSet) (n : ℕ)
    (g : (z : X _⦋n⦌) → ModuleCat.of R R ⟶ ModuleCat.of R R) (z : X _⦋n⦌) :
    (Cofan.IsColimit.desc (X.isColimitChainComplexXCofan (ModuleCat.of R R) n) g).hom
        ((X.ιChainComplex (R := ModuleCat.of R R) z).hom 1)
      = (g z).hom 1 := by
  have h := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of R R) n) g z
  have h2 := congrArg (fun (m : ModuleCat.of R R ⟶ ModuleCat.of R R) => m.hom (1 : R)) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  exact h2

/-- The value of the cross product cochain on a generating simplex. -/
theorem crossCochainR_apply (X Y : SSet) (p q : ℕ)
    (α : Cochain R X p) (β : Cochain R Y q) (z : (X ⊗ Y) _⦋p + q⦌) :
    genEval R (X ⊗ Y) (crossCochainR R X Y p q α β) z
      = genEval R X α (frontFace X p (p + q) (Nat.le_add_right p q) z.1) *
        genEval R Y β (backFace Y p q z.2) := by
  have h := genEvalDescApplyR R (X ⊗ Y) (p + q) (crossCochainRFam R X Y p q α β) z
  have h2 : (crossCochainRFam R X Y p q α β z).hom 1
      = α ((X.ιChainComplex (R := ModuleCat.of R R) (frontFace X p (p + q)
            (Nat.le_add_right p q) z.1)).hom 1)
        * β ((Y.ιChainComplex (R := ModuleCat.of R R) (backFace Y p q z.2)).hom 1) := by
    simp only [crossCochainRFam, Work.Kunneth.backFaceLE_eq_backFace, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, one_smul, genEval]
  simp only [crossCochainR, genEval]
  exact h.trans h2

/-- The value of the cross product on a single shuffle cell. -/
theorem crossCochainR_ezCellGen (X Y : SSet) (p q : ℕ)
    (α : Cochain R X p) (β : Cochain R Y q)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) (S : PShuffle p q) :
    genEval R (X ⊗ Y) (crossCochainR R X Y p q α β) (ezCellGenR p q X Y σ τ S)
      = genEval R X α (X.map ((frontIncl p (p + q) (Nat.le_add_right p q)) ≫
            (aHom S.1 S.2)).op σ)
        * genEval R Y β (Y.map ((backIncl p q) ≫ (bHom S.1 S.2)).op τ) := by
  rw [crossCochainR_apply]
  simp only [ezCellGenR, frontFace, backFace]
  rw [Work.Cohomology.map_op_comp (aHom S.1 S.2)
        (frontIncl p (p + q) (Nat.le_add_right p q)) σ,
      Work.Cohomology.map_op_comp (bHom S.1 S.2) (backIncl p q) τ]

/-- A cochain is `ℤ`-homogeneous. -/
lemma cochainR_zsmul_chain (X : SSet) {k : ℕ} (γ : Cochain R X k) (r : ℤ)
    (c : (X.chainComplex (ModuleCat.of R R)).X k) : γ (r • c) = r • γ c := by
  rw [← Int.cast_smul_eq_zsmul (R := R) r c, ← Int.cast_smul_eq_zsmul (R := R) r (γ c)]
  exact LinearMap.map_smul γ (r : R) c

/-- **The cross product on the shuffle chain of a pair of generators.**  If `β` annihilates the
degenerate `q`-simplices of `Y`, then of all the shuffle cells only the exceptional one survives,
and it has sign `+1`. -/
theorem crossCochainR_ezGenR (X Y : SSet) (p q : ℕ)
    (α : Cochain R X p) (β : Cochain R Y q)
    (hβ : ∀ x ∈ Y.degenerate q, genEval R Y β x = 0)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    crossCochainR R X Y p q α β (ezGenR R p q X Y σ τ)
      = genEval R X α σ * genEval R Y β τ := by
  have key : ∀ S : PShuffle p q,
      (crossCochainR R X Y p q α β)
        (shufSign S.1 • (((X ⊗ Y).ιChainComplex (R := ModuleCat.of R R)
          (ezCellGenR p q X Y σ τ S)).hom 1))
      = shufSign S.1 •
          (genEval R X α (X.map ((frontIncl p (p + q) (Nat.le_add_right p q)) ≫
              (aHom S.1 S.2)).op σ)
            * genEval R Y β (Y.map ((backIncl p q) ≫ (bHom S.1 S.2)).op τ)) := by
    intro S
    rw [cochainR_zsmul_chain]
    congr 1
    exact crossCochainR_ezCellGen R X Y p q α β σ τ S
  rw [ezGenR, map_sum]
  rw [Finset.sum_congr rfl (fun S _ => key S)]
  rw [Finset.sum_eq_single (Work.Kunneth.goodShuf p q)]
  · have h1 : X.map ((frontIncl p (p + q) (Nat.le_add_right p q)) ≫
        (aHom (Work.Kunneth.goodShuf p q).1 (Work.Kunneth.goodShuf p q).2)).op σ = σ := by
      have h := congrArg (fun (g : ⦋p⦌ ⟶ ⦋p⦌) => X.map g.op σ)
        (Work.Kunneth.frontIncl_comp_aHom_goodShuf p q)
      simpa using h
    have h2 : Y.map ((backIncl p q) ≫
        (bHom (Work.Kunneth.goodShuf p q).1 (Work.Kunneth.goodShuf p q).2)).op τ = τ := by
      have h := congrArg (fun (g : ⦋q⦌ ⟶ ⦋q⦌) => Y.map g.op τ)
        (Work.Kunneth.backIncl_comp_bHom_goodShuf p q)
      simpa using h
    rw [h1, h2, Work.Kunneth.shufSign_goodShuf, one_smul]
  · intro S _ hS
    have hns := Work.Kunneth.not_surjective_backIncl_bHom_goodShufF p q S hS
    have hdeg : Y.map ((backIncl p q) ≫ (bHom S.1 S.2)).op τ ∈ Y.degenerate q :=
      Work.Kunneth.mem_degenerate_of_not_surjective_self' _ hns τ
    rw [hβ _ hdeg, mul_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The Kronecker rule for the cross product on the Eilenberg–Zilber shuffle chain**, over an
arbitrary commutative ring `R`. -/
theorem crossCochainR_ezBilR (X Y : SSet) (p q : ℕ)
    (α : Cochain R X p) (β : Cochain R Y q)
    (hβ : ∀ x ∈ Y.degenerate q, genEval R Y β x = 0) (u : (X.chainComplex (ModuleCat.of R R)).X p)
    (v : (Y.chainComplex (ModuleCat.of R R)).X q) :
    crossCochainR R X Y p q α β ((ezBilR R p q X Y).hom u v) = α u * β v := by
  have hσ : ∀ σ : X _⦋p⦌,
      (crossCochainR R X Y p q α β).comp ((ezBilR R p q X Y).hom
          ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1))
        = (α ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)) • β := by
    intro σ
    apply genEval_ext (X := Y) (R := R) (k := q)
    intro τ
    have h1 : genEval R Y ((crossCochainR R X Y p q α β).comp ((ezBilR R p q X Y).hom
        ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1))) τ
        = crossCochainR R X Y p q α β (ezGenR R p q X Y σ τ) := by
      rw [genEval, LinearMap.comp_apply, ezBilR_gen]
    have h2 : genEval R Y ((α ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)) • β) τ
        = genEval R X α σ * genEval R Y β τ := by
      simp only [genEval, LinearMap.smul_apply, smul_eq_mul]
    rw [h1, h2]
    exact crossCochainR_ezGenR R X Y p q α β hβ σ τ
  have hv : ∀ v : (Y.chainComplex (ModuleCat.of R R)).X q,
      (crossCochainR R X Y p q α β).comp
          ((LinearMap.applyₗ v).comp (ezBilR R p q X Y).hom)
        = (β v) • α := by
    intro v
    apply genEval_ext (X := X) (R := R) (k := p)
    intro σ
    rw [genEval, genEval]
    have h := congrArg (fun (f : (Y.chainComplex (ModuleCat.of R R)).X q →ₗ[R] R) => f v)
      (hσ σ)
    have h1 : ((crossCochainR R X Y p q α β).comp
        ((LinearMap.applyₗ v).comp (ezBilR R p q X Y).hom))
        ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
        = crossCochainR R X Y p q α β ((ezBilR R p q X Y).hom
            ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) v) := by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply]
    have h2 : ((β v) • α) ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1)
        = α ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) * β v := by
      rw [LinearMap.smul_apply, smul_eq_mul, mul_comm]
    have h3 : crossCochainR R X Y p q α β ((ezBilR R p q X Y).hom
        ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) v)
        = α ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom 1) * β v := by
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] using h
    rw [h1, h3]
    exact h2.symm
  have h := congrArg (fun (f : (X.chainComplex (ModuleCat.of R R)).X p →ₗ[R] R) => f u) (hv v)
  have h' : crossCochainR R X Y p q α β ((ezBilR R p q X Y).hom u v) = β v * α u := by
    simpa only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, LinearMap.smul_apply,
      smul_eq_mul] using h
  rw [h', mul_comm]

end

end Work.Serre
