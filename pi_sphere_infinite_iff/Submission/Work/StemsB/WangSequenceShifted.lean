import Submission.Work.StemsB.WangSequence

/-!
# The Wang sequence in cohomology, in the degree-shifted form

The abstract Wang sequence of `WangSequence.lean` is indexed by `ℤ` (through `cohZ`) because the
identification `τ : H^k(X,A) ≅ H^{k-m}(F)` shifts the degree.  This file records the equivalent
statement with **no negative degrees**: `τ` is given in the shifted form

  `τ n : H^{n+m}(X,A) ≅ H^n(F)`,

and the exactness spots of the Wang sequence are, for every `n : ℕ`,

  `H^n(F) --β_n--> H^{n+m}(X) --α_(n+m)--> H^{n+m}(F) --θ_n--> H^{n+1}(F) --β_n^S--> H^{n+m+1}(X)`.

All the degrees that occur are `n`, `n+1`, `n+m`, `n+m+1` — non-negative — so no extension by `0`
in negative degrees is needed, and the sphere case (`WangCohSphereShifted.lean`) becomes
unconditional.
-/

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

/-- The map `H^k(X) ⟶ H^k(Fsp)` of the shifted Wang sequence. -/
def wangCohShiftα (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology ℤ k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology ℤ k Fsp) (k : ℕ) :
    Work.Cohomology.singularCohomology ℤ k X ⟶ Work.Cohomology.singularCohomology ℤ k Fsp :=
  HomologicalComplex.homologyMap (Work.Cohomology.restr ℤ X A) k ≫ (γ k).hom

/-- The map `H^n(Fsp) ⟶ H^{n+m}(X)` of the shifted Wang sequence. -/
def wangCohShiftβ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (τ : ∀ n : ℕ, (Work.Cohomology.relComplex ℤ X A).homology (n + m) ≅
      Work.Cohomology.singularCohomology ℤ n Fsp) (n : ℕ) :
    Work.Cohomology.singularCohomology ℤ n Fsp ⟶
      Work.Cohomology.singularCohomology ℤ (n + m) X :=
  (τ n).inv ≫ HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) (n + m)

/-- The map `H^{n+m}(Fsp) ⟶ H^{n+1}(Fsp)` of the shifted Wang sequence. -/
def wangCohShiftθ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology ℤ k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology ℤ k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex ℤ X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology ℤ (n + 1) Fsp) (n : ℕ) :
    Work.Cohomology.singularCohomology ℤ (n + m) Fsp ⟶
      Work.Cohomology.singularCohomology ℤ (n + 1) Fsp :=
  (γ (n + m)).inv ≫ Work.Cohomology.pairδ ℤ X A (n + m) ≫ (τS n).hom

/-- The map `H^{n+1}(Fsp) ⟶ H^{n+m+1}(X)` of the shifted Wang sequence. -/
def wangCohShiftβS (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex ℤ X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology ℤ (n + 1) Fsp) (n : ℕ) :
    Work.Cohomology.singularCohomology ℤ (n + 1) Fsp ⟶
      Work.Cohomology.singularCohomology ℤ (n + m + 1) X :=
  (τS n).inv ≫ HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) (n + m + 1)

/-- **Exactness of the shifted Wang sequence at `H^{n+m}(X)`.** -/
theorem wangCohShiftExact₁ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology ℤ k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology ℤ k Fsp)
    (τ : ∀ n : ℕ, (Work.Cohomology.relComplex ℤ X A).homology (n + m) ≅
      Work.Cohomology.singularCohomology ℤ n Fsp) (n : ℕ) :
    Function.Exact (wangCohShiftβ X A Fsp m τ n) (wangCohShiftα X A Fsp m γ (n + m)) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.pair_exact₂ ℤ X A (n + m))
  exact functionExact_conj _ _ (τ n) (Iso.refl _) (γ (n + m)) h

/-- **Exactness of the shifted Wang sequence at `H^{n+m}(Fsp)`.** -/
theorem wangCohShiftExact₂ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology ℤ k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology ℤ k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex ℤ X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology ℤ (n + 1) Fsp) (n : ℕ) :
    Function.Exact (wangCohShiftα X A Fsp m γ (n + m)) (wangCohShiftθ X A Fsp m γ τS n) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.pair_exact₃ ℤ X A (n + m))
  exact functionExact_conj _ _ (Iso.refl _) (γ (n + m)) (τS n) h

/-- **Exactness of the shifted Wang sequence at `H^{n+m+1}(X,A)`.** -/
theorem wangCohShiftExact₃ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology ℤ k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology ℤ k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex ℤ X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology ℤ (n + 1) Fsp) (n : ℕ) :
    Function.Exact (wangCohShiftθ X A Fsp m γ τS n) (wangCohShiftβS X A Fsp m τS n) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.pair_exact₁ ℤ X A (n + m))
  exact functionExact_conj _ _ (γ (n + m)) (τS n) (Iso.refl _) h

end

end Work.StemsB
