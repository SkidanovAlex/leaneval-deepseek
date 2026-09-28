import Mathlib
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.homotopyEquiv

/-!
# The shifted Wang sequence over an arbitrary coefficient ring

`Submission/Work/StemsB/WangSequenceShifted.lean` proves the exactness of the degree-shifted Wang
sequence of a pair `(X,A)` — the abstract form of `E4` of
`Submission/Work/Drive/SERRE_BLUEPRINT.md` — for coefficient ring `ℤ`, by reducing it to the
connecting maps of the pair sequence `Work.Cohomology.pair_exact₁/₂/₃ ℤ` (exactness of the
long exact sequence of a pair in cohomology).

*Every* ingredient of that argument is already stated for an arbitrary `CommRing R`
(`Work.Cohomology.relComplex R`, `restr R`, `relIncl R`, `pairδ R`, `pair_exact₁/₂/₃ R`,
`singularCohomology R`), and the two algebraic transports used (`functionExact_conj`,
`iso_hom_injective`) are coefficient-free.  This file therefore records the same statements with the
coefficient ring as an explicit parameter, so that the **ℚ-coefficient** form needed by subproject
SERRE (`Work.Serre.ratCoh`, see `Submission/Work/StemsB/QCOEFF_PLAN.md`) is available by
`R := ℚ`, and the *only* inputs it needs are the two identifications `γ` and `τS`.

Nothing here is geometric: the spherical identifications `γ` (from the fibrewise triviality over the
outer piece) and `τS` (from excision, the triviality over the inner cube, the collar isomorphism and
the clutching map) are inputs, exactly as in the ℤ version.
-/

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

/-! ## Two coefficient-free transports of exactness -/

/-- The inverse of an isomorphism of `R`-modules is a right inverse on points. -/
theorem iso_hom_inv_apply_R (R : Type) [CommRing R] {M N : ModuleCat R} (e : M ≅ N) (y : N) :
    e.hom (e.inv y) = y := by
  have hh : (e.inv ≫ e.hom) y = (𝟙 N) y := by rw [Iso.inv_hom_id]
  simpa using hh

/-- The inverse of an isomorphism of `R`-modules is a left inverse on points. -/
theorem iso_inv_hom_apply_R (R : Type) [CommRing R] {M N : ModuleCat R} (e : M ≅ N) (x : M) :
    e.inv (e.hom x) = x := by
  have hh : (e.hom ≫ e.inv) x = (𝟙 M) x := by rw [Iso.hom_inv_id]
  simpa using hh

/-- An isomorphism of `R`-modules is injective. -/
theorem iso_hom_injective_R (R : Type) [CommRing R] {M N : ModuleCat R} (e : M ≅ N) :
    Function.Injective e.hom := by
  intro a b hab
  rw [← iso_inv_hom_apply_R R e a, ← iso_inv_hom_apply_R R e b, hab]

/-- **Exactness is transported along isomorphisms** — the coefficient-generic form of
`Work.StemsB.functionExact_conj` (whose proof is coefficient-free). -/
theorem functionExact_conj_R (R : Type) [CommRing R] {M N P M' N' P' : ModuleCat R}
    (f : M ⟶ N) (g : N ⟶ P) (eM : M ≅ M') (eN : N ≅ N') (eP : P ≅ P')
    (h : Function.Exact f g) :
    Function.Exact (eM.inv ≫ f ≫ eN.hom) (eN.inv ≫ g ≫ eP.hom) := by
  intro y
  rw [show (eN.inv ≫ g ≫ eP.hom) y = eP.hom (g (eN.inv y)) from rfl]
  have hz : eP.hom (g (eN.inv y)) = 0 ↔ g (eN.inv y) = 0 :=
    ⟨fun h0 => iso_hom_injective_R R eP (by rw [h0, map_zero]),
      fun h0 => by rw [h0, map_zero]⟩
  rw [hz, h (eN.inv y), Set.mem_range, Set.mem_range]
  constructor
  · rintro ⟨z, hz'⟩
    exact ⟨eM.hom z, by
      rw [show (eM.inv ≫ f ≫ eN.hom) (eM.hom z)
            = eN.hom (f (eM.inv (eM.hom z))) from rfl,
        iso_inv_hom_apply_R R eM, hz', iso_hom_inv_apply_R R eN]⟩
  · rintro ⟨x, hx⟩
    refine ⟨eM.inv x, ?_⟩
    have hx' : eN.hom (f (eM.inv x)) = y := hx
    rw [← hx', iso_inv_hom_apply_R R eN]

/-! ## The shifted Wang sequence -/

variable (R : Type) [CommRing R]

/-- The map `H^k(X) ⟶ H^k(Fsp)` of the shifted Wang sequence. -/
def wangCohShiftαR (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp) (k : ℕ) :
    Work.Cohomology.singularCohomology R k X ⟶ Work.Cohomology.singularCohomology R k Fsp :=
  HomologicalComplex.homologyMap (Work.Cohomology.restr R X A) k ≫ (γ k).hom

/-- The map `H^n(Fsp) ⟶ H^{n+m}(X)` of the shifted Wang sequence. -/
def wangCohShiftβR (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (τ : ∀ n : ℕ, (Work.Cohomology.relComplex R X A).homology (n + m) ≅
      Work.Cohomology.singularCohomology R n Fsp) (n : ℕ) :
    Work.Cohomology.singularCohomology R n Fsp ⟶
      Work.Cohomology.singularCohomology R (n + m) X :=
  (τ n).inv ≫ HomologicalComplex.homologyMap (Work.Cohomology.relIncl R X A) (n + m)

/-- **The Wang transgression** `θ_n : H^{n+m}(Fsp) ⟶ H^{n+1}(Fsp)`: the connecting map of the pair
`(X,A)` transported by the two identifications `γ` and `τS`.  This is the map whose derivation
property is E4 of the blueprint. -/
def wangCohShiftθR (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex R X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology R (n + 1) Fsp) (n : ℕ) :
    Work.Cohomology.singularCohomology R (n + m) Fsp ⟶
      Work.Cohomology.singularCohomology R (n + 1) Fsp :=
  (γ (n + m)).inv ≫ Work.Cohomology.pairδ R X A (n + m) ≫ (τS n).hom

/-- The map `H^{n+1}(Fsp) ⟶ H^{n+m+1}(X)` of the shifted Wang sequence. -/
def wangCohShiftβSR (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex R X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology R (n + 1) Fsp) (n : ℕ) :
    Work.Cohomology.singularCohomology R (n + 1) Fsp ⟶
      Work.Cohomology.singularCohomology R (n + m + 1) X :=
  (τS n).inv ≫ HomologicalComplex.homologyMap (Work.Cohomology.relIncl R X A) (n + m + 1)

/-- **Exactness of the shifted Wang sequence at `H^{n+m}(X)`.** -/
theorem wangCohShiftExact₁R (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τ : ∀ n : ℕ, (Work.Cohomology.relComplex R X A).homology (n + m) ≅
      Work.Cohomology.singularCohomology R n Fsp) (n : ℕ) :
    Function.Exact (wangCohShiftβR R X A Fsp m τ n)
      (wangCohShiftαR R X A Fsp m γ (n + m)) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.pair_exact₂ R X A (n + m))
  exact functionExact_conj_R R _ _ (τ n) (Iso.refl _) (γ (n + m)) h

/-- **Exactness of the shifted Wang sequence at `H^{n+m}(Fsp)`.** -/
theorem wangCohShiftExact₂R (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex R X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology R (n + 1) Fsp) (n : ℕ) :
    Function.Exact (wangCohShiftαR R X A Fsp m γ (n + m))
      (wangCohShiftθR R X A Fsp m γ τS n) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.pair_exact₃ R X A (n + m))
  exact functionExact_conj_R R _ _ (Iso.refl _) (γ (n + m)) (τS n) h

/-- **Exactness of the shifted Wang sequence at `H^{n+m+1}(X,A)`.** -/
theorem wangCohShiftExact₃R (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ k : ℕ, Work.Cohomology.singularCohomology R k (TopCat.of A) ≅
      Work.Cohomology.singularCohomology R k Fsp)
    (τS : ∀ n : ℕ, (Work.Cohomology.relComplex R X A).homology (n + m + 1) ≅
      Work.Cohomology.singularCohomology R (n + 1) Fsp) (n : ℕ) :
    Function.Exact (wangCohShiftθR R X A Fsp m γ τS n)
      (wangCohShiftβSR R X A Fsp m τS n) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.pair_exact₁ R X A (n + m))
  exact functionExact_conj_R R _ _ (γ (n + m)) (τS n) (Iso.refl _) h

end

end Work.StemsB
