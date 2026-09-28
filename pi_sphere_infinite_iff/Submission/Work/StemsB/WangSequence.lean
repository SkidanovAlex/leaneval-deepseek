import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.RelCup

/-!
# The Wang sequence of a fibration over a sphere

For a fibration `p : E → S^m` with fibre `F`, the **Wang sequence** is the long exact sequence

  `⋯ ⟶ H^(n-m)(F) ⟶ H^n(E) ⟶ H^n(F) --θ--> H^(n-m+1)(F) ⟶ H^(n+1)(E) ⟶ ⋯`

It is the long exact sequence of the pair `(E, E|_D)` for one of the two discs `D` whose union is
`S^m`, read through the two identifications

* `H^n(E|_D) ≅ H^n(F)` (the fibration is trivial over the contractible disc `D`), and
* `H^n(E, E|_D) ≅ H^(n-m)(F)` (excision and the pair `(D^m, ∂D^m)`),

and `θ` is the connecting homomorphism of the pair, transported by these identifications.

This file delivers the *abstract* form of that statement: given a pair `(X,A)` and two families of
isomorphisms `γ : H^n(A) ≅ H^n(F)` and `τ : H^n(X,A) ≅ H^(n-m)(F)`, the transported sequence is
exact.  The geometric content — the construction of `γ` from the fibrewise triviality over the disc
(`Work.StemsB.cohomologyIso_fibTriv`) and of `τ` from excision and the disc pair — is supplied by
the caller; see `Work.StemsB.wangSequence_sphere`.

Since the `τ`-isomorphisms live in degrees `n - m` which may be negative, all the graded groups are
indexed by `ℤ` and extended by `0` in negative degrees (`Work.StemsB.cohZ`, `Work.StemsB.relCohZ`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

/-! ## Two elementary facts about isomorphisms of `ℤ`-modules -/

/-- The inverse of an isomorphism of `ℤ`-modules is a right inverse on points. -/
theorem iso_hom_inv_apply {M N : ModuleCat ℤ} (e : M ≅ N) (y : N) : e.hom (e.inv y) = y := by
  have hh : (e.inv ≫ e.hom) y = (𝟙 N) y := by rw [Iso.inv_hom_id]
  simpa using hh

/-- The inverse of an isomorphism of `ℤ`-modules is a left inverse on points. -/
theorem iso_inv_hom_apply {M N : ModuleCat ℤ} (e : M ≅ N) (x : M) : e.inv (e.hom x) = x := by
  have hh : (e.hom ≫ e.inv) x = (𝟙 M) x := by rw [Iso.hom_inv_id]
  simpa using hh

/-- An isomorphism of `ℤ`-modules is injective. -/
theorem iso_hom_injective {M N : ModuleCat ℤ} (e : M ≅ N) : Function.Injective e.hom := by
  intro a b hab
  rw [← iso_inv_hom_apply e a, ← iso_inv_hom_apply e b, hab]

/-- The range of an isomorphism of `ℤ`-modules is everything. -/
theorem iso_hom_surjective {M N : ModuleCat ℤ} (e : M ≅ N) : Function.Surjective e.hom :=
  fun y => ⟨e.inv y, iso_hom_inv_apply e y⟩

/-- `e.hom a = y` iff `a = e.inv y`. -/
theorem iso_hom_eq_iff {M N : ModuleCat ℤ} (e : M ≅ N) (a : M) (y : N) :
    e.hom a = y ↔ a = e.inv y := by
  constructor
  · intro h
    rw [← h, iso_inv_hom_apply]
  · intro h
    rw [h, iso_hom_inv_apply]

/-! ## Transport of exactness along isomorphisms -/

/-- **Exactness is transported along isomorphisms of `ℤ`-modules.**  If `f` and `g` are composable
with exact image/kernel and `eM`, `eN`, `eP` are isomorphisms, then the conjugated pair is exact as
well. -/
theorem functionExact_conj {M N P M' N' P' : ModuleCat ℤ} (f : M ⟶ N) (g : N ⟶ P)
    (eM : M ≅ M') (eN : N ≅ N') (eP : P ≅ P') (h : Function.Exact f g) :
    Function.Exact (eM.inv ≫ f ≫ eN.hom) (eN.inv ≫ g ≫ eP.hom) := by
  intro y
  rw [show (eN.inv ≫ g ≫ eP.hom) y = eP.hom (g (eN.inv y)) from rfl]
  have hz : eP.hom (g (eN.inv y)) = 0 ↔ g (eN.inv y) = 0 :=
    ⟨fun h0 => iso_hom_injective eP (by rw [h0, map_zero]),
      fun h0 => by rw [h0, map_zero]⟩
  rw [hz, h (eN.inv y), Set.mem_range, Set.mem_range]
  constructor
  · rintro ⟨z, hz'⟩
    exact ⟨eM.hom z, by
      rw [show (eM.inv ≫ f ≫ eN.hom) (eM.hom z)
            = eN.hom (f (eM.inv (eM.hom z))) from rfl,
        iso_inv_hom_apply, hz', iso_hom_inv_apply]⟩
  · rintro ⟨x, hx⟩
    refine ⟨eM.inv x, ?_⟩
    have hx' : eN.hom (f (eM.inv x)) = y := hx
    rw [← hx', iso_inv_hom_apply]

/-! ## The graded groups -/

/-- The zero `ℤ`-module, used to extend graded modules by `0` in negative degrees. -/
def zeroModZ : ModuleCat ℤ := ModuleCat.of ℤ (Fin 0 → ℤ)

/-- Singular cohomology, indexed by `ℤ` and extended by `0` in negative degrees. -/
noncomputable def cohZ (X : TopCat) : ℤ → ModuleCat ℤ
  | ((n : ℕ) : ℤ) => Work.Cohomology.singularCohomology ℤ n X
  | _ => zeroModZ

/-- Relative singular cohomology, indexed by `ℤ` and extended by `0` in negative degrees. -/
noncomputable def relCohZ (X : TopCat) (A : Set X) : ℤ → ModuleCat ℤ
  | ((n : ℕ) : ℤ) => Work.Cohomology.relCohomology ℤ X A n
  | _ => zeroModZ

@[simp] theorem cohZ_nat (X : TopCat) (n : ℕ) :
    cohZ X (n : ℤ) = Work.Cohomology.singularCohomology ℤ n X := rfl

@[simp] theorem relCohZ_nat (X : TopCat) (A : Set X) (n : ℕ) :
    relCohZ X A (n : ℤ) = Work.Cohomology.relCohomology ℤ X A n := rfl

/-! ## The Wang sequence -/

/-- The map `H^q(X) ⟶ H^q(F)` of the Wang sequence: the restriction to the subspace `A` followed by
the identification `γ` of `A` with the fibre. -/
def wangα (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ q : ℕ, Work.Cohomology.singularCohomology ℤ q (TopCat.of A) ≅ cohZ Fsp q) (q : ℕ) :
    cohZ X (q : ℤ) ⟶ cohZ Fsp (q : ℤ) :=
  HomologicalComplex.homologyMap (Work.Cohomology.restr ℤ X A) q ≫ (γ q).hom

/-- The map `θ : H^q(F) ⟶ H^(q+1-m)(F)` of the Wang sequence: the connecting homomorphism of the
pair `(X,A)`, transported by `γ` and `τ`. -/
def wangθ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ q : ℕ, Work.Cohomology.singularCohomology ℤ q (TopCat.of A) ≅ cohZ Fsp q)
    (τ : ∀ k : ℕ, Work.Cohomology.relCohomology ℤ X A k ≅ cohZ Fsp ((k : ℤ) - (m : ℤ)))
    (q : ℕ) : cohZ Fsp (q : ℤ) ⟶ cohZ Fsp (((q + 1 : ℕ) : ℤ) - (m : ℤ)) :=
  (γ q).inv ≫ Work.Cohomology.pairδ ℤ X A q ≫ (τ (q + 1)).hom

/-- The map `H^(q+1-m)(F) ⟶ H^(q+1)(X)` of the Wang sequence. -/
def wangβ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (τ : ∀ k : ℕ, Work.Cohomology.relCohomology ℤ X A k ≅ cohZ Fsp ((k : ℤ) - (m : ℤ)))
    (q : ℕ) : cohZ Fsp (((q + 1 : ℕ) : ℤ) - (m : ℤ)) ⟶ cohZ X (((q + 1 : ℕ) : ℤ)) :=
  (τ (q + 1)).inv ≫ HomologicalComplex.homologyMap (Work.Cohomology.relIncl ℤ X A) (q + 1)

/-- **Exactness of the Wang sequence at `H^q(F)`**: the composite of the restriction to the fibre
with `θ` is exact. -/
theorem wangExact₁ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ q : ℕ, Work.Cohomology.singularCohomology ℤ q (TopCat.of A) ≅ cohZ Fsp q)
    (τ : ∀ k : ℕ, Work.Cohomology.relCohomology ℤ X A k ≅ cohZ Fsp ((k : ℤ) - (m : ℤ)))
    (q : ℕ) : Function.Exact (wangα X A Fsp m γ q) (wangθ X A Fsp m γ τ q) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.pair_exact₃ ℤ X A q)
  exact functionExact_conj _ _ (Iso.refl (cohZ X (q : ℤ))) (γ q) (τ (q + 1)) h

/-- **Exactness of the Wang sequence at `H^(q+1-m)(F)`**: `θ` followed by the map to `H^(q+1)(X)`
is exact. -/
theorem wangExact₂ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ q : ℕ, Work.Cohomology.singularCohomology ℤ q (TopCat.of A) ≅ cohZ Fsp q)
    (τ : ∀ k : ℕ, Work.Cohomology.relCohomology ℤ X A k ≅ cohZ Fsp ((k : ℤ) - (m : ℤ)))
    (q : ℕ) : Function.Exact (wangθ X A Fsp m γ τ q) (wangβ X A Fsp m τ q) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.pair_exact₁ ℤ X A q)
  exact functionExact_conj _ _ (γ q) (τ (q + 1)) (Iso.refl (cohZ X (((q + 1 : ℕ) : ℤ)))) h

/-- **Exactness of the Wang sequence at `H^(q+1)(X)`**. -/
theorem wangExact₃ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ q : ℕ, Work.Cohomology.singularCohomology ℤ q (TopCat.of A) ≅ cohZ Fsp q)
    (τ : ∀ k : ℕ, Work.Cohomology.relCohomology ℤ X A k ≅ cohZ Fsp ((k : ℤ) - (m : ℤ)))
    (q : ℕ) : Function.Exact (wangβ X A Fsp m τ q) (wangα X A Fsp m γ (q + 1)) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.pair_exact₂ ℤ X A (q + 1))
  exact functionExact_conj _ _ (τ (q + 1)) (Iso.refl (cohZ X (((q + 1 : ℕ) : ℤ)))) (γ (q + 1)) h

end

end Work.StemsB
