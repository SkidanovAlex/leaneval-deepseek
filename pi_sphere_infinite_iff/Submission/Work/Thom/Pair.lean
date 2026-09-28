import Mathlib
import Submission.Work.Thom.Basic
import Submission.Work.Thom.Cohomology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# The Thom pair of a real vector bundle, and the Euler class

For a real vector bundle `Z` over `B` (gluing data, `Submission/Work/Thom/Basic.lean`) this module
fixes the two models of the pair whose relative cohomology carries the Thom class:

* `Work.Thom.DiscThom Z n` — the cohomology `H^n(D(E), S(E);ℤ)` of the **disc pair** (the closed
  disc bundle together with its boundary, the sphere bundle);
* `Work.Thom.OpenThom Z n` — the cohomology `H^n(E, E∖0;ℤ)` of the total space with the zero
  section removed.  These two are canonically isomorphic (`H^n(D E,S E) ≅ H^n(E,E∖0)` by the
  deformation retraction `E → D(E)` towards the zero section and excision), and the Euler class is
  computed from either.

The **Euler class** `Work.Thom.eulerClass Z n τ ∈ H^n(B;ℤ)` of a rank-`n` bundle equipped with a
class `τ` of the relative cohomology is the pullback of `τ` along the zero section:

  `e(E) = z^*(τ)`,

i.e. the *definition* `Work.Thom.eulerClass`.  When `τ` is the **Thom class** of `Z` (a class whose
product with `π^*` is the Thom isomorphism, `Submission/Work/Thom/ThomClass.lean`) this is the
Euler class in the classical sense.

The long exact sequence of the pair `(X,A)` is `Work.Cohomology.pair_exact₁/₂/₃`; this module
restates it in the chapter's notation as `Work.Thom.pairExact₁/₂/₃` so that the Gysin sequence
(`Submission/Work/Thom/Gysin.lean`) can be assembled from it.
-/

open Work.TangentClasses

namespace Work.Thom

open CategoryTheory

noncomputable section

variable {B : Type} [TopologicalSpace B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}

/-! ## The inclusion of a subspace, in the chapter's notation -/

/-- The inclusion `A ↪ X` of a subset, as a continuous map. -/
def subtypeMap {X : Type} [TopologicalSpace X] (A : Set X) : C(A, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The forgetful map out of the relative cohomology, composed with the restriction to the
subspace, is zero. -/
theorem relToAbs_comp_CohMap_subtype (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (A : Set X) (n : ℕ) : relToAbs R A n ≫ CohMap (subtypeMap A) R n = 0 := by
  have h : CohMap (subtypeMap A) R n
      = HomologicalComplex.homologyMap (Work.Cohomology.restr R (TopCat.of X) A) n := rfl
  rw [h, relToAbs_comp_restr R]

/-- The restriction map on cohomology induced by `A ⊆ X`, in the chapter's notation. -/
abbrev restrCoh {X : Type} [TopologicalSpace X] (A : Set X) (R : Type) [CommRing R] (n : ℕ) :
    Coh R n X ⟶ Coh R n A :=
  CohMap (subtypeMap A) R n

/-! ## The two Thom pairs -/

/-- `H^n(D(E),S(E);ℤ)`, the relative cohomology of a real bundle with its sphere bundle removed:
the home of the **Thom class** of an oriented bundle. -/
abbrev DiscThom (Z : RealBundle B F ι) (n : ℕ) : ModuleCat ℤ :=
  RelCoh ℤ n (DiscSub Z) (sphereInDisc Z)

/-- `H^n(E,E∖0;ℤ)`, the relative cohomology of a real bundle with its zero section removed: the
model of the Thom pair that does not use a Euclidean structure. -/
abbrev OpenThom (Z : RealBundle B F ι) (n : ℕ) : ModuleCat ℤ :=
  RelCoh ℤ n Z.TotalSpace (zeroComplement Z)

/-- The forgetful map `H^n(D(E),S(E);ℤ) → H^n(D(E);ℤ)`. -/
abbrev discToAbs (Z : RealBundle B F ι) (n : ℕ) : DiscThom Z n ⟶ Coh ℤ n (DiscSub Z) :=
  relToAbs ℤ (sphereInDisc Z) n

/-- The forgetful map `H^n(E,E∖0;ℤ) → H^n(E;ℤ)`. -/
abbrev openToAbs (Z : RealBundle B F ι) (n : ℕ) : OpenThom Z n ⟶ Coh ℤ n Z.TotalSpace :=
  relToAbs ℤ (zeroComplement Z) n

/-! ## The Euler class -/

/-- **The Euler class** `e(E) ∈ H^n(B;ℤ)` associated with a class `τ ∈ H^n(E,E∖0;ℤ)` of the Thom
pair: its pullback along the zero section, `e(E) = z^*(τ)`.  For the **Thom class** `τ = 𝔱(E)` this
is the Euler class of an oriented rank-`n` bundle; the definition does not depend on the choice of
Euclidean structure, since it uses the pair `(E,E∖0)`. -/
def eulerClass (Z : RealBundle B F ι) (n : ℕ) (τ : OpenThom Z n) : Coh ℤ n B :=
  (CohMap (zeroSection Z) ℤ n).hom ((openToAbs Z n).hom τ)

/-- **The Euler class computed on the disc pair** `(D(E),S(E))`: the pullback of a class
`τ ∈ H^n(D(E),S(E);ℤ)` along the zero section `B → D(E)`. -/
def eulerClassDisc (Z : RealBundle B F ι) (n : ℕ) (τ : DiscThom Z n) : Coh ℤ n (DiscSub Z) :=
  (discToAbs Z n).hom τ

/-- The Euler class of the disc pair, pushed forward along the zero section, is the Euler class:
`e = z^*τ`. -/
theorem eulerClassDisc_eq (Z : RealBundle B F ι) (n : ℕ) (τ : DiscThom Z n) :
    (CohMap (zeroSectionDisc Z) ℤ n).hom (eulerClassDisc Z n τ) =
      (CohMap (zeroSectionDisc Z) ℤ n).hom ((discToAbs Z n).hom τ) := rfl

/-! ## The long exact sequence of the pair, in the chapter's notation -/

/-- The connecting homomorphism `H^n(A;ℤ) → H^{n+1}(X,A;ℤ)` of the pair `(X,A)`. -/
abbrev pairδC {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    Coh ℤ n A ⟶ RelCoh ℤ (n + 1) X A :=
  Work.Cohomology.pairδ ℤ (TopCat.of X) A n

/-- The composite `H^n(A) → H^{n+1}(X,A) → H^{n+1}(X)` is zero. -/
theorem pairδC_comp_relToAbs {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    pairδC A n ≫ relToAbs ℤ A (n + 1) = 0 :=
  Work.Cohomology.pairδ_comp ℤ (TopCat.of X) A n

/-- The composite `H^n(X) → H^n(A) → H^{n+1}(X,A)` is zero. -/
theorem restrCoh_comp_pairδC {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    restrCoh A ℤ n ≫ pairδC A n = 0 :=
  Work.Cohomology.pair_comp_δ ℤ (TopCat.of X) A n

/-- **Exactness of the pair sequence at `H^{n+1}(X,A)`**:
`H^n(A) → H^{n+1}(X,A) → H^{n+1}(X)` is exact. -/
theorem pairExact₁ {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk (pairδC A n) (relToAbs ℤ A (n + 1)) (pairδC_comp_relToAbs A n)).Exact :=
  Work.Cohomology.pair_exact₁ ℤ (TopCat.of X) A n

/-- **Exactness of the pair sequence at `H^n(X)`**:
`H^n(X,A) → H^n(X) → H^n(A)` is exact. -/
theorem pairExact₂ {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relToAbs ℤ A n) (restrCoh A ℤ n)
      (relToAbs_comp_CohMap_subtype ℤ A n)).Exact :=
  Work.Cohomology.pair_exact₂ ℤ (TopCat.of X) A n

/-- **Exactness of the pair sequence at `H^n(A)`**:
`H^n(X) → H^n(A) → H^{n+1}(X,A)` is exact. -/
theorem pairExact₃ {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk (restrCoh A ℤ n) (pairδC A n) (restrCoh_comp_pairδC A n)).Exact :=
  Work.Cohomology.pair_exact₃ ℤ (TopCat.of X) A n

end

end Work.Thom
