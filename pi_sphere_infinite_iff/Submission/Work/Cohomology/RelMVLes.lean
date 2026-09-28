import Submission.Work.Cohomology.relMV_shortExact
import Submission.Work.Cohomology.relMV_quasiIso

/-!
# The relative Mayer–Vietoris long exact sequence

For a space `X`, subsets `U, V ⊆ X` and a subset `A ⊆ X`, the relative Mayer–Vietoris short exact
sequence of chain complexes (`Submission/Work/Cohomology/relMV_shortExact.lean`)

`0 ⟶ C^{U,V}_*(U∩V, U∩V∩A) ⟶ C^{U,V}_*(U,U∩A) ⊞ C^{U,V}_*(V,V∩A) ⟶ C^{U,V}_*(X,A) ⟶ 0`

gives, by the homology sequence, the long exact sequence

`⋯ ⟶ Hₙ(U∩V, U∩V∩A) ⟶ Hₙ(U,U∩A) ⊕ Hₙ(V,V∩A) ⟶ Hₙ(C^{U,V}(X,A)) ⟶ Hₙ₋₁(U∩V, U∩V∩A) ⟶ ⋯`

and the small-chains theorem for the pair (`Submission/Work/Cohomology/relMV_quasiIso.lean`)
identifies `Hₙ(C^{U,V}(X,A))` with the relative singular homology `Hₙ(X,A)`.

This file fixes the witnesses of `Work.Cohomology.relMV_shortExact` and
`Work.Cohomology.relMV_quasiIso` once and for all and records the resulting long exact sequence, in
the style of `Submission/Work/Cohomology/MVSequence.lean`.

## Main definitions and results

* `relMVF`, `relMVG`, `relMVShort`, `relMVShort_shortExact` — the short complex and its exactness;
* `relMVδ`, `relMVδ_comp`, `relMV_comp_δ` — the connecting homomorphism and the vanishing
  composites;
* `relMV_exact₁/₂/₃` — exactness at the three terms;
* `relMVPhi`, `relMVPhi_isIso`, `relMVPhi_comp`, `relMVSmallIso` — the identification of the third
  term with `Hₙ(X,A)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- The first map of the relative Mayer–Vietoris sequence (a chosen witness). -/
def relMVF (X : TopCat) (A U V : Set X) := Classical.choose (relMV_shortExact X A U V)

/-- The second map of the relative Mayer–Vietoris sequence (a chosen witness). -/
def relMVG (X : TopCat) (A U V : Set X) :=
  Classical.choose (Classical.choose_spec (relMV_shortExact X A U V))

/-- The composite of the two maps of the relative Mayer–Vietoris sequence is zero (a chosen
witness). -/
theorem relMVzero (X : TopCat) (A U V : Set X) :
    CategoryTheory.CategoryStruct.comp (relMVF X A U V) (relMVG X A U V) = 0 :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (relMV_shortExact X A U V)))

/-- **The relative Mayer–Vietoris short complex.** -/
def relMVShort (X : TopCat) (A U V : Set X) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (relMVF X A U V) (relMVG X A U V) (relMVzero X A U V)

/-- **The relative Mayer–Vietoris short complex is short exact.** -/
theorem relMVShort_shortExact (X : TopCat) (A U V : Set X) :
    (relMVShort X A U V).ShortExact :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (relMV_shortExact X A U V)))

/-- The first term of the relative Mayer–Vietoris sequence. -/
abbrev relMVH₁ (X : TopCat) (A U V : Set X) (n : ℕ) : ModuleCat ℤ :=
  (relMVShort X A U V).X₁.homology n

/-- The second term of the relative Mayer–Vietoris sequence. -/
abbrev relMVH₂ (X : TopCat) (A U V : Set X) (n : ℕ) : ModuleCat ℤ :=
  (relMVShort X A U V).X₂.homology n

/-- The third term of the relative Mayer–Vietoris sequence. -/
abbrev relMVH₃ (X : TopCat) (A U V : Set X) (n : ℕ) : ModuleCat ℤ :=
  (relMVShort X A U V).X₃.homology n

/-- **The connecting homomorphism** `Hₙ₊₁(C^{U,V}(X,A)) ⟶ Hₙ(U∩V, U∩V∩A)` of the relative
Mayer–Vietoris sequence. -/
def relMVδ (X : TopCat) (A U V : Set X) (n : ℕ) :
    relMVH₃ X A U V (n + 1) ⟶ relMVH₁ X A U V n :=
  (relMVShort_shortExact X A U V).δ (n + 1) n (by simp [ComplexShape.down])

/-- Exactness of the relative Mayer–Vietoris sequence at the first term. -/
theorem relMV_exact₁ (X : TopCat) (A U V : Set X) (n : ℕ) :
    (ShortComplex.mk (relMVδ X A U V n)
      (HomologicalComplex.homologyMap (relMVF X A U V) n)
      (by
        show relMVδ X A U V n ≫ HomologicalComplex.homologyMap (relMVF X A U V) n = 0
        exact (relMVShort_shortExact X A U V).δ_comp (n + 1) n (by simp [ComplexShape.down]))).Exact :=
  (relMVShort_shortExact X A U V).homology_exact₁ (n + 1) n (by simp [ComplexShape.down])

/-- Exactness of the relative Mayer–Vietoris sequence at the second term. -/
theorem relMV_exact₂ (X : TopCat) (A U V : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (relMVF X A U V) n)
      (HomologicalComplex.homologyMap (relMVG X A U V) n)
      (by rw [← HomologicalComplex.homologyMap_comp, relMVzero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (relMVShort_shortExact X A U V).homology_exact₂ n

/-- Exactness of the relative Mayer–Vietoris sequence at the third term. -/
theorem relMV_exact₃ (X : TopCat) (A U V : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (relMVG X A U V) (n + 1))
      (relMVδ X A U V n)
      (by
        show HomologicalComplex.homologyMap (relMVG X A U V) (n + 1) ≫ relMVδ X A U V n = 0
        exact (relMVShort_shortExact X A U V).comp_δ (n + 1) n (by simp [ComplexShape.down]))).Exact :=
  (relMVShort_shortExact X A U V).homology_exact₃ (n + 1) n (by simp [ComplexShape.down])

/-- **The small-chains map for the pair**: a chosen witness of
`Submission.Work.Cohomology.relMV_quasiIso`. -/
def relMVPhi (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) : relSmallTop U V A ⟶ relChains X A :=
  Classical.choose (relMV_quasiIso X A U V hU hV hcov)

/-- The small-chains map for the pair is a quasi-isomorphism. -/
theorem relMVPhi_isIso (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relMVPhi X A U V hU hV hcov) n) :=
  (Classical.choose_spec (relMV_quasiIso X A U V hU hV hcov)).1 n

/-- The defining property of the small-chains map for the pair. -/
theorem relMVPhi_comp (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) :
    CategoryTheory.CategoryStruct.comp
        (CategoryTheory.Limits.cokernel.π (smallInToSmall U V A)) (relMVPhi X A U V hU hV hcov)
      = CategoryTheory.CategoryStruct.comp (smallToSing U V)
          (CategoryTheory.Limits.cokernel.π (inclChains X A)) :=
  (Classical.choose_spec (relMV_quasiIso X A U V hU hV hcov)).2

/-- **The identification of the third term of the relative Mayer–Vietoris sequence with the
relative singular homology** `Hₙ(X,A)`. -/
def relMVSmallIso (X : TopCat) (A U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    relMVH₃ X A U V n ≅ (relChains X A).homology n :=
  letI := relMVPhi_isIso X A U V hU hV hcov n
  asIso (HomologicalComplex.homologyMap (relMVPhi X A U V hU hV hcov) n)

end

end Work.Cohomology
