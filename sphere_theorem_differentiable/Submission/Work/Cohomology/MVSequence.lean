import Mathlib
import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.mvComp
import Submission.Work.Cohomology.mv_shortExact
import Submission.Work.Cohomology.smallChains_homology_iso

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Mayer–Vietoris long exact sequence

Let `X` be a topological space and `U V ⊆ X`.  The Mayer–Vietoris short exact sequence of chain
complexes (`Submission/Work/Cohomology/SmallSES.lean`, `mvComp`, `mv_shortExact`)

`0 ⟶ C_*(U ∩ V) ⟶ C_*(U) ⊞ C_*(V) ⟶ C^{U,V}_*(X) ⟶ 0`

gives, by the homology sequence of `Submission/Work/Cohomology/mv_shortExact.lean`, the long exact
sequence

`⋯ ⟶ Hₙ(U ∩ V) ⟶ Hₙ(U) ⊕ Hₙ(V) ⟶ Hₙ(C^{U,V}) ⟶ Hₙ₋₁(U ∩ V) ⟶ ⋯`

and the small-chains theorem (`smallChains_homology_iso`) identifies `Hₙ(C^{U,V})` with the
singular homology `Hₙ(X)`.

## Main definitions and results

* `mvShort` — the Mayer–Vietoris short complex;
* `mvShort_shortExact` — it is short exact;
* `HSmall`, `HInter`, `HBiprod` — the three terms of the sequence, in homology;
* `mvδ`, `mvδ_comp`, `mv_comp_δ` — the connecting homomorphism and the two vanishing composites;
* `mv_H_exact₁`, `mv_H_exact₂`, `mv_H_exact₃` — exactness at the three terms;
* `smallIso` — the isomorphism `Hₙ(C^{U,V}) ≅ Hₙ(X)` (for an open cover);
* `mvδX`, `mvLeftX`, `mvRightX` — the maps of the sequence with `Hₙ(X)` as the third term.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- **The Mayer–Vietoris short complex** of the pair of subsets `U, V` of `X`. -/
abbrev mvShort (U V : Set X) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (mvLeft U V) (mvRight U V) (mvComp U V)

/-- The Mayer–Vietoris short complex is short exact. -/
theorem mvShort_shortExact (U V : Set X) : (mvShort U V).ShortExact := mv_shortExact U V

/-- `Hₙ` of the small chains of the cover `{U, V}` (the third term of the sequence). -/
abbrev HSmall (U V : Set X) (n : ℕ) : ModuleCat ℤ := (mvShort U V).X₃.homology n

/-- `Hₙ(U ∩ V)` (the first term of the sequence). -/
abbrev HInter (U V : Set X) (n : ℕ) : ModuleCat ℤ := (mvShort U V).X₁.homology n

/-- `Hₙ(U) ⊞ Hₙ(V)` (the second term of the sequence). -/
abbrev HBiprod (U V : Set X) (n : ℕ) : ModuleCat ℤ := (mvShort U V).X₂.homology n

/-- Exactness of the Mayer–Vietoris sequence at `Hₙ(U) ⊞ Hₙ(V)`. -/
theorem mv_H_exact₂ (U V : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (mvLeft U V) n)
      (HomologicalComplex.homologyMap (mvRight U V) n)
      (by rw [← HomologicalComplex.homologyMap_comp, mvComp,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (mvShort_shortExact U V).homology_exact₂ n

/-- **The connecting homomorphism** `Hₙ₊₁(C^{U,V}) ⟶ Hₙ(U ∩ V)` of the Mayer–Vietoris sequence. -/
def mvδ (U V : Set X) (n : ℕ) : HSmall U V (n + 1) ⟶ HInter U V n :=
  (mvShort_shortExact U V).δ (n + 1) n (by simp [ComplexShape.down])

/-- The connecting homomorphism followed by the map to `Hₙ(U) ⊞ Hₙ(V)` is zero. -/
theorem mvδ_comp (U V : Set X) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (mvδ U V n)
      (HomologicalComplex.homologyMap (mvLeft U V) n) = 0 :=
  (mvShort_shortExact U V).δ_comp (n + 1) n (by simp [ComplexShape.down])

/-- The map `Hₙ₊₁(U) ⊞ Hₙ₊₁(V) ⟶ Hₙ₊₁(C^{U,V})` followed by the connecting homomorphism is
zero. -/
theorem mv_comp_δ (U V : Set X) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (mvRight U V) (n + 1))
      (mvδ U V n) = 0 :=
  (mvShort_shortExact U V).comp_δ (n + 1) n (by simp [ComplexShape.down])

/-- Exactness of the Mayer–Vietoris sequence at `Hₙ(U ∩ V)`. -/
theorem mv_H_exact₁ (U V : Set X) (n : ℕ) :
    (ShortComplex.mk (mvδ U V n) (HomologicalComplex.homologyMap (mvLeft U V) n)
      (mvδ_comp U V n)).Exact :=
  (mvShort_shortExact U V).homology_exact₁ (n + 1) n (by simp [ComplexShape.down])

/-- Exactness of the Mayer–Vietoris sequence at `Hₙ₊₁(C^{U,V})`. -/
theorem mv_H_exact₃ (U V : Set X) (n : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (mvRight U V) (n + 1)) (mvδ U V n)
      (mv_comp_δ U V n)).Exact :=
  (mvShort_shortExact U V).homology_exact₃ (n + 1) n (by simp [ComplexShape.down])

/-- **The small-chains isomorphism in homology**: for an open cover `U ∪ V = X`, the homology of
the small chains is the singular homology of `X`. -/
def smallIso (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (n : ℕ) :
    HSmall U V n ≅ (singularChains ℤ X).homology n :=
  letI := smallChains_homology_iso U V hU hV hcov n
  asIso (HomologicalComplex.homologyMap (smallToSing U V) n)

/-- The Mayer–Vietoris map `Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(X)`. -/
def mvRightX (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    HBiprod U V n ⟶ (singularChains ℤ X).homology n :=
  CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (mvRight U V) n)
    (smallIso U V hU hV hcov n).hom

/-- The Mayer–Vietoris connecting map `Hₙ₊₁(X) ⟶ Hₙ(U ∩ V)`. -/
def mvδX (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ) :
    (singularChains ℤ X).homology (n + 1) ⟶ HInter U V n :=
  CategoryTheory.CategoryStruct.comp (smallIso U V hU hV hcov (n + 1)).inv (mvδ U V n)

end

end Work.Cohomology
