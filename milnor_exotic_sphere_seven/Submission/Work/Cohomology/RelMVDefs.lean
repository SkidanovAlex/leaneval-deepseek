import Submission.Work.Cohomology.SmallSES
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The relative small chains, and the definitions of the relative Mayer–Vietoris sequence

For a space `X`, subsets `U, V ⊆ X` and a subset `A ⊆ X`, the **relative small chains**
`C^{U,V}_*(X,A)` are the quotient of the small chains of `X` (the chains spanned by the simplices
whose image lies in `U` or in `V`) by the small chains whose simplices lie in `A`.  The
Mayer–Vietoris short exact sequence for a *pair* reads

`0 → C_*(U ∩ V, U ∩ V ∩ A) → C_*(U, U ∩ A) ⊕ C_*(V, V ∩ A) → C^{U,V}_*(X,A) → 0`,

and combined with the small-chains theorem for the pair it gives the long exact sequence

`… → Hⁿ(X,A) → Hⁿ(U,U∩A) ⊕ Hⁿ(V,V∩A) → Hⁿ(U∩V,U∩V∩A) → Hⁿ⁺¹(X,A) → …`

which is the algebraic tool underlying the proof of Lefschetz duality (Hatcher, Theorem 3.43) and
hence of the self-intersection formula for the zero section of a disc bundle.

Everything in this file is stated for an arbitrary simplicial set in the form of the singular
simplicial set of `X`; the *small* simplices are the ones handled by
`Submission/Work/Cohomology/SmallChains.lean`.

## Main definitions

* `IsSmallIn U V A σ` — `σ` is small and its image lies in `A`;
* `smallInSubcomplex U V A` — the corresponding subcomplex of the singular simplicial set;
* `smallInChains U V A` — its `ℤ`-chains;
* `subInclChain U V h` — the inclusion of subcomplexes for `C ⊆ B`;
* `relSmallChains U V B C h` — the cokernel of `subInclChain U V h`, i.e. `C^{U,V}_*(B,C)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- A singular simplex of `X` is **small for the pair `(U,V)` and lies in `A`** when it is small
(`Work.Cohomology.IsSmall`) and the image of the simplex is contained in `A`. -/
def IsSmallIn (U V A : Set X) {n : SimplexCategoryᵒᵖ} (σ : (TopCat.toSSet.obj X).obj n) : Prop :=
  IsSmall U V σ ∧
    Set.range (fun z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)) =>
      TopCat.toSSetObjEquiv X n σ z) ⊆ A

/-- The restriction of a simplicial map preserves being small and lying in `A`. -/
theorem IsSmallIn.map {U V A : Set X} {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m)
    {σ : (TopCat.toSSet.obj X).obj n} (h : IsSmallIn U V A σ) :
    IsSmallIn U V A ((TopCat.toSSet.obj X).map i σ) := by
  refine ⟨IsSmall.map i h.1, ?_⟩
  have hsub : Set.range (fun z : Convexity.StdSimplex ℝ (Fin (m.unop.len + 1)) =>
        TopCat.toSSetObjEquiv X m ((TopCat.toSSet.obj X).map i σ) z)
      ⊆ Set.range (fun z : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1)) =>
        TopCat.toSSetObjEquiv X n σ z) := by
    rintro y ⟨z, rfl⟩
    exact ⟨Convexity.StdSimplex.map i.unop z, TopCat.toSSetObjEquiv_naturality_apply i.unop σ z⟩
  exact hsub.trans h.2

/-- **The subcomplex of the small simplices lying in `A`.** -/
def smallInSubcomplex (U V A : Set X) : (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | IsSmallIn U V A σ}
  map i := fun _ hx => IsSmallIn.map i hx

/-- `smallInSubcomplex U V A` is contained in the small subcomplex. -/
theorem smallInSubcomplex_le (U V A : Set X) : smallInSubcomplex U V A ≤ smallSubcomplex U V :=
  fun _ _ hx => hx.1

/-- Monotonicity of the subcomplexes. -/
theorem smallInSubcomplex_mono {U V : Set X} {A B : Set X} (h : A ⊆ B) :
    smallInSubcomplex U V A ≤ smallInSubcomplex U V B :=
  fun _ _ hx => ⟨hx.1, hx.2.trans h⟩

/-- The subcomplex of small simplices lying in `A`, as a simplicial set. -/
abbrev smallInSSet (U V A : Set X) : SSet := smallInSubcomplex U V A

/-- **The small chains lying in `A`**. -/
abbrev smallInChains (U V A : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  (smallInSSet U V A).chainComplex (ModuleCat.of ℤ ℤ)

/-- The inclusion of the small chains of `C` into those of `B`, for `C ⊆ B`. -/
def subInclChain (U V : Set X) {B C : Set X} (h : C ⊆ B) :
    smallInChains U V C ⟶ smallInChains U V B :=
  SSet.chainComplexMap (Subfunctor.homOfLe (by
    intro n x hx
    exact ⟨hx.1, hx.2.trans h⟩)) (ModuleCat.of ℤ ℤ)

/-- The canonical map from the small chains lying in `A` to the small chains of `(U,V)`. -/
def smallInToSmall (U V A : Set X) : smallInChains U V A ⟶ smallChains U V :=
  SSet.chainComplexMap (Subfunctor.homOfLe (smallInSubcomplex_le U V A)) (ModuleCat.of ℤ ℤ)

/-- **The relative small chains** `C^{U,V}_*(B,C)`: the small chains lying in `B` modulo those
lying in `C`, for `C ⊆ B`. -/
abbrev relSmallChains (U V B C : Set X) (h : C ⊆ B) : ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (subInclChain U V h)

/-- **The relative small chains of the pair `(X,A)`**: the small chains of `(U,V)` modulo the
small simplices lying in `A`. -/
abbrev relSmallTop (U V A : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  cokernel (smallInToSmall U V A)

end

end Work.Cohomology
