import Mathlib
import Submission.Work.Pi6.SQM.SIG.sigmaNaturalDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# SQM / SIG — naturality of `q*`

`qStarLM K k₀ m = H^m(pairMapK K k₀)` is the pullback along the map of pairs
`(PK K, ΩK) → (K, {k₀})` induced by `evalOne K`.  The map `h : C(K,L)` sends `k₀` to `h k₀`;
on pairs it induces a square

```
(PK K, ΩK) --evalOne K--> (K, {k₀})
    |                         |
 pathMap                      h
    v                         v
(PK L, ΩL) --evalOne L--> (L, {h k₀})
```

which commutes (`pathMap_evalOne`).  Since the relative cochain complex is *contravariantly*
functorial in the pair, applying it to the square and taking homology yields the naturality
square for `q*`:

`h* ∘ q*_{K} = q*_{L} ∘ (pathMap)*`.

The mathematical content is exactly the functoriality `lmComp` of `Work.Cohomology.relComplexMap`
together with the compatibility `PKmap_evalOne`; the square is isolated as the general lemma
`relComplexMap_commSquare` below.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

/-- **The pair-map square.**  Let `(p, v)` be the "left/bottom" path and `(u, q)` the
"top/right" path of a commuting square of spaces carrying the subsets `A ⊆ X`, `B ⊆ Z`,
`C ⊆ Y`, `D ⊆ W`:

```
X --p--> Z
|         |
u         v
v         v
W --q--> Y
```

with `p ≫ v = u ≫ q`, and suppose each map carries the corresponding subset into the next.
Then the induced maps of relative cochain complexes commute:

`(D,C) → (A,D) → ...` — precisely, `q* ∘ u* = v* ∘ p*` as maps
`C^*(Y,C) ⟶ C^*(X,A)`. -/
lemma relComplexMap_commSquare (R : Type) [CommRing R] {X Z Y W : TopCat}
    (A : Set X) (B : Set Z) (C : Set Y) (D : Set W)
    (p : X ⟶ Z) (v : Z ⟶ Y) (u : X ⟶ W) (q : W ⟶ Y)
    (hp : ∀ x ∈ A, (ConcreteCategory.hom p) x ∈ B)
    (hv : ∀ y ∈ B, (ConcreteCategory.hom v) y ∈ C)
    (hu : ∀ x ∈ A, (ConcreteCategory.hom u) x ∈ D)
    (hq : ∀ y ∈ D, (ConcreteCategory.hom q) y ∈ C)
    (hcomm : p ≫ v = u ≫ q) :
    relComplexMap R D C q hq ≫ relComplexMap R A D u hu =
      relComplexMap R B C v hv ≫ relComplexMap R A B p hp := by
  have h1 := lmComp R A D C u q hu hq
  have h2 := lmComp R A B C p v hp hv
  rw [← h1, ← h2]
  exact lmCongr R A C hcomm.symm _ _

/-- Naturality of `q*`: the pullback along `pairMapK` is compatible with the maps induced by
`h : C(K,L)` on the base pair `(K,{k₀}) → (L,{h k₀})` and on the path-space pair
`(PK K, ΩK) → (PK L, ΩL)`. -/
theorem qStarNatural (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L)) (n : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (Work.Pi6.SQM.SIG.basePairMap K L k₀ h) (n + 2)) (Work.Pi6.SQM.SIG.qStarLM K k₀ (n + 2)) = CategoryTheory.CategoryStruct.comp (Work.Pi6.SQM.SIG.qStarLM L (h k₀) (n + 2)) (HomologicalComplex.homologyMap (Work.Pi6.SQM.SIG.pathPairMap K L k₀ h) (n + 2)) := by
  have key : (basePairMap K L k₀ h ≫ pairMapK K k₀) =
      (pairMapK L (h k₀) ≫ pathPairMap K L k₀ h) :=
    relComplexMap_commSquare (R := Work.Pi6.SQ.F2)
      (X := TopCat.of (PK K k₀)) (Z := TopCat.of (PK L (h k₀)))
      (Y := TopCat.of L) (W := TopCat.of K)
      (fibreSet K k₀) (fibreSet L (h k₀)) ({h k₀} : Set L) ({k₀} : Set K)
      (TopCat.ofHom (pathMap K L k₀ h))
      (TopCat.ofHom (Work.StemsB.evalOne L (h k₀)))
      (TopCat.ofHom (Work.StemsB.evalOne K k₀)) (TopCat.ofHom h)
      (fun x hx => pathMap_mem K L k₀ h x hx) (fun y hy => hy) (fun x hx => hx)
      (fun y hy => by simpa [Set.mem_singleton_iff] using congrArg h hy)
      (PKmap_evalOne K L k₀ h)
  have hhom := congrArg (fun φ => HomologicalComplex.homologyMap φ (n + 2)) key
  simpa [qStarLM, HomologicalComplex.homologyMap_comp] using hhom

end

end Work.Pi6.SQM.SIG
