import Mathlib
import Submission.Work.Cohomology.Affine
import Submission.Work.Homology.SimplexShim

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Affine chains and the combinatorial cone on `Δᴺ`

This file provides the algebraic scaffolding for the **barycentric subdivision** of simplices, the
missing ingredient for the small-simplices / Mayer–Vietoris theorem (`Submission/NOTES.md`,
session 5, "THE DESIGN OF THE SUBDIVISION CHAPTER").

An **affine chain** of degree `k` in `Δᴺ` is a formal `ℤ`-linear combination of vertex families
`Fin (k+1) → Δᴺ`; via `toChain` such a chain is sent to the corresponding chain of affine singular
simplices of the standard simplex `Delta N`.  The whole subdivision of the standard simplices is
combinatorics of these affine chains:

* `faceVF i v` — the `i`-th face of a vertex family (omitting the `i`-th vertex);
* `boundaryLC` — the alternating sum of the face maps, the affine analogue of `∂`;
* `coneVF b v`, `coneLC b` — the *cone* over a point `b`, prepending `b` to a vertex family;
* `bary v` — the barycentre of a vertex family (the coning point used for the subdivision);
* `idVert N` — the vertex family of the identity simplex of `Δᴺ`;
* `toChain` — the affine chain ↦ singular chain translation.

The key identity of the theory, delegated separately, is the sign-free cone formula

`boundaryLC (coneLC b c) = c - coneLC b (boundaryLC c)`

which is what makes the recursive definition `sdLC (n+1) := coneLC (bary …) (Σ i, (-1)^i • …)`
a chain map: the coned chain is a cycle, by the simplicial identity `δᵢ δⱼ = δ_{j+1} δᵢ`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **Affine `k`-chains of `Δᴺ`**: formal `ℤ`-linear combinations of vertex families
`Fin (k+1) → Δᴺ`, i.e. of affine parametrisations of `k`-simplices of `Δᴺ`. -/
abbrev LinChain (N k : ℕ) := (Fin (k + 1) → stdSimplex ℝ (Fin (N + 1))) →₀ ℤ

/-- The vertex family of the identity simplex of `Δᴺ`. -/
def idVert (N : ℕ) : Fin (N + 1) → stdSimplex ℝ (Fin (N + 1)) :=
  fun i => stdSimplex.vertex i

/-- The `i`-th face of a vertex family: the family with the `i`-th vertex omitted. -/
def faceVF {N k : ℕ} (i : Fin (k + 2)) (v : Fin (k + 2) → stdSimplex ℝ (Fin (N + 1))) :
    Fin (k + 1) → stdSimplex ℝ (Fin (N + 1)) :=
  fun j => v (Fin.succAbove i j)

/-- The cone of an affine simplex over a point `b`: prepend `b` to the vertex family. -/
def coneVF {N k : ℕ} (b : stdSimplex ℝ (Fin (N + 1)))
    (v : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1))) :
    Fin (k + 2) → stdSimplex ℝ (Fin (N + 1)) :=
  Fin.cons b v

/-- The **barycentre** of a vertex family: the average of its vertices.  This is the point over
which the boundary of a simplex is coned to produce the barycentric subdivision. -/
def bary {N k : ℕ} (v : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1))) :
    stdSimplex ℝ (Fin (N + 1)) :=
  ⟨fun i => (k + 1 : ℝ)⁻¹ * ∑ j, v j i, by
    constructor
    · intro i
      exact mul_nonneg (inv_nonneg.mpr (by positivity))
        (Finset.sum_nonneg fun j _ => (v j).2.1 i)
    · have h2 : (∑ i, ∑ j, v j i) = (k + 1 : ℝ) := by
        rw [Finset.sum_comm]
        simp
      rw [← Finset.mul_sum, h2, inv_mul_cancel₀]
      exact Nat.cast_add_one_ne_zero k⟩

/-- The alternating sum of the face maps on affine chains: the affine analogue of the boundary. -/
def boundaryLC (N k : ℕ) : LinChain N (k + 1) →ₗ[ℤ] LinChain N k :=
  ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.lmapDomain ℤ ℤ (faceVF (N := N) i)

/-- The cone of an affine chain over a point `b`. -/
def coneLC (N k : ℕ) (b : stdSimplex ℝ (Fin (N + 1))) :
    LinChain N k →ₗ[ℤ] LinChain N (k + 1) :=
  Finsupp.lmapDomain ℤ ℤ (coneVF b)

/-- The singular chain of `Δᴺ` determined by an affine chain: the sum of the affine simplices. -/
def toChain (N k : ℕ) : LinChain N k →ₗ[ℤ]
    ((TopCat.toSSet.obj (Delta N)).chainComplex (ModuleCat.of ℤ ℤ)).X k :=
  Finsupp.linearCombination ℤ fun w : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1)) =>
    (((TopCat.toSSet.obj (Delta N)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      (linSimplex w)).hom (1 : ℤ))

/-- The `i`-th face embedding on affine chains: post-compose every vertex with the `i`-th face map
`Δ^N → Δ^{N+1}` (so that the subdivision of the boundary of `Δ^{N+1}` can be coned over the
barycentre). -/
def embedLC (N k : ℕ) (i : Fin (N + 2)) : LinChain N k →ₗ[ℤ] LinChain (N + 1) k :=
  Finsupp.lmapDomain ℤ ℤ fun v : Fin (k + 1) → stdSimplex ℝ (Fin (N + 1)) =>
    fun j => stdSimplex.map (Fin.succAbove i) (v j)

/-- **The barycentric subdivision of the standard simplices.**  `sdLC n` is the subdivision of the
identity `n`-simplex of `Δⁿ`, as a formal `ℤ`-combination of affine simplices: it is obtained by
coning the subdivided boundary of `Δⁿ` over the barycentre,

`sdLC (n+1) = coneLC (barycentre) (Σ i, (-1)^i embedLC_i (sdLC n))`. -/
def sdLC : (n : ℕ) → LinChain n n :=
  Nat.rec (Finsupp.single (idVert 0) 1) fun n ih =>
    coneLC (n + 1) n (bary (idVert (n + 1)))
      (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC n n i ih)

/-- The **subdivision of the identity simplex** of `Δⁿ`, as a singular chain of `Δⁿ`. -/
def sdChain (n : ℕ) :
    ((TopCat.toSSet.obj (Delta n)).chainComplex (ModuleCat.of ℤ ℤ)).X n :=
  toChain n n (sdLC n)

/-- The subdivision of a single singular simplex `σ` of a space `X`: push the subdivision of the
identity simplex of `Δⁿ` forward along `σ` (viewed as a continuous map `Delta n ⟶ X`). -/
def sdElem (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (singularChains ℤ X).X n :=
  ((SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom
      (Work.Homology.toSSetObjEquiv' X (Opposite.op ⦋n⦌) σ))) (ModuleCat.of ℤ ℤ)).f n).hom
    (sdChain n)

/-- **The subdivision operator on singular chains.**  On a generator `ι σ` it is `sdElem X n σ`;
it is defined through the universal property of the chain module as the coproduct of copies of `ℤ`
indexed by the singular `n`-simplices. -/
def sdHom (X : TopCat) (n : ℕ) : (singularChains ℤ X).X n ⟶ (singularChains ℤ X).X n :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).desc
    (Cofan.mk ((singularChains ℤ X).X n)
      (fun σ : (TopCat.toSSet.obj X) _⦋n⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (sdElem X n σ))))

/-- The subdivision operator, as a linear map on `n`-chains. -/
def Sd (X : TopCat) (n : ℕ) :
    (singularChains ℤ X).X n →ₗ[ℤ] (singularChains ℤ X).X n :=
  (sdHom X n).hom

end

end Work.Cohomology
