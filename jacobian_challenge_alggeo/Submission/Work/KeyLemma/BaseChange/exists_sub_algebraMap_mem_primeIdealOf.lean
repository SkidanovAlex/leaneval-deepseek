/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sections over an affine open, constants, and the prime ideal of a `k`-rational point

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k`, let `p` be a
`k`-point of `C`, and let `Q = placeOfPoint C p` be the closed point (place) which is its
image.  Let `W ⊆ C` be an affine open neighbourhood of `Q`.  This file shows that every
section `r ∈ Γ(C, W)` differs from a *constant* section by an element of the prime ideal of
`Q`:

> `∃ c : k, r - c ∈ P`,  where `P = (hW.primeIdealOf ⟨Q.point, hQW⟩).asIdeal`.

Equivalently, the evaluation map `Γ(C, W) → κ(Q)` has image exactly the constants `k`,
because `Q` is a `k`-rational point, i.e. `[κ(Q) : k] = 1`.

## Proof

Write `φ : Γ(C,W) →+* κ(Q)` for the evaluation at `Q` (`Scheme.evaluation`), the composite of
the germ map `Γ(C,W) → 𝒪_{C,Q}` with the residue map `𝒪_{C,Q} → κ(Q)`.

* `ker_evaluation_primeIdealOf`: `ker φ = P`.  Indeed `hW.primeIdealOf_eq_map_closedPoint`
  identifies `P` with the contraction of the maximal ideal of the local ring `𝒪_{C,Q}`
  along the germ, and `IsLocalRing.ker_residue` identifies the kernel of the residue map
  with that maximal ideal.
* `evaluation_algebraMap_sections`: `φ` is a `k`-algebra map, where the `k`-structure on
  `Γ(C,W)` is `Curve.instAlgebraSections` and that on `κ(Q)` is
  `Place.instAlgebraResidueField`.  Both are built from the structure morphism `C ⟶ Spec k`,
  and the identity reduces to the naturality of `Scheme.evaluation` and of the germ.
* `residueField_algebraMap_surjective`: `k → κ(Q)` is onto since
  `[κ(Q) : k] = Q.degree = 1` (`Place.placeOfPoint_degree`) and
  `Work.CurveBasics.Place.degree_eq_finrank` identifies `Q.degree` with `finrank k κ(Q)`.

Given `r`, choose `c` with `algebraMap k κ(Q) c = φ r`; then
`φ (r - algebraMap k Γ(C,W) c) = φ r - φ (algebraMap k Γ(C,W) c) = algebraMap k κ(Q) c - φ r = 0`,
so `r - c ∈ ker φ = P`.
-/
import Mathlib
import Submission.Work.KeyLemma.BaseChange
import Submission.Work.KeyLemma.Place.placeOfPoint_degree

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.KeyLemma.BaseChange

open CategoryTheory AlgebraicGeometry
open scoped Classical

universe u

/-- The kernel of the evaluation map at the place `Q = placeOfPoint C p` is the prime ideal
defining `Q` in the affine ring `Γ(C, W)`. -/
lemma ker_evaluation_primeIdealOf {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (p : Work.KeyLemma.Curve.Point C) (W : C.left.Opens)
    (hW : AlgebraicGeometry.IsAffineOpen W)
    (hQW : (Work.KeyLemma.Curve.placeOfPoint C p).point ∈ W) :
    RingHom.ker (C.left.evaluation W (Work.KeyLemma.Curve.placeOfPoint C p).point hQW).hom
      = (hW.primeIdealOf ⟨(Work.KeyLemma.Curve.placeOfPoint C p).point, hQW⟩).asIdeal := by
  rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint, AlgebraicGeometry.Spec.map_apply,
    PrimeSpectrum.comap_asIdeal]
  rw [show (IsLocalRing.closedPoint
        (C.left.presheaf.stalk (Work.KeyLemma.Curve.placeOfPoint C p).point)).asIdeal
      = IsLocalRing.maximalIdeal _ from rfl]
  rw [← Scheme.germ_residue, CommRingCat.hom_comp, ← IsLocalRing.ker_residue, RingHom.comap_ker]
  rfl

/-- The evaluation map at `Q = placeOfPoint C p` is a map of `k`-algebras: the constant
section with value `c` evaluates to the constant `c ∈ k ⊆ κ(Q)`. -/
lemma evaluation_algebraMap_sections {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (p : Work.KeyLemma.Curve.Point C) (W : C.left.Opens)
    (_hW : AlgebraicGeometry.IsAffineOpen W)
    (hQW : (Work.KeyLemma.Curve.placeOfPoint C p).point ∈ W) (c : k) :
    C.left.evaluation W (Work.KeyLemma.Curve.placeOfPoint C p).point hQW
        (algebraMap k (C.left.presheaf.obj (Opposite.op W)) c)
      = algebraMap k (C.left.residueField (Work.KeyLemma.Curve.placeOfPoint C p).point) c := by
  have hger : ∀ b : Γ(Spec (CommRingCat.of k), ⊤),
      C.left.presheaf.germ W (Work.KeyLemma.Curve.placeOfPoint C p).point hQW
          ((C.hom.appLE ⊤ W le_top) b)
        = C.left.presheaf.germ (⊤ : C.left.Opens) (Work.KeyLemma.Curve.placeOfPoint C p).point
            trivial (C.hom.appTop b) := by
    intro b
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    congr 1
    simp only [Scheme.Hom.appLE, Category.assoc]
    rw [TopCat.Presheaf.germ_res]
    simp only [TopologicalSpace.Opens.map_top, Scheme.Hom.appTop]
  have hres : algebraMap k (C.left.residueField (Work.KeyLemma.Curve.placeOfPoint C p).point) c =
      C.left.residue (Work.KeyLemma.Curve.placeOfPoint C p).point
        (C.left.presheaf.germ (⊤ : C.left.Opens) (Work.KeyLemma.Curve.placeOfPoint C p).point
          trivial
          (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) := by
    simp only [RingHom.algebraMap_toAlgebra, ConcreteCategory.comp_apply]
    rw [Scheme.Γevaluation_naturality_apply]
    rfl
  rw [hres]
  have h1 : (algebraMap k Γ(C.left,W)) c =
      (C.hom.appLE ⊤ W le_top) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := rfl
  rw [h1, ← Scheme.germ_residue, ConcreteCategory.comp_apply, hger]

/-- The residue field of the `k`-rational place `Q = placeOfPoint C p` is one-dimensional
over `k`, so the structure map `k → κ(Q)` is surjective. -/
lemma residueField_algebraMap_surjective {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (p : Work.KeyLemma.Curve.Point C) :
    Function.Surjective
      (algebraMap k (C.left.residueField (Work.KeyLemma.Curve.placeOfPoint C p).point)) := by
  have hdeg : (Work.KeyLemma.Curve.placeOfPoint C p).degree = 1 :=
    Work.KeyLemma.Place.placeOfPoint_degree C p
  have hfin : Module.finrank k
      (C.left.residueField (Work.KeyLemma.Curve.placeOfPoint C p).point) = 1 := by
    rw [← Work.CurveBasics.Place.degree_eq_finrank (Work.KeyLemma.Curve.placeOfPoint C p), hdeg]
  rw [finrank_eq_one_iff_of_nonzero'
    (1 : C.left.residueField (Work.KeyLemma.Curve.placeOfPoint C p).point) one_ne_zero] at hfin
  intro w
  obtain ⟨c, hc⟩ := hfin w
  refine ⟨c, ?_⟩
  rw [Algebra.smul_def, mul_one] at hc
  exact hc

theorem exists_sub_algebraMap_mem_primeIdealOf {k : Type u} [Field k]
    (C : Work.CurveBasics.Curve k)
    (p : Work.KeyLemma.Curve.Point C) (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    (hQW : (Work.KeyLemma.Curve.placeOfPoint C p).point ∈ W)
    (r : C.left.presheaf.obj (Opposite.op W)) :
    ∃ c : k, r - algebraMap k (C.left.presheaf.obj (Opposite.op W)) c ∈
      (hW.primeIdealOf ⟨(Work.KeyLemma.Curve.placeOfPoint C p).point, hQW⟩).asIdeal := by
  obtain ⟨c, hc⟩ := residueField_algebraMap_surjective C p
    ((C.left.evaluation W (Work.KeyLemma.Curve.placeOfPoint C p).point hQW) r)
  refine ⟨c, ?_⟩
  rw [← ker_evaluation_primeIdealOf C p W hW hQW, RingHom.mem_ker, map_sub,
    evaluation_algebraMap_sections C p W hW hQW c, hc, sub_self]

end Work.KeyLemma.BaseChange
