import Mathlib
import Submission.Work.LerayHirsch.LhGlueDefs
import Submission.Work.LerayHirsch.lhMap_comap
import Submission.Work.LerayHirsch.zetaPow_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Naturality of the uniform Leray--Hirsch map

The uniform Leray--Hirsch map `Work.LerayHirsch.lhAny Z k` of
`Submission/Work/LerayHirsch/LhGlueDefs.lean` sends a family `(x_i)_{2i ≤ k}` to
`Σ_i π^*(x_i) ⌣ ζ^i`.  This module proves that it is natural under pullback of the bundle along a
continuous map `f : B' → B`:

`P(f)^*(lhAny Z k x) = lhAny (f^*Z) k (f^*(x_i))_i`,

the companion in every degree of the naturality `Work.LerayHirsch.lhMap_comap` of the even
Leray--Hirsch map.  It is exactly what is needed to identify the two sides of the Mayer--Vietoris
ladder of the Leray--Hirsch induction for the pullback bundle.

The proof is summand by summand, using the naturality of the degree transport
(`Work.Whitney.cohTransport_CohMap`), of the cup product (`Work.Cohomology.cupNaturalH`), of the
projection (the definition of `Work.LerayHirsch.projMapComap` together with
`Work.LerayHirsch.projMap_projMapComap`) and of the powers of the hyperplane class
(`Work.LerayHirsch.zetaPow_comap`).
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {B' : Type} [TopologicalSpace B']
variable {ι : Type} {m : ℕ}

/-- **Naturality of the degree transport `cohTransportLM`** in the form in which the summands of
`lhAny` use it: this is `Work.Whitney.cohTransport_CohMap` with the function `cohTransport` (which
is `cohTransportLM` by definition) replaced by the linear-map version. -/
theorem cohTransportLM_CohMap {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    {n n' : ℕ} (h : n = n') (f : C(B₁, B₂)) (x : Coh ℤ n B₂) :
    (CohMap f ℤ n').hom (Work.Thom.cohTransportLM h x)
      = Work.Thom.cohTransportLM h ((CohMap f ℤ n).hom x) :=
  Work.Whitney.cohTransport_CohMap h f x

/-- **Naturality of the summands of the uniform Leray--Hirsch map**: the `i`-th summand of
`lhAny Z k` pulls back along `P(f) : P(f^*E) → P(E)` to the `i`-th summand of `lhAny (f^*E) k`,
with `x_i` replaced by `f^*(x_i)`. -/
theorem lhAnySummand_comap (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (f : C(B', B)) (k : ℕ) (i : lhIdx m k)
    (x : (j : lhIdx m k) → Coh ℤ (k - 2 * (j : ℕ)) B) :
    (CohMap (projMapComap Z f) ℤ k).hom (lhAnySummand Z k i x)
      = lhAnySummand (bundleComap Z f) k i
          (fun j => (CohMap f ℤ (k - 2 * (j : ℕ))).hom (x j)) := by
  rw [lhAnySummand, lhAnySummand]
  change (CohMap (projMapComap Z f) ℤ k).hom
      (Work.Thom.cohTransportLM (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)
        (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjSpace Z))
          (k - 2 * (i : ℕ)) (2 * (i : ℕ))
          ((CohMap (projMap Z) ℤ (k - 2 * (i : ℕ))).hom (x i))
          (zetaPow Z i)))
    = Work.Thom.cohTransportLM (by omega : k - 2 * (i : ℕ) + 2 * (i : ℕ) = k)
        (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjSpace (bundleComap Z f)))
          (k - 2 * (i : ℕ)) (2 * (i : ℕ))
          ((CohMap (projMap (bundleComap Z f)) ℤ (k - 2 * (i : ℕ))).hom
            ((CohMap f ℤ (k - 2 * (i : ℕ))).hom (x i)))
          (zetaPow (bundleComap Z f) i))
  rw [cohTransportLM_CohMap]
  rw [Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (projMapComap Z f))
    (k - 2 * (i : ℕ)) (2 * (i : ℕ))
    ((CohMap (projMap Z) ℤ (k - 2 * (i : ℕ))).hom (x i)) (zetaPow Z i)]
  rw [Work.Thom.CohMap_comp_apply (projMapComap Z f) (projMap Z) ℤ (k - 2 * (i : ℕ)) (x i)]
  rw [show (projMap Z).comp (projMapComap Z f) = f.comp (projMap (bundleComap Z f)) from
    ContinuousMap.ext (fun y => projMap_projMapComap Z f y)]
  rw [← Work.Thom.CohMap_comp_apply (projMap (bundleComap Z f)) f ℤ (k - 2 * (i : ℕ)) (x i)]
  rw [zetaPow_comap Z f i]

/-- **Naturality of the uniform Leray--Hirsch map**: the decomposition
`(x_i) ↦ Σ_i π^*(x_i) ⌣ ζ^i` pulls back along `P(f) : P(f^*E) → P(E)` to the decomposition for
`f^*E` (with `x_i` replaced by `f^*(x_i)`), in **every** degree `k`. -/
theorem lhAny_glue_comap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B'] {ι : Type} {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (f : C(B', B)) (k : ℕ)
    (x : (i : Work.LerayHirsch.lhIdx m k) → Work.Thom.Coh ℤ (k - 2 * (i : ℕ)) B) :
    (Work.Thom.CohMap (Work.LerayHirsch.projMapComap Z f) ℤ k).hom (Work.LerayHirsch.lhAny Z k x)
      = Work.LerayHirsch.lhAny (Work.Thom.bundleComap Z f) k
          (fun i => (Work.Thom.CohMap f ℤ (k - 2 * (i : ℕ))).hom (x i)) := by
  simp only [lhAny_apply, lhAnyLM, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun i _ => lhAnySummand_comap Z f k i x)

end

end Work.LerayHirsch
