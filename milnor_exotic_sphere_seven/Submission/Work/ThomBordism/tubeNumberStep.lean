import Mathlib
import Submission.Work.Agree.complexificationIso
import Submission.Work.Thom.pontryaginClass_one
import Submission.Work.Thom.pontryaginClass_comap
import Submission.Work.ThomBordism.normalBundle_pontryaginNumbers
import Submission.Work.ThomBordism.Grassmann.Model

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

/-!
# The number step of obligation 2: `⟨gauss^*(p₁(γ)²), [V]⟩ = N.normalP1Sq`

See the docstring of `Work.ThomBordism.gauss_p1Sq_pairing` below; the plan is in
`Submission/Work/ThomBordism/TUBEDATA_NOTES.md` (session-8 addendum, step 7).
-/

open Work.Cohomology Work.Thom Work.TangentClasses

namespace Work.ThomBordism

noncomputable section

/-- **Invariance of the Pontryagin classes under a bundle isomorphism** (same base, same model
fibre). -/
theorem pontryaginClass_eq_of_bundleIso {B : Type} [TopologicalSpace B] {k i : ℕ}
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin k)) ι')
    (e : BundleIso Z Z') :
    Work.Thom.pontryaginClass i Z = Work.Thom.pontryaginClass i Z' := by
  unfold Work.Thom.pontryaginClass
  rw [Work.Agree.chernClass_complexificationCore_eq rfl Z Z' e (2 * i)]

/-- **Invariance of `p₁` under a bundle isomorphism.** -/
theorem pontryagin1_eq_of_bundleIso {B : Type} [TopologicalSpace B] {k : ℕ}
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin k)) ι')
    (e : BundleIso Z Z') :
    Work.Thom.pontryagin1 Z = Work.Thom.pontryagin1 Z' := by
  rw [← Work.Thom.pontryaginClass_one Z, ← Work.Thom.pontryaginClass_one Z']
  exact pontryaginClass_eq_of_bundleIso Z Z' e

/-- **The pullback of `p₁(γ)²` is the square of the pullback of `p₁(γ)`.** -/
theorem p1Sq_comap {B : Type} [TopologicalSpace B] {k m : ℕ} (gauss : C(B, Grassmann.OG k m)) :
    (CohMap gauss ℤ 8).hom (Grassmann.p1Sq k m)
      = cupH' ℤ (TopCat.toSSet.obj (TopCat.of B)) 4 4
          ((CohMap gauss ℤ 4).hom (Grassmann.p1 k m))
          ((CohMap gauss ℤ 4).hom (Grassmann.p1 k m)) := by
  rw [Grassmann.p1Sq]
  exact Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom gauss) 4 4
    (Grassmann.p1 k m) (Grassmann.p1 k m)

/-- **The pullback of `p₂(γ)` is the `p₂` of the pulled-back bundle.** -/
theorem p2_comap {B : Type} [TopologicalSpace B] {k m : ℕ} (gauss : C(B, Grassmann.OG k m)) :
    (CohMap gauss ℤ 8).hom (Grassmann.p2 k m)
      = Work.Thom.pontryaginClass 2
          (Work.Thom.bundleComap (Grassmann.tautologicalBundle k m) gauss) :=
  (Work.Thom.pontryaginClass_comap (i := 2) (Grassmann.tautologicalBundle k m) gauss).symm

/-- **The pullback of `p₁(γ)` is the `p₁` of the pulled-back bundle.** -/
theorem p1_comap {B : Type} [TopologicalSpace B] {k m : ℕ} (gauss : C(B, Grassmann.OG k m)) :
    (CohMap gauss ℤ 4).hom (Grassmann.p1 k m)
      = Work.Thom.pontryagin1
          (Work.Thom.bundleComap (Grassmann.tautologicalBundle k m) gauss) := by
  rw [← Work.Thom.pontryaginClass_one
    (Work.Thom.bundleComap (Grassmann.tautologicalBundle k m) gauss)]
  exact (Work.Thom.pontryaginClass_comap (i := 1)
    (Grassmann.tautologicalBundle k m) gauss).symm

/-- **The number step for `p₁²`**: the pairing of `gauss^*(p₁(γ)²)` with the fundamental class is
the normal `p₁²`-number of the prescribed normal-bundle datum.

The chain is `gauss^*(p₁(γ)²) = gauss^*(p₁(γ)) ⌣ gauss^*(p₁(γ)) = p₁(ν) ⌣ p₁(ν)` (the pullback of
a cup product, then the pullback of `p₁(γ)` and invariance of `p₁` under the classifying bundle
isomorphism `e`), and `⟨p₁(ν) ⌣ p₁(ν), [V]⟩ = N.normalP1Sq` is
`Work.ThomBordism.normalBundle_pontryaginNumbers`. -/
theorem gauss_p1Sq_pairing {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : PontryaginThom.EmbeddingData V (8 + k))
    (ND : PontryaginThom.NormalData V k E.e)
    (gauss : C(V.pt, Grassmann.OG k 10))
    (e : Work.Thom.BundleIso
      (Work.Thom.bundleComap (Grassmann.tautologicalBundle k 10) gauss)
      (Work.Tubular.normalBundle E ND))
    (N : PontryaginThom.NormalBundlData V) :
    kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((CohMap gauss ℤ 8).hom (Grassmann.p1Sq k 10)) V.c = N.normalP1Sq := by
  rw [p1Sq_comap gauss]
  have h1 : (CohMap gauss ℤ 4).hom (Grassmann.p1 k 10)
      = Work.Thom.pontryagin1 (Work.Tubular.normalBundle E ND) := by
    rw [p1_comap gauss]
    exact pontryagin1_eq_of_bundleIso _ _ e
  rw [h1]
  exact (Work.ThomBordism.normalBundle_pontryaginNumbers E ND N).1

/-- **The number step for `p₂`**: the pairing of `gauss^*(p₂(γ))` with the fundamental class is the
normal `p₂`-number of the prescribed normal-bundle datum. -/
theorem gauss_p2_pairing {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : PontryaginThom.EmbeddingData V (8 + k))
    (ND : PontryaginThom.NormalData V k E.e)
    (gauss : C(V.pt, Grassmann.OG k 10))
    (e : Work.Thom.BundleIso
      (Work.Thom.bundleComap (Grassmann.tautologicalBundle k 10) gauss)
      (Work.Tubular.normalBundle E ND))
    (N : PontryaginThom.NormalBundlData V) :
    kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((CohMap gauss ℤ 8).hom (Grassmann.p2 k 10)) V.c = N.normalP2 := by
  rw [p2_comap gauss]
  rw [pontryaginClass_eq_of_bundleIso _ _ e]
  exact (Work.ThomBordism.normalBundle_pontryaginNumbers E ND N).2

end

end Work.ThomBordism
