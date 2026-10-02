import Mathlib
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.ProjIsoOfBundleIso
import Submission.Work.LerayHirsch.tautLine_bundleIso_of_projIso
import Submission.Work.Thom.chernClass_homeo
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Thom.localThom_union

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Leray–Hirsch is invariant under an isomorphism of bundles

An isomorphism `e : BundleIso Z Z'` of two complex gluing-data bundles over a common base induces a
homeomorphism `Φ = projIsoMap Z Z' e : P(Z) ≃ₜ P(Z')` of the projectivisations
(`Submission/Work/LerayHirsch/ProjIsoOfBundleIso.lean`), which is compatible with the projections
to the base (`projMap_projIsoMap`) and—because the tautological line bundle is natural
(`Submission/Work/LerayHirsch/tautLine_bundleIso_of_projIso.lean`) and the Chern classes are
isomorphism-invariant (`Work.Thom.chernClass_homeo`)—carries `ζ_{Z'}` to `ζ_Z`.

The Leray–Hirsch decomposition maps are built from `π^*` and the powers of `ζ`, so they are
intertwined by `Φ^*`; since `Φ^*` is bijective, `LerayHirschFull Z ↔ LerayHirschFull Z'`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι ι' : Type} {m : ℕ}

/-! ## `ζ`-compatibility -/

/-- **The induced homeomorphism carries `ζ_{Z'}` to `ζ_Z`**: the pullback of the hyperplane class
of `P(Z')` along `P(e)` is the hyperplane class of `P(Z)`. -/
theorem zeta_projIso_of_bundleIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') [Fintype ι] [Fintype ι']
    (e : BundleIso Z Z') (Φ : ProjSpace Z ≃ₜ ProjSpace Z')
    (hΦ : ⇑Φ = ⇑(projIsoMap Z Z' e)) :
    (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ 2).hom (zeta Z') = zeta Z := by
  obtain ⟨e'⟩ := nonempty_tautLine_bundleIso_of_projIso Z Z' e
  have hmap : (Φ : C(ProjSpace Z, ProjSpace Z')) = projIsoMap Z Z' e :=
    ContinuousMap.ext (fun x => congrFun hΦ x)
  have e'' : BundleIso (tautLine Z)
      (bundleComap (tautLine Z') (Φ : C(ProjSpace Z, ProjSpace Z'))) := by
    rw [hmap]; exact e'
  have hc := chernClass_homeo (m := 1) (j := 1) Φ (tautLine Z) (tautLine Z') e''
  rw [zeta, zeta, cohTransport_rfl, cohTransport_rfl]
  exact hc

/-! ## Transfer of the Leray–Hirsch decomposition along a compatible homeomorphism -/

/-- **The powers of `ζ` are natural** under a homeomorphism of projectivisations compatible with
the hyperplane class. -/
theorem zetaPow_projIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') [Fintype ι] [Fintype ι']
    (Φ : ProjSpace Z ≃ₜ ProjSpace Z')
    (hζ : (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ 2).hom (zeta Z') = zeta Z) (i : ℕ) :
    (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * i)).hom (zetaPow Z' i) = zetaPow Z i := by
  induction i with
  | zero =>
    have h := Work.Whitney.cohTransport_CohMap (rfl : 0 = 2 * 0)
      (Φ : C(ProjSpace Z, ProjSpace Z'))
      (Work.Cohomology.oneH ℤ (Work.Whitney.ssB (ProjSpace Z')))
    rw [CohMap_oneH] at h
    rw [zetaPow_zero, zetaPow_zero]
    exact h
  | succ i ih =>
    rw [zetaPow_succ, zetaPow_succ, Work.Whitney.cupChern_CohMap, ih, hζ]

/-- **The even Leray–Hirsch summands are natural**. -/
theorem lhTerm_projIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') [Fintype ι] [Fintype ι']
    (Φ : ProjSpace Z ≃ₜ ProjSpace Z')
    (hπ : (projMap Z').comp (Φ : C(ProjSpace Z, ProjSpace Z')) = projMap Z)
    (hζ : (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ 2).hom (zeta Z') = zeta Z) (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * (k - (i : ℕ))) B) :
    (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * k)).hom (lhTerm Z' k i x)
      = lhTerm Z k i x := by
  rw [lhTerm_def, lhTerm_def, Work.Whitney.cohTransport_CohMap, Work.Whitney.cupChern_CohMap]
  congr 1
  rw [Work.Thom.CohMap_comp_apply (Φ : C(ProjSpace Z, ProjSpace Z')) (projMap Z') ℤ
    (2 * (k - (i : ℕ))) x, hπ, zetaPow_projIso Z Z' Φ hζ i]

/-- **Naturality of the degree transport** in the `cohTransportLM` form used by the summands of
`lhAny`/`lhTermOdd`. -/
theorem cohTransportLM_CohMap {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    {n n' : ℕ} (h : n = n') (f : C(B₁, B₂)) (x : Coh ℤ n B₂) :
    (CohMap f ℤ n').hom (Work.Thom.cohTransportLM h x)
      = Work.Thom.cohTransportLM h ((CohMap f ℤ n).hom x) :=
  Work.Whitney.cohTransport_CohMap h f x

/-- The defining equation of `Work.LerayHirsch.lhTermOdd` (there is no such lemma upstream). -/
theorem lhTermOdd_def' (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (k : ℕ) (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    lhTermOdd Z k i x = cohTransport (by omega)
      (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjSpace Z))
        (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ))
        ((CohMap (projMap Z) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x) (zetaPow Z i)) := rfl

/-- **The odd Leray–Hirsch summands are natural**. -/
theorem lhTermOdd_projIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') [Fintype ι] [Fintype ι']
    (Φ : ProjSpace Z ≃ₜ ProjSpace Z')
    (hπ : (projMap Z').comp (Φ : C(ProjSpace Z, ProjSpace Z')) = projMap Z)
    (hζ : (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ 2).hom (zeta Z') = zeta Z) (k : ℕ)
    (i : {i : Fin m // (i : ℕ) ≤ k}) (x : Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * k + 1)).hom (lhTermOdd Z' k i x)
      = lhTermOdd Z k i x := by
  rw [lhTermOdd_def', lhTermOdd_def']
  change (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * k + 1)).hom
      (Work.Thom.cohTransportLM (by omega : 2 * k + 1 - 2 * (i : ℕ) + 2 * (i : ℕ) = 2 * k + 1)
        (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjSpace Z'))
          (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ))
          ((CohMap (projMap Z') ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x) (zetaPow Z' i)))
    = Work.Thom.cohTransportLM (by omega : 2 * k + 1 - 2 * (i : ℕ) + 2 * (i : ℕ) = 2 * k + 1)
        (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (ProjSpace Z))
          (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ))
          ((CohMap (projMap Z) ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x) (zetaPow Z i))
  erw [cohTransportLM_CohMap]
  erw [Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom (Φ : C(ProjSpace Z, ProjSpace Z')))
      (2 * k + 1 - 2 * (i : ℕ)) (2 * (i : ℕ))
      ((CohMap (projMap Z') ℤ (2 * k + 1 - 2 * (i : ℕ))).hom x) (zetaPow Z' i)]
  erw [Work.Thom.CohMap_comp_apply (Φ : C(ProjSpace Z, ProjSpace Z')) (projMap Z') ℤ
    (2 * k + 1 - 2 * (i : ℕ)) x, hπ, zetaPow_projIso Z Z' Φ hζ i]

/-- **The Leray–Hirsch map is natural**. -/
theorem lhMap_projIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') [Fintype ι] [Fintype ι']
    (Φ : ProjSpace Z ≃ₜ ProjSpace Z')
    (hπ : (projMap Z').comp (Φ : C(ProjSpace Z, ProjSpace Z')) = projMap Z)
    (hζ : (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ 2).hom (zeta Z') = zeta Z) (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * (k - (i : ℕ))) B) :
    (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * k)).hom (lhMap Z' k xf)
      = lhMap Z k xf := by
  rw [lhMap_apply, lhMap_apply, map_sum]
  exact Finset.sum_congr rfl (fun i _ => lhTerm_projIso Z Z' Φ hπ hζ k i (xf i))

/-- **The odd Leray–Hirsch map is natural**. -/
theorem lhMapOdd_projIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') [Fintype ι] [Fintype ι']
    (Φ : ProjSpace Z ≃ₜ ProjSpace Z')
    (hπ : (projMap Z').comp (Φ : C(ProjSpace Z, ProjSpace Z')) = projMap Z)
    (hζ : (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ 2).hom (zeta Z') = zeta Z) (k : ℕ)
    (xf : (i : {i : Fin m // (i : ℕ) ≤ k}) → Coh ℤ (2 * k + 1 - 2 * (i : ℕ)) B) :
    (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * k + 1)).hom (lhMapOdd Z' k xf)
      = lhMapOdd Z k xf := by
  rw [lhMapOdd, lhMapOdd, map_sum]
  exact Finset.sum_congr rfl (fun i _ => lhTermOdd_projIso Z Z' Φ hπ hζ k i (xf i))

/-- **`LerayHirschFull` transfers along a homeomorphism of projectivisations** which is compatible
with the projections to the base and with the hyperplane class. -/
theorem lerayHirschFull_of_homeo (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι') [Fintype ι] [Fintype ι']
    (Φ : ProjSpace Z ≃ₜ ProjSpace Z')
    (hπ : (projMap Z').comp (Φ : C(ProjSpace Z, ProjSpace Z')) = projMap Z)
    (hζ : (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ 2).hom (zeta Z') = zeta Z) :
    LerayHirschFull Z ↔ LerayHirschFull Z' := by
  have hbij : ∀ n, Function.Bijective (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ n).hom :=
    fun n => Work.Cohomology.bijective_CohMap_homeomorph Φ n
  have heven : ∀ k, Function.Bijective (lhMap Z k) ↔ Function.Bijective (lhMap Z' k) := by
    intro k
    have hcomp : (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * k)).hom ∘ lhMap Z' k
        = lhMap Z k := funext (lhMap_projIso Z Z' Φ hπ hζ k)
    constructor
    · intro h
      have h' : Function.Bijective ((CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * k)).hom
          ∘ lhMap Z' k) := by rw [hcomp]; exact h
      exact (Function.Bijective.of_comp_iff' (hbij (2 * k)) (lhMap Z' k)).mp h'
    · intro h
      have h' : Function.Bijective ((CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * k)).hom
          ∘ lhMap Z' k) :=
        (Function.Bijective.of_comp_iff' (hbij (2 * k)) (lhMap Z' k)).mpr h
      rwa [hcomp] at h'
  have hodd : ∀ k, Function.Bijective (lhMapOdd Z k) ↔ Function.Bijective (lhMapOdd Z' k) := by
    intro k
    have hcomp : (CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * k + 1)).hom ∘ lhMapOdd Z' k
        = lhMapOdd Z k := funext (lhMapOdd_projIso Z Z' Φ hπ hζ k)
    constructor
    · intro h
      have h' : Function.Bijective ((CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * k + 1)).hom
          ∘ lhMapOdd Z' k) := by rw [hcomp]; exact h
      exact (Function.Bijective.of_comp_iff' (hbij (2 * k + 1)) (lhMapOdd Z' k)).mp h'
    · intro h
      have h' : Function.Bijective ((CohMap (Φ : C(ProjSpace Z, ProjSpace Z')) ℤ (2 * k + 1)).hom
          ∘ lhMapOdd Z' k) :=
        (Function.Bijective.of_comp_iff' (hbij (2 * k + 1)) (lhMapOdd Z' k)).mpr h
      rwa [hcomp] at h'
  constructor
  · intro h
    exact ⟨fun k => (heven k).mp (h.1 k), fun k => (hodd k).mp (h.2 k)⟩
  · intro h
    exact ⟨fun k => (heven k).mpr (h.1 k), fun k => (hodd k).mpr (h.2 k)⟩

/-! ## The main statement -/

theorem lerayHirschFull_of_bundleIso {B : Type} [TopologicalSpace B] {ι ι' : Type} [Fintype ι] [Fintype ι']
    {m : ℕ} {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι}
    {Z' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι'}
    (e : Work.Thom.BundleIso Z Z') :
    Work.LerayHirsch.LerayHirschFull Z ↔ Work.LerayHirsch.LerayHirschFull Z' := by
  obtain ⟨Φ, hΦ⟩ := exists_homeo_projSpace_of_bundleIso Z Z' e
  have hπ : (projMap Z').comp (Φ : C(ProjSpace Z, ProjSpace Z')) = projMap Z := by
    ext x
    show projMap Z' (Φ x) = projMap Z x
    rw [show Φ x = projIsoMap Z Z' e x from congrFun hΦ x]
    exact projMap_projIsoMap Z Z' e x
  exact lerayHirschFull_of_homeo Z Z' Φ hπ (zeta_projIso_of_bundleIso Z Z' e Φ hΦ)

end

end Work.LerayHirsch
