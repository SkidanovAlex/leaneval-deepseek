import Mathlib
import Submission.Work.Gen.DualLineCore
import Submission.Work.Gen.tensorLine_c1_additive
import Submission.Work.Gen.chernClass_tensorLine_of_nowhereZeroSection
import Submission.Work.Thom.trivialChern

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The first Chern class of the dual of a complex line bundle

For a complex line bundle `L` (gluing data over a cover `ι`) the dual bundle
`Work.Gen.dualLineCore L` has transition functions the *reciprocals* of those of `L`
(`Work.Gen.dualLineCore_coordChange`), so `L ⊗ L*` has trivial transition functions and is therefore
isomorphic to the trivial line bundle.  Writing `c₁ = Work.Thom.chernClass 1 1`, additivity of `c₁`
under the tensor product (`Work.Gen.tensorLine_c1_additive`) and the vanishing of `c₁` of a trivial
bundle (`Work.Thom.chernClass_trivial`) give

  `c₁(L ⊗ L*) = c₁(L) + c₁(L*) = 0`,  hence  `c₁(L*) = - c₁(L)`.

The bundle isomorphism `L ⊗ L* ≅ ε` is produced by
`Work.Thom.nonempty_bundleIso_of_gauge` with the gauge

  `Φ u t b = scl (L.coordChange u.1 u.2 b) • id`   (`u` the index of the product cover `ι × ι`),

whose compatibility with the transition functions of `L ⊗ L*` is exactly the cocycle identity
`scl (L.coordChange i j b) * scl (L.coordChange j k b) = scl (L.coordChange i k b)` in the form
`Work.Gen.scl_cc_comp`.  The trivial bundle is taken over the one-element cover `Unit`, so no
`Inhabited ι` (or `Nonempty B`) hypothesis is needed.
-/

open Work.TangentClasses

namespace Work.Gen

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## The scalars of the transition functions -/

/-- **The scalar of a transition function of a complex line bundle never vanishes** on the overlap
of its two base sets. -/
theorem scl_cc_ne_zero {ι : Type} (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (i j : ι) (b : B) (hi : b ∈ L.baseSet i) (hj : b ∈ L.baseSet j) :
    scl (L.coordChange i j b) ≠ 0 := by
  intro h
  have h1 := scl_cc_recip L i j b hi hj
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

/-! ## The tensor product with the dual, explicitly -/

/-- The base sets of `L ⊗ L*` are the intersections of the base sets of `L`. -/
theorem tensorLine_dual_baseSet {ι : Type}
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (u : ι × ι) :
    (tensorLine L (dualLineCore L)).baseSet u = L.baseSet u.1 ∩ L.baseSet u.2 := by
  rw [tensorLine_baseSet, dualLineCore_baseSet]

/-- The transition function of `L ⊗ L*` is multiplication by
`scl (L.coordChange u.1 u'.1 b) * scl (L.coordChange u'.2 u.2 b)`. -/
theorem tensorLine_dual_coordChange {ι : Type}
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (u u' : ι × ι) (b : B) :
    (tensorLine L (dualLineCore L)).coordChange u u' b
      = (scl (L.coordChange u.1 u'.1 b) * scl (L.coordChange u'.2 u.2 b)) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  rw [tensorLine_coordChange, dualLineCore_coordChange]

/-! ## `L ⊗ L*` is trivial -/

/-- **`L ⊗ L* ≅ ε`**: the tensor product of a complex line bundle with its dual is trivial. -/
theorem nonempty_bundleIso_tensorLine_dual_trivial {ι : Type}
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Nonempty (Work.Thom.BundleIso (tensorLine L (dualLineCore L))
      (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) Unit)) := by
  refine Work.Thom.nonempty_bundleIso_of_gauge
    (tensorLine L (dualLineCore L))
    (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) Unit)
    (fun u (_ : Unit) b => scl (L.coordChange u.1 u.2 b) •
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
    (fun u (_ : Unit) b => (scl (L.coordChange u.1 u.2 b))⁻¹ •
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- continuity of the gauge
    intro u t
    rw [tensorLine_baseSet, dualLineCore_baseSet, trivialCore_baseSet, Set.inter_univ]
    exact (continuous_scl.comp_continuousOn (L.continuousOn_coordChange u.1 u.2)).smul
      (continuousOn_const :
        ContinuousOn (fun _ : B => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) _)
  · -- continuity of the inverse gauge
    intro u t
    rw [tensorLine_baseSet, dualLineCore_baseSet, trivialCore_baseSet, Set.inter_univ]
    exact (((continuous_scl.comp_continuousOn (L.continuousOn_coordChange u.1 u.2)).inv₀
      (fun b hb => by
        simp only [Function.comp_apply] at hb ⊢
        exact scl_cc_ne_zero L u.1 u.2 b hb.1 hb.2))).smul
      (continuousOn_const :
        ContinuousOn (fun _ : B => ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) _)
  · -- the target cocycle of the trivial bundle is trivial
    intro u t t' b hu ht ht'
    rw [trivialCore_coordChange,
      show (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) =
        ContinuousLinearMap.id ℂ _ from rfl,
      ContinuousLinearMap.id_comp]
  · -- compatibility with the source transition functions
    intro u t u' b hu hu' ht
    rw [tensorLine_dual_baseSet] at hu hu'
    have h1 : scl (L.coordChange u'.1 u'.2 b)
        = scl (L.coordChange u'.1 u.1 b) * scl (L.coordChange u.1 u'.2 b) :=
      scl_cc_comp L u'.1 u.1 u'.2 b ⟨⟨hu'.1, hu.1⟩, hu'.2⟩
    have h2 : scl (L.coordChange u.1 u'.2 b)
        = scl (L.coordChange u.1 u.2 b) * scl (L.coordChange u.2 u'.2 b) :=
      scl_cc_comp L u.1 u.2 u'.2 b ⟨⟨hu.1, hu.2⟩, hu'.2⟩
    rw [tensorLine_dual_coordChange, comp_smul_id, h1, h2]
    congr 1
    ring
  · -- the inverse target cocycle of the trivial bundle is trivial
    intro u t t' b hu ht ht'
    rw [trivialCore_coordChange,
      show (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) =
        ContinuousLinearMap.id ℂ _ from rfl,
      ContinuousLinearMap.comp_id]
  · -- compatibility with the inverse source transition functions
    intro u t u' b hu hu' ht
    rw [tensorLine_dual_baseSet] at hu hu'
    have h1 : (scl (L.coordChange u.1 u.2 b))⁻¹ = scl (L.coordChange u.2 u.1 b) :=
      scl_cc_inv L u.1 u.2 b hu.1 hu.2
    have h2 : (scl (L.coordChange u'.1 u'.2 b))⁻¹ = scl (L.coordChange u'.2 u'.1 b) :=
      scl_cc_inv L u'.1 u'.2 b hu'.1 hu'.2
    have h3 : scl (L.coordChange u'.2 u'.1 b)
        = scl (L.coordChange u'.2 u.2 b) * scl (L.coordChange u.2 u'.1 b) :=
      scl_cc_comp L u'.2 u.2 u'.1 b ⟨⟨hu'.2, hu.2⟩, hu'.1⟩
    have h4 : scl (L.coordChange u.2 u'.1 b)
        = scl (L.coordChange u.2 u.1 b) * scl (L.coordChange u.1 u'.1 b) :=
      scl_cc_comp L u.2 u.1 u'.1 b ⟨⟨hu.2, hu.1⟩, hu'.1⟩
    rw [tensorLine_dual_coordChange, comp_smul_id, h1, h2, h3, h4]
    congr 1
    ring
  · -- the two gauges are mutually inverse
    intro u t b x hb
    rw [tensorLine_dual_baseSet, trivialCore_baseSet, Set.inter_univ] at hb
    have hne : scl (L.coordChange u.1 u.2 b) ≠ 0 :=
      scl_cc_ne_zero L u.1 u.2 b hb.1 hb.2
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    rw [inv_mul_cancel₀ hne, one_smul]
  · intro u t b y hb
    rw [tensorLine_dual_baseSet, trivialCore_baseSet, Set.inter_univ] at hb
    have hne : scl (L.coordChange u.1 u.2 b) ≠ 0 :=
      scl_cc_ne_zero L u.1 u.2 b hb.1 hb.2
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    rw [mul_inv_cancel₀ hne, one_smul]

/-! ## The first Chern class of the dual -/

theorem dualLineCore_c1_neg {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.Thom.chernClass 1 1 (Work.Gen.dualLineCore L) = - Work.Thom.chernClass 1 1 L := by
  obtain ⟨e⟩ := nonempty_bundleIso_tensorLine_dual_trivial (B := B) L
  have htriv : Work.Thom.chernClass 1 1 (tensorLine L (dualLineCore L)) = 0 := by
    rw [Work.Thom.chernClass_BundleIso (tensorLine L (dualLineCore L))
      (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) Unit) e]
    exact Work.Thom.chernClass_trivial (m := 1) (j := 1) (by norm_num)
  have h0 : Work.Thom.chernClass 1 1 L + Work.Thom.chernClass 1 1 (dualLineCore L) = 0 := by
    rw [← tensorLine_c1_additive L (dualLineCore L)]
    exact htriv
  exact eq_neg_of_add_eq_zero_right h0

end

end Work.Gen
