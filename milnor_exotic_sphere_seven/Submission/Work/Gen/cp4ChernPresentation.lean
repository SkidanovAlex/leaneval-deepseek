import Mathlib
import Submission.Work.Gen.CP4Smooth8
import Submission.Work.Gen.Euler
import Submission.Work.Gen.TangentPresentation
import Submission.Work.Agree.PlumbDefs
import Submission.Work.Thom.BundleIso_comap_exists
import Submission.Work.Gen.EulerToolkit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# Presentation independence of the Chern classes of `TℂP⁴`

`Work.Gen.cp4ChernPresentation`: the `j`-th Chern class of the complexified tangent bundle of `ℂP⁴`
computed in the **canonical four-step presentation** of `Submission/Work/Thom/manifoldP1.lean`
(`tangentBundle → mapFibre → reindex`) agrees with the `j`-th Chern class of the
**standard-chart presentation** `Work.Gen.stdTangentC 4` (`tangentBundle → reindex`).

The three inputs are:

* `Work.Gen.TangentPresentation` — independence of the choice of the finite chart cover (so the
  reindexing over `Work.Thom.chartCover` may be replaced by the standard cover `Work.Gen.stdChart 4`,
  the one appearing in `Work.Gen.stdTangentC`);
* `Work.Gen.mapFibre_reindex_eq` — `mapFibre` commutes with `reindex` (`rfl`);
* `Work.Gen.chernClass_complexificationCore_mapFibre` — the change of fibre
  `Work.Thom.modelLinearEquiv` does not change the Chern classes.  This is where the fact that the
  model space of `ℂP⁴` is *already* `EuclideanSpace ℝ (Fin 8)` enters: the `mapFibre` replaces the
  fibre `EuclideanSpace ℝ (Fin 8)` by the (equal, but not definitionally so) space
  `EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))))`, and the equality
  `finrank_euclideanSpace_fin` is used to compare the two ranks.  The mathematical input is
  isomorphism-invariance of the Chern classes (`Work.Thom.chernClass_BundleIso`) applied to the
  explicit gauge `cxTrans` of a self-equivalence of the fibre.

## The gauge of a change of fibre

For a real bundle `Z` with standard fibre `ℝ^k` and a continuous linear equivalence
`e : ℝ^k ≃L ℝ^k`, the complexifications of `Z.mapFibre e` and of `Z` are isomorphic: the transition
functions are `cxTrans (e g e⁻¹)` and `cxTrans g`, related by conjugation with `cxTrans e`.  The
gauge is built with `Work.Thom.nonempty_bundleIso_of_gauge`.
-/

namespace Work.Gen

open scoped Manifold

open Work.TangentClasses

noncomputable section

/-- `(cxTrans e⁻¹) ∘ (cxTrans e) = 1`: the complexification of the inverse is a left inverse of the
complexification. -/
lemma cxTrans_symm_comp (k : ℕ) (e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin k)) :
    (Work.Thom.cxTrans (e.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))).comp
      (Work.Thom.cxTrans (e : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))) = 1 := by
  rw [← Work.Thom.cxTrans_comp, ContinuousLinearEquiv.coe_symm_comp_coe]
  exact Work.Thom.cxTrans_one

/-- `(cxTrans e) ∘ (cxTrans e⁻¹) = 1`: the complexification of the inverse is a right inverse of the
complexification. -/
lemma cxTrans_comp_symm (k : ℕ) (e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin k)) :
    (Work.Thom.cxTrans (e : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))).comp
      (Work.Thom.cxTrans (e.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))) = 1 := by
  rw [← Work.Thom.cxTrans_comp, ContinuousLinearEquiv.coe_comp_coe_symm]
  exact Work.Thom.cxTrans_one

/-- **Change of fibre by a self-equivalence of the standard fibre does not change the Chern
classes.**  For a real bundle `Z` with standard fibre `EuclideanSpace ℝ (Fin k)` and a continuous
linear equivalence `e` of that fibre, the complexifications of `Z.mapFibre e` and `Z` are isomorphic
(the gauge `cxTrans e` of `Work.Thom.nonempty_bundleIso_of_gauge`), so by
`Work.Thom.chernClass_BundleIso` their Chern classes agree. -/
theorem complexificationCore_mapFibre_self {k : ℕ} {B : Type} [TopologicalSpace B] {ι : Type}
    [Fintype ι] (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin k)) (j : ℕ) :
    Work.Thom.chernClass k j (Work.Thom.complexificationCore (Z.mapFibre e))
      = Work.Thom.chernClass k j (Work.Thom.complexificationCore Z) := by
  have hss : ∀ w, (Work.Thom.cxTrans (e.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
      ((Work.Thom.cxTrans (e : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))) w) = w := by
    intro w
    rw [← ContinuousLinearMap.comp_apply, cxTrans_symm_comp]
    rfl
  have hss' : ∀ w, (Work.Thom.cxTrans (e : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))
      ((Work.Thom.cxTrans (e.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))) w) = w := by
    intro w
    rw [← ContinuousLinearMap.comp_apply, cxTrans_comp_symm]
    rfl
  have hmap : ∀ i j' b, (Work.Thom.complexificationCore (Z.mapFibre e)).coordChange i j' b =
      (Work.Thom.cxTrans e).comp (((Work.Thom.complexificationCore Z).coordChange i j' b).comp
        (Work.Thom.cxTrans (e.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))) := by
    intro i j' b
    show Work.Thom.cxTrans ((Z.mapFibre e).coordChange i j' b) = _
    rw [RealBundle.mapFibre_coordChange, Work.Thom.cxTrans_comp, Work.Thom.cxTrans_comp]
    ext v
    rfl
  have hbiso : Nonempty (Work.Thom.BundleIso
      (Work.Thom.complexificationCore (Z.mapFibre e)) (Work.Thom.complexificationCore Z)) := by
    refine Work.Thom.nonempty_bundleIso_of_gauge
      (Work.Thom.complexificationCore (Z.mapFibre e)) (Work.Thom.complexificationCore Z)
      (fun i t b => ((Work.Thom.complexificationCore Z).coordChange i t b).comp
        (Work.Thom.cxTrans (e.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k))))
      (fun i t b => (Work.Thom.cxTrans e).comp ((Work.Thom.complexificationCore Z).coordChange t i b))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · -- the gauge `b ↦ (coordChange i i' b) ∘ cxTrans e⁻¹` is continuous
      intro i i'
      have hc : ContinuousOn (fun b => (Work.Thom.complexificationCore Z).coordChange i i' b)
          ((Work.Thom.complexificationCore (Z.mapFibre e)).baseSet i ∩
            (Work.Thom.complexificationCore Z).baseSet i') :=
        ((Work.Thom.complexificationCore Z).continuousOn_coordChange i i').mono (fun b hb => hb)
      exact (ContinuousLinearMap.isBoundedLinearMap_comp_right
        (Work.Thom.cxTrans (e.symm : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))).continuous.comp_continuousOn hc
    · -- the inverse gauge `b ↦ cxTrans e ∘ (coordChange i' i b)` is continuous
      intro i i'
      have hc : ContinuousOn (fun b => (Work.Thom.complexificationCore Z).coordChange i' i b)
          ((Work.Thom.complexificationCore (Z.mapFibre e)).baseSet i ∩
            (Work.Thom.complexificationCore Z).baseSet i') :=
        ((Work.Thom.complexificationCore Z).continuousOn_coordChange i' i).mono (fun b hb => ⟨hb.2, hb.1⟩)
      exact (ContinuousLinearMap.isBoundedLinearMap_comp_left
        (Work.Thom.cxTrans (e : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)))).continuous.comp_continuousOn hc
    · -- change of target chart
      intro i t t' b h1 h2 h3
      apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply]
      rw [(Work.Thom.complexificationCore Z).coordChange_comp i t t' b ⟨⟨h1, h2⟩, h3⟩]
    · -- change of source chart
      intro i t i' b h1 h2 h3
      apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply]
      rw [hmap i' i b]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hss]
      rw [(Work.Thom.complexificationCore Z).coordChange_comp i' i t b ⟨⟨h2, h1⟩, h3⟩]
    · -- change of target chart, inverse gauge
      intro i t t' b h1 h2 h3
      apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply]
      rw [(Work.Thom.complexificationCore Z).coordChange_comp t' t i b ⟨⟨h3, h2⟩, h1⟩]
    · -- change of source chart, inverse gauge
      intro i t i' b h1 h2 h3
      apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.comp_apply]
      rw [hmap i i' b]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hss]
      rw [(Work.Thom.complexificationCore Z).coordChange_comp t i i' b ⟨⟨h3, h1⟩, h2⟩]
    · -- left inverse
      intro i i' b x hx
      simp only [ContinuousLinearMap.comp_apply]
      rw [(Work.Thom.complexificationCore Z).coordChange_comp i i' i b ⟨⟨hx.1, hx.2⟩, hx.1⟩]
      rw [(Work.Thom.complexificationCore Z).coordChange_self i b hx.1]
      simp only [hss']
    · -- right inverse
      intro i i' b y hx
      simp only [ContinuousLinearMap.comp_apply]
      simp only [hss]
      rw [(Work.Thom.complexificationCore Z).coordChange_comp i' i i' b ⟨⟨hx.2, hx.1⟩, hx.2⟩]
      exact (Work.Thom.complexificationCore Z).coordChange_self i' b hx.2 y
  obtain ⟨eiso⟩ := hbiso
  exact Work.Thom.chernClass_BundleIso _ _ eiso

/-- **Change of fibre by a continuous linear equivalence does not change the Chern classes**, in the
form in which `Work.Thom.modelLinearEquiv` is used: the model space `EuclideanSpace ℝ (Fin k)` is
replaced by `EuclideanSpace ℝ (Fin l)`, and the two ranks are identified by `h : l = k`. -/
theorem chernClass_complexificationCore_mapFibre {k l : ℕ} {B : Type} [TopologicalSpace B]
    {ι : Type} [Fintype ι] (h : l = k) (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin l)) (j : ℕ) :
    Work.Thom.chernClass l j (Work.Thom.complexificationCore (Z.mapFibre e))
      = Work.Thom.chernClass k j (Work.Thom.complexificationCore Z) := by
  subst h
  exact complexificationCore_mapFibre_self Z e j

/-- The change of fibre commutes with the reindexing of the cover. -/
theorem mapFibre_reindex_eq {B : Type} [TopologicalSpace B] {k : ℕ} {ι ι' : Type}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] EuclideanSpace ℝ (Fin k))
    (σ : ι' → ι) (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) :
    (Z.mapFibre e).reindex σ hσ = (Z.reindex σ hσ).mapFibre e := rfl

/-- **Presentation independence of the Chern classes of the complexified tangent bundle of `ℂP⁴`.**
The canonical four-step presentation `Work.Thom.complexifiedTangentBundleFinite` (over the finite
chart cover `Work.Thom.chartCover`) and the standard-chart presentation `Work.Gen.stdTangentC 4`
give the same `j`-th Chern class. -/
theorem cp4ChernPresentation (j : ℕ) :
    Work.Thom.chernClass (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) j
        (Work.Thom.complexifiedTangentBundleFinite
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 8))) (Work.Projective.CP 4))
      = Work.Thom.chernClass 8 j (Work.Gen.stdTangentC 4) := by
  change Work.Thom.chernClass (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) j
      (Work.Thom.complexificationCore
        (((Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
            (Work.Projective.CP 4)).mapFibre
          (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8)))).reindex
          (Work.Thom.chartCover (H := EuclideanSpace ℝ (Fin 8)) (M := Work.Projective.CP 4))
          (Work.Thom.chartCover_reindex_cover 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (Work.Projective.CP 4))))
      = Work.Thom.chernClass 8 j (Work.Gen.stdTangentC 4)
  -- the finite chart cover may be replaced by the standard cover of `Work.Gen.stdTangentC`
  rw [Work.Gen.TangentPresentation (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))) (M := Work.Projective.CP 4)
      (Work.Thom.chartCover (H := EuclideanSpace ℝ (Fin 8)) (M := Work.Projective.CP 4))
      (Work.Thom.chartCover_reindex_cover 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (Work.Projective.CP 4))
      (Work.Gen.stdChart 4) (Work.Gen.stdChart_covers 4) j]
  -- `mapFibre` commutes with `reindex`
  rw [show (((Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
            (Work.Projective.CP 4)).mapFibre
          (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8)))).reindex
          (Work.Gen.stdChart 4) (Work.Gen.stdChart_covers 4))
        = (((Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
            (Work.Projective.CP 4)).reindex (Work.Gen.stdChart 4)
          (Work.Gen.stdChart_covers 4)).mapFibre
          (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8)))) from rfl]
  -- the change of fibre `EuclideanSpace ℝ (Fin 8) → EuclideanSpace ℝ (Fin (finrank ℝ …))` does not
  -- change the Chern classes
  rw [chernClass_complexificationCore_mapFibre (finrank_euclideanSpace_fin)
      (((Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8))
            (Work.Projective.CP 4)).reindex (Work.Gen.stdChart 4)
          (Work.Gen.stdChart_covers 4)))
      (Work.Thom.modelLinearEquiv (E := EuclideanSpace ℝ (Fin 8))) j]
  rfl

end

end Work.Gen
