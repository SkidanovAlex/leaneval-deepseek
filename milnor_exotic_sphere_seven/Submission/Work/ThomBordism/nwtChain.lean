import Mathlib
import Submission.Work.ThomBordism.nwtSplit
import Submission.Work.Agree.PlumbDefs
import Submission.Work.Agree.whitneySumRAssoc
import Submission.Work.Whitney.Basic
import Submission.Work.Tubular.totalSpace_mapFibre_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.TangentClasses Work.Thom
open Work.ThomBordism.Grassmann

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## The reindexing isomorphism -/

/-- `Work.TangentClasses.RealBundle.reindex` is `Work.Agree.reindexCore`. -/
theorem reindex_eq_reindexCore {ι ι' : Type} (Z : VectorBundleCore ℝ B F ι) (σ : ι' → ι)
    (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) :
    RealBundle.reindex Z σ hσ = Work.Agree.reindexCore Z σ hσ := rfl

/-- **A reindexing along a covering family is isomorphic to the original bundle.** -/
theorem nonempty_bundleIso_reindex {ι ι' : Type} (Z : VectorBundleCore ℝ B F ι) (σ : ι' → ι)
    (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) :
    Nonempty (BundleIso (RealBundle.reindex Z σ hσ) Z) := by
  obtain ⟨e⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self (𝕜 := ℝ) Z σ hσ
  exact ⟨(BundleIso.ofEq (reindex_eq_reindexCore Z σ hσ)).trans e⟩

/-! ## `whitneySumR` and the honest product sum -/

/-- **The Whitney sum `Work.Whitney.whitneySumR` is the product sum `RealBundle.sum` up to the
fibre splitting `Work.Whitney.sumFibreR`.** -/
theorem nonempty_bundleIso_whitneySumR_sum {ι₁ ι₂ : Type} {k₁ k₂ : ℕ}
    (Z₁ : VectorBundleCore ℝ B (Euc k₁) ι₁) (Z₂ : VectorBundleCore ℝ B (Euc k₂) ι₂) :
    Nonempty (BundleIso (Work.Whitney.whitneySumR Z₁ Z₂) (RealBundle.sum Z₁ Z₂)) := by
  have heq : Work.Whitney.whitneySumR Z₁ Z₂
      = RealBundle.mapFibre (Work.Whitney.sumFibreR k₁ k₂) (RealBundle.sum Z₁ Z₂) := by
    refine RealBundle.ext (by funext p; rfl) (by funext x; rfl) ?_
    intro p q x
    rw [Work.Whitney.whitneySumR_coordChange, RealBundle.mapFibre_coordChange,
      RealBundle.sum_coordChange]
  rw [heq]
  exact ⟨(Work.Tubular.bundleIsoMapFibre (Work.Whitney.sumFibreR k₁ k₂)
    (RealBundle.sum Z₁ Z₂)).symm⟩

/-! ## The orthonormal complement data is the normal bundle -/

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The orthonormal complement bundle is the normal bundle** with the fibre transported along
`Work.TangentClasses.RealBundle.mapFibre (eucToFun k)`. -/
theorem orthComplementData_toRealBundle_eq
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    (orthComplementData E ND).toRealBundle
      = RealBundle.mapFibre (EuclideanSpace.equiv (Fin k) ℝ) (Work.Tubular.normalBundle E ND) := by
  refine Work.Thom.bundleCore_ext ?_ ?_ ?_
  · funext i; rfl
  · funext x; rfl
  · intro i j x
    by_cases hx : x ∈ ND.D.baseSet i ∧ x ∈ ND.D.baseSet j
    · rw [ComplementData.toRealBundle_coordChange,
        ComplementData.coordChange_of_mem (D := orthComplementData E ND) i j x hx,
        RealBundle.mapFibre_coordChange, Work.Tubular.normalBundle_coordChange,
        Work.Tubular.transFun_of_mem E ND i j x hx]
      refine ContinuousLinearMap.ext fun v => ?_
      show complP E ND j x (complI E ND i x v)
        = eucToFun k (Work.Tubular.readCLM E ND j x
            (Work.Tubular.insCLM E ND i x (funToEuc k v)))
      rw [complI_apply_of_mem E ND i hx.1, complP_apply_of_mem E ND j hx.2,
        funToEuc_eucToFun]
    · rw [ComplementData.toRealBundle_coordChange,
        ComplementData.coordChange_of_notMem (D := orthComplementData E ND) i j x hx,
        RealBundle.mapFibre_coordChange, Work.Tubular.normalBundle_coordChange,
        Work.Tubular.transFun_of_notMem E ND i j x hx]
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero]

/-- **The normal bundle is isomorphic to the orthonormal complement bundle.** -/
theorem nonempty_bundleIso_normalBundle_orthComplementData
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Nonempty (BundleIso (Work.Tubular.normalBundle E ND) (orthComplementData E ND).toRealBundle) :=
  ⟨(Work.Tubular.bundleIsoMapFibre (EuclideanSpace.equiv (Fin k) ℝ)
      (Work.Tubular.normalBundle E ND)).trans
    (BundleIso.ofEq (orthComplementData_toRealBundle_eq E ND).symm)⟩

/-! ## The triviality of the sum -/

/-- **`Zt0 ⊕ normalBundle` is trivial.** -/
theorem nonempty_bundleIso_Zt0_sum_trivial (V : Work.ThomBordism.Man8) {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Nonempty (BundleIso
      (RealBundle.sum (Zt0 V) (Work.Tubular.normalBundle E ND))
      (RealBundle.trivial V.pt (Euc (8 + k)) Unit)) := by
  obtain ⟨e₁⟩ := nonempty_bundleIso_reindex (Work.TangentClasses.tangentBundle (𝓡 8) V.pt)
    (Work.Thom.chartCover (H := Euc 8) (M := V.pt))
    (fun x => by
      obtain ⟨i, hi⟩ := Work.Thom.chartCover_spec (H := Euc 8) (M := V.pt) x
      exact ⟨i, hi⟩)
  obtain ⟨e₂⟩ := nonempty_bundleIso_normalBundle_orthComplementData E ND
  obtain ⟨e₃⟩ := Work.Agree.sum_congr (Zt0 V) (Work.TangentClasses.tangentBundle (𝓡 8) V.pt)
    (Work.Tubular.normalBundle E ND) (orthComplementData E ND).toRealBundle e₁ e₂
  exact ⟨e₃.trans (Classical.choice (nonempty_bundleIso_tangent_sum_orthComplementData E ND))⟩

/-- **`whitneySumR Zt0 normalBundle` is trivial**, the form consumed by the `2`-torsion lemmas. -/
theorem nonempty_bundleIso_whitneySumR_Zt0_trivial (V : Work.ThomBordism.Man8) {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Nonempty (BundleIso (Work.Whitney.whitneySumR (Zt0 V) (Work.Tubular.normalBundle E ND))
      (RealBundle.trivial V.pt (Euc (8 + k)) Unit)) := by
  obtain ⟨e₁⟩ := nonempty_bundleIso_whitneySumR_sum (B := V.pt) (Zt0 V)
    (Work.Tubular.normalBundle E ND)
  exact ⟨e₁.trans (Classical.choice (nonempty_bundleIso_Zt0_sum_trivial V E ND))⟩

end

end Work.ThomBordism
