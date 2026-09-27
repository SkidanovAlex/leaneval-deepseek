import Mathlib
import Submission.Work.Drive.PushDisc.sheetModel

/-!
# The ranges of `d(Φ ∘ f)` at two points with a common image and transverse tangents

`Work.Drive.PushDisc.compRangeSupEqTop` is the range-level form of the chain rule used in the
"pushing a disc" step of the Whitney move: if `f : M → ℝ^{2(k+1)}` is a smooth map whose
derivatives at `p₁` and `p₂` have `f p₁ = f p₂` and whose tangent planes together span the whole
ambient space, and if `Φ : ℝ^{2(k+1)} → Mdl k` is a smooth map whose derivative at every point is
injective (hence, since the two spaces have the same finite dimension, an isomorphism), then the
two tangent planes of `Φ ∘ f` at `p₁`, `p₂` still span.

The proof is the chain rule `mfderiv_comp` (so that `mfderiv (Φ ∘ f) p` is
`fderiv Φ (f p) ∘ mfderiv f p`), the identification `range (g ∘ f) = map g (range f)` of linear
algebra, the fact that a linear map is surjective as soon as it is injective and the two
finite-dimensional spaces have equal dimension, and `map` commuting with `⊔`.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff

/-- **Linear algebra.** If `A : E →ₗ[ℝ] F` is injective and `E`, `F` are finite dimensional of the
same dimension, then `A` carries a spanning pair of subspaces to a spanning pair. -/
lemma map_sup_range_eq_top {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hfin : Module.finrank ℝ E = Module.finrank ℝ F)
    (A : E →ₗ[ℝ] F) (hA : Function.Injective A)
    (L₁ L₂ : Submodule ℝ E) (hspan : L₁ ⊔ L₂ = ⊤) :
    Submodule.map A L₁ ⊔ Submodule.map A L₂ = ⊤ := by
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hA
  rw [← Submodule.map_sup, hspan, Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]

theorem compRangeSupEqTop {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦinj : ∀ z : EuclideanSpace ℝ (Fin (2 * (k + 1))), Function.Injective (fderiv ℝ Φ z))
    (p₁ p₂ : M) (hp : f p₁ = f p₂)
    (htrans : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * (k + 1))))) f p₂).range = ⊤) :
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) p₂).range = ⊤ := by
  -- the chain rules
  have hchain₁ : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) p₁
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1)))))
          (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) Φ (f p₁)).comp
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1))))) f p₁) :=
    mfderiv_comp (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
      (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1)))))
      (I'' := modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) p₁ (f := f) (g := Φ)
      (hΦ.contMDiff.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  have hchain₂ : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) p₂
      = (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1)))))
          (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) Φ (f p₂)).comp
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1))))) f p₂) :=
    mfderiv_comp (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
      (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1)))))
      (I'' := modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) p₂ (f := f) (g := Φ)
      (hΦ.contMDiff.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))
  -- the ranges of the composites
  have hrange₁ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) p₁).range
      = Submodule.map ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1)))))
          (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) Φ (f p₁)).toLinearMap)
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1))))) f p₁).range := by
    rw [hchain₁]
    exact LinearMap.range_comp _ _
  have hrange₂ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (fun y : M => Φ (f y)) p₂).range
      = Submodule.map ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1)))))
          (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) Φ (f p₂)).toLinearMap)
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1))))) f p₂).range := by
    rw [hchain₂]
    exact LinearMap.range_comp _ _
  -- `Φ` has injective (hence, in equal finite dimension, surjective) derivative at `f p₂`
  have hFDE : FiniteDimensional ℝ
      (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1))))) (f p₂)) := by
    change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin (2*(k+1))))
    infer_instance
  have hFDF : FiniteDimensional ℝ
      (TangentSpace (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (Φ (f p₂))) := by
    change FiniteDimensional ℝ (Work.Drive.Whitney.Mdl k)
    infer_instance
  have hfin : Module.finrank ℝ
        (TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1))))) (f p₂))
      = Module.finrank ℝ
        (TangentSpace (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) (Φ (f p₂))) := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin (2*(k+1))))
      = Module.finrank ℝ (Work.Drive.Whitney.Mdl k)
    rw [finrank_euclideanSpace, finrank_Mdl, Fintype.card_fin]
  have hinj : Function.Injective
      ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1)))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) Φ (f p₂)).toLinearMap) := by
    rw [mfderiv_eq_fderiv]
    exact hΦinj (f p₂)
  -- assemble
  rw [hrange₁, hrange₂, hp]
  change Submodule.map ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1)))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) Φ (f p₂)).toLinearMap)
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1))))) f p₁).range ⊔
      Submodule.map ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1)))))
        (modelWithCornersSelf ℝ (Work.Drive.Whitney.Mdl k)) Φ (f p₂)).toLinearMap)
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k+1))))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2*(k+1))))) f p₂).range = ⊤
  exact map_sup_range_eq_top hfin _ hinj _ _ htrans

end Work.Drive.PushDisc
