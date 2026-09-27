import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.homeomorph_isManifold

/-!
# Transparent model change of a charted space, and the smooth structure of `(0,∞) × ℝP³`

`Work.Drive.exists_chartedSpace_isManifold_of_homeomorph_contDiff`
(`Submission/Work/Drive/exists_chartedSpace_isManifold_cappingSpace.lean`) proves that a charted space
modelled on `E` can be re-charted on a `C^n`-diffeomorphic model space `E'`, but it returns the
resulting charted-space structure as an `∃`, so its charts are opaque and no smoothness statement about
a concrete map can be reduced to them.

This file gives the same construction as a **definition**, `chartedSpaceChangeModel φ` — the atlas is
the old atlas post-composed with `φ — together with the proof that it is a smooth structure
(`isManifold_changeModel`), so that smoothness in the new structure is a statement about the concrete
charts.  It then applies the construction to build the model space of the capping:

* `Work.Drive.halfLineProjectiveCharted` — the charted space structure on the product
  `(0,∞) × ℝP³` modelled on `ℝ⁴ = EuclideanSpace ℝ (Fin 4)`, obtained from the transparent projective
  structure `Work.Drive.projCharted 3` on `ℝP³`
  (`Submission/Work/Drive/projCharted.lean`), the structure on `(0,∞)` transported from `ℝ` along
  `exp : ℝ ≃ₜ (0,∞)`, the product structure, and the model change along the canonical linear
  homeomorphism `EuclideanSpace ℝ (Fin (1+3)) ≃ₜ EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)`;
* `Work.Drive.isManifold_halfLineProjectiveCharted` — it is a smooth (`C^∞`) `4`-manifold.

The capping space itself is then obtained by transporting this structure along the concrete
homeomorphism `CappingSpace ≃ₜ (0,∞) × ℝP³`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## Model change as a definition -/

/-- **Model change of a charted space along a homeomorphism of model spaces.**  Given a charted
space `M` over `E` and a homeomorphism `φ : E ≃ₜ E'`, the *push-forward* of the atlas of `M` along
`φ` (post-composing every chart with `φ`) is a charted space structure on `M` over `E'`. -/
@[instance_reducible]
def chartedSpaceChangeModel
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (φ : E ≃ₜ E') : ChartedSpace E' M :=
    { atlas := (fun e : OpenPartialHomeomorph M E => e.trans φ.toOpenPartialHomeomorph) '' atlas E M
      chartAt := fun x => (chartAt E x).trans φ.toOpenPartialHomeomorph
      mem_chart_source := fun x => by
        rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
        exact ⟨mem_chart_source E x, trivial⟩
      chart_mem_atlas := fun x => ⟨chartAt E x, chart_mem_atlas E x, rfl⟩ }

/-- **The pushed-forward structure is again a smooth structure.**  If `φ : E ≃ₜ E'` is `C^n` with
`C^n` inverse and `M` is a `C^n` manifold modelled on `E`, then `M` is a `C^n` manifold modelled on
`E'` for `chartedSpaceChangeModel φ`. -/
theorem isManifold_changeModel
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : WithTop ℕ∞}
    (φ : E ≃ₜ E') (hφ : ContDiff 𝕜 n (φ : E → E')) (hφ' : ContDiff 𝕜 n (φ.symm : E' → E))
    (hM : IsManifold (modelWithCornersSelf 𝕜 E) n M) :
    @IsManifold 𝕜 _ E' _ _ E' _ (modelWithCornersSelf 𝕜 E') n M _
      (chartedSpaceChangeModel (𝕜 := 𝕜) (M := M) φ) := by
  letI : ChartedSpace E' M := chartedSpaceChangeModel (𝕜 := 𝕜) (M := M) φ
  have hφh_app : ⇑(φ.toOpenPartialHomeomorph) = ⇑φ := Homeomorph.toOpenPartialHomeomorph_apply φ
  have hφh_symm_app : ⇑((φ.toOpenPartialHomeomorph).symm) = ⇑φ.symm :=
    Homeomorph.toOpenPartialHomeomorph_symm_apply φ
  -- the conjugated transition is `C^n` on the preimage of the source of the original transition
  have hconj : ∀ (t : OpenPartialHomeomorph E E) (s : Set E), ContDiffOn 𝕜 n (↑t) s →
      ContDiffOn 𝕜 n (↑(φ.toOpenPartialHomeomorph.symm ≫ₕ t ≫ₕ φ.toOpenPartialHomeomorph))
        (⇑φ.symm ⁻¹' s) := by
    intro t s ht
    have hmain : ContDiffOn 𝕜 n (fun x : E' => φ (t (φ.symm x))) (⇑φ.symm ⁻¹' s) :=
      hφ.contDiffOn.comp (ht.comp (hφ'.contDiffOn.mono (Set.subset_univ _)) (fun x hx => hx))
        (fun _ _ => Set.mem_univ _)
    exact hmain.congr (fun x hx => by
      simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hφh_app, hφh_symm_app])
  have htrans : ∀ (a b : OpenPartialHomeomorph M E), a ∈ atlas E M → b ∈ atlas E M →
      ContDiffOn 𝕜 n (↑(a.symm ≫ₕ b)) (a.symm ≫ₕ b).source ∧
      ContDiffOn 𝕜 n (↑(a.symm ≫ₕ b).symm) (a.symm ≫ₕ b).target := by
    intro a b ha hb
    have h2 : (a.symm ≫ₕ b) ∈ contDiffGroupoid n (modelWithCornersSelf 𝕜 E) := hM.compatible ha hb
    have h3 := mem_groupoid_of_pregroupoid.mp h2
    simp only [contDiffPregroupoid] at h3
    exact ⟨by simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
        Set.preimage_id, Set.inter_univ, Function.comp_def, id_eq] using h3.1,
      by simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
        Set.preimage_id, Set.inter_univ, Function.comp_def, id_eq] using h3.2⟩
  -- conjugation of a transition by the diffeomorphism is again `C^n`, with `C^n` inverse
  have key : ∀ (t : OpenPartialHomeomorph E E),
      ContDiffOn 𝕜 n (↑t) t.source → ContDiffOn 𝕜 n (↑t.symm) t.target →
      (φ.toOpenPartialHomeomorph.symm ≫ₕ t ≫ₕ φ.toOpenPartialHomeomorph)
        ∈ contDiffGroupoid n (modelWithCornersSelf 𝕜 E') := by
    intro t ht ht'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    simp only [contDiffPregroupoid]
    constructor
    · have hsrc : (φ.toOpenPartialHomeomorph.symm ≫ₕ t ≫ₕ φ.toOpenPartialHomeomorph).source
          = ⇑φ.symm ⁻¹' t.source := by
        simp only [OpenPartialHomeomorph.trans_source,
          Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_target,
          OpenPartialHomeomorph.symm_source, Set.univ_inter, Set.preimage_univ, Set.inter_univ,
          hφh_symm_app]
      simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
        Set.preimage_id, Set.inter_univ, Function.comp_def, id_eq, hsrc] using hconj t t.source ht
    · have htgt : (φ.toOpenPartialHomeomorph.symm ≫ₕ t ≫ₕ φ.toOpenPartialHomeomorph).target
          = ⇑φ.symm ⁻¹' t.target := by
        simp only [OpenPartialHomeomorph.trans_target,
          Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_target,
          OpenPartialHomeomorph.symm_target, Set.univ_inter, Set.preimage_univ, Set.inter_univ,
          hφh_symm_app]
      have hsym : (φ.toOpenPartialHomeomorph.symm ≫ₕ t ≫ₕ φ.toOpenPartialHomeomorph).symm
          = (φ.toOpenPartialHomeomorph.symm ≫ₕ t.symm) ≫ₕ φ.toOpenPartialHomeomorph := by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
          OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
      rw [hsym]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
        Set.preimage_id, Set.inter_univ, Function.comp_def, id_eq, htgt,
        OpenPartialHomeomorph.trans_assoc]
      exact hconj t.symm t.target ht'
  have hG : HasGroupoid M (contDiffGroupoid n (modelWithCornersSelf 𝕜 E')) := by
    refine ⟨fun {e e'} he he' => ?_⟩
    have he1 : e ∈
        (fun f : OpenPartialHomeomorph M E => f.trans φ.toOpenPartialHomeomorph) '' atlas E M := he
    have he2 : e' ∈
        (fun f : OpenPartialHomeomorph M E => f.trans φ.toOpenPartialHomeomorph) '' atlas E M := he'
    obtain ⟨a, ha, rfl⟩ := he1
    obtain ⟨b, hb, rfl⟩ := he2
    have heq : (a ≫ₕ φ.toOpenPartialHomeomorph).symm ≫ₕ (b ≫ₕ φ.toOpenPartialHomeomorph)
        = φ.toOpenPartialHomeomorph.symm ≫ₕ (a.symm ≫ₕ b) ≫ₕ φ.toOpenPartialHomeomorph := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
      simp only [OpenPartialHomeomorph.trans_assoc]
    rw [heq]
    exact key (a.symm ≫ₕ b) (htrans a b ha hb).1 (htrans a b ha hb).2
  exact IsManifold.mk' (modelWithCornersSelf 𝕜 E') n M (gr := hG)

/-! ## The model space `(0,∞) × ℝP³` of the capping, modelled on `ℝ⁴` -/

/-- The homeomorphism `exp : ℝ¹ ≃ₜ (0,∞)`, in the form of a homeomorphism of the model spaces of
the `1`-dimensional part. -/
def expHomeo : EuclideanSpace ℝ (Fin 1) ≃ₜ Set.Ioi (0 : ℝ) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).toHomeomorph.trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).toHomeomorph).trans Real.expOrderIso.toHomeomorph

/-- The canonical linear homeomorphism `ℝ¹ × ℝ³ ≃ₜ ℝ⁴` changing the model of the product
`(0,∞) × ℝP³` to `EuclideanSpace ℝ (Fin 4)`. -/
def psiEquiv : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)) ≃L[ℝ]
    EuclideanSpace ℝ (Fin 4) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 3)).symm

/-- **The transparent smooth structure on `(0,∞) × ℝP³` modelled on `ℝ⁴`.**  It is built from

* the transparent projective structure `Work.Drive.projCharted 3` on `ℝP³ = ℝP³`,
* the structure on `(0,∞)` transported from `ℝ¹` along the exponential homeomorphism,
* the product structure, and
* the model change along `psiEquiv`. -/
noncomputable def halfLineProjectiveCharted : ChartedSpace (EuclideanSpace ℝ (Fin 4))
    (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ)) :=
    Homeomorph.chartedSpace expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ))
      (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
  exact chartedSpaceChangeModel (𝕜 := ℝ) psiEquiv.toHomeomorph

/-- **`(0,∞) × ℝP³`, modelled on `ℝ⁴` by `halfLineProjectiveCharted`, is a smooth `4`-manifold.** -/
theorem isManifold_halfLineProjectiveCharted :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 4)) _ _ (EuclideanSpace ℝ (Fin 4)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
      halfLineProjectiveCharted := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  haveI h3 : IsManifold (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := isManifold_projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ)) :=
    Homeomorph.chartedSpace expHomeo
  haveI h1 : IsManifold (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞) (Set.Ioi (0 : ℝ)) :=
    homeomorph_isManifold expHomeo (𝓡 1)
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ))
      (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
  haveI hprod : IsManifold
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3)))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (Set.Ioi (0 : ℝ)) (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
  exact isManifold_changeModel (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
    (E' := EuclideanSpace ℝ (Fin 4)) (M := Set.Ioi (0 : ℝ) ×
      Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    psiEquiv.toHomeomorph psiEquiv.contDiff psiEquiv.symm.contDiff hprod

end

end Work.Drive
