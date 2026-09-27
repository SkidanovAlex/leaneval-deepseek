import Mathlib
import Submission.Work.Drive.ManifoldParity.InterSetFlowDefs

/-!
# The flow setup of a tangential field on the intersection set, and a finite chart cover

* `interSetSetup`: the `FlowSetup` of the global flow of `V` acting on `interSet D N`, from the
  box-anchored invariance statement (`Work.Drive.ManifoldParity.boxMapsTo_flowV_interSet`).
* `exists_flowCover`: `interSet D N` is covered by finitely many `FlowChart` regions, with charts
  built from the transversality `htrans` (`Work.Drive.chartDiff_surjective_of_transverse` plus
  `Work.Drive.exists_domRestrict_surjective` for the index) and `Work.Drive.exists_flowChart_at`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Set Manifold

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **The flow setup of the tangential field `V` on the intersection set.** -/
def interSetSetup (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (V : Amb 4 → Amb 4) (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (hmapsTo : ∀ x ∈ interSet D N, ∀ t : ℝ,
      (∀ u ∈ Set.uIcc (0 : ℝ) t, flowV V hV hVs u x ∈ Submission.Drive.unitBox 4) →
      flowV V hV hVs t x ∈ interSet D N) : FlowSetup 4 where
  W := V
  Φ := flowV V hV hVs
  K := interSet D N
  zero := flowV_zero V hV hVs
  add := flowV_add V hV hVs
  deriv := flowV_deriv V hV hVs
  mapsTo := hmapsTo
  cont := hV.continuous

/-- **A finite chart cover of the intersection set.**  At every point `x` of `interSet D N` the
charted difference map has surjective derivative (`htrans`), so there is an index `i` for which it is
also surjective on `{v | v i = 0}` (`exists_domRestrict_surjective`), and then
`exists_flowChart_at` produces a chart of `K` at `x` whose region contains `x`.  Compactness of
`interSet D N` gives a finite subcover. -/
theorem exists_flowCover (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) (hN : ContMDiff (𝓡 3) (𝓡 4) Ctop N)
    (htrans : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (sqPart x) = N (cbPart x) →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) D (sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) N (cbPart x)).toLinearMap = ⊤)
    (V : Amb 4 → Amb 4) (hV : ContDiff ℝ Ctop V) (hVs : HasCompactSupport V)
    (hVtan : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (sqPart x) = N (cbPart x) → ∀ p : M,
      x ∈ chartRegion p D N → fderiv ℝ (chartDiff p D N) x (V x) = 0)
    (hVne : ∀ x : Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (sqPart x) = N (cbPart x) → V x ≠ 0)
    (hmapsTo : ∀ x ∈ interSet D N, ∀ t : ℝ,
      (∀ u ∈ Set.uIcc (0 : ℝ) t, flowV V hV hVs u x ∈ Submission.Drive.unitBox 4) →
      flowV V hV hVs t x ∈ interSet D N) :
    Nonempty (FlowCover (interSetSetup D N V hV hVs hmapsTo)) := by
  classical
  have hpoint (x : Amb 4) (hx : x ∈ interSet D N) :
      ∃ C : FlowChart V (interSet D N) x, x ∈ C.region := by
    have hbox : x ∈ Submission.Drive.unitBox 4 := hx.1
    have heq : D (sqPart x) = N (cbPart x) := hx.2
    have hxreg : x ∈ chartRegion (D (sqPart x)) D N := by
      rw [mem_chartRegion]
      exact ⟨mem_chart_source _ (D (sqPart x)),
        by rw [← heq]; exact mem_chart_source _ (D (sqPart x))⟩
    have hsurj : Function.Surjective (fderiv ℝ (chartDiff (D (sqPart x)) D N) x) :=
      chartDiff_surjective_of_transverse (D (sqPart x)) D N hD hN hxreg heq (htrans x hbox heq)
    obtain ⟨i, hi⟩ := exists_domRestrict_surjective hsurj
    obtain ⟨C, -, hCx⟩ := exists_flowChart_at hD hN hV.continuous hx hsurj
      (hVtan x hbox heq (D (sqPart x)) hxreg) (hVne x hbox heq) i hi
    exact ⟨C, hCx⟩
  let Cof : ∀ x : Amb 4, x ∈ interSet D N → FlowChart V (interSet D N) x :=
    fun x hx => Classical.choose (hpoint x hx)
  by_cases hne : (interSet D N).Nonempty
  · haveI : Nonempty {x : Amb 4 // x ∈ interSet D N} :=
      ⟨⟨hne.choose, hne.choose_spec⟩⟩
    obtain ⟨t, ht⟩ := (isCompact_interSet D N hD.continuous hN.continuous).elim_finite_subcover
      (fun x : {x : Amb 4 // x ∈ interSet D N} => (Cof x.1 x.2).region)
      (fun x => (Cof x.1 x.2).isOpen_region)
      (fun x hx => Set.mem_iUnion.mpr
        ⟨⟨x, hx⟩, Classical.choose_spec (hpoint x hx)⟩)
    have hcover : interSet D N ∩ Submission.Drive.unitBox 4 ⊆
        ⋃ j : {j : {x : Amb 4 // x ∈ interSet D N} // j ∈ t}, (Cof j.1.1 j.1.2).region := by
      intro y hy
      have h := ht hy.1
      simp only [Set.mem_iUnion] at h
      obtain ⟨i, hi, hyi⟩ := h
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hyi⟩
    let Cov : FlowCover (interSetSetup D N V hV hVs hmapsTo) :=
      { ι := {j : {x : Amb 4 // x ∈ interSet D N} // j ∈ t}, str := inferInstance,
        p := fun j => j.1.1, C := fun j => Cof j.1.1 j.1.2, cover := hcover }
    exact ⟨Cov⟩
  · let p0 : Fin 0 → Amb 4 := fun j => j.elim0
    have hcover : interSet D N ∩ Submission.Drive.unitBox 4 ⊆
        ⋃ j : Fin 0, (j.elim0 : FlowChart V (interSet D N) (p0 j)).region := by
      intro y hy
      exact absurd ⟨y, hy.1⟩ hne
    let Cov : FlowCover (interSetSetup D N V hV hVs hmapsTo) :=
      { ι := Fin 0, str := inferInstance, p := p0, C := fun j => j.elim0, cover := hcover }
    exact ⟨Cov⟩

end

end Work.Drive
