import Mathlib
import Submission.Work.ThomBordism.Transversality.TransverseSard.LocalRep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Conjugating a chart by a `C^∞` local diffeomorphism of the model space preserving `range I`

This is the `C^∞` (i.e. `n = ∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`) version of
`Work.PTGeometric.exists_chart_extend_of_openPartialHomeomorph_range` (which is stated for the
*analytic* order `⊤ : WithTop ℕ∞`).

`e` is a chart of a `C^∞` manifold `M` modelled on `I : ModelWithCorners ℝ E' H`, lying in the
maximal atlas and with `x ∈ e.source`.  `T` is an open partial homeomorphism of the model space
`E'` which is `C^∞` on its source with `C^∞` inverse on its target, and which preserves
`Set.range I` in both directions; `(e.extend I) x ∈ T.source`.

Then there is a chart `e'` of the maximal atlas at `x` whose extended version is
`T ∘ (e.extend I)`:

`∀ y ∈ e'.source, (e'.extend I) y = T ((e.extend I) y)`,

and in particular `(e.extend I) y ∈ T.source` on `e'.source`.

The chart is `e ≫ₕ ψ` where `ψ : OpenPartialHomeomorph H H` is defined by
`ψ h = I.symm (T (I h))`, `ψ.symm h = I.symm (T.symm (I h))`, with `ψ.source = I ⁻¹' T.source`
and `ψ.target = I ⁻¹' T.target`.  The hypotheses `hTmap`/`hTsmap` (applied at points of
`Set.range I`) are exactly what is needed to make `ψ` a well defined open partial homeomorphism;
on `range I` the map `I ∘ ψ ∘ I.symm` coincides with `T`, so the smoothness of `T` gives
`ψ ∈ contDiffGroupoid ∞ I`, and then `e ≫ₕ ψ` is in the maximal atlas.

The argument is identical to the analytic case, since `contDiffGroupoid n I` and the whole
pregroupoid machinery are generic in the order `n : ℕ∞ω`. -/

open scoped Manifold ContDiff Topology
open Set Function

namespace Work.PTGeometric

theorem exists_chart_extend_of_openPartialHomeomorph_range_smooth
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E' H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    {x : M} (hx : x ∈ e.source)
    {T : OpenPartialHomeomorph E' E'}
    (hT : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (T : E' → E') T.source)
    (hTs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (T.symm : E' → E') T.target)
    (hTmap : ∀ ⦃v : E'⦄, v ∈ T.source → v ∈ Set.range I → T v ∈ Set.range I)
    (hTsmap : ∀ ⦃v : E'⦄, v ∈ T.target → v ∈ Set.range I → T.symm v ∈ Set.range I)
    (hexT : (e.extend I) x ∈ T.source) :
    ∃ e' : OpenPartialHomeomorph M H,
      e' ∈ IsManifold.maximalAtlas I ((⊤ : ℕ∞) : WithTop ℕ∞) M ∧
      x ∈ e'.source ∧
      (∀ y ∈ e'.source, (e.extend I) y ∈ T.source ∧ (e'.extend I) y = T ((e.extend I) y)) := by
  have hmapI : ∀ h : H, I h ∈ T.source → T (I h) ∈ Set.range I :=
    fun h hh => hTmap hh (Set.mem_range_self h)
  have hmapIs : ∀ h : H, I h ∈ T.target → T.symm (I h) ∈ Set.range I :=
    fun h hh => hTsmap hh (Set.mem_range_self h)
  have hcont1 : ContinuousOn (fun h : H => I.symm (T (I h))) (I ⁻¹' T.source) := by
    have h1 : ContinuousOn (fun h : H => T (I h)) (I ⁻¹' T.source) :=
      T.continuousOn.comp (I.continuous.continuousOn.mono (subset_univ _)) (fun h hh => hh)
    exact I.continuous_symm.comp_continuousOn h1
  have hcont2 : ContinuousOn (fun h : H => I.symm (T.symm (I h))) (I ⁻¹' T.target) := by
    have h1 : ContinuousOn (fun h : H => T.symm (I h)) (I ⁻¹' T.target) :=
      T.continuousOn_symm.comp (I.continuous.continuousOn.mono (subset_univ _)) (fun h hh => hh)
    exact I.continuous_symm.comp_continuousOn h1
  let ψ : OpenPartialHomeomorph H H :=
    { toFun := fun h => I.symm (T (I h))
      invFun := fun h => I.symm (T.symm (I h))
      source := I ⁻¹' T.source
      target := I ⁻¹' T.target
      map_source' := fun h hh => by
        simp only [Set.mem_preimage] at hh ⊢
        rw [I.right_inv (hmapI h hh)]
        exact T.map_source hh
      map_target' := fun h hh => by
        simp only [Set.mem_preimage] at hh ⊢
        rw [I.right_inv (hmapIs h hh)]
        exact T.map_target hh
      left_inv' := fun h hh => by
        simp only [Set.mem_preimage] at hh
        rw [I.right_inv (hmapI h hh), T.left_inv hh, I.left_inv]
      right_inv' := fun h hh => by
        simp only [Set.mem_preimage] at hh
        rw [I.right_inv (hmapIs h hh), T.right_inv hh, I.left_inv]
      continuousOn_toFun := hcont1
      continuousOn_invFun := hcont2
      open_source := T.open_source.preimage I.continuous
      open_target := T.open_target.preimage I.continuous }
  have hψapply : ∀ h : H, ψ h = I.symm (T (I h)) := fun h => rfl
  have hψsymm : ∀ h : H, ψ.symm h = I.symm (T.symm (I h)) := fun h => rfl
  have hmem1 : ∀ v : E', v ∈ I.symm ⁻¹' ψ.source ∩ Set.range I → v ∈ T.source := by
    rintro v ⟨hv1, hv2⟩
    have : I.symm v ∈ I ⁻¹' T.source := hv1
    simp only [Set.mem_preimage] at this
    rwa [I.right_inv hv2] at this
  have hmem2 : ∀ v : E', v ∈ I.symm ⁻¹' ψ.symm.source ∩ Set.range I → v ∈ T.target := by
    rintro v ⟨hv1, hv2⟩
    have : I.symm v ∈ I ⁻¹' T.target := hv1
    simp only [Set.mem_preimage] at this
    rwa [I.right_inv hv2] at this
  have hψG : ψ ∈ contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) I := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    constructor
    · rw [contDiffPregroupoid]
      refine ContDiffOn.congr_mono hT ?_ ?_
      · intro v hv
        have hv' : v ∈ T.source := hmem1 v hv
        simp only [Function.comp_apply, hψapply, I.right_inv hv.2]
        rw [I.right_inv (hTmap hv' hv.2)]
      · intro v hv
        exact hmem1 v hv
    · rw [contDiffPregroupoid]
      refine ContDiffOn.congr_mono hTs ?_ ?_
      · intro v hv
        have hv' : v ∈ T.target := hmem2 v hv
        simp only [Function.comp_apply, hψsymm, I.right_inv hv.2]
        rw [I.right_inv (hTsmap hv' hv.2)]
      · intro v hv
        exact hmem2 v hv
  refine ⟨e ≫ₕ ψ, ?_, ?_, ?_⟩
  · rw [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff]
    intro e'' he''
    have he0 : e ∈ StructureGroupoid.maximalAtlas M
        (contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) I) := he
    obtain ⟨h1, h2⟩ := (mem_maximalAtlas_iff.mp he0) e'' he''
    constructor
    · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
      exact (contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) I).trans
        ((contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) I).symm hψG) h1
    · rw [← OpenPartialHomeomorph.trans_assoc]
      exact (contDiffGroupoid ((⊤ : ℕ∞) : WithTop ℕ∞) I).trans h2 hψG
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hx, hexT⟩
  · intro y hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hysrc : (e.extend I) y ∈ T.source := hy2
    refine ⟨hysrc, ?_⟩
    rw [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe]
    simp only [Function.comp_apply, OpenPartialHomeomorph.trans_apply, hψapply]
    exact I.right_inv (hTmap hy2 (Set.mem_range_self (e y)))

end Work.PTGeometric
