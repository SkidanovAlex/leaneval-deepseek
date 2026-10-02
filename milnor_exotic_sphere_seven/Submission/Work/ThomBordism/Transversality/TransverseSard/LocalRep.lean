import Mathlib
import Submission.Work.ThomBordism.Transversality.TransverseSard
import Submission.Work.ThomBordism.Transversality.Preimage.BoundaryCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local normal form of a submersion: the chart-level toolkit

This file collects the pieces of the missing Mathlib direction
"surjective derivative + smoothness implies `IsSubmersionAt`" that are already proved:

* `surjective_fderiv_of_eqOn` -- a projection form forces surjectivity of the derivative;
* `exists_interiorChart_restr` -- at an interior point a chart restricts to an interior chart with
  an open coordinate target;
* `exists_chart_extend_of_openPartialHomeomorph` -- conjugating a chart by a local diffeomorphism of
  the model space whose source and target lie in `interior (range I)`;
* `contDiffOn_localRep` -- the local representation of a global `C^infinity` map in a chart;
* `exists_localDiffeomorph_shift` -- the shifted Euclidean normal form of a submersion;
* `exists_chart_linear_rep` -- the chart-level core of the normal form;
* `isSubmersionAt_of_surjective_fderiv_localRep` -- the hard direction of the normal form.

They are used by `TransverseSard/regularValue_ae.lean` and may be imported by any other file of the
chapter (no cycle: this file does not depend on `regularValue_ae`).
-/

namespace Work.ThomBordism.Transversality.TransverseSard

open scoped Manifold ContDiff Topology
open MeasureTheory Set Function Filter

/-- **A projection form forces surjectivity of the derivative.**

`U ⊆ E₁` is open and `g : E₁ → E₂` satisfies, on all of `U`, the equation `B (g v) = (equ v).1`
where `B` is a `C^∞` partial diffeomorphism of `E₂`, `g` maps `U` into `B.source`, and
`equ : E₁ ≃L[ℝ] (E₂ × F)` is a continuous linear equivalence.  Then `fderiv ℝ g a` is surjective
at every `a ∈ U`.

This is the "easy direction" of the local normal form of submersions.  On `U` one has
`g = B.symm ∘ (fun v => (equ v).1)`, so at `a ∈ U` the chain rule gives
`fderiv ℝ g a = fderiv ℝ B.symm (B (g a)) ∘ (Prod.fst ∘ equ)`; the first factor is surjective
because `fderiv ℝ B.symm (B (g a)) ∘ fderiv ℝ B (g a) = id` (the chain rule applied to
`B.symm ∘ B =ᶠ id` near `g a`), and `Prod.fst ∘ equ` is surjective. -/
theorem surjective_fderiv_of_eqOn
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E₁} (hU : IsOpen U) {g : E₁ → E₂} {a : E₁} (ha : a ∈ U)
    {B : OpenPartialHomeomorph E₂ E₂}
    (hB : ContDiffOn ℝ ∞ (B : E₂ → E₂) B.source)
    (hBsymm : ContDiffOn ℝ ∞ (B.symm : E₂ → E₂) B.target)
    (hgB : Set.MapsTo g U B.source)
    {equ : E₁ ≃L[ℝ] (E₂ × F)}
    (hwritten : Set.EqOn (fun v => B (g v)) (fun v => (equ v).1) U) :
    Function.Surjective (fderiv ℝ g a) := by
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hga : g a ∈ B.source := hgB ha
  have hBa : B (g a) ∈ B.target := B.map_source hga
  have hBd : DifferentiableAt ℝ (B : E₂ → E₂) (g a) :=
    (hB.contDiffAt (B.open_source.mem_nhds hga)).differentiableAt hne
  have hBsd : DifferentiableAt ℝ (B.symm : E₂ → E₂) (B (g a)) :=
    (hBsymm.contDiffAt (B.open_target.mem_nhds hBa)).differentiableAt hne
  have hwr : ∀ v ∈ U, B (g v) = (equ v).1 := fun v hv => by simpa using hwritten hv
  have heq : g =ᶠ[𝓝 a] (fun v => B.symm ((equ v).1)) := by
    filter_upwards [hU.mem_nhds ha] with v hv
    rw [← hwr v hv, B.left_inv (hgB hv)]
  set φ : E₁ → E₂ := fun v => (equ v).1 with hφdef
  have hφa : φ a = B (g a) := (hwr a ha).symm
  have hφeq : φ = ⇑((ContinuousLinearMap.fst ℝ E₂ F).comp (equ : E₁ →L[ℝ] (E₂ × F))) := by
    funext v; rfl
  have hφd : DifferentiableAt ℝ φ a := by
    rw [hφeq]
    exact ((ContinuousLinearMap.fst ℝ E₂ F).comp (equ : E₁ →L[ℝ] (E₂ × F))).differentiableAt
  have hφf : fderiv ℝ φ a = (ContinuousLinearMap.fst ℝ E₂ F).comp (equ : E₁ →L[ℝ] (E₂ × F)) := by
    rw [hφeq, ContinuousLinearMap.fderiv]
  have hev : (B.symm : E₂ → E₂) ∘ (B : E₂ → E₂) =ᶠ[𝓝 (g a)] id := by
    filter_upwards [B.open_source.mem_nhds hga] with x hx
    exact B.left_inv hx
  have hkey : (fderiv ℝ (B.symm : E₂ → E₂) (B (g a))) ∘SL (fderiv ℝ (B : E₂ → E₂) (g a))
      = ContinuousLinearMap.id ℝ E₂ := by
    rw [← fderiv_comp (x := g a) hBsd hBd, hev.fderiv_eq]
    simp
  have hsurj1 : Function.Surjective (fderiv ℝ (B.symm : E₂ → E₂) (B (g a))) := by
    refine Function.Surjective.of_comp (g := ⇑(fderiv ℝ (B : E₂ → E₂) (g a))) ?_
    intro y
    exact ⟨y, by simpa using congrArg (fun (L : E₂ →L[ℝ] E₂) => L y) hkey⟩
  have hsurj2 : Function.Surjective (⇑((ContinuousLinearMap.fst ℝ E₂ F).comp
      (equ : E₁ →L[ℝ] (E₂ × F)))) := by
    intro y
    refine ⟨equ.symm (y, 0), ?_⟩
    simp
  have hBsd' : DifferentiableAt ℝ (fun v : E₂ => B.symm v) (φ a) := by
    rw [hφa]; simpa using hBsd
  have hchain : fderiv ℝ (fun v => B.symm (φ v)) a
      = (fderiv ℝ (B.symm : E₂ → E₂) (B (g a))) ∘SL (fderiv ℝ φ a) := by
    have := fderiv_comp (x := a) (f := φ) (g := fun v : E₂ => B.symm v) hBsd' hφd
    simpa [hφa, Function.comp_def] using this
  rw [heq.fderiv_eq, hchain, hφf]
  simpa only [ContinuousLinearMap.coe_comp, Function.comp_def] using hsurj1.comp hsurj2

/-- **An interior chart restricting a given one, with an open coordinate neighbourhood.**

`e` is a chart of the `C^∞` manifold `M` in the maximal atlas and `x ∈ e.source` is an interior
point of `M` (`x ∉ I.boundary M`).  Then there is a chart `e'` of the maximal atlas whose source
is a neighbourhood of `x` contained in `e.source`, on which `e'` agrees with `e`, all of whose
points are interior points of `M`, and which admits an open set `W ⊆ E'` (the model space) with
`(e'.extend I) x ∈ W ⊆ (e'.extend I).target` and `W ⊆ interior (range I)`. -/
theorem exists_interiorChart_restr
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E' H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (hxi : x ∉ I.boundary M) :
    ∃ (e' : OpenPartialHomeomorph M H) (W : Set E'),
      e' ∈ IsManifold.maximalAtlas I ∞ M ∧ x ∈ e'.source ∧ e'.source ⊆ e.source ∧
      (∀ y ∈ e'.source, e' y = e y) ∧
      (∀ y ∈ e'.source, y ∉ I.boundary M) ∧
      IsOpen W ∧ W ∈ nhds ((e'.extend I) x) ∧ W ⊆ (e'.extend I).target ∧
      W ⊆ interior (Set.range I) := by
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hxint : I.IsInteriorPoint x := (I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr hxi
  have hexT : (e.extend I) x ∈ interior (e.extend I).target :=
    (Work.ThomBordism.Transversality.Preimage.isInteriorPoint_iff_of_mem_maximalAtlas
      (I := I) hne he hx).mp hxint
  have hexR : (e.extend I) x ∈ interior (Set.range I) :=
    OpenPartialHomeomorph.interior_extend_target_subset_interior_range e hexT
  set W : Set E' := interior (Set.range I) ∩ interior ((e.extend I).target) with hWdef
  have hWopen : IsOpen W := by
    rw [hWdef]; exact isOpen_interior.inter isOpen_interior
  have hxW : (e.extend I) x ∈ W := by rw [hWdef]; exact ⟨hexR, hexT⟩
  have hWtgt : W ⊆ (e.extend I).target := by
    intro v hv; rw [hWdef] at hv; exact interior_subset hv.2
  have hWrng : W ⊆ interior (Set.range I) := by
    intro v hv; rw [hWdef] at hv; exact hv.1
  have hcont : ContinuousOn (e.extend I) e.source := by
    rw [← OpenPartialHomeomorph.extend_source (f := e) (I := I)]
    exact e.continuousOn_extend
  set s : Set M := e.source ∩ (e.extend I) ⁻¹' W with hsdef
  have hsopen : IsOpen s := by
    rw [hsdef]; exact hcont.isOpen_inter_preimage e.open_source hWopen
  have hxs : x ∈ s := by rw [hsdef]; exact ⟨hx, hxW⟩
  have hsub : s ⊆ e.source := by rw [hsdef]; exact inter_subset_left
  have hsW : ∀ y ∈ s, (e.extend I) y ∈ W := by
    intro y hy; rw [hsdef] at hy; exact hy.2
  set e' : OpenPartialHomeomorph M H := e.restr s with he'def
  have hsrc : e'.source = s := by
    rw [he'def, OpenPartialHomeomorph.restr_source, hsopen.interior_eq]
    exact Set.inter_eq_right.mpr hsub
  have hsub' : e'.source ⊆ e.source := by rw [hsrc]; exact hsub
  have happ : ∀ y : M, e' y = e y := by
    intro y; rw [he'def, OpenPartialHomeomorph.restr_apply]
  have hext : ∀ y : M, (e'.extend I) y = (e.extend I) y := by
    intro y
    rw [he'def, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe,
      Function.comp_apply, Function.comp_apply]
    rw [OpenPartialHomeomorph.restr_apply]
  have hmem : e' ∈ IsManifold.maximalAtlas I ∞ M := by
    rw [he'def]
    exact restr_mem_maximalAtlas (contDiffGroupoid (∞ : WithTop ℕ∞) I) he hsopen
  refine ⟨e', W, hmem, ?_, hsub', ?_, ?_, hWopen, ?_, ?_, hWrng⟩
  · rw [hsrc]; exact hxs
  · intro y hy; exact happ y
  · intro y hy
    rw [hsrc] at hy
    have hyT : (e.extend I) y ∈ interior (e.extend I).target := by
      have := hsW y hy; rw [hWdef] at this; exact this.2
    have hyint : I.IsInteriorPoint y :=
      (Work.ThomBordism.Transversality.Preimage.isInteriorPoint_iff_of_mem_maximalAtlas
        (I := I) hne he hy.1).mpr hyT
    exact fun hb => (I.isBoundaryPoint_iff_not_isInteriorPoint y).mp hb hyint
  · exact hWopen.mem_nhds (by rw [hext]; exact hxW)
  · intro v hv
    have hvT : v ∈ (e.extend I).target := hWtgt hv
    rw [OpenPartialHomeomorph.extend_target_eq_image_source] at hvT
    obtain ⟨y, hy, hyv⟩ := hvT
    have hys : y ∈ s := by
      rw [hsdef]
      refine ⟨hy, ?_⟩
      simp only [Set.mem_preimage]
      rw [hyv]
      exact hv
    have hy' : y ∈ e'.source := by rw [hsrc]; exact hys
    have hy'' : y ∈ (e'.extend I).source := by
      rw [OpenPartialHomeomorph.extend_source]; exact hy'
    have : (e'.extend I) y = v := by rw [hext, hyv]
    rw [← this]; exact (e'.extend I).map_source hy''

/-- **Conjugating a chart by a local diffeomorphism of the model space.**

`e` is a chart of the `C^∞` manifold `M` in the maximal atlas with `x ∈ e.source`, and `T` is an
open partial homeomorphism of the model space `E'` whose source and target lie in the *interior* of
`range I` and which is `C^∞` on its source with `C^∞` inverse on its target, and such that
`(e.extend I) x ∈ T.source`.  Then there is a chart `e'` of the maximal atlas at `x` whose extended
version is `T ∘ (e.extend I)`:

`∀ y ∈ e'.source, (e'.extend I) y = T ((e.extend I) y)`.

The chart is `e ≫ₕ ψ` where `ψ = I.symm ∘ T ∘ I` is a partial diffeomorphism of `H`; the condition
that `T.source ∪ T.target ⊆ interior (range I)` makes `ψ` well defined and open, and the condition
that `T` is `C^∞` makes `ψ` an element of `contDiffGroupoid ∞ I`, so that `e ≫ₕ ψ` lies in the
maximal atlas.

This is the "conjugation step" of the submersion normal form on a manifold: a source-chart change
in the model space has to be realised by a chart of `M`, and the only obstruction is that the
resulting chart must map *interior* points to *interior* points — whence the hypotheses. -/
theorem exists_chart_extend_of_openPartialHomeomorph
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E' H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source)
    {T : OpenPartialHomeomorph E' E'}
    (hT : ContDiffOn ℝ ∞ (T : E' → E') T.source)
    (hTs : ContDiffOn ℝ ∞ (T.symm : E' → E') T.target)
    (hTsrc : T.source ⊆ interior (Set.range I)) (hTtgt : T.target ⊆ interior (Set.range I))
    (hexT : (e.extend I) x ∈ T.source) :
    ∃ e' : OpenPartialHomeomorph M H, e' ∈ IsManifold.maximalAtlas I ∞ M ∧ x ∈ e'.source ∧
      (∀ y ∈ e'.source, (e'.extend I) y = T ((e.extend I) y)) := by
  have hTmap : ∀ ⦃v : E'⦄, v ∈ T.source → T v ∈ Set.range I :=
    fun v hv => interior_subset (hTtgt (T.map_source hv))
  have hTsmap : ∀ ⦃v : E'⦄, v ∈ T.target → T.symm v ∈ Set.range I :=
    fun v hv => interior_subset (hTsrc (T.map_target hv))
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
        rw [I.right_inv (hTmap hh)]
        exact T.map_source hh
      map_target' := fun h hh => by
        simp only [Set.mem_preimage] at hh ⊢
        rw [I.right_inv (hTsmap hh)]
        exact T.map_target hh
      left_inv' := fun h hh => by
        simp only [Set.mem_preimage] at hh
        rw [I.right_inv (hTmap hh), T.left_inv hh, I.left_inv]
      right_inv' := fun h hh => by
        simp only [Set.mem_preimage] at hh
        rw [I.right_inv (hTsmap hh), T.right_inv hh, I.left_inv]
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
  have hψG : ψ ∈ contDiffGroupoid ∞ I := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
    constructor
    · rw [contDiffPregroupoid]
      refine ContDiffOn.congr_mono hT ?_ ?_
      · intro v hv
        have hv' : v ∈ T.source := hmem1 v hv
        simp only [Function.comp_apply, hψapply, I.right_inv hv.2]
        rw [I.right_inv (hTmap hv')]
      · intro v hv
        exact hmem1 v hv
    · rw [contDiffPregroupoid]
      refine ContDiffOn.congr_mono hTs ?_ ?_
      · intro v hv
        have hv' : v ∈ T.target := hmem2 v hv
        simp only [Function.comp_apply, hψsymm, I.right_inv hv.2]
        rw [I.right_inv (hTsmap hv')]
      · intro v hv
        exact hmem2 v hv
  refine ⟨e ≫ₕ ψ, ?_, ?_, ?_⟩
  · rw [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff]
    intro e'' he''
    have he0 : e ∈ StructureGroupoid.maximalAtlas M (contDiffGroupoid ∞ I) := he
    obtain ⟨h1, h2⟩ := (mem_maximalAtlas_iff.mp he0) e'' he''
    constructor
    · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc]
      exact (contDiffGroupoid ∞ I).trans ((contDiffGroupoid ∞ I).symm hψG) h1
    · rw [← OpenPartialHomeomorph.trans_assoc]
      exact (contDiffGroupoid ∞ I).trans h2 hψG
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hx, hexT⟩
  · intro y hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe]
    simp only [Function.comp_apply, OpenPartialHomeomorph.trans_apply, hψapply]
    exact I.right_inv (hTmap hy2)

/-- **The local representation of a global `C^∞` map is genuinely `C^∞`.**

For `G : M → ℝ^k` and a chart `e` of the maximal atlas, the map `v ↦ G ((e.extend I).symm v)`
(the representation of `G` in the chart) is `C^∞` on the target `I '' e.target` of the chart.
For an *open* subset `V` of that target, `ContDiffOn ℝ ∞ · V` is equivalent to
`∀ m, ContDiffOn ℝ m · V` (by `contDiffOn_infty`), so this is genuine smoothness — unlike the
pointwise hypothesis `ContDiffAt ℝ ∞ · v`. -/
theorem contDiffOn_localRep
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E' H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {k : ℕ} {G : M → EuclideanSpace ℝ (Fin k)}
    (hG : ContMDiff I (𝓡 k) ∞ G) {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) :
    ContDiffOn ℝ ∞ (fun v => G ((e.extend I).symm v)) (I '' e.target) := by
  have h1 : ContMDiffOn 𝓘(ℝ, E') I ∞ (fun v => (e.extend I).symm v) (I '' e.target) :=
    contMDiffOn_extend_symm he
  have h2 : ContMDiffOn I (𝓡 k) ∞ G univ := fun x _ => hG x
  have h3 : ContMDiffOn 𝓘(ℝ, E') (𝓡 k) ∞ (fun v => G ((e.extend I).symm v)) (I '' e.target) :=
    h2.comp h1 (fun v _ => trivial)
  rwa [contMDiffOn_iff_contDiffOn] at h3

/-- **The shifted Euclidean normal form of a submersion (the missing Mathlib step).**

`F : E → ℝ^k` is `C^∞` on the open set `U ∋ a` with `F a = 0` and `L := fderiv ℝ F a` surjective
(`E` finite-dimensional).  Then there is a local diffeomorphism `T` of `E`, defined near `a`, with
`T a = a`, carrying the level sets of `F` to those of `L` up to the constant `L a`:

`∀ v` near `a`, `L (T v) = F v + L a`,

and `T` is `C^∞` on its source with `C^∞` inverse on its target.

Construction: with `σ : ℝ^k →L[ℝ] E` a right inverse of `L`, `T v := v + σ (F v + L a - L v)`
satisfies `L (T v) = F v + L a` identically, `T a = a` and `fderiv ℝ T a = 1`.

The shift `+ L a` matters: the chart conjugation
(`exists_chart_extend_of_openPartialHomeomorph`) needs `T`'s source and target to lie in the
*interior* of `range I`, and `0` need not be an interior point (half-space model). -/
theorem exists_localDiffeomorph_shift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {k : ℕ} {F : E → EuclideanSpace ℝ (Fin k)} {U : Set E} (hU : IsOpen U) {a : E} (ha : a ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hFa : F a = 0)
    (hsurj : Function.Surjective (fderiv ℝ F a)) :
    ∃ T : OpenPartialHomeomorph E E, a ∈ T.source ∧ T a = a ∧
      (∃ V : Set E, V ∈ 𝓝 a ∧ ∀ v ∈ V, fderiv ℝ F a (T v) = F v + fderiv ℝ F a a) ∧
      ContDiffOn ℝ ∞ (T : E → E) T.source ∧
      ContDiffOn ℝ ∞ (T.symm : E → E) T.target := by
  set L : E →L[ℝ] EuclideanSpace ℝ (Fin k) := fderiv ℝ F a with hL
  obtain ⟨σ, hσ⟩ := ContinuousLinearMap.exists_rightInverse_of_surjective L
    (LinearMap.range_eq_top.mpr hsurj)
  have hσ' : ∀ x : EuclideanSpace ℝ (Fin k), L (σ x) = x := by
    intro x
    have := congrArg (fun (g : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) => g x) hσ
    simpa using this
  set Tfun : E → E := fun v => v + σ (F v + L a - L v) with hTfun
  have hkey : ∀ v : E, L (Tfun v) = F v + L a := by
    intro v
    simp only [hTfun, map_add, hσ']
    abel
  have hFm : ∀ m : ℕ, ContDiffOn ℝ (m : ℕ∞ω) F U := fun m => (contDiffOn_infty.mp hF) m
  have hTfun_smooth : ∀ m : ℕ, ContDiffOn ℝ (m : ℕ∞ω) Tfun U := by
    intro m
    have h2 : ContDiffOn ℝ (m : ℕ∞ω) (fun v : E => σ (F v + L a - L v)) U := by fun_prop
    exact (contDiffOn_id.add h2).congr (fun v _ => rfl)
  have hFd : HasFDerivAt F L a := by
    rw [hL]
    exact ((hF.contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp)).hasFDerivAt
  have hdiff : HasFDerivAt Tfun (1 : E →L[ℝ] E) a := by
    have hin : HasFDerivAt (fun v : E => F v + L a - L v) (L - L) a :=
      (hFd.add_const (L a)).sub (L.hasFDerivAt : HasFDerivAt (fun v : E => L v) L a)
    have h2 : HasFDerivAt (fun v : E => σ (F v + L a - L v)) (σ.comp (L - L)) a :=
      σ.hasFDerivAt.comp a hin
    have h3 : HasFDerivAt (fun v : E => v + σ (F v + L a - L v))
        ((1 : E →L[ℝ] E) + σ.comp (L - L)) a :=
      (hasFDerivAt_id a).add h2
    simpa [hTfun] using h3
  have hca : ContDiffAt ℝ (1 : ℕ∞ω) Tfun a := (hTfun_smooth 1).contDiffAt (hU.mem_nhds ha)
  have hstrict : HasStrictFDerivAt Tfun (↑(1 : E ≃L[ℝ] E)) a :=
    hca.hasStrictFDerivAt' hdiff (by norm_num)
  let T₀ : OpenPartialHomeomorph E E := hstrict.toOpenPartialHomeomorph Tfun
  have hT₀coe : (T₀ : E → E) = Tfun := hstrict.toOpenPartialHomeomorph_coe
  have haT₀ : a ∈ T₀.source := hstrict.mem_toOpenPartialHomeomorph_source
  -- a ball inside `U` on which `fderiv ℝ Tfun` stays within distance `1` of the identity
  have hfderiv_cont : ContinuousOn (fderiv ℝ Tfun) U :=
    (contDiffOn_infty.mpr hTfun_smooth).continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hderiv_a : fderiv ℝ Tfun a = (1 : E →L[ℝ] E) := hdiff.fderiv
  have hev1 : ∀ᶠ v in 𝓝 a, ‖fderiv ℝ Tfun v - (1 : E →L[ℝ] E)‖ < 1 := by
    have hcont : ContinuousAt (fun v : E => fderiv ℝ Tfun v) a :=
      hfderiv_cont.continuousAt (hU.mem_nhds ha)
    have hcont' : ContinuousAt (fun v : E => ‖fderiv ℝ Tfun v - (1 : E →L[ℝ] E)‖) a :=
      (hcont.sub continuousAt_const).norm
    have h0 : ‖fderiv ℝ Tfun a - (1 : E →L[ℝ] E)‖ < 1 := by rw [hderiv_a]; simp
    exact hcont'.eventually (isOpen_Iio.mem_nhds h0)
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.mp hev1
  set B : Set E := Metric.ball a (min ε₁ ε₂) with hBdef
  have hBopen : IsOpen B := Metric.isOpen_ball
  have haB : a ∈ B := Metric.mem_ball_self (lt_min hε₁ hε₂)
  have hBU : B ⊆ U := fun v hv => hb₁ (Metric.ball_subset_ball (min_le_left _ _) hv)
  have hBd : ∀ v ∈ B, ‖fderiv ℝ Tfun v - (1 : E →L[ℝ] E)‖ < 1 :=
    fun v hv => hb₂ (Metric.ball_subset_ball (min_le_right _ _) hv)
  refine ⟨T₀.restr B, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restr_source, hBopen.interior_eq]
    exact ⟨haT₀, haB⟩
  · rw [OpenPartialHomeomorph.restr_apply, hT₀coe]
    simp only [hTfun, hFa, zero_add, sub_self, map_zero, add_zero]
  · refine ⟨B, hBopen.mem_nhds haB, ?_⟩
    intro v hv
    rw [OpenPartialHomeomorph.restr_apply, hT₀coe]
    exact hkey v
  · rw [OpenPartialHomeomorph.restr_apply, OpenPartialHomeomorph.restr_source,
      hBopen.interior_eq]
    exact (contDiffOn_infty.mpr hTfun_smooth).mono (fun v hv => hBU hv.2)
  · intro y hy
    have hsy : (T₀.restr B).symm y ∈ (T₀.restr B).source := (T₀.restr B).map_target hy
    rw [OpenPartialHomeomorph.restr_source, hBopen.interior_eq] at hsy
    have hsyB : (T₀.restr B).symm y ∈ B := hsy.2
    have hsyU : (T₀.restr B).symm y ∈ U := hBU hsyB
    have hlt : ‖fderiv ℝ Tfun ((T₀.restr B).symm y) - (1 : E →L[ℝ] E)‖ < 1 := hBd _ hsyB
    have hunit : IsUnit (fderiv ℝ Tfun ((T₀.restr B).symm y)) := by
      have hab : (1 : E →L[ℝ] E) - (1 - fderiv ℝ Tfun ((T₀.restr B).symm y))
          = fderiv ℝ Tfun ((T₀.restr B).symm y) := by abel
      rw [← hab]
      exact isUnit_one_sub_of_norm_lt_one (by simpa [norm_sub_rev] using hlt)
    set f₀' : E ≃L[ℝ] E := ContinuousLinearEquiv.unitsEquiv ℝ E hunit.unit with hf₀'
    have ueq : (f₀' : E →L[ℝ] E) = fderiv ℝ Tfun ((T₀.restr B).symm y) := by
      have h1 : (f₀' : E →L[ℝ] E) = (hunit.unit : E →L[ℝ] E) := by
        rw [hf₀']
        ext x
        simp
      rw [h1, IsUnit.unit_spec]
    have hd : HasFDerivAt (⇑(T₀.restr B)) (f₀' : E →L[ℝ] E) ((T₀.restr B).symm y) := by
      have h1 : HasFDerivAt Tfun (fderiv ℝ Tfun ((T₀.restr B).symm y)) ((T₀.restr B).symm y) :=
        (((contDiffOn_infty.mpr hTfun_smooth).contDiffAt (hU.mem_nhds hsyU)).differentiableAt
          (by norm_num)).hasFDerivAt
      have h2 : (⇑(T₀.restr B)) = Tfun := by
        rw [OpenPartialHomeomorph.restr_apply, hT₀coe]
      rw [h2, ueq]
      exact h1
    refine (OpenPartialHomeomorph.contDiffAt_symm (f := T₀.restr B) hy hd ?_).contDiffWithinAt
    have : ContDiffAt ℝ ∞ Tfun ((T₀.restr B).symm y) :=
      ((contDiffOn_infty.mpr hTfun_smooth).contDiffAt (hU.mem_nhds hsyU))
    rwa [OpenPartialHomeomorph.restr_apply, hT₀coe]

/-- **The chart-level core of the normal form of submersions on a manifold.**

`x` is an interior point of `M`, `e` a chart of the maximal atlas with `x ∈ e.source`, `f x = 0`,
and the representation `frep v = f ((e.extend I).symm v)` of `f` in that chart is `C^∞` on an open
`V ∋ (e.extend I) x`, with `L := fderiv ℝ frep ((e.extend I) x)` surjective.  Then there are a
chart `e'` of the maximal atlas and an open neighbourhood `S ∋ x` with `S ⊆ e'.source` on which the
representation of `f` in `e'` is the linear map `L` up to the constant `L ((e.extend I) x)`:

`∀ y ∈ S, f y = L ((e'.extend I) y) - L ((e.extend I) x)`.

Proof: `exists_localDiffeomorph_shift` gives `T` at `ex := (e.extend I) x` with `T ex = ex` and
`L (T v) = frep v + L ex` for `v` near `ex`; restrict `T` to a ball `B ∋ ex` with
`B ⊆ T.source ∩ interior (range I) ∩ W` and `T '' B ⊆ interior (range I)`, where `W` is the set on
which the normal form holds (`ex ∈ interior (range I)` because `x` is an interior point of `M`).
Then `T₀ := T.restr B` has `T₀.source ∪ T₀.target ⊆ interior (range I)` (the target via
`PartialEquiv.image_source_eq_target`), so the chart conjugation
`exists_chart_extend_of_openPartialHomeomorph` applies, producing `e'` with
`(e'.extend I) = T₀ ∘ (e.extend I)` on `e'.source`; finally cut down to
`S := e'.source ∩ (e.source ∩ (e.extend I) ⁻¹' B)`, on which the identity holds. -/
theorem exists_chart_linear_rep
    {k : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E' H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (hxi : x ∉ I.boundary M)
    {f : M → EuclideanSpace ℝ (Fin k)} (hfx : f x = 0)
    {V : Set E'} (hV : IsOpen V) (hVx : (e.extend I) x ∈ V) (hVsub : V ⊆ (e.extend I).target)
    (hf : ContDiffOn ℝ ∞ (fun v => f ((e.extend I).symm v)) V)
    (hsurj : Function.Surjective
      (fderiv ℝ (fun v => f ((e.extend I).symm v)) ((e.extend I) x))) :
    ∃ (e' : OpenPartialHomeomorph M H) (S : Set M),
      e' ∈ IsManifold.maximalAtlas I ∞ M ∧ x ∈ S ∧ IsOpen S ∧ S ⊆ e'.source ∧
      (∀ y ∈ S, f y = fderiv ℝ (fun v => f ((e.extend I).symm v)) ((e.extend I) x)
        ((e'.extend I) y) - fderiv ℝ (fun v => f ((e.extend I).symm v)) ((e.extend I) x)
        ((e.extend I) x)) := by
  set ex : E' := (e.extend I) x with hex_def
  set frep : E' → EuclideanSpace ℝ (Fin k) := fun v => f ((e.extend I).symm v) with hfrep_def
  have hfrep_ex : frep ex = 0 := by
    rw [hfrep_def, hex_def]
    simp only []
    rw [PartialEquiv.left_inv _ (by rw [OpenPartialHomeomorph.extend_source]; exact hx), hfx]
  have hsurj' : Function.Surjective (fderiv ℝ frep ex) := by
    rw [hfrep_def, hex_def]; exact hsurj
  obtain ⟨T, hTex, hTa, ⟨W, hWmem, hWT⟩, hTsm, hTsymm⟩ :=
    exists_localDiffeomorph_shift (F := frep) (U := V) (a := ex) hV
      (by rw [hex_def]; exact hVx) hf hfrep_ex hsurj'
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hex_int : ex ∈ interior (Set.range I) := by
    rw [hex_def]
    exact OpenPartialHomeomorph.interior_extend_target_subset_interior_range e
      ((Work.ThomBordism.Transversality.Preimage.isInteriorPoint_iff_of_mem_maximalAtlas
        (I := I) hne he hx).mp ((I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr hxi))
  have hTcont : ContinuousAt (fun v : E' => T v) ex :=
    T.continuousOn.continuousAt (T.open_source.mem_nhds hTex)
  have hU : (T.source ∩ interior (Set.range I) ∩ W ∩ T ⁻¹' interior (Set.range I)) ∈ 𝓝 ex :=
    inter_mem (inter_mem (inter_mem (T.open_source.mem_nhds hTex)
      (isOpen_interior.mem_nhds hex_int)) hWmem)
      (hTcont.preimage_mem_nhds (isOpen_interior.mem_nhds (by rw [hTa]; exact hex_int)))
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hU
  set B : Set E' := Metric.ball ex ε with hBdef
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hexB : ex ∈ B := Metric.mem_ball_self hεpos
  have hB1 : B ⊆ T.source := fun v hv => (hεsub hv).1.1.1
  have hB2 : B ⊆ interior (Set.range I) := fun v hv => (hεsub hv).1.1.2
  have hB3 : B ⊆ W := fun v hv => (hεsub hv).1.2
  have hB4 : ∀ v ∈ B, T v ∈ interior (Set.range I) := fun v hv => (hεsub hv).2
  have hT₀src : (T.restr B).source ⊆ interior (Set.range I) := by
    intro v hv
    rw [OpenPartialHomeomorph.restr_source, hBopen.interior_eq] at hv
    exact hB2 hv.2
  have hT₀tgt : (T.restr B).target ⊆ interior (Set.range I) := by
    intro y hy
    rw [← PartialEquiv.image_source_eq_target] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    rw [OpenPartialHomeomorph.restr_source, hBopen.interior_eq] at hv
    exact hB4 v hv.2
  have hT₀sm : ContDiffOn ℝ ∞ ((T.restr B) : E' → E') (T.restr B).source := by
    refine hTsm.mono ?_ |>.congr ?_
    · intro v hv
      rw [OpenPartialHomeomorph.restr_source, hBopen.interior_eq] at hv
      exact hB1 hv.2
    · intro v _; rfl
  have hT₀syms : ContDiffOn ℝ ∞ ((T.restr B).symm : E' → E') (T.restr B).target := by
    refine hTsymm.mono ?_ |>.congr ?_
    · intro v hv; exact hv.1
    · intro v _; rfl
  have hexT₀ : ex ∈ (T.restr B).source := by
    rw [OpenPartialHomeomorph.restr_source, hBopen.interior_eq]
    exact ⟨hTex, hexB⟩
  obtain ⟨e', he', hxe', hconj⟩ :=
    exists_chart_extend_of_openPartialHomeomorph (T := T.restr B) I he hx hT₀sm hT₀syms hT₀src hT₀tgt hexT₀
  have hcont : ContinuousOn (e.extend I) e.source := by
    rw [← OpenPartialHomeomorph.extend_source (f := e) (I := I)]
    exact e.continuousOn_extend
  refine ⟨e', e'.source ∩ (e.source ∩ (e.extend I) ⁻¹' B), he', ?_, ?_, inter_subset_left, ?_⟩
  · exact ⟨hxe', hx, by rw [Set.mem_preimage]; exact hexB⟩
  · exact e'.open_source.inter (hcont.isOpen_inter_preimage e.open_source hBopen)
  · intro y hy
    obtain ⟨hye', hye, hyB⟩ := hy
    rw [hconj y hye']
    simp only [OpenPartialHomeomorph.restr_apply]
    have h2 : fderiv ℝ frep ex (T ((e.extend I) y)) = frep ((e.extend I) y) + fderiv ℝ frep ex ex :=
      hWT _ (hB3 hyB)
    rw [h2]
    have h3 : frep ((e.extend I) y) = f y := by
      rw [hfrep_def]
      show f ((e.extend I).symm ((e.extend I) y)) = f y
      rw [PartialEquiv.left_inv _ (by rw [OpenPartialHomeomorph.extend_source]; exact hye)]
    rw [h3]
    abel

/-- **The hard direction of the normal form of submersions on a manifold.**

`x` is an interior point of `M`, `e` a chart of the maximal atlas at `x`, `f x = 0`, and the
representation `frep := f ∘ (e.extend I).symm` of `f` in the chart is `C^∞` on an open
`V ∋ (e.extend I) x` contained in the chart target, with `fderiv ℝ frep ((e.extend I) x)`
surjective.  Then `0` is a regular value of `f` at `x`, i.e. `f` is a submersion at `x` in the
sense of `Manifold.IsSubmersionAt`.

This is the missing Mathlib statement "surjective `mfderiv` + smoothness ⟹ `IsSubmersionAt`".
Proof: apply `exists_localDiffeomorph_shift` to `frep` at `(e.extend I) x`, restrict `T` to a small
ball inside `interior (range I)` whose image also lies there, conjugate the chart by `T`
(`exists_chart_extend_of_openPartialHomeomorph`) and conclude with
`IsSubmersionAtOfComplement.mk_of_charts`, taking for the codomain chart the translation
`w ↦ w + fderiv ℝ frep ((e.extend I) x)` of `ℝ^k` and for the linear equivalence
`E' ≃L[ℝ] (ℝ^k × ker L)` the one induced by a right inverse of `L`. -/
theorem isSubmersionAt_of_surjective_fderiv_localRep
    {k : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E' H) {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (hxi : x ∉ I.boundary M)
    {f : M → EuclideanSpace ℝ (Fin k)} (hfx : f x = 0)
    {V : Set E'} (hV : IsOpen V) (hVx : (e.extend I) x ∈ V) (hVsub : V ⊆ (e.extend I).target)
    (hf : ContDiffOn ℝ ∞ (fun v => f ((e.extend I).symm v)) V)
    (hsurj : Function.Surjective (fderiv ℝ (fun v => f ((e.extend I).symm v)) ((e.extend I) x))) :
    Manifold.IsSubmersionAt I (𝓡 k) ∞ f x := by
  set ex : E' := (e.extend I) x with hex_def
  set frep : E' → EuclideanSpace ℝ (Fin k) := fun v => f ((e.extend I).symm v) with hfrep_def
  set L : E' →L[ℝ] EuclideanSpace ℝ (Fin k) := fderiv ℝ frep ex with hL_def
  have hsurj' : Function.Surjective L := by
    simpa only [hL_def, hfrep_def, hex_def] using hsurj
  obtain ⟨e', S, he', hxS, hSopen, hSsub, hident⟩ :=
    exists_chart_linear_rep (k := k) I he hx hxi hfx hV hVx hVsub hf hsurj
  have hident' : ∀ y ∈ S, f y = L ((e'.extend I) y) - L ex := fun y hy => by
    simpa only [hL_def, hfrep_def, hex_def] using hident y hy
  -- the chart restricted to S
  set e'' : OpenPartialHomeomorph M H := e'.restr S with he''_def
  have he''_mem : e'' ∈ IsManifold.maximalAtlas I ∞ M := by
    rw [he''_def]; exact restr_mem_maximalAtlas _ he' hSopen
  have he''_src : e''.source ⊆ S := by
    rw [he''_def, OpenPartialHomeomorph.restr_source, hSopen.interior_eq]
    exact inter_subset_right
  have he''_ext : ∀ y : M, (e''.extend I) y = (e'.extend I) y := by
    intro y
    rw [he''_def, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe,
      Function.comp_apply, Function.comp_apply, OpenPartialHomeomorph.restr_apply]
  have hx'' : x ∈ e''.source := by
    rw [he''_def, OpenPartialHomeomorph.restr_source, hSopen.interior_eq]
    exact ⟨hSsub hxS, hxS⟩
  -- the linear equivalence `E' ≃L (ℝ^k × ker L)`
  obtain ⟨σ, hσ⟩ := ContinuousLinearMap.exists_rightInverse_of_surjective L
    (LinearMap.range_eq_top.mpr hsurj')
  have hσ' : ∀ y, L (σ y) = y := fun y => by
    have := congrArg (fun (g : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) => g y) hσ
    simpa using this
  let φ : E' →ₗ[ℝ] (EuclideanSpace ℝ (Fin k) × L.ker) :=
    { toFun := fun v => (L v, ⟨v - σ (L v), by
        show L (v - σ (L v)) = 0
        rw [map_sub, hσ', sub_self]⟩)
      map_add' := fun v w => by
        refine Prod.ext ?_ ?_
        · show L (v + w) = L v + L w
          rw [map_add]
        · refine Subtype.ext ?_
          show (v + w) - σ (L (v + w)) = (v - σ (L v)) + (w - σ (L w))
          rw [map_add, map_add]
          abel
      map_smul' := fun c v => by
        refine Prod.ext ?_ ?_
        · show L (c • v) = c • L v
          rw [map_smul]
        · refine Subtype.ext ?_
          show (c • v) - σ (L (c • v)) = c • (v - σ (L v))
          rw [map_smul, map_smul, smul_sub] }
  have hbij : Function.Bijective φ := by
    constructor
    · intro v w hvw
      have h1 : L v = L w := congrArg (fun p => p.1) hvw
      have h2 : (v - σ (L v)) = (w - σ (L w)) := congrArg (fun p => (p.2 : E')) hvw
      calc v = σ (L v) + (v - σ (L v)) := by abel
        _ = σ (L w) + (w - σ (L w)) := by rw [h2, h1]
        _ = w := by abel
    · intro p
      obtain ⟨y, w⟩ := p
      refine ⟨σ y + w, ?_⟩
      refine Prod.ext ?_ ?_
      · show L (σ y + w) = y
        rw [map_add, hσ']
        have hw : L (w : E') = 0 := w.2
        rw [hw, add_zero]
      · refine Subtype.ext ?_
        show ((σ y + w : E') - σ (L (σ y + (w : E')))) = (w : E')
        rw [map_add, hσ']
        have hw : L (w : E') = 0 := w.2
        rw [hw, add_zero, add_sub_cancel_left]
  let eql : E' ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin k) × L.ker) := LinearEquiv.ofBijective φ hbij
  let equiv : E' ≃L[ℝ] (EuclideanSpace ℝ (Fin k) × L.ker) := eql.toContinuousLinearEquiv
  have hequiv_pr : ∀ v : E', (equiv v).1 = L v := fun v => rfl
  set Bcod : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)) :=
    (Homeomorph.addRight (L ex)).toOpenPartialHomeomorph with hBcod_def
  have hBcod_app : ∀ w : EuclideanSpace ℝ (Fin k), Bcod w = w + L ex := fun w => rfl
  have hBcod_mem : Bcod ∈ IsManifold.maximalAtlas (𝓡 k) ∞ (EuclideanSpace ℝ (Fin k)) := by
    rw [hBcod_def]
    rw [IsManifold.mem_maximalAtlas_iff]
    refine StructureGroupoid.mem_maximalAtlas_of_mem_groupoid _ ?_
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
    constructor
    · simp only [Homeomorph.toOpenPartialHomeomorph_apply,
        Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.coe_addRight,
        modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, Set.preimage_id_eq,
        Function.id_comp, Function.comp_id]
      exact (contDiffOn_id.add contDiffOn_const)
    · simp only [Homeomorph.toOpenPartialHomeomorph_symm_apply,
        Homeomorph.toOpenPartialHomeomorph_target, Homeomorph.addRight_symm,
        Homeomorph.coe_addRight, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
        Set.preimage_id_eq, Function.id_comp, Function.comp_id]
      exact (contDiffOn_id.add contDiffOn_const)
  refine (Manifold.IsSubmersionAtOfComplement.mk_of_charts (F := L.ker) equiv e'' Bcod
    hx'' ?_ he''_mem hBcod_mem ?_ ?_).isSubmersionAt
  · rw [hBcod_def]; exact mem_univ _
  · intro y hy
    rw [hBcod_def]
    exact mem_univ _
  · intro v hv
    simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply, modelWithCornersSelf_coe,
      Function.id_comp, hequiv_pr v, hBcod_app]
    have hy : (e''.extend I).symm v ∈ e''.source := by
      rw [← OpenPartialHomeomorph.extend_source (f := e'') (I := I)]
      exact (e''.extend I).map_target hv
    have h1 : f ((e''.extend I).symm v)
        = L ((e''.extend I) ((e''.extend I).symm v)) - L ex := by
      rw [he''_ext]
      exact hident' _ (he''_src hy)
    rw [h1, (e''.extend I).right_inv hv]
    abel

/-- On the model space `EuclideanSpace ℝ (Fin k)`, every chart of the maximal atlas of the
self-model is `C^∞` (as is its inverse): on the model space the maximal atlas of a structure
groupoid is the structure groupoid itself. -/
theorem contDiffOn_mem_maximalAtlas_self {k : ℕ}
    {B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))}
    (hB : B ∈ IsManifold.maximalAtlas (𝓡 k) ∞ (EuclideanSpace ℝ (Fin k))) :
    ContDiffOn ℝ ∞ (B : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) B.source ∧
      ContDiffOn ℝ ∞ (B.symm : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) B.target := by
  have hmem : B ∈ contDiffGroupoid ∞ (𝓡 k) := by
    rw [IsManifold.mem_maximalAtlas_iff] at hB
    rw [mem_maximalAtlas_iff] at hB
    have h2 : (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin k))).symm.trans B
        ∈ contDiffGroupoid ∞ (𝓡 k) := (hB _ (by simp)).2
    simpa only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans] using h2
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at hmem
  exact ⟨by simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
      Set.preimage_id_eq, Set.univ_inter, Set.inter_univ, id_eq, Function.id_comp, Function.comp_id] using hmem.1,
    by simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
      Set.preimage_id_eq, Set.univ_inter, Set.inter_univ, id_eq, Function.id_comp, Function.comp_id] using hmem.2⟩

/-- **The derivative of `w ↦ F w - χ w • t`.** -/
theorem fderiv_sub_smul_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (G : E → F) (χ : E → ℝ) (t : F) {x : E}
    (hG : DifferentiableAt ℝ G x) (hχ : DifferentiableAt ℝ χ x) :
    fderiv ℝ (fun y => G y - χ y • t) x = fderiv ℝ G x - (fderiv ℝ χ x).smulRight t :=
  (hG.hasFDerivAt.sub (hχ.hasFDerivAt.smul_const t)).fderiv

/-- **The local representation of a global `C^∞` map is genuinely `C^∞`** (arbitrary target).

For any model `𝓘(ℝ, F)` on the target values, the representation
`v ↦ G ((e.extend I).symm v)` of `G` in a chart `e` of the maximal atlas is `C^∞` on the target of
the extended chart.  This is `contDiffOn_localRep` with the codomain generalised from
`EuclideanSpace ℝ (Fin k)` to an arbitrary normed space. -/
theorem contDiffOn_localRep_of {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E' H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {G : M → F} (hG : ContMDiff I 𝓘(ℝ, F) ∞ G)
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I ∞ M) :
    ContDiffOn ℝ ∞ (fun v => G ((e.extend I).symm v)) (I '' e.target) := by
  have h1 : ContMDiffOn 𝓘(ℝ, E') I ∞ (fun v => (e.extend I).symm v) (I '' e.target) :=
    contMDiffOn_extend_symm he
  have h2 : ContMDiffOn I 𝓘(ℝ, F) ∞ G univ := fun x _ => hG x
  have h3 : ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, F) ∞ (fun v => G ((e.extend I).symm v)) (I '' e.target) :=
    h2.comp h1 (fun v _ => trivial)
  rwa [contMDiffOn_iff_contDiffOn] at h3

end Work.ThomBordism.Transversality.TransverseSard
