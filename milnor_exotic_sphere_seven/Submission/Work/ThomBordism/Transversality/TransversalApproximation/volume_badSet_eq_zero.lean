import Mathlib
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.badSetEuclid
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.chartCover
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.chartBridge
import Submission.Work.ThomBordism.Transversality.TransversalApproximation.mfderiv_surjective_of_submersionAt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Item 3 of the transversality homotopy theorem: the bad set of parameters is null

**The statement.**  For a compact `T2` manifold `M` modelled on `I`, a `C^∞` map
`G : M → ℝ^k` and a nonnegative `C^∞` function `χ : M → ℝ`, the set of parameters
`t : ℝ^k` for which there is an *interior* point `x` with `χ x > 0`, `G x = χ x • t` at which
`x ↦ G x - χ x • t` fails to be submersive is Lebesgue-null.

**The proof.**  A witness `x` lies in `{χ > 0}`; by compactness finitely many preferred charts
`chartAt H y` (from `exists_finite_chart_cover`) cover this region, and the bad set is contained
in the union over these finitely many charts of the sets

`{t | ∃ x ∈ (chartAt H y).source, I.IsInteriorPoint x ∧ 0 < χ x ∧ G x = χ x • t ∧ x critical}`.

For one chart `e = chartAt H y` one transports along a continuous linear equivalence
`L : E ≃L[ℝ] ℝ^d` (`d = finrank ℝ E`) to the Euclidean situation and applies the Euclidean
bad-set lemma `volume_badSet_eq_zero_euclid_of_isOpen`.  The two ingredients that make the
transport work are:

* the representation `v ↦ G ((e.extend I).symm v)` of `G` in the chart is `C^∞` on the interior of
  the chart target (`cInfOn_localRep`; this is `TransverseSard.contDiffOn_localRep` with the target
  space kept general, so that it applies to `χ : M → ℝ` as well), and
* surjectivity of `mfderiv I (𝓡 k) f x` is equivalent to surjectivity of the ordinary derivative of
  the chart representation of `f` at `e.extend I x`, for *any* chart `e` of the maximal atlas
  (`surjective_mfderiv_iff_surjective_fderiv_extend`) — the chart-independent form of the
  `extChartAt`-based bridge `surjective_mfderiv_iff_surjective_fderiv_extChartAt` that the
  transversality approximation needs.  Its proof is a chain-rule computation with the chart
  transition `I.extendCoordChange e (chartAt H x)`, whose derivative is invertible.
-/

open scoped Manifold ContDiff MeasureTheory Topology
open MeasureTheory Set Filter Function Topology Manifold

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.TransversalApproximation

noncomputable section

/-! ## Auxiliary lemmas -/

/-- Surjectivity of a composite of continuous linear maps reduces to surjectivity of the left
factor when the right factor is surjective. -/
private lemma surjective_comp_iff {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : F →L[ℝ] G) (B : E →L[ℝ] F) (hB : Function.Surjective B) :
    Function.Surjective (A.comp B) ↔ Function.Surjective A := by
  have h : ⇑(A.comp B) = ⇑A ∘ ⇑B := by ext x; rfl
  rw [h]
  exact Function.Surjective.of_comp_iff _ hB

/-- **Precomposition with the inverse of a continuous linear equivalence does not change
surjectivity of the derivative.** -/
private lemma surjective_fderiv_precomp_symm_iff {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (T : E ≃L[ℝ] F) (f : E → G) {y : E} (hf : DifferentiableAt ℝ f y) :
    Function.Surjective (fderiv ℝ (fun x : F => f (T.symm x)) (T y)) ↔
      Function.Surjective (fderiv ℝ f y) := by
  have hT : HasFDerivAt (fun x : F => T.symm x) (T.symm : F →L[ℝ] E) (T y) :=
    ContinuousLinearMap.hasFDerivAt (T.symm : F →L[ℝ] E)
  have hf' : HasFDerivAt f (fderiv ℝ f y) (T.symm (T y)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf.hasFDerivAt
  have h1 : fderiv ℝ (fun x : F => f (T.symm x)) (T y)
      = (fderiv ℝ f y).comp (T.symm : F →L[ℝ] E) :=
    (hf'.comp (T y) hT).fderiv
  rw [h1]
  exact surjective_comp_iff _ _ (ContinuousLinearEquiv.surjective T.symm)

/-- **The representation of a `C^∞` map in a chart of the maximal atlas is `C^∞`** on the interior
of the chart target.  (This is `TransverseSard.contDiffOn_localRep` with the target space kept
general, so that it applies also to `χ : M → ℝ`.) -/
private lemma cInfOn_localRep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {F : M → F'} (hF : ContMDiff I (modelWithCornersSelf ℝ F') ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ((⊤ : ℕ∞) : WithTop ℕ∞) M) :
    CInfOn (fun v : E => F ((e.extend I).symm v)) (interior ((e.extend I).target)) := by
  have h1 : ContMDiffOn 𝓘(ℝ, E) I ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : E => (e.extend I).symm v) (I '' e.target) :=
    contMDiffOn_extend_symm he
  have h2 : ContMDiffOn I (modelWithCornersSelf ℝ F') ((⊤ : ℕ∞) : WithTop ℕ∞) F univ :=
    fun x _ => hF x
  have h3 : ContMDiffOn 𝓘(ℝ, E) (modelWithCornersSelf ℝ F') ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : E => F ((e.extend I).symm v)) (I '' e.target) :=
    h2.comp h1 (fun v _ => trivial)
  rw [contMDiffOn_iff_contDiffOn] at h3
  rw [OpenPartialHomeomorph.extend_target']
  exact h3.mono interior_subset

/-- **Differentiability at `x` from smoothness of the chart representation.**  If the
representation of `F` in a chart `e` of the maximal atlas is `C^∞` near the image of the interior
point `x`, then `F` is differentiable at `x`. -/
private lemma mdifferentiableAt_of_cInfOn_localRep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] {k : ℕ}
    {F : M → EuclideanSpace ℝ (Fin k)} {x : M}
    {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ((⊤ : ℕ∞) : WithTop ℕ∞) M) (hex : x ∈ e.source)
    (hut : (e.extend I) x ∈ interior ((e.extend I).target))
    (h : CInfOn (fun v : E => F ((e.extend I).symm v)) (interior ((e.extend I).target))) :
    MDifferentiableAt I (𝓡 k) F x := by
  have he1 : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hca : ContMDiffAt 𝓘(ℝ, E) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun v : E => F ((e.extend I).symm v)) (e.extend I x) :=
    (h.contDiffAt (isOpen_interior.mem_nhds hut)).contMDiffAt
  have hwithin : MDiffAt[range I] (fun v : E => F ((e.extend I).symm v)) (e.extend I x) :=
    (hca.contMDiffWithinAt).mdifferentiableWithinAt (by simp)
  refine mdifferentiableWithinAt_univ.mp ((mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas
    (I := I) (f := F) he1 hex).mpr ?_)
  rw [Set.preimage_univ, Set.univ_inter]
  exact hwithin

/-- **Chart-independence of criticality.**  At an interior point `x` of a `C^∞` manifold `M`
modelled on `I`, for any chart `e` of the maximal atlas around `x`, surjectivity of the manifold
derivative of `f` at `x` is equivalent to surjectivity of the ordinary derivative of the chart
expression `z ↦ f ((e.extend I).symm z)` at `z = e.extend I x`. -/
theorem surjective_mfderiv_iff_surjective_fderiv_extend
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] {k : ℕ}
    {f : M → EuclideanSpace ℝ (Fin k)} {x : M} (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I (𝓡 k) f x)
    {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ((⊤ : ℕ∞) : WithTop ℕ∞) M) (hex : x ∈ e.source) :
    Function.Surjective (mfderiv I (𝓡 k) f x) ↔
      Function.Surjective (fderiv ℝ (fun z : E => f ((e.extend I).symm z)) (e.extend I x)) := by
  rw [surjective_mfderiv_iff_surjective_fderiv_extChartAt I hx hf]
  set C : PartialEquiv E E := I.extendCoordChange e (chartAt H x) with hC
  have hCcoe : ⇑C = fun z : E => (extChartAt I x) ((e.extend I).symm z) := by
    rw [hC]; rfl
  have hCu : C (e.extend I x) = (extChartAt I x) x := by
    rw [hCcoe]
    exact congrArg (extChartAt I x) (OpenPartialHomeomorph.extend_left_inv e hex)
  have hut : (e.extend I) x ∈ interior ((e.extend I).target) :=
    (isInteriorPoint_iff_of_mem_maximalAtlas (I := I) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp) he
      hex).mp hx
  have hurange : (e.extend I) x ∈ interior (range I) :=
    OpenPartialHomeomorph.interior_extend_target_subset_interior_range e hut
  have hmemI : range I ∈ 𝓝 (e.extend I x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hurange) interior_subset
  have hCnhds : C.source ∈ 𝓝 (e.extend I x) := by
    rw [hC]
    have h1 := ModelWithCorners.extendCoordChange_source_mem_nhdsWithin' (I := I) hex
      (mem_chart_source H x)
    rwa [nhdsWithin_eq_nhds.mpr hmemI] at h1
  have hCsrc : (e.extend I) x ∈ C.source := by
    rw [hC, ← OpenPartialHomeomorph.extend_image_source_inter]
    exact ⟨x, ⟨hex, mem_chart_source H x⟩, rfl⟩
  have hCcont : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑C) C.source := by
    rw [hC]
    exact ModelWithCorners.contDiffOn_extendCoordChange he (IsManifold.chart_mem_maximalAtlas x)
  have hCdiff : DifferentiableAt ℝ (⇑C) (e.extend I x) :=
    (hCcont.contDiffAt hCnhds).differentiableAt (by simp)
  have hCsurj : Function.Surjective (fderiv ℝ (⇑C) (e.extend I x)) := by
    have hinv : (fderivWithin ℝ (⇑C) C.source (e.extend I x)).IsInvertible := by
      rw [hC]
      exact ModelWithCorners.isInvertible_fderivWithin_extendCoordChange (I := I)
        (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp) he (IsManifold.chart_mem_maximalAtlas x) hCsrc
    rw [← fderivWithin_of_mem_nhds hCnhds]
    exact hinv.surjective
  -- the chart expression in the preferred chart at `x`
  have hmem' : (extChartAt I x) x ∈ interior (range I) := by
    have hx' := hx
    rw [ModelWithCorners.isInteriorPoint_iff] at hx'
    exact interior_mono (extChartAt_target_subset_range (I := I) x) hx'
  have hnhds' : range I ∈ 𝓝 ((extChartAt I x) x) :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hmem') interior_subset
  have hwritten : writtenInExtChartAt I (𝓡 k) x f = fun z : E => f ((extChartAt I x).symm z) := by
    funext z
    simp only [writtenInExtChartAt, Function.comp_apply]
    rw [extChartAt_self_eq]
    rfl
  have hfx_diff : DifferentiableAt ℝ (fun z : E => f ((extChartAt I x).symm z))
      ((extChartAt I x) x) := by
    have h := hf.differentiableWithinAt_writtenInExtChartAt
    rw [hwritten] at h
    exact h.differentiableAt hnhds'
  -- eventually the two chart expressions agree
  have hsymm_cont : ContinuousAt (fun z : E => (e.extend I).symm z) (e.extend I x) :=
    OpenPartialHomeomorph.continuousAt_extend_symm' e (interior_subset hut)
  have hev_src : (chartAt H x).source ∈ 𝓝 ((e.extend I).symm ((e.extend I) x)) := by
    rw [OpenPartialHomeomorph.extend_left_inv e hex]
    exact (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  have hev : (fun z : E => f ((e.extend I).symm z))
      =ᶠ[𝓝 (e.extend I x)] (fun z : E => f ((extChartAt I x).symm z)) ∘ ⇑C := by
    filter_upwards [hsymm_cont.eventually hev_src] with z hz
    have hz' : (e.extend I).symm z ∈ (extChartAt I x).source := by
      rwa [extChartAt_source]
    show f ((e.extend I).symm z) = f ((extChartAt I x).symm (C z))
    rw [hCcoe]
    show f ((e.extend I).symm z)
      = f ((extChartAt I x).symm ((extChartAt I x) ((e.extend I).symm z)))
    rw [PartialEquiv.left_inv (extChartAt I x) hz']
  -- chain rule
  have hfx_diff' : DifferentiableAt ℝ (fun z : E => f ((extChartAt I x).symm z))
      (C (e.extend I x)) := by
    rw [hCu]; exact hfx_diff
  have hchain : fderiv ℝ (fun z : E => f ((e.extend I).symm z)) (e.extend I x)
      = (fderiv ℝ (fun z : E => f ((extChartAt I x).symm z)) ((extChartAt I x) x)).comp
          (fderiv ℝ (⇑C) (e.extend I x)) := by
    have h1 : fderiv ℝ ((fun z : E => f ((extChartAt I x).symm z)) ∘ ⇑C) (e.extend I x)
        = (fderiv ℝ (fun z : E => f ((extChartAt I x).symm z)) (C (e.extend I x))).comp
            (fderiv ℝ (⇑C) (e.extend I x)) :=
      fderiv_comp (e.extend I x) hfx_diff' hCdiff
    rw [hev.fderiv_eq, h1, hCu]
  rw [hchain]
  exact (surjective_comp_iff _ _ hCsurj).symm

/-- **Item 3 of the transversality homotopy theorem.**  For a compact `T2` manifold `M`, a `C^∞` map
`G : M → ℝ^k` and a nonnegative `C^∞` function `χ`, the set of parameters `t` for which there is an
interior point `x` with `χ x > 0`, `G x = χ x • t` at which `x ↦ G x - χ x • t` is critical is
null. -/
theorem volume_badSet_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M] [T2Space M] [Nonempty M]
    {k : ℕ} (G : M → EuclideanSpace ℝ (Fin k))
    (hG : ContMDiff I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (χ : M → ℝ) (hχ : ContMDiff I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχ0 : ∀ x, 0 ≤ χ x) :
    MeasureTheory.volume {t : EuclideanSpace ℝ (Fin k) |
      ∃ x, I.IsInteriorPoint x ∧ 0 < χ x ∧ G x = χ x • t ∧
        ¬ Function.Surjective (mfderiv I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k)))
          (fun y => G y - χ y • t) x)} = 0 := by
  classical
  obtain ⟨Y, hcover, hinterior⟩ := exists_finite_chart_cover (I := I) hχ.continuous
  have hnull : ∀ y ∈ Y, MeasureTheory.volume {t : EuclideanSpace ℝ (Fin k) |
      ∃ x ∈ (chartAt H y).source, I.IsInteriorPoint x ∧ 0 < χ x ∧ G x = χ x • t ∧
        ¬ Function.Surjective (mfderiv I (𝓡 k) (fun y' => G y' - χ y' • t) x)} = 0 := by
    intro y hy
    set e : OpenPartialHomeomorph M H := chartAt H y with he_def
    have he : e ∈ IsManifold.maximalAtlas I ((⊤ : ℕ∞) : WithTop ℕ∞) M := by
      rw [he_def]; exact IsManifold.chart_mem_maximalAtlas y
    -- smoothness of the two chart expressions
    have hGe : CInfOn (fun v : E => G ((e.extend I).symm v))
        (interior ((e.extend I).target)) := cInfOn_localRep (I := I) hG he
    have hχe : CInfOn (fun v : E => χ ((e.extend I).symm v))
        (interior ((e.extend I).target)) := cInfOn_localRep (I := I) hχ he
    -- transport to coordinates
    have hd : Module.finrank ℝ E
        = Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := by
      rw [finrank_euclideanSpace, Fintype.card_fin]
    let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      (LinearEquiv.ofFinrankEq E (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) hd)
        |>.toContinuousLinearEquiv
    let V' : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
      (⇑L.symm) ⁻¹' (interior ((e.extend I).target))
    have hV'open : IsOpen V' :=
      (isOpen_interior).preimage L.symm.continuous
    have hmaps : MapsTo (⇑L.symm) V' (interior ((e.extend I).target)) := fun z hz => hz
    have hLsymm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑L.symm) V' :=
      (ContinuousLinearMap.contDiff
        (L.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] E)).contDiffOn
    have hGe' : CInfOn (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        G ((e.extend I).symm (L.symm z))) V' := by
      have h := hGe.comp hLsymm hmaps
      rwa [Function.comp_def] at h
    have hχe' : CInfOn (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        χ ((e.extend I).symm (L.symm z))) V' := by
      have h := hχe.comp hLsymm hmaps
      rwa [Function.comp_def] at h
    have hχe'0 : ∀ z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
        0 ≤ χ ((e.extend I).symm (L.symm z)) := fun z => hχ0 _
    have hnull' := volume_badSet_eq_zero_euclid_of_isOpen
      (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => G ((e.extend I).symm (L.symm z)))
      (fun z : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => χ ((e.extend I).symm (L.symm z)))
      V' hV'open hGe' hχe' hχe'0
    refine measure_mono_null ?_ hnull'
    rintro t ⟨x, hxsrc, hxi, hxpos, hxG, hxcrit⟩
    rw [he_def] at hxsrc
    have hut : (e.extend I) x ∈ interior ((e.extend I).target) := by
      have hxsrc' : x ∈ (chartAt H y).source := by rw [← he_def]; exact hxsrc
      have h := hinterior y hy x hxsrc' hxi
      rwa [← he_def] at h
    have hxinv : (e.extend I).symm (e.extend I x) = x :=
      OpenPartialHomeomorph.extend_left_inv e hxsrc
    refine ⟨L (e.extend I x), ?_, ?_, ?_, ?_⟩
    · show (⇑L.symm) (L (e.extend I x)) ∈ interior ((e.extend I).target)
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact hut
    · show 0 < χ ((e.extend I).symm (L.symm (L (e.extend I x))))
      rw [ContinuousLinearEquiv.symm_apply_apply, hxinv]
      exact hxpos
    · show G ((e.extend I).symm (L.symm (L (e.extend I x))))
          = χ ((e.extend I).symm (L.symm (L (e.extend I x)))) • t
      rw [ContinuousLinearEquiv.symm_apply_apply, hxinv]
      exact hxG
    · -- the criticality transfers to the chart
      have hFe : CInfOn (fun v : E => G ((e.extend I).symm v) - χ ((e.extend I).symm v) • t)
          (interior ((e.extend I).target)) :=
        hGe.sub (hχe.smul (contDiffOn_const :
          ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : E => t) (interior ((e.extend I).target))))
      have hFm : MDifferentiableAt I (𝓡 k)
          (fun y' : M => G y' - χ y' • t) x :=
        mdifferentiableAt_of_cInfOn_localRep (I := I) he hxsrc hut (by simpa only [] using hFe)
      have hbridge := surjective_mfderiv_iff_surjective_fderiv_extend (I := I) hxi hFm he hxsrc
      have hnotE : ¬ Function.Surjective (fderiv ℝ
          (fun v : E => G ((e.extend I).symm v) - χ ((e.extend I).symm v) • t) (e.extend I x)) :=
        fun h => hxcrit (hbridge.mpr (by simpa only [] using h))
      have hFe_diff : DifferentiableAt ℝ
          (fun v : E => G ((e.extend I).symm v) - χ ((e.extend I).symm v) • t) (e.extend I x) :=
        (hFe.contDiffAt (isOpen_interior.mem_nhds hut)).differentiableAt (by simp)
      intro hsurj
      refine hnotE ((surjective_fderiv_precomp_symm_iff L
        (fun v : E => G ((e.extend I).symm v) - χ ((e.extend I).symm v) • t) hFe_diff).mp ?_)
      simpa only [Function.comp_apply] using hsurj
  have hsub : {t : EuclideanSpace ℝ (Fin k) |
      ∃ x, I.IsInteriorPoint x ∧ 0 < χ x ∧ G x = χ x • t ∧
        ¬ Function.Surjective (mfderiv I (𝓡 k) (fun y' => G y' - χ y' • t) x)}
      ⊆ ⋃ y ∈ Y, {t : EuclideanSpace ℝ (Fin k) |
        ∃ x ∈ (chartAt H y).source, I.IsInteriorPoint x ∧ 0 < χ x ∧ G x = χ x • t ∧
          ¬ Function.Surjective (mfderiv I (𝓡 k) (fun y' => G y' - χ y' • t) x)} := by
    rintro t ⟨x, hxi, hxpos, hxG, hxcrit⟩
    obtain ⟨y, hy, hxy⟩ := hcover x hxpos
    exact Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hy, x, hxy, hxi, hxpos, hxG, hxcrit⟩⟩
  refine measure_mono_null hsub ?_
  have h1 : MeasureTheory.volume (⋃ y ∈ Y, {t : EuclideanSpace ℝ (Fin k) |
        ∃ x ∈ (chartAt H y).source, I.IsInteriorPoint x ∧ 0 < χ x ∧ G x = χ x • t ∧
          ¬ Function.Surjective (mfderiv I (𝓡 k) (fun y' => G y' - χ y' • t) x)})
      ≤ ∑ y ∈ Y, MeasureTheory.volume {t : EuclideanSpace ℝ (Fin k) |
        ∃ x ∈ (chartAt H y).source, I.IsInteriorPoint x ∧ 0 < χ x ∧ G x = χ x • t ∧
          ¬ Function.Surjective (mfderiv I (𝓡 k) (fun y' => G y' - χ y' • t) x)} :=
    measure_biUnion_finset_le Y _
  have h2 : ∑ y ∈ Y, MeasureTheory.volume {t : EuclideanSpace ℝ (Fin k) |
        ∃ x ∈ (chartAt H y).source, I.IsInteriorPoint x ∧ 0 < χ x ∧ G x = χ x • t ∧
          ¬ Function.Surjective (mfderiv I (𝓡 k) (fun y' => G y' - χ y' • t) x)} = 0 :=
    Finset.sum_eq_zero (fun y hy => hnull y hy)
  rw [h2] at h1
  exact le_antisymm h1 zero_le

end

end Work.ThomBordism.Transversality.TransversalApproximation
