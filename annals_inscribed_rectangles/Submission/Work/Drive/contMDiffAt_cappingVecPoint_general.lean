import Mathlib
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.Neutral.stripDiskValueClause
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.contMDiffAt_projMk
import Submission.Work.Drive.chartedStructure_contMDiffWithinAt
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff
import Submission.Work.Drive.contMDiffAt_projCharted_iff
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff_general

/-!
# The general-source version of `contMDiffAt_cappingVecPoint`

`Submission/Work/Drive/StripDiskAux.lean` proves that the capping point of a non-vanishing smooth
vector and a positive smooth radius is `C^∞` for maps whose source is `ℝᵏ`
(`Work.Drive.contMDiffAt_cappingVecPoint`).  The chain route needs the same statement with an
arbitrary normed source `E`; since every ingredient of the proof of the Euclidean version is stated
for an arbitrary source manifold, this file records the three general-source versions of the
analytic tools used there:

* `Work.Drive.contMDiffAt_projCharted_iff_general` — the chart criterion for maps into `ℝPⁿ`,
* `Work.Drive.contMDiffAt_projMk_general` — smoothness of a projectivised smooth non-vanishing
  vector, and
* `Work.Drive.contMDiffAt_expHomeo_symm_general` — smoothness of the radial coordinate
  `expHomeo.symm ∘ r` for a positive smooth `r`,

and then the target `Work.Drive.contMDiffAt_cappingVecPoint_general`, the generalisation of
`Work.Drive.contMDiffAt_cappingVecPoint` to an arbitrary normed source.
-/

namespace Work.Drive

open Manifold Function Set Topology Filter
open scoped Manifold ContDiff

noncomputable section

set_option linter.style.haveILetI false

/-! ## 1. The chart criterion for `ℝPⁿ` over an arbitrary source -/

/-- **Testing `C^∞` into `ℝPⁿ` (`projCharted n`) in an arbitrary projective chart, over an
arbitrary source.**  If `Z` is a charted space over `H` with model `I` and `f z` lies in the source
of the `i`-th projective chart, then `f` is `C^∞` at `z` exactly when it is continuous at `z` and
the composite `projChartMap i ∘ f` is `C^∞` at `z`.

This is `Work.Drive.contMDiffAt_projCharted_iff` with the source model uncoupled from the Euclidean
one; the proof is the same computation in the (now non-trivial) source chart of `Z`. -/
theorem contMDiffAt_projCharted_iff_general {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z] {n : ℕ}
    (f : Z → Projectivization ℝ (Eucl n)) (z : Z) (i : Fin (n + 1))
    (hz : f z ∈ projChartSource i) :
    letI := projCharted n
    (ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) f z ↔
      ContinuousAt f z ∧
        ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => projChartMap i (f w)) z) := by
  letI := projCharted n
  haveI : IsManifold (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl n)) :=
    isManifold_projCharted n
  have he' : projChart i ∈ IsManifold.maximalAtlas (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization ℝ (Eucl n)) :=
    StructureGroupoid.subset_maximalAtlas _ (Set.mem_range_self i)
  -- the extended chart `projChart i` is the map `projChartMap i`
  have hext : ⇑((projChart i).extend (𝓡 n)) = projChartMap i := by
    rw [OpenPartialHomeomorph.extend_coe]
    funext p
    simp [modelWithCornersSelf_coe]
  -- unfold the left-hand side in the chart `projChart i` of the target
  have hL : ContMDiffAt I (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) f z ↔
      ContinuousAt f z ∧
        ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          ((projChart i).extend (𝓡 n) ∘ f ∘ (extChartAt I z).symm) (range I)
          ((extChartAt I z) z) := by
    rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas' he' hz]
    simp only [continuousWithinAt_univ, preimage_univ, univ_inter]
  -- unfold the right-hand side (a map into a normed space) in the source chart of `Z`
  have hR : ContMDiffAt I (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => projChartMap i (f w)) z ↔
      ContinuousAt (fun w => projChartMap i (f w)) z ∧
        ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          ((fun w => projChartMap i (f w)) ∘ (extChartAt I z).symm) (range I)
          ((extChartAt I z) z) := by
    rw [contMDiffAt_iff]
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.comp_def, id_eq]
  -- the two smoothness conditions are the same
  have hdiff : ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((projChart i).extend (𝓡 n) ∘ f ∘ (extChartAt I z).symm) (range I)
        ((extChartAt I z) z) ↔
      ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        ((fun w => projChartMap i (f w)) ∘ (extChartAt I z).symm) (range I)
        ((extChartAt I z) z) := by
    have h1 : ((projChart i).extend (𝓡 n) ∘ f ∘ (extChartAt I z).symm)
        = ((fun w => projChartMap i (f w)) ∘ (extChartAt I z).symm) := by
      funext y
      simp only [Function.comp_apply]
      exact congrFun hext (f ((extChartAt I z).symm y))
    rw [h1]
  -- continuity of `projChartMap i ∘ f` follows from that of `f`, since `projChartMap i` is
  -- continuous on its (open) source
  have hcont : ContinuousAt f z → ContinuousAt (fun w => projChartMap i (f w)) z := fun hf =>
    (((continuousOn_projChartMap i).continuousAt
      ((isOpen_projChartSource i).mem_nhds hz))).comp hf
  rw [hL, hR, hdiff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hcont h1, h2⟩, fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩⟩

/-! ## 2. Smoothness of a projectivised smooth non-vanishing vector -/

/-- **Smoothness into `ℝPⁿ` of a projectivised smooth non-vanishing vector, over an arbitrary
source.**  This is `Work.Drive.contMDiffAt_projMk` with the source `EuclideanSpace ℝ (Fin k)`
replaced by an arbitrary charted space `Z`, proved through
`Work.Drive.contMDiffAt_projCharted_iff_general`. -/
theorem contMDiffAt_projMk_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z] {n : ℕ}
    (V : Z → Eucl n) (hV : ∀ x, V x ≠ 0) (x₀ : Z)
    (hVs : ContMDiffAt I (modelWithCornersSelf ℝ (Eucl n)) ((⊤ : ℕ∞) : WithTop ℕ∞) V x₀) :
    letI := projCharted n
    ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Projectivization.mk ℝ (V x) (hV x)) x₀ := by
  -- the transparent projective structure, so that the chart `projChart i` is available
  letI := projCharted n
  -- a chart index at which the vector `V x₀` is non-zero
  have hex : ∃ i : Fin (n + 1), (V x₀).ofLp i ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    refine hV x₀ ?_
    ext i
    simpa using not_not.mp (hcon i)
  obtain ⟨i, hi⟩ := hex
  -- reduce to continuity plus smoothness of the composite with the chart `projChart i`
  rw [contMDiffAt_projCharted_iff_general (I := I) (n := n)
    (f := fun x => Projectivization.mk ℝ (V x) (hV x)) x₀ i
    ((mem_projChartSource_iff' (i := i) (hV x₀)).mpr hi)]
  refine ⟨?_, ?_⟩
  · -- continuity: `Projectivization.mk` is continuous and `x ↦ ⟨V x, hV x⟩` is continuous at `x₀`
    exact (continuous_projectivizationMk ℝ (Eucl n)).continuousAt.comp
      (hVs.continuousAt.codRestrict (t := {v : Eucl n | v ≠ 0}) (fun x => hV x))
  · -- smoothness of the composite: it is `fun w ↦ projCoordFun i (V w)`
    have hcoord : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun v : Eucl n => projCoordFun i v) (V x₀) := by
      refine (contDiffAt_piLp (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (p := 2)
        (E := fun _ : Fin n => ℝ) (f := fun v : Eucl n => projCoordFun i v)).2 ?_
      intro j
      have hj : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun v : Eucl n => v.ofLp (i.succAbove j) / v.ofLp i) (V x₀) := by fun_prop
      simpa only [projCoordFun_ofLp] using hj
    have key : ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => projCoordFun i (V w)) x₀ :=
      hcoord.contMDiffAt.comp x₀ hVs
    have hfun : (fun w => projChartMap i (Projectivization.mk ℝ (V w) (hV w)))
        = fun w => projCoordFun i (V w) := by
      funext w
      exact projChartMap_mk i (V w) (hV w)
    rw [hfun]
    exact key

/-! ## 3. Smoothness of the radial coordinate -/

/-- **Smoothness of the first (radial) coordinate, over an arbitrary source.**  For a positive
smooth `r` on a charted space `Z` over `H`, the map `w ↦ expHomeo.symm ⟨r w, ·⟩` into `ℝ¹` is
`C^∞` at `x₀`: it is `logEucl ∘ (Real.log ∘ r)`.  This is
`Work.Drive.contMDiffAt_expHomeo_symm` with an arbitrary source. -/
theorem contMDiffAt_expHomeo_symm_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace H Z]
    {r : Z → ℝ} (hr : ∀ w, 0 < r w) (x₀ : Z)
    (hrs : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) r x₀) :
    ContMDiffAt I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => expHomeo.symm ⟨r w, hr w⟩) x₀ := by
  have hfun : (fun w => expHomeo.symm ⟨r w, hr w⟩) = fun w => logEucl (Real.log (r w)) := by
    funext w
    exact expHomeo_symm_apply ⟨r w, hr w⟩
  rw [hfun]
  have hlog : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => Real.log (r w)) x₀ :=
    (Real.contDiffAt_log.mpr (ne_of_gt (hr x₀))).contMDiffAt.comp x₀ hrs
  exact (logEucl.contDiff.contDiffAt.contMDiffAt).comp x₀ hlog

/-! ## 4. The capping point of a smooth radius and a smooth non-vanishing vector -/

/-- **Smoothness of the capping point with prescribed radius and physical vector, over an arbitrary
normed source.**  This is `Work.Drive.contMDiffAt_cappingVecPoint` with the source
`EuclideanSpace ℝ (Fin k)` replaced by an arbitrary normed space `E`. -/
theorem contMDiffAt_cappingVecPoint_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : E → ℝ) (V : E → Work.Drive.Eucl 3) (x₀ : E)
    (hr : ∀ x, 0 < r x) (hV : ∀ x, V x ≠ 0)
    (hrs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r x₀)
    (hVs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V x₀) :
    letI := Work.Drive.cappingCharted
    ContMDiffAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Work.Drive.cappingSpaceHomeoProj.symm
        (⟨r x, hr x⟩, Projectivization.mk ℝ (V x) (hV x))) x₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ)) :=
    Homeomorph.chartedSpace expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  let F : E → CappingSpace := fun w =>
    cappingSpaceHomeoProj.symm (⟨r w, hr w⟩, Projectivization.mk ℝ (V w) (hV w))
  let g : E → Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => cappingSpaceHomeoProj (F w)
  have hg : ∀ w, g w = (⟨r w, hr w⟩, Projectivization.mk ℝ (V w) (hV w)) := fun w =>
    cappingSpaceHomeoProj.apply_symm_apply _
  have hchart : (letI := cappingCharted
        ContMDiffAt (modelWithCornersSelf ℝ E)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
          ((⊤ : ℕ∞) : WithTop ℕ∞) F x₀) ↔
      ContMDiffAt (modelWithCornersSelf ℝ E)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g x₀ :=
    chartedStructure_contMDiffWithinAt (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4))
      (H := EuclideanSpace ℝ (Fin 4)) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := E) (H' := E) (modelWithCornersSelf ℝ E)
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      cappingSpaceHomeoProj.symm F Set.univ x₀
  have hfirst : ContMDiffAt (modelWithCornersSelf ℝ E) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => expHomeo.symm (g w).1) x₀ := by
    have hcomp : (fun w => expHomeo.symm (g w).1) = fun w => expHomeo.symm ⟨r w, hr w⟩ := by
      funext w
      rw [hg w]
    rw [hcomp]
    exact contMDiffAt_expHomeo_symm_general (I := modelWithCornersSelf ℝ E) hr x₀ hrs.contMDiffAt
  have hsecond : ContMDiffAt (modelWithCornersSelf ℝ E) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (g w).2) x₀ := by
    have hcomp : (fun w => (g w).2) = fun w => Projectivization.mk ℝ (V w) (hV w) := by
      funext w
      rw [hg w]
    rw [hcomp]
    exact contMDiffAt_projMk_general (I := modelWithCornersSelf ℝ E) (n := 3) V hV x₀
      hVs.contMDiffAt
  exact hchart.mpr
    ((contMDiffAt_halfLineProjective_iff_general (I := modelWithCornersSelf ℝ E) g x₀).mpr
      ⟨hfirst, hsecond⟩)

end

end Work.Drive
