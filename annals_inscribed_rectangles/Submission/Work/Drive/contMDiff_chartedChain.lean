import Mathlib
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.contMDiff_interpSweep
import Submission.Work.Drive.collapseChartBridge
import Submission.Work.Drive.chainLocalityDesign

/-!
# The charted chains of the radial-collapse transport are smooth

`Submission/Work/Drive/collapseChartBridge.lean`'s capstone `Work.Drive.even_ncard_colCount_zero_add_one`
(the first bullet of the transport, `Even (K 0 + K 1)`) takes the smoothness of the four *charted*
chains as hypotheses,

* `hsmE : ContDiff ℝ ⊤ (Function.uncurry (fun s u => chr (colPlane β Q s u)))`,
* `hsmE' : ContDiff ℝ ⊤ (fun u => chr (diskPlane Q u))`,
* `hsmV`, `hsmW` (the two clamped sweeps),

where `chr : CappingSpace → ℝ⁴` is the chart used by the counting engine.  This file *derives* them,
so that the transport's input list shrinks to the geometric and genericity data, and closes in passing
the obligation recorded at the end of `collapseTransport.lean` (§ "Note on the family smoothness of
block `0`"): the pure `ContDiff` statement of the collapse composed with the square-to-disk map.

The three ingredients:

1. `Work.Drive.contDiff_comp_colMap` — the *general* smoothness of a composition with the collapse:
   for `φ` and `G` smooth, `x ↦ colMap β (φ x) (G x)` is smooth.  (The recorded form of
   `collapseTransport`'s note is the case `φ = (·) 2`, `G = sqDisk ∘ foldBox ∘ mk2`.)
2. `Work.Drive.contMDiff_colPlane` — the honest (uncharted) joint smoothness of the collapse family
   `(s,u) ↦ colPlane β Q s u = Q (colMap β s (sqDisk (foldBox u)))` for a smooth chart `Q`.
3. `Work.Drive.contDiff_chart_comp_of_contMDiff` — the *charted* form: a `C^∞` map into `M` composed
   with a chart of `M` is `C^∞` on the region where its values lie in the chart's source (the
   `ℝ`-valued analogue of the proved `Work.Drive.contMDiffOn_chart_comp`), together with
   `Work.Drive.contMDiffOn_to_contDiffOn_domain` (the `ContMDiffOn ⟹ ContDiffOn` reduction, for an
   arbitrary normed domain); and the *global* form
   `Work.Drive.contDiff_chart_colPlane_of_resident`, which needs only the residency of the chart's
   disk image in the chart's source — a single hypothesis covering all four chains.

Everything is `sorry`-free and axiom-clean.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. The collapse composed with smooth data -/

/-- **Smoothness of the collapse composed with smooth data.**  For a smooth profile `β`, a smooth
real function `φ` and a smooth `ℂ`-valued `G`, the map `x ↦ colMap β (φ x) (G x)` is `C^∞`.

The proof avoids the product-space composition: it unfolds `colMap` into
`(colDenom β (φ x) (G x))⁻¹ • G x` and applies the library's `smul`/`inv` rules to the pullbacks of
`colDenom`, whose ingredients are `colSigma ∘ φ`, `β ∘ ‖G ·‖²` and the constant `1`. -/
lemma contDiff_comp_colMap {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβpos : ∀ t : ℝ, 0 < β t)
    {φ : X → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    {G : X → ℂ} (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : X => colMap β (φ x) (G x)) := by
  have hns : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : X => ‖G x‖ ^ 2) := by
    have he : (fun x : X => ‖G x‖ ^ 2) = fun x => (G x).re ^ 2 + (G x).im ^ 2 := by
      funext x
      rw [Complex.sq_norm, Complex.normSq_apply]
      push_cast
      ring
    rw [he]
    exact (((Complex.reCLM.contDiff (n := (⊤ : ℕ∞))).comp hG).pow 2).add
      (((Complex.imCLM.contDiff (n := (⊤ : ℕ∞))).comp hG).pow 2)
  have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : X => colDenom β (φ x) (G x)) := by
    unfold colDenom
    exact contDiff_const.add
      ((contDiff_colSigma.comp hφ).mul ((hβ.comp hns).sub contDiff_const))
  have hinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : X => (colDenom β (φ x) (G x))⁻¹) :=
    hden.inv (fun x => ne_of_gt (colDenom_pos hβpos (φ x) (G x)))
  have h2 := (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : X => ((colDenom β (φ x) (G x))⁻¹ : ℝ) • G x) from hinv.smul hG)
  simpa only [colMap] using h2

/-- **The obligation recorded in `collapseTransport.lean`**: the collapse composed with the
square-to-disk map of the box parameter is `C^∞`. -/
lemma contDiff_colMap_sqDisk_mk2 {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβpos : ∀ t : ℝ, 0 < β t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 3) =>
        colMap β (p 2) (sqDisk (foldBox (mk2 (p 0) (p 1))))) :=
  contDiff_comp_colMap hβ hβpos (by fun_prop)
    (contDiff_comp_mk2 (sqDisk_contDiff.comp (contMDiff_iff_contDiff.mp foldBox_contMDiff)))

/-- The same in the **uncurried product form** used by the design's chains
(`(s, u) ↦ colMap β s (sqDisk (foldBox u))`). -/
lemma contDiff_colMap_sqDisk_fst {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβpos : ∀ t : ℝ, 0 < β t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
        colMap β p.1 (sqDisk (foldBox p.2))) :=
  contDiff_comp_colMap hβ hβpos contDiff_fst
    (sqDisk_contDiff.comp ((contMDiff_iff_contDiff.mp foldBox_contMDiff).comp contDiff_snd))

/-! ## 2. The honest smoothness of the collapse family -/

/-- **The collapsed chart is a smooth family**: `(s, z) ↦ Q (colMap β s z)` is `C^∞` whenever `Q` is. -/
theorem contMDiff_colChart {β : ℝ → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβpos : ∀ t : ℝ, 0 < β t) {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q) :
    ContMDiff (modelWithCornersSelf ℝ (ℝ × ℂ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℂ => colChart β Q p.1 p.2) := by
  have hcol : ContMDiff (modelWithCornersSelf ℝ (ℝ × ℂ)) (modelWithCornersSelf ℝ ℂ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℂ => colMap β p.1 p.2) :=
    contMDiff_iff_contDiff.mpr (contDiff_colMap hβ hβpos)
  simpa only [colChart, Function.comp_def] using hQ.comp hcol

/-- **The honest joint smoothness of the collapsed plane**
`(s, u) ↦ colPlane β Q s u = Q (colMap β s (sqDisk (foldBox u)))`. -/
theorem contMDiff_colPlane {β : ℝ → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβpos : ∀ t : ℝ, 0 < β t) {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q) :
    ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => colPlane β Q p.1 p.2) := by
  have hcol : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => colMap β p.1 (sqDisk (foldBox p.2))) :=
    contMDiff_iff_contDiff.mpr (contDiff_colMap_sqDisk_fst hβ hβpos)
  simpa only [colPlane, colChart, diskPlane, Function.comp_def] using hQ.comp hcol

/-- **The same in the coordinate form** `(x 0, x 1, x 2) ↦ colPlane β Q (x 2) (mk2 (x 0) (x 1))`, the
shape in which the box parameter `x : ℝ³` presents the collapsed plane. -/
theorem contMDiff_colPlane_mk2 {β : ℝ → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβpos : ∀ t : ℝ, 0 < β t) {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 3) => colPlane β Q (p 2) (mk2 (p 0) (p 1))) := by
  have hcol : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : EuclideanSpace ℝ (Fin 3) => colMap β (p 2) (sqDisk (foldBox (mk2 (p 0) (p 1))))) :=
    contMDiff_iff_contDiff.mpr (contDiff_colMap_sqDisk_mk2 hβ hβpos)
  simpa only [colPlane, colChart, diskPlane, Function.comp_def] using hQ.comp hcol

/-! ## 3. The charted form: composing a smooth map into `M` with a chart of `M` -/

section ChartComp

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- **A charted smooth map is `C^∞` on the region where its values lie in the chart's source.**
This is the `ℝ⁴`-valued general-domain form of the proved
`Work.Drive.contMDiffOn_chart_comp` (which is stated for the domain `Amb 4`). -/
theorem contMDiffOn_chart_comp_of_contMDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → M) (hf : ContMDiff (modelWithCornersSelf ℝ X) (𝓡 4) Ctop f) (p : M) :
    ContMDiffOn (modelWithCornersSelf ℝ X) (𝓡 4) Ctop (fun x => chr p (f x))
      (f ⁻¹' (chr p).source) := by
  have hchart : ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
    have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
    simpa [chr] using h
  have hcomp := hchart.comp (hf.contMDiffOn (s := f ⁻¹' (chr p).source)) (fun x hx => hx)
  simpa [Function.comp_def] using hcomp

/-- **The global form**: if in addition the values of `f` lie in the chart's source *everywhere*,
then the charted map is `C^∞` on the whole domain — the shape in which the counting engine consumes
the charted chains. -/
theorem contDiff_chart_comp_of_resident {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → M) (hf : ContMDiff (modelWithCornersSelf ℝ X) (𝓡 4) Ctop f) (p : M)
    (hres : ∀ x, f x ∈ (chr p).source) :
    ContDiff ℝ Ctop (fun x => chr p (f x)) := by
  have h1 : ContMDiffOn (modelWithCornersSelf ℝ X) (𝓡 4) Ctop (fun x => chr p (f x)) Set.univ := by
    have hchart : ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
      have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
      simpa [chr] using h
    have hcomp := hchart.comp (hf.contMDiffOn (s := Set.univ)) (fun x _ => hres x)
    simpa [Function.comp_def] using hcomp
  exact contMDiff_iff_contDiff.mp (contMDiffOn_univ.mp h1)

end ChartComp

/-! ## 4. The four charted chains of the radial-collapse transport -/

/-- **The charted collapsed plane** is `C^∞` (in the uncurried product form used by the design). -/
theorem contDiff_chart_colPlane {β : ℝ → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβpos : ∀ t : ℝ, 0 < β t) {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    {q : CappingSpace}
    (hres : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ (chr q).source) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => chr q (colPlane β Q s u))) := by
  have h := contDiff_chart_comp_of_resident
    (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => colPlane β Q p.1 p.2)
    (contMDiff_colPlane hβ hβpos hQ) q (fun p => hres p.1 p.2)
  exact h

/-- **The charted disk presentation** is `C^∞`. -/
theorem contDiff_chart_diskPlane {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    {q : CappingSpace}
    (hres : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ (chr q).source) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin 2) => chr q (diskPlane Q u)) :=
  contDiff_chart_comp_of_resident (diskPlane Q) (contMDiff_diskPlane hQ) q hres

/-- **The charted clamped sweep** is `C^∞`. -/
theorem contDiff_chart_clampedSweep (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P) {q : CappingSpace}
    (hres : ∀ y : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P y ∈ (chr q).source) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 3) => chr q (clampedSweep c ψ P y)) :=
  contDiff_chart_comp_of_resident (clampedSweep c ψ P) (contMDiff_clampedSweep c ψ P hψ hP) q hres

/-! ## 5. The transport's first bullet with the smoothness inputs discharged -/

/-- **`Even (K 0 + K 1)` for the design's chains, with the four smoothness hypotheses of
`Work.Drive.even_ncard_colCount_zero_add_one` derived** from the honest smoothness of the chart and of
the two swept planes and the residency of the four chains' values in the chart's source.

The chart is the chart at a point `q` of the capping space (`Work.Drive.chr q`), and the set `A` of
the original statement is its source, so that the injectivity hypothesis is the chart's own
`OpenPartialHomeomorph.injOn`.  The remaining hypotheses are the geometric (`hcap`/`hcirc`/`hlev`) and
the genericity (`hreg`/`hface`) data, which the pair Sard analyser
(`Submission/Work/Drive/pairMeetSard.lean`) produces. -/
theorem even_ncard_colCount_zero_add_one_of_chart
    {β : ℝ → ℝ} {Q : ℂ → CappingSpace} {c : ℝ} {ψ : ℝ → ℝ}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace} {q : CappingSpace}
    (hβsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hQsm : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hψsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hP₁sm : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P₁)
    (hP₂sm : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P₂)
    (hβpos : ∀ t : ℝ, 0 < β t) (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) (hβ1 : β 1 = 1)
    (hc : 0 < c) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hPseam₁ : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₁ y = P₁ (seamInv2 y))
    (hPseam₂ : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₂ y = P₂ (seamInv2 y))
    (hEA : ∀ (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)), colPlane β Q s u ∈ (chr q).source)
    (hE'A : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u ∈ (chr q).source)
    (hVA : ∀ y : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₁ y ∈ (chr q).source)
    (hWA : ∀ z : EuclideanSpace ℝ (Fin 3), clampedSweep c ψ P₂ z ∈ (chr q).source)
    (hcap₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ < 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hcirc₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ = 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hcap₂ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ ≤ 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₂ y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (hreg : ∀ x ∈ Submission.Drive.unitBox 8,
      chartedPairDiff β Q c ψ P₁ P₂ (fun x => chr q x) x = 0 →
      Function.Surjective (fderiv ℝ (chartedPairDiff β Q c ψ P₁ P₂ (fun x => chr q x)) x))
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 8,
      chartedPairDiff β Q c ψ P₁ P₂ (fun x => chr q x) x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (chartedPairDiff β Q c ψ P₁ P₂ (fun x => chr q x)) x v.1)) :
    Even (colCount β Q (clampedSweep c ψ P₁) (clampedSweep c ψ P₂) 0
      + colCount β Q (clampedSweep c ψ P₁) (clampedSweep c ψ P₂) 1) := by
  have hsmE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun s u => (fun x => chr q x) (colPlane β Q s u))) :=
    contDiff_chart_colPlane hβsm hβpos hQsm hEA
  have hsmE' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => (fun x => chr q x) (diskPlane Q u)) :=
    contDiff_chart_diskPlane hQsm hE'A
  have hsmV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => (fun x => chr q x) (clampedSweep c ψ P₁ y)) :=
    contDiff_chart_clampedSweep c ψ P₁ hψsm hP₁sm hVA
  have hsmW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => (fun x => chr q x) (clampedSweep c ψ P₂ z)) :=
    contDiff_chart_clampedSweep c ψ P₂ hψsm hP₂sm hWA
  exact even_ncard_colCount_zero_add_one (chr := fun x => chr q x) (A := (chr q).source)
    hβpos hβ hβ1 hc hψ0 hψ1 hQseam hPseam₁ hPseam₂ (chr q).injOn hEA hE'A hVA hWA
    hsmE hsmE' hsmV hsmW hcap₁ hcirc₁ hcap₂ hlev hreg hface

/-! ## 6. The residency hypotheses, from the design's *box*-level data -/

/-- **The collapsed plane and the disk presentation live in the chart's disk**: their values are
`Q z` with `‖z‖ ≤ 1` (the collapse never increases the radius on the closed disk,
`Work.Drive.norm_colMap_le_one`). -/
lemma colPlane_mem_chartImage {β : ℝ → ℝ} (hβpos : ∀ t : ℝ, 0 < β t)
    (hβ : ∀ t : ℝ, Real.sqrt t ≤ β t) (Q : ℂ → CappingSpace) (s : ℝ)
    (u : EuclideanSpace ℝ (Fin 2)) :
    colPlane β Q s u ∈ Q '' {z : ℂ | ‖z‖ ≤ 1} :=
  ⟨colMap β s (sqDisk (foldBox u)),
    norm_colMap_le_one hβpos hβ s _ (norm_sqDisk_le_one _ (foldBox_mem_unitBox u)), rfl⟩

/-- **The charted collapsed plane is smooth as soon as the chart's disk is chart-resident** — the
hypothesis `∀ s u, colPlane β Q s u ∈ (chr q).source` of `Work.Drive.contDiff_chart_colPlane` is
derived from the single inclusion `Q '' closedBall 0 1 ⊆ (chr q).source`. -/
theorem contDiff_chart_colPlane_of_chartImage {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβpos : ∀ t : ℝ, 0 < β t)
    (hβsq : ∀ t : ℝ, Real.sqrt t ≤ β t) {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    {q : CappingSpace} (hres : Q '' {z : ℂ | ‖z‖ ≤ 1} ⊆ (chr q).source) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry (fun (s : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => chr q (colPlane β Q s u))) :=
  contDiff_chart_colPlane hβ hβpos hQ
    (fun s u => hres (colPlane_mem_chartImage hβpos hβsq Q s u))

/-- **The charted disk presentation is smooth** under the same single chart-residency inclusion. -/
theorem contDiff_chart_diskPlane_of_chartImage {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    {q : CappingSpace} (hres : Q '' {z : ℂ | ‖z‖ ≤ 1} ⊆ (chr q).source) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : EuclideanSpace ℝ (Fin 2) => chr q (diskPlane Q u)) :=
  contDiff_chart_diskPlane hQ
    (fun u => hres ⟨sqDisk (foldBox u), norm_sqDisk_le_one _ (foldBox_mem_unitBox u), rfl⟩)

/-- **The charted clamped sweep is smooth from *box*-level residency**: if the sweep's image on the
unit box lies in the chart's source and the cutoff's range is attained on `[0,1]`, then the whole
sweep's range lies in the source (`Work.Drive.clampedSweep_boxCover`), and
`Work.Drive.contDiff_chart_clampedSweep` applies.  (This is the form in which the design supplies the
residency: for the bounded cutoff `Work.Drive.cosCut` the box condition is the geometric disjointness
of the swept plane from the chart's disk, and the cutoff condition is `cosCut_mem_Icc`.) -/
theorem contDiff_chart_clampedSweep_of_box {c : ℝ} {ψ : ℝ → ℝ}
    {P : EuclideanSpace ℝ (Fin 2) → CappingSpace} (q : CappingSpace)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hψrange : ∀ t : ℝ, ∃ t' ∈ Set.Icc (0 : ℝ) 1, ψ t' = ψ t)
    (hPrange : ∀ y : EuclideanSpace ℝ (Fin 2),
      ∃ y' ∈ Submission.Drive.unitBox 1, P y' = P y)
    (hres : ∀ y ∈ Submission.Drive.unitBox 2, clampedSweep c ψ P y ∈ (chr q).source) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 3) => chr q (clampedSweep c ψ P y)) := by
  refine contDiff_chart_clampedSweep c ψ P hψ hP (fun y => ?_)
  obtain ⟨y', hy', hy⟩ := clampedSweep_boxCover (P := P) c ψ hPrange hψrange y
  rw [← hy]
  exact hres y' hy'

/-- **The transport's first bullet with *all* of its smoothness and residency inputs discharged from
the design's own geometric data.**  Compared with
`Work.Drive.even_ncard_colCount_zero_add_one_of_chart` the four residency hypotheses are gone: the
chart's disk image `Q '' {‖z‖ ≤ 1}` being contained in the chart's source covers the collapsed plane
and the disk presentation, and the sweeps need only their *box* images to be chart-resident, together
with the range conditions on the cutoff and on the two plane presentations. -/
theorem even_ncard_colCount_zero_add_one_of_data
    {β : ℝ → ℝ} {Q : ℂ → CappingSpace} {c : ℝ} {ψ : ℝ → ℝ}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace} {q : CappingSpace}
    (hβsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβpos : ∀ t : ℝ, 0 < β t)
    (hβsq : ∀ t : ℝ, Real.sqrt t ≤ β t) (hβ1 : β 1 = 1)
    (hQsm : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hψsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hP₁sm : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P₁)
    (hP₂sm : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P₂)
    (hψrange : ∀ t : ℝ, ∃ t' ∈ Set.Icc (0 : ℝ) 1, ψ t' = ψ t)
    (hP₁range : ∀ y : EuclideanSpace ℝ (Fin 2),
      ∃ y' ∈ Submission.Drive.unitBox 1, P₁ y' = P₁ y)
    (hP₂range : ∀ y : EuclideanSpace ℝ (Fin 2),
      ∃ y' ∈ Submission.Drive.unitBox 1, P₂ y' = P₂ y)
    (hresQ : Q '' {z : ℂ | ‖z‖ ≤ 1} ⊆ (chr q).source)
    (hresV : ∀ y ∈ Submission.Drive.unitBox 2, clampedSweep c ψ P₁ y ∈ (chr q).source)
    (hresW : ∀ y ∈ Submission.Drive.unitBox 2, clampedSweep c ψ P₂ y ∈ (chr q).source)
    (hc : 0 < c) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hPseam₁ : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₁ y = P₁ (seamInv2 y))
    (hPseam₂ : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₂ y = P₂ (seamInv2 y))
    (hcap₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ < 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hcirc₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ = 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₁ y)
    (hcap₂ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)),
      ‖z‖ ≤ 1 → ‖sqDisk (foldBox y)‖ < 1 → Q z ≠ P₂ y)
    (hlev : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c)
    (hreg : ∀ x ∈ Submission.Drive.unitBox 8,
      chartedPairDiff β Q c ψ P₁ P₂ (fun x => chr q x) x = 0 →
      Function.Surjective (fderiv ℝ (chartedPairDiff β Q c ψ P₁ P₂ (fun x => chr q x)) x))
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 8,
      chartedPairDiff β Q c ψ P₁ P₂ (fun x => chr q x) x = 0 →
      ∃ i : Fin 9, (x i = 0 ∨ x i = 1) ∧ (∀ j : Fin 9, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v i = 0} =>
          fderiv ℝ (chartedPairDiff β Q c ψ P₁ P₂ (fun x => chr q x)) x v.1)) :
    Even (colCount β Q (clampedSweep c ψ P₁) (clampedSweep c ψ P₂) 0
      + colCount β Q (clampedSweep c ψ P₁) (clampedSweep c ψ P₂) 1) :=
  even_ncard_colCount_zero_add_one_of_chart hβsm hQsm hψsm hP₁sm hP₂sm hβpos hβsq hβ1
    hc hψ0 hψ1 hQseam hPseam₁ hPseam₂
    (fun s u => hresQ (colPlane_mem_chartImage hβpos hβsq Q s u))
    (fun u => hresQ ⟨sqDisk (foldBox u), norm_sqDisk_le_one _ (foldBox_mem_unitBox u), rfl⟩)
    (fun y => by
      obtain ⟨y', hy', hy⟩ := clampedSweep_boxCover (P := P₁) c ψ hP₁range hψrange y
      rw [← hy]; exact hresV y' hy')
    (fun z => by
      obtain ⟨z', hz', hz⟩ := clampedSweep_boxCover (P := P₂) c ψ hP₂range hψrange z
      rw [← hz]; exact hresW z' hz')
    hcap₁ hcirc₁ hcap₂ hlev hreg hface

end

end Work.Drive
