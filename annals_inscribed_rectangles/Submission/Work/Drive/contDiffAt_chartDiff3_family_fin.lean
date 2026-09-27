import Mathlib
import Submission.Work.Drive.contDiffAt_chartDiff3_family

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option linter.unusedSectionVars false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]

/-- The block projection as a continuous linear map on the product: `(t, y) ↦ (t, bPartC k y)`,
for a parameter space `EuclideanSpace ℝ (Fin m)`. -/
private def famPartCLM (m : ℕ) (k : Fin 3) :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) →L[ℝ]
      EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 9)))
    ((TParity.bPartC k).comp
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 9))))

private lemma famPartCLM_apply (m : ℕ) (k : Fin 3)
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9)) :
    famPartCLM m k q = (q.1, TParity.bPartC k q.2) := by
  simp [famPartCLM]

/-- The `k`-th chain of the family, as a map on the parameter space
`EuclideanSpace ℝ (Fin m) × ℝ⁹`. -/
private lemma contMDiff_famChain (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G p.1 k p.2))
    (k : Fin 3) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        G q.1 k (TParity.bPartC k q.2)) := by
  have h := (hG k).comp ((famPartCLM m k).contMDiff (n := Ctop))
  simpa [Function.comp_def, famPartCLM_apply] using h

/-- The chart `chr p` is `C^∞` on its source, in the manifold sense. -/
private lemma contMDiffOn_chr (p : M) :
    ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
  simpa [chr] using h

/-- **A single charted component of the family is smooth.** -/
private lemma contDiffAt_chart_famChain (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G p.1 k p.2))
    (p : M) (t₀ : EuclideanSpace ℝ (Fin m)) {y₀ : EuclideanSpace ℝ (Fin 9)} (k : Fin 3)
    (hreg : G t₀ k (TParity.bPartC k y₀) ∈ (chr p).source) :
    ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (chr p) (G q.1 k (TParity.bPartC k q.2)))
      (t₀, y₀) := by
  have h1 : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p) (G t₀ k (TParity.bPartC k y₀)) :=
    (contMDiffOn_chr p).contMDiffAt ((chr p).open_source.mem_nhds hreg)
  have h2 := (contMDiff_famChain m G hG k).contMDiffAt
    (x := (t₀, y₀))
  exact contMDiffAt_iff_contDiffAt.mp (h1.comp (t₀, y₀) h2)

/-- **Joint smoothness of the parametrised charted difference map of three chains, for a multidimensional parameter.**

`Work.Drive.contDiffAt_chartDiff3_family` proves that for a *one*-parameter family `G : ℝ → Fin 3 → ℝ³ → M` of triples of smooth chains, the map `(t, y) ↦ chartDiff3 p (G t) y` is smooth at every point `(t₀, y₀)` at which the three values `G t₀ k (bPartC k y₀)` lie in the chart source.  A parametric-Sard argument, however, needs a parameter space of dimension at least the dimension of its target (`8` for the counting route, where `Φ : ℝ^m × ℝ⁹ → ℝ⁸`), so the one-parameter statement has to be available for `m` parameters.

This is the same statement with `ℝ` replaced by `EuclideanSpace ℝ (Fin m)`, and the same proof verbatim: the parameter enters only through `G q.1 k`, so the one-parameter argument (compose the smooth chart map `chr p` with the jointly smooth family map, then observe that `pUpCLM` is continuous linear) localises to the multidimensional parameter space unchanged.  Note that the helpers `famPartCLM`, `contMDiffOn_chr`, `contDiffAt_chart_famChain` are `private` in the imported file and must be re-declared (generalised) here.

Non-vacuous: for `m = 1` this is `Work.Drive.contDiffAt_chartDiff3_family` up to the identification `EuclideanSpace ℝ (Fin 1) ≃ ℝ`; `hreg` is the natural hypothesis (the charted difference map is only meaningful while the values are in the chart source). -/
theorem contDiffAt_chartDiff3_family_fin (m : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (p : M) (t₀ : EuclideanSpace ℝ (Fin m)) {y₀ : EuclideanSpace ℝ (Fin 9)}
    (hreg : ∀ k : Fin 3, G t₀ k (Work.Drive.TParity.bPartC k y₀) ∈ (Work.Drive.chr p).source) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        Work.Drive.TParity.chartDiff3 p (G q.1) q.2) (t₀, y₀) := by
  have hC : ∀ k : Fin 3, ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (chr p) (G q.1 k (TParity.bPartC k q.2))) (t₀, y₀) :=
    fun k => contDiffAt_chart_famChain m G hG p t₀ k (hreg k)
  have hA := (hC 0).sub (hC 1)
  have hB := (hC 0).sub (hC 2)
  have hpair := hA.prodMk hB
  have hcomp := (TParity.pUpCLM.contDiff.contDiffAt).comp (t₀, y₀) hpair
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards with q
  simp [TParity.chartDiff3, TParity.pUpCLM_apply]

end

end Work.Drive
