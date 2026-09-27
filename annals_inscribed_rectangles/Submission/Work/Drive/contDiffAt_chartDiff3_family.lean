import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.ChartDeriv

/-!
# Smoothness of the charted difference map of a smooth family of triples

`Work.Drive.TParity.chartDiff3 p D` is the charted difference map of three chains
`D 0, D 1, D 2 : ℝ³ → M`: in the chart at `p` it sends `x` to the stacked pair
`(φ (D₀ x₀) − φ (D₁ x₁), φ (D₀ x₀) − φ (D₂ x₂))`.

Here `D` is not fixed but varies with a parameter `t ∈ ℝ`: `D k = G t k`, where
`(t, v) ↦ G t k v` is a `C^∞` family of chains.  The lemma proved below is the joint smoothness
of the parametrised charted difference map

`(t, y) ↦ chartDiff3 p (G t) y`

at a parameter value `t₀` and a point `y₀` of the nine-box, under the (local) hypothesis that for
each `k` the image point `G t₀ k (bPartC k y₀)` lies in the source of the chart at `p`.  That
hypothesis is exactly what makes the chart `chr p` smooth at the three relevant image points; the
rest is the chain rule.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option linter.unusedSectionVars false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]

/-- The block projection as a continuous linear map on the product: `(t, y) ↦ (t, bPartC k y)`. -/
private def famPartCLM (k : Fin 3) :
    ℝ × EuclideanSpace ℝ (Fin 9) →L[ℝ] ℝ × EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 9)))
    ((TParity.bPartC k).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 9))))

private lemma famPartCLM_apply (k : Fin 3) (q : ℝ × EuclideanSpace ℝ (Fin 9)) :
    famPartCLM k q = (q.1, TParity.bPartC k q.2) := by
  simp [famPartCLM]

/-- The `k`-th chain of the family, as a map on the parameter space `ℝ × ℝ⁹`. -/
private lemma contMDiff_famChain (G : ℝ → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => G p.1 k p.2)) (k : Fin 3) :
    ContMDiff (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 9))) (𝓡 4) Ctop
      (fun q : ℝ × EuclideanSpace ℝ (Fin 9) => G q.1 k (TParity.bPartC k q.2)) := by
  have h := (hG k).comp ((famPartCLM k).contMDiff (n := Ctop))
  simpa [Function.comp_def, famPartCLM_apply] using h

/-- The chart `chr p` is `C^∞` on its source, in the manifold sense. -/
private lemma contMDiffOn_chr (p : M) :
    ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
  simpa [chr] using h

/-- **A single charted component of the family is smooth.** -/
private lemma contDiffAt_chart_famChain
    (G : ℝ → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => G p.1 k p.2))
    (p : M) (t₀ : ℝ) {y₀ : EuclideanSpace ℝ (Fin 9)} (k : Fin 3)
    (hreg : G t₀ k (TParity.bPartC k y₀) ∈ (chr p).source) :
    ContDiffAt ℝ Ctop
      (fun q : ℝ × EuclideanSpace ℝ (Fin 9) => (chr p) (G q.1 k (TParity.bPartC k q.2)))
      (t₀, y₀) := by
  have h1 : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p) (G t₀ k (TParity.bPartC k y₀)) :=
    (contMDiffOn_chr p).contMDiffAt ((chr p).open_source.mem_nhds hreg)
  have h2 := (contMDiff_famChain G hG k).contMDiffAt (x := (t₀, y₀))
  exact contMDiffAt_iff_contDiffAt.mp (h1.comp (t₀, y₀) h2)

/-- **The parametrised charted difference map of three chains is smooth.**
This is the family version of `Work.Drive.TParity.contDiffOn_chartDiff3`: the parameter `t` enters
through the chains `G t k`. -/
theorem contDiffAt_chartDiff3_family
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (G : ℝ → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => G p.1 k p.2))
    (p : M) (t₀ : ℝ) {y₀ : EuclideanSpace ℝ (Fin 9)}
    (hreg : ∀ k : Fin 3,
      G t₀ k (Work.Drive.TParity.bPartC k y₀) ∈ (Work.Drive.chr p).source) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × EuclideanSpace ℝ (Fin 9) =>
        Work.Drive.TParity.chartDiff3 p (G q.1) q.2) (t₀, y₀) := by
  have hC : ∀ k : Fin 3, ContDiffAt ℝ Ctop
      (fun q : ℝ × EuclideanSpace ℝ (Fin 9) =>
        (chr p) (G q.1 k (TParity.bPartC k q.2))) (t₀, y₀) :=
    fun k => contDiffAt_chart_famChain G hG p t₀ k (hreg k)
  have hA := (hC 0).sub (hC 1)
  have hB := (hC 0).sub (hC 2)
  have hpair := hA.prodMk hB
  have hcomp := (TParity.pUpCLM.contDiff.contDiffAt).comp (t₀, y₀) hpair
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards with q
  simp [TParity.chartDiff3, TParity.pUpCLM_apply]

end

end Work.Drive
