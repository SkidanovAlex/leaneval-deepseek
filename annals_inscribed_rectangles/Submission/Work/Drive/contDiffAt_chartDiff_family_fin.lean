import Mathlib
import Submission.Work.Drive.ChartBridge

/-!
# Joint smoothness of the parametrised charted difference map of two chains

`Work.Drive.chartDiff p D N` is the local model of the intersection problem of a `2`-chain
`D : ℝ² → M` and a `3`-chain `N : ℝ³ → M` in a smooth `4`-manifold `M`, charted at `p`:

`chartDiff p D N : Amb 4 → Tgt 4,  x ↦ φ (D (sqPart x)) − φ (N (cbPart x))`.

Here the `3`-chain is not fixed but varies with a parameter `t : ℝ^m`: `N = G t ·`, where
`(t, v) ↦ G t v` is a `C^∞` family of chains.  This file proves the **joint smoothness** of the
parametrised charted difference map

`(q : ℝ^m × Amb 4) ↦ chartDiff p D (G q.1) q.2`

at a parameter value `t₀` and a box point `y₀`, under the (local) hypotheses that
`D (sqPart y₀)` and `G t₀ (cbPart y₀)` both lie in the source of the chart at `p`.  That hypothesis
is exactly what makes the two chart compositions smooth at the relevant image points; the rest is
the chain rule.

The parameter `q.1` enters only through the second chain, so the argument is the one-parameter one
verbatim with `ℝ` replaced by `EuclideanSpace ℝ (Fin m)` — this is what a parametric-Sard argument
needs (`m ≥ 4` for a map `ℝ^m × ℝ⁵ → ℝ⁴`).

Non-vacuous: for `m = 0` the parameter space is a point and the statement is just the smoothness of
`chartDiff p D (G 0)` at `y₀`; `hreg` is the natural hypothesis, since the charted difference map
is only meaningful while the values lie in the chart source. -/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option linter.unusedSectionVars false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop M]

/-- The block projection as a continuous linear map on the product: `(q : ℝ^m × ℝ⁵) ↦ sqPart q.2`,
i.e. `D` is composed with this. -/
private def famSqCLM (m : ℕ) :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  sqPartCLM.comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin 5)))

private lemma famSqCLM_apply (m : ℕ)
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5)) :
    famSqCLM m q = sqPart q.2 := by
  simp [famSqCLM]

/-- The block projection as a continuous linear map on the product:
`(q : ℝ^m × ℝ⁵) ↦ (q.1, cbPart q.2)`, i.e. the parameter is kept and `G` is composed with this. -/
private def famCbCLM (m : ℕ) :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) →L[ℝ]
      EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.prod
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 5)))
    (cbPartCLM.comp (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin 5))))

private lemma famCbCLM_apply (m : ℕ)
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5)) :
    famCbCLM m q = (q.1, cbPart q.2) := by
  simp [famCbCLM]

/-- The fixed chain `D`, as a map on the parameter space `ℝ^m × ℝ⁵`. -/
private lemma contMDiff_famSq (m : ℕ) (D : EuclideanSpace ℝ (Fin 2) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Ctop D) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) => D (sqPart q.2)) := by
  have h := hD.comp ((famSqCLM m).contMDiff (n := Ctop))
  simpa [Function.comp_def, famSqCLM_apply] using h

/-- The parametrised chain `G`, as a map on the parameter space `ℝ^m × ℝ⁵`. -/
private lemma contMDiff_famCb (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) => G q.1 (cbPart q.2)) := by
  have h := hG.comp ((famCbCLM m).contMDiff (n := Ctop))
  simpa [Function.comp_def, famCbCLM_apply] using h

/-- The chart `chr p` is `C^∞` on its source, in the manifold sense. -/
private lemma contMDiffOn_chr (p : M) :
    ContMDiffOn (𝓡 4) (𝓡 4) Ctop (chr p) (chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := Ctop)
  simpa [chr] using h

/-- **A charted smooth family map is jointly smooth** at every point whose value lies in the chart
source. -/
private lemma contDiffAt_chart_fam (m : ℕ)
    (f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) → M)
    (hf : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))) (𝓡 4) Ctop f)
    (p : M) (q₀ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5))
    (hreg : f q₀ ∈ (chr p).source) :
    ContDiffAt ℝ Ctop (fun q => (chr p) (f q)) q₀ := by
  have h1 : ContMDiffAt (𝓡 4) (𝓡 4) Ctop (chr p) (f q₀) :=
    (contMDiffOn_chr p).contMDiffAt ((chr p).open_source.mem_nhds hreg)
  exact contMDiffAt_iff_contDiffAt.mp (h1.comp q₀ hf.contMDiffAt)

/-- **Joint smoothness of the parametrised charted difference map of a fixed `2`-chain and a smooth
family of `3`-chains, for a multidimensional parameter.**

The map `q ↦ chartDiff p D (G q.1) q.2` is `C^∞` at `(t₀, y₀)` as soon as the two image values
`D (sqPart y₀)` and `G t₀ (cbPart y₀)` lie in the source of the chart at `p`.  Both chart
compositions are smooth there by the chain rule (`contDiffAt_chart_fam`), and `chartDiff` is their
difference. -/
theorem contDiffAt_chartDiff_family_fin (m : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (p : M) (t₀ : EuclideanSpace ℝ (Fin m)) {y₀ : Work.Drive.Amb 4}
    (hreg : D (Work.Drive.sqPart y₀) ∈ (Work.Drive.chr p).source ∧
      G t₀ (Work.Drive.cbPart y₀) ∈ (Work.Drive.chr p).source) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
        Work.Drive.chartDiff p D (G q.1) q.2) (t₀, y₀) := by
  have h1 : ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
        (chr p) (D (sqPart q.2))) (t₀, y₀) :=
    contDiffAt_chart_fam m _ (contMDiff_famSq m D hD) p (t₀, y₀) hreg.1
  have h2 : ContDiffAt ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 5) =>
        (chr p) (G q.1 (cbPart q.2))) (t₀, y₀) :=
    contDiffAt_chart_fam m _ (contMDiff_famCb m G hG) p (t₀, y₀) hreg.2
  exact h1.sub h2

end

end Work.Drive
