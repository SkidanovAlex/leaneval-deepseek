import Mathlib
import Submission.Work.Drive.sideGerm
import Submission.Work.Drive.exists_chartPert

/-!
# The `hsurj` brick for the chart-perturbed clamped sweeps (design language)

The germ design of the lead's 14:15 message perturbs the **plane presentations**
(`Q ↦ Ξ t ∘ Q`, `Ξ` a `Work.Drive.ChartPert`) and keeps the chains as *clamped sweeps*, so the
parametric-Sard engines that must produce `Meet3Hyp` / `GoodPair` at a generic parameter are applied to
the family

> `t ↦ fun y ↦ clampedSweep c (1 - ·) (Ξ t ∘ diskPlane Q) y`

and their `hsurj` hypothesis is the surjectivity of the parameter-derivative of this family.  This file
records that statement as a **predicate** (`SweepPertSurj`), so that it can be delegated and consumed
without repeating the manifold instances of the capping space, and states the brick that the `ChartPert`
instance of `Work.Drive.exists_chartPert` produces it.

The mechanism (see the docstring of `sweepPertSurj_of_chartPert`): the family is the composite of
`t ↦ Ξ t (diskPlane Q (mk2 y))` — onto by `ChartPert` — with the fixed map
`G q = scaleCapping (exp (ψ (y 2) (log c - log (levelOf q)))) q`, whose differential in the (level,
class) coordinates of the capping space is diagonal with entries `(c / l) ^ (1 - y 2) * y 2 ≠ 0` (level)
and `id` (class); hence `G` is a local diffeomorphism precisely when `y 2 ≠ 0` (at `y 2 = 1` it is the
identity, so no direction is lost there either — the condition `y 2 ∈ (0,1)` of the definition is the
*interiority* hypothesis the counting engines consume, and it is stronger than what the argument
needs).
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The `hsurj` brick for chart-perturbed clamped sweeps** (instance-free form): for every
`ChartPert` `Ξ` of a plane chart `Q`, every level `c > 0`, every sweep parameter `y` of the box whose
third coordinate is *interior* (`y 2 ∈ (0,1)`) and every parameter `t`, the parameter-derivative of
`t' ↦ clampedSweep c (fun s => 1 - s) (fun z => Ξ t' (diskPlane Q z)) y` at `t` is surjective. -/
def SweepPertSurj (Q : ℂ → CappingSpace) (m : ℕ)
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (y : EuclideanSpace ℝ (Fin 3))
    (_hy : y ∈ Submission.Drive.unitBox 2) (_hy2 : y 2 ∈ Set.Ioo (0 : ℝ) 1)
    (t : EuclideanSpace ℝ (Fin m)),
    Function.Surjective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (fun t' => clampedSweep c (fun s => 1 - s) (fun z => Ξ t' (diskPlane Q z)) y) t)

/-- **The charted derivative is onto as soon as the manifold derivative is.**  This is the bridge that
turns the manifold-level bricks (`SweepPertSurj`, `surjective_mfderiv_dil`, the `ChartPert` orbit) into
the `hsurj` hypothesis of the parametric-Sard engines, whose derivations are *charted*
(`Work.Drive.TParity.chartDiff3`). -/
theorem surjective_fderiv_chart_comp {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → CappingSpace}
    (p : CappingSpace)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {s : EuclideanSpace ℝ (Fin n)} (hs : f s ∈ (chr p).source)
    (h : Function.Surjective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) f s)) :
    Function.Surjective (fderiv ℝ (fun u => chr p (f u)) s) := by
  rw [Work.Drive.fderiv_chart_comp f hf p hs]
  -- the change of coordinates is injective, hence (in the same dimension) surjective
  have hinj : Function.Injective
      (tangentCoordChange (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (f s) p (f s)) := by
    refine Work.Drive.tangentCoordChange_injective (x := f s) (y := p) (z := f s) ⟨?_, ?_⟩
    · exact mem_extChartAt_source (f s)
    · rw [extChartAt_source]
      exact hs
  have hsurj : Function.Surjective
      (tangentCoordChange (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (f s) p (f s)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (tangentCoordChange (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (f s) p (f s)).toLinearMap) (by simp)).mp hinj
  intro w
  obtain ⟨v, hv⟩ := hsurj w
  obtain ⟨u, hu⟩ := h v
  refine ⟨u, ?_⟩
  show (tangentCoordChange (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (f s) p (f s))
    ((mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) f s) u) = w
  rw [hu, hv]

end

end Work.Drive
