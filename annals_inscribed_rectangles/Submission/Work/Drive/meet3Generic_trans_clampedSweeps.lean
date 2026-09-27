import Mathlib
import Submission.Work.Drive.sweepTransversalityContMDiff
import Submission.Work.Drive.projChartIndexOf

/-!
# The transversality field of `Meet3Generic` for three radial sweeps, from plane conditions

`Work.Drive.Meet3Generic.trans` asks, at every triple point `x` of the three parameter cubes, for the
manifold transversality of the three chains.  For the radial sweeps `clampedSweep (c k) ψ (P k)` this
is `Work.Drive.tripleTransverse_clampedSweeps_of_contMDiff`.  This file assembles that reduction into

* the **pointwise** statement (`meet3Generic_trans_clampedSweeps_pointwise`) and
* the **uniform** statement producing exactly the type of the `trans` field of `Meet3Generic`
  (`meet3Generic_trans_clampedSweeps`),

taking the chart index to be the *canonical* one (`Work.Drive.projChartIndexOf`, so the chart
compatibility is `rfl`) and discharging all auxiliary differentiability data from
`ContMDiff (𝓡 2) (𝓡 4) Ctop (P k)`.

What remains as *hypotheses* is exactly

* `ha` — the radial coefficient `deriv ψ (x k 2) · (log (c k) − log (levelOf (P k ·)))` is non-zero at
  the triple point (so the three derivative images really contain the radial direction);
* `hc` — the class derivative `Work.Drive.planeClassDeriv` of each plane is injective at the triple
  point (each plane presentation is an immersion);
* `hV` — the three class `2`-planes at the triple point are in general position in `T ℝP³`.

These are statements about the **planes** `P k` and the cutoff `ψ`, not about the sweeps — the
geometric input of the route (`GENERICITY_INTERFACE_STATUS.md` §3bis, §4bis B).
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold Topology Filter

noncomputable section

set_option maxHeartbeats 8000000

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

/-- The canonical class-derivative of the plane `P k` at a triple point `x`, in the canonical
projective chart of the class of its sweep. -/
noncomputable def planeClassDeriv
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (k : Fin 3) (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) =>
    Work.Drive.projChartMap (Work.Drive.projChartIndexOf ((Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2))
    ((Work.Drive.cappingSpaceHomeoProj (P k y)).2))
    (Work.Drive.mk2 (x k 0) (x k 1))

/-- **Pointwise transversality of three radial sweeps** at a triple point, from the two conditions on
the planes. -/
theorem meet3Generic_trans_clampedSweeps_pointwise
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (x : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (hpt : ∀ k, Work.Drive.clampedSweep (c k) ψ (P k) (x k)
      = Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0))
    (ha : ∀ k, deriv ψ (x k 2) * (Real.log (c k) - Real.log
      (Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1))))) ≠ 0)
    (hc : ∀ k, Function.Injective (planeClassDeriv c ψ P k x))
    (hV : (planeClassDeriv c ψ P 0 x).range ⊓ (planeClassDeriv c ψ P 1 x).range
      ⊓ (planeClassDeriv c ψ P 2 x).range = ⊥) :
    TripleTransverse
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 0) ψ (P 0)) (x 0))
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 1) ψ (P 1)) (x 1))
      (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 2) ψ (P 2)) (x 2)) := by
  have hchart2 : ∀ k, (@chartAt (EuclideanSpace ℝ (Fin 3)) _
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) _
      (Work.Drive.projCharted 3) (Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2 :
      OpenPartialHomeomorph (Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
        (EuclideanSpace ℝ (Fin 3)))
      = Work.Drive.projChart (Work.Drive.projChartIndexOf ((Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2)) :=
    fun k => Work.Drive.projCharted_chartAt_eq_projChart _
  exact Work.Drive.tripleTransverse_clampedSweeps_of_contMDiff c ψ P
    (fun k => Work.Drive.projChartIndexOf ((Work.Drive.cappingSpaceHomeoProj
      (Work.Drive.clampedSweep (c k) ψ (P k) (x k))).2))
    hψ hP x hpt hchart2 ha hc hV

/-- **Transversality of three radial sweeps at every triple point**, in exactly the form of the
`trans` field of `Work.Drive.Meet3Generic`. -/
theorem meet3Generic_trans_clampedSweeps
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hψ : ContDiff ℝ Work.Drive.Ctop ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (P k))
    (ha : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, deriv ψ (x k 2) * (Real.log (c k) - Real.log
          (Work.Drive.levelOf (P k (Work.Drive.mk2 (x k 0) (x k 1))))) ≠ 0)
    (hc : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        ∀ k, Function.Injective (planeClassDeriv c ψ P k x))
    (hV : ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
        (∀ k, x k ∈ Submission.Drive.unitBox 2) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
        Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
          = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
        (planeClassDeriv c ψ P 0 x).range ⊓ (planeClassDeriv c ψ P 1 x).range
          ⊓ (planeClassDeriv c ψ P 2 x).range = ⊥) :
    ∀ x : Fin 3 → EuclideanSpace ℝ (Fin 3),
      (∀ k, x k ∈ Submission.Drive.unitBox 2) →
      Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
        = Work.Drive.clampedSweep (c 1) ψ (P 1) (x 1) →
      Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0)
        = Work.Drive.clampedSweep (c 2) ψ (P 2) (x 2) →
      TripleTransverse
        (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 0) ψ (P 0)) (x 0))
        (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 1) ψ (P 1)) (x 1))
        (mfderiv (𝓡 3) (𝓡 4) (Work.Drive.clampedSweep (c 2) ψ (P 2)) (x 2)) := by
  intro x hx h01 h02
  have hpt : ∀ k, Work.Drive.clampedSweep (c k) ψ (P k) (x k)
      = Work.Drive.clampedSweep (c 0) ψ (P 0) (x 0) := by
    intro k
    fin_cases k
    · rfl
    · exact h01.symm
    · exact h02.symm
  exact meet3Generic_trans_clampedSweeps_pointwise c ψ P hψ hP x hpt
    (ha x hx h01 h02) (hc x hx h01 h02) (hV x hx h01 h02)

end

end Work.Drive
