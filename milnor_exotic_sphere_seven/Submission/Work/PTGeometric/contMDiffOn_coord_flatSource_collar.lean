import Mathlib
import Submission.Work.PTGeometric.SourceFamily
import Submission.Work.PTGeometric.SourceNull
import Submission.Work.PTGeometric.flatCoordModel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology unitInterval
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

theorem contMDiffOn_coord_flatSource_collar {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, Work.PTGeometric.tubeAlpha (G.rep i)) ^ m = 1)
    {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (e : M → EuclideanSpace ℝ (Fin ((8 + k) + 1)))
    (he : ContMDiff (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin ((8 + k) + 1))))
      ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (hne : ∀ x : M, Work.PTGeometric.flatSourceHomotopy8 (k := k)
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
      (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ (e x) ≠ D.t₀) :
    ContMDiffOn (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ
        (EndOp (k + G.mU) × Amb (k + G.mU)))
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : M => G.coord ⟨Work.PTGeometric.flatSourceHomotopy8 (k := k)
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).H
        (Work.PTGeometric.familySource (D := D) (Fam := Fam) G m hpow).φ (e x), hne x⟩)
      {x : M | e x 0 < 1 / 2} := by
  set S := familySource (D := D) (Fam := Fam) G m hpow with hS
  intro x₀ hx₀
  obtain ⟨V, hVopen, hVmem, Ψ, hΨsm, hΨeq⟩ :=
    exists_local_smooth_model (G := G) m hpow (e x₀) hx₀ (hne x₀)
  have hVnhds : V ∈ 𝓝 (e x₀) := hVopen.mem_nhds hVmem
  have heV : e ⁻¹' V ∈ 𝓝 x₀ := he.continuous.continuousAt.preimage_mem_nhds hVnhds
  have hΨat : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin ((8 + k) + 1)))
      𝓘(ℝ, EndOp (k + G.mU) × Amb (k + G.mU)) ∞ Ψ (e x₀) :=
    (hΨsm (e x₀) hVmem).contMDiffAt hVnhds
  have hcomp : ContMDiffAt (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      𝓘(ℝ, EndOp (k + G.mU) × Amb (k + G.mU)) ∞ (fun x : M => Ψ (e x)) x₀ :=
    hΨat.comp x₀ he.contMDiffAt
  refine (hcomp.contMDiffWithinAt).congr_of_eventuallyEq ?_ ?_
  · rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨e ⁻¹' V ∩ {x : M | e x 0 < 1 / 2},
      Filter.inter_mem (nhdsWithin_le_nhds heV) self_mem_nhdsWithin, ?_⟩
    rintro x ⟨hx, -⟩
    exact hΨeq (e x) hx (hne x)
  · exact hΨeq (e x₀) hVmem (hne x₀)

end Work.PTGeometric
