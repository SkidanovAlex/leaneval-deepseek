import Mathlib
import Submission.Work.Tubular.TubeBasic
import Submission.Work.ThomBordism.ambientLocalDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- If a nonzero multiple `c • vec p` of the normal vector of `p`, added to the base point
`E.e p.1.1`, reaches `E.e x`, and the rescaled point `radialRescale E (fun _ => c) p` still lies in
the closed `ε`-disc bundle, then `p` itself lies above `E.e x`: `tubeMap E p = E.e x`. -/
theorem chartBlowUp_core {V : Work.ThomBordism.Man8} {k : ℕ}
    {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ε c : ℝ} (C : Work.Tubular.TubeChart E ε) {x : V.pt} {p : Work.Tubular.NormalTotal E}
    (hc : c ≠ 0)
    (h : Work.Tubular.tubeMap E (Work.ThomBordism.radialRescale E (fun _ => c) p) = E.e x)
    (hle : |c| * Work.Tubular.normalNorm E p ≤ ε) :
    Work.Tubular.tubeMap E p = E.e x := by
  -- The zero-section point of the tube over `x`.
  have hz : Work.Tubular.tubeMap E
      (⟨(x, (0 : Work.Tubular.Euc (8 + k))), (Work.Tubular.normalSpace E x).zero_mem⟩ :
        Work.Tubular.NormalTotal E) = E.e x := by
    rw [Work.Tubular.tubeMap_mk]; simp
  have hzn : Work.Tubular.normalNorm E
      (⟨(x, (0 : Work.Tubular.Euc (8 + k))), (Work.Tubular.normalSpace E x).zero_mem⟩ :
        Work.Tubular.NormalTotal E) ≤ ε := by
    rw [Work.Tubular.normalNorm_mk]; simpa using le_of_lt C.eps_pos
  -- The rescaled point still lies in the closed disc bundle.
  have hqn : Work.Tubular.normalNorm E
      (Work.ThomBordism.radialRescale E (fun _ => c) p) ≤ ε := by
    rw [Work.ThomBordism.normalNorm_radialRescale]
    exact hle
  -- Both points are `C.inv (E.e x)`.
  have h1 : C.inv (E.e x)
      = (⟨(x, (0 : Work.Tubular.Euc (8 + k))), (Work.Tubular.normalSpace E x).zero_mem⟩ :
          Work.Tubular.NormalTotal E) := by
    rw [← hz]; exact C.inv_tubeMap _ hzn
  have h2 : C.inv (E.e x) = Work.ThomBordism.radialRescale E (fun _ => c) p := by
    rw [← h]; exact C.inv_tubeMap _ hqn
  have hq : Work.ThomBordism.radialRescale E (fun _ => c) p
      = (⟨(x, (0 : Work.Tubular.Euc (8 + k))), (Work.Tubular.normalSpace E x).zero_mem⟩ :
          Work.Tubular.NormalTotal E) := h2 ▸ h1
  -- Read off the two components.
  have hproj : p.1.1 = x := by
    have := congrArg (fun r : Work.Tubular.NormalTotal E => r.1.1) hq
    simpa using this
  have hvec : p.1.2 = 0 := by
    have hc0 : c • p.1.2 = 0 := by
      have := congrArg (fun r : Work.Tubular.NormalTotal E => r.1.2) hq
      simpa [Work.ThomBordism.radialRescale_coe] using this
    have := congrArg (fun u => c⁻¹ • u) hc0
    rwa [inv_smul_smul₀ hc, smul_zero] at this
  show E.e p.1.1 + p.1.2 = E.e x
  rw [hproj, hvec, add_zero]

end Work.ThomBordism
