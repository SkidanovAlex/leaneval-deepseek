import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.GATE2.EXL.MinCrossing

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.EXL

/-- **The `α`-deviation of a ray point of angle `θ ∈ (α - 1/2, α)` for the canonical critical
Böttcher coordinate `varphiCrit c`.**

On the escape set of a parameter `c ∈ Mandelbar` the canonical critical Böttcher coordinate
`Work.Bottcher.varphiCrit c` agrees with the dynamical Böttcher coordinate `φ` of the datum
`hN : Work.EL.DynB c φ` (`Work.Bottcher.varphiCrit_unique`, the escape set *is* the critical
domain because `c ∈ Mandelbar`), and `Work.EL.rayPt hN θ t` lies off the filled Julia set
(`Work.EL.rayPt_mem_paramRay` and `Work.EL.paramRay_subset_compl`).  So the deviation of the ray
point is the deviation of the ray point for `φ`, which is `θ - α`
(`Work.GATE.Gate.deviation_rayPt`: the lift of the Böttcher argument into `(α - 1/2, α + 1/2]` is
the ray angle itself, and here `θ < α` puts `θ` in that window). -/
theorem deviation_rayPt {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hb : Work.ParamRays.IsDynBottcher c φ) (hM : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    {θ α t : ℝ} (hθ0 : 0 ≤ θ) (hθα : θ < α) (hθα' : α - 1 / 2 < θ) (ht : 1 < t) :
    Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (Work.EL.rayPt hN θ t) = θ - α := by
  have hθ0mem : (0 : ℝ) ≤ θ := hθ0
  -- the ray point is off the filled Julia set, hence in the escape set / critical domain
  have hz : Work.EL.rayPt hN θ t ∈ Work.EL.paramRay hN θ :=
    Work.EL.rayPt_mem_paramRay hN ht
  have hnotK : Work.EL.rayPt hN θ t ∉ Work.EL.K c :=
    Work.EL.paramRay_subset_compl hN θ hz
  have hcrit : Work.EL.rayPt hN θ t ∈ Work.ParamRays.critDomain c := by
    have hEsc : Work.ParamRays.Escaping c (Work.EL.rayPt hN θ t) :=
      (Work.ParamRays.greenFun_pos_iff_escaping c _).mp
        (by rw [← Work.Bottcher.CritBasic.green_eq]
            exact Work.PARIMPL.green_pos_of_notMem_K hnotK)
    rw [Work.ParamRays.critDomain_eq_escapingSet hM, Work.ParamRays.mem_escapingSet]
    exact hEsc
  -- the canonical critical coordinate agrees with `φ` there
  have heq : Work.Bottcher.varphiCrit c (Work.EL.rayPt hN θ t) = φ (Work.EL.rayPt hN θ t) :=
    Work.Bottcher.varphiCrit_unique (Work.ParamRays.IsDynBottcher.isCritBottcher hb) hcrit
  rw [show Work.GATE.deviation (Work.Bottcher.varphiCrit c) α (Work.EL.rayPt hN θ t)
      = Work.GATE.deviation φ α (Work.EL.rayPt hN θ t) by
    simp only [Work.GATE.deviation, Work.GATE.liftAngle, Work.GATE.bAngle, heq]]
  exact Work.GATE.Gate.deviation_rayPt hN ht hθα' (by linarith)

end Work.GATE2.EXL
