import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_map
import Submission.Work.ELTop.landsN_iff_landsAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open LeanEval.ComplexAnalysis (Tantibar)

namespace Work.ELAssembly

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`).
/-- **The portrait pairs along the parabolic cycle** (`NOTES_LEAD_mandelbar_pbavoid.md` §3.1,
(C1) and (C2)): the two root rays land at every point of the cycle (`(C1)`, by induction with
`Work.ELTop.landsN_map d.hN d.bottcher` from `d.rays` through
`Work.ELTop.landsN_iff_landsAt`), and the eight orbit angles have the explicit values
`281,215 | 461,593 | 101,860 | 821,326` over `1023` (`(C2)`, `norm_num` on `T θ = Int.fract (-2θ)`
and `α₁ = 371/1023`, `α₂ = 404/1023`).  These are the inputs of `wakePair` / (WS0) and of the
`(WS)` non-degeneracy checks. -/
theorem PbAvoid_cycle {c : ℂ} (d : Work.EL.RootParabolic c) :
    (∀ j : ℕ, Work.EL.LandsN d.hN (Work.EL.T^[j] Work.EL.alpha1)
        ((LeanEval.ComplexAnalysis.Tantibar c)^[j] d.z₁) ∧
      Work.EL.LandsN d.hN (Work.EL.T^[j] Work.EL.alpha2)
        ((LeanEval.ComplexAnalysis.Tantibar c)^[j] d.z₁)) ∧
    (Work.EL.T^[1] Work.EL.alpha1 = 281 / 1023 ∧ Work.EL.T^[1] Work.EL.alpha2 = 215 / 1023 ∧
      Work.EL.T^[2] Work.EL.alpha1 = 461 / 1023 ∧ Work.EL.T^[2] Work.EL.alpha2 = 593 / 1023 ∧
      Work.EL.T^[3] Work.EL.alpha1 = 101 / 1023 ∧ Work.EL.T^[3] Work.EL.alpha2 = 860 / 1023 ∧
      Work.EL.T^[4] Work.EL.alpha1 = 821 / 1023 ∧ Work.EL.T^[4] Work.EL.alpha2 = 326 / 1023) := by
  refine ⟨?_, ?_⟩
  · -- (C1): landing propagates along the orbit of the parabolic point.
    have hA : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁ :=
      (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher _ _).mpr d.rays.1
    have hB : Work.EL.LandsN d.hN Work.EL.alpha2 d.z₁ :=
      (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher _ _).mpr d.rays.2
    have key : ∀ (θ : ℝ) (y : ℂ) (j : ℕ), Work.EL.LandsN d.hN θ y →
        Work.EL.LandsN d.hN (Work.EL.T^[j] θ) ((Tantibar c)^[j] y) := by
      intro θ y j h
      induction j with
      | zero => simpa using h
      | succ n ih =>
        have hstep := Work.ELTop.landsN_map d.hN d.bottcher ih
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact hstep
    exact fun j => ⟨key Work.EL.alpha1 d.z₁ j hA, key Work.EL.alpha2 d.z₁ j hB⟩
  · -- (C2): the eight explicit orbit angles.
    norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2]

end Work.ELAssembly
