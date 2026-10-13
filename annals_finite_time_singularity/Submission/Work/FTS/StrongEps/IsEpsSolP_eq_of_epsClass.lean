/-
# `StrongEps/IsEpsSolP_eq_of_epsClass.lean` — **D1**: fixed-ε uniqueness of the scheme (PROVED)

curric-46 lead install (2026-10-11), `cbc/fts_strongeps_c1c5_ruling.md` §5 step 2.  Used inside
the proof of `exists_limG` to glue the horizon-`n` solutions at the same ε.
Route: Volterra form on `Qd` (FTC from `IsEpsSolP` + `hc1`), `EpsSq_intervalIntegral_le_gen`
(Minkowski), the proved gate `EpsEngine.BddLip_of_epsClass`, integral Grönwall,
`EpsSq = 0 ⇒` a.e. `0 ⇒` (continuity) `0` on `Qd`.  The hypotheses `hcl`/`hc1` are read off
`EpsUniformMem` at `C₁ := C₀`, `B := max K'(m) K'(n)` (reviewer glue `C46SERev.epsClass_of_mem`,
`~/scratch-c46-serev/rev5.lean`).

**Status: PROVED** (owner session 18).  The proof is in `IsEpsSolP_eq_of_epsClass_proof.lean`
(`Work.FTS.StrongEps.IsEpsSolP_eq_of_epsClass_proof`, axioms `[propext, Classical.choice,
Quot.sound]`); this file is the frozen statement plus the one-line transplant.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.IsEpsSolP_eq_of_epsClass_proof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **D1 — uniqueness of the ε-scheme at FIXED ε**. -/
theorem IsEpsSolP_eq_of_epsClass {α C₁ Ce Cs B T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn} {g g' : Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 0 < T)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α C₁ Φs E) (hB : 0 ≤ B)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g) (hsol' : IsEpsSolP α ρ ε T Φs E g₀ g')
    (hcl : ∀ τ ∈ Set.Icc 0 T, Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B (slice g τ))
    (hcl' : ∀ τ ∈ Set.Icc 0 T, Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B (slice g' τ))
    (hc1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (hc1' : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g' p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T)) :
    ∀ τ ∈ Set.Icc 0 T, ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → g z θ τ = g' z θ τ :=
  IsEpsSolP_eq_of_epsClass_proof hα hρ hε hε1 hT hEll hstar hml hB hsol hsol' hcl hcl' hc1 hc1'

end Work.FTS.StrongEps
