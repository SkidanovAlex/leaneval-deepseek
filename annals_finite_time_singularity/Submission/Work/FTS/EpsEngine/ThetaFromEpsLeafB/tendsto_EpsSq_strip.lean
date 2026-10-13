/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ThetaFromEpsLeafB/tendsto_EpsSq_strip` — the two strip energies vanish at `φ → 0⁺`

Sub-leaf (B) of `ThetaFromEps.lean`: for a profile `g` with `EpsMem α g` (i.e. `(g · epsW α)²`
integrable on the quarter plane `Iz ×ˢ Iθ`), the weighted energies of the two angular strips

    stripLo φ g = (z,θ) ↦ if θ ≤ φ then g z θ else 0 ,
    stripHi φ g = (z,θ) ↦ if π/2 - φ ≤ θ then g z θ else 0

tend to `0` as `φ → 0⁺`.  This is the dominated-convergence statement with which the
`θ`-uniform flatness of `J_ε g` (leaf (A), `sinpow_mixed_Jeps_le_strip`) is fed.

The proof has two independent halves, each an application of a general measure-theoretic
statement:

* `EpsSq α (stripLo φ g)` is the integral of `1_{θ ≤ φ}·(g·epsW α)²` over the quarter plane
  (`EpsSq_stripLo_eq`, `StripPlumb.lean`), whence the outer limit follows from
  `tendsto_setIntegral_Iic`: the sets `{θ ≤ φ} ∩ Iθ` shrink to the null set `{θ = 0}`
  (Fubini `EpsSq_eq_setIntegral`, dominated convergence, `ae_snd_ne` — all in
  `StripFacts.lean`);
* likewise `EpsSq α (stripHi φ g)` is the integral of `1_{π/2 - φ ≤ θ}·(g·epsW α)²`
  (`EpsSq_stripHi_eq`), and the sets `{π/2 - φ ≤ θ} ∩ Iθ` shrink to the null set `{θ = π/2}`
  (`StripIci.tendsto_setIntegral_Ici`).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.StripDefs
import Submission.Work.FTS.EpsEngine.ClassCStepEngine
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripFacts
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripPlumb
import Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripIci.tendsto_setIntegral_Ici

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafB

theorem tendsto_EpsSq_strip {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hg : Work.FTS.StrongEps.EpsMem α g) :
    Filter.Tendsto (fun φ : ℝ => Work.FTS.StrongEps.EpsSq α
        (Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    Filter.Tendsto (fun φ : ℝ => Work.FTS.StrongEps.EpsSq α
        (Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  constructor
  · have hfun : (fun φ : ℝ => Work.FTS.StrongEps.EpsSq α
          (Work.FTS.EpsEngine.ThetaFromEps.stripLo φ g))
        = fun φ : ℝ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
            (if p.2 ≤ φ then (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 else 0) :=
      funext fun φ => EpsSq_stripLo_eq α φ g hg
    rw [hfun]
    exact tendsto_setIntegral_Iic
      (F := fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) hg
  · have hfun : (fun φ : ℝ => Work.FTS.StrongEps.EpsSq α
          (Work.FTS.EpsEngine.ThetaFromEps.stripHi φ g))
        = fun φ : ℝ => ∫ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
            (if Real.pi / 2 - φ ≤ p.2 then
              (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2 else 0) :=
      funext fun φ => EpsSq_stripHi_eq α φ g hg
    rw [hfun]
    exact Work.FTS.EpsEngine.ThetaFromEpsLeafB.StripIci.tendsto_setIntegral_Ici
      (F := fun p : ℝ × ℝ => (g p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) hg

end Work.FTS.EpsEngine.ThetaFromEpsLeafB
