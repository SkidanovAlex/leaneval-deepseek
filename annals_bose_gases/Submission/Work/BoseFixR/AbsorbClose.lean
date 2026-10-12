import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixR.AbsorbCloseFix
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.AbsorbClose` — the §11 *close* absorption (corrected statement)

The close-case comparison of FS §11 is

`ℓ³Λ(a, K, η₀, μ) + errAbs ≤ CloseBoundR v R μ C₆ ρ`,

where the target's LHY term is at the chemical potential `μ`
(`4π·lhyC·μ²aℓ³·√(μa³)`) and the close bound's LHY term is at the *condensate
density* `ρ` (`4π·lhyC·ρ²aℓ³·√(ρa³)`).  Comparing them needs `√(μa³) ≳ √t`, so the
statement requires the diluteness identity

  `hμa : t ≤ μ * a ^ 3`,

which holds *by definition* at the chapter's only instantiation `t := dil v μ`
(`dil v μ = μ * (a v)^3`), where it is `le_refl`.

**The statement without `hμa` is FALSE** (the finding of the prover of the first
version of this path): with `a = ℓ = 1`, `t = 2^{-6460}`, `μ = t²`, `R = 0`,
`C₄ = C₆ = 0`, `η₀ = 1/1615`, `K = bigK 1 0 0 0` and `ρ = μ(1 − t^{3/323})` all
the other hypotheses hold (`t^{η₀} = 1/16`, `√t = 2^{-3230}`), while the two sides
differ by
`4πμ²√t·(lhyC − K·t^{η₀} − lhyC·√t·(1 − t^{3/323})^{5/2}) > 0`
(`(5/8)·lhyC − 1/(64π) > 2.49` against `lhyC·2^{-3230} < 0.005`).

The corrected statement (with `hμa`) is proved in
`Submission/Work/BoseFixR/AbsorbCloseFix.lean` as
`Work.BoseFixR.AbsorbCloseFix`; this module re-exports it under the name the
assembly uses.  `AbsorbFar` needs no such hypothesis: its comparison is
homogeneous in the target's own `√t`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixR

/-- FS §11's close leg, with the diluteness identity `t ≤ μa³` (see the module
docstring; it is `le_refl` at the only instantiation `t := dil v μ`). -/
theorem AbsorbClose {a ℓ t μ R C₄ C₆ K η₀ ρ : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) (hμ : 0 < μ) (hR : 0 ≤ R) (hC₄ : 0 ≤ C₄)
    (hC₆ : 0 ≤ C₆) (hη₀ : 0 ≤ η₀) (hη₂ : η₀ < 2 / 323) (hη₃ : η₀ ≤ 1 / 1615)
    (ht : 0 < t) (ht1 : t ≤ 1) (hK : bigK a R C₄ C₆ ≤ K) (hρ : 0 ≤ ρ)
    (hμa : t ≤ μ * a ^ 3) (hρlo : μ * (1 - t ^ (3 / 323 : ℝ)) ≤ ρ) :
    (-4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        + 4 * Real.pi * Work.UBB.lhyC * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t
        - 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * K * t ^ (1 / 2 + η₀))
      + errAbs a ℓ t μ R C₄
    ≤ -4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        + 4 * Real.pi * Work.UBB.lhyC * ρ ^ 2 * a * ℓ ^ 3 * Real.sqrt (ρ * a ^ 3)
        - C₆ * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t
            * (t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t + t ^ (1 / 1615 : ℝ)) :=
  AbsorbCloseFix ha hℓ hμ hR hC₄ hC₆ hη₀ hη₂ hη₃ ht ht1 hK hρ hμa hρlo

end Work.BoseFixR
