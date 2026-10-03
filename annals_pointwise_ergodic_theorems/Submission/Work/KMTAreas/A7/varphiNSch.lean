/-
# The Schwartz realisation of the unmodulated KMT bump `φ_N`

The unmodulated bump `varphiN N k` (`Large/Defs.lean`) is `C^∞` with compact support
(`contDiff_varphiN_all`, `hasCompactSupport_varphiN`), hence a Schwartz function.  This module
provides the `SchwartzMap` realisation `varphiNSch N k`, with the coercion lemma `varphiNSch_coe`.

It is needed by the low-frequency (`k₁ = 0`) analysis of `Work.KMTAreas.A7.lacunaryBumpVarEstimate`:
there the modulated bump splits as `varphiNt N 0 t = varphiN N 0 + (varphiNt N 0 t - varphiN N 0)`,
and the *difference* — a Schwartz function — is the symbol to which the narrow-symbol variational
estimate `Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints` is applied (its signed sums do
not vanish at the frequency origin, so the *unmodulated* part has to be handled separately).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.randSymb_schwartz

set_option autoImplicit false

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory

/-- The unmodulated KMT bump `φ_N` as a Schwartz function. -/
noncomputable def varphiNSch (N k : ℕ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_varphiN N k).toSchwartzMap (contDiff_varphiN_all N k)

@[simp] lemma varphiNSch_apply (N k : ℕ) (ξ : ℝ) :
    varphiNSch N k ξ = varphiN N k ξ :=
  HasCompactSupport.toSchwartzMap_toFun (hasCompactSupport_varphiN N k)
    (contDiff_varphiN_all N k) ξ

@[simp] lemma varphiNSch_coe (N k : ℕ) :
    (varphiNSch N k : ℝ → ℂ) = varphiN N k :=
  funext (varphiNSch_apply N k)

end

end Work.KMTAreas.A7
