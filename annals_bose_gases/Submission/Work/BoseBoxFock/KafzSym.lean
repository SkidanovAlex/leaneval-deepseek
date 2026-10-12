import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.KafzDict
import Submission.Work.BoseBoxFock.KzOpC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.KafzSym` — the symbol of `H2ndHon` at `z` and its discrepancy with `KzOpC`

At the honest family, `KafzDict.bomb_H2ndF_eq_integral` writes

    bomb Ψ (H2ndHon Ψ) = ∫_ℂ Re (Σ_{i<25} z^{p_i} z̄^{q_i} ⟪v(z), KvecF i (v(z))⟫) dν(z),
    v(z) = Phi (split Ψ) z,

i.e. `Re⟪v, symC z v⟫` with the **symbol operator**

    `symC z = Σ_{i<25} z^{pvecF i} (conj z)^{qvecF i} • KvecF i`.

For real `r ≥ 0` (where `conj r = r`) this is `symR r = Σ_i r^{p+q} • KvecF i`, an
`r`-**polynomial** of degree ≤ 4 in the operators `KvecF i`.

The pointwise comparison of `symR r` with FS's `KzOpC (r²/ℓ³)` (the `c`-number
substitution of `eq:Kz` on the zero-condensate slice, `KzOpC.lean`) has
**no `r`-dependence**: one computes

    `symR r - KzOpC (r²/ℓ³) = r² • D2 + r • D1 + D0`

with the three explicit `r`-independent operators `D2`, `D1`, `D0` below (all of
whose coefficients are real, so their quadratic forms are bounded by the window
hypothesis `⟪w, n₊w⟫ ≤ K ‖w‖²` and Bessel).  The identity is proved in
`Submission/Work/BoseBoxFock/symDiscrep.lean`; here we only *define* the objects.

Ingredients used by the definitions: `cHCF` (the contact coefficient
`½ℓ⁻³(ĝ(0)+Ŵ₁ω(0))`), `i3F` (`ℓ⁻³`), `cMuF` (`−μĝ(0)`), the slot data
`pvecF/qvecF/KvecF`, and the row words `Bkin`, `BW`, `BchiC`, `BchiA`, `Bbog1`,
`Bbog2`, `BQ3a`, `BQ3b` of `KafzDict`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-- The number sum `n₊^χ = Σ_{k} a_k†a_k` over the χ-mode lattice. -/
noncomputable def nPlusChi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (f : Mode → Fin m → ℝ) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k : Mode, nOpC (f k)

/-- The four-term linear word `Σ_k χ̂_k (a_k† + a_k + a_{−k}† + a_{−k})` of the
`𝒬₁` rows (the `r¹` part of `KzBogFS`). -/
noncomputable def linAll {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k : Mode, ((E.hatChi k : ℝ) : ℂ) •
    (annOfE (f k) + creOfE (f k) + annOfE (f (-k)) + creOfE (f (-k)))

/-- The `r⁰` part of the discrepancy `symR r − KzOpC (r²/ℓ³)`. -/
noncomputable def D0F {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ((((2 * cHCF E gHat0 + E.mu * gHat0) : ℝ)) : ℂ) • (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
  + (((-(i3F E) : ℝ)) : ℂ) •
      BW (Finset.univ : Finset Mode) (fun k => E.W1 k + E.W1omega k) f
  + (((-((i3F E) * (E.W1 0 + E.W1omega0)) : ℝ)) : ℂ) • nPlusChi f

/-- The `r¹` part of the discrepancy `symR r − KzOpC (r²/ℓ³)`. -/
noncomputable def D1F {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (((-(2 * i3F E * E.W1 0) : ℝ)) : ℂ) •
      (BchiC (Finset.univ : Finset Mode) E.hatChi 1 f
        + BchiA (Finset.univ : Finset Mode) E.hatChi 1 f)
  + (((-(2 * i3F E * E.W1omega0) : ℝ)) : ℂ) •
      (BchiC (Work.BoseB7.excited Mode) E.hatChiSq 1 g
        + BchiA (Work.BoseB7.excited Mode) E.hatChiSq 1 g)
  -- NOTE: the two `μ W₁(0)`-summands cancel; they are absent from `D1F`.
  -- (see the derivation in the docstring of `KafzSym`.)

/-- The `r²` part of the discrepancy `symR r − KzOpC (r²/ℓ³)`. -/
noncomputable def D2F {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (((-(4 * cHCF E gHat0) : ℝ)) : ℂ) • (1 : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
  + (((2 * (i3F E) * E.W1omega0 : ℝ)) : ℂ) • nOpC (f 0)

/-- **The symbol of `H2ndHon` at a real `z = r ≥ 0`**: the anti-Wick symbol
`Σ_i r^{p_i+q_i} • KvecF i` (the anti-normal dictionary of `KafzDict` evaluated at
the real coherent parameter `r`). -/
noncomputable def symR {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 r : ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ i ∈ Finset.range 25,
    (((r : ℂ) ^ (pvecF i + qvecF i))) • KvecF f g BNH PHs E gHat0 i

/-- **The symbol of `H2ndHon` at a complex `z`** (the integrand of
`KafzDict.bomb_H2ndF_eq_integral`). -/
noncomputable def symC {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (z : ℂ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ i ∈ Finset.range 25,
    ((z ^ (pvecF i) * (starRingEnd ℂ z) ^ (qvecF i))) • KvecF f g BNH PHs E gHat0 i

end Work.BoseBoxFock
