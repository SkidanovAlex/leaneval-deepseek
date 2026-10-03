/-
# `Submission.Work.FIArea7.UniCharTerm6` — the (17.10) main term

*FI* (17.10) is

  `W(β) = 2 Σ_{|k|≤K} û(k) Σ_{b≤X} (μ(b)/b) Σ_d (f*(4d)/Φ(bd)) Σ_{χ (mod 4bd)} J(χ)|S^k_χ(β')|²
          + O((X⁻¹+P⁻¹+H⁻¹+K⁻¹H²)N²log N)`,

of which the engine is the §16 identity `section16_omegaDetect_expansion`: for a fixed modulus
`Q = 4be` and a fixed coefficient `c`,

  `Σ_{z₁,z₂} unitInd Q z₁ unitInd Q z₂ (c z₁ conj (c z₂)) (Σ_ω [z₁ ≡ ωz₂] (ω|e))
     = (1/Φ(Q)) Σ_{χ (mod Q)} J(χ) S_χ(c) conj(S_χ(c))`,

with `Φ(Q) = Fintype.card (GaussUnit Q)`, `J(χ) = Σ_{p ∈ (ℤ[i]/Q)^*} ratWeight Q e p χ(p)` and
`S_χ(c) = Σ_z unitCoeff Q c z χ(unitClassD Q z)`.  This file defines that right-hand side, i.e. the
**main term of (17.10)**, with the coefficient `c = uniCoeff ε β k` and the mode weights
`(2log2+log4)` at `k = 0` and `1/|k|` on `evenFreq K`:

* `uniSChar`, `uniJChar` — `S^k_χ` and `J(χ)` of (17.12)/(17.11);
* `uniModeCharSum` — the per-`(b,e,k)` right-hand side `(1/Φ(4be))Σ_χ J(χ)|S^k_χ|²`;
* `WUniOmega6Pull6Char` — the (17.10) main term.

`Work.FIArea7.uniModeSumFree_eq_char` identifies it with `uniModeSumFree` (whose per-`(b,e,k)`
terms are the left-hand side of the same §16 identity).
-/
import Mathlib
import Submission.Work.FIArea7.UniMollify6
import Submission.Work.FIArea7.GuardRemoval6
import Submission.Work.FIArea7.Section16Expansion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **(17.12)**: `S^k_χ(c) = Σ_z unitCoeff Q c z · χ(unitClassD Q z)` for the coefficient
`c = uniCoeff ε β k` — the character sum of the §16 expansion at the mode `k`. -/
def uniSChar (Pa : Work.FITop.Params) (Q : ℕ) [NeZero Q] (ε : GaussianInt → ℤ)
    (β : GaussianInt → ℂ) (k : ℤ) (χ : AddChar (Additive (GaussUnit Q)) ℂ) : ℂ :=
  ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
    unitCoeff Q (uniCoeff ε β k) z * χ (Additive.ofMul (unitClassD Q z))

/-- **(17.11)**: `J(χ) = Σ_{p ∈ (ℤ[i]/Q)^*} ratWeight Q e p · χ(p)` — the character sum over the
rational classes. -/
def uniJChar (Q e : ℕ) [NeZero Q] (χ : AddChar (Additive (GaussUnit Q)) ℂ) : ℂ :=
  ∑ p : GaussUnit Q, ratWeight Q e p * χ (Additive.ofMul p)

/-- **The right-hand side of (16.11) at the mode `k`**: `(1/Φ(Q)) Σ_χ J(χ) S^k_χ conj(S^k_χ)`,
`Φ(Q) = Fintype.card (GaussUnit Q)`. -/
def uniModeCharSum (Pa : Work.FITop.Params) (b e : ℕ) [NeZero (4 * b * e)]
    (β : GaussianInt → ℂ) (k : ℤ) (ε : GaussianInt → ℤ) : ℂ :=
  (1 / (Fintype.card (GaussUnit (4 * b * e)) : ℂ)) *
    ∑ χ : AddChar (Additive (GaussUnit (4 * b * e))) ℂ,
      uniJChar (4 * b * e) e χ * (uniSChar Pa (4 * b * e) ε β k χ)
        * star (uniSChar Pa (4 * b * e) ε β k χ)

/-- **The `(b,e,k)`-mode factor of the (17.10) main term**, with the Möbius weight and the mode
weights of `logFac6Series`; the degenerate range `4be = 0` (which the sums `b,e ≥ 1` never meet) is
set to `0` so that no `ZMod` instance is needed at the definition site. -/
def uniCharTerm (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ) (K : ℕ)
    (ε : GaussianInt → ℤ) : ℂ :=
  (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
    * (if h : 4 * b * e = 0 then 0 else
        haveI : NeZero (4 * b * e) := ⟨h⟩
        ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModeCharSum Pa b e β 0 ε
          + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeCharSum Pa b e β k ε))

/-- **The (17.10) main term**: the `(b,e)`-sum of the mode-wise §16 expansions. -/
def WUniOmega6Pull6Char (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) (K : ℕ)
    (ε : GaussianInt → ℤ) : ℂ :=
  2 * ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X, uniCharTerm Pa b e β K ε

end

end Work.FIArea7
