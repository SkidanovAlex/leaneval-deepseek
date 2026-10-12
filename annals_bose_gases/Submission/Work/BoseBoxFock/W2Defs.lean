import ChallengeDeps
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.W2Defs` — the first-quantised `H_Λ^{2nd}` word `W₂`

The **box side** of the bridge (`box_to_model`, BF3a): FS `prop:Hamilton2ndQuant` compares
the box word `H_Λ` with the second-quantised `H_Λ^{2nd}`.  Written as a *first-quantised*
quadratic-form word (no Fock space), the comparison is

    `wordB(Φ) ≥ W₂(Φ) − C·μ²aℓ³·(d^{2(M−1)} + R²/ℓ²)·normB(Φ)`                     (BF3a)

on the class `Adm v ε₀ μ`, `n ≤ 2μℓ³`, where `W₂` is the row-by-row first-quantised
`H_Λ^{2nd}`:

| row of `H2ndF` | first-quantised word |
|---|---|
| kinetic `Σ_k τ̃(k)a_k†a_k` | `kinTauB` — the **`τ̃`-symbol** slot form `Qχτ̃(√−Δ)χQ` |
| gap `(b/2ℓ²)(N − n₀)` | `(b/2ℓ²)·cnPlus` |
| `n₊^H` gap `(ε_Tb/2d²ℓ²)·NH` | `(ε_Tb/2d²ℓ²)·nPlusHB` |
| contact + `μ` rows | `q0word` (`KzEnvHon`'s kernels) |
| the two `χ̂`-linear rows | `q1word` |
| the three `Q₂` rows | `q2word` |
| the cubic `Q̃₃` row | `q3lowWord fc ((d²ℓ)⁻¹)` |

The *other half* of the box gaps (`(b/2ℓ²)cnPlus`, `(ε_Tb/2d²ℓ²)nPlusHB` — the parts of
`bℓ⁻²cnPlus` and `bε_T(dℓ)⁻²nPlusHB` that are *not* in `W₂`) is the reserve that pays
BF3a's errors; the error term shown above is the part that survives into `errKafz` (it is
`X³`-times smaller than `errKafz`'s `(R/a)²√t` slot, and `d^{2(M−1)} = X^{564}` is far below
its `t^{2/323}` slot).

## Two conventions

* **The `τ̃` symbol.**  `tauSm eT s d ℓ` is FS's smoothed `τ`; it is **radial**, and
  `tauSmRad eT s d ℓ ‖k‖ = tauSm eT s d ℓ k` (`tauSm_eq_tauSmRad`).  `bsOneBody` wants the
  radial form, so `kinTauB` uses `tauSmRad`.  This is *structural*, not cosmetic: the
  frame-resolution identity `Qχτ̃(√−Δ)χQ = (2π)^{-3}∫τ̃(k)|Q(e^{ikx}χ_Λ)⟩⟨Q(e^{ikx}χ_Λ)|dk`
  (exact in the continuum) is what makes the model's kinetic row `Σ_k τ̃(k)a_k†a_k` the
  second quantisation of the box row, and it needs `τ̃` on *both* sides
  (see `BRIDGE_DESIGN.md` §2.1).
* **The kernels** are the honest ones: `w₁ = wLoc ℓ (g0 v h) 0` (so that `chemPartB` is
  `qLHSword`'s `μ`-line) and `w₂ = wLoc ℓ (g2 v h) 0`; `q3lowWord` uses `w₁` and
  `NodeB3B`'s cut-off `(d²ℓ)⁻¹ = K_L√(μa)`.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Metric Filter

namespace Work.BoseBoxFock

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseKinLoc Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The radial form of the smoothed kinetic symbol -/

/-- The **radial** form of FS's smoothed symbol `τ̃` (so that it can be fed to
`Work.BSKinetic.bsOneBody`, whose coefficient is a function of `‖p‖`). -/
def tauSmRad (eT s d ℓ : ℝ) (r : ℝ) : ℝ :=
  (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * tauProf (r / (2 * s * ℓ)⁻¹)
    + eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * tauProf (r / (2 * d * s * ℓ)⁻¹)

/-- `tauSm` only depends on `‖k‖`, through `tauSmRad`. -/
lemma tauSm_eq_tauSmRad (eT s d ℓ : ℝ) (k : ℝ³) :
    tauSm eT s d ℓ k = tauSmRad eT s d ℓ ‖k‖ := rfl

/-! ## 2. The box-restricted slot form -/

/-- The **box-restricted** slot-`i` lifting of a one-body form `q`, in the same normalisation
as `BoseKinLoc.kinFormB` (the integral runs over the box `abox N ℓ`, and the `ℓ⁻³` prefactor
is the peel normalisation of `slotForm`). -/
def slotFormB (N : ℕ) (q : (ℝ³ → ℝ) → ℝ) (ℓ : ℝ) (u : ℝ³) (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) : ℝ :=
  ℓ ^ (-3 : ℤ) *
    ∫ x in abox N ℓ, indU ℓ u (x i) * q (fibre N i Φ x)

/-- **The `τ̃`-kinetic word**: `Σ_i ⟨Φ, (Qχτ̃(√−Δ)χQ)_i Φ⟩`. -/
def kinTauB (N : ℕ) (ℓ d s eT : ℝ) (Φ : Submission.BoseGases.X N → ℝ) : ℝ :=
  ∑ i : Fin N, slotFormB N (fun ψ => bsOneBody ℓ (tauSmRad eT s d ℓ) 0 ψ) ℓ 0 i Φ

/-! ## 3. `W₂` -/

/-- The **kinetic part** of `W₂` (rows `kin`, `gap`, `gapH` of `H2ndF`). -/
def W2kinB (v : ℝ³ → ℝ) (μ : ℝ) (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  let P := paramsAt μ (a v)
  let ℓ := sideAt μ (a v)
  kinTauB n ℓ P.d P.s P.eT Φ
    + (P.b / 2) * ℓ ^ (-2 : ℤ) * cnPlus ℓ Φ
    + (P.eT * P.b / (2 * P.d ^ 2 * ℓ ^ 2)) * nPlusHB ℓ P.d Φ

/-- The **potential part** of `W₂` (rows `Q₀`, `Q₁`, `Q₂`, `Q̃₃` of `H2ndF`). -/
def W2potB (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (fc : LowCut)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  let ℓ := sideAt μ (a v)
  q0word (N := n) ℓ μ (wLoc ℓ (g0 v h) 0) (wLoc ℓ (g2 v h) 0) Φ
    + q1word (N := n) ℓ μ (wLoc ℓ (g0 v h) 0) (wLoc ℓ (g2 v h) 0) Φ
    + q2word (N := n) ℓ μ (wLoc ℓ (g0 v h) 0) (wLoc ℓ (g2 v h) 0) Φ
    + q3lowWord fc ((paramsAt μ (a v)).d ^ 2 * ℓ)⁻¹ ℓ (wLoc ℓ (g0 v h) 0) Φ

/-- **FS `H_Λ^{2nd}` as a first-quantised word** — the target of BF3a. -/
def W2B (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (n : ℕ) (fc : LowCut)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  W2kinB v μ n Φ + W2potB v h μ n fc Φ

/-- The BF3a error scale: `μ²aℓ³(d^{2(M−1)} + R²/ℓ²)` (FS `prop:Hamilton2ndQuant`'s error). -/
def errB (v : ℝ³ → ℝ) (R μ : ℝ) : ℝ :=
  μ ^ 2 * a v * sideAt μ (a v) ^ 3
    * ((paramsAt μ (a v)).d ^ (2 * ((paramsAt μ (a v)).M - 1))
        + R ^ 2 / sideAt μ (a v) ^ 2)

end Work.BoseBoxFock
