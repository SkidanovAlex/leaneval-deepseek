import ChallengeDeps
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.Defs` — node **BOG**: FS `eq:Combined1` at the honest datum

This is the vocabulary of the subproject `Submission/Work/BoseBogFS/` (namespace
`Work.BoseBogFS`), the chapter that proves the FS `thm:BogHamDiag` + `lem:BogIntegral`
inequality (`eq:Combined1` of FS §10, in the operator form the close-case residual
`RB67` consumes) at the corrected Bogoliubov quadratic `KzBogFS`.

## Why a local copy of the vocabulary

The design (`BOSE_BOXFOCK_LEAD.md` §5.4, `BOSE_BOXFOCK_STATEMENTS.lean.txt` §5) puts
`RHi`, `KzBogFS`, `KzOpFS`, `Q3KernelFS`, `RViewFS`, `BogOpBoundFS` in
`Submission/Work/BoseBoxFock/Defs.lean` (node `D-FS`).  That module is written by a
sibling subproject; until it exists this chapter carries **verbatim copies** of the
declarations it needs, exactly as the sibling `Submission.Work.BoseB7AK.C3Q` carries
`Q3KernelFS`/`Control3QFS`.  The statements below are verbatim from
`BOSE_BOXFOCK_STATEMENTS.lean.txt`, so re-pointing to `Work.BoseBoxFock` once it lands
is a rename.

## What this chapter delivers (see `README.md`)

* the **per-mode pair identity** with the *shifted* squeezing operator
  `b_k = a_k + α_k a_{-k}† + c_k` of FS `eq:Defb_k`, proved directly in
  `Work.BoseB7.FockData` (no `FsBogDecomp`/mode decomposition needed);
* the **per-mode ground estimate** (`thm:BogHamDiag`'s per-pair `eq:BogIneq`), hence
  the finite-sum Bogoliubov step via `Work.BoseB6.sum_pairGround_le`;
* the **reduction** of `BogOpBoundFS` to two explicit scalar estimates in the shape of
  `Work.BoseB6Est.fsZeroPoint_le` and `Work.BoseB6Est.kappaSum_le`;
* the **arithmetic** absorbing FS's error display into the free constant of
  `BogOpBoundFS`, at the corrected close threshold `μK_ℓ⁻²/(2¹⁴π)`.

## Conventions

* `Mode` is B7's finite additive group of mode labels (`Work.BoseB7.FockData`), with
  `kmom (-k) = -kmom k`; `0` is a genuine mode label (the design's `χ`-label `0`, the
  vector `Qχ_Λ`, **not** the condensate), and the Bogoliubov sums run over *all* labels
  (`F6`).
* `KzBogFS` is FS `eq:BogHamPositive-1` with the correct normalisation: weight `½` per
  mode, and `𝒞(k) = (ρ−μ)Ŵ₁(0)χ̂(kℓ)z` (the environment's `E.hatChi` is the
  *normalised* `χ̂(kℓ) = ℓ⁻³χ̂_Λ(k)`).
* every constant is absolute; `C` in `BogOpBoundFS` is the free O(1) constant of the
  §11 error bracket.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- `z = √(ρℓ³)`, FS's substituted condensate amplitude at condensate density `ρ`. -/
def bogZ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) : ℝ :=
  Real.sqrt (ρ * E.ell ^ 3)

/-! ## 1. The region kept for the diagonal reserve -/

/-- The region kept for the diagonal reserve: `|k| ≥ ½K_L√(μa)` (`= ½(d²ℓ)⁻¹`).
This is verbatim `Work.BoseBoxFock.RHi`. -/
def RHi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (F : Work.BoseB7.FockData Mode)
    (E : Work.BoseB7.Q3Env Mode) (k : Mode) : Prop :=
  E.KL * Real.sqrt (E.mu * E.aScat) / 2 ≤ ‖F.kmom k‖

instance {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (F : Work.BoseB7.FockData Mode)
    (E : Work.BoseB7.Q3Env Mode) : DecidablePred (RHi F E) :=
  fun k => Classical.dec _

/-! ## 2. FS `eq:BogHamPositive-1` with the correct normalisation: `KzBogFS` -/

/-- **FS `eq:BogHamPositive-1`** (with `𝒬₁(z)` folded in, `eq:SimplifyKz`):

  `𝒦^Bog = ½Σ_k[𝒜(n_k+n_{-k}) + ℬ(a_ka_{-k}+h.c.) + 𝒞(a_k+a_k†+a_{-k}+a_{-k}†)]`,
  `𝒞(k) = ℓ⁻³(ρ−μ)Ŵ₁(0)χ̂_Λ(k)z = (ρ−μ)Ŵ₁(0)χ̂(kℓ)z`.

`Work.BoseFixR.KzBog` has `¼` and the extra `ℓ⁻³` of `χ̂_Λ` (F2): it is `½𝒦^Bog` with a
`1/(2ℓ³)`-scaled `𝒬₁`.  The sum runs over **all** labels, including `0` (F6).

This is verbatim `Work.BoseBoxFock.KzBogFS`. -/
def KzBogFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    F.H →ₗ[ℝ] F.H :=
  let z : ℝ := Real.sqrt (ρ * E.ell ^ 3)
  ∑ k : Mode, (1 / 2 : ℝ) •
    ((E.tau k + ρ * E.W1 k) • (F.nOp k + F.nOp (-k))
      + (ρ * E.W1 k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))
      + ((ρ - E.mu) * E.W1 0 * E.hatChi k * z) •
          (F.a k + F.aDag k + F.a (-k) + F.aDag (-k)))

/-! ## 3. The per-mode data of `KzBogFS` and the shifted squeezing operator -/

/-- FS's `𝒜(k) = τ(k) + ρ_zŴ₁(k)` at the datum `(E, ρ)` — definitionally the
`A`-field of `Work.BoseFixR.KzEnvAt E ρ`. -/
def bogA {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) (k : Mode) : ℝ :=
  E.tau k + ρ * E.W1 k

/-- FS's `ℬ(k) = ρ_zŴ₁(k)` at the datum `(E, ρ)` — definitionally the `B`-field of
`KzEnvAt E ρ`. -/
def bogB {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) (k : Mode) : ℝ :=
  ρ * E.W1 k

/-- FS's `𝒞(k) = (ρ_z−μ)Ŵ₁(0)χ̂(kℓ)z` at the datum `(E, ρ)` (the corrected
normalisation: no spurious `ℓ⁻³`). -/
def bogC {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) (k : Mode) : ℝ :=
  (ρ - E.mu) * E.W1 0 * E.hatChi k * bogZ E ρ

/-- FS `thm:BogHamDiag`'s `𝒟_k = ½(𝒜_k + √(𝒜_k²−ℬ_k²))` at `(E, ρ)` — the
`D`-field of `KzEnvAt E ρ`. -/
def bogD {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) (k : Mode) : ℝ :=
  Submission.BoseGases.bogD (bogA E ρ k) (bogB E ρ k)

/-- FS `eq:Defb_k`'s squeezing parameter `α_k = ℬ_k/(𝒜_k+√(𝒜_k²−ℬ_k²))` at `(E, ρ)`
— the `alpha`-field of `KzEnvAt E ρ`. -/
def bogAlpha {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) (k : Mode) : ℝ :=
  Submission.BoseGases.bogAlpha (bogA E ρ k) (bogB E ρ k)

/-- FS `eq:Defb_k`'s **shift** `c_k = 2𝒞_k/(𝒜_k+ℬ_k+√(𝒜_k²−ℬ_k²))` at `(E, ρ)`.
(FS's `b_k` is `a_k + α_ka_{-k}† + c_k`, so this is the `c`-number part of `b_k`.) -/
def bogGamma {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) (k : Mode) : ℝ :=
  Submission.BoseGases.fmsGamma (bogA E ρ k) (bogB E ρ k) (bogC E ρ k)

/-- FS's pair quadratic `𝒜_k(n_k+n_{-k}) + ℬ_k(a_ka_{-k}+a_k†a_{-k}†)
+ 𝒞_k(a_k+a_k†+a_{-k}+a_{-k}†)` for one mode pair, as an operator. -/
def bogPairOp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) (k : Mode) :
    F.H →ₗ[ℝ] F.H :=
  (bogA E ρ k) • (F.nOp k + F.nOp (-k))
    + (bogB E ρ k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))
    + (bogC E ρ k) • (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))

/-- The **shifted squeezing operator** `b_k + c_k` of FS `eq:Defb_k` at `(E, ρ)`. -/
def bogBShift {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) (k : Mode) :
    F.H →ₗ[ℝ] F.H :=
  F.bOp (bogAlpha E ρ) k + (bogGamma E ρ k) • (1 : F.H →ₗ[ℝ] F.H)

/-- Its formal adjoint `(b_k+c_k)†` (the shift is real). -/
def bogBShiftDag {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) (k : Mode) :
    F.H →ₗ[ℝ] F.H :=
  F.bOpDag (bogAlpha E ρ) k + (bogGamma E ρ k) • (1 : F.H →ₗ[ℝ] F.H)

/-- The commutator sum `[a_k,a_k†] + [a_{-k},a_{-k}†]` of the pair `(k,−k)`. -/
def bogCcr2 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (F : Work.BoseB7.FockData Mode)
    (k : Mode) : ℝ :=
  F.ccrK k k + F.ccrK (-k) (-k)

/-! ## 4. The FS-correct diagonal reserve (`b_k` *shifted*) -/

/-- **FS's diagonalised quadratic** `(2π)⁻³ℓ³∫𝒟_kb_k†b_k dk` with FS's `b_k` of
`eq:Defb_k` (the shift `c_k` *inside* `b_k`), restricted to a region `R`.  This is the
operator of `thm:BogHamDiag` and of `thm:Control3Q`'s `eq:Q3Cancels`. -/
def dNumOpShifted {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) (R : Mode → Prop)
    [DecidablePred R] : F.H →ₗ[ℝ] F.H :=
  ∑ k ∈ (Work.BoseB7.excited Mode).filter R,
    (bogD E ρ k) • ((bogBShiftDag F E ρ k) ∘ₗ (bogBShift F E ρ k))

/-! ## 5. The corrected close threshold -/

/-- FS `eq:Close`'s threshold with the universal constant `1/(2¹⁴π)` (`F9`): the
`(ρ−μ)²` from the `𝒞`-sum lands, through `2²⁸π²`, exactly on the `(R/a)²√(μa³)` slot of
the §11 error bracket.  (`Work.BoseFixR.closeThreshold` is `μK_ℓ⁻²`, which carries the
right monomial but with the free constant of `eq:Close`.) -/
def closeThresholdFS (v : ℝ³ → ℝ) (μ : ℝ) : ℝ :=
  μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)

/-- `eq:Close` at the corrected threshold: `|ρ_z − μ| ≤ μK_ℓ⁻²/(2¹⁴π)`. -/
def CloseCondFS (v : ℝ³ → ℝ) (μ ρ : ℝ) : Prop := |ρ - μ| ≤ closeThresholdFS v μ

/-! ## 6. The corrected `§10` kernel gate (verbatim `Q3KernelFS`) -/

/-- **The honest `§10` kernel interface** (`Work.BoseK15.Q3Kernel'` with four rows
repaired; verbatim `Work.BoseBoxFock.Q3KernelFS`):
* `kmom_sub`, `hasKernel` only where `Ŵ₁(k) ≠ 0` — the unguarded rows are unsatisfiable
  on any finite lattice (`Work.BoseBoxFock` F1);
* `fL_supp2` with FS's support `|s| ≤ 2K_L√(μa)`;
* `q2exLowerR` with the reserve `½·dNumOpR` on `RHi ∖ P_H^q`. -/
abbrev Q3KernelFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (K₀ : ℝ) (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) : Prop :=
  Work.BoseBoxFock.Q3KernelFS K₀ F T E

/-! ## 7. The corrected view (`RViewFS`)

The design's `RViewFS` pins `E.tau` to the smoothed symbol `tauSm` defined from the
chosen profile `τ̃` of `exists_tauProf`; the pin below carries the profile
existentially instead (same content, no `Classical.choose` needed until the
`D-FS` module lands).  `uvCut` and `etaH` are verbatim. -/

/-- The UV cut-off `ζ_Λ(k) = f_u(|k|/Λ)` (a `LowCut`: `1` on `|k| ≤ Λ`, `0` on `|k| ≥ 2Λ`).
Verbatim `Work.BoseBoxFock.uvCut`. -/
def uvCut (fu : LowCut) (Λ : ℝ) (k : ℝ³) : ℝ := fu.f (‖k‖ / Λ)

/-- FS's `n₊^H` threshold profile on the χ-modes: `η_H(k) = 1 − f_u(|k|/(2κ))`, i.e. `0`
for `|k| ≤ 2κ`, `1` for `|k| ≥ 4κ`, with `κ = K_L√(μa) = (d²ℓ)⁻¹`.
Verbatim `Work.BoseBoxFock.etaH`. -/
def etaH (fu : LowCut) (κ : ℝ) (k : ℝ³) : ℝ := 1 - fu.f (‖k‖ / (2 * κ))

/-- The smoothed kinetic symbol pin of the corrected view: `E.tau` is
`τ̃ = (1−ε_T)c²φ(|k|/c) + ε_T c'²φ(|k|/c')` at `c = (2sℓ)⁻¹`, `c' = (2dsℓ)⁻¹` with `φ`
the profile of `exists_tauProf` (`(r−2)₊² ≤ φ ≤ (r−1)₊²`, `φ = 0` on `r ≤ 1`, smooth,
monotone). -/
def tauSmPin {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) : Prop :=
  ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ Monotone φ ∧
    (∀ r, (max 0 (r - 2)) ^ 2 ≤ φ r) ∧ (∀ r, φ r ≤ (max 0 (r - 1)) ^ 2) ∧
    (∀ r, r ≤ 1 → φ r = 0) ∧
    E.tau = (fun k => (1 - E.eT) * ((2 * E.s * E.ell)⁻¹) ^ 2
          * φ (‖F.kmom k‖ / (2 * E.s * E.ell)⁻¹)
        + E.eT * ((2 * E.d * E.s * E.ell)⁻¹) ^ 2
          * φ (‖F.kmom k‖ / (2 * E.d * E.s * E.ell)⁻¹))

/-! ## 8. The corrected view (verbatim `RViewFS`) -/

/-- **The corrected view.**  Changes against `Work.BoseFixR.RView`:
(i) `E.tau` pinned to the smoothed `τ̃`; (ii) `E.W1` pinned to `ζ·Ŵ₁` at some cut-off
radius `Λ ≥ 4K_L√(μa)` (so `supp f_L` and `supp ζ` cannot wrap); (iii) `T.NH` pinned to
the χ-mode `n₊^H`; (iv) the Bessel conjunct over **all** χ-labels with an absolute cap
`Cn ≤ 16`; (v) the gate is `Q3KernelFS`.

This is verbatim `Work.BoseBoxFock.RViewFS`. -/
def RViewFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ) (F : Work.BoseB7.FockData Mode)
    (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : Prop :=
  Nonempty (Work.BoseB7.FSParamsView E) ∧ E.mu = μ ∧ E.aScat = a v
    ∧ E.ell = ell v μ ∧ E.bigM = bigM (paramsAt μ (a v)) (a v) μ
    ∧ E.b = (paramsAt μ (a v)).b ∧ E.d = (paramsAt μ (a v)).d
    ∧ E.s = (paramsAt μ (a v)).s ∧ E.eT = (paramsAt μ (a v)).eT
    ∧ E.intM = (paramsAt μ (a v)).M ∧ gHat0 = 8 * π * a v
    ∧ tauSmPin F E
    ∧ E.A = (fun k => E.tau k + E.rho * E.W1 k)
    ∧ E.B = (fun k => E.rho * E.W1 k)
    ∧ (∃ (fu : LowCut) (Λ : ℝ), 4 * (E.KL * Real.sqrt (E.mu * E.aScat)) ≤ Λ ∧
        E.W1 = (fun k => uvCut fu Λ (F.kmom k) * chat (W1fun v h (ell v μ)) (F.kmom k)))
    ∧ E.W1omega = (fun k => chat (W1omegaFun v h (ell v μ)) (F.kmom k))
    ∧ E.W1omega0 = chat (W1omegaFun v h (ell v μ)) 0
    ∧ E.hatChi = (fun k => chat (chiFun (ell v μ)) (F.kmom k)
        / chat (fun z => chiFun (ell v μ) z ^ 2) 0)
    ∧ E.hatChiSq = (fun k =>
        chat (fun z => chiFun (ell v μ) z ^ 2) (F.kmom k)
          / chat (fun z => chiFun (ell v μ) z ^ 2) 0)
    ∧ (∃ fc : LowCut, E.fL = (fun k => fLFS fc E.KL E.mu E.aScat (F.kmom k)))
    ∧ (∃ fu : LowCut, T.NH = (1 / 32 : ℝ) • ∑ k ∈ Work.BoseB7.excited Mode,
        etaH fu (E.KL * Real.sqrt (E.mu * E.aScat)) (F.kmom k) • F.nOp k)
    ∧ (∃ Cn : ℝ, 0 ≤ Cn ∧ Cn ≤ 16 ∧
        ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    ∧ (∃ K₀ b₀ : ℝ, 0 ≤ K₀ ∧ 0 < b₀ ∧ b₀ ≤ E.b
        ∧ ∀ ρ : ℝ, CloseCondFS v μ ρ → Q3KernelFS K₀ F T (KzEnvAt E ρ))

-- `Work.BoseFixR.KzDatum.viewFS` is **not** defined here: it is the canonical declaration of
-- `Submission.Work.BoseBoxFock.Defs` (node `D-FS`, which has landed), imported below.  The
-- chapter's `RViewFS` above agrees with the canonical `Work.BoseBoxFock.RViewFS` in 22 of its
-- 23 conjuncts (conjunct 12 is `tauSmPin` here vs `E.tau = tauSm …` there); a consumer holding
-- the canonical view uses the bridge `Work.BoseBogFS.RViewFS_of_canonical`, **proved** in
-- `ViewBridge.lean` (`tauSmPin` obtained from `E.tau = tauSm …` via
-- `Classical.choose_spec Work.BoseBoxFock.exists_tauProf`); and `Q3KernelFS` below *is* the
-- canonical `Work.BoseBoxFock.Q3KernelFS` (an `abbrev`).

/-! ## 8. `BogOpBoundFS` (verbatim `BOSE_BOXFOCK_STATEMENTS.lean.txt` §5.4) -/

/-- **FS `eq:Combined1` (`thm:BogHamDiag` + `lem:BogIntegral`), corrected.**  Against
`Work.BoseFixR.BogOpBound`: (i) `KzBogFS` (the honest `𝒦^Bog`, `½` per mode, the
`𝒬₁`-normalisation `(ρ−μ)Ŵ₁(0)χ̂(kℓ)z`, the `χ`-label `0` kept in the sums); (ii) the
diagonal reserve is `dNumOpR` on `RHi` only — with the `𝒞`-term the unshifted
`Σ_{all k}𝒟b†b` cannot be split off (the linear word is `O(μK_ℓ⁻²a√(μℓ³)√𝓜)`,
`X^{-116}` times LHY, on window states); FS complete it into the shifted `b+c` on the
low modes, which is then dropped as `≥ 0`, and `c_k = O(χ̂(kℓ))` is negligible on `RHi`;
(iii) the `κ`-sum's `½(ρ−μ)²ℓ³ĝ(0)` is on the right (FS cancel it against the
`c`-number).

This is verbatim `Work.BoseBoxFock.BogOpBoundFS`; `bogOpBoundFS` below is the same
statement in this chapter's namespace (one is derived from the other by `Iff.rfl`). -/
def BogOpBoundFS (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ →
      ∀ ρ : ℝ, 0 ≤ ρ → CloseCond v μ ρ →
        ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
          (4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3)
              - C * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
                  * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ))
              * (D μ).F.normSq f
            + (D μ).F.qw f ((D μ).F.dNumOpR (KzEnvAt (D μ).E ρ) (RHi (D μ).F (KzEnvAt (D μ).E ρ)))
          ≤ (D μ).F.qw f (KzBogFS (D μ).F (D μ).E ρ)
            + ((1 / 2) * ρ ^ 2 * (D μ).E.ell ^ 3 * (D μ).E.W1omega0
                + (1 / 2) * (ρ - μ) ^ 2 * (D μ).E.ell ^ 3 * (D μ).gHat0) * (D μ).F.normSq f

end Work.BoseBogFS
