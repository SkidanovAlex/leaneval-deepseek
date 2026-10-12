import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.ZpError
import Submission.Work.BoseBogFS.hZP_of_match_mis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.SharpSlots` — the `hZP`/`hKAP` slots at a *general* density

`FINDING_zpRiemErr.md` records why the crude lattice-Riemann error
`Work.BoseB6Est.zpRiemErr` (`10⁴((n:ℝ)+1)³ + const`) can be absorbed by the §11 bracket
for *no* uniform constant, so the capstone of this chapter has to be re-issued with a
*sharp* error in **two** of its slots: the zero-point slot `hZP` and the error slot
`hEzero` (both read off `Work.BoseB6Est.fsZeroPoint_le`).

`FINDING_mismatch_weighting.md` (this session) records a second, independent defect of the
first sharp candidate `zpRiemErrSharp n B η = 10⁸(1+B)(δ log(1/δ) + η·((n:ℝ)+1))`: the
mesh-mismatch weight `η·((n:ℝ)+1)` is **bounded below by a constant** (`η ≥ 1/(2K_ℓ)` and
`(n:ℝ)+1 ≈ K_ℓ`), hence not vanishing, hence *not absorbable* by the §11 bracket.  The
correct weight is `η`, unweighted: `zpRiemErrSharpEta n B η = 10⁸(1+B)(δ log(1/δ) + η)`.

This module collects the slot producers on the corrected data, with the error budget kept
as an **explicit parameter** `Er` so that both candidates (and any future refinement) fit
the same interface:

* `zpErrorOf`/`zpScalarOf` — the zero-point error slot with budget `Er`;
  `zpErrorSharp`/`zpErrorSharpEta` are the two instances;
* `SharpCmpWith`/`SharpCmp` — the sharpened lattice comparison with budget `Er`;
* `hZP_slot_transfer` — the `hZP` slot at an **arbitrary** density `ρ`, from
  `hZP_transfer` (which needs the mode identification `FsMatch` at that same `ρ`, the `I₁`
  regime *without* the mesh relation `(n:ℝ)+1 = ℓ√(ρ_za)`, the **relative two-sided**
  mismatch `hmis` with `η ≤ 1/4`, and the comparison as a hypothesis);
  `hZP_slot_sharp`/`hZP_slot_sharpEta` are its two instances;
* `hKAP_slot_i1` — the `𝒞`-sum slot, with `FsZeroRegime` weakened to `FsI1Regime` + `0 < ℓ`
  (the proof of `hKAP_of_match` uses only those rows, and with a `ρ`-indexed identification
  the mesh relation `hrel` is not available — indeed it is *unsatisfiable* at a general `ρ`,
  `FINDING_mesh_integrality.md`).

With these, the refined capstone `bogOpBoundFS_of_sharpData` removes the `hZP`/`hKAP` slot
families from the interface entirely, leaving only the comparison `hsharp`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7 Work.BoseB6Est

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **The lattice error with the correct mismatch weight** (this session's correction):
`10⁸(1+B)·(δ·log(1/δ) + η)` with `δ = meshD n`.  Unlike
`zpRiemErrSharp = 10⁸(1+B)(δ log(1/δ) + η(n+1))`, this *vanishes* at FS's parameters, which
is what the §11 bracket needs — see `FINDING_mismatch_weighting.md` for the derivation of
the correct weight `η` (the mismatch only rescales the model sum by `(1+θ)^{-3}`, so the
extra slack it forces is `O(η)`, not `O(η(n+1))`). -/
abbrev zpRiemErrSharpEta (n : ℕ) (B η : ℝ) : ℝ :=
  10 ^ 8 * (1 + B) * (Work.BoseB6.meshD n * Real.log (1 / Work.BoseB6.meshD n) + η)

/-- The **zero-point error slot with an explicit budget** `Er`: `zpError` (`FsFinal.lean`)
with the crude `Work.BoseB6Est.zpRiemErr n K c₂` replaced by `Er`.

Like `zpError`, this is an `abbrev`, so it unfolds transparently and matching against it is
never a transparency issue. -/
abbrev zpErrorOf (ℓ a R εT Kl s d μ ρ : ℝ) (n : ℕ) (Er : ℝ) : ℝ :=
  (1 / 2) * (((2 * π) ^ 3)⁻¹ * ℓ ^ 3 * (ρ ^ 2 * a * Real.sqrt (ρ * a ^ 3))
        * (Work.BoseB6.latticeMeshErr (8 * π) n + Er)
      + 10 ^ 10 * Work.BoseB6.lhyEps a R εT Kl s d μ * ρ ^ 2 * a * Real.sqrt (ρ * a ^ 3)
          * ℓ ^ 3)

/-- **The corrected budget with the `fsI2` mismatch weight** (from the two delegated provers'
refutations this session): the mesh-mismatch factor `σ³ − 1 = O(η)` multiplies the *whole*
bracket in the reduction, including `fsI2 K = ∫β²/(2‖t‖²) = O(K.T)` (unbounded above in
`FsI1Regime`) and the `10¹⁰ε` term, so a budget of the form `10⁸(1+B)(δ log(1/δ) + η)` is
**refuted** by an explicit configuration (`K.T = 10⁸`, `β ≡ 8π`, `η = 1/4`).  The corrected
budget carries the same factors as the terms it must dominate:

`zpRiemErrSharpL n K η ε = 10¹⁴(1+K.B)·(δ·log(1/δ) + η·(1 + ε + fsI2 K))`, `δ = meshD n`.

It still vanishes at FS's parameters (`δ log(1/δ) ≈ X^{3/2}log`, `η ≈ 1/(2K_ℓ) = X^{3/2}/2`,
`η·lhyEps ≲ X^{3/2}·errSlot`, and `η·fsI2` is controlled by the row `hfsI2`), so it remains
absorbable by the §11 bracket — see `FINDING_zpRiem_sharp_status.md`. -/
abbrev zpRiemErrSharpL (n : ℕ) (K : FsKernel) (η ε : ℝ) : ℝ :=
  10 ^ 14 * (1 + K.B) * (Work.BoseB6.meshD n * Real.log (1 / Work.BoseB6.meshD n)
    + η * (1 + ε + fsI2 K))

/-- The **sharp** zero-point error slot: budget `zpRiemErrSharp`. -/
abbrev zpErrorSharp (ℓ a R εT Kl s d μ ρ : ℝ) (n : ℕ) (K : FsKernel) (η : ℝ) : ℝ :=
  zpErrorOf ℓ a R εT Kl s d μ ρ n (zpRiemErrSharp n K.B η)

/-- The **corrected** sharp zero-point error slot: budget `zpRiemErrSharpEta`. -/
abbrev zpErrorSharpEta (ℓ a R εT Kl s d μ ρ : ℝ) (n : ℕ) (K : FsKernel) (η : ℝ) : ℝ :=
  zpErrorOf ℓ a R εT Kl s d μ ρ n (zpRiemErrSharpEta n K.B η)

/-- The scalar part of `zpErrorOf` (everything except the physical prefactor `ℓ³ρ²a√(ρa³)`). -/
def zpScalarOf (a R εT Kl s d μ : ℝ) (n : ℕ) (Er : ℝ) : ℝ :=
  (1 / 2) * ((2 * π) ^ 3)⁻¹ * (Work.BoseB6.latticeMeshErr (8 * π) n + Er)
    + (1 / 2) * 10 ^ 10 * Work.BoseB6.lhyEps a R εT Kl s d μ

/-- The scalar part of `zpErrorSharp`. -/
def zpScalarSharp (a R εT Kl s d μ : ℝ) (n : ℕ) (K : FsKernel) (η : ℝ) : ℝ :=
  zpScalarOf a R εT Kl s d μ n (zpRiemErrSharp n K.B η)

/-- The scalar part of `zpErrorSharpEta`. -/
def zpScalarSharpEta (a R εT Kl s d μ : ℝ) (n : ℕ) (K : FsKernel) (η : ℝ) : ℝ :=
  zpScalarOf a R εT Kl s d μ n (zpRiemErrSharpEta n K.B η)

/-- **`zpErrorOf` factors through the scalar `zpScalarOf`.**  The physical prefactor
`ℓ³ρ²a√(ρa³)` is exactly the one of `zpError` (`zpError_eq_zpScalar`), so the `hEzero` slot
reduces to the same kind of scalar inequality. -/
theorem zpErrorOf_eq_zpScalarOf (ℓ a R εT Kl s d μ ρ : ℝ) (n : ℕ) (Er : ℝ) :
    zpErrorOf ℓ a R εT Kl s d μ ρ n Er
      = ℓ ^ 3 * (ρ ^ 2 * a * Real.sqrt (ρ * a ^ 3)) * zpScalarOf a R εT Kl s d μ n Er := by
  rw [zpErrorOf, zpScalarOf]
  ring

theorem zpErrorSharp_eq_zpScalarSharp (ℓ a R εT Kl s d μ ρ : ℝ) (n : ℕ) (K : FsKernel)
    (η : ℝ) :
    zpErrorSharp ℓ a R εT Kl s d μ ρ n K η
      = ℓ ^ 3 * (ρ ^ 2 * a * Real.sqrt (ρ * a ^ 3)) * zpScalarSharp a R εT Kl s d μ n K η :=
  zpErrorOf_eq_zpScalarOf ℓ a R εT Kl s d μ ρ n (zpRiemErrSharp n K.B η)

/-- **The sharpened lattice comparison with an explicit budget `Er`**, in the exact shape
consumed by `hZP_slot_transfer` (and hence by the capstone):
`Work.BoseB6Est.fsZeroPoint_le`'s conclusion with the crude `Work.BoseB6Est.zpRiemErr`
replaced by `Er`, at the `FsMatch` data. -/
abbrev SharpCmpWith {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 : ℝ) (M : FsMatch F E ρ gHat0) (Er : ℝ) :
    Prop :=
  zpSum M.n M.D.ρz M.D.a M.D.K M.D.εT M.D.c1 M.D.c2
    ≤ ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3))
        * ((Work.BoseB6.meshD M.n) ^ 3 * Work.BoseB6.latticeSum (8 * π) M.n)
      + fsMass M.D.ρz M.D.a M.D.ℓ M.D.K
      + 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
          * M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3) * M.D.ℓ ^ 3
      + ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3))
          * Er

/-- The sharpened lattice comparison with the budget `zpRiemErrSharp` — the shape produced
by `fsZeroPoint_le_sharp` (first delegation). -/
abbrev SharpCmp {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 : ℝ) (M : FsMatch F E ρ gHat0) (η : ℝ) :
    Prop :=
  SharpCmpWith F E ρ gHat0 M (zpRiemErrSharp M.n M.D.K.B η)

/-- The sharpened lattice comparison with the **corrected** budget `zpRiemErrSharpEta`. -/
abbrev SharpCmpEta {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 : ℝ) (M : FsMatch F E ρ gHat0) (η : ℝ) :
    Prop :=
  SharpCmpWith F E ρ gHat0 M (zpRiemErrSharpEta M.n M.D.K.B η)

/-- **The `hZP` slot at an arbitrary density `ρ`, with an explicit budget `Er`.**
`hZP_transfer` produces the bound with the *environment's* parameters; the view identifies
`E.aScat = a v`, `E.ell = ell v μ` and `FsMatch` identifies `M.D.a = E.aScat`, which turns it
into the shape the assembly consumes (`bogOpBound_at`'s `hZP`, with `Ezero := zpErrorOf … Er`). -/
theorem hZP_slot_transfer (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ)
    (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 η Er : ℝ)
    (M : FsMatch F E ρ gHat0)
    (hi1 : FsI1Regime M.D.K M.D.a M.D.R M.D.ρz M.D.μ M.D.εT M.D.c1 M.D.c2 M.D.Kl M.D.s M.D.d)
    (hn : 1 ≤ M.n) (hℓ : 0 < M.D.ℓ)
    (hmis : |(M.n : ℝ) + 1 - M.D.ℓ * Real.sqrt (M.D.ρz * M.D.a)|
      ≤ η * (M.D.ℓ * Real.sqrt (M.D.ρz * M.D.a)))
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (hsharp : SharpCmpWith F E ρ gHat0 M Er)
    (haScat : E.aScat = a v) (hell : E.ell = ell v μ) (haD : M.D.a = a v) :
    (∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k))
      ≤ -(4 * π * Work.UBB.lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3))
        + (1 / 2) * ell3 v μ * ρ ^ 2 * E.W1omega0
        + zpErrorOf (ell v μ) (a v) M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ ρ M.n Er := by
  have hmain := hZP_transfer F E ρ gHat0 η Er M hi1 hn hℓ hmis hη hη1 hsharp
  rw [haScat, hell, haD] at hmain
  simpa only [zpErrorOf, ell3] using hmain

/-- **The `hZP` slot at an arbitrary density `ρ`**, with the budget `zpRiemErrSharp`
(`fsZeroPoint_le_sharp`). -/
theorem hZP_slot_sharp (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ)
    (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 η : ℝ)
    (M : FsMatch F E ρ gHat0)
    (hi1 : FsI1Regime M.D.K M.D.a M.D.R M.D.ρz M.D.μ M.D.εT M.D.c1 M.D.c2 M.D.Kl M.D.s M.D.d)
    (hn : 1 ≤ M.n) (hℓ : 0 < M.D.ℓ)
    (hmis : |(M.n : ℝ) + 1 - M.D.ℓ * Real.sqrt (M.D.ρz * M.D.a)|
      ≤ η * (M.D.ℓ * Real.sqrt (M.D.ρz * M.D.a)))
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (hsharp : SharpCmp F E ρ gHat0 M η)
    (haScat : E.aScat = a v) (hell : E.ell = ell v μ) (haD : M.D.a = a v) :
    (∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k))
      ≤ -(4 * π * Work.UBB.lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3))
        + (1 / 2) * ell3 v μ * ρ ^ 2 * E.W1omega0
        + zpErrorSharp (ell v μ) (a v) M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ ρ M.n M.D.K η :=
  hZP_slot_transfer v h μ F E ρ gHat0 η (zpRiemErrSharp M.n M.D.K.B η) M hi1 hn hℓ hmis hη
    hη1 hsharp haScat hell haD

/-- **The `hZP` slot at an arbitrary density `ρ`**, with the **corrected** budget
`zpRiemErrSharpEta` — the absorbable one (`FINDING_mismatch_weighting.md`). -/
theorem hZP_slot_sharpEta (v : ℝ³ → ℝ) (h : ScatSol v) (μ : ℝ)
    (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 η : ℝ)
    (M : FsMatch F E ρ gHat0)
    (hi1 : FsI1Regime M.D.K M.D.a M.D.R M.D.ρz M.D.μ M.D.εT M.D.c1 M.D.c2 M.D.Kl M.D.s M.D.d)
    (hn : 1 ≤ M.n) (hℓ : 0 < M.D.ℓ)
    (hmis : |(M.n : ℝ) + 1 - M.D.ℓ * Real.sqrt (M.D.ρz * M.D.a)|
      ≤ η * (M.D.ℓ * Real.sqrt (M.D.ρz * M.D.a)))
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (hsharp : SharpCmpEta F E ρ gHat0 M η)
    (haScat : E.aScat = a v) (hell : E.ell = ell v μ) (haD : M.D.a = a v) :
    (∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k))
      ≤ -(4 * π * Work.UBB.lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3))
        + (1 / 2) * ell3 v μ * ρ ^ 2 * E.W1omega0
        + zpErrorSharpEta (ell v μ) (a v) M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ ρ M.n
            M.D.K η :=
  hZP_slot_transfer v h μ F E ρ gHat0 η (zpRiemErrSharpEta M.n M.D.K.B η) M hi1 hn hℓ hmis
    hη hη1 hsharp haScat hell haD

/-- **The `𝒞`-sum slot with `FsZeroRegime` weakened to `FsI1Regime` + `0 < ℓ`.**

`hKAP_of_match`'s proof consumes only the `I₁`-regime rows, `0 < ℓ` and the datum's own
`hℓ3 : 3 ≤ ℓ³`; the mesh relation `hrel` of `FsZeroRegime` is never used.  At a
`ρ`-indexed identification this matters: `hrel` is unsatisfiable at a general close `ρ`
(`FINDING_mesh_integrality.md`). -/
theorem hKAP_slot_i1 (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 : ℝ)
    (M : FsMatch F E ρ gHat0)
    (hi1 : FsI1Regime M.D.K M.D.a M.D.R M.D.ρz M.D.μ M.D.εT M.D.c1 M.D.c2 M.D.Kl M.D.s M.D.d)
    (hℓ : 0 < M.D.ℓ) :
    (∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k)
        (bogC E ρ k))
      ≤ (ρ - E.mu) ^ 2 * (gHat0 / 2) * E.ell ^ 3 * (1 + M.D.δ) := by
  have hρa : 0 < M.D.ρz * M.D.a := mul_pos hi1.hρz hi1.ha
  have hAB : ∀ k : modeIdx M.n,
      M.D.χh (modePos M.n k) ≠ 0 →
      (16 * Real.pi - 2) * (M.D.ρz * M.D.a)
        ≤ fsA M.D.ρz M.D.a M.D.K M.D.εT M.D.c1 M.D.c2 (modePos M.n k)
          + fsB M.D.ρz M.D.a M.D.K (modePos M.n k) :=
    fun k hk => fsAB_ge M.D.K M.D.χh hρa.le hi1.hε0
      (by linarith [hi1.hε1]) hi1.hηT M.D.hχsupp hk
  have hkappa : kappaSum M.n M.D.ρz M.D.a M.D.ℓ M.D.μ M.D.z M.D.K
      M.D.εT M.D.c1 M.D.c2 M.D.χh
      ≤ fsEkappa M.D.ρz M.D.a M.D.ℓ M.D.μ M.D.z M.D.chiM M.D.δ :=
    kappaSum_le M.D.K M.D.χh hρa hℓ M.D.hchiM M.D.hδ
      M.D.hℓ3 M.D.hχnorm hAB
  have hhalf :
      (∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k)
          (bogC E ρ k))
        = (1 / 2) * kappaSum M.n M.D.ρz M.D.a M.D.ℓ M.D.μ M.D.z M.D.K
            M.D.εT M.D.c1 M.D.c2 M.D.χh := by
    rw [← Finset.mul_sum]
    rw [sum_kap_eq F E ρ gHat0 M]
  have hE : 0 ≤ fsEkappa M.D.ρz M.D.a M.D.ℓ M.D.μ M.D.z M.D.chiM M.D.δ := by
    have hnum : 0 ≤ 8 * Real.pi * M.D.a * M.D.z ^ 2 * M.D.chiM :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hi1.ha.le) (sq_nonneg _))
        M.D.hchiM
    have hden : 0 ≤ M.D.ρz * M.D.ℓ ^ 3 :=
      mul_nonneg hi1.hρz.le (pow_nonneg hℓ.le 3)
    have hG : 0 ≤ fsG0 M.D.ρz M.D.a M.D.ℓ M.D.z M.D.chiM / 2 :=
      div_nonneg (div_nonneg hnum hden) (by norm_num)
    have hsq : 0 ≤ (M.D.ρz - M.D.μ) ^ 2 := sq_nonneg _
    have h1δ : 0 ≤ 1 + M.D.δ := by linarith [M.D.hδ]
    rw [fsEkappa]
    exact mul_nonneg (mul_nonneg (mul_nonneg hsq hG) (pow_nonneg hℓ.le 3)) h1δ
  rw [hhalf]
  calc (1 / 2) * kappaSum M.n M.D.ρz M.D.a M.D.ℓ M.D.μ M.D.z M.D.K
        M.D.εT M.D.c1 M.D.c2 M.D.χh
      ≤ (1 / 2) * fsEkappa M.D.ρz M.D.a M.D.ℓ M.D.μ M.D.z M.D.chiM M.D.δ :=
        mul_le_mul_of_nonneg_left hkappa (by norm_num : (0 : ℝ) ≤ 1 / 2)
    _ ≤ fsEkappa M.D.ρz M.D.a M.D.ℓ M.D.μ M.D.z M.D.chiM M.D.δ := by
        linarith [hE]
    _ = (ρ - E.mu) ^ 2 * (gHat0 / 2) * E.ell ^ 3 * (1 + M.D.δ) := by
        rw [fsEkappa, M.hG0, M.hρ, M.hμ, M.hℓ]

/-- **The `hEzero` slot reduces to the scalar inequality, for an arbitrary budget `Er`.**
The physical prefactors `ℓ³ρ²a√(ρa³)` cancel against
`errBracket = μ²aℓ³√(dil)·errSlot`: it suffices that `ρ²√(ρa³) ≤ 4μ²√(μa³)` (FS's close
region gives `ρ ≤ (3/2)μ`) and that the scalar part is `C·errSlot`. -/
theorem zpErrorOf_le_scalar (v : ℝ³ → ℝ) (R μ ρ : ℝ) (εT Kl s d : ℝ) (n : ℕ) (Er C : ℝ)
    (hav : 0 < a v) (hμ : 0 < μ) (hC : 0 ≤ C) (hℓ : 0 ≤ ell v μ) (hρ : 0 ≤ ρ)
    (hρμ : ρ ^ 2 * Real.sqrt (ρ * a v ^ 3) ≤ 4 * μ ^ 2 * Real.sqrt (μ * a v ^ 3))
    (hscal : zpScalarOf (a v) R εT Kl s d μ n Er ≤ C * errSlot v R μ) :
    zpErrorOf (ell v μ) (a v) R εT Kl s d μ ρ n Er
      ≤ (4 * C) * errBracket v R μ := by
  rw [zpErrorOf_eq_zpScalarOf, errBracket_eq_mul_errSlot]
  have hℓ3 : 0 ≤ ell v μ ^ 3 := pow_nonneg hℓ 3
  have hX : 0 ≤ errSlot v R μ := by
    rw [errSlot]
    have h1 : (0 : ℝ) ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (R / a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h3 : (0 : ℝ) ≤ errExp v μ := by
      rw [errExp]
      exact Real.rpow_nonneg (by rw [Work.BoseFixR.dil]; positivity) _
    linarith
  have hfac : (0 : ℝ) ≤ ell v μ ^ 3 * (ρ ^ 2 * a v * Real.sqrt (ρ * a v ^ 3)) :=
    mul_nonneg hℓ3
      (mul_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt hav)) (Real.sqrt_nonneg _))
  calc ell v μ ^ 3 * (ρ ^ 2 * a v * Real.sqrt (ρ * a v ^ 3))
        * zpScalarOf (a v) R εT Kl s d μ n Er
      ≤ ell v μ ^ 3 * (ρ ^ 2 * a v * Real.sqrt (ρ * a v ^ 3)) * (C * errSlot v R μ) :=
        mul_le_mul_of_nonneg_left hscal hfac
    _ = C * (ell v μ ^ 3 * a v) * (ρ ^ 2 * Real.sqrt (ρ * a v ^ 3)) * errSlot v R μ := by ring
    _ ≤ C * (ell v μ ^ 3 * a v) * (4 * μ ^ 2 * Real.sqrt (μ * a v ^ 3))
          * errSlot v R μ := by
        refine mul_le_mul_of_nonneg_right ?_ hX
        exact mul_le_mul_of_nonneg_left hρμ
          (mul_nonneg hC (mul_nonneg hℓ3 (le_of_lt hav)))
    _ = 4 * C * (μ ^ 2 * a v * ell3 v μ * Real.sqrt (Work.BoseFixR.dil v μ)
          * errSlot v R μ) := by
        rw [ell3, Work.BoseFixR.dil]
        ring

/-- **The `hEzero` slot of the corrected capstone, in scalar form**: for the budget
`zpRiemErrSharpEta` it suffices that
`zpScalarSharpEta (a v) R εT Kl s d μ n K η ≤ C·errSlot v R μ`. -/
theorem zpErrorSharpEta_le_scalar (v : ℝ³ → ℝ) (R μ ρ : ℝ) (εT Kl s d : ℝ) (n : ℕ)
    (K : FsKernel) (η C : ℝ)
    (hav : 0 < a v) (hμ : 0 < μ) (hC : 0 ≤ C) (hℓ : 0 ≤ ell v μ) (hρ : 0 ≤ ρ)
    (hρμ : ρ ^ 2 * Real.sqrt (ρ * a v ^ 3) ≤ 4 * μ ^ 2 * Real.sqrt (μ * a v ^ 3))
    (hscal : zpScalarSharpEta (a v) R εT Kl s d μ n K η ≤ C * errSlot v R μ) :
    zpErrorSharpEta (ell v μ) (a v) R εT Kl s d μ ρ n K η
      ≤ (4 * C) * errBracket v R μ :=
  zpErrorOf_le_scalar v R μ ρ εT Kl s d n (zpRiemErrSharpEta n K.B η) C hav hμ hC hℓ hρ hρμ
    hscal

/-- **The `hEzero` slot of the first delegation (`zpRiemErrSharp`), in scalar form.** -/
theorem zpErrorSharp_le_scalar (v : ℝ³ → ℝ) (R μ ρ : ℝ) (εT Kl s d : ℝ) (n : ℕ)
    (K : FsKernel) (η C : ℝ)
    (hav : 0 < a v) (hμ : 0 < μ) (hC : 0 ≤ C) (hℓ : 0 ≤ ell v μ) (hρ : 0 ≤ ρ)
    (hρμ : ρ ^ 2 * Real.sqrt (ρ * a v ^ 3) ≤ 4 * μ ^ 2 * Real.sqrt (μ * a v ^ 3))
    (hscal : zpScalarSharp (a v) R εT Kl s d μ n K η ≤ C * errSlot v R μ) :
    zpErrorSharp (ell v μ) (a v) R εT Kl s d μ ρ n K η
      ≤ (4 * C) * errBracket v R μ :=
  zpErrorOf_le_scalar v R μ ρ εT Kl s d n (zpRiemErrSharp n K.B η) C hav hμ hC hℓ hρ hρμ
    hscal

end Work.BoseBogFS
