import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseBogFS.hZP_of_match
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.hZP_of_match_mis` — the zero-point slot at a *general* density

`hZP_of_match` closes the chapter's zero-point slot at the **datum's own density**, because
`Work.BoseB6Est.FsZeroRegime.hrel` is the *equality* `(n:ℝ)+1 = ℓ√(ρ_z a)`, so the mesh is
matched only at `ρ = (D μ).E.rho` (`FINDING_mesh_integrality.md`).  The design's
`BogOpBoundFS` however quantifies `ρ` over the whole close region.

This module removes that constraint: it takes

* `FsI1Regime` + `1 ≤ n` + `0 < ℓ` (the rows of `FsZeroRegime` *except* `hrel`),
* a **relative, two-sided** mesh-mismatch hypothesis
  `|(n:ℝ)+1 − ℓ√(ρ_z a)| ≤ η·ℓ√(ρ_z a)` with `η ≤ 1/4` (the honest mismatch is `O(K_ℓ⁻²)`,
  so this costs nothing), and
* the **sharpened lattice comparison** — `fsZeroPoint_le` with the crude counting term
  `zaRiemErr = 10⁴((n:ℝ)+1)³` replaced by the *vanishing* error
  `zpRiemErrSharp n K.B η = 10⁸(1+K.B)(δ log(1/δ) + η((n:ℝ)+1))`, `δ = meshD n`, which
  (unlike `10⁴(n+1)³ = 10⁴X^{-9/2}` and unlike *any* constant) is `o(errExp) = o(X^{1/5})`
  and can therefore be absorbed by the `§11` bracket — see `FINDING_zpRiemErr.md`

as a *hypothesis*, and performs the transfer (`lattice_sum_upper`, `half_lhyValue_eight_pi`,
`hZP_arith`, `sum_zp_eq`), exactly as `hZP_of_match` does.  The moment the analytic
comparison is proved (in `Work.BoseB6Est` or here), this lemma turns it into the chapter's
`hZP` slot at **every** close `ρ`.

Note the shape of the sharp error: it is a *positive* power of the diluteness times a
logarithm, with **no additive constant**.  That is forced: `errSlot = X² + (R/a)²√dil + X^{1/5}`
tends to `0` as `dil → 0`, while `Adm v ε₀ μ` has no lower bound on `dil`, so a slot
`zpScalar ≤ C·errSlot` with a uniform `C` can only hold if the transferred error vanishes —
which rules out *every* constant term, including the `10⁴(1+K.B)²(1+|log(K.T/c₂)|)` term of
the shipped `zpRiemErr` (its `log` is absorbed by `lhyEps` through `FsI1Regime.hEpsLog`).
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

/-- The **sharp lattice error**: `10⁸(1+K.B)·(δ·log(1/δ) + η·((n:ℝ)+1))` with
`δ = meshD n`.  Unlike the crude `10⁴((n:ℝ)+1)³`, this *vanishes* at FS's parameters
(`δ log(1/δ) = X^{3/2}log(1/X)`, `η(n+1) = O(K_ℓ⁻¹)`), which is what the §11 bracket needs. -/
abbrev zpRiemErrSharp (n : ℕ) (B η : ℝ) : ℝ :=
  10 ^ 8 * (1 + B) * (Work.BoseB6.meshD n * Real.log (1 / Work.BoseB6.meshD n)
    + η * ((n : ℝ) + 1))

/-- **The zero-point slot at a general density**, from the sharpened lattice comparison.

`hsharp` is `Work.BoseB6Est.fsZeroPoint_le`'s conclusion with the crude
`Work.BoseB6Est.zpRiemErr` replaced by `zpRiemErrSharp`. -/
theorem hZP_transfer (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 η Er : ℝ)
    (M : FsMatch F E ρ gHat0)
    (hi1 : FsI1Regime M.D.K M.D.a M.D.R M.D.ρz M.D.μ M.D.εT M.D.c1 M.D.c2 M.D.Kl M.D.s M.D.d)
    (hn : 1 ≤ M.n) (hℓ : 0 < M.D.ℓ)
    (hmis : |(M.n : ℝ) + 1 - M.D.ℓ * Real.sqrt (M.D.ρz * M.D.a)|
      ≤ η * (M.D.ℓ * Real.sqrt (M.D.ρz * M.D.a)))
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (hsharp : zpSum M.n M.D.ρz M.D.a M.D.K M.D.εT M.D.c1 M.D.c2
      ≤ ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3))
          * ((Work.BoseB6.meshD M.n) ^ 3 * Work.BoseB6.latticeSum (8 * π) M.n)
        + fsMass M.D.ρz M.D.a M.D.ℓ M.D.K
        + 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
            * M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3) * M.D.ℓ ^ 3
        + ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3))
            * Er) :
    (∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k))
      ≤ -(4 * π * Work.UBB.lhyC * ρ ^ 2 * E.aScat * E.ell ^ 3
            * Real.sqrt (ρ * E.aScat ^ 3))
        + (1 / 2) * E.ell ^ 3 * ρ ^ 2 * E.W1omega0
        + (1 / 2) * (((2 * π) ^ 3)⁻¹ * E.ell ^ 3
              * (ρ ^ 2 * E.aScat * Real.sqrt (ρ * E.aScat ^ 3))
              * (Work.BoseB6.latticeMeshErr (8 * π) M.n + Er)
            + 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
                * ρ ^ 2 * M.D.a * Real.sqrt (ρ * M.D.a ^ 3) * E.ell ^ 3) := by
  -- the sharpened lattice comparison (hypothesis) and the sharp lattice model bound
  have hz := hsharp
  have hmesh := Work.BoseB6.lattice_sum_upper (c := 8 * π) (by positivity) hn
  -- the prefactor is nonnegative
  have hCc : 0 ≤ ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3
      * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)) := by
    have hρz : 0 < M.D.ρz := hi1.hρz
    have ha : 0 < M.D.a := hi1.ha
    positivity
  -- `½·C·lhyValue(8π) = 4π·lhyC·ρ_z²aℓ³√(ρ_z a³)`
  have hCV : (1 / 2) * ((((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3
          * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
        * Work.BoseB6.lhyValue (8 * π))
      = 4 * π * Work.UBB.lhyC * M.D.ρz ^ 2 * M.D.a * M.D.ℓ ^ 3
        * Real.sqrt (M.D.ρz * M.D.a ^ 3) := by
    have key := Work.BoseBogFS.half_lhyValue_eight_pi
    calc (1 / 2) * ((((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3
            * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
          * Work.BoseB6.lhyValue (8 * π))
        = (M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
            * ((1 / 2) * ((2 * π) ^ 3)⁻¹ * Work.BoseB6.lhyValue (8 * π)) := by ring
      _ = (M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
            * (4 * π * Work.UBB.lhyC) := by rw [key]
      _ = 4 * π * Work.UBB.lhyC * M.D.ρz ^ 2 * M.D.a * M.D.ℓ ^ 3
            * Real.sqrt (M.D.ρz * M.D.a ^ 3) := by ring
  -- the arithmetic core, at the sharp error slot
  have hmain := hZP_arith
    (A := zpSum M.n M.D.ρz M.D.a M.D.K M.D.εT M.D.c1 M.D.c2)
    (Cc := ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
    (ML := Work.BoseB6.meshD M.n ^ 3 * Work.BoseB6.latticeSum (8 * π) M.n)
    (A2 := fsMass M.D.ρz M.D.a M.D.ℓ M.D.K)
    (e := 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
      * M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3) * M.D.ℓ ^ 3)
    (Ec := Er)
    (Vv := Work.BoseB6.lhyValue (8 * π))
    (Em := Work.BoseB6.latticeMeshErr (8 * π) M.n)
    (mc := 4 * π * Work.UBB.lhyC * M.D.ρz ^ 2 * M.D.a * M.D.ℓ ^ 3
      * Real.sqrt (M.D.ρz * M.D.a ^ 3))
    hCc hz hmesh hCV
  -- the datum's parameters are the envelope's (`FsMatch`)
  have hRHS : -(4 * π * Work.UBB.lhyC * M.D.ρz ^ 2 * M.D.a * M.D.ℓ ^ 3
          * Real.sqrt (M.D.ρz * M.D.a ^ 3))
        + (1 / 2) * fsMass M.D.ρz M.D.a M.D.ℓ M.D.K
        + (1 / 2) * ((((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3
                * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3)))
              * (Work.BoseB6.latticeMeshErr (8 * π) M.n + Er)
            + 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
                * M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3) * M.D.ℓ ^ 3)
      = -(4 * π * Work.UBB.lhyC * ρ ^ 2 * E.aScat * E.ell ^ 3
            * Real.sqrt (ρ * E.aScat ^ 3))
        + (1 / 2) * E.ell ^ 3 * ρ ^ 2 * E.W1omega0
        + (1 / 2) * (((2 * π) ^ 3)⁻¹ * E.ell ^ 3
              * (ρ ^ 2 * E.aScat * Real.sqrt (ρ * E.aScat ^ 3))
              * (Work.BoseB6.latticeMeshErr (8 * π) M.n + Er)
            + 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
                * ρ ^ 2 * M.D.a * Real.sqrt (ρ * M.D.a ^ 3) * E.ell ^ 3) := by
    rw [Work.BoseB6Est.fsMass, ← M.hGw, M.hρ, M.ha, M.hℓ]
    ring
  rw [← Finset.mul_sum, Work.BoseBogFS.sum_zp_eq F E ρ gHat0 M]
  rw [← hRHS]
  exact hmain


theorem hZP_of_match_mis (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 η : ℝ)
    (M : FsMatch F E ρ gHat0)
    (hi1 : FsI1Regime M.D.K M.D.a M.D.R M.D.ρz M.D.μ M.D.εT M.D.c1 M.D.c2 M.D.Kl M.D.s M.D.d)
    (hn : 1 ≤ M.n) (hℓ : 0 < M.D.ℓ)
    (hmis : |(M.n : ℝ) + 1 - M.D.ℓ * Real.sqrt (M.D.ρz * M.D.a)|
      ≤ η * (M.D.ℓ * Real.sqrt (M.D.ρz * M.D.a)))
    (hη : 0 ≤ η) (hη1 : η ≤ 1 / 4)
    (hsharp : zpSum M.n M.D.ρz M.D.a M.D.K M.D.εT M.D.c1 M.D.c2
      ≤ ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3))
          * ((Work.BoseB6.meshD M.n) ^ 3 * Work.BoseB6.latticeSum (8 * π) M.n)
        + fsMass M.D.ρz M.D.a M.D.ℓ M.D.K
        + 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
            * M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3) * M.D.ℓ ^ 3
        + ((2 * π) ^ 3)⁻¹ * M.D.ℓ ^ 3 * (M.D.ρz ^ 2 * M.D.a * Real.sqrt (M.D.ρz * M.D.a ^ 3))
            * zpRiemErrSharp M.n M.D.K.B η) :
    (∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k))
      ≤ -(4 * π * Work.UBB.lhyC * ρ ^ 2 * E.aScat * E.ell ^ 3
            * Real.sqrt (ρ * E.aScat ^ 3))
        + (1 / 2) * E.ell ^ 3 * ρ ^ 2 * E.W1omega0
        + (1 / 2) * (((2 * π) ^ 3)⁻¹ * E.ell ^ 3
              * (ρ ^ 2 * E.aScat * Real.sqrt (ρ * E.aScat ^ 3))
              * (Work.BoseB6.latticeMeshErr (8 * π) M.n + zpRiemErrSharp M.n M.D.K.B η)
            + 10 ^ 10 * Work.BoseB6.lhyEps M.D.a M.D.R M.D.εT M.D.Kl M.D.s M.D.d M.D.μ
                * ρ ^ 2 * M.D.a * Real.sqrt (ρ * M.D.a ^ 3) * E.ell ^ 3) :=
  hZP_transfer F E ρ gHat0 η (zpRiemErrSharp M.n M.D.K.B η) M hi1 hn hℓ hmis hη hη1 hsharp


end Work.BoseBogFS
