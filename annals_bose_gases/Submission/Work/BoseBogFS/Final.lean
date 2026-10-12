import ChallengeDeps
import Submission.Work.BoseBogFS.Arith
import Submission.Work.BoseBogFS.qw_KzBogFS_le_window
import Submission.Work.BoseBogFS.qw_KzBogFS_le_window_direct
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.Final` — the assembled `BogOpBoundFS` statement

Chains the chapter's pieces into the `BogOpBoundFS`-shaped conclusion
(`BogOpBoundAtFS`, i.e. the design's `BogOpBoundFS` at the corrected close threshold):

* `zpKapSum` — the scalar `S = Σ_k ½(𝒵_k+κ_k)`;
* `winKbar` — the window bound `𝒦^Bog ≤ Kbar·‖f‖²` supplied by `qw_KzBogFS_le_window`;
* `reserveLoss` — the reserve's scalar cost `½Kbar + ½S + 3G`;
* `hRes_of_window` — the `hRes` obligation of `bogOpBound_at` from
  `qw_dNumOpR_le_res` + `qw_KzBogFS_le_window`;
* `bogOpBoundFS_of_estimates` — the whole statement, with the two B6Est estimates, the
  numeric rows, the window data and the arithmetic slots as explicit hypotheses.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- `S = Σ_k ½(𝒵_k+κ_k)`, the scalar of `qw_KzBogFS_ge`. -/
def zpKapSum (E : Q3Env Mode) (ρ : ℝ) : ℝ :=
  ∑ k : Mode, (1 / 2 : ℝ) * (Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k)
    + Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k))

/-- The window bound `Kbar` of `qw_KzBogFS_le_window`. -/
def winKbar (E : Q3Env Mode) (Dsup : ℝ) : ℝ :=
  Dsup * (600 * E.bigM + 32 * (Fintype.card Mode : ℝ) + 32) + (Fintype.card Mode : ℝ) + 1

/-- The reserve's scalar cost in the `hRes` shape of `bogOpBound_at`:
`Res = σ·Kbar + σ·S + (1+σ⁻¹)G` with `S = zpKapSum`, `Kbar = winKbar`.  The free `σ > 0` is
the Cauchy–Schwarz parameter of `normSq_bOp_le`; it has to be chosen small compared with
`X²` but large compared with `G`, which is what makes the slot `hResB` absorbable
(`README.md` §4, F8). -/
def reserveLoss (E : Q3Env Mode) (ρ Dsup G σ : ℝ) : ℝ :=
  σ * winKbar E Dsup + σ * zpKapSum E ρ + (1 + σ⁻¹) * G

/-- **The `hRes` obligation of `bogOpBound_at`** from the window data: the corpus's
unshifted `dNumOpR` on `RHi` is controlled by `𝒦^Bog` up to `zpKapSum + reserveLoss`. -/
theorem hRes_of_window (F : FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Q3Env Mode)
    (ρ Cn Dsup G σ : ℝ) (hσ : 0 < σ) (hnum : BogNumeric F E ρ) (hbigM : 0 ≤ E.bigM)
    (hDsup : ∀ k : Mode, bogD E ρ k ≤ Dsup) (hCn : Cn ≤ 16)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    (hγ : ∀ k : Mode, (bogGamma E ρ k) ^ 2 ≤ 1)
    (hα : ∀ k : Mode, (bogAlpha E ρ k) ^ 2 ≤ 1)
    (hG : (∑ k ∈ (Work.BoseB7.excited Mode).filter (RHi F (KzEnvAt E ρ)),
        (bogD E ρ k) * (bogGamma E ρ k) ^ 2) ≤ G) :
    ∀ f : F.H, T.NWindow E.bigM f →
      F.qw f (F.dNumOpR (KzEnvAt E ρ) (RHi F (KzEnvAt E ρ)))
        ≤ F.qw f (KzBogFS F E ρ) + (zpKapSum E ρ + reserveLoss E ρ Dsup G σ) * F.normSq f := by
  intro f hf
  have hKbar : ∀ g : F.H, T.NWindow E.bigM g →
      F.qw g (KzBogFS F E ρ) ≤ winKbar E Dsup * F.normSq g :=
    fun g hg => qw_KzBogFS_le_window F T E ρ Cn Dsup hnum hbigM hDsup hCn hBessel hγ hα g hg
  have h := qw_dNumOpR_le_res F T E ρ (winKbar E Dsup) G σ hσ hnum hKbar hG f hf
  simpa only [reserveLoss, zpKapSum, winKbar] using h

/-- **`BogOpBoundAtFS` from the estimates.**  The whole of node `BOG`: the design's
`BogOpBoundFS` at the corrected close threshold, from

* `hnum`, `hbigM`, `hBessel`, `hDsup`, the coefficient rows `hAwin`/`hCwin` with the
  constant row `hKbig`, and `hG` — the gate/window data (`BogNumeric` supplies the
  diagonalisation rows; `hAwin`/`hCwin` are the datum's kernel bounds and `hKbig` the
  (always satisfiable) large-`Dsup` row that lets the *direct* window bound
  `qw_KzBogFS_le_window_direct` meet `winKbar`; the Bessel conjunct `n₊^χ ≤ Cn·n₊` with
  `Cn ≤ 16` is `RViewFS`'s; `hG` bounds `Σ_{RHi}𝒟_kγ_k²` and is `O((κℓ)^{-∞})`);
* `hZP`, `hKAP` — `Work.BoseB6Est.fsZeroPoint_le` and `Work.BoseB6Est.kappaSum_le` in the
  chapter's shapes (see `README.md` §5.2–5.3 for the lattice transfer that is still open);
* `hEzero`, `hResB`, `hδ` — the §11 arithmetic slots;
* `hg0`, `hmu`, `hell` — the view's identifications for `ĝ(0)`, `μ`, `ℓ`.

> **⚠ SUPERSEDED.**  This is the *old-shape* assembly: its slots are quantified over every
> `μ` with no `Adm`/view, which `FINDING_slot_shapes.md` shows is uninhabitable
> (`E.eT = (paramsAt μ (a v)).eT < 1` already fails without `Adm`).  Use the honest-data
> capstone `Work.BoseBogFS.bogOpBoundAtFS_of_sharpMatchL` (module
> `Submission.Work.BoseBogFS.SharpL`), whose slots are `Adm`/`viewFS`-indexed; this lemma is
> kept as the shape of the assembly.

The conclusion is `BogOpBoundAtFS`, which is `BogOpBoundFS` once `closeThreshold` is
`μK_ℓ⁻²/(2¹⁴π)` (`BogOpBoundAtFS.toBogOpBoundFS`). -/
theorem bogOpBoundFS_of_estimates (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum)
    (Ezero δ : ℝ → ℝ) (Dsup G σv : ℝ → ℝ → ℝ) (Cn C₄ C₅ C₀ : ℝ)
    (hav : 0 < a v) (hσv : ∀ (μ ρ : ℝ), 0 < σv μ ρ)
    (hC₄ : 0 ≤ C₄) (hC₅ : 0 ≤ C₅) (hC₀ : 0 ≤ C₀) (hCn : Cn ≤ 16)
    (hnum : ∀ (μ : ℝ) (ρ : ℝ), CloseCondFS v μ ρ → BogNumeric (D μ).F (D μ).E ρ)
    (hbigM : ∀ (μ : ℝ) (ρ : ℝ), 0 ≤ (D μ).E.bigM)
    (hBessel : ∀ (μ : ℝ) (ρ : ℝ), ∀ f : (D μ).F.H,
      (D μ).F.bp ((∑ k : (D μ).Mode, (D μ).F.nOp k) f) f
        ≤ Cn * (D μ).F.bp ((D μ).T.N f) f)
    (A C : ℝ → ℝ → ℝ)
    (hAwin : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ →
      ∀ k : (D μ).Mode, bogA (D μ).E ρ k ≤ A μ ρ)
    (hCwin : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ →
      ∀ k : (D μ).Mode, |bogC (D μ).E ρ k| ≤ C μ ρ)
    (hKbig : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ →
      10 ^ 6 * (A μ ρ + C μ ρ + 1) * ((D μ).E.bigM + 1)
        * ((Fintype.card (D μ).Mode : ℝ) + 1) ≤ winKbar (D μ).E (Dsup μ ρ))
    (hDsup : ∀ (μ : ℝ) (ρ : ℝ) (k : (D μ).Mode), bogD (D μ).E ρ k ≤ Dsup μ ρ)
    (hG : ∀ (μ : ℝ) (ρ : ℝ), (∑ k ∈ (Work.BoseB7.excited (D μ).Mode).filter
        (RHi (D μ).F (KzEnvAt (D μ).E ρ)),
        (bogD (D μ).E ρ k) * (bogGamma (D μ).E ρ k) ^ 2) ≤ G μ ρ)
    (hZP : ∀ (μ : ℝ) (ρ : ℝ), CloseCondFS v μ ρ → (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
        (bogA (D μ).E ρ k) (bogB (D μ).E ρ k))
      ≤ -(4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3))
        + (1 / 2) * ell3 v μ * ρ ^ 2 * (D μ).E.W1omega0 + Ezero μ)
    (hKAP : ∀ (μ : ℝ) (ρ : ℝ), CloseCondFS v μ ρ → (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr
        (bogA (D μ).E ρ k) (bogB (D μ).E ρ k) (bogC (D μ).E ρ k))
      ≤ (ρ - μ) ^ 2 * ((D μ).gHat0 / 2) * ell3 v μ * (1 + δ μ))
    (hEzero : ∀ (μ : ℝ) (ρ : ℝ), CloseCondFS v μ ρ → Ezero μ ≤ C₄ * errBracket v R μ)
    (hResB : ∀ (μ : ℝ) (ρ : ℝ), CloseCondFS v μ ρ →
      reserveLoss (D μ).E ρ (Dsup μ ρ) (G μ ρ) (σv μ ρ) ≤ C₅ * errBracket v R μ)
    (hδ : ∀ (μ : ℝ) (ρ : ℝ), CloseCondFS v μ ρ → δ μ ≤ C₀ * dil v μ * (R / a v) ^ 2)
    (hδ0 : ∀ (μ : ℝ), 0 ≤ δ μ)
    (hg0 : ∀ (μ : ℝ), (D μ).gHat0 = 8 * π * a v)
    (hmu : ∀ (μ : ℝ), (D μ).E.mu = μ) (hell : ∀ (μ : ℝ), (D μ).E.ell = ell v μ) :
    BogOpBoundAtFS v h R D := by
  refine ⟨1, C₄ + C₅ + C₀ / ((2 : ℝ) ^ 26 * π) + 1, one_pos, by positivity, ?_⟩
  intro μ hadm hview ρ hρ hclose f hf
  have hμ : 0 < μ := hadm.1
  have hdil1 : Work.BoseFixR.dil v μ ≤ 1 := by
    have := hadm.2.1
    simpa only [Work.BoseFixR.dil] using this
  have hArith := hArith_of_pieces v R μ ρ (δ μ) (Ezero μ)
    (reserveLoss (D μ).E ρ (Dsup μ ρ) (G μ ρ) (σv μ ρ)) C₄ C₅ C₀ (D μ).gHat0
    hav hμ hdil1 (hg0 μ) hclose (hδ μ ρ hclose) hC₀ (hEzero μ ρ hclose) (hResB μ ρ hclose)
    hC₄ hC₅
  have hmain := bogOpBound_at v h R (D μ) μ ρ (hnum μ ρ hclose) (hmu μ) (hell μ) (Ezero μ)
    (reserveLoss (D μ).E ρ (Dsup μ ρ) (G μ ρ) (σv μ ρ)) (δ μ)
    (C₄ + C₅ + C₀ / ((2 : ℝ) ^ 26 * π) + 1) (hδ0 μ) (hZP μ ρ hclose) (hKAP μ ρ hclose)
    (by
      have hKbar : ∀ g : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM g →
          (D μ).F.qw g (KzBogFS (D μ).F (D μ).E ρ)
            ≤ winKbar (D μ).E (Dsup μ ρ) * (D μ).F.normSq g :=
        fun g hg => qw_KzBogFS_le_window_direct (D μ).F (D μ).T (D μ).E ρ Cn (A μ ρ) (C μ ρ)
          (winKbar (D μ).E (Dsup μ ρ)) (hnum μ ρ hclose) (hbigM μ ρ)
          (hBessel μ ρ) hCn (hAwin μ ρ hclose) (hCwin μ ρ hclose)
          (hKbig μ ρ hclose) g hg
      simpa only [reserveLoss, zpKapSum] using
        qw_dNumOpR_le_res (D μ).F (D μ).T (D μ).E ρ (winKbar (D μ).E (Dsup μ ρ)) (G μ ρ) (σv μ ρ)
          (hσv μ ρ) (hnum μ ρ hclose) hKbar (hG μ ρ))
    hArith f hf
  simpa only [errBracket, mul_assoc, hell, ell3] using hmain

end Work.BoseBogFS
