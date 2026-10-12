import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.NumericRows
import Submission.Work.BoseBogFS.WindowArith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.SharpCap` — the capstone with the *sharp* zero-point error
# and the *habitable* slot shapes

`FsFinal.bogOpBoundFS_of_fsData` carries three defects that make it uninhabitable, and this
module removes all three:

1. it is indexed by the datum's own density (`M : ∀ μ, FsMatch … ((D μ).E.rho) …`), so it
   cannot serve the `∀ ρ` quantifier of `BogOpBoundFS`; here the mode identification is
   indexed by the **statement's** density,
   `M : ∀ μ ρ, CloseCondFS v μ ρ → FsMatch (D μ).F (D μ).E ρ ((D μ).gHat0)` — the
   `ρ`-indexed family of `FINDING_mesh_integrality.md`, which is satisfiable because the
   **relative, two-sided** mismatch `hmis` with `η ≤ 1/4` lets the mesh `(n:ℝ)+1` approximate
   `ℓ√(ρ_za)` instead of equalling it (the close region moves `ℓ√(ρa)` only by the relative
   amount `K_ℓ⁻²/(2¹⁵) ≪ 1/4`, so one mesh serves the whole region);
2. its zero-point and error slots are the *crude* `zpError`, which `FINDING_zpRiemErr.md`
   shows no honest datum can satisfy; here they are `zpErrorOf … Er` with the budget `Er` an
   explicit parameter, and `hZP`/`hKAP` are read off the sharpened comparison through
   `hZP_slot_transfer`/`hKAP_slot_i1`.  The absorbable instance is
   `zpRiemErrSharpEta` (`FINDING_mismatch_weighting.md`);
3. its slots are quantified over **all** `μ`, while every fact about the environment's
   kernels is available only *under the view* (`E.eT = (paramsAt μ (a v)).eT < 1` already
   fails without `Adm`, so `BogNumeric (D μ).F (D μ).E ρ` is false for `μa³ ≥ 1`).  Here the
   whole assembly is stated at a **fixed `ε₀`** — `BogOpBoundAtFSWith v h R D ε₀`, the body
   of `BogOpBoundAtFS` for that `ε₀` — and every view-dependent slot carries
   `(hadm : Adm v ε₀ μ) (hview : (D μ).viewFS v h μ)`.  This is strictly easier to
   instantiate than the old shape, and `BogOpBoundAtFS_of_with` recovers the existential
   `∃ ε₀` form.

Also: the slot `hδ0` of the old capstone is *dropped* — it is the field `FsBogData.hδ`.

What is left in the interface is exactly what the honest datum (node `D-FS`) must supply:
the `FsMatch` family with its `I₁` regime, the comparison, the gate rows, the `δ` slot, the
window rows and the §11 identifications.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7 Work.BoseB6Est

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- `ℓ = K_ℓ(μa)^{-1/2} > 0` at `μ > 0`, `a v > 0`. -/
theorem ell_pos_bog (v : ℝ³ → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    0 < ell v μ := by
  have hKl : 0 < (paramsAt μ (a v)).Kl := by
    show 0 < Work.BoseBox.fsXp (μ * (a v) ^ 3) (-(3 / 2))
    rw [Work.BoseBox.fsXp]
    exact Real.rpow_pos_of_pos (by positivity) _
  rw [ell, sideAt, Work.BoseBox.boxSide]
  exact mul_pos hKl (Real.rpow_pos_of_pos (by positivity) _)

/-- **The §11 bracket is strictly positive** on the admissible region. -/
theorem errBracket_pos (v : ℝ³ → ℝ) {R μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    0 < errBracket v R μ := by
  have hdil : 0 < dil v μ := mul_pos hμ (pow_pos hav 3)
  have hX : 0 < Work.BoseFixR.fsX v μ := by
    rw [Work.BoseFixR.fsX, Work.BoseBox.fsXp]
    exact Real.rpow_pos_of_pos hdil _
  have hE : 0 < errExp v μ := by
    rw [errExp]
    exact Real.rpow_pos_of_pos hdil _
  have he : 0 < ell3 v μ := by
    rw [ell3]
    exact pow_pos (ell_pos_bog v hμ hav) 3
  have hb : 0 < Work.BoseFixR.fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ)
      + errExp v μ := by
    have h2 : 0 ≤ (R / a v) ^ 2 * Real.sqrt (dil v μ) := by positivity
    nlinarith [sq_pos_of_pos hX]
  rw [errBracket]
  exact mul_pos (mul_pos (mul_pos (mul_pos (pow_pos hμ 2) hav) he) (Real.sqrt_pos.mpr hdil)) hb

/-- **`BogOpBoundAtFS` at a fixed `ε₀`** — the body of `BogOpBoundAtFS`
(`Main.lean`) with the existential `ε₀` peeled off, so that an assembly can carry slots
indexed by the admissibility evidence `Adm v ε₀ μ` and the view. -/
abbrev BogOpBoundAtFSWith (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum)
    (ε₀ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ →
      ∀ ρ : ℝ, 0 ≤ ρ → CloseCondFS v μ ρ →
        ∀ f : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM f →
          (4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3)
              - C * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
                  * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ))
              * (D μ).F.normSq f
            + (D μ).F.qw f ((D μ).F.dNumOpR (KzEnvAt (D μ).E ρ)
                (RHi (D μ).F (KzEnvAt (D μ).E ρ)))
          ≤ (D μ).F.qw f (KzBogFS (D μ).F (D μ).E ρ)
            + ((1 / 2) * ρ ^ 2 * (D μ).E.ell ^ 3 * (D μ).E.W1omega0
                + (1 / 2) * (ρ - μ) ^ 2 * (D μ).E.ell ^ 3 * (D μ).gHat0)
              * (D μ).F.normSq f

/-- The existential-`ε₀` form from the fixed-`ε₀` form. -/
theorem BogOpBoundAtFS_of_with {v : ℝ³ → ℝ} {h : ScatSol v} {R : ℝ} {D : ℝ → KzDatum}
    {ε₀ : ℝ} (hε : 0 < ε₀) (hB : BogOpBoundAtFSWith v h R D ε₀) : BogOpBoundAtFS v h R D := by
  obtain ⟨C, hC, hf⟩ := hB
  exact ⟨ε₀, C, hε, hC, hf⟩

/-- **The assembly at a fixed `ε₀`, with an explicit zero-point budget `Er`.**

Slots: the gate rows (`hnum`, `hbigM`, `hBessel`, `hγ`, `hα`, `hDsup`, `hG`), the `hZP`/
`hKAP`/`hEzero` rows at the budget `Er`, the two linear reserve-window rows, the `δ` slot
and the §11 identifications.  Every view-dependent slot carries `Adm v ε₀ μ` and the view. -/
theorem bogOpBoundAtFSWith_of_sharpData (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ)
    (D : ℝ → KzDatum) (ε₀ : ℝ) (hε₀1 : ε₀ ≤ 1)
    (M : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → FsMatch (D μ).F (D μ).E ρ ((D μ).gHat0))
    (Er : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → ℝ)
    (Dsup G : ℝ → ℝ → ℝ) (Cn C₄ C₅ C₀ : ℝ) (hav : 0 < a v)
    (hC₄ : 0 ≤ C₄) (hC₅ : 0 < C₅) (hC₀ : 0 ≤ C₀) (hCn : Cn ≤ 16)
    (hnum : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      BogNumeric (D μ).F (D μ).E ρ)
    (hbigM : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → 0 ≤ (D μ).E.bigM)
    (hBessel : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ f : (D μ).F.H,
      (D μ).F.bp ((∑ k : (D μ).Mode, (D μ).F.nOp k) f) f ≤ Cn * (D μ).F.bp ((D μ).T.N f) f)
    (A C : ℝ → ℝ → ℝ)
    (hAwin : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      ∀ k : (D μ).Mode, bogA (D μ).E ρ k ≤ A μ ρ)
    (hCwin : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      ∀ k : (D μ).Mode, |bogC (D μ).E ρ k| ≤ C μ ρ)
    (hKbig : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      10 ^ 6 * (A μ ρ + C μ ρ + 1) * ((D μ).E.bigM + 1)
        * ((Fintype.card (D μ).Mode : ℝ) + 1) ≤ winKbar (D μ).E (Dsup μ ρ))
    (hDsup : ∀ (μ ρ : ℝ) (k : (D μ).Mode), bogD (D μ).E ρ k ≤ Dsup μ ρ)
    (hG : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → (∑ k ∈ (Work.BoseB7.excited (D μ).Mode).filter
        (RHi (D μ).F (KzEnvAt (D μ).E ρ)),
        (bogD (D μ).E ρ k) * (bogGamma (D μ).E ρ k) ^ 2) ≤ G μ ρ)
    (hZP : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA (D μ).E ρ k)
          (bogB (D μ).E ρ k))
        ≤ -(4 * π * Work.UBB.lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3))
          + (1 / 2) * ell3 v μ * ρ ^ 2 * (D μ).E.W1omega0
          + zpErrorOf (ell v μ) (a v) (M μ ρ ‹_›).D.R (M μ ρ ‹_›).D.εT (M μ ρ ‹_›).D.Kl
              (M μ ρ ‹_›).D.s (M μ ρ ‹_›).D.d (M μ ρ ‹_›).D.μ ρ (M μ ρ ‹_›).n
              (Er μ ρ ‹_›))
    (hKAP : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr (bogA (D μ).E ρ k)
          (bogB (D μ).E ρ k) (bogC (D μ).E ρ k))
        ≤ (ρ - μ) ^ 2 * ((D μ).gHat0 / 2) * ell3 v μ * (1 + (M μ ρ ‹_›).D.δ))
    (hEzero : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      zpErrorOf (ell v μ) (a v) (M μ ρ ‹_›).D.R (M μ ρ ‹_›).D.εT (M μ ρ ‹_›).D.Kl
        (M μ ρ ‹_›).D.s (M μ ρ ‹_›).D.d (M μ ρ ‹_›).D.μ ρ (M μ ρ ‹_›).n (Er μ ρ ‹_›)
      ≤ C₄ * errBracket v R μ)
    (hG0 : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      0 ≤ G μ ρ)
    (hSpos : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      0 < winKbar (D μ).E (Dsup μ ρ) + zpKapSum (D μ).E ρ)
    (hwinG : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      G μ ρ ≤ (C₅ * errBracket v R μ) / 2)
    (hwinGS : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      G μ ρ * (winKbar (D μ).E (Dsup μ ρ) + zpKapSum (D μ).E ρ)
        ≤ (C₅ * errBracket v R μ) ^ 2 / 16)
    (hδ : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      (M μ ρ ‹_›).D.δ ≤ C₀ * dil v μ * (R / a v) ^ 2)
    (hg0 : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).gHat0 = 8 * π * a v)
    (hmu : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.mu = μ)
    (hell : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.ell = ell v μ) :
    BogOpBoundAtFSWith v h R D ε₀ := by
  refine ⟨C₄ + C₅ + C₀ / ((2 : ℝ) ^ 26 * π) + 1, by positivity, ?_⟩
  intro μ hadm hview ρ hρ hclose f hf
  have hμ : 0 < μ := hadm.1
  have hdil1 : Work.BoseFixR.dil v μ ≤ 1 :=
    le_trans (by simpa only [Work.BoseFixR.dil] using hadm.2.1) hε₀1
  have hcs : CloseCondFS v μ ρ := hclose
  -- the optimal Cauchy–Schwarz parameter, from the two linear window conditions
  obtain ⟨σ, hσ, hσle⟩ := exists_sigma_reserveLoss_le (D μ).E ρ (Dsup μ ρ) (G μ ρ)
    (C₅ * errBracket v R μ) (hG0 μ hadm hview ρ hcs) (hSpos μ hadm hview ρ hcs)
    (mul_pos hC₅ (errBracket_pos v hμ hav))
    (hwinG μ hadm hview ρ hcs) (hwinGS μ hadm hview ρ hcs)
  have hArith := hArith_of_pieces v R μ ρ (M μ ρ hcs).D.δ
    (zpErrorOf (ell v μ) (a v) (M μ ρ hcs).D.R (M μ ρ hcs).D.εT (M μ ρ hcs).D.Kl
      (M μ ρ hcs).D.s (M μ ρ hcs).D.d (M μ ρ hcs).D.μ ρ (M μ ρ hcs).n (Er μ ρ hcs))
    (reserveLoss (D μ).E ρ (Dsup μ ρ) (G μ ρ) σ) C₄ C₅ C₀ (D μ).gHat0
    hav hμ hdil1 (hg0 μ hadm hview) hcs (hδ μ hadm hview ρ hcs) hC₀
    (hEzero μ hadm hview ρ hcs) hσle hC₄ hC₅.le
  have hmain := bogOpBound_at v h R (D μ) μ ρ (hnum μ hadm hview ρ hcs) (hmu μ hadm hview)
    (hell μ hadm hview)
    (zpErrorOf (ell v μ) (a v) (M μ ρ hcs).D.R (M μ ρ hcs).D.εT (M μ ρ hcs).D.Kl
      (M μ ρ hcs).D.s (M μ ρ hcs).D.d (M μ ρ hcs).D.μ ρ (M μ ρ hcs).n (Er μ ρ hcs))
    (reserveLoss (D μ).E ρ (Dsup μ ρ) (G μ ρ) σ) (M μ ρ hcs).D.δ
    (C₄ + C₅ + C₀ / ((2 : ℝ) ^ 26 * π) + 1) (M μ ρ hcs).D.hδ
    (hZP μ hadm hview ρ hcs) (hKAP μ hadm hview ρ hcs)
    (by
      have hKbar : ∀ g : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM g →
          (D μ).F.qw g (KzBogFS (D μ).F (D μ).E ρ)
            ≤ winKbar (D μ).E (Dsup μ ρ) * (D μ).F.normSq g :=
        fun g hg => qw_KzBogFS_le_window_direct (D μ).F (D μ).T (D μ).E ρ Cn (A μ ρ) (C μ ρ)
          (winKbar (D μ).E (Dsup μ ρ)) (hnum μ hadm hview ρ hcs) (hbigM μ hadm hview)
          (hBessel μ hadm hview) hCn (hAwin μ hadm hview ρ hcs) (hCwin μ hadm hview ρ hcs)
          (hKbig μ hadm hview ρ hcs) g hg
      simpa only [reserveLoss, zpKapSum] using
        qw_dNumOpR_le_res (D μ).F (D μ).T (D μ).E ρ (winKbar (D μ).E (Dsup μ ρ)) (G μ ρ) σ hσ
          (hnum μ hadm hview ρ hcs) hKbar (hG μ ρ hcs))
    hArith f hf
  simpa only [errBracket, mul_assoc, hell μ hadm hview, ell3] using hmain

/-- **The capstone from the honest data, at a fixed `ε₀` and explicit budget `Er`.**
The `hZP`/`hKAP` slots are *discharged* here from the `ρ`-indexed identification `M`, the
`I₁` regime, the relative mesh mismatch `hmis` and the lattice comparison `hsharp`, through
the proved `hZP_slot_transfer` and `hKAP_slot_i1`. -/
theorem bogOpBoundAtFSWith_of_sharpMatch (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ)
    (D : ℝ → KzDatum) (ε₀ : ℝ) (hε₀1 : ε₀ ≤ 1)
    (M : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → FsMatch (D μ).F (D μ).E ρ ((D μ).gHat0))
    (Er : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → ℝ)
    (η : ℝ → ℝ → ℝ)
    (hi1 : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      FsI1Regime (M μ ρ hc).D.K (M μ ρ hc).D.a (M μ ρ hc).D.R (M μ ρ hc).D.ρz
        (M μ ρ hc).D.μ (M μ ρ hc).D.εT (M μ ρ hc).D.c1 (M μ ρ hc).D.c2 (M μ ρ hc).D.Kl
        (M μ ρ hc).D.s (M μ ρ hc).D.d)
    (hn : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ), 1 ≤ (M μ ρ hc).n)
    (hℓ : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ), 0 < (M μ ρ hc).D.ℓ)
    (hmis : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      |((M μ ρ hc).n : ℝ) + 1 - (M μ ρ hc).D.ℓ * Real.sqrt ((M μ ρ hc).D.ρz * (M μ ρ hc).D.a)|
        ≤ η μ ρ * ((M μ ρ hc).D.ℓ * Real.sqrt ((M μ ρ hc).D.ρz * (M μ ρ hc).D.a)))
    (hη : ∀ (μ ρ : ℝ), 0 ≤ η μ ρ) (hη1 : ∀ (μ ρ : ℝ), η μ ρ ≤ 1 / 4)
    (hsharp : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      SharpCmpWith (D μ).F (D μ).E ρ ((D μ).gHat0) (M μ ρ hc) (Er μ ρ hc))
    (Dsup G : ℝ → ℝ → ℝ) (Cn C₄ C₅ C₀ : ℝ) (hav : 0 < a v)
    (hC₄ : 0 ≤ C₄) (hC₅ : 0 < C₅) (hC₀ : 0 ≤ C₀) (hCn : Cn ≤ 16)
    (hnum : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      BogNumeric (D μ).F (D μ).E ρ)
    (hbigM : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → 0 ≤ (D μ).E.bigM)
    (hBessel : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ f : (D μ).F.H,
      (D μ).F.bp ((∑ k : (D μ).Mode, (D μ).F.nOp k) f) f ≤ Cn * (D μ).F.bp ((D μ).T.N f) f)
    (A C : ℝ → ℝ → ℝ)
    (hAwin : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      ∀ k : (D μ).Mode, bogA (D μ).E ρ k ≤ A μ ρ)
    (hCwin : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      ∀ k : (D μ).Mode, |bogC (D μ).E ρ k| ≤ C μ ρ)
    (hKbig : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      10 ^ 6 * (A μ ρ + C μ ρ + 1) * ((D μ).E.bigM + 1)
        * ((Fintype.card (D μ).Mode : ℝ) + 1) ≤ winKbar (D μ).E (Dsup μ ρ))
    (hDsup : ∀ (μ ρ : ℝ) (k : (D μ).Mode), bogD (D μ).E ρ k ≤ Dsup μ ρ)
    (hG : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → (∑ k ∈ (Work.BoseB7.excited (D μ).Mode).filter
        (RHi (D μ).F (KzEnvAt (D μ).E ρ)),
        (bogD (D μ).E ρ k) * (bogGamma (D μ).E ρ k) ^ 2) ≤ G μ ρ)
    (hEzero : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      zpErrorOf (ell v μ) (a v) (M μ ρ ‹_›).D.R (M μ ρ ‹_›).D.εT (M μ ρ ‹_›).D.Kl
        (M μ ρ ‹_›).D.s (M μ ρ ‹_›).D.d (M μ ρ ‹_›).D.μ ρ (M μ ρ ‹_›).n (Er μ ρ ‹_›)
      ≤ C₄ * errBracket v R μ)
    (hG0 : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      0 ≤ G μ ρ)
    (hSpos : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      0 < winKbar (D μ).E (Dsup μ ρ) + zpKapSum (D μ).E ρ)
    (hwinG : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      G μ ρ ≤ (C₅ * errBracket v R μ) / 2)
    (hwinGS : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      G μ ρ * (winKbar (D μ).E (Dsup μ ρ) + zpKapSum (D μ).E ρ)
        ≤ (C₅ * errBracket v R μ) ^ 2 / 16)
    (hδ : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      (M μ ρ ‹_›).D.δ ≤ C₀ * dil v μ * (R / a v) ^ 2)
    (hg0 : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).gHat0 = 8 * π * a v)
    (hmu : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.mu = μ)
    (hell : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.ell = ell v μ)
    (hascat : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.aScat = a v) :
    BogOpBoundAtFSWith v h R D ε₀ :=
  bogOpBoundAtFSWith_of_sharpData v h R D ε₀ hε₀1 M Er Dsup G Cn C₄ C₅ C₀ hav hC₄ hC₅
    hC₀ hCn hnum hbigM hBessel A C hAwin hCwin hKbig hDsup hG
    (fun μ hadm hview ρ hcs =>
      hZP_slot_transfer v h μ (D μ).F (D μ).E ρ ((D μ).gHat0) (η μ ρ) (Er μ ρ hcs)
        (M μ ρ hcs) (hi1 μ ρ hcs) (hn μ ρ hcs) (hℓ μ ρ hcs) (hmis μ ρ hcs) (hη μ ρ)
        (hη1 μ ρ) (hsharp μ ρ hcs) (hascat μ hadm hview) (hell μ hadm hview)
        ((M μ ρ hcs).ha.trans (hascat μ hadm hview)))
    (fun μ hadm hview ρ hcs => by
      have hk := hKAP_slot_i1 (D μ).F (D μ).E ρ ((D μ).gHat0) (M μ ρ hcs)
        (hi1 μ ρ hcs) (hℓ μ ρ hcs)
      rw [hmu μ hadm hview, hell μ hadm hview] at hk
      exact hk)
    hEzero hG0 hSpos hwinG hwinGS hδ hg0 hmu hell

/-- **The capstone from the honest data, at the corrected (absorbable) budget
`zpRiemErrSharpEta`.**  This is `bogOpBoundAtFSWith_of_sharpMatch` with
`Er μ ρ hc := zpRiemErrSharpEta (M μ ρ hc).n (M μ ρ hc).D.K.B (η μ ρ)` and
`hsharp : SharpCmpEta …` — *exactly* the statement delegated in
`FINDING_mismatch_weighting.md` and produced by `fsZeroPoint_le_sharpEta`. -/
theorem bogOpBoundAtFSWith_of_sharpMatchEta (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ)
    (D : ℝ → KzDatum) (ε₀ : ℝ) (hε₀1 : ε₀ ≤ 1)
    (M : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → FsMatch (D μ).F (D μ).E ρ ((D μ).gHat0))
    (η : ℝ → ℝ → ℝ)
    (hi1 : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      FsI1Regime (M μ ρ hc).D.K (M μ ρ hc).D.a (M μ ρ hc).D.R (M μ ρ hc).D.ρz
        (M μ ρ hc).D.μ (M μ ρ hc).D.εT (M μ ρ hc).D.c1 (M μ ρ hc).D.c2 (M μ ρ hc).D.Kl
        (M μ ρ hc).D.s (M μ ρ hc).D.d)
    (hn : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ), 1 ≤ (M μ ρ hc).n)
    (hℓ : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ), 0 < (M μ ρ hc).D.ℓ)
    (hmis : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      |((M μ ρ hc).n : ℝ) + 1 - (M μ ρ hc).D.ℓ * Real.sqrt ((M μ ρ hc).D.ρz * (M μ ρ hc).D.a)|
        ≤ η μ ρ * ((M μ ρ hc).D.ℓ * Real.sqrt ((M μ ρ hc).D.ρz * (M μ ρ hc).D.a)))
    (hη : ∀ (μ ρ : ℝ), 0 ≤ η μ ρ) (hη1 : ∀ (μ ρ : ℝ), η μ ρ ≤ 1 / 4)
    (hsharp : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      SharpCmpEta (D μ).F (D μ).E ρ ((D μ).gHat0) (M μ ρ hc) (η μ ρ))
    (Dsup G : ℝ → ℝ → ℝ) (Cn C₄ C₅ C₀ : ℝ) (hav : 0 < a v)
    (hC₄ : 0 ≤ C₄) (hC₅ : 0 < C₅) (hC₀ : 0 ≤ C₀) (hCn : Cn ≤ 16)
    (hnum : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      BogNumeric (D μ).F (D μ).E ρ)
    (hbigM : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → 0 ≤ (D μ).E.bigM)
    (hBessel : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ f : (D μ).F.H,
      (D μ).F.bp ((∑ k : (D μ).Mode, (D μ).F.nOp k) f) f ≤ Cn * (D μ).F.bp ((D μ).T.N f) f)
    (A C : ℝ → ℝ → ℝ)
    (hAwin : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      ∀ k : (D μ).Mode, bogA (D μ).E ρ k ≤ A μ ρ)
    (hCwin : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      ∀ k : (D μ).Mode, |bogC (D μ).E ρ k| ≤ C μ ρ)
    (hKbig : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      10 ^ 6 * (A μ ρ + C μ ρ + 1) * ((D μ).E.bigM + 1)
        * ((Fintype.card (D μ).Mode : ℝ) + 1) ≤ winKbar (D μ).E (Dsup μ ρ))
    (hDsup : ∀ (μ ρ : ℝ) (k : (D μ).Mode), bogD (D μ).E ρ k ≤ Dsup μ ρ)
    (hG : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → (∑ k ∈ (Work.BoseB7.excited (D μ).Mode).filter
        (RHi (D μ).F (KzEnvAt (D μ).E ρ)),
        (bogD (D μ).E ρ k) * (bogGamma (D μ).E ρ k) ^ 2) ≤ G μ ρ)
    (hEzero : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      zpErrorSharpEta (ell v μ) (a v) (M μ ρ ‹_›).D.R (M μ ρ ‹_›).D.εT (M μ ρ ‹_›).D.Kl
        (M μ ρ ‹_›).D.s (M μ ρ ‹_›).D.d (M μ ρ ‹_›).D.μ ρ (M μ ρ ‹_›).n (M μ ρ ‹_›).D.K
        (η μ ρ) ≤ C₄ * errBracket v R μ)
    (hwinG : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      G μ ρ ≤ (C₅ * errBracket v R μ) / 2)
    (hwinGS : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      G μ ρ * (winKbar (D μ).E (Dsup μ ρ) + zpKapSum (D μ).E ρ)
        ≤ (C₅ * errBracket v R μ) ^ 2 / 16)
    (hδ : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      (M μ ρ ‹_›).D.δ ≤ C₀ * dil v μ * (R / a v) ^ 2)
    (hg0 : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).gHat0 = 8 * π * a v)
    (hmu : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.mu = μ)
    (hell : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.ell = ell v μ)
    (hascat : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.aScat = a v) :
    BogOpBoundAtFSWith v h R D ε₀ :=
  bogOpBoundAtFSWith_of_sharpMatch v h R D ε₀ hε₀1 M
    (fun μ ρ _ => zpRiemErrSharpEta (M μ ρ ‹_›).n (M μ ρ ‹_›).D.K.B (η μ ρ)) η
    hi1 hn hℓ hmis hη hη1 hsharp Dsup G Cn C₄ C₅ C₀ hav hC₄ hC₅ hC₀ hCn hnum hbigM hBessel
    A C hAwin hCwin hKbig
    hDsup hG hEzero
    (fun μ hadm hview ρ hc => le_trans (sum_RHi_bogD_mul_gammaSq_nonneg (hnum μ hadm hview ρ hc))
      (hG μ ρ hc))
    (fun μ hadm hview ρ hc => winKbar_add_zpKapSum_pos (hnum μ hadm hview ρ hc) (hDsup μ ρ)
      (hbigM μ hadm hview)) hwinG hwinGS hδ hg0 hmu hell hascat

/-- **The corrected capstone in the shape the lead consumes**: `BogOpBoundAtFS`, from the
honest-data layer at the budget `zpRiemErrSharpEta`. -/
theorem bogOpBoundAtFS_of_sharpMatchEta (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ)
    (D : ℝ → KzDatum) (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (M : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → FsMatch (D μ).F (D μ).E ρ ((D μ).gHat0))
    (η : ℝ → ℝ → ℝ)
    (hi1 : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      FsI1Regime (M μ ρ hc).D.K (M μ ρ hc).D.a (M μ ρ hc).D.R (M μ ρ hc).D.ρz
        (M μ ρ hc).D.μ (M μ ρ hc).D.εT (M μ ρ hc).D.c1 (M μ ρ hc).D.c2 (M μ ρ hc).D.Kl
        (M μ ρ hc).D.s (M μ ρ hc).D.d)
    (hn : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ), 1 ≤ (M μ ρ hc).n)
    (hℓ : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ), 0 < (M μ ρ hc).D.ℓ)
    (hmis : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      |((M μ ρ hc).n : ℝ) + 1 - (M μ ρ hc).D.ℓ * Real.sqrt ((M μ ρ hc).D.ρz * (M μ ρ hc).D.a)|
        ≤ η μ ρ * ((M μ ρ hc).D.ℓ * Real.sqrt ((M μ ρ hc).D.ρz * (M μ ρ hc).D.a)))
    (hη : ∀ (μ ρ : ℝ), 0 ≤ η μ ρ) (hη1 : ∀ (μ ρ : ℝ), η μ ρ ≤ 1 / 4)
    (hsharp : ∀ (μ ρ : ℝ) (hc : CloseCondFS v μ ρ),
      SharpCmpEta (D μ).F (D μ).E ρ ((D μ).gHat0) (M μ ρ hc) (η μ ρ))
    (Dsup G : ℝ → ℝ → ℝ) (Cn C₄ C₅ C₀ : ℝ) (hav : 0 < a v)
    (hC₄ : 0 ≤ C₄) (hC₅ : 0 < C₅) (hC₀ : 0 ≤ C₀) (hCn : Cn ≤ 16)
    (hnum : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      BogNumeric (D μ).F (D μ).E ρ)
    (hbigM : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → 0 ≤ (D μ).E.bigM)
    (hBessel : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ f : (D μ).F.H,
      (D μ).F.bp ((∑ k : (D μ).Mode, (D μ).F.nOp k) f) f ≤ Cn * (D μ).F.bp ((D μ).T.N f) f)
    (A C : ℝ → ℝ → ℝ)
    (hAwin : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      ∀ k : (D μ).Mode, bogA (D μ).E ρ k ≤ A μ ρ)
    (hCwin : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      ∀ k : (D μ).Mode, |bogC (D μ).E ρ k| ≤ C μ ρ)
    (hKbig : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      10 ^ 6 * (A μ ρ + C μ ρ + 1) * ((D μ).E.bigM + 1)
        * ((Fintype.card (D μ).Mode : ℝ) + 1) ≤ winKbar (D μ).E (Dsup μ ρ))
    (hDsup : ∀ (μ ρ : ℝ) (k : (D μ).Mode), bogD (D μ).E ρ k ≤ Dsup μ ρ)
    (hG : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → (∑ k ∈ (Work.BoseB7.excited (D μ).Mode).filter
        (RHi (D μ).F (KzEnvAt (D μ).E ρ)),
        (bogD (D μ).E ρ k) * (bogGamma (D μ).E ρ k) ^ 2) ≤ G μ ρ)
    (hEzero : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      zpErrorSharpEta (ell v μ) (a v) (M μ ρ ‹_›).D.R (M μ ρ ‹_›).D.εT (M μ ρ ‹_›).D.Kl
        (M μ ρ ‹_›).D.s (M μ ρ ‹_›).D.d (M μ ρ ‹_›).D.μ ρ (M μ ρ ‹_›).n (M μ ρ ‹_›).D.K
        (η μ ρ) ≤ C₄ * errBracket v R μ)
    (hwinG : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      G μ ρ ≤ (C₅ * errBracket v R μ) / 2)
    (hwinGS : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      G μ ρ * (winKbar (D μ).E (Dsup μ ρ) + zpKapSum (D μ).E ρ)
        ≤ (C₅ * errBracket v R μ) ^ 2 / 16)
    (hδ : ∀ (μ : ℝ), Adm v ε₀ μ → (D μ).viewFS v h μ → ∀ ρ : ℝ, (hc : CloseCondFS v μ ρ) →
      (M μ ρ ‹_›).D.δ ≤ C₀ * dil v μ * (R / a v) ^ 2)
    (hg0 : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).gHat0 = 8 * π * a v)
    (hmu : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.mu = μ)
    (hell : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.ell = ell v μ)
    (hascat : ∀ μ : ℝ, Adm v ε₀ μ → (D μ).viewFS v h μ → (D μ).E.aScat = a v) :
    BogOpBoundAtFS v h R D :=
  BogOpBoundAtFS_of_with hε₀
    (bogOpBoundAtFSWith_of_sharpMatchEta v h R D ε₀ hε₀1 M η hi1 hn hℓ hmis hη hη1 hsharp Dsup G
      Cn C₄ C₅ C₀ hav hC₄ hC₅ hC₀ hCn hnum hbigM hBessel A C hAwin hCwin hKbig hDsup hG hEzero hwinG hwinGS hδ
      hg0 hmu hell hascat)

end Work.BoseBogFS
