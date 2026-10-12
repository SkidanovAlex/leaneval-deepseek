import ChallengeDeps
import Submission.Work.BoseBogFS.hZP_of_match
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.FsFinal` — `BogOpBoundFS` from FS's own data

> **⚠ SUPERSEDED (session 2).**  The capstone below is kept as the *shape* of the assembly,
> but it is **not instantiable**: its `hZP`/`hEzero` slots use the *crude* `zpError`
> (`FINDING_zpRiemErr.md`), and all its slots are quantified over **every** `μ` while every
> fact about the environment's kernels is available only under `Adm` and the view
> (`FINDING_slot_shapes.md`).  Use **`SharpCap.bogOpBoundAtFSWith_of_sharpMatchEta`** /
> **`SharpCap.bogOpBoundAtFS_of_sharpMatchEta`** instead — same conclusion
> (`BogOpBoundAtFS`), sharp error budget, `Adm`/`viewFS`-indexed slots.  The transfers
> `hZP_of_match`/`hKAP_of_match` below remain useful and are still exported.

The capstone: `BogOpBoundAtFS` — the design's `BogOpBoundFS` at the corrected close
threshold — for an arbitrary family `D : ℝ → KzDatum` (not only `HonestBoxFam`), with

* `M : ∀ μ, FsMatch (D μ).F (D μ).E ((D μ).E.rho) ((D μ).gHat0)` — FS's mesh-`n` data at
  **the environment's own density** `(D μ).E.rho`, i.e. the "mode identification" repair of
  `BOSE_BOXFOCK_LEAD.md` §5.2 *at the datum* (plus `hreg : FsZeroRegime` at that datum).
  Indexing by the density of the datum rather than by the statement's free `ρ` is what makes
  the family satisfiable: `FsZeroRegime.hrel` (`(n:ℝ)+1 = ℓ√(ρ_z a)`) ties the mesh to
  `ρ_z = (D μ).E.rho`, and `E.rho` (unlike the statement's `ρ`) is only bounded by the view,
  so it can be chosen mesh-compatible.  See `FINDING_mesh_integrality.md`.
* the per-density slots `hZP`/`hKAP` — the two B6Est estimates at the statement's density
  `ρ`.  **These are discharged at `ρ = (D μ).E.rho` by `hZP_of_match`/`hKAP_of_match`**
  (rewriting `(D μ).E.aScat`, `(D μ).E.ell`, `(D μ).E.mu` with `hview`); at a *general*
  close `ρ` the environment's mode lattice is not mesh-matched to `ρ`, so the transfer needs
  either the small-mismatch version of `Work.BoseB6Est.fsZeroPoint_le` or a sharper
  `zpRiemErr` — `FINDING_mesh_integrality.md`, `FINDING_zpRiemErr.md`.
* `hnum`, `hbigM`, `hBessel`, `hα`, `hγ`, `hDsup`, `hG` — the gate/window rows
  (`hnum` is discharged by `bogNumeric_of_viewFS`);
* `hEzero`, `hResB`, `hδ`, `hδ0` — the §11 slots (`hResB` by `hResB_of_window`, `hEzero` by
  `zpError_le_scalar` plus a sharpened `fsZeroPoint_le`);
* the reserve by `hRes_of_window`; the §11 arithmetic by `hArith_of_pieces`.
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

/-- The `Ezero` slot of `hZP`: the lattice-mesh, discretisation and `ε(μ,ρ_z)` errors of
`Work.BoseB6Est.fsZeroPoint_le`, at the density `ρ` (an `abbrev`, so it unfolds
transparently and matching is never a transparency issue). -/
abbrev zpError (ℓ aScat a R εT Kl s d μ ρ : ℝ) (n : ℕ) (K : FsKernel) (c₂ : ℝ) : ℝ :=
  (1 / 2) * (((2 * π) ^ 3)⁻¹ * ℓ ^ 3 * (ρ ^ 2 * aScat * Real.sqrt (ρ * aScat ^ 3))
        * (Work.BoseB6.latticeMeshErr (8 * π) n + zpRiemErr n K c₂)
      + 10 ^ 10 * Work.BoseB6.lhyEps a R εT Kl s d μ * ρ ^ 2 * a * Real.sqrt (ρ * a ^ 3)
          * ℓ ^ 3)

/-- **`BogOpBoundAtFS` from FS's own data (at the datum's density).** -/
theorem bogOpBoundFS_of_fsData (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum)
    (M : ∀ μ : ℝ, FsMatch (D μ).F (D μ).E ((D μ).E.rho) ((D μ).gHat0))
    (hreg : ∀ μ : ℝ,
      FsZeroRegime (M μ).n (M μ).D.K (M μ).D.a (M μ).D.R (M μ).D.ρz (M μ).D.ℓ (M μ).D.μ
        (M μ).D.z (M μ).D.chiM (M μ).D.δ (M μ).D.εT (M μ).D.c1 (M μ).D.c2 (M μ).D.Kl
        (M μ).D.s (M μ).D.d)
    (Dsup G σv : ℝ → ℝ → ℝ) (Cn C₄ C₅ C₀ : ℝ) (hav : 0 < a v)
    (hσv : ∀ (μ ρ : ℝ), 0 < σv μ ρ)
    (hC₄ : 0 ≤ C₄) (hC₅ : 0 ≤ C₅) (hC₀ : 0 ≤ C₀) (hCn : Cn ≤ 16)
    (hnum : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → BogNumeric (D μ).F (D μ).E ρ)
    (hbigM : ∀ (μ ρ : ℝ), 0 ≤ (D μ).E.bigM)
    (hBessel : ∀ (μ ρ : ℝ), ∀ f : (D μ).F.H,
      (D μ).F.bp ((∑ k : (D μ).Mode, (D μ).F.nOp k) f) f ≤ Cn * (D μ).F.bp ((D μ).T.N f) f)
    (A C : ℝ → ℝ → ℝ)
    (hAwin : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ →
      ∀ k : (D μ).Mode, bogA (D μ).E ρ k ≤ A μ ρ)
    (hCwin : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ →
      ∀ k : (D μ).Mode, |bogC (D μ).E ρ k| ≤ C μ ρ)
    (hKbig : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ →
      10 ^ 6 * (A μ ρ + C μ ρ + 1) * ((D μ).E.bigM + 1)
        * ((Fintype.card (D μ).Mode : ℝ) + 1) ≤ winKbar (D μ).E (Dsup μ ρ))
    (hDsup : ∀ (μ ρ : ℝ) (k : (D μ).Mode), bogD (D μ).E ρ k ≤ Dsup μ ρ)
    (hG : ∀ (μ ρ : ℝ), (∑ k ∈ (Work.BoseB7.excited (D μ).Mode).filter
        (RHi (D μ).F (KzEnvAt (D μ).E ρ)),
        (bogD (D μ).E ρ k) * (bogGamma (D μ).E ρ k) ^ 2) ≤ G μ ρ)
    (hZP : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ →
      (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA (D μ).E ρ k)
          (bogB (D μ).E ρ k))
        ≤ -(4 * π * Work.UBB.lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3))
          + (1 / 2) * ell3 v μ * ρ ^ 2 * (D μ).E.W1omega0
          + zpError (ell v μ) (a v) (M μ).D.a (M μ).D.R (M μ).D.εT (M μ).D.Kl (M μ).D.s
              (M μ).D.d (M μ).D.μ ρ (M μ).n (M μ).D.K (M μ).D.c2)
    (hKAP : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ →
      (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr (bogA (D μ).E ρ k)
          (bogB (D μ).E ρ k) (bogC (D μ).E ρ k))
        ≤ (ρ - μ) ^ 2 * ((D μ).gHat0 / 2) * ell3 v μ * (1 + (M μ).D.δ))
    (hEzero : ∀ (μ ρ : ℝ), (hc : CloseCondFS v μ ρ) →
      zpError (ell v μ) (a v) (M μ).D.a (M μ).D.R (M μ).D.εT
        (M μ).D.Kl (M μ).D.s (M μ).D.d (M μ).D.μ ρ (M μ).n (M μ).D.K (M μ).D.c2
      ≤ C₄ * errBracket v R μ)
    (hResB : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ →
      reserveLoss (D μ).E ρ (Dsup μ ρ) (G μ ρ) (σv μ ρ) ≤ C₅ * errBracket v R μ)
    (hδ : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → (M μ).D.δ ≤ C₀ * dil v μ * (R / a v) ^ 2)
    (hδ0 : ∀ (μ ρ : ℝ), CloseCondFS v μ ρ → 0 ≤ (M μ).D.δ)
    (hg0 : ∀ μ : ℝ, (D μ).gHat0 = 8 * π * a v)
    (hmu : ∀ μ : ℝ, (D μ).E.mu = μ) (hell : ∀ μ : ℝ, (D μ).E.ell = ell v μ) :
    BogOpBoundAtFS v h R D := by
  refine ⟨1, C₄ + C₅ + C₀ / ((2 : ℝ) ^ 26 * π) + 1, one_pos, by positivity, ?_⟩
  intro μ hadm hview ρ hρ hclose f hf
  have hμ : 0 < μ := hadm.1
  have hdil1 : Work.BoseFixR.dil v μ ≤ 1 := by
    have := hadm.2.1
    simpa only [Work.BoseFixR.dil] using this
  have hcs : CloseCondFS v μ ρ := hclose
  have hArith := hArith_of_pieces v R μ ρ (M μ).D.δ
    (zpError (ell v μ) (a v) (M μ).D.a (M μ).D.R (M μ).D.εT (M μ).D.Kl (M μ).D.s
      (M μ).D.d (M μ).D.μ ρ (M μ).n (M μ).D.K (M μ).D.c2)
    (reserveLoss (D μ).E ρ (Dsup μ ρ) (G μ ρ) (σv μ ρ)) C₄ C₅ C₀ (D μ).gHat0
    hav hμ hdil1 (hg0 μ) hcs (hδ μ ρ hcs) hC₀ (hEzero μ ρ hcs) (hResB μ ρ hcs) hC₄ hC₅
  have hmain := bogOpBound_at v h R (D μ) μ ρ (hnum μ ρ hcs) (hmu μ) (hell μ)
    (zpError (ell v μ) (a v) (M μ).D.a (M μ).D.R (M μ).D.εT (M μ).D.Kl (M μ).D.s
      (M μ).D.d (M μ).D.μ ρ (M μ).n (M μ).D.K (M μ).D.c2)
    (reserveLoss (D μ).E ρ (Dsup μ ρ) (G μ ρ) (σv μ ρ)) (M μ).D.δ
    (C₄ + C₅ + C₀ / ((2 : ℝ) ^ 26 * π) + 1) (hδ0 μ ρ hcs) (hZP μ ρ hcs) (hKAP μ ρ hcs)
    (by
      have hKbar : ∀ g : (D μ).F.H, (D μ).T.NWindow (D μ).E.bigM g →
          (D μ).F.qw g (KzBogFS (D μ).F (D μ).E ρ)
            ≤ winKbar (D μ).E (Dsup μ ρ) * (D μ).F.normSq g :=
        fun g hg => qw_KzBogFS_le_window_direct (D μ).F (D μ).T (D μ).E ρ Cn (A μ ρ) (C μ ρ)
          (winKbar (D μ).E (Dsup μ ρ)) (hnum μ ρ hcs) (hbigM μ ρ)
          (hBessel μ ρ) hCn (hAwin μ ρ hcs) (hCwin μ ρ hcs) (hKbig μ ρ hcs) g hg
      simpa only [reserveLoss, zpKapSum] using
        qw_dNumOpR_le_res (D μ).F (D μ).T (D μ).E ρ (winKbar (D μ).E (Dsup μ ρ)) (G μ ρ)
          (σv μ ρ) (hσv μ ρ) (hnum μ ρ hcs) hKbar (hG μ ρ))
    hArith f hf
  simpa only [errBracket, mul_assoc, hell, ell3, zpError] using hmain

/-- **The two per-density slots at the datum's density.**  `hZP_of_match` /
`hKAP_of_match` at `ρ := (D μ).E.rho` give the `hZP`/`hKAP` slots of
`bogOpBoundFS_of_fsData` *at that density* (one rewrites `(D μ).E.aScat`, `(D μ).E.ell`,
`(D μ).E.mu` with the view). -/
theorem hZP_slot_at_envRho (v : ℝ³ → ℝ) (h : ScatSol v) (R : ℝ) (D : ℝ → KzDatum)
    (M : ∀ μ : ℝ, FsMatch (D μ).F (D μ).E ((D μ).E.rho) ((D μ).gHat0))
    (hreg : ∀ μ : ℝ,
      FsZeroRegime (M μ).n (M μ).D.K (M μ).D.a (M μ).D.R (M μ).D.ρz (M μ).D.ℓ (M μ).D.μ
        (M μ).D.z (M μ).D.chiM (M μ).D.δ (M μ).D.εT (M μ).D.c1 (M μ).D.c2 (M μ).D.Kl
        (M μ).D.s (M μ).D.d)
    (μ : ℝ) (hview : (D μ).viewFS v h μ) :
    (∑ k : (D μ).Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint (bogA (D μ).E ((D μ).E.rho) k)
        (bogB (D μ).E ((D μ).E.rho) k))
      ≤ -(4 * π * Work.UBB.lhyC * (D μ).E.rho ^ 2 * a v * ell3 v μ
            * Real.sqrt ((D μ).E.rho * a v ^ 3))
        + (1 / 2) * ell3 v μ * (D μ).E.rho ^ 2 * (D μ).E.W1omega0
        + zpError (ell v μ) (a v) (M μ).D.a (M μ).D.R (M μ).D.εT (M μ).D.Kl (M μ).D.s
            (M μ).D.d (M μ).D.μ ((D μ).E.rho) (M μ).n (M μ).D.K (M μ).D.c2 := by
  have h := hZP_of_match (D μ).F (D μ).E ((D μ).E.rho) ((D μ).gHat0) (M μ) (hreg μ)
  rw [hview.2.2.1, hview.2.2.2.1] at h
  simpa only [zpError, ell3, mul_assoc] using h

end Work.BoseBogFS
