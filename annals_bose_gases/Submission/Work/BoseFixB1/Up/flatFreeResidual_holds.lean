import ChallengeDeps
import Submission.Work.BoseFixB1.Up.FlatRowsDelta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Up.flatFreeResidual_holds` — the flat (condensed) branch of FS `thm:smallbox`

## ⚖️ LATER SESSION (2026-10-10, evening): read `Up/FINDING_two_spellings_of_the_flat_leaf.md`

Three machine-checked facts that decide how this leaf may be *attacked* (the statement below is
unchanged):

1. `Work.BoseFixB1.Up.FlatWordKin ⟺ Work.BoseFixB1.Up.FlatRowsDeltaKin`
   (`Up/flatWordKinIff.lean`), so the band-case refutation of the word spelling
   (`Up/FINDING_flatWordLeBand_missing_count_cap.md`) is a refutation of **`FlatRowsDeltaKin` as
   well**: the existential `Efib`/`Epair` does not spread the offending cross term (the minimal
   witness is the pair of deviations themselves, which reproduces the word inequality).  Do not
   re-file either as an open leaf on the current hypothesis list.
2. The frozen flat arm's *other* spelling (`Work.BoseFixB1S.FlatArmSliding` ⟸
   `Work.BoseFixB1.WindowSliding`) carries the **volume window** `S ≤ K₀(μ|B(u)|+1)‖Φ‖²`, and
   `Up/countCapBridge.lean` (PROVED) shows that window and the word lane's count cap
   `n ≤ Cs·μ·|B(u)|` are **the same hypothesis** (both directions).  So a per-box row of this arm
   must carry the count window; supplying it is a *separate, shared* obligation (FS's
   `(n+1)/|B(u)| ≤ 9μ`, `thm:smallbox` l.3907), not part of the razor.
3. The *density* form `τ ≤ Cμ` must not be used: it needs a lower bound on `chiMass = ∫χ²`, which is
   unreachable for the corpus's opaque bump (see
   `Up/FINDING_flatWordLeBandCapped_session4.md` §6ter).  Use the *volume/count* form.
4. **The same argument reaches this residual itself** (see `FINDING_two_spellings_of_the_flat_leaf.md`
   §0.2/§2): `PerBoxFlatFree`'s class *contains* the refuted dense-band class and the offending
   column `μ·flatFibSum` is present in this residual's own inequality with coefficient one (`c₁`
   multiplies only the nonnegative `Fterm`; `C`'s slot is density-independent).  So — *granting the
   admissibility of the filed refutation's pair-dead family* (the one check named in that note §4) —
   the statement below is **false as filed**, and every route through it
   (`Work.BoseFixB1.perBoxFWeight_holds` included) is dead.  That is why the honest options are
   *re-routing* (cube lane / count lane) rather than proving this statement.

Consequently the honest options for this leaf are: (a) keep this statement (which is *stronger* than
FS's `thm:smallbox`) and prove the razor without a window — no route known, the known route is
refuted; or (b) re-point the chain's leaf to the windowed/capped spelling
(`Work.BoseFixB1.Up.FlatBandCappedJoint`, `Up/flatWordLeBandCapped.lean`), whose residual is the
razor *with* the window supplied by fact 2.

## ⛔ NEW (2026-10-10): the route to this leaf through `FlatWordKin` is BROKEN at the band case
##    (the residual itself is NOT refuted — read the reconciliation)

Read `Up/FINDING_flatWordLeBand_FALSE_countCap.md` **first**.  Its prover (and the sibling prover
for the cube twin `BoseB1Cube.bandKinDead_of_cubeRazor`) declared the band case of the dense arm
**FALSE as spelled**: the fibre-deviation cross term `2μ·sup|δ|·√(n₊·S)` (`S = boxFlatCount`) carries
the **unbounded factor `S`**, while the hypotheses (`goodSet`, `¬IsThinBox`, `n₊ < γn‖Φ‖²`,
`μ ≤ τ`) bound neither `n` nor `S`, and every payer in the row is quadratic in the deviation or
norm-scaled.  The missing hypothesis is the **count cap** `S ≤ Cs·τ·κ·‖Φ‖²` that every *proved*
fibre row in the corpus carries.

**What that does and does not kill** (the reconciliation): the reductions here are one-way —
`flatRowsDeltaKin_of_flatWordKin` and `flatFreeResidual_of_rowsDeltaKin` prove
`FlatWordKin ⟹ FlatRowsDeltaKin ⟹ FlatFreeResidual` — so the band case of `FlatWordKin` being false
kills the *route* through `FlatWordKin`, **not** this residual.  `flatFreeResidual_holds`'s own
analysis below (the corners are paid by the boundary flatness, `chiSmallB ≲ d^N`) still stands, and
`FlatRowsDeltaKin` (with its existential `Efib`/`Epair`, which can spread the cross term between the
two deviations) is not refuted either.

## ⚖️ VERDICT (corrected): the statement is **TRUE, not refuted** — the corner boxes are *paid* by
##    the boundary flatness of the corpus bump

The sliding-box word `sbKin` windows its **spectral** slot by the *ball*-supported cutoff
`chiB ℓ d u = chiScale ℓ · chiScale (ℓd) (· − (ℓd)•u)`, while every *other* object of `PerBoxF` —
`nCountB`, `chiMass`, `w1MassB`, `flatFibSum`, `flatPairSum`, `flatErrB` — is built from the
*cube*-supported bump `chiSmallB M ℓ d u` (see `DLSmallKernels.wSmallPair`).  The two windows have
different supports, and at a **corner** box (`ℓ/2 + ℓd/2 ≤ ‖(ℓd)•u‖`, which is compatible with
`u ∈ goodSet`/`interiorSet`, `dlBox ≠ ∅`, `¬IsThinBox` and `chiSmallB ≢ 0`) the spectral half of
the word vanishes identically, for every state (`BoseFixB1/CornerMismatch.lean`,
`Work.BoseFixB1.corner_tBwordKinInd_eq_zero`), while the kernels stay alive.

**A previous session read that as a refutation** (`Up/FINDING_flatFreeResidual_session2.md` §7:
"the hole/Jastrow family has `flatPairSum = 0` and density `τ = μ`, so `PerBoxF` at `c₁ = 0`
requires `½μ²W₁‖Φ‖² ≤ tbGapCoeff (ℓd) ε_T·n₊ + C(μ²(a v)Γκ‖Φ‖² + μ(a v)‖Φ‖²)`, whose right side is
`o(½μ²W₁‖Φ‖²)`").  **That reading is wrong**, and the error is a single but decisive one: it
evaluates the demand `W₁ = ∬w_{1,B(u)}` at its *unsaturated* value `≈ 8π(a v)(ℓd)³` on the corner.
On the corner the whole two-factor cutoff is *superpolynomially small*:

    Work.BoseFixB1.chiSmallB_corner_flat  (PROVED, axiom-clean, this directory)
      ∀ M ≥ 1, ∀ N, ∃ C > 0, ∀ ℓ d > 0, ∀ u x,  ℓ/2 + ℓd/2 ≤ ‖(ℓd)•u‖ →
        chiSmallB M ℓ d u x ≤ C · (((√3 − 1)/2)·d)^N ,

i.e. `chiSmallB ≲ d^N`, hence `chiMass = ∫chiSmallB² ≲ d^{2N}(ℓd)³` and
`w1MassB ≈ 8π(a v)·chiMass ≲ (a v)(ℓd)³d^{2N}` on the corner.  At the corner `PerBoxF` therefore
reads (the F-row is `0` at density `τ = μ`; the mean-field rows `∝ chiMass` are negligible)

    ½μ²·w1MassB·‖Φ‖² + C·μ²(a v)κ·chiMass·‖Φ‖²  ≲  gap·n₊ + C·μ(a v)‖Φ‖² ,

and the **un-suppressed** credit `C·μ(a v)‖Φ‖²` (the last term of FS's error bracket,
`+μ(a v)` inside the parenthesis, `−C·(…)` overall) wins: the ratio is

    μ(a v)(ℓd)³d^{2N} / μ(a v)  =  μ(ℓd)³ d^{2N}  =  t^{-0.458}·t^{0.0372·N}  →  0   (N ≥ 13),

where `t = μ(a v)³`, `(ℓd)³ = a³t^{-1.458}`, `d = t^{6/323}`.  So the corner case is **not** a
counterexample — it is exactly the case FS's `chiSmallB`-based estimate `eq:chiBadset`
(`|χ_{B(u)}| ≤ C(μ^{-1/3}/ℓ)^M`) is designed for, transposed to the `d`-scale `(√3−1)d/2`.  The same
computation kills the sibling's variant that keeps only the gap half: the gap half's own payment
`tbGapCoeff·n₊` is *additional* to the credit that already suffices.

**Consequences.**
* Do **not** `declare_false` this target, and do not re-file
  `Work.BoseFixB1.PerBoxF`, `Work.BoseFixB1.Up.FlatRows*`, `PerBoxFlatFree` or the sibling's
  `flatBranch*`/`SmallBoxCollected`/`AprioriHLambdaIneq` on the strength of the corner
  configurations.
* The mismatch stays a *modelling* remark (FS's own `χ_B` is a cube bump and uses **one** cutoff in
  both slots — `final_v2.tex` l.3522, `eq:chiBdefinition`; the corpus's `chi` is a `ContDiffBump 0`,
  a *ball*, `Submission/CubicChi.lean`), and it is what motivates the matched-window chapter
  `Submission/Work/BoseFixB1/Cube/` — but it is **not** a refutation of the frozen chapter.

## (What remains valid in this cone)

The target: `FlatFreeResidual v h R = ∃ γ > 0, PerBoxFlatFree v h R γ`, i.e. `PerBoxF` at a free
threshold `γ` on the good set, non-thin sliding boxes.  It is the single residual of
`Work.BoseFixB1.perBoxFWeight_holds`.

## State of the art in this cone (see `Up/FINDING_flatFreeResidual_session2.md`)

Proved and axiom-clean here: the sharp flat ledger and its **Δ-augmented, kinetic-aware** version

* `Work.BoseFixB1.Up.perBoxF_of_ledger_delta` (`Up/FlatLedgerDelta.lean`) — `PerBoxF` from the two
  band rows plus the budget `Efib + Epair ≤ C·err·N + W₁·slack + ½(W₂−W₁)(τ²N+V) + P` with an
  arbitrary kinetic payer `P ≤ sbKin` (the skeleton discards `sbKin`, or keeps only its `ε_T`-gap
  half — that is why the corpus's deviation-row verdicts are pessimistic),
* `Work.BoseFixB1.Up.FlatRowsDeltaKin` (`Up/FlatRowsDelta.lean`) — **the residual in its weakest
  known form**: the two deviation rows with the budget paid by
  `C·flatErrB + flatSlackB + Δ + sbKin`,
* `Work.BoseFixB1.Up.FlatWordKin` (`Up/FlatRowsDelta.lean`) — the same residual in *word* form
  (no existential quantifiers): `sbWord ≥ ½W₂(τ²‖Φ‖²+V) − μW₁τ‖Φ‖² − C·flatErrB − flatSlackB − Δ`;
  `flatRowsDeltaKin_of_flatWordKin` shows it is equivalent to `FlatRowsDeltaKin`,
* `Work.BoseFixB1.Up.flatFreeResidual_of_rowsDeltaKin`
  (`Up/flatFreeResidual_of_splitDelta.lean`) — **`FlatRowsDeltaKin ⟹ FlatFreeResidual`**,
* `Work.BoseFixB1.Up.flatFreeResidual_of_splitDelta` — the same with the `ε_T`-gap payer
  `K₂μ(a v)n₊` (via the lever `Up.sbKin_ge_K2_mu_av_nPlus`), and
  `flatRowsSplitDelta_of_flatRowsSplit` certifying that the Δ-residual is strictly weaker than the
  corpus's `FlatRowsSplit`.

**What remains is exactly `Work.BoseFixB1.Up.FlatRowsDeltaKin`** — a statement about the *word*
(not about `PerBoxF`): in the band `n₊ < γnN`, the fibre and pair deviations are absorbed by the
proved error bracket, the arithmetic slack, the pair-condensate surplus `Δ` and the full kinetic
word `sbKin`.  All other branches are PROVED (`Up.perBoxFlatZeroHolds` at `n₊ = 0`,
`Up.gapAtAll γ` for `n₊ ≥ γnN`, `Up.perBoxF_thin_holds` for thin boxes).  The correlation-hole /
Jastrow states — the only family any refutation attempt uses — *do* satisfy this residual: their
pair energy is suppressed exactly, but their in-box hole profile has a large Dirichlet energy, so
`sbKin ≳ 4πρ₀²n_in/w ≫ ½W₂(τ²N+V) = Θ(μ(a v)n_in)`; see the FINDING §2.  **Do not
`declare_false`** on the strength of those notes.
-/

namespace Work.BoseFixB1.Up

theorem flatFreeResidual_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseFixB1.Up.FlatFreeResidual v h R := by sorry

end Work.BoseFixB1.Up
