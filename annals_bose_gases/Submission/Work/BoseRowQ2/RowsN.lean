import ChallengeDeps
import Submission.Work.BoseRowQ2.Rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.RowsN` — the `NH` route of row 3 (lead's ruling 2026-10-08)

**Live again** (un-retired by the lead's NH ruling, `LEAD_RULING_NH.md`): row 3
(`RowQ2AllRegimeN`) holds at the *current* `T.NH`, through the rows of this file.

* **`GchiAtN`**  `⟨Gop⟩ ≤ (1+ε)⟨Σ_k a_k†a_k⟩ + (1+1/ε)(C₁/κ_lat)²⟨T.N⟩` (`κ_lat = K_LK_ℓ/2π = ℓκ`);
* **`MainAtN`**  FS l.3240–3262 at the halved `b/800` `ℓ⁻²` credit, so that the freed `b/800` pays
  the `T.N` correction, while its own `NH` slot stays inside the `b/400` `NH` half of `gapOpT`;
* **`ArithAt2`** `2ρŴ₁ω(0)(1+1/ε)(C₁/κ_lat)² ≤ (b/800)ℓ⁻²`;
* the row-level packages `RowGchiN`, `RowMainN`, `RowArith2`, `RowQ2AllCoreN`, and the packing
  `RowQ2AllRegimeN_of_coreN` (`RowQ2All_of_coreN.lean`) that produces the gate's `hrow3All`.

## The earlier "SUPERSEDED / FALSE" verdict on this file is **RETRACTED**

It rested on the witness `u = θ_{s₀} + h_N` ("one particle, `f_L` kills `h_N`") with
`⟨Gop⟩ = 1`, `⟨Σ_k a_k†a_k⟩ → 0` and — the *error* — `⟨T.N⟩ = 1`.  For the one-particle state
`a†(u)|vac⟩` one has `T.N = totNumOp`, hence `⟨T.N⟩ = ‖u‖² = 1 + ‖h_N‖²`; being one particle means
`N`-eigenvalue `1`, **not** unit norm.  On that witness `h_N` must cancel `θ_{s₀}` on `{χ ≥ c}`,
and duality against a band-limited test function of bandwidth below `κ` forces `‖h_N‖² ≥ e^{cK}`
with `K = κℓ = d⁻² = t^{−12/323}`; so `(1+1/ε)(C₁/κ_lat)²⟨T.N⟩` is *huge* on the witness and pays
the deficit.  The 3-D numerics of `LEAD_RULING_NH.md` §2 give the worst-case deficit
`λ_max(Gop − Qχ²Q)/‖u‖²` as `0.31` at `K = 32` and `0.176, 0.054, 0.024` at `K = 48, 96, 144` — it
tends to `0`, faster than `1/K`.

The *other* refutations in this directory are unaffected: `not_payMask`/`not_payMaskRegime` kill
only the mask route (`maskNum ⪯ C₀·NH`), and the flat-layer packets of
`FINDING_RowQ2AllCubeCore_FALSE.md` have `∫χ²|·|² ≈ e^{−R/2c}‖u‖²`, so they too are paid by the
`δ‖u‖²` rows.

**Route status** (lead's work list, `LEAD_RULING_NH.md` §6): (B) `gchiN_oneBody` and its one-body
lift, (C) `rowGchiN_honest` (from (B) via `besselOpMat_le_of_mat`), (D) `rowArith2_honest`, and then
(E) `rowQ2AllRegimeN_honest` packs `RowQ2AllCoreN` and applies `RowQ2AllRegimeN_of_coreN`.  The
`MaskRow.lean` route and the (R1)/(R2) landings are records only.

## The corrected `Gchi`/`Main` rows (design history)

The lead's `BOSE_HARD_DESIGN.md` §3 rules that `Rows.lean`'s `GchiAt` is **false**
for a structural reason: the honest `n₊^H` (`T.NH`) is a *χ-weighted* number, while
FS's `n₊^H` is the free high-momentum number of `Qψ`.  Witness (hand argument,
`BOSE_HARD_DESIGN.md` §3): the one-particle θ-state `u = θ_{s₀} + h_N` with `h_N`
high-pass and approximating `−θ_{s₀}` on the ball `B` — there `⟨Gop⟩ = 1` while
`⟨Σ_k a_k†a_k⟩ → 0` and `⟨n₊^H⟩ → 0`, because `fL` kills the high-pass part inside
`Gop` and the χ-weighted `NH` sees nothing.  (This directory's own delegation
`FINDING_rowGchi_honest_session1.md` §1 recorded the same witness and reduced `GchiAt` to
the matrix inequality `A ⪯ (1+ε)F + (Cχ/(32ε))T`; **its quantitative conclusion is only as good
as the row it attacks** — it is the χ-weighted `NH` that the witness defeats, not `T.N`, see the
retraction above.  The *shell* `κ < |k| ≤ 2κ` is the reason the `NH`-form cannot be repaired by
any frame comparison: the mask weights `(1−f_L)²` are supported there while `η_H = 0`  —
`not_payMaskRegime`.)

The correction (lead, in their words: "State `RowGchiN` with
`(1+1/ε)(C₁/κ_lat)²·T.N` in place of `(Cχ/ε)·NH`, `κ_lat = K_LK_ℓ/2π`") is that the
correction term must be a *free* number:

* **`GchiAtN`**  `⟨Gop⟩ ≤ (1+ε)⟨Σ_k a_k†a_k⟩ + (1+1/ε)(C₁/κ_lat)²⟨T.N⟩`,
* and consequently **`MainAtN`** drops its `ℓ⁻²` credit from `b/400` to `b/800`, so
  that the freed `b/800` pays the new correction:
  `2ρ(1+ε)Ŵ₁ω(0)⟨Σ_k a_k†a_k⟩ ≤ ⟨Q₂^ex,all⟩ + (b/800)ℓ⁻²⟨n₊⟩ + (b/800)ε_T(dℓ)⁻²⟨n₊^H⟩`,
* with a second arithmetic row **`ArithAt2`** `2ρŴ₁ω(0)(1+1/ε)(C₁/κ_lat)² ≤ (b/800)ℓ⁻²`
  (the lead's (d); it holds since `(C₁/κ_lat)² ≍ d⁴` and `ε ≍ ε_T^{-1}(dK_ℓ)²`, so
  the ratio is `~X^{17.75} → ∞`).

The budget then closes exactly as before: `b/800` (Gchi correction) + `b/800` (Main's
`ℓ⁻²` slot) = `b/400` (the `ℓ⁻²` half of `gapOpT`), and Main's `b/800` `NH` slot is
inside the `b/400` `NH` half.  The *old* `GchiAt`/`RowGchi`/`MainAt` are kept in
`Rows.lean` (the child's `rowMain_honest` is stated against them and is proved there);
they are superseded and must not be used downstream.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## 1. The corrected pointwise conditions -/

/-- **FS l.3253, corrected** (lead's `RowGchiN`): the localised
`Σ_jQ_{L,j}χ_Λ²Q_{L,j}` (`Gop`) against the total χ-number and the **free**
high-momentum number `T.N = n₊`, with the commutator constant `C₁` and the lattice
threshold `κ_lat = K_LK_ℓ/2π`.  The `(1+1/ε)` is Young's inequality; `C₁/κ_lat` is
the Schur norm of the commutator `[χ, f_L(D)]` (`BOSE_HARD_DESIGN.md` §3(a)–(b)). -/
def GchiAtN {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (C₁ : ℝ) (κ_lat : ℝ) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (ε : ℝ) : Prop :=
  ∀ Ψ : (Work.BoseRowsFS.honF v h fc fu HM μ).H,
    (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        ((Work.BoseRowsFS.honT v h fc fu HM μ).Gop (Work.BoseRowsFS.honE v h fc fu HM μ))
      ≤ (1 + ε) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
        + (1 + 1 / ε) * (C₁ / κ_lat) ^ 2
          * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              (Work.BoseRowsFS.honT v h fc fu HM μ).N

/-- **FS l.3240–3262 at a fixed `ε`, re-stated** (lead: "re-state `MainAt` with
`(b/800)ℓ⁻²·N`"): the `ℓ⁻²` credit is halved so that the other half pays the
`GchiAtN` correction; the `NH` credit is unchanged. -/
def MainAtN {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ ρ ε : ℝ) : Prop :=
  ∀ Ψ : (Work.BoseRowsFS.honF v h fc fu HM μ).H,
    2 * ρ * (1 + ε) * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
      ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
            (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
        + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).N
        + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
            * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                    * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).NH

/-- **The second arithmetic row**: `2ρŴ₁ω(0)(1+1/ε)(C₁/κ_lat)² ≤ (b/800)ℓ⁻²`. -/
def ArithAt2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (C₁ : ℝ) (κ_lat : ℝ) (HM : ∀ μ : ℝ, HonestModes v μ) (μ ρ ε : ℝ) : Prop :=
  2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * (1 + 1 / ε) * (C₁ / κ_lat) ^ 2
    ≤ ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
        * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))

/-! ## 2. The corrected rows -/

/-- FS l.3253 corrected, as a row (with the cube-size row). -/
def RowGchiN {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) (C₁ : ℝ) (κ_lat ε : ℝ → ℝ) : Prop :=
  εg ≤ 1 →
    ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ : ℝ) (hμ : 0 < μ), μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
        ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
          GchiAtN (v := v) (h := h) (fc := fc) (fu := fu) C₁ (κ_lat μ) HM μ (ε μ)

/-- FS l.3240–3262 re-stated, as a row. -/
def RowMainN {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) (ε : ℝ → ℝ) : Prop :=
  εg ≤ 1 →
    ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ : ℝ) (hμ : 0 < μ), μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
        ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
          MainAtN (v := v) (h := h) (fc := fc) (fu := fu) HM μ ρ (ε μ)

/-- The second arithmetic, as a row. -/
def RowArith2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) (C₁ : ℝ) (κ_lat ε : ℝ → ℝ) : Prop :=
  εg ≤ 1 →
    ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ : ℝ) (hμ : 0 < μ), μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
        ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
          ArithAt2 (v := v) (h := h) (fc := fc) (fu := fu) C₁ (κ_lat μ) HM μ ρ (ε μ)

/-! ## 3. The corrected core -/

/-- **The core of the corrected row 3 at a *given* threshold and cube size**, in
the lead's corrected shape: one `C₁ ≥ 0`, one lattice threshold `κ_lat : ℝ → ℝ`
(`= K_LK_ℓ/2π`), one `ε : ℝ → ℝ` (FS's `ε ∝ ε_T^{-1}(dK_ℓ)²`), with the four
conditions `ArithAt`, `ArithAt2`, `GchiAtN`, `MainAtN` at `ε μ`. -/
def RowQ2AllCoreAtN {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) : Prop :=
  ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∃ κ_lat ε : ℝ → ℝ,
    (∀ μ : ℝ, 0 < μ → 0 < κ_lat μ) ∧ (∀ μ : ℝ, 0 < μ → 0 < ε μ) ∧
    RowArith (h := h) (fc := fc) (fu := fu) R εg Ng (96 / Real.pi) ε ∧
    RowArith2 (h := h) (fc := fc) (fu := fu) R εg Ng C₁ κ_lat ε ∧
    RowGchiN (h := h) (fc := fc) (fu := fu) R εg Ng C₁ κ_lat ε ∧
    RowMainN (h := h) (fc := fc) (fu := fu) R εg Ng ε

/-- **The corrected core, producing its own cube size and threshold** (both are
needed: `GchiAtN` needs the cube-size row, and the `ε`-window is astronomically
thin — `FINDING_RowQ2AllCore_FALSE.md`, `Rows.lean` §2). -/
def RowQ2AllCoreN {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) : Prop :=
  ∃ Ng : ℝ → ℕ, ∃ εg' : ℝ, 0 < εg' ∧ εg' ≤ εg ∧
    RowQ2AllCoreAtN (h := h) (fc := fc) (fu := fu) R εg' Ng

end Work.BoseRowQ2
