import ChallengeDeps
import Submission.Work.BoseRowQ2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.Rows` — the rows of FS l.3240–3262, at a *chosen* `ε`

FS's proof of `eq:Q3Cancels` (`final_v2.tex` l.3240–3262) consists of three
ingredients, all used at **one and the same** `ε ∝ ε_T^{-1}(dK_ℓ)²`:

1. **(l.3253–3254, `GchiAt`)** `Σ_jQ_{L,j}χ²Q_{L,j} ≤ (1+ε)Σ_jQ_jχ²Q_j + Cε^{-1}n₊^H`;
2. **(l.3240 + `eq:CompIntegrals-Final-2`, `MainAt`)** the `Q₂^ex` comparison
   `2ρ(1+ε)Ŵ₁ω(0)Σ_ka_k†a_k ≤ Σ_kρ(Ŵ₁ω(k)+Ŵ₁ω(0))a_k†a_k +` a fraction of the gap;
3. **(`ArithAt`)** the arithmetic that this `ε` is *both* large enough (so that
   `Cε^{-1}` is paid by the `ε_T(dℓ)⁻²n₊^H` gap) and small enough (so that the
   `(1+ε)` factor itself is paid by the `ℓ⁻²n₊` gap).

**The quantifier of `ε` is the delicate part** — two independent reviews of an
earlier statement caught this: `MainAt` with `ε` ranging over *all* of `(0,1]` is
**false**.  On the Part-A label-`0` witness (`⟨n₊⟩ = 1`, `⟨n₊^H⟩ = 0`,
`Σ_k⟨n_k⟩ ≥ (1−κ²)² ≈ 0.518`) it forces `2ρε(1−κ²)²ρŴ₁ω(0) ≤ (b/400)ℓ⁻²`, i.e.
`ε ≲ (μa³)^{3/323} → 0` — the same estimate (`ρŴ₁ω(0)ℓ² ≍ K_ℓ² → ∞`) that refutes
`RowQ2`.  The correct statement is therefore **joint**: one absolute `Cχ` and, at
every honest datum of the régime, one `ε` at which all three hold.  That is
`RowQ2AllCore` — the primary target of this directory (it *produces* its own
diluteness threshold, §2 below).  The same three conditions split by hand are the
composable rows `RowArith`/`RowGchi`/`RowMain` (one shared `Cχ` and one shared
`ε : ℝ → ℝ`), glued by `RowQ2AllCoreAt_of_rows`.

## The budget of the reserve (`b/400`)

The corpus reserves `b/400` of the gap where FS spend `b/50`.  The assembly
(`RowQ2All_of_rows.lean`) splits it in halves, `b/800` for the `n₊^H` correction
of (1) and `b/800` (with the whole `ℓ⁻²n₊` part) for (2).  Both halves are
satisfied with margin a positive power of `(μa³)` (see `NOTES.md`, `REPORT.md`),
so the `b/400` reserve is **not** tight.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseB7.FockData

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **The total χ-mode number operator** `Σ_k a_k†a_k` over **all** labels.  This is
FS's `Σ_jQ_jχ²Q_j` in the χ-mode picture (`final_v2.tex` l.1584,
`a_k = ℓ^{-3/2}a(Q(e^{ikx}χ_Λ))`): FS's l.3253 compares the localised
`Σ_jQ_{L,j}χ²Q_{L,j} = Gop` with it. -/
def allNumOp (F : FockData Mode) : F.H →ₗ[ℝ] F.H := ∑ k : Mode, F.nOp k

/-- `qw` of a finite weighted sum over all labels. -/
theorem qw_sum_all (F : FockData Mode) (Φ : F.H) (c : Mode → ℝ)
    (X : Mode → F.H →ₗ[ℝ] F.H) :
    F.qw Φ (∑ k : Mode, c k • X k) = ∑ k : Mode, c k * F.qw Φ (X k) := by
  simp only [FockData.qw, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
    smul_eq_mul]

/-- The `qw` of `allNumOp` is the sum of the `qw` of the `nOp`. -/
theorem qw_allNumOp (F : FockData Mode) (Ψ : F.H) :
    F.qw Ψ F.allNumOp = ∑ k : Mode, F.qw Ψ (F.nOp k) := by
  have h : F.allNumOp = ∑ k : Mode, (1 : ℝ) • F.nOp k := by
    simp [allNumOp]
  rw [h, qw_sum_all]
  simp

/-- `allNumOp` is nonnegative as a quadratic form. -/
theorem allNumOp_qw_nonneg (F : FockData Mode) (Ψ : F.H) : 0 ≤ F.qw Ψ F.allNumOp := by
  rw [qw_allNumOp]
  exact Finset.sum_nonneg fun k _ => nOp_qw_nonneg' F k Ψ

end Work.BoseB7.FockData

namespace Work.BoseB7A.TildeData

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : Work.BoseB7.FockData Mode} (T : TildeData F)

/-- The gap word expanded: `⟨gapOpT⟩ = ℓ⁻²⟨N⟩ + ε_T(dℓ)⁻²⟨NH⟩`. -/
theorem qw_gapOpT (E : Q3Env Mode) (Ψ : F.H) :
    F.qw Ψ (T.gapOpT E)
      = E.ell ^ (-(2 : ℝ)) * F.qw Ψ T.N
        + (E.eT * (E.d * E.ell) ^ (-(2 : ℝ))) * F.qw Ψ T.NH := by
  rw [Work.BoseB7A.TildeData.gapOpT, Work.BoseB7.FockData.qw_add,
    Work.BoseB7.FockData.qw_smul, Work.BoseB7.FockData.qw_smul]

end Work.BoseB7A.TildeData

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-! ## 1. The three conditions at a fixed `ε` -/

/-- **FS l.3253 at a fixed `ε`**: the localised `Σ_jQ_{L,j}χ_Λ²Q_{L,j}` (the
corpus's `Gop`) against the total χ-mode number `Σ_k a_k†a_k` and FS's
`Cε^{-1}n₊^H`.  (`n₊^H` is the honest `T.NH`; FS's own correction is the physical
`1_{(d^{-2}ℓ^{-1},∞)}(√-Δ)` number, and the honest `NH` is a *lower* form of it,
so using `NH` makes the row weaker — and it is what the `ε_T(dℓ)⁻²` gap pays.) -/
def GchiAt {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (Cχ : ℝ) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (ε : ℝ) : Prop :=
  ∀ Ψ : (Work.BoseRowsFS.honF v h fc fu HM μ).H,
    (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
        ((Work.BoseRowsFS.honT v h fc fu HM μ).Gop (Work.BoseRowsFS.honE v h fc fu HM μ))
      ≤ (1 + ε) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
        + (Cχ / ε) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            (Work.BoseRowsFS.honT v h fc fu HM μ).NH

/-- **FS l.3240–3262 at a fixed `ε`**: the `Q₂^ex` comparison, against the
*corrected* `Q2exAll` and with the reserve split in halves. -/
def MainAt {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (HM : ∀ μ : ℝ, HonestModes v μ) (μ ρ ε : ℝ) : Prop :=
  ∀ Ψ : (Work.BoseRowsFS.honF v h fc fu HM μ).H,
    2 * ρ * (1 + ε) * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
        * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
            (Work.BoseRowsFS.honF v h fc fu HM μ).allNumOp
      ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
          ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
            (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
        + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(2 : ℝ))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).N
        + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
            * ((Work.BoseRowsFS.honE v h fc fu HM μ).eT
                * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                    * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ)))
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                (Work.BoseRowsFS.honT v h fc fu HM μ).NH

/-- **The arithmetic at a fixed `ε`**: the `Cχ/ε` correction of FS l.3253 is paid
out of half of the `ε_T(dℓ)⁻²n₊^H` gap.  At the honest parameters
`ε_T^{-1}(dK_ℓ)²·(dℓ)² = (μa³)^{-13/1292}` makes this a comparison of *identical*
`(μa³)`-powers, i.e. an absolute condition on `ε`, independent of `μ`. -/
def ArithAt {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (Cχ : ℝ) (HM : ∀ μ : ℝ, HonestModes v μ) (μ ρ ε : ℝ) : Prop :=
  2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 * (Cχ / ε)
    ≤ ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 800)
        * (Work.BoseRowsFS.honE v h fc fu HM μ).eT
        * ((Work.BoseRowsFS.honE v h fc fu HM μ).d
            * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ^ (-(2 : ℝ))

/-! ## 2. The primary target and its three composable rows

FS l.3240–3262 uses **one and the same** `ε` for three conditions, so the honest
statement is the joint one: one absolute `Cχ`, one cube-size function `Ng` and one
*function* `ε : ℝ → ℝ` (chosen from the data — FS choose `ε ∝ ε_T^{-1}(dK_ℓ)²`),
with all three conditions of §1 at `ε μ`.  The three rows
`RowArith`/`RowGchi`/`RowMain` are that statement split by condition; they are
composable (`RowQ2AllCoreAt_of_rows`) because they share `Cχ` and `ε`.

## ⚠ The cube-size row is *not* optional

`GchiAt` compares `Gop` (whose diagonal is `χ̂²(0) = 1`) with
`Σ_{k ∈ LabN} a_k†a_k`, the **truncated** frame sum.  The continuum identity
`Σ_{k ∈ ℤ³}|⟨χ-mode_k, χ_Λ e^{isx}⟩|² = ∫χ² = 1` is only an *inequality* on a
coarser lattice (`Work.BoseK15.sum_hatChi_sq_le`), and the missing Parseval tail
is exactly what `MainAt` cannot pay: at `N = 1` a child of this area produced the
machine-checked counterexample `FINDING_RowQ2AllCore_FALSE.md` (`Φ := ã_s†|vac⟩`
at the label `s` with `labVec 1 s = (-1,-1,-1)`: `⟨Gop⟩ = 1` while
`Σ_k⟨a_k†a_k⟩ = 0.5633`, forcing `ε μ ≥ 0.775`, against `MainAt`'s
`ε μ → 0`).  Hence every row below carries the cube-size hypothesis
`∀ μ, Ng μ ≤ (HM μ).N`, exactly as `RowIntOneRegimeN` and `RowSumW1sq_regime` do.

## ⚠ The diluteness threshold must be *produced*, not assumed

The three conditions have a **two-sided `ε`-window** for each datum:

* `ArithAt` needs `ε ≥ 1600 Cχ ρŴ₁ω(0)/(b μa)`,
* `MainAt` needs `ε ≤ (b/400)ℓ⁻²⟨n₊⟩/(2ρŴ₁ω(0)⟨Σ_k a_k†a_k⟩)`.

With `ρ ≍ μ`, `Ŵ₁ω(0) ≍ 8πa`, `⟨Σ_k a_k†a_k⟩/⟨n₊⟩ ≲ 48/π` and
`ℓ⁻² = μa·(μa³)^{3/323}`, the window is
`[C₁(μa³)^{13/1292}, C₂(μa³)^{12/1292}]` with `C₁/C₂ ≈ 5·10^{13}`
(script `_num/window.py`), so it is nonempty **only for
`μa³ ≲ (C₂/C₁)^{1292} ≈ 10^{-17684}`**.  Hence `RowQ2AllCoreAt R εg Ng` (the core
at a *given* threshold) is **false** at the gate's (or any `O(1)`) threshold, and
the row must produce its own threshold — exactly as
`Work.BoseRowsFS.RowIntOneRegime_honest` does (`∃ ε₀ ≤ εg`).  `RowQ2AllCore R εg Ng`
below is that statement: `∃ εg' ∈ (0, εg]` at which the core holds.  (This is
inherent to FS's own argument — their conditions are all of the form `f ≪ g`, i.e.
`f ≤ C(μa³)^{ε₀}g`, and composing them shrinks the threshold to a power; it is not
an artefact of the formalisation.) -/

/-- The arithmetic row, at a *given* `Cχ` and `ε : ℝ → ℝ`. -/
def RowArith {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) (Cχ : ℝ) (ε : ℝ → ℝ) : Prop :=
  εg ≤ 1 →
    ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ : ℝ) (hμ : 0 < μ), μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
        ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
          ArithAt (v := v) (h := h) (fc := fc) (fu := fu) Cχ HM μ ρ (ε μ)

/-- FS l.3253 (the `ε`-row), at a *given* `Cχ` and `ε : ℝ → ℝ`. -/
def RowGchi {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) (Cχ : ℝ) (ε : ℝ → ℝ) : Prop :=
  εg ≤ 1 →
    ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ : ℝ) (hμ : 0 < μ), μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
        ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
          GchiAt (v := v) (h := h) (fc := fc) (fu := fu) Cχ HM μ (ε μ)

/-- FS l.3240–3262 (the `Q₂^ex` row), at a *given* `ε : ℝ → ℝ`. -/
def RowMain {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) (ε : ℝ → ℝ) : Prop :=
  εg ≤ 1 →
    ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ : ℝ) (hμ : 0 < μ), μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
        ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
          MainAt (v := v) (h := h) (fc := fc) (fu := fu) HM μ ρ (ε μ)

/-- **The core of the corrected row 3 at a *given* threshold and cube size.**  One
absolute constant `Cχ ≥ 0` and one function `ε : ℝ → ℝ` (positive on `μ > 0`), at
which all three conditions of §1 hold at every honest datum of the dilute régime
with `Ng μ ≤ (HM μ).N`, and every admissible `ρ`.  Use `RowQ2AllCore` (which
produces its own threshold): by §2 this is false at any `O(1)` `εg`. -/
def RowQ2AllCoreAt {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) (Ng : ℝ → ℕ) : Prop :=
  ∃ Cχ : ℝ, ∃ ε : ℝ → ℝ, 0 ≤ Cχ ∧ (∀ μ : ℝ, 0 < μ → 0 < ε μ) ∧
    RowArith (h := h) (fc := fc) (fu := fu) R εg Ng Cχ ε ∧
    RowGchi (h := h) (fc := fc) (fu := fu) R εg Ng Cχ ε ∧
    RowMain (h := h) (fc := fc) (fu := fu) R εg Ng ε

/-- **The core of the corrected row 3, producing its own cube size *and* its own
diluteness threshold.**  There are a cube-size function `Ng` and `εg' ∈ (0, εg]`
at which `RowQ2AllCoreAt R εg' Ng` holds.

Both quantifiers are essential and *existential*: `Ng` must be *produced* (a free
`Ng` could be `≡ 1`, and then the truncated frame sum of `GchiAt` is off by the
Parseval tail — `FINDING_RowQ2AllCore_FALSE.md`), and the threshold must be
*produced* (the two-sided `ε`-window of §2 is nonempty only for
`μa³ ≲ 10^{-17684}`, so the row at a given `O(1)` `εg` is false). -/
def RowQ2AllCore {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (R εg : ℝ) : Prop :=
  ∃ Ng : ℝ → ℕ, ∃ εg' : ℝ, 0 < εg' ∧ εg' ≤ εg ∧
    RowQ2AllCoreAt (h := h) (fc := fc) (fu := fu) R εg' Ng

/-- **The three rows at a common `(Cχ, ε)` give the core at that threshold.** -/
theorem RowQ2AllCoreAt_of_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {R εg : ℝ} {Ng : ℝ → ℕ}
    (hrows : ∃ Cχ : ℝ, ∃ ε : ℝ → ℝ, 0 ≤ Cχ ∧ (∀ μ : ℝ, 0 < μ → 0 < ε μ) ∧
      RowArith (h := h) (fc := fc) (fu := fu) R εg Ng Cχ ε ∧
      RowGchi (h := h) (fc := fc) (fu := fu) R εg Ng Cχ ε ∧
      RowMain (h := h) (fc := fc) (fu := fu) R εg Ng ε) :
    RowQ2AllCoreAt (h := h) (fc := fc) (fu := fu) R εg Ng :=
  hrows

/-- The same, up to the threshold: a core at some cube size and `εg' ≤ εg` gives
`RowQ2AllCore R εg`. -/
theorem RowQ2AllCore_of_coreAt {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {R εg εg' : ℝ} {Ng : ℝ → ℕ} (h0 : 0 < εg') (hle : εg' ≤ εg)
    (hcore : RowQ2AllCoreAt (h := h) (fc := fc) (fu := fu) R εg' Ng) :
    RowQ2AllCore (h := h) (fc := fc) (fu := fu) R εg :=
  ⟨Ng, εg', h0, hle, hcore⟩

/-! ## 4. The label-`0` reserve row (for the gate variant) -/

/-- **The label-`0` reserve row — ⛔ RETIRED** (lead's ruling 2026-10-07 17:20).

*Retired with `GateAll.lean`.*  The `All` gate
(`Work.BoseBoxFock.HonestGateFSAll`, `BOSE_ALL_DESIGN.md` item 6) carries the
reserve `½⟨dNumOpR (RHi ∧ ¬PHq)⟩` inside its own `Q3KernelFSAll.q2exLowerR` field
and consumes `RowQ2AllRegimeN` directly, so no separate reserve obligation is
needed.  The definition is kept only because files are never deleted here.

--- The gate's reserved row carries the free term
`(1/2)⟨dNumOpR (rHi ∖ P_H^q)⟩`; for the *corrected* row `RowQ2All` to feed the
gate's `q2exLowerR` slot one needs precisely that this reserve dominates the
label-`0` correction `2ρŴ₁ω(0)⟨n₀⟩` which `Q2exAll` adds.  This is the one extra
obligation of the gate variant `exists_honestGateFS_of_honestInterface_all`
(`GateAll.lean`); see `NOTES.md` §A.4 for its size. -/
def RowReserveLabelZero {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} (R εg : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
    ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
      ∀ Ψ : (Work.BoseRowsFS.honF v h fc fu HM μ).H,
        2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).nOp 0)
          ≤ (1 / 2) * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).dNumOpR
                (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
                (fun k => rHi (Work.BoseRowsFS.honF v h fc fu HM μ)
                    (Work.BoseRowsFS.honE v h fc fu HM μ) k
                  ∧ ¬ (Work.BoseRowsFS.honF v h fc fu HM μ).PHq
                      (Work.BoseRowsFS.honE v h fc fu HM μ).KH
                      (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k))

end Work.BoseRowQ2
