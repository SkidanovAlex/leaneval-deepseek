import ChallengeDeps
import Submission.Work.BoseBoxFock.exists_honestModes
import Submission.Work.BoseRowsFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.Defs` — the corrected row 3 of the `BoseRowsFS` gate

Row 3 of the honest gate (`Work.BoseRowsFS.RowQ2`, FS §12 `eq:Q3Cancels`) is

    `2 ρ Ŵ₁ω(0) ⟨Ψ, G Ψ⟩ ≤ ⟨Ψ, Q₂^ex Ψ⟩ + (b/400) ⟨Ψ, gapOp Ψ⟩`.

The first-quantised `Q₂^ex` of the corpus (`Work.BoseB7.FockData.Q2ex`) is

    `Q₂^ex = Σ_{k ∈ P_H, k ≠ 0} ρ(Ŵ₁ω(k) + Ŵ₁ω(0)) a_k†a_k`,

i.e. it runs over the *excited* modes only, while FS's `eq:Q3Cancels` and the
operator `Σ_j Q_jχ²Q_j` which is compared with it carry the label `k = 0` (the
vector `Qχ_Λ`) as well.  This module introduces the corrected operator

    `Q2exAll E = Σ_{k} ρ(Ŵ₁ω(k) + Ŵ₁ω(0)) a_k†a_k`   (**all** labels)

together with its basic API, and the two `Prop`s `RowQ2All` /
`RowQ2AllRegime(N)` which are row 3 with `Q2exAll` in place of `Q2ex`, in the
unrestricted and the dilute-regime form (the form in which rows 1 and 2 are
true: `RowSumW1sq_regime`, `RowIntOneRegime_honest`).

The correction is exactly the label-0 term: with `Ŵ₁ω(0) = Ŵ₁ω(0)` read at the
label `0` (which is the honest case, `honE_W1omega_zero`), `Q2exAll` is `Q2ex`
plus `2ρŴ₁ω(0)·n₀`.  Since `Q2exAll ≥ Q2ex`, the corrected row is *weaker* than
the original one — and necessarily so: the original row is **false**
(`NOTES.md`, and the machine-checked reduction in `PartA/`).

This module contains definitions and the operator algebra only; the live assembly of
`RowQ2AllRegimeN` is `RowQ2All_of_coreN` + `rowQ2AllRegimeN_honest`
(see `FINDING_rowQ2AllRegimeN_honest.md`).  The `hGchi`/`hMainChi` rows of the original design are
the retired `RowQ2All_of_rows`/`GateAll` route, and the *sharp* `hGchi` row with the θ-framed
correction is the retired mask route of `MaskRow.lean`.
-/

noncomputable section

open scoped BigOperators Pointwise

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.BoseB7.FockData

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **The corrected `Q₂^ex`** (FS `eq:Q3Cancels`): FS's `Q₂^ex` summed over **all**
mode labels, i.e. `Σ_k ρ(Ŵ₁ω(k) + Ŵ₁ω(0)) a_k†a_k`.  The label `k = 0` (the
vector `Qχ_Λ`) is what `Work.BoseB7.FockData.Q2ex`'s `excited` sum drops; FS's
`eq:Q3Cancels` compares `Σ_j Q_jχ²Q_j` — which does contain it — with
`Q₂^ex`, so the row is only valid for this corrected operator. -/
def Q2exAll (F : FockData Mode) (E : Q3Env Mode) : F.H →ₗ[ℝ] F.H :=
  ∑ k : Mode, (E.rho * (E.W1omega k + E.W1omega0)) • F.nOp k

/-- `⟨Ψ, n_k Ψ⟩ = ⟨a_kΨ, a_kΨ⟩ ≥ 0` for the mode number operator `n_k = a_k†a_k`. -/
theorem nOp_qw_nonneg' (F : FockData Mode) (k : Mode) (Ψ : F.H) : 0 ≤ F.qw Ψ (F.nOp k) := by
  have h : F.qw Ψ (F.nOp k) = F.bp (F.a k Ψ) (F.a k Ψ) := by
    rw [FockData.qw, FockData.nOp, LinearMap.comp_apply]
    exact F.aDag_adjoint k (F.a k Ψ) Ψ
  rw [h]
  exact F.bp_nonneg _

/-- `Q2exAll` is `Q2ex` plus the label-`0` term: the `excited` sum is the whole
sum with the `k = 0` term removed (`Finset.sum_erase_add`). -/
theorem Q2exAll_eq_Q2ex_add (F : FockData Mode) (E : Q3Env Mode) :
    F.Q2ex E + (E.rho * (E.W1omega 0 + E.W1omega0)) • F.nOp 0 = F.Q2exAll E := by
  have h := Finset.sum_erase_add (Finset.univ : Finset Mode)
    (fun k : Mode => (E.rho * (E.W1omega k + E.W1omega0)) • F.nOp k) (Finset.mem_univ 0)
  rw [Q2exAll, Q2ex, Work.BoseB7.excited]
  exact h

/-- The label-`0` term of `Q2exAll`: when the environment's `Ŵ₁ω` at the label
`0` is its value `Ŵ₁ω(0)` (the honest case, `Work.BoseRowQ2.honE_W1omega_zero`),
the correction is `2ρŴ₁ω(0)·n₀`. -/
theorem Q2exAll_eq_Q2ex_add_two (F : FockData Mode) (E : Q3Env Mode)
    (h0 : E.W1omega 0 = E.W1omega0) :
    F.Q2exAll E = F.Q2ex E + (2 * E.rho * E.W1omega0) • F.nOp 0 := by
  have h := F.Q2exAll_eq_Q2ex_add E
  rw [h0] at h
  have hcoef : E.rho * (E.W1omega0 + E.W1omega0) = 2 * E.rho * E.W1omega0 := by ring
  rw [hcoef] at h
  exact h.symm

/-- `Q2exAll` as a sum of `qw`-values. -/
theorem qw_Q2exAll (F : FockData Mode) (E : Q3Env Mode) (Ψ : F.H) :
    F.qw Ψ (F.Q2exAll E)
      = ∑ k : Mode, (E.rho * (E.W1omega k + E.W1omega0)) * F.qw Ψ (F.nOp k) := by
  simp only [Q2exAll, FockData.qw, LinearMap.sum_apply, map_sum, LinearMap.smul_apply,
    map_smul, smul_eq_mul]

/-- `Q2exAll` dominates `Q2ex` as a quadratic form, whenever the label-`0`
coefficient is nonnegative: this is why the corrected row is the *weaker*
statement. -/
theorem Q2ex_qw_le_Q2exAll (F : FockData Mode) (E : Q3Env Mode) (Ψ : F.H)
    (h : 0 ≤ E.rho * (E.W1omega 0 + E.W1omega0)) :
    F.qw Ψ (F.Q2ex E) ≤ F.qw Ψ (F.Q2exAll E) := by
  have h0 := F.Q2exAll_eq_Q2ex_add E
  have hnn : 0 ≤ F.qw Ψ ((E.rho * (E.W1omega 0 + E.W1omega0)) • F.nOp 0) := by
    rw [FockData.qw_smul]
    exact mul_nonneg h (nOp_qw_nonneg' F 0 Ψ)
  calc F.qw Ψ (F.Q2ex E) ≤ F.qw Ψ (F.Q2ex E)
        + F.qw Ψ ((E.rho * (E.W1omega 0 + E.W1omega0)) • F.nOp 0) := le_add_of_nonneg_right hnn
    _ = F.qw Ψ (F.Q2ex E + (E.rho * (E.W1omega 0 + E.W1omega0)) • F.nOp 0) :=
        (FockData.qw_add F Ψ _ _).symm
    _ = F.qw Ψ (F.Q2exAll E) := by rw [h0]

end Work.BoseB7.FockData

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS

/-! ## 1. The honest `Ŵ₁ω` at the label `0` -/

/-- **The honest environment's `Ŵ₁ω` at the label `0` is its value `Ŵ₁ω(0)`**: the
honest `W1omega` is `chat (W1omegaFun v h ℓ) ∘ kmom` and `W1omega0` is the same
`chat` at `0`, while the honest `kmom` at the label `0` is `0`
(`Work.BoseBoxFock.kmomLab_zero`). -/
theorem honE_W1omega_zero (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : ScatSol v)
    (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) :
    (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega 0
      = (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0 := by
  have hkmom : (Work.BoseRowsFS.honF v h fc fu HM μ).kmom 0 = 0 := by
    rw [Work.BoseRowsFS.honF_kmom]
    exact Work.BoseBoxFock.kmomLab_zero (ellH v μ) (HM μ).N
  have h1 : (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega 0
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h
          (Work.BoseBox.sideAt μ (BoseGases.a v)))
          ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom 0) := rfl
  have h2 : (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
      = Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h
          (Work.BoseBox.sideAt μ (BoseGases.a v))) 0 := rfl
  rw [h1, h2, hkmom]

/-! ## 2. The corrected row -/

/-- **Row 3 corrected: FS §12's `eq:Q3Cancels` with `Q2exAll`.**

`2ρŴ₁ω(0)⟨Ψ, G Ψ⟩ ≤ ⟨Ψ, Q₂^ex,all Ψ⟩ + (b/400)⟨Ψ, gapOp Ψ⟩`

at the honest data, for every model vector `Ψ`.  This is `Work.BoseRowsFS.RowQ2`
with the first-quantised `Q₂^ex` replaced by the corrected `Q2exAll` (all labels,
including `k = 0`).  The correction is *necessary*: the unrestricted `RowQ2` is
false. -/
def RowQ2All {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut} (R : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
      ∀ Ψ : (Work.BoseRowsFS.honF v h fc fu HM μ).H,
        2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
            * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honT v h fc fu HM μ).Gop
                  (Work.BoseRowsFS.honE v h fc fu HM μ))
          ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
              ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
                (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
            + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
                * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                    ((Work.BoseRowsFS.honT v h fc fu HM μ).gapOpT
                      (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))

/-- **Row 3 corrected, in the dilute regime** (the form in which rows 1 and 2
are available, and the form the honest gate consumes): the same as `RowQ2All`
but only for `μ a³ ≤ εg`, and at a free cube size `Ng`. -/
def RowQ2AllRegimeN {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    (Ng : ℝ → ℕ) (R εg : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
    ∀ (μ : ℝ), 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
      ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
        ∀ Ψ : (Work.BoseRowsFS.honF v h fc fu HM μ).H,
          2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  ((Work.BoseRowsFS.honT v h fc fu HM μ).Gop
                    (Work.BoseRowsFS.honE v h fc fu HM μ))
            ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
                  (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
              + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
                  * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                      ((Work.BoseRowsFS.honT v h fc fu HM μ).gapOpT
                        (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))

/-- The cube-size-free form of `RowQ2AllRegimeN`. -/
def RowQ2AllRegime {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut} (R εg : ℝ) : Prop :=
  ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
    μ * (_root_.BoseGases.a v) ^ 3 ≤ εg →
      ∀ ρ : ℝ, AdmRho (Work.BoseRowsFS.honE v h fc fu HM μ) ρ →
        ∀ Ψ : (Work.BoseRowsFS.honF v h fc fu HM μ).H,
          2 * ρ * (Work.BoseRowsFS.honE v h fc fu HM μ).W1omega0
              * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                  ((Work.BoseRowsFS.honT v h fc fu HM μ).Gop
                    (Work.BoseRowsFS.honE v h fc fu HM μ))
            ≤ (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                ((Work.BoseRowsFS.honF v h fc fu HM μ).Q2exAll
                  (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))
              + ((Work.BoseRowsFS.honE v h fc fu HM μ).b / 400)
                  * (Work.BoseRowsFS.honF v h fc fu HM μ).qw Ψ
                      ((Work.BoseRowsFS.honT v h fc fu HM μ).gapOpT
                        (KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ))

/-! ## 3. The corrected row is weaker than the original

`Q2exAll ≥ Q2ex` (`Q2ex_qw_le_Q2exAll`), so `RowQ2` implies `RowQ2All`.  The
converse is *false*: the label-`0` term is exactly what the original row cannot
afford (`NOTES.md`, `PartA/`). -/

/-- Row 3 in the restricted form the gate consumes (`RowQ2AllRegimeN`) is
equivalent to `RowQ2AllRegime` when the cube-size row is vacuous. -/
theorem rowQ2AllRegime_of_regimeN {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v} {fc fu : LowCut}
    {Ng : ℝ → ℕ} {R εg : ℝ} (hrow : RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu) Ng R εg)
    (hNg : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), Ng μ ≤ (HM μ).N) :
    RowQ2AllRegime (h := h) (fc := fc) (fu := fu) R εg :=
  fun HM μ hμ hε ρ hρ Ψ => hrow HM (fun μ => hNg HM μ) μ hμ hε ρ hρ Ψ

/-- **The corrected row 3 is monotone in the cube size and in the diluteness
threshold** — the `Ng`/`εg` analogue of `GateThresholds.mono`, needed by any caller
that has to *move* the gate's threshold and cube size so that the row (which
produces its own, `Rows.lean`'s `RowQ2AllCore`) applies: enlarging `εg` makes the
row stronger (`μ` ranges over more values), so it transports downwards; the
cube-size row `∀ μ, Ng μ ≤ (HM μ).N` is a *hypothesis* restricting `HM`, so the
row transports *upwards* in `Ng` (a larger `Ng` excludes `HM`s). -/
theorem RowQ2AllRegimeN_mono {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : ScatSol v}
    {fc fu : LowCut} {Ng Ng' : ℝ → ℕ} {R εg εg' : ℝ}
    (hrow : RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu) Ng R εg)
    (hNg : ∀ μ : ℝ, Ng μ ≤ Ng' μ) (hεg : εg' ≤ εg) :
    RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu) Ng' R εg' :=
  fun HM hN μ hμ hε ρ hρ Ψ =>
    hrow HM (fun μ => le_trans (hNg μ) (hN μ)) μ hμ (le_trans hε hεg) ρ hρ Ψ

end Work.BoseRowQ2
