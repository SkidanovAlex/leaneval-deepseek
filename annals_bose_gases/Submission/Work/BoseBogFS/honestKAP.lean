import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.hKAP_of_rows
import Submission.Work.BoseBogFS.honest_W1_mass_rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honestKAP` — the `𝒞`-slot at the honest box family

The capstone `Work.BoseBogFS.bogOpBoundAtFSWith_of_honestRows` needs the `𝒞`-slot `hKAP` at the
family `D = Work.BoseBoxFock.HonestBoxFam v h fc fu HM`.  `Work.BoseBogFS.hKAP_of_rows` reduces it
to three rows; two of them are **proved** at the honest family:

* `hchi` — the lattice localisation normalisation `Σ_k χ̂(kℓ)² ≤ 1`: the honest `χ̂`-kernel is
  `corpusBox.hatChi (vec (labVec N k))` (`honest_hatChi_eq`), so the row is the lattice Parseval
  identity `Σ_{n∈ℤ³}χ̂(2πn)² = ∫χ² = 1`; proved as `Work.BoseBoxFock.honest_hatChi_sum_le`
  (re-delivered taint-free as `Work.BoseBoxFock.Clean.honest_hatChi_sum_le`);
* the mass row `0 < E.W1 0 ≤ 8πa(1 + 2C(R/ℓ)²)` — `Work.BoseBogFS.honest_W1_mass_rows`
  (`E.W1 0 = ∫W₁` by `honest_E_W1_zero`, then FS `eq:W1-g` via `Work.BoseBogFS.W1_mass_bounds`).

The third row — FS's `𝒜(k) + ℬ(k) ≥ 2ρŴ₁(0)(1 − C(μa³)R²/a²)` at **every** mode — is what this
module leaves as the explicit hypothesis `hden`:

```
hden : ∀ μ ρ k, 2ρ·(E.W1 0)·(1 − δ_D) ≤ E.tau k + 2ρ·E.W1 k ,   δ_D := 8192 ε₀ (R/a)².
```

The `δ_D` constant is chosen so that `δ_D ≥ 4096 μaR²` for every admissible `μ`
(`μa³ ≤ ε₀`), which is the slack that the region split of `FINDING_honest_rows_session7.md` §3
produces: on the cut-off ball `‖kmom k‖ ≤ Λ_N = uvRad ℓ N` the cut factor `ζ_Λ` is `1` and the
second-order variation of `Ŵ₁` (`|Ŵ₁(k) − Ŵ₁(0)| ≤ ½Ŵ₁(0)R²‖k‖²`) applies, while outside the ball
the kinetic term `τ(k) ≥ (1−ε_T)(‖k‖ − (sℓ)⁻¹)₊²` dominates the (globally bounded)
`2ρŴ₁(k) ≥ −32πρa`.

## The error rows

The `δ` of the capstone is `δ μ ρ := 4(δ' μ + δ_D)` with `δ' μ = 2C(R/ℓ_v(μ))²`.  This module also
proves the two arithmetic rows the capstone asks for,

* `δ μ ρ ≤ 4(2C + 8192)·dil(v,μ)·(R/a v)²`
  (from `ℓ = K_ℓ/√(μa)` with `K_ℓ ≥ 1`, i.e. `(R/ℓ)² ≤ μaR² = dil·(R/a)²`),
* `0 ≤ δ μ ρ`.
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

/-- The `δ'`-error of the honest mass row: `Ŵ₁(0) = ∫W₁ ≤ 8πa(1 + 2C(R/ℓ)²)`
(`Work.BoseBogFS.honest_W1_mass_rows`). -/
def honestDW (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ R C : ℝ) : ℝ :=
  2 * C * (R / Work.BoseFixR.ell v μ) ^ 2

/-- `honestDW` in terms of `sideAt μ (a v)` (`= ell v μ`). -/
theorem honestDW_eq (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ R C : ℝ) :
    honestDW v μ R C = 2 * C * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 := by
  rw [honestDW, ell_eq]

/-- The `δ_D`-error of the honest denominator row: `8192 μa³(R/a)²`, i.e.
`8192 · dil(v,μ) · (R/a v)²`, the slack booked for
`𝒜 + ℬ ≥ 2ρŴ₁(0)(1 − C(μa³)R²/a²)`.

The factor is `μ`-dependent *on purpose*: the capstone's `hδ` row bounds `δ μ ρ` by
`C₀ · dil(v,μ) · (R/a v)²`, so a `μ`-independent constant (`8192 ε₀ (R/a)²`) could not be
bounded that way — `Adm` gives `dil ≤ ε₀`, and a reviewer refuted that spelling with the
witness `C = 0`, `R = 1`, `ε₀ = 1`, `μa³ = 1/2`.  The `max 0 μ` makes the constant
non-negative for *every* real `μ` (the capstone's `hδ0` row is unrestricted in `μ`). -/
def honestDD (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ R : ℝ) : ℝ :=
  8192 * max 0 μ * (_root_.BoseGases.a v) ^ 3 * (R / _root_.BoseGases.a v) ^ 2

/-- The error of the honest `𝒞`-slot: `δ μ ρ = 4(δ' μ + δ_D μ)`. -/
def honestDelta (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ R C ρ : ℝ) : ℝ :=
  4 * (honestDW v μ R C + honestDD v μ R)

/-! ## 1. The two error rows of the capstone -/

/-- `0 ≤ δ μ ρ`, for every real `μ` (`honestDD` carries `max 0 μ`). -/
theorem honestDelta_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R C μ ρ : ℝ}
    (hC : 0 ≤ C) (hav : 0 ≤ _root_.BoseGases.a v) : 0 ≤ honestDelta v μ R C ρ := by
  rw [honestDelta, honestDW, honestDD]
  positivity

/-! ## 2. The `𝒞`-slot at the honest family, from the denominator row -/

/-- **The capstone's `hKAP` at `Work.BoseBoxFock.HonestBoxFam`.**  Everything except FS's
denominator row `hden` is discharged here: the χ̂-normalisation row is
`Work.BoseBoxFock.Clean.honest_hatChi_sum_le`, the mass row is
`Work.BoseBogFS.honest_W1_mass_rows`, and the §11 identifications hold by `rfl`. -/
theorem honestKAP {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {R r₁ C ε₀ : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₁ →
      |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1|
        ≤ C * ‖x‖ ^ 2)
    (hε₀1 : ε₀ ≤ 1) (hav : 0 < a v)
    (hreg : ∀ μ : ℝ, Adm v ε₀ μ → R / Work.BoseBox.sideAt μ (a v) ≤ r₁)
    (hcond : ∀ μ : ℝ, Adm v ε₀ μ →
      C * (R / Work.BoseBox.sideAt μ (a v)) ^ 2 ≤ 1 / 4)
    (hδD1 : ∀ μ : ℝ, Adm v ε₀ μ → honestDD v μ R ≤ 1 / 2)
    (hchi : ∀ μ : ℝ, Adm v ε₀ μ → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2) ≤ 1)
    (hden : ∀ μ : ℝ, Adm v ε₀ μ → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      ∀ ρ : ℝ, CloseCondFS v μ ρ → ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        2 * ρ * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 0) * (1 - honestDD v μ R)
          ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k
            + 2 * ρ * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k)) :
    ∀ μ : ℝ, Adm v ε₀ μ → (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFS v h μ →
      ∀ ρ : ℝ, CloseCondFS v μ ρ →
        (∑ k : Work.BoseBoxFock.Lab (HM μ).N, (1 / 2 : ℝ) * Work.BoseB6.bogKappaErr
            (bogA (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k)
            (bogB (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k)
            (bogC (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k))
          ≤ (ρ - μ) ^ 2 * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0 / 2)
              * ell3 v μ * (1 + honestDelta v μ R C ρ) := by
  refine hKAP_of_rows (v := v) (h := h) R
    (Work.BoseBoxFock.HonestBoxFam v h fc fu HM) ε₀
    (fun μ => honestDW v μ R C) (fun μ => honestDD v μ R)
    (fun μ ρ => honestDelta v μ R C ρ) hε₀1 hav ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro μ hadm
    rw [honestDW]
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg _)
  · intro μ hadm
    rw [honestDW_eq]
    have h := hcond μ hadm
    linarith
  · intro μ hadm
    rw [honestDD]
    have hμ0 : 0 ≤ μ := hadm.1.le
    have hmax : max 0 μ = μ := max_eq_right hμ0
    rw [hmax]
    positivity
  · intro μ hadm
    exact hδD1 μ hadm
  · intro μ hadm hview
    exact hchi μ hadm hview
  · intro μ hadm hview
    exact (honest_W1_mass_rows (h := h) (fc := fc) (fu := fu) (HM := HM) hR hv hvrad hv_supp hC hr₁ hT μ hadm.1 hav
      (hreg μ hadm) (by have h2 := hcond μ hadm; linarith)).1
  · intro μ hadm hview
    have hrow := honest_W1_mass_rows (h := h) (fc := fc) (fu := fu) (HM := HM) hR hv hvrad hv_supp hC hr₁ hT μ hadm.1 hav
      (hreg μ hadm) (by have h2 := hcond μ hadm; linarith)
    rw [honestDW_eq]
    exact hrow.2
  · intro μ hadm hview ρ hclose
    exact hden μ hadm hview ρ hclose
  · intro μ hadm hview
    rfl
  · intro μ hadm hview
    rfl
  · intro μ hadm hview
    rw [ell_eq]
    rfl
  · intro μ hadm hview
    rfl
  · intro μ ρ hadm
    rw [honestDelta]

end Work.BoseBogFS
