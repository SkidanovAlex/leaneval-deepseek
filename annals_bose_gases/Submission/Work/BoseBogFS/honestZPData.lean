import ChallengeDeps
import Submission.Work.BoseBogFS.honestZPBricks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honestZPData` — the honest `FsBogData` of the zero-point slot

`FINDING_honestZP_design.md` §1: the honest `FsBogData n` at
`D μ = Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ`, with the mesh size `honestN`,
the affine kernel `honestK`, `chiM = 1`, `δ = 0` and the localisation `honestXh`.  All the
data comes from `Work.BoseBogFS.honestZPDefs`; the two rows are
`Work.BoseBogFS.honestXh_supp` and `Work.BoseBogFS.honestChiNorm`
(the shifted-cube Parseval row `Work.BoseBogFS.sum_hatChi_shifted_cube_le`).

It is consumed by the honest `FsMatchEnv` assembly (`FINDING_honestZP_design.md` §1–§2).
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

/-- **The honest `FsBogData`.**  `R` is the support radius of `v`, `ρ` the density, `N` the box's
lattice size `(HM μ).N` (which enters only through the kernel cutoff `honestZPT`). -/
def honestD (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ ρ : ℝ) (N : ℕ)
    (hη : 0 ≤ honestZPη v R ρ) (hT : 0 ≤ honestZPT v μ ρ N)
    (hℓ3 : 3 ≤ (Work.BoseFixR.ell v μ) ^ 3)
    (hcube : (∑ k : Fin 3 → Fin (Work.BoseB6.gridD (honestN v μ ρ)),
        (Work.BoseK15.corpusBox.hatChi
          ((1 / 2 : ℝ) • Work.BoseB4.vec
            (fun i : Fin 3 =>
              2 * (k i : ℤ) - (Work.BoseB6.gridD (honestN v μ ρ) : ℤ)))) ^ 2)
      ≤ 1) : Work.BoseB6Est.FsBogData (honestN v μ ρ) :=
  { K := honestK v R μ ρ N hη hT
    a := a v
    R := R
    ρz := ρ
    ℓ := Work.BoseFixR.ell v μ
    μ := μ
    z := Real.sqrt (ρ * Work.BoseFixR.ell v μ ^ 3)
    chiM := 1
    δ := 0
    εT := (paramsAt μ (a v)).eT
    c1 := (2 * (paramsAt μ (a v)).s * Work.BoseFixR.ell v μ)⁻¹ / Real.sqrt (ρ * a v)
    c2 := (2 * (paramsAt μ (a v)).d * (paramsAt μ (a v)).s * Work.BoseFixR.ell v μ)⁻¹
      / Real.sqrt (ρ * a v)
    Kl := (paramsAt μ (a v)).Kl
    s := (paramsAt μ (a v)).s
    d := (paramsAt μ (a v)).d
    -- `c₁, c₂` are the kinetic thresholds in the **`t`-units** of `modePos`/`fsA`:
    -- `c₁ = (2sℓ)⁻¹/√(ρ_z a)`, exactly as `Work.BoseBogFS.hA_env_of_rows` states them.
    χh := honestXh v μ ρ N (honestK v R μ ρ N hη hT)
    hχsupp := by
      intro t ht
      exact honestXh_supp v μ ρ N _ (by rw [honestK_T v R μ ρ N hη hT] at ht ⊢; exact ht)
    hchiM := by norm_num
    hδ := le_rfl
    hχnorm := honestChiNorm v μ ρ N (honestK v R μ ρ N hη hT)
      (honestK_T v R μ ρ N hη hT) hcube
    hℓ3 := hℓ3 }

end Work.BoseBogFS
