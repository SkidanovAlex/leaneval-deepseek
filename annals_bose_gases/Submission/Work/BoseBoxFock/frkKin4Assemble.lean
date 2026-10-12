import ChallengeDeps
import Submission.Work.BoseBoxFock.FRK.FormRowKin_holds_of_leaves
import Submission.Work.BoseBoxFock.FRK.etaHRow_window_v2
import Submission.Work.BoseBoxFock.FRK.tauRow_window_of_valid_W3
import Submission.Work.BoseBoxFock.FRK.windowHigh_le
import Submission.Work.BoseBoxFock.frkD4
import Submission.Work.BoseBoxFock.tauSm_admissible
import Submission.Work.BoseBoxFock.windowAlias_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FormRowKin4_holds_assembled` — the kinetic row at the **strong** reserve

The BF3c v2 design (`Work.BoseBoxFock.frkCore`, "PART B — the reserve transfer") runs the whole
row comparison at the **strong** kinetic reserve `(b/4 − b/100)·ℓ⁻²cnPlus` (the definition
`FRK.FormRowKin4`) and credits the potential side with the transferred amount
`γ = b/4 − b/100` (`FRK.FormW2BpotG`, `FRK.PotCubicG`).  The two credits cancel in
`FRK.RowB_of_kin4_potG`, so the assembly produces the frozen `RowB`.

This module supplies the **kinetic half of that route**: `∃ ε₀ C, FormRowKin4 … ε₀ C`.  Every
ingredient is already proved:

* the dictionary D4 `FRK.FormRowKin4_of_oneBody4` (`frkD4.lean`, PROVED) — it consumes the
  per-fibre one-body inequality `FRK.OBineq4` at the honest parameters and produces `FormRowKin4`
  with constant `C = 0` (`errKafz v R μ 0 = 0`; the whole kinetic allowance is the reserve);
* the two one-body rows: the `τ̃` row `FRK.tauRow_window_of_valid_W3` at `W3 = windowAlias_le`,
  `W4 = tauSm_admissible` (PROVED), and the `η_H` row `FRK.etaHRow_window_v2` at
  `S1 = FRK.windowHigh_le`, `W3 = windowAlias_le`, majorant `FRK.etaH_majorant_exists` (PROVED);
* `FRK.oneBody4_at_honest` (`FRK/FormRowKin_holds_of_leaves.lean`, PROVED), which converts the two
  rows into `OBineq4` at the honest parameters with the threshold `ε₀ = s₀³²³`.

Note that **S1 is not needed** for `FormRowKin4`: it enters only through the `η_H` row.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- **`FormRowKin4` from the per-fibre one-body inequality** `FRK.OBineq4` at the honest
parameters (the dictionary D4 at the constant `C = 0`). -/
theorem FormRowKin4_of_OB (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ) (Nmin : ℝ → ℕ)
    (hOB : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (N : ℕ) (ψ : Ω → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      FRK.OBineq4 (Work.BoseBox.sideAt μ (BoseGases.a v))
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).b (FRK.kappaHon v μ) fu N ψ) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ FRK.FormRowKin4 v h fc fu R J Nmin ε₀ C := by
  obtain ⟨ε₀, hε₀, hOB'⟩ := hOB
  exact ⟨ε₀, 0, hε₀, le_refl 0, FRK.FormRowKin4_of_oneBody4 v h fc fu R J Nmin ε₀ hOB'⟩

/-- **The kinetic half of the BF3c v2 row table, proved** — `FormRowKin4` (the strong reserve) at
every mode family and every lattice cut-off, with the explicit threshold `ε₀ = s₀³²³` and constant
`C = 0`. -/
theorem FormRowKin4_holds_assembled (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (R J : ℝ) (Nmin : ℝ → ℕ) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧ FRK.FormRowKin4 v h fc fu R J Nmin ε₀ C :=
  FormRowKin4_of_OB v h fc fu R J Nmin
    (FRK.oneBody4_at_honest v hav fc fu
      (FRK.tauRow_window_of_valid_W3 windowAlias_le tauSm_admissible)
      (FRK.etaHRow_window_v2 FRK.windowHigh_le windowAlias_le FRK.etaH_majorant_exists))

end Work.BoseBoxFock
