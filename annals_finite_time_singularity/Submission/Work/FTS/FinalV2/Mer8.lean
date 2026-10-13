import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.FinalV2.Producers
import Submission.Work.FTS.Final.MeridianRed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.FinalV2.Mer8` — (8′) producer, PROVED modulo its three research-free feeds
(`sol_fire`, `psiCan_C3`, `profDerivData_min` in `FinalV2.Producers`). curric-46 lead install,
2026-10-10, from `cbc/fts_final_redesign.lean`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.FinalV2

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Physical (PhysClock)
open Work.FTS.Final
open Work.FTS.FinalClock
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG)

set_option autoImplicit false

variable {C₀ Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **(8′) producer, PROVED modulo the research-free lemmas above** (`sol_fire`, `psiCan_C3`,
`profDerivData_min`): the existing `hMer_of_dyn` at `(Φ, g) := (psiFire Φs E g, extG g)`. -/
theorem mer8' {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3) (hEL : EllLimOK3 (pExp a) E)
    (hStar : StarPkgo2 (pExp a) Cs Φs) {g : Fam} {A B : ℝ → ℝ} {C : PhysClock}
    (hSol : Sol (pExp a) Φs E g) (hOK : DynOK' (pExp a) C₀ Φs E g)
    (hClock : ClockData (pExp a) (PsiCan Φs E g) g A B C) :
    MeridianEqOn (Work.FTS.Physical.merProfile a A B (extG g) C)
      (Work.FTS.MeridianDyn.merPsi (pExp a) A B (psiFire Φs E g) C) C.T := by
  have haG : 0 < pExp a := Work.FTS.Regularity.pExp_pos ha
  obtain ⟨hSolF, hmu⟩ := sol_fire hSol
  have hC3 := psiCan_C3 hEL hStar hOK
  have hΦ : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => psiFire Φs E g q.1 q.2 τ) Work.Construction.Qd := by
    intro τ hτ
    exact ((hC3 τ hτ.le).of_le (by norm_num)).congr (fun q hq => psiFire_of_pos hq.2.1)
  have hmin := (Work.FTS.Final.ExtG.dynOK_extG haG hOK.1).1
  exact hMer_of_dyn ha ha13 hSolF hmin hΦ (fun τ _ Z Θ => psiFire_odd Φs E g Z Θ τ)
    (profDerivData_min hmin hΦ)
    ⟨fun τ hτ => (hClock.1 τ hτ).trans (hmu τ hτ).symm, hClock.2.1, hClock.2.2.1,
      hClock.2.2.2.1, hClock.2.2.2.2⟩

end Work.FTS.FinalV2
