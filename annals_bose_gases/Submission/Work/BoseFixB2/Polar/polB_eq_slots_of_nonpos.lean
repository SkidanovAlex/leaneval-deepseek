import ChallengeDeps
import Submission.Work.BoseFixB2.Polar.wordB_box_local
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Polar.polB_eq_slots_of_nonpos`

**The degenerate side length.**  When FS's box side collapses,
`fsSide v μ = sideAt μ (a v) ≤ 0`, the centred configuration box `abox n (fsSide v μ)`
is a null set (`abox_volume_eq_zero_of_one_le_of_nonpos`).  Consequently

* the box word vanishes identically, `wordB v h μ n X = 0`
  (`boxFormB_eq_zero_of_nonpos`), so the polarised word `polB` — a linear combination of
  two box words — is `0`;
* each slot kinetic form `kinBilFS v μ i Φ Ψ = (fsSide v μ)⁻³ ∫_{abox n ℓ} …` is `0`
  (empty sum when `n = 0`, null box otherwise), and the potential form
  `potBil n v (g0 v h) (fsSide v μ) μ Φ Ψ = ∫_{abox n ℓ} Φ Ψ · potWordU …` is `0` as
  well (`potWordU 0 … = 0` in the `n = 0` case, where the box is the whole space).

Hence the `lem:LocMatrices` slot decomposition of `polB` — which in general requires
smoothness of the states and integrability of the potential word — holds **trivially**
for `fsSide v μ ≤ 0`, with no hypotheses on `Φ`, `Ψ`.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory

namespace Work.BoseFixB2.Polar

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.UBBInputs3

theorem polB_eq_slots_of_nonpos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {Φ Ψ : Submission.BoseGases.X n → ℝ} (hside : Work.BoseFixB2.fsSide v μ ≤ 0) : Work.BoseFixB2.polB v h μ n Φ Ψ = (∑ i : Fin n, Work.BoseFixB2.kinBilFS v μ i Φ Ψ) + Work.BoseFixB2.potBil n v (Submission.BoseGases.g0 v h) (Work.BoseFixB2.fsSide v μ) μ Φ Ψ := by
  -- the box word vanishes on the degenerate box, hence so does `polB`
  have hword : ∀ X : X n → ℝ, Work.BoseBoxFix.wordB v h μ n X = 0 := by
    intro X
    rw [Work.BoseBoxFix.wordB]
    exact Work.BoseFixB2.Polar.boxFormB_eq_zero_of_nonpos hside X
  have hpol : Work.BoseFixB2.polB v h μ n Φ Ψ = 0 := by
    simp only [Work.BoseFixB2.polB]
    rw [hword (fun x => Φ x + Ψ x), hword (fun x => Φ x - Ψ x)]
    norm_num
  rw [hpol]
  -- every slot kinetic form vanishes: the box is a null set
  have hkinzero : (∑ i : Fin n, Work.BoseFixB2.kinBilFS v μ i Φ Ψ) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have hn : 1 ≤ n := by have := i.isLt; omega
    have hvol := Work.BoseFixB2.Polar.abox_volume_eq_zero_of_one_le_of_nonpos n hn
      (Work.BoseFixB2.fsSide v μ) hside
    simp only [Work.BoseFixB2.kinBilFS, Work.BoseFixB2.kinBil]
    rw [MeasureTheory.setIntegral_measure_zero _ hvol, mul_zero]
  -- the potential form vanishes as well (`potWordU 0 … = 0` in the empty case)
  have hpotzero : Work.BoseFixB2.potBil n v (Submission.BoseGases.g0 v h)
      (Work.BoseFixB2.fsSide v μ) μ Φ Ψ = 0 := by
    cases n with
    | zero => simp [Work.BoseFixB2.potBil, Work.BoseKinLoc.potWordU]
    | succ m =>
        have hvol := Work.BoseFixB2.Polar.abox_volume_eq_zero_of_one_le_of_nonpos (m + 1)
          (Nat.le_add_left 1 m) (Work.BoseFixB2.fsSide v μ) hside
        simp only [Work.BoseFixB2.potBil]
        rw [MeasureTheory.setIntegral_measure_zero _ hvol]
  rw [hkinzero, hpotzero, zero_add]

end Work.BoseFixB2.Polar
