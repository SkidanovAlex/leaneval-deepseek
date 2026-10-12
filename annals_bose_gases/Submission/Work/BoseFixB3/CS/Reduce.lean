import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.Eps.highSlot_chiSq_aP_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB3.CS.Reduce` — the decomposition behind `B3CSRoot`

The two words of the CS step do **not** share their first factor in the corpus's vocabulary
(the corpus's `lowMult` is the free-space multiplier of the box restriction, so it does not
annihilate constants): for the slot-`j`-constant piece `Ψ = aP ℓ i (aP ℓ j Φ)` one has

    highSlot fc κ ℓ j Ψ x = Ψ x * leakFn fc κ ℓ (x j)               (`highSlot_aP_aP_eq`)

with `leakFn fc κ ℓ y = 1 − lowMult fc κ ℓ (fun _ => 1) y`.  Hence
`highSlot_j (aP_i Φ) = highSlot_j (aP_i (aQ_j Φ)) + (P_jP_iΦ)·leakFn(x_j)`, and the two words
of `B3CSRoot` decompose as FS's pairing plus the **leakage term** (see
`B3CSRoot_ANALYSIS.md`; the leakage is bounded by the high-pass estimate
`CS.Pieces.highpass_content_small`).
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Metric Filter

namespace Work.BoseFixB3.CS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix
open Work.BoseFixB3.Eps

set_option autoImplicit false

/-- The constant function `1` on the fibre variable. -/
def oneFn : EuclideanSpace ℝ (Fin 3) → ℝ := fun _ => 1

/-- The **leakage function** `1 − lowMult fc κ ℓ (fun _ => 1)`. -/
def leakFn (fc : LowCut) (κ ℓ : ℝ) (y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  1 - lowMult fc κ ℓ oneFn y

/-- A `P`-projection is constant in its own slot. -/
lemma aP_const_slot {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i : Fin n) {Φ : X n → ℝ} (hΦc : Continuous Φ)
    (x : X n) (y : EuclideanSpace ℝ (Fin 3)) :
    aP ℓ i Φ (Function.update x i y) = aP ℓ i Φ x :=
  aP_const_in_coord hℓ i hΦc x y

/-- `aP ℓ i (aP ℓ j Φ)` is independent of the slot-`j` coordinate (`i ≠ j`). -/
lemma aP_aP_const_slot {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Φ : X n → ℝ} (hΦc : Continuous Φ) (x : X n) (y : EuclideanSpace ℝ (Fin 3)) :
    aP ℓ i (aP ℓ j Φ) (Function.update x j y) = aP ℓ i (aP ℓ j Φ) x := by
  have hcongr : ∀ z : EuclideanSpace ℝ (Fin 3),
      aP ℓ j Φ (Function.update (Function.update x j y) i z)
        = aP ℓ j Φ (Function.update x i z) := by
    intro z
    have hupd : Function.update (Function.update x j y) i z
        = Function.update (Function.update x i z) j y :=
      Function.update_comm (Ne.symm hij) y z x
    rw [hupd]
    exact aP_const_slot hℓ j hΦc (Function.update x i z) y
  show (1 / ℓ ^ 3) * (∫ z in acube ℓ,
      aP ℓ j Φ (Function.update (Function.update x j y) i z)) = _
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  exact hcongr z

/-- **The leakage identity.** -/
lemma highSlot_aP_aP_eq (fc : LowCut) (κ ℓ : ℝ) (hℓ : 0 < ℓ) {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) {Φ : X n → ℝ} (hΦc : Continuous Φ) (x : X n) :
    highSlot fc κ ℓ j (aP ℓ i (aP ℓ j Φ)) x
      = aP ℓ i (aP ℓ j Φ) x * leakFn fc κ ℓ (x j) := by
  have hfib : (fun z : EuclideanSpace ℝ (Fin 3) =>
        aP ℓ i (aP ℓ j Φ) (Function.update x j z)) = fun _ => aP ℓ i (aP ℓ j Φ) x := by
    funext z
    exact aP_aP_const_slot hℓ hij hΦc x z
  show aP ℓ i (aP ℓ j Φ) x
      - lowMult fc κ ℓ (fun z => aP ℓ i (aP ℓ j Φ) (Function.update x j z)) (x j) = _
  rw [hfib]
  show aP ℓ i (aP ℓ j Φ) x
      - lowMult fc κ ℓ (fun _ => aP ℓ i (aP ℓ j Φ) x) (x j) = _
  have hc : (fun _ : EuclideanSpace ℝ (Fin 3) => aP ℓ i (aP ℓ j Φ) x)
      = fun z => aP ℓ i (aP ℓ j Φ) x * oneFn z := by
    funext z; simp [oneFn]
  rw [hc, lowMult_const_mul]
  unfold leakFn
  ring

end Work.BoseFixB3.CS
