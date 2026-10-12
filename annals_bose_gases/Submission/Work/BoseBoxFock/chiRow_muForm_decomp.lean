import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiLinearAux
import Submission.Work.BoseBoxFock.chiRowDefs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_muForm_decomp` — the μ-form splits into line + correction

The `μ`-row of the FS `Q₁` χ-sandwich is

    `muForm n ℓ w Φ = 2Σ_j∫_{abox}(P_jΦ)·Φ·w(x_j)`,

its evaluated (`Q_j`-pairing) part is `muLine n ℓ w Φ = 2Σ_j∫_{abox}(Q_jΦ)·w(x_j)·(P_jΦ)`,
and the difference is the *diagonal* form `muCorr n ℓ w Φ = 2Σ_j∫_{abox}(P_jΦ)²·w(x_j)`.
The identity proved here is the pointwise decomposition at the heart of the split,

    `(P_jΦ)·Φ = (Q_jΦ)·(P_jΦ) + (P_jΦ)²`   (since `Q_j = 1 − P_j`),

integrated slot by slot.  The only non-trivial input is that the two summands are integrable
on the box: both are of the shape `A x · w (x j) · B x` with `A`, `B` continuous and `w`
measurable and bounded, which is exactly the workspace lemma
`Work.BoseBoxFock.integrableOn_cont_slot_bounded` (`chiLinearAux.lean`).

Everything here is `sorry`-free and rests only on the corpus's `aP`-toolbox
(`aP_continuous`, `aQ_continuous`) and the measurable-bounded slot toolbox.
-/

namespace Work.BoseBoxFock

open scoped BigOperators
open MeasureTheory

set_option autoImplicit false

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- Integrability on the box of the `muLine` summand of slot `j`:
`x ↦ (Q_jΦ x)·w(x_j)·(P_jΦ x)`, the product of two continuous slot factors and the bounded
measurable slot weight `w (·_j)`. -/
private lemma integrableOn_chiRow_muLine {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {Φ : X n → ℝ} (hΦc : Continuous Φ) {u : Sp → ℝ} (hum : Measurable u) {K : ℝ}
    (huK : ∀ z, |u z| ≤ K) :
    IntegrableOn (fun x : X n => (aQ ℓ j Φ x) * u (x j) * (aP ℓ j Φ x)) (abox n ℓ) volume :=
  integrableOn_cont_slot_bounded (n := n) (ℓ := ℓ) hℓ j (A := aQ ℓ j Φ)
    (B := aP ℓ j Φ) (aQ_continuous hℓ j hΦc) (aP_continuous hℓ j hΦc) hum huK

/-- Integrability on the box of the `muCorr` summand of slot `j`:
`x ↦ (P_jΦ x)²·w(x_j)`. -/
private lemma integrableOn_chiRow_muCorr {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {Φ : X n → ℝ} (hΦc : Continuous Φ) {u : Sp → ℝ} (hum : Measurable u) {K : ℝ}
    (huK : ∀ z, |u z| ≤ K) :
    IntegrableOn (fun x : X n => (aP ℓ j Φ x) ^ 2 * u (x j)) (abox n ℓ) volume := by
  have h := integrableOn_cont_slot_bounded (n := n) (ℓ := ℓ) hℓ j
    (A := fun x : X n => (aP ℓ j Φ x) ^ 2) (B := fun _ : X n => (1 : ℝ))
    ((aP_continuous hℓ j hΦc).pow 2) continuous_const hum huK
  refine h.congr ?_
  filter_upwards with x
  ring

/-- The per-slot decomposition `(P_jΦ)·Φ = (Q_jΦ)·(P_jΦ) + (P_jΦ)²` after integration over
the box. -/
private lemma chiRow_muForm_slot {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {Φ : X n → ℝ} (hΦc : Continuous Φ) {u : Sp → ℝ} (hum : Measurable u) {K : ℝ}
    (huK : ∀ z, |u z| ≤ K) :
    (∫ x in abox n ℓ, (aP ℓ j Φ x) * Φ x * u (x j))
      = (∫ x in abox n ℓ, (aQ ℓ j Φ x) * u (x j) * (aP ℓ j Φ x))
        + (∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2 * u (x j)) := by
  have hpt : (fun x : X n => (aP ℓ j Φ x) * Φ x * u (x j))
      = fun x : X n =>
          (aQ ℓ j Φ x) * u (x j) * (aP ℓ j Φ x) + (aP ℓ j Φ x) ^ 2 * u (x j) := by
    funext x
    simp only [aQ]
    ring
  rw [hpt]
  exact integral_add (integrableOn_chiRow_muLine hℓ j hΦc hum huK)
    (integrableOn_chiRow_muCorr hℓ j hΦc hum huK)

theorem chiRow_muForm_decomp {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ) {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hwm : Measurable w)
    {K : ℝ} (hw : ∀ x, |w x| ≤ K) :
    Work.BoseBoxFock.muForm n ℓ w Φ
      = Work.BoseBoxFock.muLine n ℓ w Φ + Work.BoseBoxFock.muCorr n ℓ w Φ := by
  have hsum :
      (∑ j : Fin n, ∫ x in abox n ℓ, (aP ℓ j Φ x) * Φ x * w (x j))
        = (∑ j : Fin n, ∫ x in abox n ℓ, (aQ ℓ j Φ x) * w (x j) * (aP ℓ j Φ x))
          + (∑ j : Fin n, ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2 * w (x j)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => chiRow_muForm_slot hℓ j hΦc hwm hw)
  unfold muForm muLine muCorr
  rw [hsum]
  ring

end Work.BoseBoxFock
