import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Q0Value
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_muLine_slot` — the μ-line slot row of the FS `Q₁` χ-row

Fix the centred cube `acube ℓ` of side `ℓ > 0`, the one-body weight
`g : (ℝ³) → ℝ` and the normalised cube mean

    `c := (ℓ³)⁻¹ ∫_{acube ℓ} g`.

The slot projector of the corpus is the `j`-slot conditional expectation

    `aP ℓ j Φ x = (ℓ³)⁻¹ ∫_{acube ℓ} Φ (update x j y) dy`,   `aQ ℓ j Φ = Φ − aP ℓ j Φ`.

The μ-line row of the χ-sandwich of the `Q₁` term pairs the *slot-`j`-only* weight
`g(x j)` with the *mean-free* part of the slot-`j` fibre.  The identity proved here is
that the row may be evaluated with `g` itself replaced by its mean-free part
`g − c` inside the `Q_j`, and that the resulting row is the plain σ-row

    `Σ_j ∫_{abox} Φ·Q_j((g(·_j) − c)·P_jΦ) = Σ_j ∫_{abox} (Q_jΦ)·g(x_j)·(P_jΦ)`.

## Mathematics (all of it is the projection algebra of `aP`)

Write `A := P_jΦ` (constant in slot `j`), `w := (x ↦ g (x j))` and `Ψ := (w − c)·A`.
Then, using only `P_jA = A`, `∫_{abox} Φ·P_jΦ = ∫_{abox} (P_jΦ)²` (self-adjointness plus
idempotence) and `P_j w = c` (the cube mean of `g`):

* `P_j Ψ = A · (ℓ³)⁻¹ ∫_{acube ℓ}(g − c) = 0`, so `Q_j Ψ = Ψ = (w − c)·A`;
* hence `∫ Φ·Q_j Ψ = ∫ Φ w A − c ∫ Φ A = ∫ Φ w A − c ∫ A²`;
* and `∫ w A² = ∫ A²·(P_j w) = c ∫ A²` since `A²` is slot-`j`-constant;
* while `∫ (Q_jΦ)·g(x_j)·A = ∫ Φ w A − ∫ w A²`.

The two sides therefore agree slot by slot.  The two auxiliary facts about the slot mean are
the content of the two private lemmas below; the rest is bookkeeping with the integrability
lemmas of `Q0Sector`/`Q0Value`.

The statement of `chiRow_muLine_slot` is unchanged; it rests only on the corpus's
`aP`-toolbox (`aP_const_in_coord`, `aP_idem`, `aP_sym_box`, `aP_continuous`,
`integrableOn_acube_of_continuous`, `integrableOn_abox_of_continuous`,
`integral_const_acube`).
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

noncomputable section

set_option autoImplicit false

open Submission.BoseGases

/-! ## The two elementary facts about the slot mean -/

/-- `P_j` fixes every function that does not depend on the value of the `j`-th coordinate:
`F (update x j z) = F x` for all `z` forces `aP ℓ j F x = F x`. -/
private lemma aP_of_slot_const {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin N)
    {F : X N → ℝ} (hF : ∀ x z, F (Function.update x j z) = F x) (x : X N) :
    aP ℓ j F x = F x := by
  have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
  unfold aP
  have h : (∫ y in acube ℓ, F (Function.update x j y)) = ∫ y in acube ℓ, F x := by
    apply integral_congr_ae
    filter_upwards with y
    exact hF x y
  rw [h, integral_const_acube ℓ hℓ, one_div, mul_comm (F x) (ℓ ^ 3), inv_mul_cancel_left₀ hℓ3]

/-- The slot mean of the slot weight `y ↦ w (y j)` is the cube mean of `w`:
`aP ℓ j (fun y => w (y j)) x = (1/ℓ³) ∫_{acube ℓ} w`. -/
private lemma aP_weight_slot {N : ℕ} {ℓ : ℝ} (j : Fin N) (w : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : X N) :
    aP ℓ j (fun y : X N => w (y j)) x = (1 / ℓ ^ 3) * ∫ y in acube ℓ, w y := by
  unfold aP
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  simp

/-! ## The slot-by-slot evaluation -/

/-- The per-slot form of the μ-line identity: for every slot `j` the `Q_j`-row with weight
`g (·_j) − c` (where `c` is the normalised cube mean of `g`) equals the σ-row. -/
private lemma perSlot {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : X n → ℝ} (hΦc : Continuous Φ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgc : Continuous g) (j : Fin n) :
    (∫ x in abox n ℓ,
        Φ x * (aQ ℓ j
          (fun y : X n =>
            (g (y j) - (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, g z)) *
              aP ℓ j Φ y) x))
      = ∫ x in abox n ℓ,
          (aQ ℓ j Φ x) * g (x j) * (aP ℓ j Φ x) := by
  set c : ℝ := (ℓ ^ 3)⁻¹ * (∫ z in acube ℓ, g z) with hc
  have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
  have hAc : Continuous (fun x : X n => aP ℓ j Φ x) := aP_continuous hℓ j hΦc
  have hwc : Continuous (fun x : X n => g (x j)) := hgc.comp (continuous_apply j)
  have hA2c : Continuous (fun x : X n => (aP ℓ j Φ x) ^ 2) := hAc.pow 2
  have hc3 : c * ℓ ^ 3 = ∫ z in acube ℓ, g z := by
    rw [hc, mul_assoc, mul_comm (∫ z in acube ℓ, g z) (ℓ ^ 3), ← mul_assoc,
      inv_mul_cancel₀ hℓ3, one_mul]
  have hmean : (∫ z in acube ℓ, (g z - c)) = 0 := by
    have hgint : IntegrableOn g (acube ℓ) volume := integrableOn_acube_of_continuous hℓ hgc
    have hcint : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => c) (acube ℓ) volume :=
      integrableOn_acube_of_continuous hℓ continuous_const
    rw [integral_sub hgint hcint, integral_const_acube ℓ hℓ, hc3, sub_self]
  have hPw : ∀ x : X n, aP ℓ j (fun y : X n => g (y j)) x = c := by
    intro x
    rw [aP_weight_slot, one_div, hc]
  have hPΨ : ∀ x : X n, aP ℓ j
      (fun y : X n => (g (y j) - c) * aP ℓ j Φ y) x = 0 := by
    intro x
    have hcongr : (∫ y in acube ℓ, (fun y' : X n => (g (y' j) - c) * aP ℓ j Φ y')
          (Function.update x j y)) = ∫ y in acube ℓ, aP ℓ j Φ x * (g y - c) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [Function.update_self, aP_const_in_coord hℓ j hΦc x y]
      ring
    calc aP ℓ j (fun y : X n => (g (y j) - c) * aP ℓ j Φ y) x
        = (1 / ℓ ^ 3) * (∫ y in acube ℓ,
            (fun y' : X n => (g (y' j) - c) * aP ℓ j Φ y')
              (Function.update x j y)) := rfl
      _ = (1 / ℓ ^ 3) * (∫ y in acube ℓ, aP ℓ j Φ x * (g y - c)) := by rw [hcongr]
      _ = (1 / ℓ ^ 3) * (aP ℓ j Φ x * (∫ y in acube ℓ, (g y - c))) := by
            rw [integral_const_mul]
      _ = 0 := by rw [hmean, mul_zero, mul_zero]
  have hQ : ∀ x : X n, aQ ℓ j (fun y : X n => (g (y j) - c) * aP ℓ j Φ y) x
      = (g (x j) - c) * aP ℓ j Φ x := by
    intro x
    unfold aQ
    rw [hPΨ x, sub_zero]
  have hL : (∫ x in abox n ℓ, Φ x * (aQ ℓ j
        (fun y : X n => (g (y j) - c) * aP ℓ j Φ y) x))
      = (∫ x in abox n ℓ, Φ x * g (x j) * aP ℓ j Φ x)
        - c * (∫ x in abox n ℓ, Φ x * aP ℓ j Φ x) := by
    have h1 : IntegrableOn (fun x : X n => Φ x * g (x j) * aP ℓ j Φ x) (abox n ℓ) volume :=
      integrableOn_abox_of_continuous hℓ ((hΦc.mul hwc).mul hAc)
    have h2 : IntegrableOn (fun x : X n => c * (Φ x * aP ℓ j Φ x)) (abox n ℓ) volume :=
      integrableOn_abox_of_continuous hℓ (continuous_const.mul (hΦc.mul hAc))
    rw [show (∫ x in abox n ℓ, Φ x * (aQ ℓ j
            (fun y : X n => (g (y j) - c) * aP ℓ j Φ y) x))
          = ∫ x in abox n ℓ, (Φ x * g (x j) * aP ℓ j Φ x - c * (Φ x * aP ℓ j Φ x)) from by
        apply integral_congr_ae
        filter_upwards with x
        rw [hQ x]
        ring]
    rw [integral_sub h1 h2, integral_const_mul]
  have hFixA : ∀ x : X n, aP ℓ j (fun y : X n => aP ℓ j Φ y) x = aP ℓ j Φ x := by
    intro x
    exact aP_idem hℓ j hΦc x
  have hEA2 : (∫ x in abox n ℓ, Φ x * aP ℓ j Φ x) = ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2 := by
    have hsym := aP_sym_box (ℓ := ℓ) hℓ j hAc hΦc
    calc (∫ x in abox n ℓ, Φ x * aP ℓ j Φ x)
        = ∫ x in abox n ℓ, aP ℓ j (fun y : X n => aP ℓ j Φ y) x * Φ x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hFixA x]
          ring
      _ = ∫ x in abox n ℓ, aP ℓ j Φ x * aP ℓ j Φ x := hsym
      _ = ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with x
          ring
  have hEw : (∫ x in abox n ℓ, g (x j) * (aP ℓ j Φ x) ^ 2)
      = c * ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2 := by
    have hFixA2 : ∀ x : X n, aP ℓ j (fun y : X n => (aP ℓ j Φ y) ^ 2) x = (aP ℓ j Φ x) ^ 2 := by
      intro x
      exact aP_of_slot_const hℓ j (fun x z => by rw [aP_const_in_coord hℓ j hΦc x z]) x
    have hsym := aP_sym_box (ℓ := ℓ) hℓ j hA2c hwc
    calc (∫ x in abox n ℓ, g (x j) * (aP ℓ j Φ x) ^ 2)
        = ∫ x in abox n ℓ, (aP ℓ j (fun y : X n => (aP ℓ j Φ y) ^ 2) x)
            * (fun y : X n => g (y j)) x := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hFixA2 x]
          ring
      _ = ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2 * (aP ℓ j (fun y : X n => g (y j)) x) := hsym
      _ = ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2 * c := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hPw x]
      _ = c * ∫ x in abox n ℓ, (aP ℓ j Φ x) ^ 2 := by
          rw [integral_mul_const, mul_comm]
  have hR : (∫ x in abox n ℓ, (aQ ℓ j Φ x) * g (x j) * aP ℓ j Φ x)
      = (∫ x in abox n ℓ, Φ x * g (x j) * aP ℓ j Φ x)
        - ∫ x in abox n ℓ, g (x j) * (aP ℓ j Φ x) ^ 2 := by
    have h1 : IntegrableOn (fun x : X n => Φ x * g (x j) * aP ℓ j Φ x) (abox n ℓ) volume :=
      integrableOn_abox_of_continuous hℓ ((hΦc.mul hwc).mul hAc)
    have h2 : IntegrableOn (fun x : X n => g (x j) * (aP ℓ j Φ x) ^ 2) (abox n ℓ) volume :=
      integrableOn_abox_of_continuous hℓ (hwc.mul hA2c)
    rw [show (∫ x in abox n ℓ, (aQ ℓ j Φ x) * g (x j) * aP ℓ j Φ x)
          = ∫ x in abox n ℓ, (Φ x * g (x j) * aP ℓ j Φ x - g (x j) * (aP ℓ j Φ x) ^ 2) from by
        apply integral_congr_ae
        filter_upwards with x
        unfold aQ
        ring]
    rw [integral_sub h1 h2]
  rw [hL, hEA2, ← hEw, hR]

/-! ## The μ-line slot row -/

theorem chiRow_muLine_slot {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgc : Continuous g) :
    (∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        Φ x * (Submission.BoseGases.aQ ℓ j
          (fun y : Submission.BoseGases.X n =>
            (g (y j) - (ℓ ^ 3)⁻¹ * (∫ z in Submission.BoseGases.acube ℓ, g z)) *
              Submission.BoseGases.aP ℓ j Φ y) x))
      = ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.aQ ℓ j Φ x) * g (x j) *
            (Submission.BoseGases.aP ℓ j Φ x) := by
  exact Finset.sum_congr rfl (fun j _ => perSlot hℓ hΦc hgc j)

end

end Work.BoseBoxFock
