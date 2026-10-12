import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chiRow_rhsEval
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_slotIdentity` — the `n₀`-sandwich slot identity of the FS `Q₁` χ-row

The statement is the exact evaluation of the `n₀`-sandwich ("χ-row") of the `Q₁` term in the
box analysis of Fournais–Solovjev, written in the raw centred-box vocabulary
(`X n = (ℝ³)ⁿ`, `acube ℓ`, `abox n ℓ`, `aP ℓ i`, `aQ ℓ i = 1 - aP ℓ i`).

With `ψᵢ := aP ℓ i Φ`, `h := g - (ℓ³)⁻¹∫_{acube ℓ} g` and the auxiliary double sum

    `Zᵢⱼ := ∫_{abox n ℓ} (aP ℓ i Φ x) * h (x i) * (aP ℓ j Φ x)`,

the proof goes by evaluating the two sides *independently*:

* `chiRow_lhsEval` (proved below, **no** mean-zero hypothesis needed): the left-hand side
  equals `2 * ∑ᵢ ∑ⱼ Zᵢⱼ`.  The two slots of the χ-row give
  `∑ᵢ ⨍ ψᵢ·(∑ⱼ h(xⱼ)ψⱼ)` and `∑ᵢ ⨍ ψᵢ·h(xᵢ)·(∑ⱼ ψⱼ)`; each is `∑ᵢ∑ⱼ` of a term, and the
  two double sums agree by the exchange `i ↔ j` inside the integral
  (`∫ ψᵢ h(xⱼ) ψⱼ = ∫ ψⱼ h(xⱼ) ψᵢ`).  No cancellation among the diagonal terms is used, so
  `∫_{acube} h = 0` is *not* needed here.
* `Work.BoseBoxFock.chiRow_rhsEval` (the delegated twin, a separate module): the right-hand
  side equals the same `2 * ∑ᵢ ∑ⱼ Zᵢⱼ`.  Here the mean-zero hypothesis *is* needed, twice:
  the diagonal `Zᵢᵢ` vanishes and the `h(xᵢ)·aP ℓ i (aP ℓ j Φ)` residual vanishes, both because
  `aP ℓ i (fun y => h (y i) * F y) = 0` for `F` constant in slot `i` and `∫_{acube} h = 0`
  (the factor `F x` pulls out of the slot mean and the remaining cube integral of `h` is `0`).

The assembly below supplies `h := g - (ℓ³)⁻¹∫_{acube ℓ} g`, its continuity, its vanishing cube
mean and the pointwise splitting `g = h + c`, and chains the two evaluations.
-/

namespace Work.BoseBoxFock

open Submission.BoseGases MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## The pointwise form of the sum-self-adjointness of the slot means -/

/-- `∫ Φ · (∑ᵢ Pᵢ Fᵢ) = ∑ᵢ ∫ (PᵢΦ) · Fᵢ`: the slot self-adjointness `aP_sym_box`
distributed over a finite sum of slots, in the pointwise-sum form used by the χ-row. -/
private lemma aP_sym_sum_pt {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : X n → ℝ}
    (hΦc : Continuous Φ) {F : Fin n → X n → ℝ} (hF : ∀ i, Continuous (F i)) :
    (∫ x in abox n ℓ, Φ x * (∑ i, (aP ℓ i (F i)) x))
      = ∑ i, ∫ x in abox n ℓ, (aP ℓ i Φ) x * F i x := by
  calc (∫ x in abox n ℓ, Φ x * (∑ i, (aP ℓ i (F i)) x))
      = ∫ x in abox n ℓ, ∑ i, Φ x * (aP ℓ i (F i)) x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Finset.mul_sum]
    _ = ∑ i, ∫ x in abox n ℓ, Φ x * (aP ℓ i (F i)) x := by
        rw [integral_finset_sum]
        intro i _
        exact integrableOn_mul_aP hℓ i hΦc (hF i)
    _ = ∑ i, ∫ x in abox n ℓ, (aP ℓ i Φ) x * F i x := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact (aP_sym_box hℓ i hΦc (hF i)).symm

/-! ## Evaluation of the left-hand side -/

/-- The left-hand side of the χ-row slot identity is `2 ∑ᵢ ∑ⱼ Zᵢⱼ`.  No mean-zero
hypothesis on `h` is used. -/
theorem chiRow_lhsEval {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : X n → ℝ} (hΦc : Continuous Φ)
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} (hhc : Continuous h) :
    (∫ x in abox n ℓ,
        Φ x *
          ( (∑ i : Fin n, aP ℓ i
                (fun y : X n => (∑ j : Fin n, h (y j) * aP ℓ j Φ y)) x)
            + (∑ i : Fin n, aP ℓ i
                (fun y : X n => h (y i) * (∑ j : Fin n, aP ℓ j Φ y)) x) ))
      = 2 * ∑ i : Fin n, ∑ j : Fin n,
          (∫ x in abox n ℓ, (aP ℓ i Φ x) * h (x i) * (aP ℓ j Φ x)) := by
  have hF1c : Continuous (fun y : X n => ∑ j : Fin n, h (y j) * aP ℓ j Φ y) :=
    continuous_finsetSum _ (fun j _ => (hhc.comp (continuous_apply j)).mul (aP_continuous hℓ j hΦc))
  have hF2c : ∀ i : Fin n, Continuous (fun y : X n => h (y i) * (∑ j : Fin n, aP ℓ j Φ y)) :=
    fun i => (hhc.comp (continuous_apply i)).mul
      (continuous_finsetSum _ (fun j _ => aP_continuous hℓ j hΦc))
  have hAeval : (∫ x in abox n ℓ, Φ x * (∑ i : Fin n,
        (aP ℓ i (fun y : X n => (∑ j : Fin n, h (y j) * aP ℓ j Φ y))) x))
      = ∑ i : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ) x * (∑ j : Fin n, h (x j) * aP ℓ j Φ x) :=
    aP_sym_sum_pt (ℓ := ℓ) hℓ hΦc (fun _ => hF1c)
  have hBeval : (∫ x in abox n ℓ, Φ x * (∑ i : Fin n,
        (aP ℓ i (fun y : X n => h (y i) * (∑ j : Fin n, aP ℓ j Φ y))) x))
      = ∑ i : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ) x * (h (x i) * (∑ j : Fin n, aP ℓ j Φ x)) :=
    aP_sym_sum_pt (ℓ := ℓ) hℓ hΦc hF2c
  have hAexp : (∑ i : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ) x * (∑ j : Fin n, h (x j) * aP ℓ j Φ x))
      = ∑ i : Fin n, ∑ j : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ) x * h (x j) * (aP ℓ j Φ) x := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∫ x in abox n ℓ, (aP ℓ i Φ) x * (∑ j : Fin n, h (x j) * aP ℓ j Φ x))
        = ∫ x in abox n ℓ, ∑ j : Fin n, (aP ℓ i Φ) x * h (x j) * (aP ℓ j Φ) x from by
          apply integral_congr_ae
          filter_upwards with x
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [integral_finset_sum]
    intro j _
    refine integrableOn_abox_of_continuous hℓ ?_
    exact ((aP_continuous hℓ i hΦc).mul (hhc.comp (continuous_apply j))).mul (aP_continuous hℓ j hΦc)
  have hBexp : (∑ i : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ) x * (h (x i) * (∑ j : Fin n, aP ℓ j Φ x)))
      = ∑ i : Fin n, ∑ j : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ) x * h (x i) * (aP ℓ j Φ) x := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show (∫ x in abox n ℓ, (aP ℓ i Φ) x * (h (x i) * (∑ j : Fin n, aP ℓ j Φ x)))
        = ∫ x in abox n ℓ, ∑ j : Fin n, (aP ℓ i Φ) x * h (x i) * (aP ℓ j Φ) x from by
          apply integral_congr_ae
          filter_upwards with x
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [integral_finset_sum]
    intro j _
    refine integrableOn_abox_of_continuous hℓ ?_
    exact ((aP_continuous hℓ i hΦc).mul (hhc.comp (continuous_apply i))).mul (aP_continuous hℓ j hΦc)
  have hsplit : (∫ x in abox n ℓ, Φ x * ((∑ i : Fin n, (aP ℓ i
          (fun y : X n => (∑ j : Fin n, h (y j) * aP ℓ j Φ y))) x)
        + (∑ i : Fin n, (aP ℓ i (fun y : X n => h (y i) * (∑ j : Fin n, aP ℓ j Φ y))) x)))
      = (∫ x in abox n ℓ, Φ x * (∑ i : Fin n, (aP ℓ i
            (fun y : X n => (∑ j : Fin n, h (y j) * aP ℓ j Φ y))) x))
        + (∫ x in abox n ℓ, Φ x * (∑ i : Fin n, (aP ℓ i
            (fun y : X n => h (y i) * (∑ j : Fin n, aP ℓ j Φ y))) x)) := by
    have hA1c : Continuous (fun x : X n => ∑ i : Fin n, (aP ℓ i
        (fun y : X n => (∑ j : Fin n, h (y j) * aP ℓ j Φ y))) x) :=
      continuous_finsetSum _ (fun i _ => aP_continuous hℓ i hF1c)
    have hA2c : Continuous (fun x : X n => ∑ i : Fin n, (aP ℓ i
        (fun y : X n => h (y i) * (∑ j : Fin n, aP ℓ j Φ y))) x) :=
      continuous_finsetSum _ (fun i _ => aP_continuous hℓ i (hF2c i))
    have hI1 : Integrable (fun x : X n => Φ x * (∑ i : Fin n, (aP ℓ i
        (fun y : X n => (∑ j : Fin n, h (y j) * aP ℓ j Φ y))) x))
        ((volume : Measure (X n)).restrict (abox n ℓ)) :=
      integrableOn_abox_of_continuous hℓ (hΦc.mul hA1c)
    have hI2 : Integrable (fun x : X n => Φ x * (∑ i : Fin n, (aP ℓ i
        (fun y : X n => h (y i) * (∑ j : Fin n, aP ℓ j Φ y))) x))
        ((volume : Measure (X n)).restrict (abox n ℓ)) :=
      integrableOn_abox_of_continuous hℓ (hΦc.mul hA2c)
    have h1 : (∫ x in abox n ℓ, Φ x * ((∑ i : Fin n, (aP ℓ i
            (fun y : X n => (∑ j : Fin n, h (y j) * aP ℓ j Φ y))) x)
          + (∑ i : Fin n, (aP ℓ i (fun y : X n => h (y i) * (∑ j : Fin n, aP ℓ j Φ y))) x)))
        = ∫ x in abox n ℓ, Φ x * (∑ i : Fin n, (aP ℓ i
              (fun y : X n => (∑ j : Fin n, h (y j) * aP ℓ j Φ y))) x)
            + Φ x * (∑ i : Fin n, (aP ℓ i
              (fun y : X n => h (y i) * (∑ j : Fin n, aP ℓ j Φ y))) x) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [h1, integral_add hI1 hI2]
  have hswap : (∑ i : Fin n, ∑ j : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ x) * h (x j) * (aP ℓ j Φ x))
      = ∑ i : Fin n, ∑ j : Fin n, ∫ x in abox n ℓ, (aP ℓ i Φ x) * h (x i) * (aP ℓ j Φ x) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hsplit, hAeval, hBeval, hAexp, hBexp, hswap]
  ring

/-! ## The χ-row slot identity -/

theorem chiRow_slotIdentity {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgc : Continuous g) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Φ x *
          ( (∑ i : Fin n, Submission.BoseGases.aP ℓ i
                (fun y : Submission.BoseGases.X n =>
                  (∑ j : Fin n, (g (y j) - (ℓ ^ 3)⁻¹ *
                    (∫ z in Submission.BoseGases.acube ℓ, g z)) *
                      Submission.BoseGases.aP ℓ j Φ y)) x)
            + (∑ i : Fin n, Submission.BoseGases.aP ℓ i
                (fun y : Submission.BoseGases.X n =>
                  (g (y i) - (ℓ ^ 3)⁻¹ * (∫ z in Submission.BoseGases.acube ℓ, g z)) *
                    (∑ j : Fin n, Submission.BoseGases.aP ℓ j Φ y)) x) ))
      = 2 * ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else
          (∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ i Φ x) * g (x i) *
              (Submission.BoseGases.aQ ℓ i
                (fun y : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ j Φ y) x)) := by
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 3) =>
      g z - (ℓ^3)⁻¹ * (∫ t in Submission.BoseGases.acube ℓ, g t)) :=
    hgc.sub continuous_const
  have hmean : (∫ z in Submission.BoseGases.acube ℓ,
      (g z - (ℓ^3)⁻¹ * (∫ t in Submission.BoseGases.acube ℓ, g t))) = 0 := by
    have h1 : (∫ z in Submission.BoseGases.acube ℓ,
          (g z - (ℓ^3)⁻¹ * (∫ t in Submission.BoseGases.acube ℓ, g t)))
        = (∫ z in Submission.BoseGases.acube ℓ, g z)
          - (∫ z in Submission.BoseGases.acube ℓ,
              ((ℓ^3)⁻¹ * (∫ t in Submission.BoseGases.acube ℓ, g t))) :=
      integral_sub (integrableOn_acube_of_continuous hℓ hgc)
        (integrableOn_acube_of_continuous hℓ continuous_const)
    rw [h1, integral_const_acube ℓ hℓ]
    field_simp
    ring
  have hg_eq : ∀ z : EuclideanSpace ℝ (Fin 3),
      g z = (g z - (ℓ^3)⁻¹ * (∫ t in Submission.BoseGases.acube ℓ, g t))
        + (ℓ^3)⁻¹ * (∫ t in Submission.BoseGases.acube ℓ, g t) := by
    intro z; ring
  have hL := chiRow_lhsEval (ℓ := ℓ) hℓ hΦc hcont
  have hR := chiRow_rhsEval (ℓ := ℓ) hℓ hΦc hgc hcont hmean hg_eq
  exact hL.trans hR.symm

end

end Work.BoseBoxFock
