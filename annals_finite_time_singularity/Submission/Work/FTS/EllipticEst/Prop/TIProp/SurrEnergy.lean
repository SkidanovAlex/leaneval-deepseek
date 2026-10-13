import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Defs
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.BumpFacts
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrals
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.tvHypAux
import Submission.Work.EllipticEst.Core.i0Aux.TVRed.Helpers
import Submission.Work.FTS.EllipticEst.Prop.TIProp.Helpers

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted energies of the surrogate

From the estimates of `TVRed.surrIntegrals` and the endpoint bounds for `F₀`, `F₁` at the scale
`L⁴ = P/(16(P+E))`, the surrogate `ℓ = surrFun ψ F₀ F₁ L` satisfies

* `∫ (ℓ')² σ ≤ 10⁶ (Cb+1)² (P + √(P E))`,
* `∫ (ℓ'')² σ ≤ 10⁸ (Cb+1)² (P + E)`,

and the three weighted squares of `ℓ`, `ℓ'`, `ℓ''` are integrable on `Iθ`.
-/

namespace Work.FTS.EllipticEst.Prop.TIProp

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "σ" => Work.FTS.EllipticEst.thEta

/-- The weighted energies of the surrogate and the integrability of its weighted squares. -/
theorem surr_energy {ψ : ℝ → ℝ} {Cb F₀ F₁ L P E : ℝ}
    (hψ : Work.EllipticEst.Core.i0Aux.IsBump ψ Cb) (hL : 0 < L) (hLp : L ≤ Real.pi / 4)
    (hPpos : 0 < P) (hEnn : 0 ≤ E)
    (hL4 : L ^ 4 = P / (16 * (P + E)))
    (hF0 : F₀ ^ 2 ≤ 2 * L ^ (3 + Work.Spaces.eta) * E
      + 100 * L ^ (Work.Spaces.eta - 1) * P)
    (hF1 : F₁ ^ 2 ≤ 2 * L ^ (3 + Work.Spaces.eta) * E
      + 100 * L ^ (Work.Spaces.eta - 1) * P) :
    ((∫ θ in Work.Spaces.Iθ,
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
          ≤ 10 ^ 6 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)))
    ∧ ((∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 * σ θ)
          ≤ 10 ^ 8 * (Cb + 1) ^ 2 * (P + E))
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
          Work.Spaces.Iθ)
    ∧ (MeasureTheory.IntegrableOn (fun θ : ℝ =>
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 * σ θ)
          Work.Spaces.Iθ) := by
  have hPnn : 0 ≤ P := hPpos.le
  have hPEpos : 0 < P + E := by linarith
  have hXnn : 0 ≤ Real.sqrt (P * E) := Real.sqrt_nonneg _
  obtain ⟨-, hS2, hS3, -⟩ :=
    Work.EllipticEst.Core.i0Aux.TVRed.surrIntegrals (F₀ := F₀) (F₁ := F₁) hψ hL hLp
  -- ## the two elementary scale facts
  have hL2r : L ^ (2 : ℝ) = Real.sqrt (P / (16 * (P + E))) := by
    have h : (L ^ 2) ^ 2 = P / (16 * (P + E)) := by rw [← pow_mul, hL4]
    have hL2 : L ^ 2 = Real.sqrt (P / (16 * (P + E))) := by
      rw [← h, Real.sqrt_sq (sq_nonneg L)]
    have hc : L ^ (2 : ℝ) = L ^ 2 := Real.rpow_natCast L 2
    rw [hc, hL2]
  have hL2E : L ^ (2 : ℝ) * E ≤ Real.sqrt (P * E) := by
    have hkey : L ^ (2 : ℝ) * E = Real.sqrt (P * E ^ 2 / (16 * (P + E))) := by
      have h1 : L ^ (2 : ℝ) * E
          = Real.sqrt (P / (16 * (P + E))) * Real.sqrt (E ^ 2) := by
        rw [hL2r, Real.sqrt_sq hEnn]
      have h2 : Real.sqrt (P / (16 * (P + E))) * Real.sqrt (E ^ 2)
          = Real.sqrt (P * E ^ 2 / (16 * (P + E))) := by
        rw [show P * E ^ 2 / (16 * (P + E)) = P / (16 * (P + E)) * E ^ 2 by ring]
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ P / (16 * (P + E))) (E ^ 2)]
      exact h1.trans h2
    rw [hkey]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (P + E))]
    have h8 : E ≤ 16 * (P + E) := by linarith [hPEpos.le]
    have h9 : E ^ 2 ≤ (16 * (P + E)) * E := by
      have h10 := mul_le_mul_of_nonneg_right h8 hEnn
      simpa [pow_two, mul_comm] using h10
    nlinarith [h9, hPnn, hEnn]
  have hinv4 : L ^ (-4 : ℝ) = 16 * (P + E) / P := by
    have h4r : L ^ (4 : ℝ) = P / (16 * (P + E)) := by
      have hc : L ^ (4 : ℝ) = L ^ 4 := Real.rpow_natCast L 4
      rw [hc]; exact hL4
    rw [show (-4 : ℝ) = -(4 : ℝ) by ring, Real.rpow_neg hL.le, h4r, inv_div]
  have hL2inv : L ^ (-2 : ℝ) * P = 4 * Real.sqrt (P * (P + E)) := by
    have hsq : (L ^ (-2 : ℝ) * P) ^ 2 = (4 * Real.sqrt (P * (P + E))) ^ 2 := by
      have h4r : L ^ (4 : ℝ) = P / (16 * (P + E)) := by
        have hc : L ^ (4 : ℝ) = L ^ 4 := Real.rpow_natCast L 4
        rw [hc]; exact hL4
      have hA : (L ^ (-2 : ℝ) * P) ^ 2 = (L ^ (-4 : ℝ)) * P ^ 2 := by
        rw [mul_pow, show (L ^ (-2 : ℝ)) ^ 2 = L ^ (-4 : ℝ) by
          rw [pow_two, ← Real.rpow_add hL]
          congr 1
          ring]
      have hB : L ^ (-4 : ℝ) = 16 * (P + E) / P := by
        rw [show (-4 : ℝ) = -(4 : ℝ) by ring, Real.rpow_neg hL.le, h4r, inv_div]
      have hC : (4 * Real.sqrt (P * (P + E))) ^ 2 = 16 * (P * (P + E)) := by
        rw [mul_pow, show (4 : ℝ) ^ 2 = 16 by norm_num,
          Real.sq_sqrt (by positivity : (0 : ℝ) ≤ P * (P + E))]
      have hPne : P ≠ 0 := ne_of_gt hPpos
      rw [hA, hB, hC]
      field_simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · exfalso
      have h1 : 0 ≤ L ^ (-2 : ℝ) * P := mul_nonneg (Real.rpow_nonneg hL.le _) hPnn
      have h2 : 0 < 4 * Real.sqrt (P * (P + E)) := by
        have h3 : 0 < Real.sqrt (P * (P + E)) := Real.sqrt_pos.mpr (by positivity)
        linarith
      linarith
  -- ## the products of powers
  have hpA : L ^ (3 + Work.Spaces.eta) * L ^ (-(1 + Work.Spaces.eta)) = L ^ (2 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hpA2 : L ^ (Work.Spaces.eta - 1) * L ^ (-(1 + Work.Spaces.eta)) = L ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hpB : L ^ (3 + Work.Spaces.eta) * L ^ (-(3 + Work.Spaces.eta)) = 1 := by
    rw [← Real.rpow_add hL,
      show 3 + Work.Spaces.eta + (-(3 + Work.Spaces.eta)) = (0 : ℝ) by ring, Real.rpow_zero]
  have hpB2 : L ^ (Work.Spaces.eta - 1) * L ^ (-(3 + Work.Spaces.eta)) = L ^ (-4 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  -- ## the two scaled endpoint bounds
  have hsum : F₀ ^ 2 + F₁ ^ 2 ≤ 4 * L ^ (3 + Work.Spaces.eta) * E
      + 200 * L ^ (Work.Spaces.eta - 1) * P := by linarith [hF0, hF1]
  have hscA : (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(1 + Work.Spaces.eta)) ≤ 1000 * (P + Real.sqrt (P * E)) := by
    have h1 : (4 * L ^ (3 + Work.Spaces.eta) * E + 200 * L ^ (Work.Spaces.eta - 1) * P)
          * L ^ (-(1 + Work.Spaces.eta))
        = 4 * (L ^ (3 + Work.Spaces.eta) * L ^ (-(1 + Work.Spaces.eta))) * E
          + 200 * (L ^ (Work.Spaces.eta - 1) * L ^ (-(1 + Work.Spaces.eta))) * P := by ring
    have h2 := mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hL.le (-(1 + Work.Spaces.eta)))
    rw [h1, hpA, hpA2] at h2
    have h3 : 4 * (L ^ (2 : ℝ) * E) ≤ 4 * Real.sqrt (P * E) :=
      mul_le_mul_of_nonneg_left hL2E (by norm_num)
    have h5 : 200 * (L ^ (-2 : ℝ) * P) = 800 * Real.sqrt (P * (P + E)) := by
      rw [hL2inv]; ring
    have h6 : Real.sqrt (P * (P + E)) ≤ P + Real.sqrt (P * E) :=
      Work.EllipticEst.Core.i0Aux.tvc_sqrt_mul_le hPnn hEnn
    linarith [h2, h3, h5, h6]
  have hscB : (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta)) ≤ 4000 * (P + E) := by
    have h1 : (4 * L ^ (3 + Work.Spaces.eta) * E + 200 * L ^ (Work.Spaces.eta - 1) * P)
          * L ^ (-(3 + Work.Spaces.eta))
        = 4 * (L ^ (3 + Work.Spaces.eta) * L ^ (-(3 + Work.Spaces.eta))) * E
          + 200 * (L ^ (Work.Spaces.eta - 1) * L ^ (-(3 + Work.Spaces.eta))) * P := by ring
    have h2 := mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hL.le (-(3 + Work.Spaces.eta)))
    rw [h1, hpB, hpB2, hinv4] at h2
    have h3 : 200 * (16 * (P + E) / P) * P = 3200 * (P + E) := by
      field_simp
      ring
    linarith [h2, h3, hEnn, hPEpos.le]
  -- ## the two energy bounds
  have hAE : (∫ θ in Work.Spaces.Iθ,
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
      ≤ 10 ^ 6 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)) := by
    refine hS2.trans ?_
    have h2 : (0 : ℝ) ≤ (Cb + 1) ^ 2 := by positivity
    calc 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(1 + Work.Spaces.eta))
        = 1000 * (Cb + 1) ^ 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (-(1 + Work.Spaces.eta))) := by ring
      _ ≤ 1000 * (Cb + 1) ^ 2 * (1000 * (P + Real.sqrt (P * E))) :=
          mul_le_mul_of_nonneg_left hscA (by positivity)
      _ = 10 ^ 6 * (Cb + 1) ^ 2 * (P + Real.sqrt (P * E)) := by ring
  have hEE : (∫ θ in Work.Spaces.Iθ,
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 * σ θ)
      ≤ 10 ^ 8 * (Cb + 1) ^ 2 * (P + E) := by
    refine hS3.trans ?_
    have h2 : (0 : ℝ) ≤ (Cb + 1) ^ 2 := by positivity
    calc 1000 * (Cb + 1) ^ 2 * (F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta))
        = 1000 * (Cb + 1) ^ 2 * ((F₀ ^ 2 + F₁ ^ 2) * L ^ (-(3 + Work.Spaces.eta))) := by ring
      _ ≤ 1000 * (Cb + 1) ^ 2 * (4000 * (P + E)) :=
          mul_le_mul_of_nonneg_left hscB (by positivity)
      _ ≤ 10 ^ 8 * (Cb + 1) ^ 2 * (P + E) := by
          have h3 : 0 ≤ P + E := by linarith
          nlinarith [h2, h3, sq_nonneg (Cb + 1)]
  -- ## the integrability of the three weighted squares
  have hℓc : Continuous (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) :=
    (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ (ne_of_gt hL)).continuous
  have hℓ1c : ContDiff ℝ 1 (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) := by
    simpa using (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ
      (ne_of_gt hL)).deriv' (n := 1)
  have hℓbound : ∀ θ : ℝ,
      (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 ≤ (|F₀| + |F₁|) ^ 2 := by
    intro θ
    have h := Work.EllipticEst.Core.i0Aux.TVRed.surr_bound (F₀ := F₀) (F₁ := F₁) (L := L) hψ θ
    calc (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2
        = |Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ| ^ 2 := (sq_abs _).symm
      _ ≤ (|F₀| + |F₁|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have hℓ1bound : ∀ θ : ℝ,
      (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2
        ≤ (Cb * (|F₀| + |F₁|) / L) ^ 2 := by
    intro θ
    have h := Work.EllipticEst.Core.i0Aux.TVRed.deriv_surr_bound (F₀ := F₀) (F₁ := F₁) (L := L) hψ hL θ
    calc (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2
        = |deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ| ^ 2 := (sq_abs _).symm
      _ ≤ (Cb * (|F₀| + |F₁|) / L) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have hℓ2bound : ∀ θ : ℝ,
      (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2
        ≤ (Cb * (|F₀| + |F₁|) / L ^ 2) ^ 2 := by
    intro θ
    have h := Work.EllipticEst.Core.i0Aux.TVRed.deriv2_surr_bound (F₀ := F₀) (F₁ := F₁) (L := L) hψ hL θ
    calc (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2
        = |deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ| ^ 2 := (sq_abs _).symm
      _ ≤ (Cb * (|F₀| + |F₁|) / L ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have hint0 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 * σ θ) Work.Spaces.Iθ := by
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L θ) ^ 2 * σ θ)
        (volume.restrict Work.Spaces.Iθ) :=
      ((hℓc.pow 2).aestronglyMeasurable).mul
        (Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_thEta)
    refine Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_of_abs_le
      (Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_const_mul_thEta
        ((|F₀| + |F₁|) ^ 2)) haesm ?_
    intro θ hθ
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθ))]
    exact mul_le_mul_of_nonneg_right (hℓbound θ)
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hint1 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ := by
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L) θ) ^ 2 * σ θ)
        (volume.restrict Work.Spaces.Iθ) :=
      (((hℓ1c.continuous).pow 2).aestronglyMeasurable).mul
        (Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_thEta)
    refine Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_of_abs_le
      (Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_const_mul_thEta
        ((Cb * (|F₀| + |F₁|) / L) ^ 2)) haesm ?_
    intro θ hθ
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθ))]
    exact mul_le_mul_of_nonneg_right (hℓ1bound θ)
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hℓ2cont : ContinuousOn (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 1 (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h2 : ContDiff ℝ 1 (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) := by
        simpa using (Work.EllipticEst.Core.i0Aux.TVRed.surr_smooth hψ
          (ne_of_gt hL)).deriv' (n := 1)
      exact h2.contDiffOn
    exact contDiffOn_zero.1 (h1.deriv_of_isOpen isOpen_Ioo (by norm_num))
  have hint2 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 * σ θ)
      Work.Spaces.Iθ := by
    have haesm : AEStronglyMeasurable (fun θ : ℝ =>
        (deriv (deriv (Work.EllipticEst.Core.i0Aux.surrFun ψ F₀ F₁ L)) θ) ^ 2 * σ θ)
        (volume.restrict Work.Spaces.Iθ) :=
      ((Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_of_continuousOn hℓ2cont).pow 2).mul
        (Work.EllipticEst.Core.i0Aux.TVRed.tvh_aesm_thEta)
    refine Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_of_abs_le
      (Work.EllipticEst.Core.i0Aux.TVRed.tvh_integrableOn_const_mul_thEta
        ((Cb * (|F₀| + |F₁|) / L ^ 2) ^ 2)) haesm ?_
    intro θ hθ
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg hθ))]
    exact mul_le_mul_of_nonneg_right (hℓ2bound θ)
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  exact ⟨hAE, hEE, hint0, hint1, hint2⟩

end Work.FTS.EllipticEst.Prop.TIProp
