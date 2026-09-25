import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.DbarCnPertAux

namespace Work.NN.Core

theorem jholo_dbar_pointwise {n : ℕ} (hn : 0 < n) {α ε : ℝ} (hε : 0 ≤ ε) {ρ : Fin n → ℝ}
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    (hA : ∀ i j : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single i 1) j)
      (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε)
    {h : Work.NN.Core.Cn n → ℂ}
    (hdbar : ∀ j : Fin n, ∀ z ∈ Work.CR.Flat.polydisc 0 ρ,
      Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) h z (Pi.single j 1) = 0)
    {z : Work.NN.Core.Cn n} (hz : z ∈ Work.CR.Flat.polydisc 0 ρ) :
    (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2)
      ≤ (n : ℝ) ^ 2 * ε ^ 2 *
        (∑ j : Fin n, (‖Work.CR.Flat.dCoord j h z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2)) := by
  classical
  set S : ℝ := ∑ j : Fin n, (‖Work.CR.Flat.dCoord j h z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2) with hS
  set T : ℝ := ∑ j : Fin n, (‖Work.CR.Flat.dCoord j h z‖ + ‖Work.CR.Flat.dbarCoord j h z‖) with hT
  have hbj : ∀ j : Fin n, Work.CR.Flat.dbarCoord j h z
      = -(Complex.I / 2) * fderiv ℝ h z (A z (Pi.single j (1 : ℂ))) := by
    intro j
    have h0 := hdbar j z hz
    rw [dbarCoef_lin] at h0
    have h1 : Work.CR.Flat.dbarCoord j h z = -Lcoef A h j z := by linear_combination h0
    rw [h1, Lcoef]
    ring
  have hEntry : ∀ i k : Fin n, ‖(A z (Pi.single i (1 : ℂ))) k‖ ≤ ε := by
    intro i k
    have h1 := Work.CR.Flat.norm_apply_le_holderNorm 1 α (fun z => A z (Pi.single i 1) k)
      (Work.CR.Flat.polydisc 0 ρ) hz
    have h2 := le_trans h1 (hA i k)
    exact (ENNReal.ofReal_le_ofReal_iff hε).mp h2
  have hFb : ∀ j : Fin n, ‖fderiv ℝ h z (A z (Pi.single j (1 : ℂ)))‖ ≤ ε * T := by
    intro j
    rw [fderiv_eq_sum_dCoord_dbarCoord]
    refine (norm_sum_le Finset.univ _).trans ?_
    calc ∑ k : Fin n, ‖(A z (Pi.single j (1 : ℂ))) k * Work.CR.Flat.dCoord k h z
            + starRingEnd ℂ ((A z (Pi.single j (1 : ℂ))) k) * Work.CR.Flat.dbarCoord k h z‖
        ≤ ∑ k : Fin n, ε * (‖Work.CR.Flat.dCoord k h z‖ + ‖Work.CR.Flat.dbarCoord k h z‖) := by
          refine Finset.sum_le_sum fun k _ => ?_
          calc ‖(A z (Pi.single j (1 : ℂ))) k * Work.CR.Flat.dCoord k h z
                + starRingEnd ℂ ((A z (Pi.single j (1 : ℂ))) k) * Work.CR.Flat.dbarCoord k h z‖
              ≤ ‖(A z (Pi.single j (1 : ℂ))) k * Work.CR.Flat.dCoord k h z‖
                + ‖starRingEnd ℂ ((A z (Pi.single j (1 : ℂ))) k) * Work.CR.Flat.dbarCoord k h z‖ :=
                norm_add_le _ _
            _ = ‖(A z (Pi.single j (1 : ℂ))) k‖ * (‖Work.CR.Flat.dCoord k h z‖
                + ‖Work.CR.Flat.dbarCoord k h z‖) := by
                rw [norm_mul, norm_mul, Complex.norm_conj]; ring
            _ ≤ ε * (‖Work.CR.Flat.dCoord k h z‖ + ‖Work.CR.Flat.dbarCoord k h z‖) :=
                mul_le_mul_of_nonneg_right (hEntry j k) (by positivity)
      _ = ε * T := by rw [← Finset.mul_sum, ← hT]
  have hb : ∀ j : Fin n, ‖Work.CR.Flat.dbarCoord j h z‖ ≤ ε * T / 2 := by
    intro j
    rw [hbj j, norm_mul]
    have hc : ‖(-(Complex.I / 2) : ℂ)‖ = 1 / 2 := by
      rw [norm_neg, norm_div, Complex.norm_I]; norm_num
    rw [hc]
    nlinarith [hFb j]
  have hsumsq : (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2) ≤ (n : ℝ) * (ε * T / 2) ^ 2 := by
    calc (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2)
        ≤ ∑ j : Fin n, (ε * T / 2) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
      _ = (n : ℝ) * (ε * T / 2) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hT2 : T ^ 2 ≤ 2 * (n : ℝ) * S := by
    have hcs : T ^ 2 ≤ (n : ℝ) * ∑ k : Fin n,
        (‖Work.CR.Flat.dCoord k h z‖ + ‖Work.CR.Flat.dbarCoord k h z‖) ^ 2 := by
      rw [hT]
      have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun k : Fin n => ‖Work.CR.Flat.dCoord k h z‖ + ‖Work.CR.Flat.dbarCoord k h z‖)
      simpa using hh
    have htk : (∑ k : Fin n, (‖Work.CR.Flat.dCoord k h z‖ + ‖Work.CR.Flat.dbarCoord k h z‖) ^ 2)
        ≤ 2 * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      nlinarith [sq_nonneg (‖Work.CR.Flat.dCoord k h z‖ - ‖Work.CR.Flat.dbarCoord k h z‖)]
    have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
    nlinarith [hcs, htk, hn0]
  calc (∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j h z‖ ^ 2)
      ≤ (n : ℝ) * (ε * T / 2) ^ 2 := hsumsq
    _ = (n : ℝ) * ε ^ 2 * T ^ 2 / 4 := by ring
    _ ≤ (n : ℝ) * ε ^ 2 * (2 * (n : ℝ) * S) / 4 := by
        have h1 : (0 : ℝ) ≤ (n : ℝ) * ε ^ 2 / 4 := by positivity
        have h2 := mul_le_mul_of_nonneg_left hT2 h1
        calc (n : ℝ) * ε ^ 2 * T ^ 2 / 4 = ((n : ℝ) * ε ^ 2 / 4) * T ^ 2 := by ring
          _ ≤ ((n : ℝ) * ε ^ 2 / 4) * (2 * (n : ℝ) * S) := h2
          _ = (n : ℝ) * ε ^ 2 * (2 * (n : ℝ) * S) / 4 := by ring
    _ = (n : ℝ) ^ 2 * ε ^ 2 * S / 2 := by ring
    _ ≤ (n : ℝ) ^ 2 * ε ^ 2 * S := by
        have h2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * ε ^ 2 * S := by rw [hS]; positivity
        linarith

end Work.NN.Core
