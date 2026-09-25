import Mathlib
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.CR.Flat.Cauchy.bmCz.integral_bmKernel_mul_dCoord
import Submission.Work.CR.Flat.Cauchy.bmDzKernel_cz_bound
import Submission.Work.CR.Flat.Cauchy.bmCz.czAux
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.NN.Core.CzBfar.bmKernel_ibp_translate
import Submission.Work.NN.Core.CzBfar.eucNorm_ge_three_mul
import Submission.Work.NN.Core.CzBfar.far_single_bound
import Submission.Work.NN.Core.CzBfar.far_diff_bound

noncomputable section

namespace Work.NN.Core

open MeasureTheory Set

/-! ### A local helper -/

private lemma dCoord_comp_add_dev {n : ℕ} (j : Fin n) (g : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    Work.CR.Flat.dCoord j (fun x : Fin n → ℂ => g (z + x))
      = fun x => Work.CR.Flat.dCoord j g (z + x) := by
  funext x
  simp only [Work.CR.Flat.dCoord, fderiv_comp_add_left]

/-! ## The far-field estimate -/

theorem czB_far_bound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Fin n → (Fin n → ℂ) → ℂ) (A K : Fin n → ℝ),
      (∀ j, ContDiff ℝ 1 (F j)) →
      (∀ j, 0 ≤ A j) → (∀ j, 0 ≤ K j) →
      (∀ j z, R ≤ ‖z‖ → F j z = 0) →
      (∀ j z, ‖F j z‖ ≤ A j) →
      (∀ j x y, ‖F j x - F j y‖ ≤ K j * ‖x - y‖ ^ α) →
      ∀ i : Fin n,
        (∀ z : Fin n → ℂ, 4 * (Real.sqrt n * (R + 1)) + 4 ≤ ‖z‖ →
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z‖
            ≤ C * ∑ j, (A j + K j)) ∧
        (∀ z z' : Fin n → ℂ, 4 * (Real.sqrt n * (R + 1)) + 4 ≤ ‖z‖ →
          4 * (Real.sqrt n * (R + 1)) + 4 ≤ ‖z'‖ →
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
            - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z'‖
            ≤ C * ‖z - z'‖ ^ α * ∑ j, (A j + K j)) := by
  classical
  -- the support radius
  set r : ℝ := max R 1 with hrmax
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hRr : R ≤ r := le_max_left R 1
  have hrR1 : r ≤ R + 1 := max_le (by linarith) (by linarith)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  -- the constants supplied by the two far-field estimates
  choose C1 hC1pos hC1 using fun p : Fin n × Fin n => CzBfar.far_single_bound hn p.1 p.2 hr
  choose C2 hC2pos hC2 using fun p : Fin n × Fin n => CzBfar.far_diff_bound hn p.1 p.2 hr hα0 hα1
  set Cc : ℝ := 1 + ∑ p : Fin n × Fin n, (C1 p + C2 p) with hCcmax
  have hCcpos : 0 < Cc := by
    rw [hCcmax]
    have h : (0 : ℝ) ≤ ∑ p : Fin n × Fin n, (C1 p + C2 p) :=
      Finset.sum_nonneg (fun p _ => by have := hC1pos p; have := hC2pos p; linarith)
    linarith
  have hC1le : ∀ p : Fin n × Fin n, C1 p ≤ Cc := by
    intro p
    have h : C1 p + C2 p ≤ ∑ q : Fin n × Fin n, (C1 q + C2 q) :=
      Finset.single_le_sum (s := Finset.univ) (f := fun q => C1 q + C2 q) (a := p)
        (fun q _ => by have := hC1pos q; have := hC2pos q; linarith) (Finset.mem_univ p)
    have := hC2pos p
    rw [hCcmax]; linarith
  have hC2le : ∀ p : Fin n × Fin n, C2 p ≤ Cc := by
    intro p
    have h : C1 p + C2 p ≤ ∑ q : Fin n × Fin n, (C1 q + C2 q) :=
      Finset.single_le_sum (s := Finset.univ) (f := fun q => C1 q + C2 q) (a := p)
        (fun q _ => by have := hC1pos q; have := hC2pos q; linarith) (Finset.mem_univ p)
    have := hC1pos p
    rw [hCcmax]; linarith
  refine ⟨Cc, le_of_lt hCcpos, ?_⟩
  intro F A K hF hA hK hvan hbdd hholder i
  have hcs : ∀ l, HasCompactSupport (F l) := fun l =>
    Work.CR.Flat.Cauchy.bmCz.hasCompactSupport_of_norm_le
      (fun x hx => hvan l x (le_trans hRr hx))
  have hzr : ∀ {w : Fin n → ℂ}, 4 * (Real.sqrt n * (R + 1)) + 4 ≤ ‖w‖ → r < ‖w‖ := by
    intro w hw
    have hR1 : (0 : ℝ) ≤ R + 1 := by linarith
    nlinarith [hR1, hw, hsqrt1, hrR1,
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt n) hR1]
  -- the integrated form of the derivative of the potential
  have hdec : ∀ w : Fin n → ℂ, r < ‖w‖ →
      Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) w
        = -∑ l, ∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (w + x) := by
    intro w hw
    have hhd : ∀ l : Fin n,
        (∫ x, Work.CR.Flat.Cauchy.bmKernel l x * Work.CR.Flat.dCoord i (F l) (w + x))
          = -∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (w + x) := by
      intro l
      have h := CzBfar.bmKernel_ibp_translate l i (hF l)
        (fun x hx => hvan l x (le_trans hRr hx)) hw
      simpa only [dCoord_comp_add_dev] using h
    rw [Work.NN.Core.bmPotential_dCoord_eq hn hF hcs i w]
    refine Eq.trans (Finset.sum_congr rfl (fun l _ => hhd l)) ?_
    rw [Finset.sum_neg_distrib]
  constructor
  · intro z hz
    rw [hdec z (hzr hz)]
    have hgeo : ∀ x, ‖z + x‖ < r → 3 * r ≤ Work.CR.Flat.Cauchy.eucNorm x :=
      fun x hx => CzBfar.eucNorm_ge_three_mul hn hR hRr hrR1 hz hx
    calc ‖-∑ l, ∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z + x)‖
        = ‖∑ l, ∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z + x)‖ := norm_neg _
      _ ≤ ∑ l, ‖∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z + x)‖ := norm_sum_le _ _
      _ ≤ ∑ l, Cc * A l := by
          refine Finset.sum_le_sum (fun l _ => ?_)
          refine le_trans (hC1 (i, l) (F l) (A l) z (hA l) (hbdd l) ?_ hgeo) ?_
          · exact fun x hx => hvan l x (le_trans hRr hx)
          · exact mul_le_mul_of_nonneg_right (hC1le (i, l)) (hA l)
      _ = Cc * ∑ l, A l := by rw [Finset.mul_sum]
      _ ≤ Cc * ∑ l, (A l + K l) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun l _ => by linarith [hK l]))
            (le_of_lt hCcpos)
  · intro z z' hz hz'
    rw [hdec z (hzr hz), hdec z' (hzr hz')]
    have hgeo : ∀ x, ‖z + x‖ < r → 3 * r ≤ Work.CR.Flat.Cauchy.eucNorm x :=
      fun x hx => CzBfar.eucNorm_ge_three_mul hn hR hRr hrR1 hz hx
    have hgeo' : ∀ x, ‖z' + x‖ < r → 3 * r ≤ Work.CR.Flat.Cauchy.eucNorm x :=
      fun x hx => CzBfar.eucNorm_ge_three_mul hn hR hRr hrR1 hz' hx
    have hsplit : (∑ l, (∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z + x)))
        - (∑ l, (∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z' + x)))
        = ∑ l, ((∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z + x))
            - (∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z' + x))) := by
      rw [Finset.sum_sub_distrib]
    calc ‖-∑ l, (∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z + x))
          - -∑ l, (∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z' + x))‖
        = ‖(∑ l, (∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z + x)))
            - (∑ l, (∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z' + x)))‖ := by
          rw [neg_sub_neg, norm_sub_rev]
      _ = ‖∑ l, ((∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z + x))
            - (∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z' + x)))‖ := by rw [hsplit]
      _ ≤ ∑ l, ‖(∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z + x))
            - (∫ x, Work.CR.Flat.Cauchy.bmDzKernel i l x * F l (z' + x))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ l, Cc * K l * ‖z - z'‖ ^ α := by
          refine Finset.sum_le_sum (fun l _ => ?_)
          refine le_trans (hC2 (i, l) (F l) (K l) z z' (hK l) (hholder l) ?_ hgeo hgeo') ?_
          · exact fun x hx => hvan l x (le_trans hRr hx)
          · refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hC2le (i, l)) (hK l)) ?_
            exact Real.rpow_nonneg (norm_nonneg _) α
      _ = Cc * ‖z - z'‖ ^ α * ∑ l, K l := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun l _ => by ring)
      _ ≤ Cc * ‖z - z'‖ ^ α * ∑ l, (A l + K l) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun l _ => by linarith [hA l]))
            (by positivity)

end Work.NN.Core
