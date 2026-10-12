import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.boxAvgAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Change of variables for the pair kernel.**

For a bounded continuous even `ξ` vanishing off the ball of radius `σ` and a bounded a.e. strongly
measurable `W` vanishing off the ball of radius `ρ`, the double kernel
`ξ w W (w - y + c) ξ y` integrates to the same value as the *shifted* pair form
`W y ξ (x - y) ξ (c - x)`.

The proof is the substitution `y ↦ w + c - y` in the inner integral, Fubini
(`integral_integral_swap`, with the joint integrability supplied by
`integrable_prod_of_bdd_of_supp`), the translation `w ↦ w - c` and the evenness `ξ (-z) = ξ z`. -/
theorem integral_shift_pair_eq {c : EuclideanSpace ℝ (Fin 3)} {ξ : EuclideanSpace ℝ (Fin 3) → ℂ}
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} {ρ σ : ℝ}
    (hξc : Continuous ξ) (hξb : ∃ C, ∀ x, ‖ξ x‖ ≤ C) (hξs : ∀ x, σ < ‖x‖ → ξ x = 0)
    (hξe : ∀ z, ξ (-z) = ξ z)
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, ρ < ‖x‖ → W x = 0) :
    (∫ w, ∫ y, ξ w * ((W (w - y + c) : ℝ) : ℂ) * ξ y)
      = ∫ y, ∫ x, ((W y : ℝ) : ℂ) * ξ (x - y) * ξ (c - x) := by
  obtain ⟨Cξ, hCξ⟩ := hξb
  obtain ⟨CW, hCW⟩ := hWb
  have hCξnn : 0 ≤ Cξ := le_trans (norm_nonneg (ξ 0)) (hCξ 0)
  have hCWnn : 0 ≤ CW := le_trans (norm_nonneg (W 0)) (hCW 0)
  -- ## Integrability of the rearranged kernel on the product
  have hfint : Integrable (fun p : E3 × E3 =>
      ξ p.1 * ((W p.2 : ℝ) : ℂ) * ξ (p.1 + c - p.2)) (volume.prod volume) := by
    refine integrable_prod_of_bdd_of_supp (ρ := σ) (σ := ρ) (f := fun p : E3 × E3 =>
      ξ p.1 * ((W p.2 : ℝ) : ℂ) * ξ (p.1 + c - p.2)) ?_ ?_ ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : E3 × E3 => ξ p.1) (volume.prod volume) :=
        (hξc.comp continuous_fst).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : E3 × E3 => ((W p.2 : ℝ) : ℂ))
          (volume.prod volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable hWm.comp_snd
      have h3 : AEStronglyMeasurable (fun p : E3 × E3 => ξ (p.1 + c - p.2))
          (volume.prod volume) :=
        (hξc.comp (by fun_prop)).aestronglyMeasurable
      exact (h1.mul h2).mul h3
    · refine ⟨Cξ * CW * Cξ, fun p => ?_⟩
      have h1 : ‖ξ p.1‖ ≤ Cξ := hCξ p.1
      have h2 : ‖((W p.2 : ℝ) : ℂ)‖ ≤ CW := by simpa using hCW p.2
      have h3 : ‖ξ (p.1 + c - p.2)‖ ≤ Cξ := hCξ _
      calc ‖ξ p.1 * ((W p.2 : ℝ) : ℂ) * ξ (p.1 + c - p.2)‖
          = ‖ξ p.1‖ * ‖((W p.2 : ℝ) : ℂ)‖ * ‖ξ (p.1 + c - p.2)‖ := by rw [norm_mul, norm_mul]
        _ ≤ Cξ * CW * Cξ := by
              exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hCξnn) h3 (norm_nonneg _)
                (mul_nonneg hCξnn hCWnn)
    · intro p hp
      simp [hξs p.1 hp]
    · intro p hp
      simp [hWs p.2 hp, Complex.ofReal_zero]
  -- ## Step 1: inner substitution `y ↦ w + c - y`
  have hstep1 : (∫ w, ∫ y, ξ w * ((W (w - y + c) : ℝ) : ℂ) * ξ y)
      = ∫ w, ∫ y, ξ w * ((W y : ℝ) : ℂ) * ξ (w + c - y) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    beta_reduce
    rw [← integral_comp_const_sub (c := w + c)
      (f := fun z : E3 => ξ w * ((W z : ℝ) : ℂ) * ξ (w + c - z))]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    beta_reduce
    rw [sub_sub_cancel (w + c) y, sub_add_eq_add_sub w y c]
  -- ## Step 2: Fubini
  have hswap : (∫ w, ∫ y, ξ w * ((W y : ℝ) : ℂ) * ξ (w + c - y))
      = ∫ y, ∫ w, ξ w * ((W y : ℝ) : ℂ) * ξ (w + c - y) := by
    refine integral_integral_swap ?_
    exact hfint
  -- ## Step 3: inner substitution `w ↦ w - c`
  have hstep3 : (∫ y, ∫ w, ξ w * ((W y : ℝ) : ℂ) * ξ (w + c - y))
      = ∫ y, ∫ w, ξ (w - c) * ((W y : ℝ) : ℂ) * ξ (w - y) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    beta_reduce
    rw [← integral_add_right_eq_self (μ := (volume : Measure E3))
      (f := fun z : E3 => ξ (z - c) * ((W y : ℝ) : ℂ) * ξ (z - y)) c]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    beta_reduce
    rw [add_sub_cancel_right w c]
  -- ## Step 4: evenness `ξ (w - c) = ξ (c - w)`
  have hstep4 : (∫ y, ∫ w, ξ (w - c) * ((W y : ℝ) : ℂ) * ξ (w - y))
      = ∫ y, ∫ w, ((W y : ℝ) : ℂ) * ξ (c - w) * ξ (w - y) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    beta_reduce
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    beta_reduce
    rw [show w - c = -(c - w) by abel, hξe (c - w)]
    ring
  -- ## Step 5: commutative rearrangement of the two `ξ` factors
  have hstep5 : (∫ y, ∫ w, ((W y : ℝ) : ℂ) * ξ (c - w) * ξ (w - y))
      = ∫ y, ∫ x, ((W y : ℝ) : ℂ) * ξ (x - y) * ξ (c - x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    beta_reduce
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    beta_reduce
    ring
  calc (∫ w, ∫ y, ξ w * ((W (w - y + c) : ℝ) : ℂ) * ξ y)
      = ∫ w, ∫ y, ξ w * ((W y : ℝ) : ℂ) * ξ (w + c - y) := hstep1
    _ = ∫ y, ∫ w, ξ w * ((W y : ℝ) : ℂ) * ξ (w + c - y) := hswap
    _ = ∫ y, ∫ w, ξ (w - c) * ((W y : ℝ) : ℂ) * ξ (w - y) := hstep3
    _ = ∫ y, ∫ w, ((W y : ℝ) : ℂ) * ξ (c - w) * ξ (w - y) := hstep4
    _ = ∫ y, ∫ x, ((W y : ℝ) : ℂ) * ξ (x - y) * ξ (c - x) := hstep5

end Work.BoseBoxFock
