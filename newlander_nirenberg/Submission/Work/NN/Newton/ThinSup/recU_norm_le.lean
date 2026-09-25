import Mathlib
import Submission.Work.NN.Ratio.Defs
import Submission.Work.CR.Flat.Cauchy.openSolDefs
import Submission.Work.CR.Flat.Cauchy.integral_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

namespace Work.NN.Newton.ThinSup

open scoped NNReal ENNReal ContDiff
open Set MeasureTheory Filter
open Work.NN.Ratio

/-- Sup-norm bound for the one-variable Cauchy-type transform: if `‖g‖ ≤ A` everywhere then
`‖dbarTransform ρ j g z‖ ≤ 2 ρ A`.  Directly from
`dbarTransform ρ j g z = -(π)⁻¹ ∫_{‖w‖<ρ} g (z + w e_j)/w dw` and
`∫_{‖w‖<ρ} ‖w‖⁻¹ = 2πρ` (the case `s = -1` of `integral_norm_rpow_ball`).  No continuity,
measurability, closedness or support hypothesis on `g` is needed. -/
theorem dbarTransform_norm_le_aux {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (j : Fin n)
    {g : (Fin n → ℂ) → ℂ} {A : ℝ} (hA : 0 ≤ A) (hg : ∀ y, ‖g y‖ ≤ A) (z : Fin n → ℂ) :
    ‖Work.CR.Flat.Cauchy.dbarTransform ρ j g z‖ ≤ 2 * ρ * A := by
  have hmaj : IntegrableOn (fun w : ℂ => A * ‖w‖ ^ (-1 : ℝ)) (Metric.ball (0 : ℂ) ρ) :=
    (Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball (ρ := ρ) (s := -1)
      (by norm_num)).const_mul A
  have hpt : ∀ w : ℂ,
      ‖g (z + Function.update (0 : Fin n → ℂ) j w) / w‖ ≤ A * ‖w‖ ^ (-1 : ℝ) := by
    intro w
    rw [norm_div]
    calc ‖g (z + Function.update (0 : Fin n → ℂ) j w)‖ / ‖w‖ ≤ A / ‖w‖ :=
          div_le_div_of_nonneg_right (hg _) (norm_nonneg w)
      _ = A * ‖w‖ ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
  have hbound : ‖∫ w in Metric.ball (0 : ℂ) ρ,
        g (z + Function.update (0 : Fin n → ℂ) j w) / w‖ ≤
      ∫ w in Metric.ball (0 : ℂ) ρ, A * ‖w‖ ^ (-1 : ℝ) :=
    norm_integral_le_of_norm_le hmaj (Eventually.of_forall hpt)
  have hval : (∫ w in Metric.ball (0 : ℂ) ρ, A * ‖w‖ ^ (-1 : ℝ)) = A * (2 * Real.pi * ρ) := by
    rw [integral_const_mul,
      Work.CR.Flat.Cauchy.integral_norm_rpow_ball hρ (by norm_num : (-2 : ℝ) < -1)]
    rw [show (-1 : ℝ) + 2 = 1 by norm_num, Real.rpow_one, div_one]
  have hpi : ‖((Real.pi : ℂ))⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hpi2 : Real.pi⁻¹ * (2 * Real.pi) = 2 := by
    rw [mul_comm (2 : ℝ) Real.pi, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  simp only [Work.CR.Flat.Cauchy.dbarTransform, norm_mul, norm_neg]
  rw [hpi]
  calc Real.pi⁻¹ * ‖∫ w in Metric.ball (0 : ℂ) ρ,
        g (z + Function.update (0 : Fin n → ℂ) j w) / w‖
      ≤ Real.pi⁻¹ * (A * (2 * Real.pi * ρ)) :=
        mul_le_mul_of_nonneg_left (le_trans hbound (le_of_eq hval)) (by positivity)
    _ = 2 * ρ * A := by
        rw [show Real.pi⁻¹ * (A * (2 * Real.pi * ρ))
            = (Real.pi⁻¹ * (2 * Real.pi)) * (A * ρ) by ring, hpi2]
        ring

/-- Sup-norm bound for the telescoping solution operator `G.recU`: if all components of the datum
are bounded by `A`, then `‖G.recU g z‖ ≤ n · 2 G.r · (max 1 (2 G.r G.cχ)) ^ n · A` for every `z`.
This is the iteration of the auxiliary bound
`‖dbarTransform ρ j g z‖ ≤ 2 ρ sup‖g‖` (`ρ > 0`, from `∫_{‖w‖<ρ} ‖w‖⁻¹ = 2πρ`) along the `n`
stages of the recursion: each stage multiplies the sup bound by `2 G.r · G.cχ`, and the final sum
over the `n` coordinates costs the factor `n · 2 G.r`.  Requires no smoothness, closedness or
finiteness: it is the triangle inequality plus the `L¹` bound of the Cauchy kernel. -/
theorem recU_norm_le {n : ℕ} (G : Work.NN.Ratio.Geom n) {g : Fin n → (Fin n → ℂ) → ℂ} {A : ℝ}
    (hA : 0 ≤ A) (hg : ∀ j y, ‖g j y‖ ≤ A) (z : Fin n → ℂ) :
    ‖G.recU g z‖ ≤ (n : ℝ) * (2 * G.r) * (max 1 (2 * G.r * G.cχ)) ^ n * A := by
  set X : ℝ := max 1 (2 * G.r * G.cχ) with hX
  have hX1 : 1 ≤ X := le_max_left _ _
  have hX0 : 0 ≤ X := le_trans zero_le_one hX1
  have hXr : 2 * G.r * G.cχ ≤ X := le_max_right _ _
  -- Uniform bound on every stage of the recursion.
  have key : ∀ m : ℕ, ∀ k : Fin n, ∀ y : Fin n → ℂ, ‖G.recF g m k y‖ ≤ X ^ m * A := by
    intro m
    induction m with
    | zero =>
        intro k y
        rw [Geom.recF_zero]
        simpa using hg k y
    | succ m ih =>
        intro k y
        by_cases hlt : m < n
        · have hrec : G.recF g (m + 1) = G.stepData ⟨m, hlt⟩ (G.recF g m) :=
            Geom.recF_succ_of_lt (G := G) hlt
          have hstep : G.recF g (m + 1) k y =
              Work.CR.Flat.Cauchy.dbarTransform G.r ⟨m, hlt⟩
                (fun y' => G.cutFbar ⟨m, hlt⟩ y' * G.recF g m k y') y := by
            rw [hrec]; rfl
          rw [hstep]
          have hA' : 0 ≤ G.cχ * (X ^ m * A) :=
            mul_nonneg G.hcχ0 (mul_nonneg (pow_nonneg hX0 m) hA)
          have hbnd : ∀ y' : Fin n → ℂ,
              ‖G.cutFbar ⟨m, hlt⟩ y' * G.recF g m k y'‖ ≤ G.cχ * (X ^ m * A) := by
            intro y'
            rw [norm_mul]
            exact mul_le_mul (Geom.norm_cutFbar_le (G := G) _ y') (ih k y')
              (norm_nonneg _) G.hcχ0
          have htr := dbarTransform_norm_le_aux (n := n) G.hr0 ⟨m, hlt⟩ hA' hbnd y
          calc ‖Work.CR.Flat.Cauchy.dbarTransform G.r ⟨m, hlt⟩
                  (fun y' => G.cutFbar ⟨m, hlt⟩ y' * G.recF g m k y') y‖
              ≤ 2 * G.r * (G.cχ * (X ^ m * A)) := htr
            _ = (2 * G.r * G.cχ) * (X ^ m * A) := by ring
            _ ≤ X * (X ^ m * A) :=
                mul_le_mul_of_nonneg_right hXr (mul_nonneg (pow_nonneg hX0 m) hA)
            _ = X ^ (m + 1) * A := by rw [pow_succ]; ring
        · have hrec : G.recF g (m + 1) = G.recF g m := by
            rw [Geom.recF_succ (G := G)]
            exact dite_eq_right (not_lt.mpr (not_lt.mp hlt))
          rw [hrec]
          calc ‖G.recF g m k y‖ ≤ X ^ m * A := ih k y
            _ ≤ X ^ (m + 1) * A :=
                mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hX1 (Nat.le_succ m)) hA
  rw [show G.recU g z = ∑ j : Fin n, Work.CR.Flat.Cauchy.dbarTransform G.r j
      (fun y => G.cutF j y * G.recF g (j : ℕ) j y) z from rfl]
  have hterm : ∀ j : Fin n,
      ‖Work.CR.Flat.Cauchy.dbarTransform G.r j
        (fun y => G.cutF j y * G.recF g (j : ℕ) j y) z‖ ≤ 2 * G.r * (X ^ n * A) := by
    intro j
    have hA' : 0 ≤ X ^ (j : ℕ) * A := mul_nonneg (pow_nonneg hX0 _) hA
    have hbnd : ∀ y : Fin n → ℂ, ‖G.cutF j y * G.recF g (j : ℕ) j y‖ ≤ X ^ (j : ℕ) * A := by
      intro y
      rw [norm_mul]
      calc ‖G.cutF j y‖ * ‖G.recF g (j : ℕ) j y‖ ≤ 1 * (X ^ (j : ℕ) * A) :=
            mul_le_mul (Geom.norm_cutF_le_one (G := G) j y) (key (j : ℕ) j y)
              (norm_nonneg _) zero_le_one
        _ = X ^ (j : ℕ) * A := one_mul _
    have htr := dbarTransform_norm_le_aux (n := n) G.hr0 j hA' hbnd z
    refine le_trans htr ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hX1 (Nat.le_of_lt j.isLt)) hA)
      (by linarith [G.hr0])
  calc ‖∑ j : Fin n, Work.CR.Flat.Cauchy.dbarTransform G.r j
          (fun y => G.cutF j y * G.recF g (j : ℕ) j y) z‖
      ≤ ∑ j : Fin n, ‖Work.CR.Flat.Cauchy.dbarTransform G.r j
          (fun y => G.cutF j y * G.recF g (j : ℕ) j y) z‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, 2 * G.r * (X ^ n * A) := Finset.sum_le_sum (fun j _ => hterm j)
    _ = (n : ℝ) * (2 * G.r) * X ^ n * A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Work.NN.Newton.ThinSup
