import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Order.Group.Lattice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2

open MeasureTheory

/-- Cauchy–Schwarz in the `L²` form used for Schur-type estimates:
`∫ |A| * |B| ≤ √(∫ A²) * √(∫ B²)`. -/
lemma abs_integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {A B : α → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA2 : Integrable (fun a => A a ^ 2) μ) (hB2 : Integrable (fun a => B a ^ 2) μ) :
    ∫ a, |A a| * |B a| ∂μ ≤ Real.sqrt (∫ a, A a ^ 2 ∂μ) * Real.sqrt (∫ a, B a ^ 2 ∂μ) := by
  have hmA : MemLp (fun a => |A a|) 2 μ := by
    rw [memLp_two_iff_integrable_sq]
    · simpa [sq_abs] using hA2
    · exact hAm.abs.aestronglyMeasurable
  have hmB : MemLp (fun a => |B a|) 2 μ := by
    rw [memLp_two_iff_integrable_sq]
    · simpa [sq_abs] using hB2
    · exact hBm.abs.aestronglyMeasurable
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (Real.HolderConjugate.two_two)
      (ae_of_all _ fun a => abs_nonneg _) (ae_of_all _ fun a => abs_nonneg _)
      (by simpa using hmA) (by simpa using hmB)
  have e1 : (∫ a, |A a| ^ (2:ℝ) ∂μ) = ∫ a, A a ^ 2 ∂μ :=
    integral_congr_ae (ae_of_all _ fun a => by simp only [Real.rpow_two, sq_abs])
  have e2 : (∫ a, |B a| ^ (2:ℝ) ∂μ) = ∫ a, B a ^ 2 ∂μ :=
    integral_congr_ae (ae_of_all _ fun a => by simp only [Real.rpow_two, sq_abs])
  rw [e1, e2] at h
  simp only [← Real.sqrt_eq_rpow] at h
  exact h

theorem weight_diff_integral_le {Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) (p : ℝ × ℝ) :
    |∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ 2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1) * Real.exp (Cw * (|p.1| + |p.2|))
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by
  set θ : ℝ := Cw * (|p.1| + |p.2|) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hexp1 : 0 ≤ Real.exp θ - 1 := by
    have := Real.one_le_exp hθ0; linarith
  have he2 : 1 ≤ 2 * Real.exp θ := by
    have := Real.one_le_exp hθ0; linarith
  have hs1 : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2) := Real.sqrt_nonneg _
  have hs2 : 0 ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := Real.sqrt_nonneg _
  have hD : 0 ≤ (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
      * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)) := mul_nonneg hexp1 (mul_nonneg hs1 hs2)
  -- the two-sided comparability of `Q` under the shift `p`
  have hle : ∀ y, Q (y - p) ≤ Real.exp θ * Q y := by
    intro y
    have h := hQsh y (-p)
    rw [sub_eq_add_neg]
    simpa [hθ] using h
  have hge : ∀ y, Q y ≤ Real.exp θ * Q (y - p) := by
    intro y
    have h := hQsh' y (-p)
    rw [sub_eq_add_neg]
    simpa [hθ] using h
  let A : ℝ × ℝ → ℝ := fun y => Real.sqrt (Q y) * G₂ y
  let B : ℝ × ℝ → ℝ := fun y => Real.sqrt (Q (y - p)) * G₁ (y - p)
  have hsub : Measurable (fun y : ℝ × ℝ => y - p) := measurable_id.sub measurable_const
  have hAm : Measurable A := hQm.sqrt.mul hG2m
  have hBm : Measurable B := (hQm.comp hsub).sqrt.mul (hG1m.comp hsub)
  -- pointwise bound on the weight difference
  have hpt : ∀ y : ℝ × ℝ,
      |Q y - Q (y - p)| ≤ (Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p)) := by
    intro y
    have hX : 0 ≤ Q y := hQ0 y
    have hY : 0 ≤ Q (y - p) := hQ0 _
    have h1 : Q y ≤ Real.exp θ * Q (y - p) := hge y
    have h2 : Q (y - p) ≤ Real.exp θ * Q y := hle y
    have hmin : |Q y - Q (y - p)| ≤ (Real.exp θ - 1) * min (Q y) (Q (y - p)) := by
      rcases le_total (Q (y - p)) (Q y) with h | h
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]
        nlinarith [h1]
      · rw [min_eq_left h, abs_of_nonpos (by linarith), neg_sub]
        nlinarith [h2]
    have hmin2 : min (Q y) (Q (y - p)) ≤ Real.sqrt (Q y * Q (y - p)) := by
      rcases le_total (Q y) (Q (y - p)) with h | h
      · calc min (Q y) (Q (y - p)) = Q y := min_eq_left h
          _ = Real.sqrt (Q y * Q y) := (Real.sqrt_mul_self hX).symm
          _ ≤ Real.sqrt (Q y * Q (y - p)) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h hX)
      · calc min (Q y) (Q (y - p)) = Q (y - p) := min_eq_right h
          _ = Real.sqrt (Q (y - p) * Q (y - p)) := (Real.sqrt_mul_self hY).symm
          _ ≤ Real.sqrt (Q y * Q (y - p)) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right h hY)
    calc |Q y - Q (y - p)| ≤ (Real.exp θ - 1) * min (Q y) (Q (y - p)) := hmin
      _ ≤ (Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p)) := mul_le_mul_of_nonneg_left hmin2 hexp1
  -- pointwise bound on the full integrand
  have hfpt : ∀ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ (Real.exp θ - 1) * (|Real.sqrt (Q y) * G₂ y| * |Real.sqrt (Q (y - p)) * G₁ (y - p)|) := by
    intro y
    have h1 := hpt y
    have hs : Real.sqrt (Q y * Q (y - p)) = Real.sqrt (Q y) * Real.sqrt (Q (y - p)) :=
      Real.sqrt_mul (hQ0 y) (Q (y - p))
    have hg1 : 0 ≤ |G₁ (y - p)| := abs_nonneg _
    have hg2 : 0 ≤ |G₂ y| := abs_nonneg _
    have hstep : |Q y - Q (y - p)| * |G₁ (y - p)| * |G₂ y|
        ≤ (Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p)) * |G₁ (y - p)| * |G₂ y| := by
      calc |Q y - Q (y - p)| * |G₁ (y - p)| * |G₂ y|
          = |Q y - Q (y - p)| * (|G₁ (y - p)| * |G₂ y|) := by ring
        _ ≤ ((Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p))) * (|G₁ (y - p)| * |G₂ y|) :=
            mul_le_mul_of_nonneg_right h1 (mul_nonneg hg1 hg2)
        _ = (Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p)) * |G₁ (y - p)| * |G₂ y| := by ring
    calc |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
        = |Q y - Q (y - p)| * |G₁ (y - p)| * |G₂ y| := by rw [abs_mul, abs_mul]
      _ ≤ (Real.exp θ - 1) * Real.sqrt (Q y * Q (y - p)) * |G₁ (y - p)| * |G₂ y| := hstep
      _ = (Real.exp θ - 1) *
            (|Real.sqrt (Q y) * G₂ y| * |Real.sqrt (Q (y - p)) * G₁ (y - p)|) := by
          rw [hs, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (Q y)),
            abs_of_nonneg (Real.sqrt_nonneg (Q (y - p)))]
          ring
  have hA2 : Integrable (fun y : ℝ × ℝ => A y ^ 2) := by
    refine hI2.congr ?_
    filter_upwards with y
    simp [A, mul_pow, Real.sq_sqrt (hQ0 y)]
  have hB2 : Integrable (fun y : ℝ × ℝ => B y ^ 2) := by
    refine (hI1.comp_sub_right p).congr ?_
    filter_upwards with y
    simp [B, mul_pow, Real.sq_sqrt (hQ0 (y - p))]
  have hABint : Integrable (fun y : ℝ × ℝ => |A y| * |B y|) := by
    refine Integrable.mono' ((hA2.add hB2).div_const 2)
      ((hAm.abs).mul (hBm.abs)).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (by positivity)]
    change |A y| * |B y| ≤ (A y ^ 2 + B y ^ 2) / 2
    have hsq : A y ^ 2 = |A y| ^ 2 := (sq_abs (A y)).symm
    have hsq2 : B y ^ 2 = |B y| ^ 2 := (sq_abs (B y)).symm
    rw [hsq, hsq2]
    nlinarith [sq_nonneg (|A y| - |B y|)]
  have hCS := abs_integral_mul_le_sqrt_mul_sqrt (volume : Measure (ℝ × ℝ)) hAm hBm hA2 hB2
  have eA : (∫ y : ℝ × ℝ, A y ^ 2) = ∫ y : ℝ × ℝ, Q y * G₂ y ^ 2 :=
    integral_congr_ae (by filter_upwards with y; simp [A, mul_pow, Real.sq_sqrt (hQ0 y)])
  have eB : (∫ y : ℝ × ℝ, B y ^ 2) = ∫ y : ℝ × ℝ, Q y * G₁ y ^ 2 := by
    have h1 : (∫ y : ℝ × ℝ, B y ^ 2) = ∫ y : ℝ × ℝ, Q (y - p) * G₁ (y - p) ^ 2 :=
      integral_congr_ae (by
        filter_upwards with y
        simp [B, mul_pow, Real.sq_sqrt (hQ0 (y - p))])
    rw [h1, integral_sub_right_eq_self (fun u : ℝ × ℝ => Q u * G₁ u ^ 2) p]
  have hmain : ∫ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)) := by
    calc ∫ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
        ≤ ∫ y : ℝ × ℝ, (Real.exp θ - 1) * (|A y| * |B y|) := by
          refine integral_mono_of_nonneg
            (f := fun y : ℝ × ℝ => |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y|)
            (g := fun y : ℝ × ℝ => (Real.exp θ - 1) * (|A y| * |B y|)) ?_ ?_ ?_
          · exact Filter.Eventually.of_forall (fun y => abs_nonneg _)
          · exact hABint.const_mul (Real.exp θ - 1)
          · exact Filter.Eventually.of_forall (fun y => hfpt y)
      _ = (Real.exp θ - 1) * ∫ y : ℝ × ℝ, |A y| * |B y| := integral_const_mul _ _
      _ ≤ (Real.exp θ - 1) *
            (Real.sqrt (∫ y : ℝ × ℝ, A y ^ 2) * Real.sqrt (∫ y : ℝ × ℝ, B y ^ 2)) :=
          mul_le_mul_of_nonneg_left hCS hexp1
      _ = (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)) := by
          rw [eA, eB]; ring
  have hfinal : (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
        * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2))
      ≤ 2 * (Real.exp θ - 1) * Real.exp θ * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by
    calc (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2))
        = 1 * ((Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2))) := by ring
      _ ≤ (2 * Real.exp θ) * ((Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2))) :=
            mul_le_mul_of_nonneg_right he2 hD
      _ = 2 * (Real.exp θ - 1) * Real.exp θ * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
            * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by ring
  calc |∫ y : ℝ × ℝ, (Q y - Q (y - p)) * G₁ (y - p) * G₂ y|
      ≤ ∫ y : ℝ × ℝ, |(Q y - Q (y - p)) * G₁ (y - p) * G₂ y| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ (Real.exp θ - 1) * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)) := hmain
    _ ≤ 2 * (Real.exp θ - 1) * Real.exp θ * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := hfinal
    _ = 2 * (Real.exp (Cw * (|p.1| + |p.2|)) - 1) * Real.exp (Cw * (|p.1| + |p.2|))
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2) := by rw [hθ]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2
