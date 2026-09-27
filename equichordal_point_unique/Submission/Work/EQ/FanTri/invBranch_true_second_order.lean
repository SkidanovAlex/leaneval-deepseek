import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.FanSep.Defs
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.FanSep.sqrt_step
import Submission.Work.EQ.FanTri.analytic_invBranch
import Submission.Work.EQ.FanTri.SecOrderDefs
import Submission.Work.EQ.FanTri.sR_sharp
import Submission.Work.EQ.FanTri.sR_lipschitz
import Submission.Work.EQ.FanTri.PhiT_coords
import Submission.Work.EQ.FanTri.facA_bounds
import Submission.Work.EQ.FanTri.facB_bounds

namespace Work.EQ.FanTri

open Work.EQ Complex Metric

noncomputable section

/-! ## Elementary values of the auxiliary quantities at the origin -/

lemma sD_zero (a : ℝ) : sD a (0 : ℂ × ℂ) = (sHat a : ℂ) := by
  simp [sD]

lemma sR_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : sR a 0 = (sHat a : ℂ) := by
  have hS : 0 < sHat a := sHat_pos ha1
  have hz : ‖(0 : ℂ × ℂ)‖ ≤ sHat a / 16 := by
    simp only [norm_zero]; positivity
  obtain ⟨-, -, -, -, hsqrt, -⟩ := sD_sR_setup ha0 ha1 hz
  rw [hsqrt, sD_zero, Prod.snd_zero, zero_div]
  simp [sqHalf_zero]

lemma facB_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    facB a 0 = (((sHat a)⁻¹ : ℝ) : ℂ) := by
  rw [facB, sR_zero ha0 ha1]
  exact (map_inv₀ (algebraMap ℝ ℂ) (sHat a)).symm

/-- Bookkeeping identity: the second-order remainder of the pair `(x,y)` is the remainder of
the shifted pair `(x-A₁, y-A₁)`. -/
theorem invBranch_sub_eq_PhiT (a : ℝ) (x y : ℂ × ℂ) :
    invBranch a true x - invBranch a true y - (-(x.1 - y.1), (x.2 - y.2) / (eqLam a : ℂ)) =
      PhiT a (x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))) -
        PhiT a (y - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))) := by
  unfold PhiT shiftA1
  ext <;> simp <;> ring

/-! ## Numeric cores of the two coordinate estimates -/

private lemma arith_A {S B A d : ℝ} (hS : 0 < S) (_hd : 0 ≤ d) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdB : d ≤ S / 16 * B) :
    B * A * (4 / S ^ 2) + d * (100 / S ^ 3 * A) ≤ 11 / S ^ 2 * (B * A) := by
  have hBA : 0 ≤ B * A := mul_nonneg hB hA
  have h1 : d * (100 / S ^ 3 * A) ≤ S / 16 * B * (100 / S ^ 3 * A) := by
    apply mul_le_mul_of_nonneg_right hdB
    positivity
  have h2 : S / 16 * B * (100 / S ^ 3 * A) = 100 / 16 / S ^ 2 * (B * A) := by
    field_simp
  have h3 : B * A * (4 / S ^ 2) = 4 / S ^ 2 * (B * A) := by ring
  have h4 : (4 : ℝ) / S ^ 2 + 100 / 16 / S ^ 2 ≤ 11 / S ^ 2 := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    norm_num
  nlinarith [h1, h2, h3, h4, hBA]

private lemma arith_B {S Z u B A : ℝ} (hS : 0 < S) (hA : 0 ≤ A) (hZu : Z + u ≤ B) :
    A * (100 / S ^ 3 * Z) + u * (100 / S ^ 3 * A) ≤ 100 / S ^ 3 * (B * A) := by
  have h1 : A * (100 / S ^ 3 * Z) + u * (100 / S ^ 3 * A) = 100 / S ^ 3 * (A * (Z + u)) := by
    ring
  rw [h1]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h2 : A * (Z + u) ≤ B * A := by
    calc A * (Z + u) ≤ A * B := mul_le_mul_of_nonneg_left hZu hA
      _ = B * A := by ring
  exact h2

/-! ## The two coordinate estimates -/

/-- First coordinate of the second-order remainder, `O((‖z‖+‖w‖)‖z-w‖)`. -/
lemma PhiT_fst_bound {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z w : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) (hw : ‖w‖ ≤ sHat a / 16) :
    ‖(PhiT a z).1 - (PhiT a w).1‖ ≤ 11 / sHat a ^ 2 * ((‖z‖ + ‖w‖) * ‖z - w‖) := by
  obtain ⟨-, -, hfz, -⟩ := PhiT_coords ha0 ha1 hz
  obtain ⟨-, -, hfw, -⟩ := PhiT_coords ha0 ha1 hw
  obtain ⟨hA1, hA2⟩ := facA_bounds ha0 ha1 hz hw
  have hS : 0 < sHat a := sHat_pos ha1
  have hquad : ‖z.2 ^ 2 - w.2 ^ 2‖ ≤ (‖z‖ + ‖w‖) * ‖z - w‖ := by
    have h1 : z.2 ^ 2 - w.2 ^ 2 = (z.2 - w.2) * (z.2 + w.2) := by ring
    rw [h1, norm_mul]
    calc ‖z.2 - w.2‖ * ‖z.2 + w.2‖ ≤ ‖z - w‖ * (‖z‖ + ‖w‖) := by
          apply mul_le_mul
          · have h2 : z.2 - w.2 = (z - w).2 := (Prod.snd_sub z w).symm
            rw [h2]
            exact norm_snd_le (z - w)
          · exact le_trans (norm_add_le _ _) (add_le_add (norm_snd_le z) (norm_snd_le w))
          · positivity
          · positivity
      _ = (‖z‖ + ‖w‖) * ‖z - w‖ := by ring
  have hw2 : ‖w.2 ^ 2‖ ≤ sHat a / 16 * (‖z‖ + ‖w‖) := by
    have hw2' : ‖w.2‖ ≤ sHat a / 16 := le_trans (norm_snd_le w) hw
    have h1 : ‖w.2 ^ 2‖ = ‖w.2‖ * ‖w.2‖ := by rw [norm_pow, pow_two]
    rw [h1]
    have h2 : ‖w.2‖ * ‖w.2‖ ≤ sHat a / 16 * ‖w.2‖ :=
      mul_le_mul_of_nonneg_right hw2' (norm_nonneg _)
    have h3 : sHat a / 16 * ‖w.2‖ ≤ sHat a / 16 * (‖z‖ + ‖w‖) :=
      mul_le_mul_of_nonneg_left
        (le_trans (norm_snd_le w) (le_add_of_nonneg_left (norm_nonneg z))) (by positivity)
    linarith
  have hkey : z.2 ^ 2 * facA a z - w.2 ^ 2 * facA a w
      = (z.2 ^ 2 - w.2 ^ 2) * facA a z + w.2 ^ 2 * (facA a z - facA a w) := by ring
  rw [hfz, hfw, hkey]
  calc ‖(z.2 ^ 2 - w.2 ^ 2) * facA a z + w.2 ^ 2 * (facA a z - facA a w)‖
      ≤ ‖(z.2 ^ 2 - w.2 ^ 2) * facA a z‖ + ‖w.2 ^ 2 * (facA a z - facA a w)‖ :=
        norm_add_le _ _
    _ ≤ ((‖z‖ + ‖w‖) * ‖z - w‖) * (4 / sHat a ^ 2) +
        (sHat a / 16 * (‖z‖ + ‖w‖)) * (100 / sHat a ^ 3 * ‖z - w‖) := by
        apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul hquad hA1 (norm_nonneg _) (by positivity)
        · rw [norm_mul]
          exact mul_le_mul hw2 hA2 (norm_nonneg _) (by positivity)
    _ ≤ 11 / sHat a ^ 2 * ((‖z‖ + ‖w‖) * ‖z - w‖) :=
        arith_A (sHat_pos ha1) (by positivity) (norm_nonneg _) (by positivity) le_rfl

/-- Second coordinate of the second-order remainder, `O((‖z‖+‖w‖)‖z-w‖)`. -/
lemma PhiT_snd_bound {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z w : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) (hw : ‖w‖ ≤ sHat a / 16) :
    ‖(PhiT a z).2 - (PhiT a w).2‖ ≤ 100 / sHat a ^ 3 * ((‖z‖ + ‖w‖) * ‖z - w‖) := by
  obtain ⟨-, -, -, hsz⟩ := PhiT_coords ha0 ha1 hz
  obtain ⟨-, -, -, hsw⟩ := PhiT_coords ha0 ha1 hw
  obtain ⟨-, hB⟩ := facB_bounds ha0 ha1 hz hw
  have hS : 0 < sHat a := sHat_pos ha1
  have hz0 : ‖(0 : ℂ × ℂ)‖ ≤ sHat a / 16 := by
    simp only [norm_zero]; positivity
  obtain ⟨-, hB0⟩ := facB_bounds ha0 ha1 hz hz0
  have hfac0 : facB a 0 = (((sHat a)⁻¹ : ℝ) : ℂ) := facB_zero ha0 ha1
  have hfacz : ‖facB a z - (((sHat a)⁻¹ : ℝ) : ℂ)‖ ≤ 100 / sHat a ^ 3 * ‖z‖ := by
    rw [← hfac0]
    calc ‖facB a z - facB a 0‖ ≤ 100 / sHat a ^ 3 * ‖z - 0‖ := hB0
      _ = 100 / sHat a ^ 3 * ‖z‖ := by rw [sub_zero]
  have hkey : z.2 * (facB a z - (((sHat a)⁻¹ : ℝ) : ℂ))
        - w.2 * (facB a w - (((sHat a)⁻¹ : ℝ) : ℂ))
      = (z.2 - w.2) * (facB a z - (((sHat a)⁻¹ : ℝ) : ℂ))
        + w.2 * (facB a z - facB a w) := by ring
  rw [hsz, hsw, hkey]
  calc ‖(z.2 - w.2) * (facB a z - (((sHat a)⁻¹ : ℝ) : ℂ))
          + w.2 * (facB a z - facB a w)‖
      ≤ ‖(z.2 - w.2) * (facB a z - (((sHat a)⁻¹ : ℝ) : ℂ))‖
          + ‖w.2 * (facB a z - facB a w)‖ := norm_add_le _ _
    _ ≤ ‖z - w‖ * (100 / sHat a ^ 3 * ‖z‖) + ‖w.2‖ * (100 / sHat a ^ 3 * ‖z - w‖) := by
        apply add_le_add
        · rw [norm_mul]
          refine mul_le_mul ?_ hfacz (by positivity) (norm_nonneg _)
          have h2 : z.2 - w.2 = (z - w).2 := (Prod.snd_sub z w).symm
          rw [h2]
          exact norm_snd_le _
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ ≤ 100 / sHat a ^ 3 * ((‖z‖ + ‖w‖) * ‖z - w‖) :=
        arith_B (sHat_pos ha1) (norm_nonneg _) (by linarith [norm_snd_le w])

/-- **The second-order remainder is `O((‖z‖+‖w‖)‖z-w‖)`.** -/
lemma PhiT_bound {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (z w : ℂ × ℂ)
    (hz : ‖z‖ ≤ sHat a / 16) (hw : ‖w‖ ≤ sHat a / 16) :
    ‖PhiT a z - PhiT a w‖ ≤ (200 / sHat a ^ 3 + 1) * (‖z‖ + ‖w‖) * ‖z - w‖ := by
  have hS : 0 < sHat a := sHat_pos ha1
  have h1 := PhiT_fst_bound ha0 ha1 hz hw
  have h2 := PhiT_snd_bound ha0 ha1 hz hw
  have hmax : ‖PhiT a z - PhiT a w‖ ≤
      max (11 / sHat a ^ 2 * ((‖z‖ + ‖w‖) * ‖z - w‖))
        (100 / sHat a ^ 3 * ((‖z‖ + ‖w‖) * ‖z - w‖)) := by
    rw [Prod.norm_def]
    apply max_le
    · rw [Prod.fst_sub]; exact le_trans h1 (le_max_left _ _)
    · rw [Prod.snd_sub]; exact le_trans h2 (le_max_right _ _)
  have hBA : (0 : ℝ) ≤ (‖z‖ + ‖w‖) * ‖z - w‖ := by positivity
  refine le_trans hmax (max_le ?_ ?_)
  · have hS1 : sHat a ≤ 1 / 2 := sHat_le_half ha0 ha1
    have h3 : 11 / sHat a ^ 2 ≤ 200 / sHat a ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : 11 * sHat a ^ 3 ≤ 11 * (1 / 2) * sHat a ^ 2 := by
        calc 11 * sHat a ^ 3 = 11 * sHat a ^ 2 * sHat a := by ring
          _ ≤ 11 * sHat a ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left hS1 (by positivity)
          _ = 11 * (1 / 2) * sHat a ^ 2 := by ring
      nlinarith [h4, sq_nonneg (sHat a)]
    calc 11 / sHat a ^ 2 * ((‖z‖ + ‖w‖) * ‖z - w‖)
        ≤ (200 / sHat a ^ 3 + 1) * ((‖z‖ + ‖w‖) * ‖z - w‖) :=
          mul_le_mul_of_nonneg_right (by linarith) hBA
      _ = (200 / sHat a ^ 3 + 1) * (‖z‖ + ‖w‖) * ‖z - w‖ := by ring
  · have hS3 : (0 : ℝ) < sHat a ^ 3 := by positivity
    have h3 : 100 / sHat a ^ 3 ≤ 200 / sHat a ^ 3 + 1 := by
      have h4 : 100 / sHat a ^ 3 ≤ 200 / sHat a ^ 3 :=
        div_le_div_of_nonneg_right (by norm_num) hS3.le
      linarith
    calc 100 / sHat a ^ 3 * ((‖z‖ + ‖w‖) * ‖z - w‖)
        ≤ (200 / sHat a ^ 3 + 1) * ((‖z‖ + ‖w‖) * ‖z - w‖) :=
          mul_le_mul_of_nonneg_right h3 hBA
      _ = (200 / sHat a ^ 3 + 1) * (‖z‖ + ‖w‖) * ‖z - w‖ := by ring

/-- **Second-order expansion of the principal inverse branch at `A₁ = (-1/2,0)`.**  Near `A₁`
the map `invBranch a true` differs from the linear map `L(δ₁,δ₂) = (-δ₁, δ₂/λ)` by
`O((‖x-A₁‖+‖y-A₁‖)‖x-y‖)`; the derivatives are `∂₁ = -1`, `∂₂ = 0` in the first coordinate
and `∂₂ = 1/λ = (1+a)/(1-a)` in the second.  It suffices to prove the one-point form
`‖invBranch a true (A₁+z) - A₁ - (-(z.1), z.2/λ)‖ ≤ N ‖z‖ ^ 2`, since
`G x - G y - L(x-y) = [G x - G A₁ - L(x-A₁)] - [G y - G A₁ - L(y-A₁)]`.  Algebraically, with
`D = s - z₁` (`s = (1-a)/2 > 0`) and `ρ = (D ^ 2 + z₂ ^ 2) ^ (1/2) = D * sqHalf ((z₂/D)^2)`
(`FanSep.sqrt_step`), the first coordinate is `-z₁ + (1 - 1/S)` with `S = sqHalf ((z₂/D)^2)`
and `FanSep.norm_inv_sqHalf_sub_one_le_aux` bounds `1 - 1/S` by `O(‖z‖ ^ 2)`. -/
theorem invBranch_true_second_order {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ ρ N : ℝ, 0 < ρ ∧ 0 < N ∧ ∀ x y : ℂ × ℂ,
      ‖x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ →
      ‖y - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ ≤ ρ →
      ‖Work.EQ.invBranch a true x - Work.EQ.invBranch a true y -
        ( (-(x.1 - y.1)), (x.2 - y.2) / (Work.EQ.eqLam a : ℂ) )‖ ≤
        N * (‖x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖ +
             ‖y - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))‖) * ‖x - y‖ := by
  have hS : 0 < sHat a := sHat_pos ha1
  refine ⟨sHat a / 16, 200 / sHat a ^ 3 + 1, by positivity, by positivity, ?_⟩
  intro x y hx hy
  rw [invBranch_sub_eq_PhiT a x y]
  have hb := PhiT_bound ha0 ha1 (x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)))
    (y - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))) hx hy
  have hsub : (x - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ))) - (y - (((-1 / 2 : ℝ) : ℂ), (0 : ℂ)))
      = x - y := by
    rw [sub_sub_sub_cancel_right]
  rwa [hsub] at hb

end

end Work.EQ.FanTri
