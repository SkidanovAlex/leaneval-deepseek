/-
# The bilinear window sum limit

`Work.KMTPlan.A6.BileWindowSumLimit`: as `R → ∞`,

  `R⁻¹ · ∑'_n g(n/R) · w(n mod Q)  ⟶  Q⁻¹ · ∑_z w z`,

for `w : ZMod Q → ℝ` and `g : ℝ → ℝ` a `W^{1,1}` function with `∫ g = 1`.

The proof is a Riemann-sum argument.  Writing `n = m·Q + z.val` for the residue class
`z : ZMod Q` of `n` (bijection `ZMod Q × ℤ ≃ ℤ`, `sum_int_eq_sum_zmod_mul`), the sum becomes

  `∑_z w z · ∑_m g(((m + z.val/Q)·h))`,   `h = Q/R`,

and for every fixed shift `a` the lattice sum `h · ∑_m g((m+a)h)` tends to `∫ g` with
error at most `h · ∫‖g'‖` (`latticeSum_bound`).  Summing over the `Q` residue classes with the
positive weights `w z` and using `∫ g = 1` gives an error at most
`(∑_z w z) · (∫‖g'‖) / R → 0` (`W := ∑_z w z` in the proof).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.latticeSum_bound
import Submission.Work.KMTPlan.A6.sum_int_eq_sum_zmod_mul

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

theorem BileWindowSumLimit
    {g : ℝ → ℝ} (hd : Differentiable ℝ g) (hg : MeasureTheory.Integrable g)
    (hg' : MeasureTheory.Integrable (deriv g))
    (hg1 : ∫ t : ℝ, g t = 1)
    {Q : ℕ} [NeZero Q] (hQ : 1 ≤ Q) (w : ZMod Q → ℝ) (hw : ∀ z : ZMod Q, 0 ≤ w z) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      |(R : ℝ)⁻¹ * (∑' n : ℤ, g ((n : ℝ) / (R : ℝ)) * w (n : ZMod Q))
        - (Q : ℝ)⁻¹ * (∑ z : ZMod Q, w z)| ≤ ε := by
  intro ε hε
  set W : ℝ := ∑ z : ZMod Q, w z with hWdef
  obtain ⟨R₀, hR₀⟩ := exists_nat_ge (W * (∫ t : ℝ, ‖deriv g t‖) / ε)
  refine ⟨max 1 R₀, fun R hR => ?_⟩
  have hRnat : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hRge : W * (∫ t : ℝ, ‖deriv g t‖) / ε ≤ (R : ℝ) :=
    le_trans hR₀ (le_trans (Nat.cast_le.mpr (le_max_right _ _)) (Nat.cast_le.mpr hR))
  have hQpos : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hQ)
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hRnat)
  have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRpos
  set h : ℝ := (Q : ℝ) / (R : ℝ) with hhdef
  have hhpos : 0 < h := div_pos hQpos hRpos
  -- the lattice-sum estimate at the shift of each residue class
  have hSz : ∀ z : ZMod Q,
      |(∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h) * h) - ∫ t : ℝ, g t|
        ≤ h * ∫ t : ℝ, ‖deriv g t‖ := by
    intro z
    have hA := latticeSum_bound hd hg hg' ((z.val : ℝ) / (Q : ℝ)) hhpos
    exact hA.2.2
  have hST : ∀ z : ZMod Q,
      (∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h) * h)
        = (∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h)) * h := by
    intro z
    exact tsum_mul_right
  -- summability of the shifted lattice sums, and of the weighted series over `ℤ`
  have hsumm_unshift : Summable (fun n : ℤ => g ((n : ℝ) / (R : ℝ))) := by
    have hA := (latticeSum_bound hd hg hg' 0 (h := (R : ℝ)⁻¹) (inv_pos.mpr hRpos)).1
    simpa [div_eq_mul_inv] using hA
  have hsummF : Summable (fun n : ℤ => g ((n : ℝ) / (R : ℝ)) * w (n : ZMod Q)) := by
    have hnorm : Summable (fun n : ℤ => ‖g ((n : ℝ) / (R : ℝ))‖) := hsumm_unshift.norm
    have hmaj : Summable (fun n : ℤ => W * ‖g ((n : ℝ) / (R : ℝ))‖) := Summable.mul_left W hnorm
    refine hmaj.of_norm_bounded (fun n => ?_)
    have hle : ‖w ((n : ℤ) : ZMod Q)‖ ≤ W := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw _), hWdef]
      exact Finset.single_le_sum (fun z _ => hw z) (Finset.mem_univ _)
    rw [norm_mul, mul_comm W]
    exact mul_le_mul_of_nonneg_left hle (norm_nonneg _)
  -- splitting the series into residue classes modulo `Q`
  have hdecomp : (∑' n : ℤ, g ((n : ℝ) / (R : ℝ)) * w (n : ZMod Q))
      = ∑ z : ZMod Q, (∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h)) * w z := by
    rw [sum_int_eq_sum_zmod_mul Q (fun n : ℤ => g ((n : ℝ) / (R : ℝ)) * w (n : ZMod Q)) hsummF]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    have h1 : (∑' m : ℤ, g ((((m : ℤ) * Q + z.val : ℤ) : ℝ) / (R : ℝ))
          * w ((((m : ℤ) * Q + z.val : ℤ)) : ZMod Q))
        = ∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h) * w z :=
      tsum_congr (fun m => by
        rw [show ((((m : ℤ) * Q + z.val : ℤ)) : ZMod Q) = z from by push_cast; simp,
            show ((((m : ℤ) * Q + z.val : ℤ) : ℝ) / (R : ℝ))
              = ((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h from by
              rw [hhdef]; push_cast; field_simp])
    rw [h1]
    exact tsum_mul_right
  have hkey : (Q : ℝ)⁻¹ * h = (R : ℝ)⁻¹ := by rw [hhdef]; field_simp
  have hmain : (R : ℝ)⁻¹ * (∑' n : ℤ, g ((n : ℝ) / (R : ℝ)) * w (n : ZMod Q))
      = (Q : ℝ)⁻¹ * ∑ z : ZMod Q,
          w z * (∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h) * h) := by
    rw [hdecomp, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [hST z, ← hkey]
    ring
  have hdiff : (R : ℝ)⁻¹ * (∑' n : ℤ, g ((n : ℝ) / (R : ℝ)) * w (n : ZMod Q))
      - (Q : ℝ)⁻¹ * (∑ z : ZMod Q, w z)
      = (Q : ℝ)⁻¹ * ∑ z : ZMod Q,
          w z * ((∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h) * h) - ∫ t : ℝ, g t) := by
    rw [hmain, ← mul_sub, hg1]
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun z _ => by ring)
  have hbound : |(Q : ℝ)⁻¹ * ∑ z : ZMod Q,
        w z * ((∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h) * h) - ∫ t : ℝ, g t)|
      ≤ (Q : ℝ)⁻¹ * (W * (h * ∫ t : ℝ, ‖deriv g t‖)) := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hQpos.le)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hQpos.le)
    calc |∑ z : ZMod Q, w z * ((∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h) * h) - ∫ t : ℝ, g t)|
        ≤ ∑ z : ZMod Q, |w z * ((∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h) * h) - ∫ t : ℝ, g t)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ z : ZMod Q, |w z| * |(∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h) * h) - ∫ t : ℝ, g t| := by
          simp only [abs_mul]
      _ = ∑ z : ZMod Q, w z * |(∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h) * h) - ∫ t : ℝ, g t| :=
          Finset.sum_congr rfl (fun z _ => by rw [abs_of_nonneg (hw z)])
      _ ≤ ∑ z : ZMod Q, w z * (h * ∫ t : ℝ, ‖deriv g t‖) :=
          Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hSz z) (hw z))
      _ = W * (h * ∫ t : ℝ, ‖deriv g t‖) := by rw [hWdef, Finset.sum_mul]
  have hscale : (Q : ℝ)⁻¹ * (W * (h * ∫ t : ℝ, ‖deriv g t‖))
      = W * (∫ t : ℝ, ‖deriv g t‖) / (R : ℝ) := by
    rw [hhdef]; field_simp
  calc |(R : ℝ)⁻¹ * (∑' n : ℤ, g ((n : ℝ) / (R : ℝ)) * w (n : ZMod Q))
        - (Q : ℝ)⁻¹ * (∑ z : ZMod Q, w z)|
      = |(Q : ℝ)⁻¹ * ∑ z : ZMod Q,
          w z * ((∑' m : ℤ, g (((m : ℝ) + (z.val : ℝ) / (Q : ℝ)) * h) * h) - ∫ t : ℝ, g t)| := by
        rw [hdiff]
    _ ≤ (Q : ℝ)⁻¹ * (W * (h * ∫ t : ℝ, ‖deriv g t‖)) := hbound
    _ = W * (∫ t : ℝ, ‖deriv g t‖) / (R : ℝ) := hscale
    _ ≤ ε := by
          rw [div_le_iff₀ hRpos]
          have hmul : W * (∫ t : ℝ, ‖deriv g t‖) ≤ (R : ℝ) * ε := by
            have h1 := mul_le_mul_of_nonneg_right hRge hε.le
            rwa [div_mul_cancel₀ _ (ne_of_gt hε)] at h1
          linarith [hmul]

end Work.KMTPlan.A6
