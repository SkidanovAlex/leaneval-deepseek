import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.wtE_shift_le
import Submission.Work.FTS.StrongEps.sinTwo_thShift_bounds
import Submission.Work.FTS.StrongEps.Weights

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

/-!
# `Submission/Work/FTS/StrongEps/HkSqAux/wdiv_shift_le.lean` — the shift bound for
`w / sin(2θ)^{η/2}`

The single-slot weight `w z / sin(2θ)^{η/2}` (`w z = (1+z)²/z²`, `η = 99/100`) is the square root
of the pure `D_z`-weight `wtE z θ = w z² sin(2θ)^{-η}` of
`Submission/Work/FTS/StrongEps/Weights.lean`.  Here we record the *reverse* direction of
`Work.FTS.StrongEps.wtE_shift_le`: the shifted weight dominates the unshifted one up to
`e^{C(|p₁|+|p₂|)}`,

  `w z / sin(2θ)^{η/2} ≤ e^{C(|p₁|+|p₂|)} · w (zShift z p₁) / sin(2·thShift θ p₂)^{η/2}`,

which is the "lower bound" form needed when the shift is used to *replace* the point `(z,θ)` by a
shifted one (the two directions are compatible because `p ↦ -p` inverts the shift).

Both halves are elementary.

* **the `z`-half.**  `w z = ((1+z)/z)²` while `w (z e^{-p}) = ((e^{p}+z)/z)²`, and
  `1 + z ≤ e^{|p|} (e^{p} + z)` because `1 ≤ e^{|p|}e^{p}` and `z ≤ e^{|p|}z`; whence
  `w z ≤ e^{2|p|} w (zShift z p)`.
  (The companion direction `w (zShift z p) ≤ e^{2|p|} w z` is `w_zShift_le`.)
* **the `θ`-half.**  `sinTwo_thShift_bounds` gives `sin(2·thShift θ p) ≤ e^{|p|} sin(2θ)`, hence,
  raising to the *nonnegative* power `η/2` and using `(e^{|p|})^{η/2} ≤ e^{|p|}`,
  `sin(2·thShift θ p)^{η/2} ≤ e^{|p|} sin(2θ)^{η/2}`, which after inverting is exactly
  `sin(2θ)^{-η/2} ≤ e^{|p|} sin(2·thShift θ p)^{-η/2}`.

`C = 3` suffices for the product (`2|p₁| + |p₂| ≤ 3(|p₁|+|p₂|)`).
-/

/-! ## The reverse radial bound -/

/-- **`w z ≤ e^{2|p|} w (zShift z p)`** — the reverse of `w_zShift_le`, which gives the same
inequality with the two sides exchanged (both are true, since `p ↦ -p` inverts the shift).  The
proof uses the forms `w z = ((1+z)/z)²`, `w (z e^{-p}) = ((e^{p}+z)/z)²` and the elementary bound
`1 + z ≤ e^{|p|} (e^{p} + z)`. -/
theorem w_le_w_zShift (z p : ℝ) (hz : 0 < z) :
    Work.Spaces.w z ≤ Real.exp (2 * |p|) * Work.Spaces.w (Work.FTS.StrongEps.zShift z p) := by
  -- the elementary inequality `1 + z ≤ e^{|p|} (e^{p} + z)`
  have hsum : 1 + z ≤ Real.exp |p| * (Real.exp p + z) := by
    have h1 : (1 : ℝ) ≤ Real.exp |p| * Real.exp p := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith [neg_le_abs p])
    have h2 : z ≤ Real.exp |p| * z := by
      rw [mul_comm]
      exact le_mul_of_one_le_right hz.le (Real.one_le_exp (abs_nonneg p))
    have h3 : 1 + z ≤ Real.exp |p| * Real.exp p + Real.exp |p| * z := add_le_add h1 h2
    rwa [← mul_add] at h3
  have hdiv : (1 + z) / z ≤ Real.exp |p| * ((Real.exp p + z) / z) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hsum hz.le
  have hsq : ((1 + z) / z) ^ 2
      ≤ (Real.exp |p| * ((Real.exp p + z) / z)) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg (by linarith) hz.le) hdiv 2
  -- identify the two weights with the squares of the quotients
  have hexp2 : (Real.exp |p|) ^ 2 = Real.exp (2 * |p|) := by
    rw [sq, ← Real.exp_add, two_mul]
  have hA : Work.Spaces.w z = ((1 + z) / z) ^ 2 := by
    rw [Work.Spaces.w, div_pow]
  have hB : Work.Spaces.w (Work.FTS.StrongEps.zShift z p)
      = ((Real.exp p + z) / z) ^ 2 := by
    have hquot : (1 + z * Real.exp (-p)) / (z * Real.exp (-p))
        = (Real.exp p + z) / z := by
      have hep : Real.exp (-p) * Real.exp p = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      rw [show 1 + z * Real.exp (-p) = Real.exp (-p) * (Real.exp p + z) from by
            rw [mul_add, hep]; ring,
          show z * Real.exp (-p) = Real.exp (-p) * z from by rw [mul_comm]]
      exact mul_div_mul_left _ _ (Real.exp_ne_zero (-p))
    have hsq' : Work.Spaces.w (Work.FTS.StrongEps.zShift z p)
        = ((1 + z * Real.exp (-p)) / (z * Real.exp (-p))) ^ 2 := by
      rw [Work.FTS.StrongEps.zShift, Work.Spaces.w, div_pow]
    rw [hsq', hquot]
  rw [hA, hB]
  calc ((1 + z) / z) ^ 2
      ≤ (Real.exp |p| * ((Real.exp p + z) / z)) ^ 2 := hsq
    _ = Real.exp (2 * |p|) * ((Real.exp p + z) / z) ^ 2 := by rw [mul_pow, hexp2]

/-! ## The angular half -/

/-- **`sin(2θ)^{-η/2} ≤ e^{|p|} sin(2·thShift θ p)^{-η/2}`** for `θ ∈ (0, π/2)`.  From
`sin(2·thShift θ p) ≤ e^{|p|} sin(2θ)` (`sinTwo_thShift_bounds`) one raises to the nonnegative
power `η/2`, using `(e^{|p|})^{η/2} ≤ e^{|p|}` (as `η/2 ≤ 1` and `e^{|p|} ≥ 1`), and inverts.

The statement is given with the inverses `(sin(2θ)^{η/2})⁻¹` rather than the negative powers
`sin(2θ)^{-η/2}`, which is the form in which it is consumed. -/
theorem sEtaHalf_inv_thShift_le {θ p : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹
      ≤ Real.exp |p|
        * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ (Work.Spaces.eta / 2))⁻¹ := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.StrongEps.sin_two_pos hθ
  have hs' : 0 < Real.sin (2 * Work.FTS.StrongEps.thShift θ p) :=
    Work.FTS.StrongEps.sin_two_pos (Work.FTS.StrongEps.thShift_mem hθ)
  have he : 0 ≤ Work.Spaces.eta / 2 := by rw [Work.Spaces.eta]; norm_num
  have he1 : Work.Spaces.eta / 2 ≤ 1 := by rw [Work.Spaces.eta]; norm_num
  have hE : (1 : ℝ) ≤ Real.exp |p| := Real.one_le_exp (abs_nonneg p)
  -- raise the bound `sin(2·thShift) ≤ e^{|p|} sin 2θ` to the nonnegative power `η/2`
  have h1 : Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ (Work.Spaces.eta / 2)
      ≤ Real.exp |p| * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    have h0 : Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ (Work.Spaces.eta / 2)
        ≤ (Real.exp |p| * Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_le_rpow hs'.le (Work.FTS.StrongEps.sinTwo_thShift_bounds hθ).2 he
    rw [Real.mul_rpow (Real.exp_pos _).le hs.le] at h0
    have h2 : (Real.exp |p|) ^ (Work.Spaces.eta / 2) ≤ Real.exp |p| :=
      Real.rpow_le_self_of_one_le hE he1
    have h3 : 0 ≤ Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
      (Real.rpow_pos_of_pos hs _).le
    calc Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ (Work.Spaces.eta / 2)
        ≤ (Real.exp |p|) ^ (Work.Spaces.eta / 2) * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := h0
      _ ≤ Real.exp |p| * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
          mul_le_mul_of_nonneg_right h2 h3
  -- invert the inequality
  have h4 : (Real.exp |p| * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹
      ≤ (Real.sin (2 * Work.FTS.StrongEps.thShift θ p) ^ (Work.Spaces.eta / 2))⁻¹ :=
    (inv_le_inv₀ (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hs _))
      (Real.rpow_pos_of_pos hs' _)).mpr h1
  have h5 : (Real.exp |p| * Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹
      = Real.exp (-|p|) * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹ := by
    rw [mul_inv_rev, ← Real.exp_neg]
    ring
  rw [h5] at h4
  have h6 := mul_le_mul_of_nonneg_left h4 (Real.exp_pos |p|).le
  rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h6

/-! ## The two halves combined -/

theorem wdiv_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z θ p₁ p₂ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (C * (|p₁| + |p₂|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁)
              / (Real.sin (2 * (Work.FTS.StrongEps.thShift θ p₂))) ^ (Work.Spaces.eta / 2)) := by
  refine ⟨3, by norm_num, fun z θ p₁ p₂ hz hθ => ?_⟩
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.StrongEps.sin_two_pos hθ
  have hs' : 0 < Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂) :=
    Work.FTS.StrongEps.sin_two_pos (Work.FTS.StrongEps.thShift_mem hθ)
  have hw := w_le_w_zShift z p₁ hz
  have hth := sEtaHalf_inv_thShift_le (θ := θ) (p := p₂) hθ
  have hprod : Work.Spaces.w z * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹
      ≤ (Real.exp (2 * |p₁|) * Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁))
        * (Real.exp |p₂|
            * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂)
                ^ (Work.Spaces.eta / 2))⁻¹) :=
    mul_le_mul hw hth (inv_nonneg.mpr (Real.rpow_nonneg hs.le _))
      (mul_nonneg (Real.exp_pos _).le (Work.FTS.StrongEps.w_nonneg _))
  have hexp : Real.exp (2 * |p₁| + |p₂|) ≤ Real.exp (3 * (|p₁| + |p₂|)) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg p₁, abs_nonneg p₂])
  have hnn : 0 ≤ Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁)
      * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂) ^ (Work.Spaces.eta / 2))⁻¹ :=
    mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
      (inv_nonneg.mpr (Real.rpow_nonneg hs'.le _))
  calc Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      = Work.Spaces.w z * (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))⁻¹ := by
        simp only [div_eq_mul_inv]
    _ ≤ (Real.exp (2 * |p₁|) * Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁))
        * (Real.exp |p₂|
            * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂)
                ^ (Work.Spaces.eta / 2))⁻¹) := hprod
    _ = Real.exp (2 * |p₁| + |p₂|)
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁)
              * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂)
                  ^ (Work.Spaces.eta / 2))⁻¹) := by
        rw [Real.exp_add]; ring
    _ ≤ Real.exp (3 * (|p₁| + |p₂|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁)
              * (Real.sin (2 * Work.FTS.StrongEps.thShift θ p₂)
                  ^ (Work.Spaces.eta / 2))⁻¹) :=
        mul_le_mul_of_nonneg_right hexp hnn
    _ = Real.exp (3 * (|p₁| + |p₂|))
          * (Work.Spaces.w (Work.FTS.StrongEps.zShift z p₁)
              / (Real.sin (2 * (Work.FTS.StrongEps.thShift θ p₂)))
                  ^ (Work.Spaces.eta / 2)) := by
        simp only [div_eq_mul_inv]

end Work.FTS.StrongEps.HkSqAux
