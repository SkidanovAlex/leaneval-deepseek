/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.Work.Analysis.Concentration.Improving

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The weak-type (level-set) form of the concentration estimates

Two "weak-type" statements relating the level sets of an averaging operator to the concentration
estimates of Appendix C:

* `polyShiftAverage_weak_type` — Chebyshev's inequality applied to the `L¹ → L^s` improving
  estimate: the level sets of the polynomial average decay like `t^{-s}`, i.e. the operator is of
  weak type `(1, s)`;
* `fiberLpBound_of_fiberWeakType_fiberWeakType` is the (sharper) layer-cake statement converting
  the distributional bound on the fibre counting function `h` into the `L^s` bound; it is proved
  in the companion module `fiberLpBound_of_fiberWeakType`.
-/

set_option autoImplicit false

namespace Work.Analysis.Concentration

open Polynomial Finset MeasureTheory

noncomputable section

/-- The `L^s` norm of a function on `ℤ/Qℤ`, raised to the power `s`, is the average of the
pointwise `s`-th powers. -/
lemma LpNormZMod_rpow (Q : ℕ) [NeZero Q] {s : ℝ} (hs : 0 < s) (g : ZMod Q → ℂ) :
    (LpNormZMod Q s g) ^ s = (Q : ℝ)⁻¹ * ∑ y : ZMod Q, ‖g y‖ ^ s := by
  unfold LpNormZMod
  have hS : 0 ≤ (Q : ℝ)⁻¹ * ∑ y : ZMod Q, ‖g y‖ ^ s :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (norm_nonneg _) s)
  rw [← Real.rpow_mul hS, one_div, inv_mul_cancel₀ (ne_of_gt hs), Real.rpow_one]

/-- **Weak-type `(1, s)` bound for the polynomial averaging operator.**  If the fibre counting
function satisfies the `L^s` concentration bound `FiberLpBound P Q s C`, then the level sets of
`polyShiftAverageZMod P Q f` decay like `t^{-s}`:
`#{y : ‖A f y‖ ≥ t} ≤ (C ‖f‖_{L¹}/t)^s Q`. -/
theorem polyShiftAverage_weak_type {P : Polynomial ℤ} {Q : ℕ} [NeZero Q] {s C : ℝ}
    (hs : 1 < s) (hC : 0 ≤ C) (h : FiberLpBound P Q s C) {t : ℝ} (ht : 0 < t)
    (f : ZMod Q → ℂ) :
    ((Finset.univ.filter
        (fun y : ZMod Q => t ≤ ‖polyShiftAverageZMod P Q f y‖)).card : ℝ)
      ≤ ((C * LpNormZMod Q 1 f) / t) ^ s * Q := by
  set g := polyShiftAverageZMod P Q f with hg
  have hs0 : 0 < s := by linarith
  -- Chebyshev's inequality
  have hcheb : ((Finset.univ.filter (fun y : ZMod Q => t ≤ ‖g y‖)).card : ℝ) * t ^ s
      ≤ ∑ y : ZMod Q, ‖g y‖ ^ s := by
    have h1 : ((Finset.univ.filter (fun y : ZMod Q => t ≤ ‖g y‖)).card : ℝ) * t ^ s
        = ∑ _y ∈ Finset.univ.filter (fun y : ZMod Q => t ≤ ‖g y‖), t ^ s := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h1]
    calc ∑ y ∈ Finset.univ.filter (fun y : ZMod Q => t ≤ ‖g y‖), t ^ s
        ≤ ∑ y ∈ Finset.univ.filter (fun y : ZMod Q => t ≤ ‖g y‖), ‖g y‖ ^ s :=
          Finset.sum_le_sum (fun y hy =>
            Real.rpow_le_rpow ht.le (Finset.mem_filter.mp hy).2 hs0.le)
      _ ≤ ∑ y : ZMod Q, ‖g y‖ ^ s :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun y _ _ => Real.rpow_nonneg (norm_nonneg _) s)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hsum : ∑ y : ZMod Q, ‖g y‖ ^ s = Q * (LpNormZMod Q s g) ^ s := by
    rw [LpNormZMod_rpow Q hs0 g]
    exact (mul_inv_cancel_left₀ hQpos.ne' _).symm
  have hbound : LpNormZMod Q s g ≤ C * LpNormZMod Q 1 f :=
    polyImproving_of_fiberLpBound (r := s) (C := C) (p := 1) (p' := s)
      (le_of_lt hs) hC h le_rfl (le_of_lt hs) (by ring) f
  have htspos : 0 < t ^ s := Real.rpow_pos_of_pos ht s
  have hfinal : ((Finset.univ.filter (fun y : ZMod Q => t ≤ ‖g y‖)).card : ℝ)
      ≤ (Q * (C * LpNormZMod Q 1 f) ^ s) / t ^ s := by
    rw [le_div_iff₀ htspos]
    calc ((Finset.univ.filter (fun y : ZMod Q => t ≤ ‖g y‖)).card : ℝ) * t ^ s
        ≤ ∑ y : ZMod Q, ‖g y‖ ^ s := hcheb
      _ = Q * (LpNormZMod Q s g) ^ s := hsum
      _ ≤ Q * (C * LpNormZMod Q 1 f) ^ s :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (LpNormZMod_nonneg Q s g) hbound hs0.le) (by positivity)
  refine hfinal.trans (le_of_eq ?_)
  rw [Real.div_rpow (mul_nonneg hC (LpNormZMod_nonneg Q 1 f)) ht.le]
  ring

end

end Work.Analysis.Concentration
