import Mathlib
import Submission.Lib.Unif2.ExtremalOnto

namespace Work.BasinSC.StepOneCrit

/-!
# The disc automorphism `w ↦ (w - c)/(1 - conj c · w)`

We package `Submission.mobiusA c` and its inverse `Submission.mobiusA (-c)` as a pair of mutually
inverse automorphisms of the open unit disc, holomorphic (indeed analytic) on the closed unit
disc with nowhere-vanishing derivative there.  These are the standard Möbius automorphisms of the
disc used to normalise a marked point to the origin.
-/

/-- `‖a‖ < 1` implies `Complex.normSq a < 1`. -/
theorem normSq_lt_one_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) : Complex.normSq a < 1 := by
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg a]

/-- `1 - conj a * a ≠ 0` when `‖a‖ < 1`. -/
theorem one_sub_conj_mul_self_ne_zero {a : ℂ} (ha : ‖a‖ < 1) :
    (1 : ℂ) - (starRingEnd ℂ) a * a ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * a = 1 := by
    simp only [sub_eq_zero] at h
    exact h.symm
  have h2 : Complex.normSq a = 1 := by
    have h3 : ((Complex.normSq a : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self, h1]
    exact_mod_cast h3
  rw [Complex.normSq_eq_norm_sq] at h2
  nlinarith [norm_nonneg a]

/-- The disc automorphism is strictly contracting towards the interior: it maps the open unit disc
into itself. -/
theorem norm_mobiusA_lt_one {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖Submission.mobiusA a w‖ < 1 := by
  have hwle : ‖w‖ ≤ 1 := le_of_lt hw
  have hden := Submission.mobiusA_denom_ne_zero ha hwle
  have hnum : ‖w - a‖ < ‖1 - (starRingEnd ℂ) a * w‖ := by
    have hsq : Complex.normSq (w - a)
        < Complex.normSq (1 - (starRingEnd ℂ) a * w) := by
      rw [Submission.normSq_one_sub_conj_mul a w]
      have h1 := normSq_lt_one_of_norm_lt_one ha
      have h2 := normSq_lt_one_of_norm_lt_one hw
      nlinarith [Complex.normSq_nonneg (w - a)]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    rw [sq_lt_sq] at hsq
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hsq
  rw [Submission.mobiusA, norm_div, div_lt_one (norm_pos_iff.mpr hden)]
  exact hnum

/-- Explicit form of `mobiusA (-a)` as an additive Möbius map. -/
theorem mobiusA_neg_apply (a u : ℂ) :
    Submission.mobiusA (-a) u = (u + a) / (1 + (starRingEnd ℂ) a * u) := by
  rw [Submission.mobiusA]
  have e1 : u - -a = u + a := by ring
  have e2 : (1 : ℂ) - (starRingEnd ℂ) (-a) * u = 1 + (starRingEnd ℂ) a * u := by
    rw [map_neg]
    ring
  rw [e1, e2]

/-- `mobiusA (-a)` is a left inverse of `mobiusA a` on the closed unit disc. -/
theorem mobiusA_comp_neg {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    Submission.mobiusA (-a) (Submission.mobiusA a w) = w := by
  have hD : (1 : ℂ) - (starRingEnd ℂ) a * w ≠ 0 := Submission.mobiusA_denom_ne_zero ha hw
  have hD' : (1 : ℂ) - w * (starRingEnd ℂ) a ≠ 0 := by simpa [mul_comm] using hD
  have haa : (1 : ℂ) - (starRingEnd ℂ) a * a ≠ 0 := one_sub_conj_mul_self_ne_zero ha
  have hne : 1 + (starRingEnd ℂ) a * Submission.mobiusA a w ≠ 0 := by
    intro h0
    have hprod : (1 - (starRingEnd ℂ) a * w)
        * (1 + (starRingEnd ℂ) a * Submission.mobiusA a w)
        = 1 - (starRingEnd ℂ) a * a := by
      rw [Submission.mobiusA]
      field_simp
      ring
    rw [h0, mul_zero] at hprod
    exact haa hprod.symm
  have hnum : Submission.mobiusA a w + a
      = w * (1 + (starRingEnd ℂ) a * Submission.mobiusA a w) := by
    rw [Submission.mobiusA]
    field_simp [hD']
    ring
  rw [mobiusA_neg_apply a (Submission.mobiusA a w), hnum, mul_div_assoc, div_self hne,
    mul_one]

/-- The derivative of `mobiusA a` does not vanish on the closed unit disc when `‖a‖ < 1`. -/
theorem deriv_mobiusA_ne_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    deriv (Submission.mobiusA a) w ≠ 0 := by
  have hden : 1 - (starRingEnd ℂ) a * w ≠ 0 := Submission.mobiusA_denom_ne_zero ha hw
  have haa : (1 : ℂ) - (starRingEnd ℂ) a * a ≠ 0 := one_sub_conj_mul_self_ne_zero ha
  rw [Submission.deriv_mobiusA a w hden]
  exact div_ne_zero haa (pow_ne_zero 2 hden)

/-- Möbius automorphism of the unit disc sending `c` to `0`, with its inverse: take
`m := Submission.mobiusA c` and `η := Submission.mobiusA (-c)` (module
`Submission.Lib.Unif2.ExtremalOnto` already has `Submission.mobiusA_self`,
`Submission.norm_mobiusA_le`, `Submission.mobiusA_denom_ne_zero`,
`Submission.analyticAt_mobiusA`, `Submission.deriv_mobiusA`, `Submission.normSq_one_sub_conj_mul`
-- import `Submission.Lib.Unif2.ExtremalOnto`).  Strict ball membership follows from
`Submission.normSq_one_sub_conj_mul`: `normSq (w - c) < normSq (1 - c̄ w)` when `‖w‖ < 1`, `‖c‖ < 1`;
the two composition identities are field algebra (denominators nonzero by
`Submission.mobiusA_denom_ne_zero`). -/
theorem disc_automorphism {c : ℂ} (hc : ‖c‖ < 1) :
    ∃ (m η : ℂ → ℂ),
      m c = 0 ∧
      (∀ w : ℂ, ‖w‖ < 1 → ‖m w‖ < 1) ∧
      (∀ w : ℂ, ‖w‖ < 1 → ‖η w‖ < 1) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → η (m w) = w) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → m (η w) = w) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → DifferentiableAt ℂ m w) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → DifferentiableAt ℂ η w) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → deriv m w ≠ 0) ∧
      (∀ w : ℂ, ‖w‖ ≤ 1 → deriv η w ≠ 0) := by
  have hnc : ‖-c‖ < 1 := by simpa using hc
  refine ⟨Submission.mobiusA c, Submission.mobiusA (-c), Submission.mobiusA_self c,
    fun w hw => norm_mobiusA_lt_one hc hw,
    fun w hw => norm_mobiusA_lt_one hnc hw,
    fun w hw => mobiusA_comp_neg hc hw,
    fun w hw => ?_,
    fun w hw => ?_,
    fun w hw => ?_,
    fun w hw => deriv_mobiusA_ne_zero hc hw,
    fun w hw => deriv_mobiusA_ne_zero hnc hw⟩
  · simpa using mobiusA_comp_neg (a := -c) hnc hw
  · exact (Submission.analyticAt_mobiusA c
      (Submission.mobiusA_denom_ne_zero hc hw)).differentiableAt
  · exact (Submission.analyticAt_mobiusA (-c)
      (Submission.mobiusA_denom_ne_zero hnc hw)).differentiableAt

end Work.BasinSC.StepOneCrit
