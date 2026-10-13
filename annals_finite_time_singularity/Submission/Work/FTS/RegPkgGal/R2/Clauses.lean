import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.RegPkgGal.R2.hasDerivAt_slice_pth
import Submission.Work.FTS.RegPkgGal.R2.hasDerivAt_slice_pz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The three clauses of the repaired Taylor datum

`zClause_aux` (radial Lipschitz clause), `angClause_aux` (angular `α`-Hölder clause under the
*minimal* repair: continuity of the angular slices on `Iθ`), and `angClause_nbhd` (the same
clause under the *widened* smoothness hypothesis, i.e. `C¹` on a neighbourhood of the closed
angular range, which is the shape adopted by the repaired interface `R2b`).

The two analytic inputs of the angular clause are hypotheses here:
`hM`/`hIntγ` come from `Work.FTS.RegPkgGal.R2.angIntegral_le`, and `hE` from
`Work.FTS.RegPkgGal.R2.integrableOn_pth_slice`.  `angClause_nbhd` does not need `hE` (the
closed-interval FTC supplies the integrability of the derivative).
-/

open MeasureTheory Set Filter Topology
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R2

/-- Auxiliary: the angular clause of the corrected Taylor datum. -/
theorem angClause_aux {α Cθ M : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCθ : 0 ≤ Cθ) (hM0 : 0 ≤ M)
    {g : ℝ → ℝ → ℝ}
    (hM : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)) ≤ M * (b - a) ^ α)
    (hIntγ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      IntervalIntegrable (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
        volume a b)
    (hE : ∀ z : ℝ, 0 < z → IntegrableOn (fun s : ℝ => Work.Spaces.pth g z s)
      (Set.Icc 0 (Real.pi / 2)) volume)
    (hsm : ContDiffOn ℝ 1 (Function.uncurry g)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth g z θ| ≤ Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α)
    (hcontθ : ∀ z : ℝ, 0 < z → z ≤ 2 → ContinuousOn (fun θ => g z θ) Work.Spaces.Iθ)
    (hB1 : ∀ {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      HasDerivAt (fun s : ℝ => g z s) (Work.Spaces.pth g z θ) θ) :
    ∀ z θ θ' : ℝ, 0 < z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Cθ * M * z ^ 2 * |θ - θ'| ^ α := by
  intro z θ θ' hz hz2 hθ hθ'
  have key : ∀ a b : ℝ, a ∈ Work.Spaces.Iθ → b ∈ Work.Spaces.Iθ → a ≤ b →
      |g z a - g z b| ≤ Cθ * M * z ^ 2 * |a - b| ^ α := by
    intro a b ha hb hab
    rcases eq_or_lt_of_le hab with heq | hlt
    · subst heq
      simp [Real.zero_rpow (ne_of_gt hα)]
    have habI : Set.Icc a b ⊆ Work.Spaces.Iθ := fun s hs =>
      ⟨le_trans ha.1 hs.1, le_trans hs.2 hb.2⟩
    have hcont : ContinuousOn (fun s : ℝ => g z s) (Set.Icc a b) :=
      (hcontθ z hz hz2).mono habI
    have hderiv : ∀ s ∈ Set.Ioo a b,
        HasDerivAt (fun s : ℝ => g z s) (Work.Spaces.pth g z s) s := by
      intro s hs
      exact hB1 hz ⟨lt_of_le_of_lt ha.1 hs.1, lt_of_lt_of_le hs.2 hb.2⟩
    have hint : IntervalIntegrable (fun s : ℝ => Work.Spaces.pth g z s) volume a b := by
      have hsub : Set.uIoc a b ⊆ Set.Icc 0 (Real.pi / 2) := by
        intro s hs
        rw [Set.uIoc_of_le hab] at hs
        exact ⟨le_trans ha.1 (le_of_lt hs.1), le_trans hs.2 hb.2⟩
      exact intervalIntegrable_iff.mpr ((hE z hz).mono_set hsub)
    have hftc : ∫ s in a..b, Work.Spaces.pth g z s = g z b - g z a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ Real.pi / 2 := by
      rw [ae_iff]
      simpa using measure_singleton (Real.pi / 2)
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioc a b →
        ‖Work.Spaces.pth g z s‖
          ≤ Cθ * z ^ 2 * ((Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)) := by
      filter_upwards [hne] with s hs_ne hs_mem
      have hs0 : 0 < s := lt_of_le_of_lt ha.1 hs_mem.1
      have hs1 : s < Real.pi / 2 :=
        lt_of_le_of_ne (le_trans hs_mem.2 hb.2) hs_ne
      have hsin : 0 < Real.sin (2 * s) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      rw [Real.norm_eq_abs]
      have hD := hd z s (le_of_lt hz) ⟨hs0.le, le_of_lt hs1⟩
      have hpth : |Work.Spaces.pth g z s| = |Work.Spaces.Dth g z s| / Real.sin (2 * s) := by
        rw [Work.Spaces.Dth, abs_mul, abs_of_pos hsin,
          mul_div_cancel_left₀ _ (ne_of_gt hsin)]
      rw [hpth]
      refine (div_le_div_of_nonneg_right hD hsin.le).trans_eq ?_
      ring
    have hIntMaj : IntervalIntegrable
        (fun s : ℝ => Cθ * z ^ 2 * ((Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)))
        volume a b :=
      (hIntγ a b ha.1 hab hb.2).const_mul (Cθ * z ^ 2)
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab hae hIntMaj
    rw [Real.norm_eq_abs] at hnorm
    have h2 : (∫ s in a..b, Cθ * z ^ 2 *
          ((Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)))
        = Cθ * z ^ 2 *
          (∫ s in a..b, (Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)) := by
      rw [intervalIntegral.integral_const_mul]
    rw [h2] at hnorm
    have h3 : Cθ * z ^ 2 *
          (∫ s in a..b, (Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s))
        ≤ Cθ * M * z ^ 2 * (b - a) ^ α := by
      have h := hM a b ha.1 hab hb.2
      have hcz : 0 ≤ Cθ * z ^ 2 := mul_nonneg hCθ (sq_nonneg z)
      have h4 := mul_le_mul_of_nonneg_left h hcz
      calc Cθ * z ^ 2 *
            (∫ s in a..b, (Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s))
          ≤ Cθ * z ^ 2 * (M * (b - a) ^ α) := h4
        _ = Cθ * M * z ^ 2 * (b - a) ^ α := by ring
    have hfin : |∫ s in a..b, Work.Spaces.pth g z s| ≤ Cθ * M * z ^ 2 * (b - a) ^ α :=
      hnorm.trans h3
    calc |g z a - g z b| = |g z b - g z a| := abs_sub_comm _ _
      _ = |∫ s in a..b, Work.Spaces.pth g z s| := by rw [hftc]
      _ ≤ Cθ * M * z ^ 2 * (b - a) ^ α := hfin
      _ = Cθ * M * z ^ 2 * |a - b| ^ α := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
  rcases le_total θ θ' with hle | hle
  · exact key θ θ' hθ hθ' hle
  · rw [abs_sub_comm, abs_sub_comm θ θ']
    exact key θ' θ hθ' hθ hle

/-- Auxiliary: the radial Lipschitz clause of the corrected Taylor datum. -/
theorem zClause_aux {K Q K' : ℝ} (hQ0 : 0 ≤ Q) (hQK : max Q K ≤ K')
    {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 (Function.uncurry g)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hvt : Work.Spaces.VanishTheta g)
    (hquad : ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ| ≤ K * z ^ 2)
    (hlinz : ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz g z θ| ≤ Q * z)
    (hB2 : ∀ {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
      HasDerivAt (fun s : ℝ => g s θ) (Work.Spaces.pz g z θ) z) :
    ∀ θ ∈ Work.Spaces.Iθ, ∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
      |g z θ - g z' θ| ≤ K' * max z z' * |z - z'| := by
  intro θ hθ z z' hz hz2 hz' hz'2
  have hK'0 : 0 ≤ K' := le_trans (le_max_of_le_left hQ0) hQK
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [hvt.1 z, hvt.1 z', sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hK'0 (le_max_of_le_right hz')) (abs_nonneg _)
  rcases eq_or_lt_of_le hθ.2 with hpi | hpi
  · subst hpi
    rw [hvt.2 z, hvt.2 z', sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg hK'0 (le_max_of_le_right hz')) (abs_nonneg _)
  have hθI : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨h0, hpi⟩
  have hzero : g 0 θ = 0 := by
    have h := hquad θ hθ 0 le_rfl (by norm_num : (0:ℝ) ≤ 2)
    have h' : |g 0 θ| ≤ 0 := by simpa using h
    exact abs_eq_zero.mp (le_antisymm h' (abs_nonneg _))
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ 2 → 0 ≤ b → b ≤ 2 → a ≤ b →
      |g a θ - g b θ| ≤ K' * max a b * |a - b| := by
    intro a b ha ha2 hb hb2 hab
    rcases eq_or_lt_of_le hab with heq | hlt
    · subst heq
      simp
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · subst ha0
      rw [hzero, zero_sub, abs_neg, max_eq_right hb, zero_sub, abs_neg, abs_of_nonneg hb]
      have h1 : |g b θ| ≤ K * b ^ 2 := hquad θ hθ b hb hb2
      have hK' : K ≤ K' := le_trans (le_max_right Q K) hQK
      have h1' : K * b ^ 2 ≤ K' * b ^ 2 := mul_le_mul_of_nonneg_right hK' (sq_nonneg b)
      nlinarith [h1, h1']
    · have hcont : ContinuousOn (fun s : ℝ => g s θ) (Set.Icc a b) := by
        have h1 : ContinuousOn (fun s : ℝ => (s, θ)) (Set.Icc a b) :=
          continuousOn_id.prodMk continuousOn_const
        have h2 := hsm.continuousOn.comp h1 (fun s hs => ⟨lt_of_lt_of_le hapos hs.1, hθI⟩)
        simpa [Function.comp_def, Function.uncurry] using h2
      have hderiv : ∀ s ∈ Set.Ico a b,
          HasDerivWithinAt (fun s : ℝ => g s θ) (Work.Spaces.pz g s θ) (Set.Ici s) s :=
        fun s hs => (hB2 (lt_of_lt_of_le hapos hs.1) hθI).hasDerivWithinAt
      have hbound : ∀ s ∈ Set.Ico a b, ‖Work.Spaces.pz g s θ‖ ≤ Q * b := by
        intro s hs
        rw [Real.norm_eq_abs]
        have hs2 : s ≤ 2 := by linarith [hs.2, hb2]
        have h1 : |Work.Spaces.pz g s θ| ≤ Q * s := hlinz θ hθ s (le_trans ha hs.1) hs2
        have h2 : Q * s ≤ Q * b := mul_le_mul_of_nonneg_left hs.2.le hQ0
        linarith
      have hkey := norm_image_sub_le_of_norm_deriv_right_le_segment
        (f := fun s : ℝ => g s θ) (f' := fun s : ℝ => Work.Spaces.pz g s θ)
        (a := a) (b := b) (C := Q * b) hcont hderiv hbound
      have hmem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
      have hmain : ‖g b θ - g a θ‖ ≤ Q * b * (b - a) := hkey b hmem
      rw [Real.norm_eq_abs, abs_sub_comm] at hmain
      have hQK' : Q ≤ K' := le_trans (le_max_left Q K) hQK
      have h4 : Q * b * (b - a) ≤ K' * b * (b - a) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQK' hb) (by linarith)
      calc |g a θ - g b θ| ≤ Q * b * (b - a) := hmain
        _ ≤ K' * b * (b - a) := h4
        _ = K' * max a b * |a - b| := by
            rw [max_eq_right hab, abs_of_nonpos (by linarith), neg_sub]
  rcases le_total z z' with hle | hle
  · exact key z z' hz hz2 hz' hz'2 hle
  · rw [abs_sub_comm, max_comm, abs_sub_comm z z']
    exact key z' z hz' hz'2 hz hz2 hle

/-! ## The angular clause in the *widened* smoothness setting

When the joint `C¹` hypothesis is taken on a neighbourhood of the closed angular range
(`θ ∈ (-1, π/2+1)`), every angular slice is `C¹` *across* the two endpoints, so the `θ`-FTC
(`intervalIntegral.integral_deriv_of_contDiffOn_Icc`) applies with no integrability side
condition; only the angular integral bound `∫_a^b Γ/sin(2θ) ≤ M (b-a)^α` is needed.  This is
the shape of the statement used by the repaired interface. -/

theorem angClause_nbhd {α Cθ M : ℝ} (hα : 0 < α) (hCθ : 0 ≤ Cθ) (hM0 : 0 ≤ M)
    {g : ℝ → ℝ → ℝ}
    (hM : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ)) ≤ M * (b - a) ^ α)
    (hIntγ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      IntervalIntegrable (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
        volume a b)
    (hsm : ContDiffOn ℝ 1 (Function.uncurry g)
      (Set.prod (Set.Ioi (-1:ℝ)) (Set.Ioo (-1:ℝ) (Real.pi / 2 + 1))))
    (hd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth g z θ| ≤ Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α) :
    ∀ z θ θ' : ℝ, 0 ≤ z → z ≤ 2 → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |g z θ - g z θ'| ≤ Cθ * M * z ^ 2 * |θ - θ'| ^ α := by
  intro z θ θ' hz hz2 hθ hθ'
  have key : ∀ a b : ℝ, a ∈ Work.Spaces.Iθ → b ∈ Work.Spaces.Iθ → a ≤ b →
      |g z a - g z b| ≤ Cθ * M * z ^ 2 * |a - b| ^ α := by
    intro a b ha hb hab
    rcases eq_or_lt_of_le hab with heq | hlt
    · subst heq
      simp [Real.zero_rpow (ne_of_gt hα)]
    have hz1 : (-1:ℝ) < z := by linarith
    have hsub : Set.Icc a b ⊆ Set.Ioo (-1:ℝ) (Real.pi / 2 + 1) := by
      intro s hs
      exact ⟨by linarith [ha.1, hs.1], by linarith [hb.2, hs.2, Real.pi_pos]⟩
    have hslice : ContDiffOn ℝ 1 (fun s : ℝ => g z s)
        (Set.Ioo (-1:ℝ) (Real.pi / 2 + 1)) := by
      have h1 : ContDiffOn ℝ 1 (fun s : ℝ => (z, s)) (Set.Ioo (-1:ℝ) (Real.pi / 2 + 1)) :=
        contDiffOn_const.prodMk contDiffOn_id
      have h2 := hsm.comp h1 (fun s hs => ⟨hz1, hs⟩)
      simpa [Function.comp_def, Function.uncurry] using h2
    have hC1 : ContDiffOn ℝ 1 (fun s : ℝ => g z s) (Set.Icc a b) := hslice.mono hsub
    have hftc : ∫ s in a..b, deriv (fun s : ℝ => g z s) s = g z b - g z a :=
      intervalIntegral.integral_deriv_of_contDiffOn_Icc hC1 hab
    have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ Real.pi / 2 := by
      rw [ae_iff]
      simpa using measure_singleton (Real.pi / 2)
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Ioc a b →
        ‖deriv (fun s : ℝ => g z s) s‖
          ≤ Cθ * z ^ 2 * ((Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)) := by
      filter_upwards [hne] with s hs_ne hs_mem
      have hs0 : 0 < s := lt_of_le_of_lt ha.1 hs_mem.1
      have hs1 : s < Real.pi / 2 := lt_of_le_of_ne (le_trans hs_mem.2 hb.2) hs_ne
      have hsin : 0 < Real.sin (2 * s) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      rw [Real.norm_eq_abs]
      have hD := hd z s hz ⟨hs0.le, le_of_lt hs1⟩
      have hpth : |deriv (fun s : ℝ => g z s) s|
          = |Work.Spaces.Dth g z s| / Real.sin (2 * s) := by
        rw [show deriv (fun s : ℝ => g z s) s = Work.Spaces.pth g z s from rfl,
          Work.Spaces.Dth, abs_mul, abs_of_pos hsin, mul_div_cancel_left₀ _ (ne_of_gt hsin)]
      rw [hpth]
      refine (div_le_div_of_nonneg_right hD hsin.le).trans_eq ?_
      ring
    have hIntMaj : IntervalIntegrable
        (fun s : ℝ => Cθ * z ^ 2 * ((Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)))
        volume a b :=
      (hIntγ a b ha.1 hab hb.2).const_mul (Cθ * z ^ 2)
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab hae hIntMaj
    have h2 : (∫ s in a..b, Cθ * z ^ 2 *
          ((Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)))
        = Cθ * z ^ 2 *
          (∫ s in a..b, (Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s)) := by
      rw [intervalIntegral.integral_const_mul]
    rw [h2] at hnorm
    have h3 : Cθ * z ^ 2 *
          (∫ s in a..b, (Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s))
        ≤ Cθ * M * z ^ 2 * (b - a) ^ α := by
      have h := hM a b ha.1 hab hb.2
      have hcz : 0 ≤ Cθ * z ^ 2 := mul_nonneg hCθ (sq_nonneg z)
      have h4 := mul_le_mul_of_nonneg_left h hcz
      calc Cθ * z ^ 2 *
            (∫ s in a..b, (Real.sin s * Real.cos s ^ 2) ^ α / Real.sin (2 * s))
          ≤ Cθ * z ^ 2 * (M * (b - a) ^ α) := h4
        _ = Cθ * M * z ^ 2 * (b - a) ^ α := by ring
    have hfin : |∫ s in a..b, deriv (fun s : ℝ => g z s) s| ≤ Cθ * M * z ^ 2 * (b - a) ^ α :=
      hnorm.trans h3
    calc |g z a - g z b| = |g z b - g z a| := abs_sub_comm _ _
      _ = |∫ s in a..b, deriv (fun s : ℝ => g z s) s| := by rw [hftc]
      _ ≤ Cθ * M * z ^ 2 * (b - a) ^ α := hfin
      _ = Cθ * M * z ^ 2 * |a - b| ^ α := by
          rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
  rcases le_total θ θ' with hle | hle
  · exact key θ θ' hθ hθ' hle
  · rw [abs_sub_comm, abs_sub_comm θ θ']
    exact key θ' θ hθ' hθ hle

end Work.FTS.RegPkgGal.R2
