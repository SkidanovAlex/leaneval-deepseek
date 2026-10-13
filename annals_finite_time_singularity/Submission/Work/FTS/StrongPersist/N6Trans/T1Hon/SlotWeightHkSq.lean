import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.HardSlotAux.SlotIntegrableHonest
import Submission.Work.H2.T1Q.SlotBoundQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.T1Hon

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Continuity of the angular `rpow` weight on the open quadrant -/

/-- The uncurried angular weight `θ ↦ sin(2θ)^p` (applied to the second coordinate) is
continuous on the open quadrant, where `sin(2θ) > 0`. -/
theorem continuousOn_sin_two_rpow_snd (p : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => (Real.sin (2 * q.2)) ^ p)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsinpos : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2),
      0 < Real.sin (2 * q.2) := by
    intro q hq
    obtain ⟨h1, h2⟩ := hq
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [h2.1])
      (by linarith [h2.2, Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun q hq => Or.inl (ne_of_gt (hsinpos q hq)))

/-! ## The `θ`-integrability of a single weighted slot -/

/-- **Angular integrability of a single `ℋ⁴`-slot.**  The slot
`θ ↦ (D_z^bD_θ^a g)(z,θ)² · sin(2θ)^{-q}` is integrable on `Iθ` for `a + b ≤ 4`, for
`q ∈ {0, η}` when `a = 0` and `q ∈ {0, η, γ}` when `a ≥ 1`.  This generalizes
`HardSlotAux.SlotIntegrableHonest` (the case `a + b = 4`) in exactly two respects: the total
order is relaxed to `a + b ≤ 4`, and for `a = 0` the exponent `q = 0` is allowed as well. -/
theorem slotThetaIntegrableGen (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      Work.Spaces.Iθ := by
  have hwne : Work.Spaces.w z ≠ 0 := by
    rw [Work.Spaces.w]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hz))
  have hw2ne : (Work.Spaces.w z) ^ 2 ≠ 0 := pow_ne_zero 2 hwne
  have hHk : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ)
      (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
    have h : Integrable (fun θ : ℝ => Work.Spaces.HkIntegrand α 4 g z θ)
        (volume.restrict Work.Spaces.Iθ) := hmem.1 z (le_of_lt hz)
    rwa [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo] at h
  change Integrable (fun θ : ℝ =>
      (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
    (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo]
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- ## `a = 0`: the pure `D_z`-slot with exponent `0` or `η`
    have hb4 : b ≤ 4 := by omega
    rw [ha0, Work.Spaces.mixed_zero_right]
    -- the `η`-weighted slot is exactly the `HkMem`-integrable summand of the norm
    have heta : Integrable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      have hZ : Integrable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        Work.FTS.EllipticEst.integrableOn_zSummand α 4 hg hmem b hb4 (z := z) (le_of_lt hz)
      rw [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo] at hZ
      refine (hZ.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [mul_pow, Work.H2.T1Q.slotQ_whz_sq z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      rw [show (Work.Spaces.DzIter b g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter b g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) from by ring]
      rw [inv_mul_cancel_left₀ hw2ne]
    rcases hq0 ha0 with hq | hq
    · -- `q = 0`: dominated by the `η`-slot, since `sin(2θ) ≤ 1` on the open interval
      rw [hq]
      have haesm : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.DzIter b g z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(0 : ℝ)))
          (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
        have hfun : (fun θ : ℝ => (Work.Spaces.DzIter b g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(0 : ℝ)))
            = fun θ : ℝ => (Work.Spaces.DzIter b g z θ) ^ 2 := by
          funext θ
          rw [neg_zero, Real.rpow_zero, mul_one]
        rw [hfun]
        exact ContinuousOn.aestronglyMeasurable
          ((Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_slice_of_smoothOpen
            (hg.DzIter b) hz).pow 2) measurableSet_Ioo
      refine Integrable.mono' heta haesm ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos
          (Work.FTS.StrongPersist.N6Trans.HardSlotAux.sin_two_pos_of_Ioo hθ)
          (Real.sin_le_one _) (by norm_num [Work.Spaces.eta])
      rw [neg_zero, Real.rpow_zero, mul_one,
        Real.norm_of_nonneg (sq_nonneg (Work.Spaces.DzIter b g z θ))]
      simpa using mul_le_mul_of_nonneg_left h1 (sq_nonneg (Work.Spaces.DzIter b g z θ))
    · -- `q = η`: exactly the `ℋ⁴`-summand
      rw [hq]
      exact heta
  · -- ## `a ≥ 1`: every slot is a summand of the `ℋ⁴`-integrand with weight `sin(2θ)^{-γ}`
    have hcontm : ContinuousOn (fun θ : ℝ => Work.Spaces.mixed b a g z θ)
        (Set.Ioo (0 : ℝ) (π / 2)) :=
      Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_slice_of_smoothOpen
        (hg.mixed b a) hz
    have hM : Integrable (fun θ : ℝ =>
        (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2)
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      have haesm : AEStronglyMeasurable (fun θ : ℝ =>
          (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2)
          (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
        ContinuousOn.aestronglyMeasurable
          ((hcontm.mul (Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_Wt_slice
            α z)).pow 2) measurableSet_Ioo
      refine Integrable.mono' hHk haesm ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ a b hapos hab
    have hgamma : Integrable (fun θ : ℝ => (Work.Spaces.mixed b a g z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      refine (hM.const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [mul_pow, Work.H2.T1Q.slotQ_wt_sq α z ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
      rw [show (Work.Spaces.mixed b a g z θ) ^ 2
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed b a g z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) from by ring]
      rw [inv_mul_cancel_left₀ hw2ne]
    -- a smaller exponent gives a smaller weight, so every `q ≤ γ` is integrable as well
    have hred : ∀ p : ℝ, p ≤ Work.Spaces.gam α → Integrable
        (fun θ : ℝ => (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-p))
        (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) := by
      intro p hp
      have haesm : AEStronglyMeasurable (fun θ : ℝ =>
          (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-p))
          (volume.restrict (Set.Ioo (0 : ℝ) (π / 2))) :=
        ContinuousOn.aestronglyMeasurable
          ((hcontm.pow 2).mul
            (Work.FTS.StrongPersist.N6Trans.HardSlotAux.continuousOn_sin_two_rpow (-p)))
          measurableSet_Ioo
      refine Integrable.mono' hgamma haesm ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg
          (Work.Spaces.sin_two_nonneg_of_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) _))]
      exact mul_le_mul_of_nonneg_left
        (Work.FTS.StrongPersist.N6Trans.HardSlotAux.rpow_sin_two_neg_le hp hθ)
        (sq_nonneg _)
    obtain hq | hq | hq := hqa hapos
    · rw [hq]
      exact hred 0 (le_of_lt (Work.Spaces.gam_pos hα))
    · rw [hq]
      exact hred Work.Spaces.eta (le_trans (le_of_lt Work.Spaces.eta_lt_one)
        (le_of_lt (Work.Spaces.one_lt_gam hα)))
    · rw [hq]
      exact hred (Work.Spaces.gam α) le_rfl

/-! ## The pointwise domination in `θ` -/

/-- **Pointwise domination of a weighted `ℋ⁴`-slot by the `ℋ⁴`-integrand.**  For every slot
`(a,b)` with `a + b ≤ 4` and every exponent `q` admissible for that slot (`q ∈ {0, η}` when
`a = 0`, `q ∈ {0, η, γ}` when `a ≥ 1`), and every angle `θ` in the open interval `(0, π/2)`,
`w(z)²·((D_z^bD_θ^a g)(z,θ))²·sin(2θ)^{-q} ≤ HkIntegrand α 4 g z θ`. -/
theorem slotWeight_pointwise_le (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α) (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · -- ## `a = 0`: the pure `D_z`-slot, with `q ≤ η`
    have hb4 : b ≤ 4 := by omega
    have hqle : q ≤ Work.Spaces.eta := by
      rcases hq0 ha0 with hq | hq
      · rw [hq]; exact le_of_lt Work.Spaces.eta_pos
      · rw [hq]
    have hsq : (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      Work.FTS.StrongPersist.N6Trans.HardSlotAux.rpow_sin_two_neg_le hqle hθ
    rw [ha0, Work.Spaces.mixed_zero_right]
    have hrhs : (Work.Spaces.DzIter b g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      rw [mul_pow, Work.H2.T1Q.slotQ_whz_sq z hθI]
      ring
    rw [show (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.DzIter b g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        = ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter b g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-q) from by ring]
    refine le_trans (mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))) ?_
    rw [← hrhs]
    exact Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ b hb4
  · -- ## `a ≥ 1`: the mixed slot, with `q ≤ γ`
    have hqle : q ≤ Work.Spaces.gam α := by
      obtain hq | hq | hq := hqa hapos
      · rw [hq]; exact le_of_lt (Work.Spaces.gam_pos hα)
      · rw [hq]
        exact le_trans (le_of_lt Work.Spaces.eta_lt_one) (le_of_lt (Work.Spaces.one_lt_gam hα))
      · rw [hq]
    have hsq : (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Work.FTS.StrongPersist.N6Trans.HardSlotAux.rpow_sin_two_neg_le hqle hθ
    have hrhs : (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2
        = ((Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [mul_pow, Work.H2.T1Q.slotQ_wt_sq α z hθI]
      ring
    rw [show (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        = ((Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed b a g z θ) ^ 2)
          * (Real.sin (2 * θ)) ^ (-q) from by ring]
    refine le_trans (mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))) ?_
    rw [← hrhs]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ a b hapos hab

/-- The pointwise domination, in the almost-everywhere form needed for the `θ`-integration:
it holds at every `θ ∈ Iθ` except the two endpoints, which are null. -/
theorem ae_slotWeight_pointwise_le (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α) (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) (z : ℝ) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rw [Work.FTS.StrongPersist.N6Trans.HardSlotAux.restrict_Iθ_eq_restrict_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => slotWeight_pointwise_le α g a b q hα hab hq0 hqa hθ)

/-! ## The per-`z` bound -/

/-- **The per-`z` bound of the weighted slot energy.**  For every `z ∈ Iz`,
`w(z)²·∫_θ (D_z^bD_θ^a g)(z,θ)²·sin(2θ)^{-q} ≤ ∫_θ HkIntegrand α 4 g z θ`. -/
theorem slotWeight_z_le (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · -- at `z = 0` the radial weight vanishes
    subst hz0
    have hw0 : Work.Spaces.w 0 = 0 := by rw [Work.Spaces.w]; norm_num
    rw [hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ))
  · rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z (le_of_lt hzpos)) ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
        mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)))
    · exact ae_slotWeight_pointwise_le α g a b q hα hab hq0 hqa z

/-! ## Almost-everywhere strong measurability of the `z`-marginal -/

/-- The `z`-marginal of the weighted slot energy is a.e. strongly measurable on `Iz`: the
uncurried slot is continuous on the open quadrant, hence a.e. strongly measurable for the
product measure, and integration in `θ` preserves a.e. strong measurability
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`). -/
theorem aesm_slotWeight (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed b a g p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-q))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    ((hg.mixed b a).continuousOn.pow 2).mul (continuousOn_sin_two_rpow_snd (-q))
  have hX : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed b a g p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-q))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hinner := hX.integral_prod_right' (ν := volume.restrict Work.Spaces.Iθ)
  have hw2 : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
    simp only [Work.Spaces.w]
    fun_prop
  exact hw2.aestronglyMeasurable.mul hinner

/-- The `z`-marginal of the weighted slot energy is nonnegative everywhere. -/
theorem slotWeight_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ) (z : ℝ) :
    0 ≤ (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) :=
  mul_nonneg (sq_nonneg _) (integral_nonneg_of_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _))))

/-! ## The main theorem -/

/-- The `z`-integrability and the `ℋ⁴`-bound of the weighted angular slot energy.
For `g` honestly in `ℋ⁴` (`SmoothOpen` plus `HkMem α 4 g`) and every slot `(a,b)` with
`a + b ≤ 4` and exponent `q` admissible for that slot (`q ∈ {0, eta}` for `a = 0`,
`q ∈ {0, eta, gam α}` for `a ≥ 1`), the function
`z ↦ w(z)²·∫_θ (mixed b a g z θ)²·sin(2θ)^{-q}` is integrable on `Iz = [0,∞)` with integral at
most `HkSq α 4 g`.

Route: `w(z)²·∫_θ ... ≤ ∫_θ w(z)²(...)²` (as `w² ≥ 0`), and the a.e. pointwise domination
`w(z)²σ^{-q}(mixed b a g z θ)² ≤ HkIntegrand α 4 g z θ` (for `a = 0`: `V = DzIter b g` and
`σ^{-q} ≤ σ^{-eta}`, giving the `i`-th `D_z`-summand of `HkIntegrand`; for `a ≥ 1`: the mixed
summand with weight `Wt α` and `q ≤ gam α`), first in `θ` for each `z ∈ Iz` (the `θ`-slice of
`HkIntegrand` is integrable by `HkMem`) and then in `z` (the `HkMem`-integrability of
`z ↦ ∫_θ HkIntegrand α 4 g z θ`, plus a.e. strong measurability of `z ↦ ∫_θ ...` from continuity
on the open quadrant, `Work.FTS.H2.aesm_of_Qd` /
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`).  Both conjuncts are needed: the second
by the per-slot assembly, the first to be able to `integral_const_mul`.

**Two traps.**  (1) The pointwise domination is *false* at `θ = 0` and `θ = π/2` when `q = 0`
(Lean has `0 ^ 0 = 1` but `0 ^ (-q) = 0` for `q > 0`, and the `HkIntegrand` summand vanishes
there), so it must be used a.e. (`setIntegral_mono_ae` / `integral_mono_ae`), not pointwise.
(2) For the first conjunct, the a.e. strong measurability of `z ↦ ∫_θ ...` on `Iz` has to cover
`z = 0`; there `w 0 = 0` and the whole function is `0`, so a `z = 0` case split (or an a.e.
argument on `Ioi 0`) settles it. -/
theorem SlotWeightHkSq (α : ℝ) (g : ℝ → ℝ → ℝ) (a b : ℕ) (q : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hab : a + b ≤ 4)
    (hq0 : a = 0 → q = 0 ∨ q = Work.Spaces.eta)
    (hqa : 1 ≤ a → q = 0 ∨ q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
        Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
        ≤ Work.Spaces.HkSq α 4 g := by
  set F : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed b a g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) with hF
  set H : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ with hH
  have hle : ∀ z ∈ Work.Spaces.Iz, F z ≤ H z :=
    fun z hz => slotWeight_z_le α g a b q hα hα1 hg hmem hab hq0 hqa hz
  have hFint : MeasureTheory.IntegrableOn F Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hmem.2 (aesm_slotWeight α g a b q hg) ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => by
      rw [Real.norm_of_nonneg (by rw [hF]; exact slotWeight_nonneg α g a b q z)]
      exact hle z hz)
  refine ⟨hFint, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hFint hmem.2
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hle z hz))
  simpa only [hH, Work.Spaces.HkSq] using hmono

end

end Work.FTS.StrongPersist.N6Trans.T1Hon
