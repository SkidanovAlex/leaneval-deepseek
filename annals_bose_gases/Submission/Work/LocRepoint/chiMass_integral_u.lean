import Mathlib.Tactic.Have
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.LocRepoint.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The normalisation of the repointed `χ_{B(u)}²`-mass `Work.LocRepoint.chiMass`

The repointed cutoff is

    `chiSmallB M L d u x = chiScale L x * chiSmall M ((L*d)⁻¹ • x - u)`

(`chiScale L x = χ(x/L)` for the corpus global bump `χ` of `Submission.CubicChi`, `∫χ² = 1`,
support in the ball of radius `1/2`; `chiSmall M` is FS's cosine-`M`-th-power bump with
`∫χ_M² = 1`, support in the unit ball).  We compute, exactly as in the corpus analogue
(`Work.SmallBoxSliding.integral_chiMass_eq`),

    `∫_u chiMass M L d u = ∫_u ∫_x χ_{B(u)}(x)² dx du = L³`.

The two factors separate: for fixed `x` the `u`-integral of the second factor is
`∫_v χ_M(v)² = 1` by translation invariance, and the remaining `x`-integral of
`χ(x/L)²` is `L³` by the additive-Haar dilation formula together with `∫χ² = 1`.

Everything beyond those two normalisations is Fubini, for which the joint integrability of
`(u,x) ↦ χ_{B(u)}(x)²` is obtained from compact support: a nonzero value forces
`‖x‖ ≤ L/2` (support of `chiScale L`) and `‖u‖ ≤ 1/(2d) + 1` (support of `chiSmall M`
after removing the `x`-contribution), and the integrand is continuous.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.LocRepoint

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false

/-! ## Elementary support facts -/

/-- `chiScale L` vanishes outside the ball of radius `L/2`. -/
lemma chiScale_eq_zero_of_half_lt_norm {L : ℝ} (hL : 0 < L) (x : ℝ³) (hx : L / 2 < ‖x‖) :
    chiScale L x = 0 := by
  have hLpos : (0 : ℝ) < L⁻¹ := inv_pos.mpr hL
  rw [chiScale]
  refine chi_eq_zero_of_norm_gt _ ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hLpos]
  have h : L⁻¹ * (L / 2) = 1 / 2 := by field_simp
  rw [← h]
  exact mul_lt_mul_of_pos_left hx hLpos

/-- `chiSmallBase` vanishes outside the unit ball. -/
lemma chiSmallBase_eq_zero_of_one_lt_norm {M : ℕ} (hM : 1 ≤ M) (z : ℝ³) (hz : 1 < ‖z‖) :
    chiSmallBase M z = 0 := by
  by_contra hb
  exact absurd (chiSmallBase_support_norm_le hM hb) (not_le.mpr hz)

/-- A nonzero normalised bump forces the unnormalised one nonzero. -/
lemma chiSmallBase_ne_zero_of_chiSmall_ne_zero {M : ℕ} {z : ℝ³} (hz : chiSmall M z ≠ 0) :
    chiSmallBase M z ≠ 0 := by
  intro h0
  exact hz (by simp [chiSmall, h0])

/-! ## The two one-factor normalisations -/

/-- Translation invariance of the `χ_M²`-mass: for every centre `y`,
`∫_u χ_M(y − u)² du = ∫ χ_M² = 1`. -/
lemma integral_chiSmall_sub_sq_eq_one {M : ℕ} (hM : 1 ≤ M) (y : ℝ³) :
    (∫ u : ℝ³, (chiSmall M (y - u)) ^ 2) = 1 := by
  rw [MeasureTheory.integral_sub_left_eq_self (fun v : ℝ³ => (chiSmall M v) ^ 2) volume y,
    chiSmall_L2 hM]

/-- The additive-Haar dilation normalisation: `∫_x χ(x/L)² dx = L³`. -/
lemma integral_chiScale_sq {L : ℝ} (hL : 0 < L) :
    (∫ x : ℝ³, (chiScale L x) ^ 2) = L ^ 3 := by
  have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℝ³)
      (fun z : ℝ³ => (chi z) ^ 2) (R := L) (le_of_lt hL)
  have hfr : Module.finrank ℝ ℝ³ = 3 := by rw [finrank_euclideanSpace, Fintype.card_fin]
  rw [hfr, smul_eq_mul] at h
  have hLHS : (∫ x : ℝ³, (chiScale L x) ^ 2) = ∫ x : ℝ³, (chi (L⁻¹ • x)) ^ 2 := by
    simp only [chiScale]
  rw [hLHS, h, chi_L2, mul_one]

/-! ## Joint integrability, for Fubini -/

/-- The `x`-slice of the repointed cutoff square is integrable for every `u`: it is continuous
and supported in the fixed ball `‖x‖ ≤ L/2` (`chiScale_eq_zero_of_half_lt_norm`). -/
lemma integrable_chiSmallB_sq_slice {M : ℕ} (hM : 1 ≤ M) {L d : ℝ} (hL : 0 < L)
    (u : ℝ³) : Integrable (fun x : ℝ³ => (chiSmallB M L d u x) ^ 2) := by
  have hcont : Continuous (fun x : ℝ³ => (chiSmallB M L d u x) ^ 2) := by
    have h1 : Continuous (fun x : ℝ³ => chiScale L x) := by
      unfold chiScale
      exact chi_continuous.comp (continuous_id.const_smul (L⁻¹))
    have h2 : Continuous (fun x : ℝ³ => chiSmall M ((L * d)⁻¹ • x - u)) :=
      (chiSmall_continuous hM).comp ((continuous_id.const_smul ((L * d)⁻¹)).sub continuous_const)
    have h3 : Continuous (fun x : ℝ³ => chiSmallB M L d u x) := by
      unfold chiSmallB
      exact h1.mul h2
    exact h3.pow 2
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ³) (L / 2)) ?_
  intro x hx
  rw [Function.mem_support] at hx
  have hx' : chiSmallB M L d u x ≠ 0 := by
    intro h0; exact hx (by rw [h0]; norm_num)
  have h1 : chiScale L x ≠ 0 := by
    intro h0; exact hx' (by unfold chiSmallB; rw [h0, zero_mul])
  have hnorm : ‖x‖ ≤ L / 2 := by
    by_contra hb
    exact h1 (chiScale_eq_zero_of_half_lt_norm hL x (lt_of_not_ge hb))
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

/-- **Joint integrability of `(u,x) ↦ χ_{B(u)}(x)²`** on `ℝ³ × ℝ³`, the hypothesis of Fubini in
the main computation.  The integrand is continuous, and a nonzero value forces
`‖x‖ ≤ L/2` (support of `chiScale L`) and `‖u‖ ≤ 1/(2d) + 1` (support of `chiSmall M` after
removing the `x`-contribution), so the support is contained in a product of closed balls. -/
lemma uncurry_chiSmallB_sq_integrable {M : ℕ} (hM : 1 ≤ M) {L d : ℝ} (hL : 0 < L)
    (hd : 0 < d) :
    Integrable (Function.uncurry (fun u x : ℝ³ => (chiSmallB M L d u x) ^ 2))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
  have hld : (0 : ℝ) < L * d := mul_pos hL hd
  have hcont : Continuous (fun p : ℝ³ × ℝ³ =>
      (chiScale L p.2 * chiSmall M ((L * d)⁻¹ • p.2 - p.1)) ^ 2) := by
    have h1 : Continuous (fun p : ℝ³ × ℝ³ => chiScale L p.2) := by
      unfold chiScale
      exact chi_continuous.comp (continuous_snd.const_smul (L⁻¹))
    have h2 : Continuous (fun p : ℝ³ × ℝ³ => chiSmall M ((L * d)⁻¹ • p.2 - p.1)) :=
      (chiSmall_continuous hM).comp ((continuous_snd.const_smul ((L * d)⁻¹)).sub continuous_fst)
    exact (h1.mul h2).pow 2
  have hcs : HasCompactSupport (fun p : ℝ³ × ℝ³ =>
      (chiScale L p.2 * chiSmall M ((L * d)⁻¹ • p.2 - p.1)) ^ 2) := by
    refine HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : ℝ³) (1 / (2 * d) + 1)).prod
        (isCompact_closedBall (0 : ℝ³) (L / 2))) ?_
    intro p hp
    rw [Function.mem_support] at hp
    have hp' : chiScale L p.2 * chiSmall M ((L * d)⁻¹ • p.2 - p.1) ≠ 0 := by
      intro h0; exact hp (by rw [h0]; norm_num)
    have hx1 : chiScale L p.2 ≠ 0 := fun h => hp' (by rw [h, zero_mul])
    have hx2 : chiSmall M ((L * d)⁻¹ • p.2 - p.1) ≠ 0 := fun h => hp' (by rw [h, mul_zero])
    have hnorm_x : ‖p.2‖ ≤ L / 2 := by
      by_contra hb
      exact hx1 (chiScale_eq_zero_of_half_lt_norm hL p.2 (lt_of_not_ge hb))
    have hy : chiSmallBase M ((L * d)⁻¹ • p.2 - p.1) ≠ 0 :=
      chiSmallBase_ne_zero_of_chiSmall_ne_zero hx2
    have hnorm_y : ‖(L * d)⁻¹ • p.2 - p.1‖ ≤ 1 := chiSmallBase_support_norm_le hM hy
    have hnorm_u : ‖p.1‖ ≤ 1 / (2 * d) + 1 := by
      have h1 : ‖(L * d)⁻¹ • p.2‖ ≤ 1 / (2 * d) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hld)]
        have hc : (L * d)⁻¹ * (L / 2) = 1 / (2 * d) := by field_simp
        rw [← hc]
        exact mul_le_mul_of_nonneg_left hnorm_x (le_of_lt (inv_pos.mpr hld))
      calc ‖p.1‖ = ‖((L * d)⁻¹ • p.2) - ((L * d)⁻¹ • p.2 - p.1)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖(L * d)⁻¹ • p.2‖ + ‖(L * d)⁻¹ • p.2 - p.1‖ := norm_sub_le _ _
        _ ≤ 1 / (2 * d) + 1 := add_le_add h1 hnorm_y
    exact ⟨by simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_u,
           by simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_x⟩
  have hEq : Function.uncurry (fun u x : ℝ³ => (chiSmallB M L d u x) ^ 2)
      = fun p : ℝ³ × ℝ³ => (chiScale L p.2 * chiSmall M ((L * d)⁻¹ • p.2 - p.1)) ^ 2 := by
    funext p
    obtain ⟨u, x⟩ := p
    simp only [Function.uncurry_apply_pair, chiSmallB]
  rw [hEq]
  exact hcont.integrable_of_hasCompactSupport hcs

/-! ## The main theorem -/

theorem chiMass_integral_u {M : ℕ} (hM : 1 ≤ M) {L d : ℝ} (hL : 0 < L) (hd : 0 < d) :
    (∫ u : EuclideanSpace ℝ (Fin 3), Work.LocRepoint.chiMass M L d u) = L ^ 3 := by
  -- the pointwise-in-`x` `u`-integral of the cutoff square
  have hslice : ∀ x : ℝ³, (∫ u : ℝ³, (chiSmallB M L d u x) ^ 2) = (chiScale L x) ^ 2 := by
    intro x
    have hmul : (fun u : ℝ³ => (chiSmallB M L d u x) ^ 2)
        = fun u : ℝ³ => (chiScale L x) ^ 2 * (chiSmall M ((L * d)⁻¹ • x - u)) ^ 2 := by
      funext u
      simp only [chiSmallB, mul_pow]
    rw [hmul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub_left_eq_self (fun v : ℝ³ => (chiSmall M v) ^ 2) volume
        ((L * d)⁻¹ • x), chiSmall_L2 hM, mul_one]
  -- Fubini in `(u,x)` at the product measure
  have hswap := MeasureTheory.integral_integral_swap (μ := (volume : Measure ℝ³))
    (ν := (volume : Measure ℝ³))
    (f := fun u x : ℝ³ => (chiSmallB M L d u x) ^ 2)
    (uncurry_chiSmallB_sq_integrable hM hL hd)
  calc (∫ u : ℝ³, chiMass M L d u)
      = ∫ u : ℝ³, ∫ x : ℝ³, (chiSmallB M L d u x) ^ 2 := by simp only [chiMass]
    _ = ∫ x : ℝ³, ∫ u : ℝ³, (chiSmallB M L d u x) ^ 2 := hswap
    _ = ∫ x : ℝ³, (chiScale L x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        exact hslice x
    _ = L ^ 3 := integral_chiScale_sq hL

end Work.LocRepoint
