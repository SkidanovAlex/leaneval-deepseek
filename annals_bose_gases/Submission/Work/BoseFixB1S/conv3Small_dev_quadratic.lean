import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1S.chiSmall_lipschitz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped Real

set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- **The self-convolution against the shifted bump**: for `M ≥ 1` the defining
integral of `conv3Small M t = ∫_y χ_M y · χ_M (t − y)` equals the integral of
`χ_M y · χ_M (y − t)` — substitute `y ↦ t − y` (`integral_sub_left_eq_self`),
which reflects the second factor, and use evenness `chiSmall_even`. -/
lemma devQuad_conv_eq_shift {M : ℕ} (hM : 1 ≤ M) (t : ℝ³) :
    conv3Small M t = ∫ y : ℝ³, chiSmall M y * chiSmall M (y - t) := by
  have h := MeasureTheory.integral_sub_left_eq_self
    (f := fun u : ℝ³ => chiSmall M u * chiSmall M (u - t)) volume t
  have hleft : (∫ x : ℝ³, chiSmall M (t - x) * chiSmall M ((t - x) - t))
      = ∫ x : ℝ³, chiSmall M x * chiSmall M (t - x) := by
    apply integral_congr_ae
    filter_upwards with x
    have harg : (t - x) - t = -x := by abel
    rw [harg, chiSmall_even hM x, mul_comm]
  rw [hleft] at h
  simpa [conv3Small] using h

/-- **Polarisation identity for the self-convolution.** For `M ≥ 1`
(`∫χ_M² = 1` by `chiSmall_L2`, `χ_M` even):

    1 − (χ_M ⋆ χ_M)(t) = (1/2) · ∫_y (χ_M y − χ_M (y − t))² dy.

Expand the square, split the integral (`integral_add`/`integral_sub`), use
`chiSmall_L2` twice (the shifted factor by translation invariance
`integral_sub_right_eq_self`) and `devQuad_conv_eq_shift` for the cross term. -/
lemma devQuad_one_sub_eq_half_integral {M : ℕ} (hM : 1 ≤ M) (t : ℝ³) :
    1 - conv3Small M t
      = (1 / 2) * ∫ y : ℝ³, (chiSmall M y - chiSmall M (y - t)) ^ 2 := by
  have hint2 : Integrable (fun y : ℝ³ => (chiSmall M y) ^ 2) volume :=
    chiSmall_sq_integrable hM
  have hint3 : Integrable (fun y : ℝ³ => (chiSmall M (y - t)) ^ 2) volume :=
    hint2.comp_sub_right t
  have hmul : Integrable
      (fun y : ℝ³ => 2 * (chiSmall M y * chiSmall M (y - t))) volume := by
    have hcont : Continuous
        (fun y : ℝ³ => chiSmall M y * chiSmall M (y - t)) :=
      (chiSmall_continuous hM).mul
        ((chiSmall_continuous hM).comp (continuous_id.sub continuous_const))
    have hcs : HasCompactSupport
        (fun y : ℝ³ => chiSmall M y * chiSmall M (y - t)) :=
      (chiSmall_hasCompactSupport hM).mono (by
        intro y hy
        rw [Function.mem_support] at hy ⊢
        intro h
        exact hy (by rw [h, zero_mul]))
    exact (hcont.integrable_of_hasCompactSupport hcs).const_mul 2
  have hsub : (∫ y : ℝ³, ((chiSmall M y) ^ 2 - 2 * (chiSmall M y * chiSmall M (y - t))))
      = (∫ y : ℝ³, (chiSmall M y) ^ 2)
        - (∫ y : ℝ³, 2 * (chiSmall M y * chiSmall M (y - t))) :=
    MeasureTheory.integral_sub
      (f := fun y : ℝ³ => (chiSmall M y) ^ 2)
      (g := fun y : ℝ³ => 2 * (chiSmall M y * chiSmall M (y - t))) hint2 hmul
  have hadd : (∫ y : ℝ³, ((chiSmall M y) ^ 2 - 2 * (chiSmall M y * chiSmall M (y - t))
        + (chiSmall M (y - t)) ^ 2))
      = (∫ y : ℝ³, ((chiSmall M y) ^ 2 - 2 * (chiSmall M y * chiSmall M (y - t))))
        + (∫ y : ℝ³, (chiSmall M (y - t)) ^ 2) :=
    MeasureTheory.integral_add
      (f := fun y : ℝ³ => (chiSmall M y) ^ 2 - 2 * (chiSmall M y * chiSmall M (y - t)))
      (g := fun y : ℝ³ => (chiSmall M (y - t)) ^ 2) (hint2.sub hmul) hint3
  have hkey : (∫ y : ℝ³, (chiSmall M y - chiSmall M (y - t)) ^ 2)
      = 1 - 2 * conv3Small M t + 1 := by
    have e1 : (∫ y : ℝ³, (chiSmall M y - chiSmall M (y - t)) ^ 2)
        = ∫ y : ℝ³, ((chiSmall M y) ^ 2 - 2 * (chiSmall M y * chiSmall M (y - t))
            + (chiSmall M (y - t)) ^ 2) := by
      apply integral_congr_ae
      filter_upwards with y
      ring
    rw [e1, hadd, hsub]
    rw [chiSmall_L2 hM, MeasureTheory.integral_const_mul, ← devQuad_conv_eq_shift hM t,
      MeasureTheory.integral_sub_right_eq_self (fun z : ℝ³ => (chiSmall M z) ^ 2) t,
      chiSmall_L2 hM]
  rw [hkey]
  ring

/-- **Support obstruction bound for the polarisation integral.** If `χ_M` is
`L`-Lipschitz for the shift, `|χ_M y − χ_M (y−t)| ≤ L‖t‖` (all `y`, `t`), then

    ∫_y (χ_M y − χ_M (y−t))² dy ≤ 2 L² ‖t‖².

Pointwise the integrand is `≤ L²‖t‖²`, and it vanishes unless `y` or `y − t` lies
in the unit cube `C = {|z_j| ≤ 1/2}` (`chiSmall_support_mem_abs_le`); since
`volume C = 1` (`eucl_cube_volume`) and translations preserve volume, the
dominating function `L²‖t‖²·(1_C + 1_{C+t})` integrates to `L²‖t‖²·(1+1)`. -/
lemma devQuad_integral_diff_sq_le {M : ℕ} (hM : 1 ≤ M) {L : ℝ}
    (hLip : ∀ y t : ℝ³, |chiSmall M y - chiSmall M (y - t)| ≤ L * ‖t‖) (t : ℝ³) :
    ∫ y : ℝ³, (chiSmall M y - chiSmall M (y - t)) ^ 2 ≤ 2 * L ^ 2 * ‖t‖ ^ 2 := by
  set C : Set ℝ³ := {z : ℝ³ | ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 2} with hCdef
  set Cp : Set ℝ³ := (fun y : ℝ³ => y - t) ⁻¹' C with hCpdef
  have hCmeas : MeasurableSet C := by rw [hCdef]; exact eucl_cube_measurable
  have hCpmeas : MeasurableSet Cp := hCmeas.preimage (measurable_id.sub measurable_const)
  have hCvolE : (volume : Measure ℝ³) C = ENNReal.ofReal 1 := by
    rw [hCdef]
    have h := eucl_cube_volume (c := (1 / 2 : ℝ)) (by norm_num)
    have h2 : (2 * (1 / 2 : ℝ)) ^ 3 = 1 := by norm_num
    rw [h2] at h
    exact h
  have hCvol : (volume C).toReal = 1 := by
    rw [hCvolE, ENNReal.toReal_ofReal (by norm_num)]
  have hCpvolE : (volume : Measure ℝ³) Cp = (volume : Measure ℝ³) C := by
    rw [hCpdef]
    exact (measurePreserving_sub_right (volume : Measure ℝ³) t).measure_preimage
      hCmeas.nullMeasurableSet
  have hCpvol : (volume Cp).toReal = (volume C).toReal := by rw [hCpvolE]
  have hLsq : (0 : ℝ) ≤ L ^ 2 * ‖t‖ ^ 2 := by positivity
  have hb : ∀ y : ℝ³, (chiSmall M y - chiSmall M (y - t)) ^ 2 ≤ L ^ 2 * ‖t‖ ^ 2 := by
    intro y
    have h := hLip y t
    have h2 : |chiSmall M y - chiSmall M (y - t)| ^ 2 ≤ (L * ‖t‖) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h 2
    calc (chiSmall M y - chiSmall M (y - t)) ^ 2
        = |chiSmall M y - chiSmall M (y - t)| ^ 2 := (sq_abs _).symm
      _ ≤ (L * ‖t‖) ^ 2 := h2
      _ = L ^ 2 * ‖t‖ ^ 2 := by ring
  have hpt : ∀ y : ℝ³, (chiSmall M y - chiSmall M (y - t)) ^ 2
      ≤ L ^ 2 * ‖t‖ ^ 2 * (C.indicator (fun _ => (1 : ℝ)) y
          + Cp.indicator (fun _ => (1 : ℝ)) y) := by
    intro y
    by_cases hyC : y ∈ C
    · have h1 : (1 : ℝ) ≤ C.indicator (fun _ => (1 : ℝ)) y
          + Cp.indicator (fun _ => (1 : ℝ)) y := by
        rw [Set.indicator_of_mem hyC]
        have h2 := Set.indicator_nonneg (s := Cp) (f := fun _ => (1 : ℝ))
          (fun a _ => zero_le_one) y
        linarith
      calc (chiSmall M y - chiSmall M (y - t)) ^ 2 ≤ L ^ 2 * ‖t‖ ^ 2 := hb y
        _ = L ^ 2 * ‖t‖ ^ 2 * 1 := by ring
        _ ≤ L ^ 2 * ‖t‖ ^ 2 * (C.indicator (fun _ => (1 : ℝ)) y
              + Cp.indicator (fun _ => (1 : ℝ)) y) :=
            mul_le_mul_of_nonneg_left h1 hLsq
    · have hy0 : chiSmall M y = 0 := by
        by_contra hne
        exact hyC (by rw [hCdef]; exact chiSmall_support_mem_abs_le hM hne)
      by_cases hyCp : y ∈ Cp
      · have h1 : (1 : ℝ) ≤ C.indicator (fun _ => (1 : ℝ)) y
            + Cp.indicator (fun _ => (1 : ℝ)) y := by
          rw [Set.indicator_of_mem hyCp]
          have h2 := Set.indicator_nonneg (s := C) (f := fun _ => (1 : ℝ))
            (fun a _ => zero_le_one) y
          linarith
        have hb' : (chiSmall M (y - t)) ^ 2 ≤ L ^ 2 * ‖t‖ ^ 2 := by
          have h := hb y
          rw [hy0, zero_sub, neg_sq] at h
          exact h
        calc (chiSmall M y - chiSmall M (y - t)) ^ 2 = (chiSmall M (y - t)) ^ 2 := by
              rw [hy0]; ring
          _ ≤ L ^ 2 * ‖t‖ ^ 2 := hb'
          _ = L ^ 2 * ‖t‖ ^ 2 * 1 := by ring
          _ ≤ L ^ 2 * ‖t‖ ^ 2 * (C.indicator (fun _ => (1 : ℝ)) y
                + Cp.indicator (fun _ => (1 : ℝ)) y) :=
              mul_le_mul_of_nonneg_left h1 hLsq
      · have hyt0 : chiSmall M (y - t) = 0 := by
          by_contra hne
          exact hyCp (by rw [hCpdef]; exact chiSmall_support_mem_abs_le hM hne)
        have h0 : (chiSmall M y - chiSmall M (y - t)) ^ 2 = 0 := by rw [hy0, hyt0]; ring
        rw [h0]
        exact mul_nonneg hLsq (add_nonneg
          (Set.indicator_nonneg (s := C) (f := fun _ => (1 : ℝ)) (fun a _ => zero_le_one) y)
          (Set.indicator_nonneg (s := Cp) (f := fun _ => (1 : ℝ)) (fun a _ => zero_le_one) y))
  have hCfin : (volume : Measure ℝ³) C ≠ ⊤ := by
    rw [hCvolE]; exact ENNReal.ofReal_ne_top
  have hCpfin : (volume : Measure ℝ³) Cp ≠ ⊤ := by
    rw [hCpvolE]; exact hCfin
  have hCint : Integrable (C.indicator (fun _ : ℝ³ => (1 : ℝ))) volume :=
    (integrable_indicator_iff hCmeas).mpr (integrableOn_const hCfin (by simp))
  have hCpint : Integrable (Cp.indicator (fun _ : ℝ³ => (1 : ℝ))) volume :=
    (integrable_indicator_iff hCpmeas).mpr (integrableOn_const hCpfin (by simp))
  have hRint : Integrable (fun y : ℝ³ => L ^ 2 * ‖t‖ ^ 2
      * (C.indicator (fun _ => (1 : ℝ)) y + Cp.indicator (fun _ => (1 : ℝ)) y)) volume :=
    (hCint.add hCpint).const_mul (L ^ 2 * ‖t‖ ^ 2)
  calc ∫ y : ℝ³, (chiSmall M y - chiSmall M (y - t)) ^ 2
      ≤ ∫ y : ℝ³, L ^ 2 * ‖t‖ ^ 2 * (C.indicator (fun _ => (1 : ℝ)) y
          + Cp.indicator (fun _ => (1 : ℝ)) y) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun y => sq_nonneg _)) hRint
          (Filter.Eventually.of_forall hpt)
    _ = L ^ 2 * ‖t‖ ^ 2 * ((volume C).toReal + (volume Cp).toReal) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hCint hCpint,
          MeasureTheory.integral_indicator_const (1 : ℝ) hCmeas,
          MeasureTheory.integral_indicator_const (1 : ℝ) hCpmeas]
        simp only [MeasureTheory.Measure.real_def, smul_eq_mul, mul_one]
    _ = 2 * L ^ 2 * ‖t‖ ^ 2 := by rw [hCpvol, hCvol]; ring

/-- Global quadratic deviation of the cosine-`M` self-convolution for every `M ≥ 1`
(no restriction on `M`): there is `C ≥ 0` with `|(χ_M ⋆ χ_M)(t) − 1| ≤ C·‖t‖²` for
EVERY `t : ℝ³`.

Route.  (i) `M ≥ 3`: `Submission.BoseGases.convDevC_bound`
(`Submission/Work/Conv3SmallGlobal.lean`) gives `‖(χ_M⋆χ_M)(t) − 1‖ ≤ convDevC M·‖t‖²`
for all `t`.  (ii) `M ≤ 2`: the exact identity
`1 − conv3Small M t = (1/2)∫_y (χ_M y − χ_M (y−t))² dy` (from `chiSmall_L2`:
`∫χ_M² = 1`, `chiSmall_even`, and translation invariance of Lebesgue measure), the
pointwise bound `|χ_M y − χ_M (y−t)| ≤ L‖t‖` where `L` is a Lipschitz constant for
`chiSmall M` (telescope the product of the three 1-D factors `z ↦ zeta1d (z_j)`, each
`π`-Lipschitz, all factors in `[0,1]`; `chiSmall M = chiSmallBase M / √(chiSmallNormSq M)`),
and the support obstruction: the integrand vanishes unless `y` or `y−t` lies in the unit
cube `{|z_j| ≤ 1/2}` (`chiSmall_support_mem_abs_le`), whose volume is `1`
(`Submission.BoseGases.eucl_cube_volume`), so `1 − conv3Small M t ≤ 2L²‖t‖²`; combine with
the `‖t‖ ≥ 1` fallback `|conv3Small M t| ≤ 1` (`conv3Small_abs_le_one`) as in
`Submission.BoseGases.conv3Small_quadratic_dev`.

Route used here: the Lipschitz bound `L` of `chiSmall M` exists for EVERY `M ≥ 1`
(`Work.BoseFixB1S.chiSmall_lipschitz`), and the support obstruction bounds the
polarisation integral globally in `t`; so no case split on `M` is needed —
`1 − conv3Small M t = (1/2)∫(χ_M y − χ_M (y−t))² dy ≤ L²‖t‖²`, i.e. `C := L²`
works for all `t`. -/
theorem conv3Small_dev_quadratic {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.conv3Small M t - 1| ≤ C * ‖t‖ ^ 2 := by
  obtain ⟨L, hL0, hLip⟩ := chiSmall_lipschitz hM
  refine ⟨L ^ 2, sq_nonneg L, fun t => ?_⟩
  have hid := devQuad_one_sub_eq_half_integral hM t
  have hbd := devQuad_integral_diff_sq_le hM hLip t
  have hnonneg : 0 ≤ 1 - conv3Small M t := by
    rw [hid]
    exact mul_nonneg (by norm_num) (integral_nonneg (fun y => sq_nonneg _))
  have hle : 1 - conv3Small M t ≤ L ^ 2 * ‖t‖ ^ 2 := by
    rw [hid]
    nlinarith [hbd]
  rw [abs_sub_comm, abs_of_nonneg hnonneg]
  exact hle

end Work.BoseFixB1S
