import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.PotSupport
import Submission.Scat1D
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Glue between the radial 1D weak equation and the half-line regularity theorem

`Scat1D.scattering_1D_weak_equation_halfLine` gives, for a radial potential
`v` and a radial weak scattering solution `w`, the 1D weak equation

    ∫_{r>0} u·χ''  =  −(1/2)·∫_{r>0} r·gprof·χ      (∀ χ ∈ C∞c((0,∞)))

with `u(r) := r · radialProfile w r` and
`gprof(r) := radialProfile v r · (1 − radialProfile w r)`.

This module provides the two glue facts that the regularity programme
(`Submission.HalfLineReg.weak_snd_regularity_Ioi`) needs to apply on an
arbitrary half-line `(a, ∞)`, `a > 0`:

1. **`scatH` is integrable on `(a,∞)`** — with `scatH(r) := −(1/2)·r·gprof(r)`
   (`h` of the regularity theorem).  The profile `r ↦ r·gprof(r)` is integrable
   on `(a, ∞)` because its 3D lift `g(x) := v(x)·(1−w(x))` is *locally*
   integrable (`IsScatteringSolution.rhs_integrable`) and vanishes outside the
   ball `B(0,R)` (radial: `radialProfile v r = 0` for `r ≥ R`); the radial
   change of variables (`RadialIntegral.integrable_radial_ball_r3`) links the
   two, and on `r ≥ a` one has `r ≤ r²/a`.

2. **`scatH_weak_eq`** — restricting the half-line equation to test functions
   supported in `(a,∞)` gives the hypothesis of `weak_snd_regularity_Ioi` on
   `(a,∞)` (both integrands are supported in `(a,∞)`).

Also records the convenient local-integrability of `u` on `(a,∞)` (already in
`ProfileLocInt.profile_mul_locallyIntegrableOn`).
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable def scatH (v w : ℝ³ → ℝ) (r : ℝ) : ℝ :=
  -(1 / 2) * r * (radialProfile v r) * (1 - radialProfile w r)

lemma scatH_eq_zero_of_abs_ge {v w : ℝ³ → ℝ} {R : ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    {r : ℝ} (hRr : R ≤ |r|) : scatH v w r = 0 := by
  unfold scatH
  have hv0 : radialProfile v r = 0 := by
    unfold radialProfile
    exact v_eq_zero_of_norm_ge hv_supp (x := r • radU0) (by simpa [norm_smul_radU0] using hRr)
  simp [hv0]

lemma radial_mul_one_sub {v w : ℝ³ → ℝ} (hvrad : IsRadial v) (hrad : IsRadial w) :
    IsRadial (fun x : ℝ³ => v x * (1 - w x)) := by
  intro x y hxy
  change v x * (1 - w x) = v y * (1 - w y)
  rw [hvrad x y hxy, hrad x y hxy]

lemma radialProfile_mul_one_sub (v w : ℝ³ → ℝ) (r : ℝ) :
    radialProfile (fun x : ℝ³ => v x * (1 - w x)) r =
      radialProfile v r * (1 - radialProfile w r) := by
  simp [radialProfile]

lemma scatH_eq {v w : ℝ³ → ℝ} (r : ℝ) :
    scatH v w r = -(1 / 2) * (r * (radialProfile v r * (1 - radialProfile w r))) := by
  unfold scatH
  ring

/-- Pointwise domination: for 0 < a ≤ r, |r·X| ≤ (1/a)·|r²·X|. -/
lemma abs_mul_ge_of_one_le (a r : ℝ) (X : ℝ) (ha : 0 < a) (hra : a ≤ r) :
    |r * X| ≤ (1 / a) * |r ^ 2 * X| := by
  have hpos : 0 < r := lt_of_lt_of_le ha hra
  have hr0 : 0 < r ^ 2 := sq_pos_of_pos hpos
  rw [abs_mul, abs_mul, abs_of_pos hpos, abs_of_pos hr0]
  have hle : r ≤ (1 / a) * r ^ 2 := by
    rw [show (1 / a) * r ^ 2 = r ^ 2 / a by ring]
    rw [le_div_iff₀ ha]
    have hmul : a * r ≤ r * r := mul_le_mul_of_nonneg_right hra (le_of_lt hpos)
    nlinarith
  have hres := mul_le_mul_of_nonneg_right hle (abs_nonneg X)
  rw [← mul_assoc]
  exact hres

/-- main integrability of r·gprof -/
theorem rgprof_integrable_Ioi {v w : ℝ³ → ℝ} {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hvrad : IsRadial v) (hrad : IsRadial w) (hw : IsScatteringSolution w v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) :
    MeasureTheory.IntegrableOn
      (fun r : ℝ => r * (radialProfile v r * (1 - radialProfile w r))) (Set.Ioi a) volume := by
  let gprof : ℝ → ℝ := fun r => radialProfile v r * (1 - radialProfile w r)
  change IntegrableOn (fun r : ℝ => r * gprof r) (Set.Ioi a) volume
  have hpg : ∀ r : ℝ, radialProfile (fun x : ℝ³ => v x * (1 - w x)) r = gprof r := by
    intro r
    simp [gprof, radialProfile_mul_one_sub]
  let g3 : ℝ³ → ℝ := fun x => v x * (1 - w x)
  have hg3li : LocallyIntegrable g3 := by
    change LocallyIntegrable (v * (1 - w))
    exact hw.rhs_integrable
  have hg3rad : IsRadial g3 := by
    simpa [g3] using radial_mul_one_sub hvrad hrad
  have hgcb : IntegrableOn g3 (Metric.closedBall (0 : ℝ³) R) volume := by
    exact hg3li.integrableOn_isCompact (isCompact_closedBall (0 : ℝ³) R)
  have hgball : IntegrableOn g3 (Metric.ball (0 : ℝ³) R) volume :=
    hgcb.mono_set (Metric.ball_subset_closedBall)
  have hleft : IntegrableOn (fun x : ℝ³ => radialProfile g3 ‖x‖) (Metric.ball (0 : ℝ³) R) volume := by
    apply hgball.congr_fun _ (isOpen_ball.measurableSet)
    intro x hx
    exact radial_eq_profile hg3rad x
  have hradint : IntegrableOn (fun r : ℝ => r ^ 2 * radialProfile g3 r) (Set.Ioo 0 R) volume := by
    exact (integrable_radial_ball_r3 (f := radialProfile g3) R).mp hleft
  have hradg : IntegrableOn (fun r : ℝ => r ^ 2 * gprof r) (Set.Ioo 0 R) volume := by
    apply hradint.congr_fun _ isOpen_Ioo.measurableSet
    intro r hr
    dsimp
    rw [hpg r]
  have hsub_aR : Set.Ioo a R ⊆ Set.Ioo 0 R := by
    intro r hr
    exact ⟨lt_trans ha hr.1, hr.2⟩
  have hradg_aR : IntegrableOn (fun r : ℝ => r ^ 2 * gprof r) (Set.Ioo a R) volume :=
    hradg.mono_set hsub_aR
  have hb1 : IntegrableOn (fun r : ℝ => |r ^ 2 * gprof r|) (Set.Ioo a R) volume := by
    change Integrable (fun r : ℝ => |r ^ 2 * gprof r|) (volume.restrict (Set.Ioo a R))
    exact hradg_aR.abs
  have hb2 : IntegrableOn (fun r : ℝ => (1 / a) * |r ^ 2 * gprof r|) (Set.Ioo a R) volume := by
    change Integrable (fun r : ℝ => (1 / a) * |r ^ 2 * gprof r|) (volume.restrict (Set.Ioo a R))
    exact hb1.const_mul (1 / a)
  have hsm_h : AEStronglyMeasurable (fun r : ℝ => r ^ 2 * gprof r)
      (volume.restrict (Set.Ioo a R)) := by
    exact (show Integrable (fun r : ℝ => r ^ 2 * gprof r) (volume.restrict (Set.Ioo a R)) from hradg_aR).aestronglyMeasurable
  have hcinv : ContinuousOn (fun r : ℝ => r⁻¹) (Set.Ioo a R) := by
    refine continuousOn_inv₀.mono ?_
    intro r hr
    exact ne_of_gt (lt_trans ha hr.1)
  have hsm_inv : AEStronglyMeasurable (fun r : ℝ => r⁻¹)
      (volume.restrict (Set.Ioo a R)) := by
    exact ContinuousOn.aestronglyMeasurable hcinv isOpen_Ioo.measurableSet
  have hsm_g : AEStronglyMeasurable gprof (volume.restrict (Set.Ioo a R)) := by
    have hsm_1 : AEStronglyMeasurable (fun r : ℝ => r⁻¹ * (r ^ 2 * gprof r))
        (volume.restrict (Set.Ioo a R)) := hsm_inv.mul hsm_h
    have hsm_2 : AEStronglyMeasurable (fun r : ℝ => r⁻¹ * (r⁻¹ * (r ^ 2 * gprof r)))
        (volume.restrict (Set.Ioo a R)) := hsm_inv.mul hsm_1
    refine hsm_2.congr ?_
    change ∀ᵐ (r : ℝ) ∂(volume.restrict (Set.Ioo a R)),
      r⁻¹ * (r⁻¹ * (r ^ 2 * gprof r)) = gprof r
    rw [ae_restrict_iff' isOpen_Ioo.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro r hr
    have hrne : r ≠ 0 := ne_of_gt (lt_trans ha hr.1)
    calc
      r⁻¹ * (r⁻¹ * (r ^ 2 * gprof r)) = (r⁻¹ * r⁻¹ * r ^ 2) * gprof r := by ring
      _ = gprof r := by
        have hrr : r⁻¹ * r⁻¹ * r ^ 2 = 1 := by
          field_simp [hrne]
        rw [hrr, one_mul]
  have hsm_f : AEStronglyMeasurable (fun r : ℝ => r * gprof r)
      (volume.restrict (Set.Ioo a R)) := by
    have hsm_id : AEStronglyMeasurable (fun r : ℝ => r) (volume.restrict (Set.Ioo a R)) := by
      simpa using (Continuous.aestronglyMeasurable continuous_id :
        AEStronglyMeasurable (fun r : ℝ => r) (volume.restrict (Set.Ioo a R)))
    exact hsm_id.mul hsm_g
  have hfint_bounded : IntegrableOn (fun r : ℝ => r * gprof r) (Set.Ioo a R) volume := by
    have bound_ae : ∀ᵐ (r : ℝ) ∂(volume.restrict (Set.Ioo a R)),
        ‖r * gprof r‖ ≤ (1 / a) * |r ^ 2 * gprof r| := by
      rw [ae_restrict_iff' isOpen_Ioo.measurableSet]
      refine Filter.Eventually.of_forall ?_
      intro r hr
      rcases hr with ⟨hra, hrR⟩
      have hmain : |r * gprof r| ≤ (1 / a) * |r ^ 2 * gprof r| := by
        exact abs_mul_ge_of_one_le a r (gprof r) ha (le_of_lt hra)
      simpa using hmain
    exact Integrable.mono' hb2 hsm_f bound_ae
  have hzero_tail : ∀ r ∈ Set.Ioi a ∩ {r : ℝ | R ≤ r}, r * gprof r = 0 := by
    intro r hr
    have hRr : R ≤ r := hr.2
    have hRleabs : R ≤ |r| := by
      rw [abs_of_nonneg (le_trans (le_of_lt hR) hRr)]
      exact hRr
    have hv0 : radialProfile v r = 0 := by
      unfold radialProfile
      exact v_eq_zero_of_norm_ge hv_supp (x := r • radU0) (by simpa [norm_smul_radU0] using hRleabs)
    simp [gprof, hv0]
  have htail : IntegrableOn (fun r : ℝ => r * gprof r) (Set.Ioi a ∩ {r : ℝ | R ≤ r}) volume := by
    have hz : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioi a ∩ {r : ℝ | R ≤ r}) volume :=
      MeasureTheory.integrableOn_zero
    refine hz.congr_fun ?_ ((measurableSet_Ioi : MeasurableSet (Set.Ioi a)).inter measurableSet_Ici)
    intro r hr
    exact (hzero_tail r hr).symm
  have hsplit : Set.Ioi a = Set.Ioo a R ∪ (Set.Ioi a ∩ {r : ℝ | R ≤ r}) := by
    ext r
    constructor
    · intro hr
      by_cases hRr : R ≤ r
      · exact Or.inr ⟨hr, hRr⟩
      · exact Or.inl ⟨hr, lt_of_not_ge hRr⟩
    · intro hr
      rcases hr with h | h
      · exact h.1
      · exact h.1
  rw [hsplit]
  exact hfint_bounded.union htail

theorem scatH_integrable_Ioi {v w : ℝ³ → ℝ} {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hvrad : IsRadial v) (hrad : IsRadial w) (hw : IsScatteringSolution w v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) :
    MeasureTheory.IntegrableOn (scatH v w) (Set.Ioi a) volume := by
  let gprof : ℝ → ℝ := fun r => radialProfile v r * (1 - radialProfile w r)
  have hmain := rgprof_integrable_Ioi (v := v) (w := w) (R := R) (a := a) hR ha hvrad hrad hw hv_supp
  have hpt : ∀ r : ℝ, scatH v w r = -(1 / 2) * (r * gprof r) := by
    intro r
    unfold scatH
    dsimp [gprof]
    ring
  have hcm : IntegrableOn (fun r : ℝ => -(1 / 2) * (r * gprof r)) (Set.Ioi a) volume := by
    change Integrable (fun r : ℝ => -(1 / 2) * (r * gprof r)) (volume.restrict (Set.Ioi a))
    exact (show Integrable (fun r : ℝ => r * gprof r) (volume.restrict (Set.Ioi a)) from hmain).const_mul (-(1 / 2))
  refine hcm.congr_fun ?_ measurableSet_Ioi
  intro r hr
  exact (hpt r).symm

theorem scatH_weak_eq_Ioi {v w : ℝ³ → ℝ} {R a : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hvrad : IsRadial v) (hrad : IsRadial w) (hw : IsScatteringSolution w v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) :
    ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ r : ℝ, χ r ≠ 0 → a < r) →
      (∫ r : ℝ in Set.Ioi a, (r * radialProfile w r) * deriv (deriv χ) r) =
      (∫ r : ℝ in Set.Ioi a, scatH v w r * χ r) := by
  intro χ hχ hχcs hχsupp
  let A : ℝ → ℝ := fun r => (r * radialProfile w r) * deriv (deriv χ) r
  let B : ℝ → ℝ := fun r => r * (radialProfile v r * (1 - radialProfile w r)) * χ r
  have h1 : (∫ r in Set.Ioi (0 : ℝ), A r) = -(1 / 2) * (∫ r in Set.Ioi (0 : ℝ), B r) := by
    simpa [A, B] using (scattering_1D_weak_equation ha hvrad hrad hw χ hχ hχcs hχsupp)
  have hA0 : ∀ r : ℝ, r ∈ Set.Ioo (0 : ℝ) a → A r = 0 := by
    intro r hr
    have hχ2 : deriv (deriv χ) r = 0 := deriv_chi_second_zero_on_Ioo hχsupp r hr
    simp [A, hχ2]
  have hB0 : ∀ r : ℝ, r ∈ Set.Ioo (0 : ℝ) a → B r = 0 := by
    intro r hr
    rcases hr with ⟨hr0, hra⟩
    have hχ0 : χ r = 0 := by
      by_contra h
      have : a < r := hχsupp r h
      linarith
    simp [B, hχ0]
  have hAint : (∫ r in Set.Ioi (0 : ℝ), A r) = (∫ r in Set.Ioi a, A r) :=
    integral_Ioi_eq_Ioi_of_zero_on_Ioo (f := A) (R := a) ha hA0
  have hBint : (∫ r in Set.Ioi (0 : ℝ), B r) = (∫ r in Set.Ioi a, B r) :=
    integral_Ioi_eq_Ioi_of_zero_on_Ioo (f := B) (R := a) ha hB0
  have hpt : ∀ r : ℝ, scatH v w r * χ r = -(1 / 2) * B r := by
    intro r
    dsimp [B]
    unfold scatH
    ring
  calc
    (∫ r : ℝ in Set.Ioi a, (r * radialProfile w r) * deriv (deriv χ) r)
        = (∫ r : ℝ in Set.Ioi a, A r) := by rfl
    _ = (∫ r : ℝ in Set.Ioi (0 : ℝ), A r) := hAint.symm
    _ = -(1 / 2) * (∫ r : ℝ in Set.Ioi (0 : ℝ), B r) := h1
    _ = -(1 / 2) * (∫ r : ℝ in Set.Ioi a, B r) := by rw [hBint]
    _ = (∫ r : ℝ in Set.Ioi a, -(1 / 2) * B r) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (∫ r : ℝ in Set.Ioi a, scatH v w r * χ r) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact (hpt r).symm



/-- The scattering profile `u(r) := r·radialProfile w r` is locally integrable
on `(a,∞)` for `a > 0` (restatement of `ProfileLocInt.profile_mul_locallyIntegrableOn`
in the scattering-solution context). -/
lemma scat_u_locallyIntegrable_Ioi {v w : ℝ³ → ℝ} {a : ℝ} (ha : 0 < a)
    (hrad : IsRadial w) (hw : IsScatteringSolution w v) :
    MeasureTheory.LocallyIntegrableOn (fun r : ℝ => r * radialProfile w r)
      (Set.Ioi a) volume := by
  exact profile_mul_locallyIntegrableOn (w := w) (R := a) ha hrad hw.lhs_integrable

end Submission.BoseGases
