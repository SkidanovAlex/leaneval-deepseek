import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.LocDataExt.Majorant5
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.FTS.StrongEps.EpsE4Thr.TracesAux.abs_DthIter_Gam_le
import Submission.Work.FTS.NonlinRows.AkRhoJetBasic
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.OpenPkg.Good
import Submission.Work.FTS.H2.InvOneAddSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ℋ⁴`-honesty of `AK α` for every `α > 0`

`Work.FTS.NonlinRows.NAux3.HkMem_AK` proves `Work.Spaces.HkMem α 4 (Work.Construction.AK α)`
under the extra hypothesis `α ≤ 1`.  The only place that hypothesis enters is the *numerical*
control of the angular majorant: for `α ≤ 1` the exponent `17α/30 - 1` of the dominating
`sin(2θ)`-power is `≤ 0`, so the delivered `angMaj_mem` (which uses `Work.Spaces.sin_two_rpow`
in its stated range `-1 < p ≤ 0`) applies.

This file removes the restriction.  The mathematical content is unchanged and in fact slightly
sharper: the pointwise angular inequality

`Γ(θ)² sin(2θ)^{-γ} ≤ 2^{-2α/3} sin(2θ)^{17α/30-1}`

holds for every `α > 0` (its proof never used `α ≤ 1`; only the *integrability* of the
majorant `sin(2θ)^{17α/30-1}` needs a case distinction on the sign of `17α/30 - 1`, the
positive case being trivial because `sin(2θ) ≤ 1`).  Consequently `angMaj α` is integrable on
`Iθ` for every `α > 0`, and the separable-datum majorant
`LocDataExt.HkIntegrand_sepGam_le` (which is stated for arbitrary `α > 0`) finishes the job.

The remaining two inputs are

* the *radial* jet bound `AkRhoJetBasic.akRho_jet_bound` for `2z²/(1+z)³`, transported to the
  normalised factor `2z²/((1+z)³c(α))` by `DzIter_const_mul` — no lower bound on `c(α)` is
  needed (the factor enters only through its square);
* the *angular* jet bound `|D_θ^i Γ| ≤ C·Γ` on `Iθ` (`Spaces.dthU_iter_Gam_abs_bound`,
  available for every `α > 0`), which produces the constant `Rθ` of the majorant.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## `c α ≠ 0` for every `α > 0` -/

/-- The normalisation constant `c α = ∫_{Iθ} Γ(θ)K(θ) dθ` is positive (hence nonzero) for every
`α > 0`: the integrand is nonnegative everywhere and `≥ 3(1/4)^{α/3+1}` on `[π/6, π/4]`,
where `sin θ cos²θ ≥ 1/4`. -/
theorem c_ne_zero_of_pos (α : ℝ) (hα : 0 < α) : Work.Spaces.c α ≠ 0 := by
  have hsub : Set.Icc (π / 6) (π / 4) ⊆ Work.Spaces.Iθ := fun θ hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hint : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      Work.Spaces.Iθ := Work.Spaces.CAux.integrableOn_GamK α hα
  have hnonneg : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (0 : ℝ) ≤ Work.Spaces.Gam α θ * Work.Spaces.K θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact (Work.Spaces.gamK_bounds α θ hα hθ).1
  have hle : ∫ θ in Set.Icc (π / 6) (π / 4), Work.Spaces.Gam α θ * Work.Spaces.K θ
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ :=
    MeasureTheory.setIntegral_mono_set hint hnonneg (Filter.Eventually.of_forall hsub)
  have hconst_le : ∀ θ ∈ Set.Icc (π / 6) (π / 4),
      3 * (1 / 4 : ℝ) ^ (α / 3 + 1) ≤ Work.Spaces.Gam α θ * Work.Spaces.K θ := by
    intro θ hθ
    have hs : (1 / 2 : ℝ) ≤ Real.sin θ := by
      have h1 : Real.sin (π / 6) ≤ Real.sin θ :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
          (by linarith [hθ.2, Real.pi_pos]) hθ.1
      rwa [Real.sin_pi_div_six] at h1
    have hc2 : (1 / 2 : ℝ) ≤ Real.cos θ ^ 2 := by
      have h1 : Real.cos (π / 4) ≤ Real.cos θ :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hθ.1, Real.pi_pos])
          (by linarith [Real.pi_pos]) hθ.2
      rw [Real.cos_pi_div_four] at h1
      have hsq : (√2 / 2) ^ 2 = (1 / 2 : ℝ) := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      have h2 : (√2 / 2) ^ 2 ≤ (Real.cos θ) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      linarith [h2, hsq]
    have hsin0 : (0 : ℝ) ≤ Real.sin θ := le_trans (by norm_num) hs
    have hu : (1 / 4 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2 := by
      have h1 := mul_le_mul hs hc2 (by norm_num : (0 : ℝ) ≤ 1 / 2) hsin0
      rw [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num] at h1
      exact h1
    have hp : (0 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2 := le_trans (by norm_num) hu
    have hGam : (1 / 4 : ℝ) ^ (α / 3 + 1)
        ≤ (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 + 1) :=
      Real.rpow_le_rpow (by norm_num) hu (by linarith)
    have hprod : Work.Spaces.Gam α θ * Work.Spaces.K θ
        = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3 + 1) := by
      rw [Work.Spaces.Gam, Work.Spaces.K]
      have hsplit : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
            * (3 * Real.sin θ * Real.cos θ ^ 2)
          = 3 * ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
              * (Real.sin θ * Real.cos θ ^ 2) ^ (1 : ℝ)) := by
        rw [Real.rpow_one]; ring
      rw [hsplit, ← Real.rpow_add' hp (show α / 3 + 1 ≠ 0 by linarith)]
    rw [hprod]
    exact mul_le_mul_of_nonneg_left hGam (by norm_num)
  have hge : 3 * (1 / 4 : ℝ) ^ (α / 3 + 1) * volume.real (Set.Icc (π / 6) (π / 4))
      ≤ ∫ θ in Set.Icc (π / 6) (π / 4), Work.Spaces.Gam α θ * Work.Spaces.K θ :=
    MeasureTheory.setIntegral_ge_of_const_le_real measurableSet_Icc
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hconst_le
      (hint.mono_set hsub)
  have hvol : volume.real (Set.Icc (π / 6) (π / 4)) = π / 12 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hpos : 0 < 3 * (1 / 4 : ℝ) ^ (α / 3 + 1) * volume.real (Set.Icc (π / 6) (π / 4)) := by
    have hb : 0 < (1 / 4 : ℝ) ^ (α / 3 + 1) := Real.rpow_pos_of_pos (by norm_num) _
    rw [hvol]
    positivity
  have hcpos : 0 < Work.Spaces.c α := lt_of_lt_of_le hpos (le_trans hge hle)
  exact ne_of_gt hcpos

/-! ## Smoothness of `AK α` on the open quadrant, for every `α > 0` -/

/-- `AK α = (Γ(θ)/c α)·2z²/(1+z)³` is `C⁴` on the open quadrant for every `α > 0`
(the `α ≤ 1` in `Work.FTS.OpenPkg.contDiffOn_four_AK` was only used to see `c α ≠ 0`). -/
theorem contDiffOn_four_AK_gen (α : ℝ) (hα : 0 < α) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.AK α)) Work.FTS.EllipticEst.Q0 := by
  have hcne : Work.Spaces.c α ≠ 0 := c_ne_zero_of_pos α hα
  have hGam := (Work.FTS.OpenPkg.contDiffOn_Gam_Q0 α 4).div contDiffOn_const
    (fun p hp => hcne)
  have hrad : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => 2 * p.1 ^ 2 / (1 + p.1) ^ 3)
      Work.FTS.EllipticEst.Q0 :=
    (contDiffOn_const.mul (contDiffOn_fst.pow 2)).div
      ((contDiffOn_const.add contDiffOn_fst).pow 3)
      (fun p hp => pow_ne_zero 3 (ne_of_gt
        (by linarith [Set.mem_Ioi.mp hp.1] : (0 : ℝ) < 1 + p.1)))
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)) = Function.uncurry (Work.Construction.AK α) := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Work.Construction.AK]
  rw [← hfun]
  exact hGam.mul hrad

/-! ## The angular pointwise bound, for every `α > 0` -/

/-- **The sharp angular bound**: `Γ(θ)² sin(2θ)^{-γ(α)} ≤ 2^{-2α/3} sin(2θ)^{17α/30-1}` on `Iθ`,
for every `α > 0`.  (This is `Work.FTS.LocData.GamSq_sin_neg_gam_le` without the hypothesis
`α ≤ 1`, which its proof never used: the only step needing care is the multiplicative identity
`X^{2α/3}·X^{-γ} = X^{17α/30-1}`, which is handled below by the case `X = 0`.) -/
theorem GamSq_sin_neg_gam_le_gen (α : ℝ) (hα : 0 < α) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hX0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; positivity
  have hexp : 2 * α / 3 + -(Work.Spaces.gam α) = 17 * α / 30 - 1 := by
    simp only [Work.Spaces.gam]; ring
  have hΓ2 : Work.Spaces.Gam α θ ^ 2 = (Real.sin θ * Real.cos θ ^ 2) ^ (2 * α / 3) := by
    rw [Work.Spaces.Gam]
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2)]
    congr 1
    ring
  have hc2 : Real.cos θ ^ 2 ≤ Real.cos θ := by nlinarith [hc0, Real.cos_le_one θ]
  have hYle : Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * Real.cos θ :=
    mul_le_mul_of_nonneg_left hc2 hs0
  have hstat : Work.Spaces.Gam α θ ^ 2 ≤ (Real.sin θ * Real.cos θ) ^ (2 * α / 3) := by
    rw [hΓ2]
    exact Real.rpow_le_rpow (by positivity) hYle (by linarith : (0 : ℝ) ≤ 2 * α / 3)
  rcases eq_or_lt_of_le hX0 with hXeq | hXpos
  · -- `sin(2θ) = 0`: both sides are `0 ≤ ·`
    have hz : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) = 0 := by
      rw [← hXeq]
      exact Real.zero_rpow (by simp only [Work.Spaces.gam]; linarith)
    rw [hz, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hX0 _)
  · have hstep2 : (Real.sin θ * Real.cos θ) ^ (2 * α / 3)
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
      have hY : Real.sin θ * Real.cos θ = Real.sin (2 * θ) / 2 := by
        rw [Real.sin_two_mul]; ring
      rw [hY, Work.FTS.LocData.angMaj_div_two_rpow _ hX0, mul_assoc,
        ← Real.rpow_add hXpos, hexp]
    calc Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ (Real.sin θ * Real.cos θ) ^ (2 * α / 3)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hstat (Real.rpow_nonneg hX0 _)
      _ = 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := hstep2

/-! ## Integrability of the angular majorants for every `α > 0` -/

/-- `sin(2θ)^p` is integrable on `Iθ` as soon as `p > -1` (for `p > 0` it is bounded by `1`). -/
theorem integrableOn_sinTwo_rpow (p : ℝ) (hp : -1 < p) :
    IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ := by
  by_cases hp0 : p ≤ 0
  · exact (Work.Spaces.sin_two_rpow p hp hp0).1
  · have hp0' : 0 < p := not_le.mp hp0
    have hbdd : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
      MeasureTheory.integrableOn_const
        (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    refine hbdd.mono' ?_ ?_
    · exact (Measurable.pow_const
        (Real.measurable_sin.comp (measurable_const.mul measurable_id)) p).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      have hX0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hX0 _)]
      exact Real.rpow_le_one hX0 (Real.sin_le_one _) hp0'.le

/-- Integrability of `Γ(θ)² sin(2θ)^{-γ}` on `Iθ`, for every `α > 0`. -/
theorem integrableOn_gamSq_sin_neg_gam (α : ℝ) (hα : 0 < α) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  have hmeas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIntX : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
      Work.Spaces.Iθ :=
    integrableOn_sinTwo_rpow (17 * α / 30 - 1) (by linarith)
  refine (hIntX.const_mul (2 ^ (-(2 * α / 3)))).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem hmeas] with θ hθ
    have hX0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hX0 _))]
    exact GamSq_sin_neg_gam_le_gen α hα hθ

/-- Integrability of `Γ(θ)² sin(2θ)^{-η}` on `Iθ`, for every `α > 0`. -/
theorem integrableOn_gamSq_sin_neg_eta (α : ℝ) (hα : 0 < α) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hmeas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIntX : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by simp only [Work.Spaces.eta]; norm_num)
      (by simp only [Work.Spaces.eta]; norm_num)).1
  refine hIntX.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem hmeas] with θ hθ
    have hX0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hX0 _))]
    exact Work.FTS.LocData.GamSq_sin_neg_eta_le α hα hθ

/-- **`angMaj α` is integrable on `Iθ` for every `α > 0`** (the `α ≤ 1` of
`Work.FTS.LocData.angMaj_mem` was only used to keep the exponent `17α/30-1` nonpositive). -/
theorem integrableOn_angMaj_of_pos (α : ℝ) (hα : 0 < α) :
    IntegrableOn (fun θ => Work.FTS.LocData.angMaj α θ) Work.Spaces.Iθ := by
  have hInt0 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hsum : IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (integrableOn_gamSq_sin_neg_gam α hα).add (integrableOn_gamSq_sin_neg_eta α hα)
  have hangMaj : (fun θ : ℝ => Work.FTS.LocData.angMaj α θ) = fun θ : ℝ =>
      (Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + Work.Spaces.Gam α θ ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) + 1 := by
    funext θ
    rw [Work.FTS.LocData.angMaj_apply]
  rw [hangMaj]
  exact hsum.add hInt0

/-! ## The angular jet bound for `Γ`, for every `α > 0` -/

/-- `|D_θ^i Γ| ≤ C·Γ` on all of `Iθ`, for every `i` and every `α > 0`. -/
theorem GamJetBound (α : ℝ) (hα : 0 < α) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ C * (Work.Spaces.Gam α θ) ^ 2 := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    refine ⟨1, zero_le_one, fun θ _ => ?_⟩
    simp
  · obtain ⟨M, hM0, hM⟩ :=
      Work.FTS.StrongEps.EpsE4Thr.TracesAux.exists_Tfun_bound α (i - 1)
    refine ⟨(α * M) ^ 2, sq_nonneg _, fun θ hθ => ?_⟩
    rw [Work.FTS.LocData.DthIter_rad_eq i (fun θ' => Work.Spaces.Gam α θ') 0 θ]
    have hb := Work.Spaces.dthU_iter_Gam_abs_bound i hpos α hα M hM θ hθ
    have h2 : (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ) ^ 2
        ≤ (α * M * Work.Spaces.Gam α θ) ^ 2 := by
      rw [← sq_abs (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ)]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    calc (Work.Spaces.dthU^[i] (fun t => Work.Spaces.Gam α t) θ) ^ 2
        ≤ (α * M * Work.Spaces.Gam α θ) ^ 2 := h2
      _ = (α * M) ^ 2 * (Work.Spaces.Gam α θ) ^ 2 := by ring

/-! ## The `ℋ⁴`-membership -/

theorem HkMemAKGeneral (α : ℝ) (hα : 0 < α) : Work.Spaces.HkMem α 4 (Work.Construction.AK α) := by
  obtain ⟨R₀, hR₀0, hB₀⟩ := Work.FTS.NonlinRows.AkRhoJetBasic.akRho_jet_bound
  choose C hC using fun i : ℕ => GamJetBound α hα i
  set Rθ : ℝ := ∑ i ∈ Finset.range 5, C i with hRθdef
  have hRθ : 0 ≤ Rθ := by
    rw [hRθdef]
    exact Finset.sum_nonneg (fun i _ => (hC i).1)
  have hJet : ∀ i ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.DthIter i (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2
        ≤ Rθ * (Work.Spaces.Gam α θ) ^ 2 := by
    intro i hi θ hθ
    have h1 := (hC i).2 θ hθ
    have h2 : C i ≤ Rθ := by
      rw [hRθdef]
      exact Finset.single_le_sum (fun j _ => (hC j).1) (Finset.mem_range.mpr (by omega))
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
  set R : ℝ := R₀ * (1 / Work.Spaces.c α) ^ 2 with hRdef
  have hR0 : 0 ≤ R := by
    rw [hRdef]; positivity
  have hB : ∀ j ≤ 4, ∀ z ∈ Work.Spaces.Iz, ∀ θ' : ℝ,
      (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) z θ'
        * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
    intro j hj z hz θ'
    have hfun : (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α)
        = fun z _ : ℝ => (1 / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) := by
      funext z θ''
      rw [one_div]
      ring
    have hmult := congrFun (congrFun (Work.FTS.LocDataExt.DzIter_const_mul
      (1 / Work.Spaces.c α) (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) j) z) θ'
    have hsq : (Work.Spaces.DzIter j
          (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) z θ'
        * Work.Spaces.w z) ^ 2
        = (1 / Work.Spaces.c α) ^ 2
          * (Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) z θ'
            * Work.Spaces.w z) ^ 2 := by
      rw [hfun]
      rw [hmult]
      ring
    rw [hsq]
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have hw0 : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
      have hz0' : Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) 0 θ'
          * Work.Spaces.w 0 = 0 := by rw [hw0, mul_zero]
      rw [hz0']
      have hsq0 : (1 / Work.Spaces.c α) ^ 2 * (0 : ℝ) ^ 2 = 0 := by ring
      rw [hsq0]
      exact div_nonneg hR0 (by norm_num)
    · have h1 := hB₀ j hj hz0 θ'
      calc (1 / Work.Spaces.c α) ^ 2
            * (Work.Spaces.DzIter j (fun z _ : ℝ => 2 * z ^ 2 / (1 + z) ^ 3) z θ'
              * Work.Spaces.w z) ^ 2
          ≤ (1 / Work.Spaces.c α) ^ 2 * (R₀ / (1 + z) ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = R / (1 + z) ^ 2 := by rw [hRdef]; ring
  refine Work.FTS.LocData.HkMem_of_majorant α 4 (f := Work.Construction.AK α)
    (M := fun z θ => (((5 : ℝ) + 25 * Rθ) * R / (1 + z) ^ 2)
      * Work.FTS.LocData.angMaj α θ)
    (Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn (F := Work.Construction.AK α) α
      (n := 4) (k := 4) le_rfl (contDiffOn_four_AK_gen α hα)) ?_ ?_ ?_
  · -- the `θ`-slices of the majorant are integrable
    intro z _hz
    exact (integrableOn_angMaj_of_pos α hα).const_mul
      (((5 : ℝ) + 25 * Rθ) * R / (1 + z) ^ 2)
  · -- the `z`-integral of the majorant is integrable
    have hkey : IntegrableOn (fun z : ℝ => (((5 : ℝ) + 25 * Rθ) * R
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        (Set.Ioi 0) :=
      Work.FTS.H2.InvOneAddSq.1.const_mul (((5 : ℝ) + 25 * Rθ) * R
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ))
    have hkeyIz : IntegrableOn (fun z : ℝ => (((5 : ℝ) + 25 * Rθ) * R
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        (Set.Ici 0) :=
      hkey.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have heqfun : (fun z : ℝ => (((5 : ℝ) + 25 * Rθ) * R
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.LocData.angMaj α θ)) * (1 / (1 + z)) ^ 2)
        = fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            (((5 : ℝ) + 25 * Rθ) * R / (1 + z) ^ 2) * Work.FTS.LocData.angMaj α θ := by
      funext z
      rw [MeasureTheory.integral_const_mul]
      rw [one_div, inv_pow, div_eq_mul_inv]
      ring
    rw [← heqfun]
    exact hkeyIz
  · -- the pointwise domination
    intro z hz θ hθ
    have hAK : Work.Construction.AK α
        = fun z θ => (2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) * Work.Spaces.Gam α θ := by
      funext z θ
      rw [Work.Construction.AK]
      ring
    rw [hAK]
    have h1 := Work.FTS.LocDataExt.HkIntegrand_sepGam_le α hα 4
      (ρ := fun z => 2 * z ^ 2 / (1 + z) ^ 3 / Work.Spaces.c α) hR0 hRθ hB hJet hz hθ
    refine le_trans h1 (le_of_eq ?_)
    push_cast
    ring

end Work.FTS.StrongEps.EpsRLX
