/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassC/bessel_z` — Bessel's inequality for the angular modes, integrated in `z`

`Work.EllipticEst.ModalSolution.cmode_bessel` states Bessel's inequality for the angular
Dirichlet basis `eFam m` of `Lzero` *slicewise in `z`*:

  `∑_{m ≤ N} eNorm m · (cmode m F z)² ≤ ∫_θ (F z θ)² cos θ`.

This module integrates that bound in `z` against the radial weight `w(z)² = ((1+z)²/z²)²`,
which is the radial weight of the paper's `ℋ`-norms
(`HkSq α 0 g = ∫_z w(z)² ∫_θ g² sin(2θ)^{-η}`, `HkSq_zero_eq_w`).  The result
`sum_eNorm_cmode_sq_le_HkSq` is the source-side half of the level-`0` honest-modal estimate
(`NOTES_mode_sum_level0.md`): the weighted `L²`-norm of the mode coefficients of a source `F`
is dominated by the source's own `ℋ⁰`-norm.

The proof is measure-theoretic bookkeeping:

* the slicewise bound `cmode_bessel` is multiplied by `ENNReal.ofReal ((w z)²)` and pushed
  inside the `θ`-`lintegral` (`lintegral_const_mul'`, `ENNReal.ofReal_mul`);
* the resulting pointwise-in-`z` inequality is integrated in `z` (`lintegral_mono`), the finite
  sum is taken out of the `z`-`lintegral` (`lintegral_add_left'`, by induction on the `Finset`,
  using only `AEMeasurable` of the summands — supplied by `ModalSolution.aesm_cmode`);
* the right-hand side is turned into `ofReal (w z² · ∫_θ (F z θ)² cos θ)` by
  `ofReal_integral_eq_lintegral_ofReal` (the slice integrability hypothesis `hint`), and the
  corollary uses `cos θ ≤ sin(2θ)^{-η}` a.e. (the failure set is `{0}`, since `0 ^ (-η) = 0`
  and `cos 0 = 1`) plus the pointwise identity `HkIntegrand α 0 F = F² w² sin(2θ)^{-η}`.

This is step (2) of `NOTES_mode_sum_level0.md`.  Together with `ModeSumMain` (the
angular/radial mode-sum estimate) and `RadGreenModeEnergy` (the per-mode bound
`μ_m‖a_m w‖ ≤ ‖c_m w‖`) it gives the level-`0` estimate `HkSq α 0 Ψ_N ≤ C · HkSq α 0 F` for the
truncations `Ψ_N = psiTrunc α F N`, uniformly in `N`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.ClassC.ModeSumMain
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

local notation "Iθ" => Work.Spaces.Iθ
local notation "Iz" => Work.Spaces.Iz
local notation "w" => Work.Spaces.w
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "cmode" => Work.FTS.PhiStar.Series.cmode
local notation "eNorm" => Work.EllipticEst.ModalSolution.eNorm

/-! ## Elementary facts -/

/-- `w` is continuous on `(0,∞)`. -/
theorem continuousOn_w : ContinuousOn w (Set.Ioi (0 : ℝ)) := by
  have h : w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h]
  exact (continuousOn_const.add continuousOn_id).pow 2 |>.div (continuousOn_id.pow 2)
    (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

/-- The angular interval is measurable (needed as a *named* lemma so that `rw` can match it). -/
theorem measurableSet_Iθ : MeasurableSet Iθ := measurableSet_Icc

/-- `z ↦ w z² · (eNorm m · cmode m F z²)` is a.e. (strongly) measurable on `(0,∞)`. -/
theorem aemeasurable_modeTerm {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (m : ℕ) :
    AEMeasurable (fun z : ℝ => (w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hcm : AEMeasurable (fun z : ℝ => cmode m F z)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (Work.EllipticEst.ModalSolution.aesm_cmode hsm m).aemeasurable
  have hw : AEMeasurable (fun z : ℝ => (w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (continuousOn_w.aemeasurable measurableSet_Ioi).pow_const 2
  exact hw.mul ((hcm.pow_const 2).const_mul (eNorm m))

/-- The two Dirichlet endpoints of the angular interval are the zeros of `σ`. -/
theorem sEta_zero_at {θ : ℝ} (hθ : θ = 0 ∨ θ = Real.pi / 2) : sEta θ = 0 := by
  have hη : -(Work.Spaces.eta) ≠ 0 := by norm_num [Work.Spaces.eta]
  rcases hθ with h | h
  · rw [h, Work.FTS.EllipticEst.sEta, mul_zero, Real.sin_zero]
    exact Real.zero_rpow hη
  · rw [h, Work.FTS.EllipticEst.sEta]
    have h2 : 2 * (Real.pi / 2) = Real.pi := by ring
    rw [h2, Real.sin_pi]
    exact Real.zero_rpow hη

/-! ## The pointwise comparison `cos θ ≤ sin(2θ)^{-η}` -/

/-- `cos θ ≤ σ θ` for `θ ∈ Iθ`, `θ ≠ 0`.  (At `θ = 0` the inequality fails: `cos 0 = 1` while
Lean's `0 ^ (-η) = 0`; the single point `{0}` is null, which is all the applications need.) -/
theorem cos_le_sEta_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Iθ) (h0 : θ ≠ 0) : Real.cos θ ≤ sEta θ := by
  rcases eq_or_lt_of_le hθ.2 with h | h
  · subst h
    rw [Real.cos_pi_div_two, sEta_zero_at (Or.inr rfl)]
  · have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hθ.1 (Ne.symm h0), h⟩
    have h1 : 1 ≤ sEta θ := Work.FTS.EllipticEst.Honest.one_le_sEta hθ'
    have h2 : Real.cos θ ≤ 1 := Real.cos_le_one θ
    linarith

/-- `cos θ ≤ σ θ` almost everywhere on `Iθ`. -/
theorem ae_cos_le_sEta :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ), Real.cos θ ≤ sEta θ := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Iθ, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (0 : ℝ))
  intro θ hθ
  simp only [Set.mem_setOf_eq] at hθ ⊢
  by_contra hne
  exact hθ (fun hmem => cos_le_sEta_of_mem_Iθ hmem hne)

/-! ## Bessel's inequality integrated in `z` -/

/-- **Bessel's inequality for the mode coefficients, integrated in `z` against `w²`.**

  `∑_{m ≤ N} ∫⁻_z w(z)² · eNorm m · (cmode m F z)²  ≤  ∫⁻_z ofReal (w(z)² · ∫_θ (F z θ)² cos θ)`.

The hypothesis `hint` is the slice integrability of `(F z ·)² cos` (`z > 0`); it is what makes
the `θ`-`lintegral` on the right equal to `ofReal` of the `θ`-integral. -/
theorem bessel_z (F : ℝ → ℝ → ℝ) (N : ℕ) (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Iθ) :
    (∑ m ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * Real.cos θ) := by
  -- the slicewise Bessel bound, multiplied by `(w z)²` and pushed inside the θ-lintegral
  have hpt : ∀ z : ℝ, (∑ m ∈ Finset.range (N + 1),
        ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
      ≤ ∫⁻ θ in Iθ, ENNReal.ofReal ((w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ)) := by
    intro z
    have hb : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
          eNorm m * (cmode m F z) ^ 2)
        ≤ ∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * Real.cos θ) :=
      Work.EllipticEst.ModalSolution.cmode_bessel F z N
    have hsplit : ENNReal.ofReal (∑ m ∈ Finset.range (N + 1),
          eNorm m * (cmode m F z) ^ 2)
        = ∑ m ∈ Finset.range (N + 1), ENNReal.ofReal (eNorm m * (cmode m F z) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro m _
      exact mul_nonneg (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m)) (sq_nonneg _)
    rw [hsplit] at hb
    have hw : 0 ≤ (w z) ^ 2 := by positivity
    have hmul := mul_le_mul_right hb (ENNReal.ofReal ((w z) ^ 2))
    have hleft : ENNReal.ofReal ((w z) ^ 2) * (∑ m ∈ Finset.range (N + 1),
          ENNReal.ofReal (eNorm m * (cmode m F z) ^ 2))
        = ∑ m ∈ Finset.range (N + 1),
            ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by rw [← ENNReal.ofReal_mul hw])
    have hright : ENNReal.ofReal ((w z) ^ 2) *
          (∫⁻ θ in Iθ, ENNReal.ofReal ((F z θ) ^ 2 * Real.cos θ))
        = ∫⁻ θ in Iθ, ENNReal.ofReal ((w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ)) := by
      rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal ((w z) ^ 2))
        (fun θ => ENNReal.ofReal ((F z θ) ^ 2 * Real.cos θ)) ENNReal.ofReal_ne_top]
      exact MeasureTheory.lintegral_congr (fun θ => (ENNReal.ofReal_mul hw).symm)
    rw [hleft, hright] at hmul
    exact hmul
  -- integrate the pointwise-in-`z` inequality
  have h1 : (∫⁻ z in Set.Ioi (0 : ℝ), (∑ m ∈ Finset.range (N + 1),
        ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ), (∫⁻ θ in Iθ,
          ENNReal.ofReal ((w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ))) :=
    MeasureTheory.lintegral_mono hpt
  -- the summands are a.e. measurable, so the sum comes out of the `z`-integral
  have haem : ∀ m : ℕ, AEMeasurable
      (fun z : ℝ => ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun m => (aemeasurable_modeTerm hsm m).ennreal_ofReal
  have hsumsplit : (∫⁻ z in Set.Ioi (0 : ℝ), (∑ m ∈ Finset.range (N + 1),
        ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))))
      = ∑ m ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)) := by
    refine Finset.induction_on (Finset.range (N + 1)) ?_ ?_
    · simp
    · intro a s ha ih
      have hL : (∫⁻ z in Set.Ioi (0 : ℝ), (∑ m ∈ insert a s,
            ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))))
          = ∫⁻ z in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((w z) ^ 2 * (eNorm a * (cmode a F z) ^ 2))
              + ∑ m ∈ s, ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))) :=
        MeasureTheory.lintegral_congr (fun z => by
          show (∑ m ∈ insert a s, ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
            = ENNReal.ofReal ((w z) ^ 2 * (eNorm a * (cmode a F z) ^ 2))
              + ∑ m ∈ s, ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))
          rw [Finset.sum_insert ha])
      rw [hL, MeasureTheory.lintegral_add_left' (haem a), ih, Finset.sum_insert ha]
  -- the RHS: `∫⁻_θ ofReal (…)` is `ofReal` of the `θ`-integral
  have hconv : (∫⁻ z in Set.Ioi (0 : ℝ), (∫⁻ θ in Iθ,
        ENNReal.ofReal ((w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ))))
      = ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * Real.cos θ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have hInt : MeasureTheory.Integrable (fun θ => (w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ))
        (MeasureTheory.volume.restrict Iθ) :=
      (hint z hz).const_mul ((w z) ^ 2)
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => (w z) ^ 2 * ((F z θ) ^ 2 * Real.cos θ)) := by
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Iθ).mpr ?_
      refine Filter.Eventually.of_forall (fun θ hθ => ?_)
      have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
    congr 1
    exact MeasureTheory.integral_const_mul ((w z) ^ 2) (fun θ => (F z θ) ^ 2 * Real.cos θ)
  rw [hsumsplit, hconv] at h1
  exact h1

/-! ## The corollary: the Bessel sum is dominated by the source's `ℋ⁰`-norm -/

/-- **Bessel's inequality for the mode coefficients against `HkSq α 0`.**

  `∑_{m ≤ N} eNorm m · ∫_z (cmode m F z)² w(z)²  ≤  HkSq α 0 F`.

This is the source-side input of the level-`0` honest-modal estimate. -/
theorem sum_eNorm_cmode_sq_le_HkSq (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α 0 F)
    (hint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Iθ)
    (hintσ : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * sEta θ) Iθ) :
    (∑ m ∈ Finset.range (N + 1), eNorm m *
        ∫ z in Set.Ioi (0 : ℝ), (cmode m F z) ^ 2 * (w z) ^ 2) ≤ Work.Spaces.HkSq α 0 F := by
  -- the outer integrand of `HkSq` is integrable
  have hIntHk : MeasureTheory.Integrable
      (fun z => ∫ θ in Iθ, (F z θ) ^ 2 * (w z) ^ 2 * sEta θ)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine (hmem.2.mono_set (fun z hz => le_of_lt hz)).congr_fun ?_ measurableSet_Ioi
    intro z _
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
    rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq α (fun z θ => F z θ) z θ,
      Work.FTS.EllipticEst.Honest.sq_profile_eq (fun z θ => F z θ) z θ
        (Work.FTS.GalBasis.cc.sin_two_nonneg_of_mem_Iθ hθ)]
    rfl
  have hθeq : ∀ z : ℝ, (w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * sEta θ
      = ∫ θ in Iθ, (F z θ) ^ 2 * (w z) ^ 2 * sEta θ := by
    intro z
    have h1 : (∫ θ in Iθ, (F z θ) ^ 2 * (w z) ^ 2 * sEta θ)
        = ∫ θ in Iθ, (w z) ^ 2 * ((F z θ) ^ 2 * sEta θ) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [h1, MeasureTheory.integral_const_mul]
  have hHkSqLim : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Iθ,
        (F z θ) ^ 2 * (w z) ^ 2 * sEta θ) = Work.Spaces.HkSq α 0 F := by
    rw [Work.FTS.ClassC.HkSq_zero_eq_w α F]
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    exact (MeasureTheory.integral_Ici_eq_integral_Ioi (μ := MeasureTheory.volume)
      (x := (0 : ℝ))).symm
  have hB : (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * sEta θ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 0 F) := by
    have hpoint : (fun z : ℝ => ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ,
          (F z θ) ^ 2 * sEta θ))
        =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
          (fun z => ENNReal.ofReal (∫ θ in Iθ, (F z θ) ^ 2 * (w z) ^ 2 * sEta θ)) :=
      Filter.Eventually.of_forall (fun z => by
        show ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * sEta θ) = _
        rw [hθeq z])
    rw [MeasureTheory.lintegral_congr_ae hpoint]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntHk
      (Filter.Eventually.of_forall (fun z => by
        refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
        have hs := Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hs))]
    rw [hHkSqLim]
  -- Bessel, then the `cos ≤ σ` comparison
  have hbess := bessel_z F N hsm hint
  have hcmp : (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * Real.cos θ))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * ∫ θ in Iθ, (F z θ) ^ 2 * sEta θ) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ (w z) ^ 2)
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hintσ z hz) ?_
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Iθ).mpr ?_
      refine Filter.Eventually.of_forall (fun θ hθ => ?_)
      have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
      positivity
    · filter_upwards [ae_cos_le_sEta] with θ hθ
      exact mul_le_mul_of_nonneg_left hθ (sq_nonneg _)
  have hmain : (∑ m ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 0 F) :=
    le_trans (le_trans hbess hcmp) (le_of_eq hB)
  -- each summand is finite, and is `ofReal` of the corresponding real integral
  have hHkSq_nonneg : 0 ≤ Work.Spaces.HkSq α 0 F := by
    rw [Work.FTS.ClassC.HkSq_zero_eq_w α F]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z _ => ?_)
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    have hs := Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hs
  have hterm : ∀ m ∈ Finset.range (N + 1), eNorm m *
        ∫ z in Set.Ioi (0 : ℝ), (cmode m F z) ^ 2 * (w z) ^ 2
      = (∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))).toReal := by
    intro m _
    have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        (fun z : ℝ => (w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)) :=
      Filter.Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _)
        (mul_nonneg (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m)) (sq_nonneg _)))
    have haesm : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ => (w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (aemeasurable_modeTerm hsm m).aestronglyMeasurable
    have hconv := MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg haesm
    have hw2 : (∫ z in Set.Ioi (0 : ℝ), (w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))
        = eNorm m * ∫ z in Set.Ioi (0 : ℝ), (cmode m F z) ^ 2 * (w z) ^ 2 := by
      have h1 : (∫ z in Set.Ioi (0 : ℝ), (w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))
          = ∫ z in Set.Ioi (0 : ℝ), eNorm m * ((cmode m F z) ^ 2 * (w z) ^ 2) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)
      rw [h1, MeasureTheory.integral_const_mul]
    rw [hw2] at hconv
    exact hconv
  have hfin : ∀ m ∈ Finset.range (N + 1),
      (∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))) ≠ ⊤ := by
    intro m hm
    have hsingle : (∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2)))
        ≤ ∑ i ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
            ENNReal.ofReal ((w z) ^ 2 * (eNorm i * (cmode i F z) ^ 2)) :=
      Finset.single_le_sum (f := fun i => ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm i * (cmode i F z) ^ 2)))
        (fun i _ => zero_le) hm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans hsingle hmain)
  have hsum_eq : (∑ m ∈ Finset.range (N + 1), eNorm m *
        ∫ z in Set.Ioi (0 : ℝ), (cmode m F z) ^ 2 * (w z) ^ 2)
      = (∑ m ∈ Finset.range (N + 1), ∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((w z) ^ 2 * (eNorm m * (cmode m F z) ^ 2))).toReal := by
    rw [ENNReal.toReal_sum (fun m hm => hfin m hm)]
    exact Finset.sum_congr rfl (fun m hm => hterm m hm)
  rw [hsum_eq]
  exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain)
    (le_of_eq (ENNReal.toReal_ofReal hHkSq_nonneg))

end Work.FTS.ClassC
