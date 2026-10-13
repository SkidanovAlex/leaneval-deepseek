/-
# `ModalSolution/eFamParsevalAux`: the three structural lemmas behind `eFam_parseval`

This module packages, under `_aux` names, the three facts that turn the Hilbert-basis machinery
into Parseval's identity for the Gegenbauer modes (`eFamParsevalDefs.lean` carries the
definitions `eM`, `eFamD`, `eFamLp`, `eFamE` and the inner-product API):

* `inner_eFamLp_eFamLp` — the inner product of two mode classes;
* `eFamE_orthonormal_aux` — the normalised modes are orthonormal (from `eFam_orthogonal` and the
  norm value `eFam_norm_fts`);
* `eFamE_span_orthogonal_eq_bot_aux` — they are total in `L²(Iθ, cos θ dθ)`: the orthogonal
  complement of their span is `⊥`.  This is the `Lp` form of the completeness
  `Work.FTS.PhiStar.Gegenbauer.eFam_complete` (an `Lp` class is a.e. strongly measurable by
  construction, so the measurability pathology of `eFamBasisFts` cannot arise);
* `cmode_eq_setIntegral_aux` — `cmode`'s interval integral is the set integral over `Iθ`.

The proofs follow the already-proved siblings `LevelOneAsm/eigE_orthonormal.lean` and
`LevelOneAsm/eigE_span_orthogonal_eq_bot.lean` verbatim with the `eig*` family replaced by the
`eFam*` one (the `_aux` suffix keeps the names distinct from the same lemmas delivered
independently by colleagues in `eFamE_orthonormal.lean`,
`eFamE_span_orthogonal_eq_bot.lean`, `cmode_eq_setIntegral.lean`).
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.EllipticEst.ModalSolution.eFamParsevalDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution

local notation "Iθ" => Work.Spaces.Iθ
local notation "angMeasure" => Work.FTS.EllipticEst.LevelOneAsm.angMeasure

/-- The inner product of two mode classes is the weighted integral of the two modes. -/
theorem inner_eFamLp_eFamLp (n m : ℕ) :
    inner ℝ (eFamLp n) (eFamLp m) = ∫ θ in Iθ, eM n θ * eM m θ * Real.cos θ :=
  inner_toLp_eFamLp (eFam_memLp n) m

/-- The normalised modes form an orthonormal family of `L²(Iθ, cos θ dθ)`. -/
theorem eFamE_orthonormal_aux : Orthonormal ℝ eFamE := by
  rw [orthonormal_iff_ite]
  intro n m
  have hinner : inner ℝ (eFamE n) (eFamE m)
      = (Real.sqrt (eFamD n))⁻¹ * (Real.sqrt (eFamD m))⁻¹ *
        ∫ θ in Iθ, eM n θ * eM m θ * Real.cos θ := by
    rw [eFamE, eFamE, real_inner_smul_left, inner_smul_right, inner_eFamLp_eFamLp]
    ring
  rw [hinner]
  rcases eq_or_ne n m with hnm | hnm
  · subst hnm
    rw [ite_eq_left rfl]
    have hd := eFamD_pos n
    have hI : (∫ θ in Iθ, eM n θ * eM n θ * Real.cos θ) = eFamD n := by
      rw [eFamD]
      exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hI, ← mul_inv, ← sq, Real.sq_sqrt (le_of_lt hd), inv_mul_cancel₀ (ne_of_gt hd)]
  · rw [ite_eq_right hnm]
    have hzero : (∫ θ in Iθ, eM n θ * eM m θ * Real.cos θ) = 0 := by
      rw [integral_Iθ_eq_intervalIntegral]
      exact Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal n m hnm
    rw [hzero, mul_zero]

/-- **Totality of the modes**: the orthogonal complement of the span of `eFamE` is trivial.
This is `eFam_complete` transported to `Lp ℝ 2 angMeasure`. -/
theorem eFamE_span_orthogonal_eq_bot_aux :
    Submodule.orthogonal (Submodule.span ℝ (Set.range eFamE)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  -- `y` is orthogonal to every normalised mode
  have hmem : ∀ n : ℕ, inner ℝ (eFamE n) y = 0 := fun n =>
    (Submodule.mem_orthogonal _ y).mp hy (eFamE n) (Submodule.subset_span (Set.mem_range_self n))
  -- hence orthogonal to every raw mode class (the normalising scalar is nonzero)
  have hLp : ∀ n : ℕ, inner ℝ (eFamLp n) y = 0 := by
    intro n
    have h := hmem n
    simp only [eFamE, real_inner_smul_left] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (eFamD_pos n))))
    · exact h'
  -- the mode moments of the representative of `y` vanish, in the order used by `eFam_complete`
  have hint : ∀ n : ℕ,
      (∫ θ in Iθ, (y : ℝ → ℝ) θ * eM n θ * Real.cos θ) = 0 := by
    intro n
    rw [show (∫ θ in Iθ, (y : ℝ → ℝ) θ * eM n θ * Real.cos θ)
          = ∫ θ in Iθ, eM n θ * (y : ℝ → ℝ) θ * Real.cos θ from
        setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
    rw [← inner_eFamLp_any n y]
    exact hLp n
  -- a.e. strong measurability and square integrability for the unweighted measure
  have hy_aesm_L : AEStronglyMeasurable (y : ℝ → ℝ) (volume.restrict Iθ) :=
    AEStronglyMeasurable.mono_ac
      Work.FTS.EllipticEst.LevelOneAsm.restrict_absolutelyContinuous_angMeasure
      (MeasureTheory.Lp.memLp y).aestronglyMeasurable
  have hy_int_sq : Integrable (fun a => ((y : ℝ → ℝ) a) ^ 2) angMeasure :=
    (MeasureTheory.memLp_two_iff_integrable_sq
      (MeasureTheory.Lp.memLp y).aestronglyMeasurable).mp (MeasureTheory.Lp.memLp y)
  have hy_int : IntegrableOn (fun θ => ((y : ℝ → ℝ) θ) ^ 2 * Real.cos θ) Iθ := by
    show Integrable (fun θ => ((y : ℝ → ℝ) θ) ^ 2 * Real.cos θ) (volume.restrict Iθ)
    have h := (MeasureTheory.integrable_withDensity_iff_integrable_smul'
      (μ := volume.restrict Iθ)
      (f := fun θ => ENNReal.ofReal (Real.cos θ))
      (Real.measurable_cos.ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))
      (g := fun a => ((y : ℝ → ℝ) a) ^ 2)).mp hy_int_sq
    refine h.congr ?_
    filter_upwards [ae_restrict_mem (s := Iθ) measurableSet_Icc] with θ hθ
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (Work.FTS.EllipticEst.LevelOneAsm.cos_nonneg_of_mem_Iθ hθ)]
    ring
  -- completeness of the mode system
  have hae := Work.FTS.PhiStar.Gegenbauer.eFam_complete (y : ℝ → ℝ) hy_aesm_L hy_int
    (fun m => hint m)
  have hae2 : (y : ℝ → ℝ) =ᵐ[angMeasure] 0 :=
    Work.FTS.EllipticEst.LevelOneAsm.angMeasure_absolutelyContinuous.ae_eq hae
  exact (MeasureTheory.Lp.eq_zero_iff_ae_eq_zero).mpr hae2

/-- `cmode` (interval integrals on `(0, π/2)`) in terms of the set integral over `Iθ` and the
norm `eFamD` used by the `L²` inner products. -/
theorem cmode_eq_setIntegral_aux (F : ℝ → ℝ → ℝ) (z : ℝ) (m : ℕ) :
    Work.FTS.PhiStar.Series.cmode m F z
      = (∫ θ in Iθ, F z θ * eM m θ * Real.cos θ) / eFamD m := by
  show (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      / (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
    = (∫ θ in Iθ, F z θ * eM m θ * Real.cos θ) / eFamD m
  have h1 : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = ∫ θ in Iθ, F z θ * eM m θ * Real.cos θ := by
    rw [← integral_Iθ_eq_intervalIntegral
      (f := fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)]
    try exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by simp only [eM])
  have h2 : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) = eFamD m := by
    rw [← integral_Iθ_eq_intervalIntegral
      (f := fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)]
    try rw [eFamD]
    try exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => by simp only [eM])
  rw [h1, h2]

end Work.EllipticEst.ModalSolution
