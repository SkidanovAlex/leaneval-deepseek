import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SlotProjAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-! ## Auxiliary lemmas

Three elementary inputs to `slotInt_measurable_bounded`:

* `continuous_prod_PV_pair` — the product of the kernels over the slots of `U`, as a function of
  the *pair* (configuration, fibre variable), is continuous (each slot contributes a `PV`-kernel,
  which is continuous in its two arguments by `continuous_PV_uncurry`);
* `measurable_updateFinset_pair` — `(x, z) ↦ Function.updateFinset x U z` is measurable
  (coordinatewise: the coordinate `j` is either the fibre variable `z ⟨j, ·⟩` or `x j`);
* `exists_integral_norm_PV_bound` — the one-slot norm integrals `a ↦ ∫ t, ‖PV e a t‖` are
  uniformly bounded, since
  `‖PV e a t‖ ≤ Σ l, ‖e l a‖ ‖e l t‖ ≤ Σ l, M l ‖e l t‖` with `M l = sup ‖e l‖ < ∞`
  (continuity + compact support) and each `t ↦ M l ‖e l t‖` is integrable. -/

/-- The product of the projection kernels over the slots of `U` is continuous as a function of the
configuration and of the fibre variables jointly. -/
theorem continuous_prod_PV_pair {m : ℕ} (e : Fin m → Ω → ℂ) (he : ∀ l, Continuous (e l))
    {ι : Type*} (U : Finset ι) :
    Continuous (fun p : (ι → Ω) × (↑U → Ω) => ∏ i : ↑U, PV e (p.1 i.1) (p.2 i)) := by
  refine continuous_finsetProd _ (fun i _ => ?_)
  have h1 : Continuous (fun p : (ι → Ω) × (↑U → Ω) => p.1 i.1) :=
    (continuous_apply i.1).comp continuous_fst
  have h2 : Continuous (fun p : (ι → Ω) × (↑U → Ω) => p.2 i) :=
    (continuous_apply i).comp continuous_snd
  exact (continuous_PV_uncurry e he).comp (Continuous.prodMk h1 h2)

/-- Replacing the slots of `U` by the fibre variables is a measurable operation, jointly in the
configuration and in the fibre variables. -/
theorem measurable_updateFinset_pair {ι : Type*} [DecidableEq ι] (U : Finset ι) :
    Measurable (fun p : (ι → Ω) × (↑U → Ω) => Function.updateFinset p.1 U p.2) := by
  refine Measurable.of_eval (fun j => ?_)
  simp only [Function.updateFinset_def]
  split_ifs with hj
  · exact (measurable_pi_apply (⟨j, hj⟩ : ↑U)).comp measurable_snd
  · exact (measurable_pi_apply j).comp measurable_fst

/-- The one-slot norm integrals `a ↦ ∫ t, ‖PV e a t‖` are uniformly bounded, because the kernel is
dominated by the (integrable) combination `Σ l, M l ‖e l t‖` of the modes. -/
theorem exists_integral_norm_PV_bound {m : ℕ} (e : Fin m → Ω → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l)) :
    ∃ C₁, ∀ a : Ω, ∫ t : Ω, ‖PV e a t‖ ≤ C₁ := by
  classical
  have hbd : ∀ l : Fin m, ∃ M : ℝ, ∀ a : Ω, ‖e l a‖ ≤ M :=
    fun l => (he l).bounded_above_of_compact_support (hec l)
  set M : Fin m → ℝ := fun l => max (Classical.choose (hbd l)) 0
  have hM : ∀ l a, ‖e l a‖ ≤ M l := fun l a =>
    le_trans (Classical.choose_spec (hbd l) a) (le_max_left _ _)
  refine ⟨∑ l : Fin m, M l * ∫ t : Ω, ‖e l t‖, fun a => ?_⟩
  have hInt : ∀ l : Fin m, Integrable (fun t : Ω => M l * ‖e l t‖) := fun l =>
    (((he l).integrable_of_hasCompactSupport (hec l)).norm).const_mul _
  have hgint : Integrable (fun t : Ω => ∑ l : Fin m, M l * ‖e l t‖) :=
    integrable_finsetSum _ (fun l _ => hInt l)
  have hpt : ∀ t : Ω, ‖PV e a t‖ ≤ ∑ l : Fin m, M l * ‖e l t‖ := by
    intro t
    calc ‖PV e a t‖ = ‖∑ l : Fin m, e l a * star (e l t)‖ := rfl
      _ ≤ ∑ l : Fin m, ‖e l a * star (e l t)‖ := norm_sum_le _ _
      _ = ∑ l : Fin m, ‖e l a‖ * ‖e l t‖ := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [norm_mul, norm_star]
      _ ≤ ∑ l : Fin m, M l * ‖e l t‖ :=
            Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hM l a) (norm_nonneg _)
  calc ∫ t : Ω, ‖PV e a t‖
      ≤ ∫ t : Ω, ∑ l : Fin m, M l * ‖e l t‖ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _) hgint
          (Filter.Eventually.of_forall hpt)
    _ = ∑ l : Fin m, ∫ t : Ω, M l * ‖e l t‖ := integral_finsetSum _ (fun l _ => hInt l)
    _ = ∑ l : Fin m, M l * ∫ t : Ω, ‖e l t‖ :=
        Finset.sum_congr rfl fun l _ => integral_const_mul _ _

-- namespace `Work.BoseBoxFock`; imports `Submission.Work.BoseBoxFock.SlotProjAux`.
/-- The slot projection preserves measurability and boundedness.  With `Ω = EuclideanSpace ℝ (Fin 3)`
and `slotInt e U Φ x = ∫ z : (↑U → Ω), (∏ i : ↑U, PV e (x i.1) (z i)) * Φ (updateFinset x U z)`, if
`Φ` is measurable and bounded then so is `slotInt e U Φ`.  (The index type is finite so that the
product σ-algebra on `ι → Ω` is the Borel σ-algebra.)

Measurability: the integrand `(x,z) ↦ (∏ i, PV e (x i.1) (z i)) * Φ (updateFinset x U z)` is jointly
measurable (the kernel is continuous, `updateFinset` is measurable by `measurable_pi_iff`), so
`MeasureTheory.StronglyMeasurable.integral_prod_right` gives measurability of `x ↦ ∫ z, ...`.

Boundedness: if `‖Φ‖ ≤ CΦ` then
`‖slotInt e U Φ x‖ ≤ ∫ z, CΦ * ∏ i, ‖PV e (x i.1) (z i)‖`
(`MeasureTheory.norm_integral_le_of_norm_le` with the continuous compactly supported dominator
`z ↦ CΦ * ∏ i, ‖PV e (x i.1) (z i)‖`), and by `MeasureTheory.integral_fintype_prod_eq_prod` this is
`CΦ * ∏ i : ↑U, ∫ t, ‖PV e (x i.1) t‖`, which is `≤ CΦ * C₁ ^ U.card` for a constant `C₁` with
`∀ a, ∫ t, ‖PV e a t‖ ≤ C₁` (such a `C₁` exists since `‖PV e a t‖ ≤ Σ l, M l * ‖e l t‖` with
`M l = sup ‖e l‖ < ∞`). -/
theorem slotInt_measurable_bounded {m : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Finset ι)
    (Φ : (ι → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) :
    Measurable (slotInt e U Φ) ∧ ∃ C, ∀ x : ι → EuclideanSpace ℝ (Fin 3), ‖slotInt e U Φ x‖ ≤ C := by
  classical
  -- the integrand is jointly measurable
  have hjoint : Measurable (fun p : (ι → Ω) × (↑U → Ω) =>
      (∏ i : ↑U, PV e (p.1 i.1) (p.2 i)) * Φ (Function.updateFinset p.1 U p.2)) :=
    (continuous_prod_PV_pair e he U).measurable.mul
      (hΦm.comp (measurable_updateFinset_pair U))
  refine ⟨?_, ?_⟩
  · -- measurability of the fibre integral
    have hsm : StronglyMeasurable (fun x : ι → Ω => ∫ z : ↑U → Ω,
        (∏ i : ↑U, PV e (x i.1) (z i)) * Φ (Function.updateFinset x U z)) :=
      hjoint.stronglyMeasurable.integral_prod_right'
    exact hsm.measurable
  · obtain ⟨CΦ, hCΦ⟩ := hΦb
    obtain ⟨C₁, hC₁⟩ := exists_integral_norm_PV_bound e he hec
    refine ⟨(max C₁ 0) ^ U.card * max CΦ 0, fun x => ?_⟩
    set F : (↑U → Ω) → ℂ := fun z =>
      (∏ i : ↑U, PV e (x i.1) (z i)) * Φ (Function.updateFinset x U z) with hF
    have hkcont : Continuous (fun z : ↑U → Ω => ∏ i : ↑U, PV e (x i.1) (z i)) :=
      continuous_finsetProd _ (fun i _ => (continuous_PV_snd e he (x i.1)).comp (continuous_apply i))
    have hkcs : HasCompactSupport (fun z : ↑U → Ω => ∏ i : ↑U, PV e (x i.1) (z i)) :=
      hasCompactSupport_prod_PV e hec U x
    have hkint : Integrable (fun z : ↑U → Ω => ∏ i : ↑U, ‖PV e (x i.1) (z i)‖) volume :=
      (hkcont.norm.integrable_of_hasCompactSupport hkcs.norm).congr
        (Filter.Eventually.of_forall fun z => norm_prod Finset.univ _)
    have hC_eq : (∫ z : ↑U → Ω, ‖F z‖) = ∫ z : ↑U → Ω, (∏ i : ↑U, ‖PV e (x i.1) (z i)‖) *
        ‖Φ (Function.updateFinset x U z)‖ :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by
        simp only [hF, norm_mul, norm_prod])
    have hD : (∫ z : ↑U → Ω, (∏ i : ↑U, ‖PV e (x i.1) (z i)‖) *
          ‖Φ (Function.updateFinset x U z)‖)
        ≤ ∫ z : ↑U → Ω, (∏ i : ↑U, ‖PV e (x i.1) (z i)‖) * max CΦ 0 := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => ?_)
        (hkint.mul_const _) (Filter.Eventually.of_forall fun z => ?_)
      · exact mul_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_left ((hCΦ _).trans (le_max_left CΦ 0))
          (Finset.prod_nonneg fun i _ => norm_nonneg _)
    have hFub : (∫ z : ↑U → Ω, ∏ i : ↑U, ‖PV e (x i.1) (z i)‖)
        = ∏ i : ↑U, ∫ t : Ω, ‖PV e (x i.1) t‖ :=
      integral_fintype_prod_volume_eq_prod (E := fun _ : ↑U => Ω)
        (f := fun i : ↑U => fun t : Ω => ‖PV e (x i.1) t‖)
    have hprod : (∏ i : ↑U, ∫ t : Ω, ‖PV e (x i.1) t‖) ≤ (max C₁ 0) ^ U.card := by
      have h := Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun i : ↑U => ∫ t : Ω, ‖PV e (x i.1) t‖) (g := fun _ : ↑U => max C₁ 0)
        (fun i _ => integral_nonneg fun t => norm_nonneg _)
        (fun i _ => (hC₁ (x i.1)).trans (le_max_left C₁ 0))
      rw [Finset.prod_const] at h
      rwa [Finset.card_univ, Fintype.card_coe] at h
    calc ‖slotInt e U Φ x‖ = ‖∫ z : ↑U → Ω, F z‖ := by simp only [slotInt, hF]
      _ ≤ ∫ z : ↑U → Ω, ‖F z‖ := norm_integral_le_integral_norm F
      _ = ∫ z : ↑U → Ω, (∏ i : ↑U, ‖PV e (x i.1) (z i)‖) *
            ‖Φ (Function.updateFinset x U z)‖ := hC_eq
      _ ≤ ∫ z : ↑U → Ω, (∏ i : ↑U, ‖PV e (x i.1) (z i)‖) * max CΦ 0 := hD
      _ = (∫ z : ↑U → Ω, ∏ i : ↑U, ‖PV e (x i.1) (z i)‖) * max CΦ 0 := integral_mul_const _ _
      _ = (∏ i : ↑U, ∫ t : Ω, ‖PV e (x i.1) t‖) * max CΦ 0 := by rw [hFub]
      _ ≤ (max C₁ 0) ^ U.card * max CΦ 0 :=
          mul_le_mul_of_nonneg_right hprod (le_max_right CΦ 0)

end Work.BoseBoxFock
