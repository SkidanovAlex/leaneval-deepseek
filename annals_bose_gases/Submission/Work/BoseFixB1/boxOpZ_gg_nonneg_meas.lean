import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.BoxOpGDefs
import Submission.Work.BoseFixB1.BoxTauGenMeasToolbox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.boxOpZ_gg_nonneg_meas`

Positivity of the diagonal quadratic form of the box one-slot operator `boxOpZ A g g` for slot
weights `g` that are only **measurable, bounded, and supported in `A ⊆ acube a`** (no continuity):

`0 ≤ ∫_{x ∈ abox (N+1) a} Ψ x · boxOpZ A g g Ψ x`,   `Ψ` continuous.

This is the "measured" analogue of `Work.BoseFixB1.boxOpG_gg_nonneg` /
`Work.BoseFixB1.boxOpZ_slot_sq`, which are stated for *continuous* `g` with `tsupport g ⊆ A`.
The proof is the same: summing the one-slot decomposition of `boxOpZ A g g` inside the box
integral splits the pairing into `N+1` slot contributions (`boxOpZ_sum_expand_meas`), and each
slot contribution is the integral of a **square** (`boxOpZ_slot_sq_meas`):

`∫_{abox (N+1) a} Ψ x · g(x i) · ∫_{z∈A} g z Ψ(x_{i←z}) dz
   = ∫_{r ∈ abox N a} (∫_{z∈A} g z Ψ(kcInsN N i (z,r)) dz)²`.

The only place where the continuity of `g` was used in the continuous statement is the
integrability of the peeled integrand; here it is replaced by measurability + boundedness of `g`
on the finite-measure set `A` (`Work.BoseFixB1S.integrableOn_mul_of_bound`,
`Work.BoseFixB1.abs_fibreMean_mul_le`).  The indicator collapse `1_A · g = g` uses only the
support condition `g = 0` off `A`.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- A continuous function is bounded in absolute value on the box. -/
theorem exists_abs_bound_of_continuousOn_abox {M : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Ψ : Submission.BoseGases.X M → ℝ} (hΨ : Continuous Ψ) :
    ∃ B : ℝ, ∀ x ∈ Submission.BoseGases.abox M ℓ, |Ψ x| ≤ B := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact M hℓ).exists_bound_of_continuousOn
    hΨ.continuousOn
  refine ⟨|C|, fun x hx => ?_⟩
  have h : ‖Ψ x‖ ≤ |C| := le_trans (hC x hx) (le_abs_self C)
  simpa only [Real.norm_eq_abs] using h

/-- **Integrability of the per-slot integrand** (measured version).  For `x` in the box the
slot-`i` integrand `Ψ x · g(x i) · ∫_{z∈A} g z Ψ(x_{i←z}) dz` is bounded on the compact box
(the fibre integral is bounded by `max Cg 0 · max B 0 · vol A`), hence integrable. -/
theorem integrableOn_boxOpZslot_meas {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgm : Measurable g)
    {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) (i : Fin (N + 1)) :
    IntegrableOn
      (fun x : Submission.BoseGases.X (N + 1) =>
        Ψ x * (g (x i) * ∫ z in A, g z * Ψ (Function.update x i z)))
      (Submission.BoseGases.abox (N + 1) a) volume := by
  obtain ⟨B, hB⟩ := exists_abs_bound_of_continuousOn_abox (M := N + 1) ha hΨ
  have hfibm : Measurable
      (fun x : Submission.BoseGases.X (N + 1) =>
        ∫ z in A, g z * Ψ (Function.update x i z)) :=
    measurable_fibreMean_mul hAm i hgm hΨ.measurable
  have hgm' : Measurable
      (fun x : Submission.BoseGases.X (N + 1) =>
        g (x i) * ∫ z in A, g z * Ψ (Function.update x i z)) :=
    (hgm.comp (measurable_pi_apply i)).mul hfibm
  refine Work.BoseFixB1S.integrableOn_mul_of_bound (N := N + 1) (ℓ := a) ha
    hΨ.measurable hgm' (Cf := B)
    (Cg := max Cg 0 * (max Cg 0 * max B 0 * (volume A).toReal)) hB ?_
  intro x hx
  rw [abs_mul]
  exact mul_le_mul (le_trans (hgC (x i)) (le_max_left Cg 0))
    (abs_fibreMean_mul_le ha hAc hgC hB hx i) (abs_nonneg _) (le_max_right Cg 0)

/-- **The `Σ`/`∫` exchange** (measured version): summing the one-slot decomposition of
`boxOpZ A g g` inside the box integral splits the pairing into the `N+1` slot contributions. -/
theorem boxOpZ_sum_expand_meas {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgm : Measurable g) (hg0 : ∀ z, z ∉ A → g z = 0)
    {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) :
    ∫ x in Submission.BoseGases.abox (N + 1) a, Ψ x * Work.BoseFixB1.boxOpZ A g g Ψ x
      = ∑ i : Fin (N + 1), ∫ x in Submission.BoseGases.abox (N + 1) a,
          Ψ x * (g (x i) * ∫ z in A, g z * Ψ (Function.update x i z)) := by
  have hint : ∀ i : Fin (N + 1), IntegrableOn
      (fun x : Submission.BoseGases.X (N + 1) =>
        Ψ x * (g (x i) * ∫ z in A, g z * Ψ (Function.update x i z)))
      (Submission.BoseGases.abox (N + 1) a) volume :=
    fun i => integrableOn_boxOpZslot_meas ha hAm hAc hgm hgC hΨ i
  simp only [Work.BoseFixB1.boxOpZ, Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum]
  intro i _
  exact (hint i).integrable

/-- **The diagonal slot contribution** (measured version).  For `g` measurable, bounded and
vanishing off `A ⊆ acube a`, the `i`-th summand of `boxOpZ A g g` paired against `Ψ` on the box
equals the integral over the peeled box of the square of the `A`-fibre. -/
theorem boxOpZ_slot_sq_meas {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgm : Measurable g) (hg0 : ∀ z, z ∉ A → g z = 0)
    {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) (i : Fin (N + 1)) :
    ∫ x in Submission.BoseGases.abox (N + 1) a,
        Ψ x * (g (x i) * ∫ z in A, g z * Ψ (Function.update x i z))
      = ∫ r in Submission.BoseGases.abox N a,
          (∫ z in A, g z * Ψ (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 := by
  -- the pointwise indicator identity `1_A · g = g`
  have hind : ∀ y : EuclideanSpace ℝ (Fin 3),
      A.indicator (fun _ => (1 : ℝ)) y * g y = g y := by
    intro y
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, one_mul]
    · rw [Set.indicator_of_notMem hy, zero_mul, hg0 y hy]
  set F : Submission.BoseGases.X (N + 1) → ℝ :=
    (fun x => Ψ x * (g (x i) * ∫ z in A, g z * Ψ (Function.update x i z))) with hFdef
  have hFint : IntegrableOn F (Submission.BoseGases.abox (N + 1) a) volume :=
    integrableOn_boxOpZslot_meas ha hAm hAc hgm hgC hΨ i
  -- peel the slot `i`: `abox (N+1) a ≃ acube a × abox N a`
  rw [Submission.BoseGases.abox_integral_peel (n := N) (ℓ := a) i F hFint]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun r => ?_))
  have hval : ∀ y : EuclideanSpace ℝ (Fin 3),
      F (Submission.BoseGases.kcInsN N i (y, r))
        = Ψ (Submission.BoseGases.kcInsN N i (y, r)) * g y
            * (∫ z in A, g z * Ψ (Submission.BoseGases.kcInsN N i (z, r))) := by
    intro y
    rw [hFdef]
    simp only [Submission.BoseGases.kc_insN_apply_same, Submission.BoseGases.update_kcInsN]
    ring
  -- the `y`-integral of the creation weight times `Ψ` is the fibre itself
  have hfib : (∫ y in Submission.BoseGases.acube a,
        Ψ (Submission.BoseGases.kcInsN N i (y, r)) * g y)
      = ∫ z in A, g z * Ψ (Submission.BoseGases.kcInsN N i (z, r)) := by
    have hEq : (fun t : EuclideanSpace ℝ (Fin 3) =>
          A.indicator (fun _ => (1 : ℝ)) t
            * (g t * Ψ (Submission.BoseGases.kcInsN N i (t, r))))
        = fun t : EuclideanSpace ℝ (Fin 3) =>
            Ψ (Submission.BoseGases.kcInsN N i (t, r)) * g t := by
      funext t
      rw [← mul_assoc, hind t]
      ring
    rw [← hEq, Work.BoseFixB1S.setIntegral_indicator_one_mul hAm hAc
      (fun t => g t * Ψ (Submission.BoseGases.kcInsN N i (t, r)))]
  calc ∫ y in Submission.BoseGases.acube a, F (Submission.BoseGases.kcInsN N i (y, r))
      = ∫ y in Submission.BoseGases.acube a,
          Ψ (Submission.BoseGases.kcInsN N i (y, r)) * g y
            * (∫ z in A, g z * Ψ (Submission.BoseGases.kcInsN N i (z, r))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        exact hval y
    _ = (∫ y in Submission.BoseGases.acube a,
            Ψ (Submission.BoseGases.kcInsN N i (y, r)) * g y)
          * (∫ z in A, g z * Ψ (Submission.BoseGases.kcInsN N i (z, r))) := by
        rw [MeasureTheory.integral_mul_const]
    _ = (∫ z in A, g z * Ψ (Submission.BoseGases.kcInsN N i (z, r)))
          * (∫ z in A, g z * Ψ (Submission.BoseGases.kcInsN N i (z, r))) := by
        rw [hfib]
    _ = (∫ z in A, g z * Ψ (Submission.BoseGases.kcInsN N i (z, r))) ^ 2 := by ring

theorem boxOpZ_gg_nonneg_meas {N : ℕ} {a : ℝ} (ha : 0 < a)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hAm : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube a)
    {g : EuclideanSpace ℝ (Fin 3) → ℝ} (hgm : Measurable g) (hg0 : ∀ z, z ∉ A → g z = 0)
    {Cg : ℝ} (hgC : ∀ z, |g z| ≤ Cg)
    {Ψ : Submission.BoseGases.X (N + 1) → ℝ} (hΨ : Continuous Ψ) :
    0 ≤ ∫ x in Submission.BoseGases.abox (N + 1) a, Ψ x * Work.BoseFixB1.boxOpZ A g g Ψ x := by
  rw [boxOpZ_sum_expand_meas ha hAm hAc hgm hg0 hgC hΨ]
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [boxOpZ_slot_sq_meas ha hAm hAc hgm hg0 hgC hΨ i]
  exact MeasureTheory.integral_nonneg
    (f := fun r : Submission.BoseGases.X N =>
      (∫ z in A, g z * Ψ (Submission.BoseGases.kcInsN N i (z, r))) ^ 2)
    (fun r => sq_nonneg _)

end Work.BoseFixB1
