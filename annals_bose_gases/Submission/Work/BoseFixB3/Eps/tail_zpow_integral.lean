import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.RadialIntegral
import Submission.Work.BoseFixB3.Eps.Ioi_tail_zpow
import Submission.Work.BoseFixB3.Eps.exterior_norm_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Eps.tail_zpow_integral`

The tail integral of `‖p‖^{-N}` over the exterior of a ball of radius `κ` in `ℝ³`:

    `∫_{κ ≤ ‖p‖} ‖p‖^{-N} dp ≤ C κ^{3-N}    (N ≥ 4, κ > 0)`,

with `C = 4π/(N-3)`.  The exact value is `4π κ^{3-N}/(N-3)`: in polar coordinates the
volume element is `4π r² dr` and the radial integral is `∫_κ^∞ r^{2-N} dr = κ^{3-N}/(N-3)`.

The proof is assembled from three pieces:

* `Work.BoseFixB3.Eps.exterior_inv_nat_eq` (this file): the polar-coordinate reduction
  `∫_{κ ≤ ‖p‖} ‖p‖^{-N} dp = 4π ∫_κ^∞ r² r^{-N} dr`, using the radial-integration identity
  `Submission.BoseGases.integral_fun_norm_r3`;
* `Work.BoseFixB3.Eps.Ioi_tail_zpow` (delegated): the exact value of the one-dimensional
  tail integral `∫_κ^∞ r² (r^N)⁻¹ dr = κ^{3-N}/(N-3)`;
* `Work.BoseFixB3.Eps.exterior_norm_integrable` (delegated): the integrability
  equivalence transporting `IntegrableOn` across the polar decomposition.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseFixB3.Eps

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Polar reduction of the exterior integral.**  For `κ > 0`,

    `∫_{κ ≤ ‖p‖} ‖p‖^{-N} dp = 4π ∫_κ^∞ r² r^{-N} dr`.

The set integral is written as the full-space integral of the radial indicator
`(Ici κ).indicator (· ^ N)⁻¹`, and the radius integral is identified with the one over
`(κ,∞)` (the sets `Ioi 0 ∩ Ici κ` and `Ici κ` coincide, and `Ici κ = Ioi κ` modulo the
null point `κ`). -/
lemma exterior_inv_nat_eq (N : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    (∫ p in {q : ℝ³ | κ ≤ ‖q‖}, (‖p‖ ^ N)⁻¹)
      = 4 * Real.pi * (∫ r in Set.Ioi κ, r ^ 2 * (r ^ N)⁻¹) := by
  let g : ℝ → ℝ := (Set.Ici κ).indicator (fun r : ℝ => (r ^ N)⁻¹)
  have hmeas : MeasurableSet {q : ℝ³ | κ ≤ ‖q‖} :=
    measurableSet_le measurable_const measurable_norm
  have hpoint : (fun p : ℝ³ => g ‖p‖) =
      ({q : ℝ³ | κ ≤ ‖q‖}).indicator (fun p : ℝ³ => (‖p‖ ^ N)⁻¹) := by
    funext p
    by_cases hp : κ ≤ ‖p‖
    · simp [g, hp]
    · simp [g, hp]
  have hfull : (∫ p : ℝ³, g ‖p‖) = (∫ p in {q : ℝ³ | κ ≤ ‖q‖}, (‖p‖ ^ N)⁻¹) := by
    calc
      (∫ p : ℝ³, g ‖p‖)
          = ∫ p : ℝ³, ({q : ℝ³ | κ ≤ ‖q‖}).indicator
              (fun p : ℝ³ => (‖p‖ ^ N)⁻¹) p := by rw [hpoint]
      _ = ∫ p in {q : ℝ³ | κ ≤ ‖q‖}, (‖p‖ ^ N)⁻¹ := integral_indicator hmeas
  have h_inter : Set.Ioi (0 : ℝ) ∩ Set.Ici κ = Set.Ici κ := by
    ext r
    exact ⟨fun hr => hr.2, fun hr => ⟨lt_of_lt_of_le hκ hr, hr⟩⟩
  have hJ : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
      = ∫ r in Set.Ioi κ, r ^ 2 * (r ^ N)⁻¹ := by
    have hind : (fun r : ℝ => r ^ 2 * g r) =
        (Set.Ici κ).indicator (fun r : ℝ => r ^ 2 * (r ^ N)⁻¹) := by
      funext r
      by_cases hr : κ ≤ r
      · simp [g, hr]
      · simp [g, hr]
    calc
      (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
          = ∫ r in Set.Ioi (0 : ℝ),
              (Set.Ici κ).indicator (fun r : ℝ => r ^ 2 * (r ^ N)⁻¹) r := by rw [hind]
      _ = ∫ r in Set.Ioi (0 : ℝ) ∩ Set.Ici κ, r ^ 2 * (r ^ N)⁻¹ := by
            rw [setIntegral_indicator (s := Set.Ioi (0 : ℝ)) (t := Set.Ici κ)
              (f := fun r : ℝ => r ^ 2 * (r ^ N)⁻¹)
              (by measurability : MeasurableSet (Set.Ici κ))]
      _ = ∫ r in Set.Ici κ, r ^ 2 * (r ^ N)⁻¹ := by rw [h_inter]
      _ = ∫ r in Set.Ioi κ, r ^ 2 * (r ^ N)⁻¹ := by
            rw [integral_Ici_eq_integral_Ioi (f := fun r : ℝ => r ^ 2 * (r ^ N)⁻¹)]
  calc
    (∫ p in {q : ℝ³ | κ ≤ ‖q‖}, (‖p‖ ^ N)⁻¹) = ∫ p : ℝ³, g ‖p‖ := hfull.symm
    _ = 4 * Real.pi * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) :=
          Submission.BoseGases.integral_fun_norm_r3 (g := g)
    _ = 4 * Real.pi * (∫ r in Set.Ioi κ, r ^ 2 * (r ^ N)⁻¹) := by rw [hJ]

theorem tail_zpow_integral (N : ℕ) (hN : 4 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ κ : ℝ, 0 < κ →
      MeasureTheory.IntegrableOn (fun p : EuclideanSpace ℝ (Fin 3) => ((‖p‖) ^ N)⁻¹)
        {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖} MeasureTheory.volume ∧
      (∫ p in {q : EuclideanSpace ℝ (Fin 3) | κ ≤ ‖q‖}, ((‖p‖) ^ N)⁻¹)
        ≤ C * κ ^ (3 - (N : ℤ)) := by
  have hNr4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN3 : (3 : ℝ) < (N : ℝ) := by linarith
  refine ⟨4 * Real.pi / ((N : ℝ) - 3), ?_, ?_⟩
  · apply div_nonneg (by positivity) (by linarith)
  · intro κ hκ
    -- integrability: transport the radial integrability through the polar decomposition
    have hint : IntegrableOn (fun p : ℝ³ => (‖p‖ ^ N)⁻¹) {q : ℝ³ | κ ≤ ‖q‖} := by
      refine (exterior_norm_integrable (N := N) hκ).mpr ?_
      have hconv : IntegrableOn (fun r : ℝ => r ^ ((2 : ℝ) - N)) (Set.Ioi κ) :=
        integrableOn_Ioi_rpow_of_lt (by linarith : (2 : ℝ) - N < -1) hκ
      refine hconv.congr_fun (fun r hr => ?_) measurableSet_Ioi
      exact (sq_mul_pow_inv_eq_rpow N (lt_trans hκ hr)).symm
    refine ⟨hint, ?_⟩
    -- value of the integral: polar reduction, then the one-dimensional tail integral
    rw [exterior_inv_nat_eq N hκ, Ioi_tail_zpow N hN hκ]
    set A : ℝ := κ ^ (3 - (N : ℤ)) with hA
    exact le_of_eq (by ring)

end Work.BoseFixB3.Eps
