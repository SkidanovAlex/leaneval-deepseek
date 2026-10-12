import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Ring.Star
import Submission.RadialIntegral
import Submission.Work.BoseFixB3.Eps.Ioi_tail_zpow
import Submission.Work.BoseFixB3.Eps.exterior_norm_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.euclTailInvPow`

The exact value (and integrability) of the tails `‖t‖^{-4}` and `‖t‖^{-6}` on `ℝ³`:

    ∫_{T < ‖t‖} ‖t‖^{-4} dt = 4π / T ,      ∫_{T < ‖t‖} ‖t‖^{-6} dt = 4π / (3 T³)      (T > 0).

In polar coordinates on `ℝ³` the volume element is `4π r² dr`, so for `N ≥ 4`

    ∫_{T < ‖t‖} ‖t‖^{-N} dt = 4π ∫_T^∞ r^{2-N} dr = 4π T^{3-N} / (N-3),

which specialises to the two claims (`N = 4`: `T^{-1} = 1/T`; `N = 6`: `T^{-3} = 1/T³`).

The proof is assembled from three corpus pieces:

* `Work.BoseBogFS.exterior_inv_pow_eq` (this file): the polar-coordinate reduction of the
  strict exterior integral `∫_{T < ‖p‖}` to the half-line integral `∫_T^∞`, using the
  unconditional radial-integration identity `Submission.BoseGases.integral_fun_norm_r3`;
* `Work.BoseBogFS.exterior_inv_pow_integrable` (this file): integrability, transported
  through the polar decomposition `Work.BoseFixB3.Eps.exterior_norm_integrable` and the
  `L¹`-criterion `integrableOn_Ioi_rpow_of_lt`;
* `Work.BoseFixB3.Eps.Ioi_tail_zpow`: the exact one-dimensional tail value.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology

namespace Work.BoseBogFS

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Polar-coordinate reduction of the strict exterior integral.**  For `T > 0` and any
`N : ℕ`,

    `∫_{T < ‖p‖} ‖p‖^{-N} dp = 4π ∫_T^∞ r² (r^N)⁻¹ dr`.

The exterior integral is written as the full-space integral of the radial function
`(Ioi T).indicator (· ^ N)⁻¹`, and then the radius integral is pushed to `(T,∞)`
(the sets `Ioi 0 ∩ Ioi T` and `Ioi T` coincide because `T > 0`). -/
lemma exterior_inv_pow_eq (N : ℕ) {T : ℝ} (hT : 0 < T) :
    (∫ p in {q : ℝ³ | T < ‖q‖}, ((‖p‖ : ℝ) ^ N)⁻¹)
      = 4 * Real.pi * (∫ r in Set.Ioi T, r ^ 2 * (r ^ N)⁻¹) := by
  let g : ℝ → ℝ := (Set.Ioi T).indicator (fun r : ℝ => (r ^ N)⁻¹)
  have hmeas : MeasurableSet {q : ℝ³ | T < ‖q‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hpoint : (fun p : ℝ³ => g ‖p‖) =
      ({q : ℝ³ | T < ‖q‖}).indicator (fun p : ℝ³ => (‖p‖ ^ N)⁻¹) := by
    funext p
    by_cases hp : T < ‖p‖
    · simp [g, hp]
    · simp [g, hp]
  have hfull : (∫ p : ℝ³, g ‖p‖) = (∫ p in {q : ℝ³ | T < ‖q‖}, (‖p‖ ^ N)⁻¹) := by
    calc
      (∫ p : ℝ³, g ‖p‖) = ∫ p : ℝ³, ({q : ℝ³ | T < ‖q‖}).indicator
              (fun p : ℝ³ => (‖p‖ ^ N)⁻¹) p := by rw [hpoint]
      _ = ∫ p in {q : ℝ³ | T < ‖q‖}, (‖p‖ ^ N)⁻¹ := integral_indicator hmeas
  have h_inter : Set.Ioi (0 : ℝ) ∩ Set.Ioi T = Set.Ioi T := by
    ext r
    exact ⟨fun hr => hr.2, fun hr => ⟨lt_trans hT hr, hr⟩⟩
  have hJ : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
      = ∫ r in Set.Ioi T, r ^ 2 * (r ^ N)⁻¹ := by
    have hind : (fun r : ℝ => r ^ 2 * g r) =
        (Set.Ioi T).indicator (fun r : ℝ => r ^ 2 * (r ^ N)⁻¹) := by
      funext r
      by_cases hr : r ∈ Set.Ioi T
      · simp [g, hr]
      · simp [g, hr]
    calc
      (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
          = ∫ r in Set.Ioi (0 : ℝ),
              (Set.Ioi T).indicator (fun r : ℝ => r ^ 2 * (r ^ N)⁻¹) r := by rw [hind]
      _ = ∫ r in Set.Ioi (0 : ℝ) ∩ Set.Ioi T, r ^ 2 * (r ^ N)⁻¹ := by
            rw [setIntegral_indicator (s := Set.Ioi (0 : ℝ)) (t := Set.Ioi T)
              (f := fun r : ℝ => r ^ 2 * (r ^ N)⁻¹)
              (by measurability : MeasurableSet (Set.Ioi T))]
      _ = ∫ r in Set.Ioi T, r ^ 2 * (r ^ N)⁻¹ := by rw [h_inter]
  calc
    (∫ p in {q : ℝ³ | T < ‖q‖}, ((‖p‖ : ℝ) ^ N)⁻¹) = ∫ p : ℝ³, g ‖p‖ := hfull.symm
    _ = 4 * Real.pi * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) :=
          Submission.BoseGases.integral_fun_norm_r3 (g := g)
    _ = 4 * Real.pi * (∫ r in Set.Ioi T, r ^ 2 * (r ^ N)⁻¹) := by rw [hJ]

/-- **Integrability of the exterior tail.**  For `N ≥ 4` and `T > 0` the function
`p ↦ ‖p‖^{-N}` is integrable on `{T < ‖p‖} ⊂ ℝ³`.  (On the strictly *larger* set
`{T ≤ ‖p‖}` this is `Work.BoseFixB3.Eps.exterior_norm_integrable` together with the
`L¹`-criterion on the half-line; restrict along the inclusion.) -/
lemma exterior_inv_pow_integrable (N : ℕ) (hN : 4 ≤ N) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun p : ℝ³ => ((‖p‖ : ℝ) ^ N)⁻¹) {q : ℝ³ | T < ‖q‖} := by
  have hNr4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hbase : IntegrableOn (fun p : ℝ³ => ((‖p‖ : ℝ) ^ N)⁻¹) {q : ℝ³ | T ≤ ‖q‖} := by
    refine (Work.BoseFixB3.Eps.exterior_norm_integrable (N := N) hT).mpr ?_
    have hconv : IntegrableOn (fun r : ℝ => r ^ ((2 : ℝ) - N)) (Set.Ioi T) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : (2 : ℝ) - N < -1) hT
    refine hconv.congr_fun (fun r hr => ?_) measurableSet_Ioi
    exact (Work.BoseFixB3.Eps.sq_mul_pow_inv_eq_rpow N (lt_trans hT hr)).symm
  exact hbase.mono_set (show {q : ℝ³ | T < ‖q‖} ⊆ {q : ℝ³ | T ≤ ‖q‖} from by
    intro q hq
    simp only [Set.mem_ofPred_eq] at hq ⊢
    exact le_of_lt hq)

/-- The `‖t‖^{-4}` tail value: `∫_{T < ‖t‖} ‖t‖^{-4} dt = 4π/T` for `T > 0`. -/
lemma exterior_inv4_eq {T : ℝ} (hT : 0 < T) :
    (∫ p in {q : ℝ³ | T < ‖q‖}, ((‖p‖ : ℝ) ^ 4)⁻¹) = 4 * Real.pi / T := by
  rw [exterior_inv_pow_eq 4 hT, Work.BoseFixB3.Eps.Ioi_tail_zpow 4 (by norm_num) hT]
  push_cast
  norm_num
  rw [div_eq_mul_inv]

/-- The `‖t‖^{-6}` tail value: `∫_{T < ‖t‖} ‖t‖^{-6} dt = 4π/(3T³)` for `T > 0`. -/
lemma exterior_inv6_eq {T : ℝ} (hT : 0 < T) :
    (∫ p in {q : ℝ³ | T < ‖q‖}, ((‖p‖ : ℝ) ^ 6)⁻¹) = 4 * Real.pi / (3 * T ^ 3) := by
  rw [exterior_inv_pow_eq 6 hT, Work.BoseFixB3.Eps.Ioi_tail_zpow 6 (by norm_num) hT]
  push_cast
  norm_num
  have hT3 : (T : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hT.ne'
  field_simp

theorem euclTailInvPow :
    (∀ {T : ℝ}, 0 < T →
        MeasureTheory.IntegrableOn (fun t : EuclideanSpace ℝ (Fin 3) => ((‖t‖ : ℝ) ^ 4)⁻¹)
            {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}
          ∧ (∫ t in {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}, ((‖t‖ : ℝ) ^ 4)⁻¹)
              = 4 * Real.pi / T)
      ∧ (∀ {T : ℝ}, 0 < T →
        MeasureTheory.IntegrableOn (fun t : EuclideanSpace ℝ (Fin 3) => ((‖t‖ : ℝ) ^ 6)⁻¹)
            {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}
          ∧ (∫ t in {t : EuclideanSpace ℝ (Fin 3) | T < ‖t‖}, ((‖t‖ : ℝ) ^ 6)⁻¹)
              = 4 * Real.pi / (3 * T ^ 3)) := by
  constructor
  · intro T hT
    exact ⟨exterior_inv_pow_integrable 4 (by norm_num) hT, exterior_inv4_eq hT⟩
  · intro T hT
    exact ⟨exterior_inv_pow_integrable 6 (by norm_num) hT, exterior_inv6_eq hT⟩

end Work.BoseBogFS
