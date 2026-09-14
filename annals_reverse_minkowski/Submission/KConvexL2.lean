import Mathlib
import Submission.LEllStar
-- ⚠ IMPORT-CLASH WORKAROUND (session 123), see `Submission/KConvex.lean`.
import Submission.Fix.HermSumDenseVec
import Submission.Commons.Geometry.Convex.smul_mem_iff_le_inv_gauge
import Submission.Commons.GeometryOfNumbers.gauge_le_iff

/-!
# The K-convexity bound for all of `L²(μ; X)`

`Submission.KConvexGauge.kconvex_gauge` bounds the first chaos component of a *finite Hermite sum*.
Here we extend it to arbitrary `Φ ∈ L²(μ_N; X)` (`X = (ℝⁿ, ‖·‖_K)`), by

* defining the first-chaos projection `Q1` explicitly (`Q1 v x = ∑ᵢ xᵢ • (∫ yᵢ v y ∂μ)/gaussZ N`),
* proving `Q1 (hermSum s C) = comp 1 s C`,
* proving the crude continuity bound `‖Q1 v‖_{L²} ≤ √N ‖v‖_{L²}`,
* extending the Hermite-sum bound to all `v` by density of the Hermite sums.
-/

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal Topology Real Pointwise

namespace Submission.KConvexL2

variable {n N : ℕ}

open Submission.KConvex Submission.GaussianChaos Submission.LEllStar

noncomputable section

/-- Duality: `⟪z, w⟫ ≤ gauge K w` for `z` in the polar of `K`. -/
theorem inner_le_gauge_of_mem_polar {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hcvx : Convex ℝ K) (hKcpt : IsCompact K) (hK0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    {z : EuclideanSpace ℝ (Fin n)} (hz : ∀ y ∈ K, inner ℝ z y ≤ 1)
    (w : EuclideanSpace ℝ (Fin n)) : inner ℝ z w ≤ gauge K w := by
  rcases eq_or_lt_of_le (gauge_nonneg w) with h | h
  · have hmem : w ∈ (0 : ℝ) • K := by
      refine Commons.GeometryOfNumbers.mem_smul_of_forall_lt hKcpt (interior_subset hK0) le_rfl
        (fun r hr => ?_)
      exact (Commons.Geometry.Convex.gauge_le_iff_of_pos hKcpt hcvx hK0 hr).mp
        (by rw [← h]; exact hr.le)
    have hne : K.Nonempty := ⟨0, interior_subset hK0⟩
    rw [zero_smul_set hne] at hmem
    have hw : w = 0 := by simpa using hmem
    rw [hw]; simp
  · obtain ⟨y, hy, hyw⟩ :=
      (Commons.Geometry.Convex.gauge_le_iff_of_pos hKcpt hcvx hK0 h).mp le_rfl
    have hsw : (gauge K w) • y = w := hyw
    have key : inner ℝ z w = gauge K w * inner ℝ z y := by
      conv_lhs => rw [← hsw]
      rw [inner_smul_right]
    rw [key]
    exact mul_le_of_le_one_right h.le (hz y hy)

/-- Jensen for `gauge K` with respect to any measure. -/
theorem gauge_integral_le_finite {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcvx : Convex ℝ K) (hKcpt : IsCompact K) (hK0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    {α : Type*} [MeasurableSpace α] {ν : Measure α} (Φ : α → EuclideanSpace ℝ (Fin n))
    (hΦ : Integrable Φ ν) (hΦg : Integrable (fun a => gauge K (Φ a)) ν) :
    gauge K (∫ a, Φ a ∂ν) ≤ ∫ a, gauge K (Φ a) ∂ν := by
  rw [Commons.Geometry.Convex.gauge_eq_sSup_inner_polar K hcvx hKcpt hK0]
  refine csSup_le ⟨0, 0, (fun y _ => by simp), by simp⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  have hzi : Integrable (fun a => inner ℝ z (Φ a)) ν := (innerSL ℝ z).integrable_comp hΦ
  have hcomm : inner ℝ z (∫ a, Φ a ∂ν) = ∫ a, inner ℝ z (Φ a) ∂ν :=
    (ContinuousLinearMap.integral_comp_comm (innerSL ℝ z) hΦ).symm
  simp only [hcomm]
  exact integral_mono hzi hΦg (fun a => inner_le_gauge_of_mem_polar hcvx hKcpt hK0 hz (Φ a))

/-! ### The first-chaos projection -/

/-- The energy of a standard basis multi-index equals the total mass `gaussZ N`. -/
theorem energy_single_one (i : Fin N) :
    Submission.GaussianChaos.energy (Pi.single i (1:ℕ)) = gaussZ N := by
  rw [Submission.GaussianChaos.energy, gaussZ]
  rw [Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, Nat.factorial_one, Nat.cast_one, one_mul]
  · intro k _ hk; rw [Pi.single_eq_of_ne hk, Nat.factorial_zero, Nat.cast_one]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The first-chaos projection `Q₁`. -/
noncomputable def Q1 (v : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n) :=
  fun x => ∑ i : Fin N, (x.ofLp i) •
    ((gaussZ N)⁻¹ • (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
      ∂Submission.GaussianChaos.μ N))

/-- `∫ yᵢ • v y ∂μ` for a finite Hermite sum `v`. -/
theorem integral_coord_smul_hermSum (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) (i : Fin N) :
    ∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • Submission.GaussianChaos.hermSum s C y
        ∂Submission.GaussianChaos.μ N
      = (if Pi.single i (1:ℕ) ∈ s then gaussZ N else 0) • C (Pi.single i (1:ℕ)) := by
  classical
  have hpt : ∀ y : EuclideanSpace ℝ (Fin N),
      (y.ofLp i) • Submission.GaussianChaos.hermSum s C y
        = ∑ α ∈ s, (y.ofLp i * Submission.GaussianChaos.herm α y) • C α := by
    intro y
    rw [Submission.GaussianChaos.hermSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [smul_smul]
  have hval : ∀ α : Fin N → ℕ,
      (∫ y : EuclideanSpace ℝ (Fin N), y.ofLp i * Submission.GaussianChaos.herm α y
        ∂Submission.GaussianChaos.μ N)
        = (if α = Pi.single i (1:ℕ) then gaussZ N else 0) := by
    intro α
    by_cases hα : α = Pi.single i (1:ℕ)
    · subst hα
      rw [if_pos rfl]
      have hcongr : (fun x : EuclideanSpace ℝ (Fin N) =>
            x.ofLp i * Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) x)
          = fun x => (Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) x)^2 := by
        funext x; rw [herm_single_one i x]; ring
      rw [hcongr, Submission.GaussianChaos.integral_herm_sq, energy_single_one]
    · rw [if_neg hα]
      have hcongr : (fun x : EuclideanSpace ℝ (Fin N) =>
            x.ofLp i * Submission.GaussianChaos.herm α x)
          = fun x => Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) x
              * Submission.GaussianChaos.herm α x := by
        funext x; rw [herm_single_one i x]
      rw [hcongr]
      exact Submission.GaussianChaos.integral_herm_mul_herm (fun h => hα h.symm)
  rw [funext hpt, integral_finsetSum]
  swap
  · intro α _
    have h : Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
        (Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) x
          * Submission.GaussianChaos.herm α x) • C α) (Submission.GaussianChaos.μ N) :=
      (Submission.GaussianChaos.integrable_herm_mul_herm (Pi.single i (1:ℕ)) α).smul_const (C α)
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    change (Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) y
        * Submission.GaussianChaos.herm α y) • C α
      = (y.ofLp i * Submission.GaussianChaos.herm α y) • C α
    rw [herm_single_one i y]
  have hsum : (∑ α ∈ s, (∫ y : EuclideanSpace ℝ (Fin N),
        (y.ofLp i * Submission.GaussianChaos.herm α y) • C α
          ∂Submission.GaussianChaos.μ N))
      = ∑ α ∈ s, (if α = Pi.single i (1:ℕ) then gaussZ N else 0) • C α := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_smul_const (f := fun y : EuclideanSpace ℝ (Fin N) =>
      y.ofLp i * Submission.GaussianChaos.herm α y) (c := C α), hval]
  rw [hsum]
  by_cases hi : Pi.single i (1:ℕ) ∈ s
  · rw [if_pos hi, Finset.sum_eq_single (Pi.single i (1:ℕ))]
    · rw [if_pos rfl]
    · intro α _ hα; rw [if_neg hα, zero_smul]
    · intro h; exact absurd hi h
  · rw [if_neg hi]
    have hzero : (∑ α ∈ s, (if α = Pi.single i (1:ℕ) then gaussZ N else 0) • C α) = 0 := by
      rw [Finset.sum_eq_zero]
      intro α hα
      have hne : α ≠ Pi.single i (1:ℕ) := by
        intro h; exact hi (by rw [← h]; exact hα)
      rw [if_neg hne, zero_smul]
    rw [hzero, zero_smul]

/-- `Q₁` of a finite Hermite sum is its first-chaos component. -/
theorem Q1_hermSum (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    Q1 (fun y => Submission.GaussianChaos.hermSum s C y)
      = fun x => Submission.KConvex.comp 1 s C x := by
  classical
  funext x
  rw [Q1, comp_one_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_coord_smul_hermSum]
  by_cases hi : Pi.single i (1:ℕ) ∈ s
  · rw [if_pos hi, if_pos hi]
    simp only [smul_smul, mul_assoc, inv_mul_cancel₀ (gaussZ_ne_zero N), mul_one, one_smul]
  · rw [if_neg hi, if_neg hi]; simp

/-! ### Linearity and continuity of `Q₁` -/

theorem integral_coord_smul_add (v w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, Integrable (fun y : EuclideanSpace ℝ (Fin N) => (y.ofLp i) • v y)
      (Submission.GaussianChaos.μ N))
    (hw : ∀ i, Integrable (fun y : EuclideanSpace ℝ (Fin N) => (y.ofLp i) • w y)
      (Submission.GaussianChaos.μ N)) (i : Fin N) :
    (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • (v y + w y) ∂Submission.GaussianChaos.μ N)
      = (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y ∂Submission.GaussianChaos.μ N)
        + (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • w y ∂Submission.GaussianChaos.μ N) := by
  rw [← integral_add (hv i) (hw i)]
  congr 1
  funext y
  rw [smul_add]

theorem Q1_add (v w : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, Integrable (fun y : EuclideanSpace ℝ (Fin N) => (y.ofLp i) • v y)
      (Submission.GaussianChaos.μ N))
    (hw : ∀ i, Integrable (fun y : EuclideanSpace ℝ (Fin N) => (y.ofLp i) • w y)
      (Submission.GaussianChaos.μ N)) :
    Q1 (v + w) = Q1 v + Q1 w := by
  funext x
  simp only [Q1, Pi.add_apply]
  rw [Finset.sum_congr rfl (fun i _ => by rw [integral_coord_smul_add v w hv hw i])]
  simp only [smul_add, Finset.sum_add_distrib]

/-- Minkowski for the square roots of `L²` norms. -/
theorem sqrt_integral_add_le {f g : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemLp f 2 (Submission.GaussianChaos.μ N))
    (hg : MemLp g 2 (Submission.GaussianChaos.μ N)) :
    Real.sqrt (∫ x, (f x + g x) ^ 2 ∂Submission.GaussianChaos.μ N)
      ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂Submission.GaussianChaos.μ N)
        + Real.sqrt (∫ x, (g x) ^ 2 ∂Submission.GaussianChaos.μ N) := by
  have hfg : MemLp (fun x => f x + g x) 2 (Submission.GaussianChaos.μ N) := hf.add hg
  have h2 : hfg.toLp (fun x => f x + g x) = hf.toLp f + hg.toLp g := MemLp.toLp_add hf hg
  have h1 : ‖hfg.toLp (fun x => f x + g x)‖ ≤ ‖hf.toLp f‖ + ‖hg.toLp g‖ := by
    rw [h2]; exact norm_add_le _ _
  have e1 : ‖hfg.toLp (fun x => f x + g x)‖
      = Real.sqrt (∫ x, (f x + g x) ^ 2 ∂Submission.GaussianChaos.μ N) := norm_toLp_sqrt hfg
  have e2 : ‖hf.toLp f‖ = Real.sqrt (∫ x, (f x) ^ 2 ∂Submission.GaussianChaos.μ N) :=
    norm_toLp_sqrt hf
  have e3 : ‖hg.toLp g‖ = Real.sqrt (∫ x, (g x) ^ 2 ∂Submission.GaussianChaos.μ N) :=
    norm_toLp_sqrt hg
  rw [e1, e2, e3] at h1
  exact h1


/-- Comparison of the Euclidean norm with the gauge of a compact body. -/
theorem exists_gauge_le_mul_norm (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (hK0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K) :
    ∃ cu : ℝ, 0 < cu ∧ ∀ w : EuclideanSpace ℝ (Fin n), gauge K w ≤ cu * ‖w‖ := by
  obtain ⟨r, hr0, hr⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hK0)
  refine ⟨2 / r, by positivity, fun w => ?_⟩
  have hmem : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (r / 2) ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) :=
    Metric.closedBall_mem_nhds _ (by linarith)
  have habs : Absorbent ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (r / 2)) :=
    absorbent_nhds_zero hmem
  have hsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (r / 2) ⊆ K :=
    (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hr
  calc gauge K w ≤ gauge (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (r / 2)) w :=
        gauge_mono habs hsub w
    _ = ‖w‖ / (r / 2) := gauge_closedBall (by linarith) w
    _ = 2 / r * ‖w‖ := by field_simp

theorem exists_norm_le_mul_gauge (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (hKcpt : IsCompact K) (hK0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ ≤ R * gauge K w := by
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin n))).mp
    hKcpt.isBounded
  refine ⟨max R₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun w => ?_⟩
  have hRpos : 0 < max R₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsub : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (max R₀ 1) :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have habs : Absorbent ℝ K := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp hK0)
  have hmono := gauge_mono habs hsub w
  rw [gauge_closedBall hRpos.le w, div_le_iff₀ hRpos] at hmono
  calc ‖w‖ ≤ gauge K w * max R₀ 1 := hmono
    _ = max R₀ 1 * gauge K w := by ring

theorem Q1_crude (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (habs : Absorbent ℝ K) (hbdd : Bornology.IsVonNBounded ℝ K) (hbal : Balanced ℝ K)
    (hcpt : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (v : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n))
    (hvmeas : AEStronglyMeasurable v (Submission.GaussianChaos.μ N))
    (hv : MemLp (fun x => gauge K (v x)) 2 (Submission.GaussianChaos.μ N)) :
    ∫ x, (gauge K (Q1 v x)) ^ 2 ∂Submission.GaussianChaos.μ N
      ≤ (N : ℝ) ^ 2 * ∫ x, (gauge K (v x)) ^ 2 ∂Submission.GaussianChaos.μ N := by
  classical
  have hΔ : (0:ℝ) < gaussZ N := gaussZ_pos N
  set A : ℝ := ∫ x, (gauge K (v x)) ^ 2 ∂Submission.GaussianChaos.μ N with hA
  have hAnn : 0 ≤ A := integral_nonneg (fun x => sq_nonneg _)
  set G : ℝ := Real.sqrt A with hG
  have hGnn : 0 ≤ G := Real.sqrt_nonneg _
  have hcoord : ∀ i : Fin N,
      MemLp (fun y : EuclideanSpace ℝ (Fin N) => y.ofLp i) 2 (Submission.GaussianChaos.μ N) := by
    intro i
    rw [memLp_two_iff_integrable_sq (by fun_prop :
      AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin N) => y.ofLp i)
        (Submission.GaussianChaos.μ N))]
    refine (Submission.GaussianChaos.integrable_herm_mul_herm (Pi.single i (1:ℕ))
      (Pi.single i (1:ℕ))).congr (Filter.Eventually.of_forall fun y => ?_)
    change Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) y
        * Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) y = y.ofLp i ^ 2
    rw [herm_single_one i y]
    ring
  have hprodint : ∀ i : Fin N, Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
      |y.ofLp i| * gauge K (v y)) (Submission.GaussianChaos.μ N) := by
    intro i
    rw [← memLp_one_iff_integrable]
    have h : MemLp ((fun x : EuclideanSpace ℝ (Fin N) => ‖x.ofLp i‖)
        * fun x => gauge K (v x)) 1 (Submission.GaussianChaos.μ N) := hv.mul (hcoord i).norm
    rw [memLp_one_iff_integrable]
    refine (memLp_one_iff_integrable.mp h).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply, Real.norm_eq_abs, mul_comm]
  -- Cauchy-Schwarz for the scalar products
  have hcs : ∀ i : Fin N,
      (∫ y : EuclideanSpace ℝ (Fin N), |y.ofLp i| * gauge K (v y)
        ∂Submission.GaussianChaos.μ N) ≤ Real.sqrt (gaussZ N) * G := by
    intro i
    have h1 := integral_mul_norm_le_Lp_mul_Lq (μ := Submission.GaussianChaos.μ N)
      (p := (2:ℝ)) (q := (2:ℝ))
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
      (f := fun y : EuclideanSpace ℝ (Fin N) => |y.ofLp i|) (g := fun y => gauge K (v y))
      (by simpa [Real.norm_eq_abs] using (hcoord i).norm) (by simpa using hv)
    have hL : (∫ y : EuclideanSpace ℝ (Fin N), |y.ofLp i| * gauge K (v y)
        ∂Submission.GaussianChaos.μ N)
        = ∫ y : EuclideanSpace ℝ (Fin N), ‖|y.ofLp i|‖ * ‖gauge K (v y)‖
          ∂Submission.GaussianChaos.μ N := by
      congr 1
      funext y
      rw [Real.norm_eq_abs, abs_abs, Real.norm_of_nonneg (gauge_nonneg _)]
    have hR1 : (∫ y : EuclideanSpace ℝ (Fin N), ‖|y.ofLp i|‖ ^ (2:ℝ)
        ∂Submission.GaussianChaos.μ N) ^ ((1:ℝ)/2) = Real.sqrt (gaussZ N) := by
      have hA : (∫ y : EuclideanSpace ℝ (Fin N), ‖|y.ofLp i|‖ ^ (2:ℝ)
          ∂Submission.GaussianChaos.μ N) = gaussZ N := by
        rw [show (fun y : EuclideanSpace ℝ (Fin N) => ‖|y.ofLp i|‖ ^ (2:ℝ))
            = fun y => ‖|y.ofLp i|‖ ^ 2 from funext fun y => Real.rpow_natCast _ 2]
        rw [show (fun y : EuclideanSpace ℝ (Fin N) => ‖|y.ofLp i|‖ ^ 2)
            = fun y => y.ofLp i * y.ofLp i from funext fun y => by
              rw [Real.norm_eq_abs, abs_abs, sq_abs, sq]]
        rw [integral_coord_mul_coord i i, if_pos rfl, mul_one]
      rw [hA, show gaussZ N ^ ((1:ℝ)/2) = Real.sqrt (gaussZ N) from (Real.sqrt_eq_rpow _).symm]
    have hR2 : (∫ y : EuclideanSpace ℝ (Fin N), ‖gauge K (v y)‖ ^ (2:ℝ)
        ∂Submission.GaussianChaos.μ N) ^ ((1:ℝ)/2) = G := by
      have hA : (∫ y : EuclideanSpace ℝ (Fin N), ‖gauge K (v y)‖ ^ (2:ℝ)
          ∂Submission.GaussianChaos.μ N) = A := by
        rw [show (fun y : EuclideanSpace ℝ (Fin N) => ‖gauge K (v y)‖ ^ (2:ℝ))
            = fun y => ‖gauge K (v y)‖ ^ 2 from funext fun y => Real.rpow_natCast _ 2]
        rw [show (fun y : EuclideanSpace ℝ (Fin N) => ‖gauge K (v y)‖ ^ 2)
            = fun y => (gauge K (v y)) ^ 2 from funext fun y => by
              rw [Real.norm_of_nonneg (gauge_nonneg _)]]
      rw [hA, show A ^ ((1:ℝ)/2) = G from by rw [hG, Real.sqrt_eq_rpow]]
    calc (∫ y : EuclideanSpace ℝ (Fin N), |y.ofLp i| * gauge K (v y)
          ∂Submission.GaussianChaos.μ N)
        = ∫ y : EuclideanSpace ℝ (Fin N), ‖|y.ofLp i|‖ * ‖gauge K (v y)‖
            ∂Submission.GaussianChaos.μ N := hL
      _ ≤ (∫ y : EuclideanSpace ℝ (Fin N), ‖|y.ofLp i|‖ ^ (2:ℝ)
              ∂Submission.GaussianChaos.μ N) ^ ((1:ℝ)/2)
            * (∫ y : EuclideanSpace ℝ (Fin N), ‖gauge K (v y)‖ ^ (2:ℝ)
              ∂Submission.GaussianChaos.μ N) ^ ((1:ℝ)/2) := h1
      _ = Real.sqrt (gaussZ N) * G := by rw [hR1, hR2]

  -- the coordinate functionals
  have hci : ∀ i : Fin N,
      gauge K ((gaussZ N)⁻¹ • (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
        ∂Submission.GaussianChaos.μ N)) ≤ G / Real.sqrt (gaussZ N) := by
    intro i
    by_cases hint : Integrable (fun y : EuclideanSpace ℝ (Fin N) => (y.ofLp i) • v y)
        (Submission.GaussianChaos.μ N)
    · have hgi : Integrable (fun y : EuclideanSpace ℝ (Fin N) => gauge K ((y.ofLp i) • v y))
          (Submission.GaussianChaos.μ N) := by
        rw [show (fun y : EuclideanSpace ℝ (Fin N) => gauge K ((y.ofLp i) • v y))
            = fun y => |y.ofLp i| * gauge K (v y) from funext fun y => by
              rw [gauge_smul hbal, Real.norm_eq_abs]]
        exact hprodint i
      have hJ := gauge_integral_le_finite K hcvx hcpt h0
        (fun y : EuclideanSpace ℝ (Fin N) => (y.ofLp i) • v y) hint hgi
      rw [show (∫ y : EuclideanSpace ℝ (Fin N), gauge K ((y.ofLp i) • v y)
            ∂Submission.GaussianChaos.μ N)
          = ∫ y : EuclideanSpace ℝ (Fin N), |y.ofLp i| * gauge K (v y)
              ∂Submission.GaussianChaos.μ N from by
        congr 1; funext y; rw [gauge_smul hbal, Real.norm_eq_abs]] at hJ
      rw [show gauge K ((gaussZ N)⁻¹ • (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
          ∂Submission.GaussianChaos.μ N))
          = (gaussZ N)⁻¹ * gauge K (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
              ∂Submission.GaussianChaos.μ N) from by
        rw [gauge_smul hbal, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΔ)]]
      calc (gaussZ N)⁻¹ * gauge K (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
              ∂Submission.GaussianChaos.μ N)
          ≤ (gaussZ N)⁻¹ * (Real.sqrt (gaussZ N) * G) :=
            mul_le_mul_of_nonneg_left (hJ.trans (hcs i)) (inv_nonneg.mpr hΔ.le)
        _ = G / Real.sqrt (gaussZ N) := by
            rw [div_eq_mul_inv]
            field_simp
            rw [Real.sq_sqrt hΔ.le]
    · rw [integral_undef hint]
      simp only [smul_zero, gauge_zero]
      exact div_nonneg hGnn (Real.sqrt_nonneg _)
  -- the pointwise bound
  have hpt : ∀ x : EuclideanSpace ℝ (Fin N),
      gauge K (Q1 v x) ≤ (∑ i, |x.ofLp i|) * (G / Real.sqrt (gaussZ N)) := by
    intro x
    have h1 : gauge K (∑ i : Fin N, (x.ofLp i) •
        ((gaussZ N)⁻¹ • (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
          ∂Submission.GaussianChaos.μ N)))
        ≤ ∑ i : Fin N, gauge K ((x.ofLp i) •
            ((gaussZ N)⁻¹ • (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
              ∂Submission.GaussianChaos.μ N))) :=
      gauge_sum_le hcvx habs _ _
    rw [show Q1 v x = ∑ i : Fin N, (x.ofLp i) •
        ((gaussZ N)⁻¹ • (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
          ∂Submission.GaussianChaos.μ N)) from rfl]
    calc gauge K _ ≤ ∑ i, gauge K ((x.ofLp i) •
            ((gaussZ N)⁻¹ • (∫ y, (y.ofLp i) • v y ∂Submission.GaussianChaos.μ N))) := h1
      _ = ∑ i, |x.ofLp i| * gauge K ((gaussZ N)⁻¹ • (∫ y, (y.ofLp i) • v y
            ∂Submission.GaussianChaos.μ N)) :=
          Finset.sum_congr rfl fun i _ => by rw [gauge_smul hbal, Real.norm_eq_abs]
      _ ≤ ∑ i, |x.ofLp i| * (G / Real.sqrt (gaussZ N)) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hci i) (abs_nonneg _)
      _ = (∑ i, |x.ofLp i|) * (G / Real.sqrt (gaussZ N)) := by rw [Finset.sum_mul]
  -- integrability
  have hxint : Integrable (fun x : EuclideanSpace ℝ (Fin N) => ∑ i, (x.ofLp i) ^ 2)
      (Submission.GaussianChaos.μ N) := by
    refine integrable_finsetSum _ fun i _ => ?_
    have hb : (fun x : EuclideanSpace ℝ (Fin N) => (x.ofLp i) ^ 2)
        = fun x => Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) x
            * Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) x := by
      funext x; rw [herm_single_one i x]; ring
    rw [hb]
    exact Submission.GaussianChaos.integrable_herm_mul_herm _ _
  have hint2 : (∫ x : EuclideanSpace ℝ (Fin N), ∑ i, (x.ofLp i) ^ 2
      ∂Submission.GaussianChaos.μ N) = (N : ℝ) * gaussZ N := by
    rw [integral_finsetSum _ (fun i _ => by
      have hb : (fun x : EuclideanSpace ℝ (Fin N) => (x.ofLp i) ^ 2)
          = fun x => Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) x
              * Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) x := by
        funext x; rw [herm_single_one i x]; ring
      rw [hb]
      exact Submission.GaussianChaos.integrable_herm_mul_herm _ _)]
    rw [Finset.sum_congr rfl (fun i _ => ?_), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [show (∫ x : EuclideanSpace ℝ (Fin N), (x.ofLp i) ^ 2 ∂Submission.GaussianChaos.μ N)
        = ∫ x, x.ofLp i * x.ofLp i ∂Submission.GaussianChaos.μ N from by
      congr 1; funext x; ring]
    rw [integral_coord_mul_coord i i, if_pos rfl, mul_one]
  have hpt2 : ∀ x : EuclideanSpace ℝ (Fin N),
      (∑ i, |x.ofLp i|) ^ 2 ≤ (N : ℝ) * ∑ i, (x.ofLp i) ^ 2 := by
    intro x
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
      (fun i => |x.ofLp i|) (fun _ => (1:ℝ))
    simp only [mul_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sq_abs] at h
    linarith [h]
  -- assemble
  set c2 : ℝ := G / Real.sqrt (gaussZ N) with hc2
  have hc2nn : 0 ≤ c2 := div_nonneg hGnn (Real.sqrt_nonneg _)
  have hInt3 : Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
      ((∑ i, |x.ofLp i|) * c2) ^ 2) (Submission.GaussianChaos.μ N) := by
    refine Integrable.mono' (hxint.const_mul ((N:ℝ) * c2 ^ 2)) (by fun_prop) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc ((∑ i, |x.ofLp i|) * c2) ^ 2 = (∑ i, |x.ofLp i|) ^ 2 * c2 ^ 2 := by ring
      _ ≤ ((N : ℝ) * ∑ i, (x.ofLp i) ^ 2) * c2 ^ 2 :=
          mul_le_mul_of_nonneg_right (hpt2 x) (sq_nonneg c2)
      _ = (N : ℝ) * c2 ^ 2 * ∑ i, (x.ofLp i) ^ 2 := by ring
  calc ∫ x, (gauge K (Q1 v x)) ^ 2 ∂Submission.GaussianChaos.μ N
      ≤ ∫ x, ((∑ i, |x.ofLp i|) * c2) ^ 2 ∂Submission.GaussianChaos.μ N := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
          hInt3 (Filter.Eventually.of_forall fun x => ?_)
        exact pow_le_pow_left₀ (gauge_nonneg (Q1 v x)) (hpt x) 2
    _ = c2 ^ 2 * ∫ x, (∑ i, |x.ofLp i|) ^ 2 ∂Submission.GaussianChaos.μ N := by
        rw [show (fun x : EuclideanSpace ℝ (Fin N) => ((∑ i, |x.ofLp i|) * c2) ^ 2)
            = fun x => c2 ^ 2 * (∑ i, |x.ofLp i|) ^ 2 from
          funext fun x => by rw [mul_pow]; ring,
          integral_const_mul]
    _ ≤ c2 ^ 2 * ∫ x, ((N : ℝ) * ∑ i, (x.ofLp i) ^ 2) ∂Submission.GaussianChaos.μ N :=
        mul_le_mul_of_nonneg_left
          (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x =>
              sq_nonneg (∑ i, |x.ofLp i|))
            (hxint.const_mul _) (Filter.Eventually.of_forall hpt2)) (sq_nonneg c2)
    _ = c2 ^ 2 * ((N : ℝ) * ((N : ℝ) * gaussZ N)) := by
        rw [integral_const_mul, hint2]
    _ = (N : ℝ) ^ 2 * A := by
        rw [hc2, hG, div_pow, Real.sq_sqrt hAnn, Real.sq_sqrt hΔ.le]
        field_simp


theorem memLp_gauge_Q1 (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (hbal : Balanced ℝ K) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (v : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n)) :
    MemLp (fun x => gauge K (Q1 v x)) 2 (Submission.GaussianChaos.μ N) := by
  classical
  set M : ℝ := ∑ i : Fin N, gauge K ((gaussZ N)⁻¹ • (∫ y : EuclideanSpace ℝ (Fin N),
      (y.ofLp i) • v y ∂Submission.GaussianChaos.μ N)) with hM
  have hcoord : ∀ i : Fin N,
      MemLp (fun y : EuclideanSpace ℝ (Fin N) => y.ofLp i) 2 (Submission.GaussianChaos.μ N) := by
    intro i
    rw [memLp_two_iff_integrable_sq (by fun_prop :
      AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin N) => y.ofLp i)
        (Submission.GaussianChaos.μ N))]
    refine (Submission.GaussianChaos.integrable_herm_mul_herm (Pi.single i (1:ℕ))
      (Pi.single i (1:ℕ))).congr (Filter.Eventually.of_forall fun y => ?_)
    change Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) y
        * Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) y = y.ofLp i ^ 2
    rw [herm_single_one i y]
    ring
  have hg : MemLp (fun x : EuclideanSpace ℝ (Fin N) => ∑ i, |x.ofLp i|)
      2 (Submission.GaussianChaos.μ N) := by
    have h : MemLp (fun x : EuclideanSpace ℝ (Fin N) => ∑ i, ‖x.ofLp i‖)
        2 (Submission.GaussianChaos.μ N) :=
      memLp_finsetSum _ fun i _ => (hcoord i).norm
    simpa only [Real.norm_eq_abs] using h
  refine MemLp.of_le_mul (f := fun x => gauge K (Q1 v x))
    (g := fun x : EuclideanSpace ℝ (Fin N) => ∑ i, |x.ofLp i|) (c := M) hg ?_ ?_
  · have hQ1eq : Q1 v = fun x : EuclideanSpace ℝ (Fin N) => ∑ i : Fin N, (x.ofLp i) •
        ((gaussZ N)⁻¹ • (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
          ∂Submission.GaussianChaos.μ N)) := rfl
    have hcont : Continuous (Q1 v) := by
      rw [hQ1eq]
      exact continuous_finsetSum _ fun i _ =>
        (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin N) => x.ofLp i).smul
          continuous_const
    exact ((continuous_gauge hcvx (mem_interior_iff_mem_nhds.mp h0)).comp hcont).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (gauge_nonneg _),
      Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
    rw [show Q1 v x = ∑ i : Fin N, (x.ofLp i) • ((gaussZ N)⁻¹ •
        (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y ∂Submission.GaussianChaos.μ N)) from rfl]
    calc gauge K (∑ i : Fin N, (x.ofLp i) • ((gaussZ N)⁻¹ •
            (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
              ∂Submission.GaussianChaos.μ N)))
        ≤ ∑ i : Fin N, gauge K ((x.ofLp i) • ((gaussZ N)⁻¹ •
            (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
              ∂Submission.GaussianChaos.μ N))) :=
          gauge_sum_le hcvx (absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)) _ _
      _ = ∑ i : Fin N, |x.ofLp i| * gauge K ((gaussZ N)⁻¹ •
            (∫ y : EuclideanSpace ℝ (Fin N), (y.ofLp i) • v y
              ∂Submission.GaussianChaos.μ N)) :=
          Finset.sum_congr rfl fun i _ => by rw [gauge_smul hbal, Real.norm_eq_abs]
      _ ≤ ∑ i : Fin N, |x.ofLp i| * M := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact Finset.single_le_sum
            (f := fun i : Fin N => gauge K ((gaussZ N)⁻¹ • (∫ y : EuclideanSpace ℝ (Fin N),
              (y.ofLp i) • v y ∂Submission.GaussianChaos.μ N)))
            (fun j _ => gauge_nonneg _) (Finset.mem_univ i)
      _ = M * (∑ i, |x.ofLp i|) := by rw [← Finset.sum_mul, mul_comm]

theorem integrable_coord_smul {v : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n)}
    (hv : MemLp v 2 (Submission.GaussianChaos.μ N)) (i : Fin N) :
    Integrable (fun y : EuclideanSpace ℝ (Fin N) => (y.ofLp i) • v y)
      (Submission.GaussianChaos.μ N) := by
  have hc : MemLp (fun y : EuclideanSpace ℝ (Fin N) => y.ofLp i) 2
      (Submission.GaussianChaos.μ N) := by
    rw [memLp_two_iff_integrable_sq (by fun_prop :
      AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin N) => y.ofLp i)
        (Submission.GaussianChaos.μ N))]
    refine (Submission.GaussianChaos.integrable_herm_mul_herm (Pi.single i (1:ℕ))
      (Pi.single i (1:ℕ))).congr (Filter.Eventually.of_forall fun y => ?_)
    change Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) y
        * Submission.GaussianChaos.herm (Pi.single i (1:ℕ)) y = y.ofLp i ^ 2
    rw [herm_single_one i y]
    ring
  have h : MemLp ((fun y : EuclideanSpace ℝ (Fin N) => y.ofLp i) • v) 1
      (Submission.GaussianChaos.μ N) := hv.smul hc
  exact (memLp_one_iff_integrable.mp h).congr (Filter.Eventually.of_forall fun y => rfl)

theorem kconvex_l2 (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (habs : Absorbent ℝ K) (hbdd : Bornology.IsVonNBounded ℝ K) (hbal : Balanced ℝ K)
    (hcpt : IsCompact K) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (hKsymm : (-K : Set (EuclideanSpace ℝ (Fin n))) = K)
    {d : ℝ} (hd : 1 ≤ d) (T : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT1 : ∀ x, ‖T x‖ ≤ gauge K x) (hT2 : ∀ x, gauge K x ≤ d * ‖T x‖)
    (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n))
    (hΦ : MemLp Φ 2 (Submission.GaussianChaos.μ N))
    (hΦg : MemLp (fun x => gauge K (Φ x)) 2 (Submission.GaussianChaos.μ N)) :
    ∫ x, (gauge K (Q1 Φ x)) ^ 2 ∂Submission.GaussianChaos.μ N
      ≤ (4 * (1 + Real.log d / Real.log 2)) ^ 2 *
        ∫ x, (gauge K (Φ x)) ^ 2 ∂Submission.GaussianChaos.μ N := by
  classical
  set C0 : ℝ := 4 * (1 + Real.log d / Real.log 2) with hC0
  set A : ℝ := ∫ x, (gauge K (Φ x)) ^ 2 ∂Submission.GaussianChaos.μ N with hA
  have hAnn : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hC0nn : 0 ≤ C0 := by
    rw [hC0]; have := Real.log_nonneg hd; positivity
  obtain ⟨cu, hcu, hcu_b⟩ := exists_gauge_le_mul_norm K hcvx h0
  have hCnon : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hHerm : ∀ (s : Finset (Fin N → ℕ)) (C' : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)),
      Real.sqrt (∫ x, (gauge K (Q1 (fun y => Submission.GaussianChaos.hermSum s C' y) x)) ^ 2
          ∂Submission.GaussianChaos.μ N)
        ≤ C0 * Real.sqrt (∫ x, (gauge K (Submission.GaussianChaos.hermSum s C' x)) ^ 2
            ∂Submission.GaussianChaos.μ N) := by
    intro s C'
    have h := Submission.KConvexGauge.kconvex_gauge K hcvx habs hbdd hbal hcpt
      (mem_interior_iff_mem_nhds.mp h0) h0 hKsymm hd T hT1 hT2 s C'
    have hC0' : (4 * (1 + Real.log d / Real.log 2)) ^ 2 = C0 ^ 2 := by rw [hC0]
    rw [hC0'] at h
    have hq : Q1 (fun y => Submission.GaussianChaos.hermSum s C' y)
        = fun x => Submission.KConvex.comp 1 s C' x := Q1_hermSum s C'
    rw [hq]
    refine (Real.sqrt_le_sqrt h).trans (le_of_eq ?_)
    rw [Real.sqrt_mul (sq_nonneg C0), Real.sqrt_sq hC0nn]
  have hfinal : Real.sqrt (∫ x, (gauge K (Q1 Φ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
      ≤ C0 * Real.sqrt A := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set η : ℝ := δ / (C0 + (N:ℝ) + 1) with hη
    have hK1pos : 0 < C0 + (N:ℝ) + 1 := by linarith
    have hηpos : 0 < η := by rw [hη]; exact div_pos hδ hK1pos
    have hηle : (C0 + (N:ℝ)) * η ≤ δ := by
      rw [hη, mul_div_assoc', div_le_iff₀ hK1pos]; nlinarith [hC0nn, hCnon, hδ]
    obtain ⟨s, C', hsC'⟩ := Commons.Analysis.GaussianMeasure.hermSum_dense_vec Φ hΦ
      (η / (cu + 1)) (by positivity)
    set Ψ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n) :=
      fun y => Submission.GaussianChaos.hermSum s C' y with hΨ
    have hΨmem : MemLp Ψ 2 (Submission.GaussianChaos.μ N) := memLp_hermSum s C'
    have hΨg : MemLp (fun x => gauge K (Ψ x)) 2 (Submission.GaussianChaos.μ N) := by
      rw [hΨ]
      exact memLp_gauge_hermSum K hcvx (mem_interior_iff_mem_nhds.mp h0) d (le_trans zero_le_one hd)
        T hT1 hT2 s C'
    have hcontΨ : Continuous Ψ := by rw [hΨ]; exact continuous_hermSum s C'
    have hdiffg : MemLp (fun x => gauge K (Φ x - Ψ x)) 2 (Submission.GaussianChaos.μ N) := by
      refine MemLp.of_le_mul (f := fun x => gauge K (Φ x - Ψ x))
        (g := fun x => gauge K (Φ x) + gauge K (Ψ x)) (c := 1) (hΦg.add hΨg) ?_ ?_
      · exact (continuous_gauge hcvx (mem_interior_iff_mem_nhds.mp h0)).comp_aestronglyMeasurable
          (hΦ.aestronglyMeasurable.sub hcontΨ.aestronglyMeasurable)
      · filter_upwards with x
        rw [Real.norm_of_nonneg (gauge_nonneg _), one_mul,
          Real.norm_of_nonneg (add_nonneg (gauge_nonneg _) (gauge_nonneg _))]
        have hsym : ∀ z ∈ K, -z ∈ K := by
          intro z hz
          have : -z ∈ (-K : Set (EuclideanSpace ℝ (Fin n))) := by simpa using hz
          rwa [hKsymm] at this
        calc gauge K (Φ x - Ψ x) = gauge K (Φ x + -Ψ x) := by rw [sub_eq_add_neg]
          _ ≤ gauge K (Φ x) + gauge K (-Ψ x) := gauge_add_le hcvx habs _ _
          _ = gauge K (Φ x) + gauge K (Ψ x) := by rw [gauge_neg hsym]
    have hdiffmem : MemLp (fun x => Φ x - Ψ x) 2 (Submission.GaussianChaos.μ N) := hΦ.sub hΨmem
    have hbd : Real.sqrt (∫ x, (gauge K (Φ x - Ψ x)) ^ 2 ∂Submission.GaussianChaos.μ N) ≤ η := by
      have hInt1 : Integrable (fun x : EuclideanSpace ℝ (Fin N) => (gauge K (Φ x - Ψ x)) ^ 2)
          (Submission.GaussianChaos.μ N) :=
        (memLp_two_iff_integrable_sq hdiffg.aestronglyMeasurable).mp hdiffg
      have hInt2 : Integrable (fun x : EuclideanSpace ℝ (Fin N) => cu ^ 2 * ‖Φ x - Ψ x‖ ^ 2)
          (Submission.GaussianChaos.μ N) :=
        ((memLp_two_iff_integrable_sq hdiffmem.norm.aestronglyMeasurable).mp
          hdiffmem.norm).const_mul _
      have hmono := integral_mono hInt1 hInt2 (fun x => by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (gauge_nonneg _) (hcu_b (Φ x - Ψ x)) 2)
      have h3 : (∫ x, cu ^ 2 * ‖Φ x - Ψ x‖ ^ 2 ∂Submission.GaussianChaos.μ N)
          = cu ^ 2 * ∫ x, ‖Φ x - Ψ x‖ ^ 2 ∂Submission.GaussianChaos.μ N :=
        integral_const_mul _ _
      rw [h3] at hmono
      have h5 : Real.sqrt (∫ x, ‖Φ x - Ψ x‖ ^ 2 ∂Submission.GaussianChaos.μ N)
          < η / (cu + 1) := Real.sqrt_lt' (by positivity) |>.mpr hsC'
      have h4 : Real.sqrt (cu ^ 2 * ∫ x, ‖Φ x - Ψ x‖ ^ 2 ∂Submission.GaussianChaos.μ N) ≤ η := by
        rw [Real.sqrt_mul (sq_nonneg cu), Real.sqrt_sq hcu.le]
        calc cu * Real.sqrt (∫ x, ‖Φ x - Ψ x‖ ^ 2 ∂Submission.GaussianChaos.μ N)
            ≤ cu * (η / (cu + 1)) := mul_le_mul_of_nonneg_left h5.le hcu.le
          _ ≤ η := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity : (0:ℝ) < cu + 1)]
              nlinarith [hcu, hηpos]
      exact le_trans (Real.sqrt_le_sqrt hmono) h4
    have hadd : Q1 Φ = Q1 Ψ + Q1 (Φ - Ψ) := by
      have h := Q1_add Ψ (Φ - Ψ) (fun i => integrable_coord_smul hΨmem i)
        (fun i => integrable_coord_smul hdiffmem i)
      rwa [show (Ψ + (Φ - Ψ)) = Φ from funext fun x => by
        simp only [Pi.add_apply, Pi.sub_apply]; abel] at h
    have hf : MemLp (fun x => gauge K (Q1 Ψ x)) 2 (Submission.GaussianChaos.μ N) :=
      memLp_gauge_Q1 K hcvx hbal h0 Ψ
    have hk : MemLp (fun x => gauge K (Q1 (Φ - Ψ) x)) 2 (Submission.GaussianChaos.μ N) :=
      memLp_gauge_Q1 K hcvx hbal h0 (Φ - Ψ)
    have hMink : Real.sqrt (∫ x, (gauge K (Q1 Φ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
        ≤ Real.sqrt (∫ x, (gauge K (Q1 Ψ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
          + Real.sqrt (∫ x, (gauge K (Q1 (Φ - Ψ) x)) ^ 2 ∂Submission.GaussianChaos.μ N) := by
      have h := sqrt_integral_add_le (f := fun x => gauge K (Q1 Ψ x))
        (g := fun x => gauge K (Q1 (Φ - Ψ) x)) hf hk
      refine (Real.sqrt_le_sqrt ?_).trans h
      have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin N) =>
          (gauge K (Q1 Ψ x) + gauge K (Q1 (Φ - Ψ) x)) ^ 2) (Submission.GaussianChaos.μ N) :=
        (memLp_two_iff_integrable_sq (hf.add hk).aestronglyMeasurable).mp (hf.add hk)
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hInt
        (Filter.Eventually.of_forall fun x => ?_)
      show gauge K (Q1 Φ x) ^ 2 ≤ (gauge K (Q1 Ψ x) + gauge K (Q1 (Φ - Ψ) x)) ^ 2
      rw [show Q1 Φ x = (Q1 Ψ + Q1 (Φ - Ψ)) x from congrFun hadd x]
      refine pow_le_pow_left₀ (gauge_nonneg _) ?_ 2
      exact gauge_add_le hcvx habs _ _
    have hHerm2 : Real.sqrt (∫ x, (gauge K (Q1 Ψ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
        ≤ C0 * Real.sqrt (∫ x, (gauge K (Ψ x)) ^ 2 ∂Submission.GaussianChaos.μ N) := by
      rw [hΨ]; exact hHerm s C'
    have hcru : Real.sqrt (∫ x, (gauge K (Q1 (Φ - Ψ) x)) ^ 2 ∂Submission.GaussianChaos.μ N)
        ≤ (N : ℝ) * Real.sqrt (∫ x, (gauge K (Φ x - Ψ x)) ^ 2 ∂Submission.GaussianChaos.μ N) := by
      have h := Q1_crude K hcvx habs hbdd hbal hcpt h0 (Φ - Ψ)
        hdiffmem.aestronglyMeasurable hdiffg
      calc Real.sqrt (∫ x, (gauge K (Q1 (Φ - Ψ) x)) ^ 2 ∂Submission.GaussianChaos.μ N)
          ≤ Real.sqrt ((N : ℝ) ^ 2 * ∫ x, (gauge K (Φ x - Ψ x)) ^ 2
              ∂Submission.GaussianChaos.μ N) := Real.sqrt_le_sqrt h
        _ = (N : ℝ) * Real.sqrt (∫ x, (gauge K (Φ x - Ψ x)) ^ 2
              ∂Submission.GaussianChaos.μ N) := by
            rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (N:ℝ)^2), Real.sqrt_sq (by positivity)]
    have hΨsq : Real.sqrt (∫ x, (gauge K (Ψ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
        ≤ Real.sqrt A + η := by
      have hpt : (∫ x, (gauge K (Ψ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
          ≤ ∫ x, (gauge K (Φ x) + gauge K (Φ x - Ψ x)) ^ 2 ∂Submission.GaussianChaos.μ N := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) ?_
          (Filter.Eventually.of_forall fun x => ?_)
        · exact (memLp_two_iff_integrable_sq (hΦg.add hdiffg).aestronglyMeasurable).mp
            (hΦg.add hdiffg)
        · refine pow_le_pow_left₀ (gauge_nonneg _) ?_ 2
          have hsym : ∀ z ∈ K, -z ∈ K := by
            intro z hz
            have : -z ∈ (-K : Set (EuclideanSpace ℝ (Fin n))) := by simpa using hz
            rwa [hKsymm] at this
          have hdec : Ψ x = Φ x + -(Φ x - Ψ x) := by rw [← sub_eq_add_neg, sub_sub_cancel]
          rw [show gauge K (Ψ x) = gauge K (Φ x + -(Φ x - Ψ x)) from congrArg (gauge K) hdec]
          refine (gauge_add_le hcvx habs (Φ x) (-(Φ x - Ψ x))).trans_eq ?_
          show gauge K (Φ x) + gauge K (-(Φ x - Ψ x)) = gauge K (Φ x) + gauge K (Φ x - Ψ x)
          rw [gauge_neg hsym]
      have h2 := sqrt_integral_add_le (f := fun x => gauge K (Φ x))
        (g := fun x => gauge K (Φ x - Ψ x)) hΦg hdiffg
      refine (Real.sqrt_le_sqrt hpt).trans ?_
      rw [show (∫ x, (gauge K (Φ x) + gauge K (Φ x - Ψ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
          = ∫ x, ((fun x : EuclideanSpace ℝ (Fin N) =>
              gauge K (Φ x) + gauge K (Φ x - Ψ x)) x) ^ 2 ∂Submission.GaussianChaos.μ N from rfl]
      refine h2.trans ?_
      rw [show Real.sqrt (∫ x, (gauge K (Φ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
          = Real.sqrt A from by rw [hA]]
      exact add_le_add le_rfl hbd
    calc Real.sqrt (∫ x, (gauge K (Q1 Φ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
        ≤ Real.sqrt (∫ x, (gauge K (Q1 Ψ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
          + Real.sqrt (∫ x, (gauge K (Q1 (Φ - Ψ) x)) ^ 2 ∂Submission.GaussianChaos.μ N) := hMink
      _ ≤ C0 * Real.sqrt (∫ x, (gauge K (Ψ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
            + (N : ℝ) * Real.sqrt (∫ x, (gauge K (Φ x - Ψ x)) ^ 2
                ∂Submission.GaussianChaos.μ N) := add_le_add hHerm2 hcru
      _ ≤ C0 * (Real.sqrt A + η) + (N : ℝ) * η :=
          add_le_add (mul_le_mul_of_nonneg_left hΨsq hC0nn)
            (mul_le_mul_of_nonneg_left hbd hCnon)
      _ ≤ C0 * Real.sqrt A + δ := by nlinarith [hηle, hC0nn, hCnon]
  calc (∫ x, (gauge K (Q1 Φ x)) ^ 2 ∂Submission.GaussianChaos.μ N)
      = (Real.sqrt (∫ x, (gauge K (Q1 Φ x)) ^ 2 ∂Submission.GaussianChaos.μ N)) ^ 2 :=
        (Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)).symm
    _ ≤ (C0 * Real.sqrt A) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hfinal 2
    _ = C0 ^ 2 * A := by rw [mul_pow, Real.sq_sqrt hAnn]
    _ = (4 * (1 + Real.log d / Real.log 2)) ^ 2 *
          ∫ x, (gauge K (Φ x)) ^ 2 ∂Submission.GaussianChaos.μ N := by rw [hC0, hA]


end

end Submission.KConvexL2
