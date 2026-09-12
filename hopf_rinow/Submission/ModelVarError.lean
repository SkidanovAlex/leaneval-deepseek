import Submission.Model
import Submission.ModelCore
import Mathlib

/-!
# Uniform first-order Taylor error for the geodesic vector field along a compact trajectory

Task: prove the final theorem `odeField_taylor_error` by real mathematics.

## Statement (in words)

Let `V := odeField g : E × E → E × E` be the (autonomous, C¹) geodesic vector field of a smooth
invertible metric family `g`, and let `z : ℝ → E × E` be continuous on the compact interval
`Icc (-T) T`.  Then the derivative error of `V` is *uniformly* small along the trajectory:

    ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Icc (-T) T, ∀ y ∈ closedBall (z t) δ,
      ‖V y - V (z t) - (fderiv ℝ V (z t)) (y - z t)‖ ≤ ε * ‖y - z t‖

## Why true

`V` is C¹ everywhere (`Submission.ModelCore.odeField_contDiffAt g hg hinv` gives
`ContDiffAt ℝ 1 V x` for every `x`).  In particular the Fréchet derivative
`x ↦ fderiv ℝ V x` is continuous, so its oscillation around the (compact) trajectory image
`K = z '' Icc (-T) T` is uniform (classical: a continuous function has vanishing oscillation,
uniformly over a compact family of base points -- proved below by a subsequence argument).
Applying the mean-value inequality to the affine error function on each ball `closedBall x δ`
(`Convex.norm_image_sub_le_of_norm_fderiv_le'`) then yields the first-order Taylor estimate
uniformly in the base point `x ∈ K`.
-/

open ContinuousLinearMap Filter
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

open scoped ContDiff

/-- Auxiliary uniform-continuity estimate: if `W` is continuous and `K` is compact, then the
oscillation `‖W q - W x‖` of `W` around any base point `x ∈ K` tends to zero uniformly with the
distance `‖q - x‖` (the point `q` itself may lie anywhere in the ambient space). -/
lemma uniform_osc {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : X → Z} (hW : Continuous W) {K : Set X}
    (hK : IsCompact K) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ q, q ∈ closedBall x δ → ‖W q - W x‖ ≤ ε := by
  intro ε hε
  by_contra h
  push_neg at h
  have hseq : ∀ n : ℕ, ∃ x ∈ K, ∃ q : X,
      q ∈ closedBall x ((1 : ℝ) / (n + 1)) ∧ ε < ‖W q - W x‖ := by
    intro n
    exact h ((1 : ℝ) / (n + 1)) (by positivity)
  choose xn hxK qn hq using hseq
  rcases hK.tendsto_subseq hxK with ⟨a, haK, φ, hφmono, hφxlim⟩
  have hqin : ∀ n : ℕ, qn n ∈ closedBall (xn n) ((1 : ℝ) / (n + 1)) := fun n => (hq n).1
  have hbad : ∀ n : ℕ, ε < ‖W (qn n) - W (xn n)‖ := fun n => (hq n).2
  have hWa : ContinuousAt W a := hW.continuousAt
  have hcont : ∀ ε' > 0, ∃ η > 0, ∀ q, ‖q - a‖ < η → ‖W q - W a‖ < ε' := by
    intro ε' hε'
    rcases (Metric.continuousAt_iff.mp hWa) ε' hε' with ⟨η, hη, hh⟩
    refine ⟨η, hη, ?_⟩
    intro q hq
    have hda : dist q a < η := by simpa [dist_eq_norm] using hq
    have hdW : dist (W q) (W a) < ε' := hh hda
    simpa [dist_eq_norm] using hdW
  rcases hcont (ε / 2) (by positivity) with ⟨η, hηpos, hηbd⟩
  have hxev : ∀ᶠ k in atTop, ‖xn (φ k) - a‖ < η / 2 := by
    have hlim := (Metric.tendsto_nhds.mp hφxlim) (η / 2) (by positivity)
    filter_upwards [hlim] with k hk
    simpa [dist_eq_norm] using hk
  have hge : ∀ k : ℕ, k ≤ φ k := by
    intro k
    calc
      k ≤ k + φ 0 := by omega
      _ ≤ φ (k + 0) := hφmono.add_le_nat k 0
      _ = φ k := by simp
  have hrev : ∀ᶠ k in atTop, (1 : ℝ) / (φ k + 1) < η / 2 := by
    have hlim : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) := by
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hhalf := (Metric.tendsto_nhds.mp hlim) (η / 2) (by positivity)
    filter_upwards [hhalf] with k hk
    have hb0 : (1 : ℝ) / ((k : ℝ) + 1) < η / 2 := by
      have hle : (1 : ℝ) / ((k : ℝ) + 1) ≤ |(1 : ℝ) / ((k : ℝ) + 1)| := le_abs_self _
      have hlt : |(1 : ℝ) / ((k : ℝ) + 1)| < η / 2 := by
        simpa [dist_eq_norm, Real.norm_eq_abs] using hk
      exact lt_of_le_of_lt hle hlt
    have hle2 : (1 : ℝ) / (φ k + 1) ≤ (1 : ℝ) / (k + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have hkc : (k : ℝ) ≤ φ k := by exact_mod_cast hge k
        linarith
    exact lt_of_le_of_lt hle2 hb0
  have hqev : ∀ᶠ k in atTop, ‖qn (φ k) - a‖ < η := by
    filter_upwards [hxev, hrev] with k hx hrt
    have hqin' : qn (φ k) ∈ closedBall (xn (φ k)) ((1 : ℝ) / (φ k + 1)) := hqin (φ k)
    have hqdist : ‖qn (φ k) - xn (φ k)‖ ≤ (1 : ℝ) / (φ k + 1) := by
      simpa [dist_eq_norm] using hqin'
    have htri : dist (qn (φ k)) a ≤ dist (qn (φ k)) (xn (φ k)) + dist (xn (φ k)) a :=
      dist_triangle (qn (φ k)) (xn (φ k)) a
    have hle : ‖qn (φ k) - a‖ ≤ ‖qn (φ k) - xn (φ k)‖ + ‖xn (φ k) - a‖ := by
      simpa [dist_eq_norm] using htri
    nlinarith
  have hWev : ∀ᶠ k in atTop,
      ‖W (qn (φ k)) - W a‖ < ε / 2 ∧ ‖W (xn (φ k)) - W a‖ < ε / 2 := by
    filter_upwards [hqev, hxev] with k hq hx
    constructor
    · exact hηbd (qn (φ k)) hq
    · exact hηbd (xn (φ k)) (lt_trans hx (by linarith))
  rcases (eventually_atTop.1 hWev) with ⟨N, hN⟩
  have hNW := hN N (le_rfl)
  have hWbd1 : ‖W (qn (φ N)) - W a‖ < ε / 2 := hNW.1
  have hWbd2 : ‖W (xn (φ N)) - W a‖ < ε / 2 := hNW.2
  have htri : dist (W (qn (φ N))) (W (xn (φ N))) ≤
      dist (W (qn (φ N))) (W a) + dist (W a) (W (xn (φ N))) :=
    dist_triangle (W (qn (φ N))) (W a) (W (xn (φ N)))
  have hmain : ‖W (qn (φ N)) - W (xn (φ N))‖ ≤
      ‖W (qn (φ N)) - W a‖ + ‖W (xn (φ N)) - W a‖ := by
    simpa [dist_eq_norm, norm_sub_rev] using htri
  have hbadN : ε < ‖W (qn (φ N)) - W (xn (φ N))‖ := hbad (φ N)
  nlinarith

/-- First-order Taylor error of a C¹ map `V`, uniform over a compact family of base points:
for every `ε > 0` there is a `δ > 0` such that for all `x ∈ K` and all `y` in the ball of radius
`δ` around `x`, `‖V y - V x - (fderiv ℝ V x) (y - x)‖ ≤ ε * ‖y - x‖`. -/
lemma uniform_taylor_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : X → X) (hV : ContDiff ℝ 1 V) {K : Set X} (hK : IsCompact K) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ K, ∀ y, y ∈ closedBall x δ →
      ‖V y - V x - fderiv ℝ V x (y - x)‖ ≤ ε * ‖y - x‖ := by
  intro ε hε
  have hfdcont : Continuous (fderiv ℝ V) := hV.continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  rcases uniform_osc (W := fderiv ℝ V) hfdcont hK ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x hx y hy
  have hdiff : ∀ q ∈ closedBall x δ, DifferentiableAt ℝ V q := by
    intro q hq
    exact (hV.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt
  have hbnd : ∀ q ∈ closedBall x δ, ‖fderiv ℝ V q - fderiv ℝ V x‖ ≤ ε := fun q hq => hδ x hx q hq
  exact Convex.norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ) (f := V) (s := closedBall x δ)
    (φ := fderiv ℝ V x) hdiff hbnd (convex_closedBall x δ) (by simp [hδpos.le]) hy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- The geodesic vector field has a uniform first-order Taylor error along a compact continuous
trajectory. -/
theorem odeField_taylor_error (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {T : ℝ} (hT : 0 < T) {c vel : ℝ → E}
    (hc : ContinuousOn c (Icc (-T) T)) (hv : ContinuousOn vel (Icc (-T) T)) :
    ∀ ε > 0, ∃ δ > 0,
      ∀ t ∈ Icc (-T) T, ∀ y : E × E, y ∈ closedBall (c t, vel t) δ →
        ‖odeField g y - odeField g (c t, vel t)
           - (fderiv ℝ (odeField g) (c t, vel t)) (y - (c t, vel t))‖ ≤ ε * ‖y - (c t, vel t)‖ := by
  let z : ℝ → E × E := fun t => (c t, vel t)
  have hV1 : ContDiff ℝ 1 (odeField g) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rcases p with ⟨x, v⟩
    exact odeField_contDiffAt g hg hinv x v
  have hz : ContinuousOn z (Icc (-T) T) := by
    simpa [z] using hc.prodMk hv
  have hK : IsCompact (z '' (Icc (-T) T)) := isCompact_Icc.image_of_continuousOn hz
  intro ε hε
  rcases uniform_taylor_bound (X := E × E) (V := odeField g) hV1 hK ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro t ht y hy
  have hxK : z t ∈ z '' (Icc (-T) T) := ⟨t, ht, rfl⟩
  exact hδ (z t) hxK y hy

end

end Submission.Model
