import Submission.GapEstimate

/-!
# The quadratic gap estimate

This is the `O(s ^ 2)` companion of `Submission.GapEstimate.riemannianEDist_le_cube_of_gap`: two
chart curves which agree in position *and* velocity at `0` are at distance `O(s ^ 2)`.  (The
third-order estimate needs in addition that the *accelerations* agree.)  The estimate compares the
flow of a vector field with the geodesic ray in the same direction: both start at the same point
with the same velocity, so their distance is `O(s ^ 2)`.

Main results:

* `riemannianEDist_le_sq_of_gap`: the abstract form (an additive error `g` with `g 0 = 0`,
  `g' 0 = 0`);
* `riemannianEDist_le_sq_of_same_jet`: two chart curves with the same value and the same first
  derivative at `0` are at distance `O(s ^ 2)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.Length
open Submission.ChartBounds
open Submission.BonnetMyers
open Submission.ChartConnection
open Submission.HopfRinow

namespace Submission.GapEstimate

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

/-- **The quadratic gap estimate.**  If `g` vanishes at `0` together with its first derivative, and
its first three derivatives are controlled on `Ioo (-ρ) ρ`, then the Riemannian distance between
the chart points `V s + g s` and `V s` is `O(s ^ 2)`, with the explicit constant
`sqrt Λ * (M₀ / 6 * ρ + norm (g'' 0) / 2)`. -/
theorem riemannianEDist_le_sq_of_gap {x₀ : M} {V g g' g'' g''' : ℝ → E} {K : Set E}
    {c : E} {r Λ M₀ ρ : ℝ} (hK : K = Metric.ball c r) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ)
    (hg0 : g 0 = 0) (hg'0 : g' 0 = 0)
    (h1 : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt g (g' s) s)
    (h2 : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt g' (g'' s) s)
    (h3 : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt g'' (g''' s) s)
    (hbd : ∀ s ∈ Ioo (-ρ) ρ, ‖g''' s‖ ≤ M₀)
    (hbound : ∀ z ∈ K, ∀ a : E,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm z) a a ≤ Λ * ‖a‖ ^ 2)
    (hKt : ∀ z ∈ K, z ∈ (extChartAt I x₀).target)
    (hVin : ∀ s ∈ Ioo (-ρ) ρ, V s ∈ K) (hUVin : ∀ s ∈ Ioo (-ρ) ρ, V s + g s ∈ K) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ s : ℝ, |s| < ρ' →
      Manifold.riemannianEDist I ((extChartAt I x₀).symm (V s + g s)) ((extChartAt I x₀).symm (V s))
        ≤ ENNReal.ofReal (Real.sqrt Λ * ((M₀ / 6 * ρ + ‖g'' 0‖ / 2) * |s| ^ 2)) := by
  refine ⟨ρ, hρ, le_rfl, fun s hs => ?_⟩
  have hsI : s ∈ Ioo (-ρ) ρ := ⟨by linarith [abs_lt.mp hs], by linarith [abs_lt.mp hs]⟩
  have hsρ : |s| < ρ := hs
  have hMnn : 0 ≤ M₀ := le_trans (norm_nonneg _) (hbd 0 ⟨by linarith, by linarith⟩)
  -- the norm bound on the difference
  have hgnorm : ‖g s‖ ≤ (M₀ / 6 * ρ + ‖g'' 0‖ / 2) * |s| ^ 2 := by
    have h := Commons.Analysis.Calculus.taylor_second_order_cubic_rem
      (f := g) (f' := g') (f'' := g'') (f''' := g''') (M := M₀) (r := ρ) hρ h1 h2 h3 hbd s hsI
    simp only [hg0, hg'0, smul_zero, sub_zero] at h
    have hsplit : g s = (g s - (s ^ 2 / 2) • g'' 0) + (s ^ 2 / 2) • g'' 0 := by abel
    have h1' : ‖g s‖ ≤ M₀ / 6 * |s| ^ 3 + ‖(s ^ 2 / 2) • g'' 0‖ := by
      calc ‖g s‖ = ‖(g s - (s ^ 2 / 2) • g'' 0) + (s ^ 2 / 2) • g'' 0‖ := congrArg norm hsplit
        _ ≤ ‖g s - (s ^ 2 / 2) • g'' 0‖ + ‖(s ^ 2 / 2) • g'' 0‖ := norm_add_le _ _
        _ ≤ M₀ / 6 * |s| ^ 3 + ‖(s ^ 2 / 2) • g'' 0‖ := add_le_add h le_rfl
    have h2' : ‖(s ^ 2 / 2) • g'' 0‖ = |s| ^ 2 / 2 * ‖g'' 0‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ s ^ 2 / 2), sq_abs]
    have h3' : M₀ / 6 * |s| ^ 3 ≤ M₀ / 6 * ρ * |s| ^ 2 := by
      have hsq : 0 ≤ |s| ^ 2 := by positivity
      have hcube : |s| ^ 3 ≤ ρ * |s| ^ 2 := by
        rw [show |s| ^ 3 = |s| * |s| ^ 2 by ring]
        exact mul_le_mul_of_nonneg_right hsρ.le hsq
      calc M₀ / 6 * |s| ^ 3 ≤ M₀ / 6 * (ρ * |s| ^ 2) :=
            mul_le_mul_of_nonneg_left hcube (by linarith)
        _ = M₀ / 6 * ρ * |s| ^ 2 := by ring
    calc ‖g s‖ ≤ M₀ / 6 * |s| ^ 3 + |s| ^ 2 / 2 * ‖g'' 0‖ := by rw [← h2']; exact h1'
      _ ≤ M₀ / 6 * ρ * |s| ^ 2 + |s| ^ 2 / 2 * ‖g'' 0‖ := add_le_add h3' le_rfl
      _ = (M₀ / 6 * ρ + ‖g'' 0‖ / 2) * |s| ^ 2 := by ring
  -- the segment between the two points stays in the ball
  have hconv : ∀ t ∈ Icc (0:ℝ) 1, V s + g s + t • (V s - (V s + g s)) ∈ K := by
    intro t ht
    rw [hK]
    exact (convex_ball c r).add_smul_sub_mem (hK ▸ hUVin s hsI) (hK ▸ hVin s hsI) ht
  have h := riemannianEDist_chart_le (x₀ := x₀) (K := K) (Λ := Λ) hΛ hbound hKt
    (hUVin s hsI) hconv
  refine h.trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.sqrt Λ * ‖V s - (V s + g s)‖
        ≤ Real.sqrt Λ * ((M₀ / 6 * ρ + ‖g'' 0‖ / 2) * |s| ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg Λ)
        rw [show V s - (V s + g s) = -g s by abel, norm_neg]
        exact hgnorm
    _ = Real.sqrt Λ * ((M₀ / 6 * ρ + ‖g'' 0‖ / 2) * |s| ^ 2) := rfl

/-- **Two chart curves with the same 2-jet are `O(s ^ 2)` apart.**  If `r₁` and `r₂` are `C³` chart
curves (with the derivative functions `Aᵢ`, `Bᵢ` supplied explicitly) which have the same value and
the same first derivative at `0`, and the third derivatives differ by at most `M₀` on `Ioo (-ρ) ρ`,
then the Riemannian distance of the corresponding points is `O(s ^ 2)`. -/
theorem riemannianEDist_le_sq_of_same_jet {x₀ : M} {r₁ r₂ : ℝ → E}
    {A₁ A₂ A₃ B₁ B₂ B₃ : ℝ → E} {K : Set E} {c : E} {r Λ M₀ ρ : ℝ}
    (hK : K = Metric.ball c r) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ)
    (hval : r₁ 0 = r₂ 0) (hvel : A₁ 0 = B₁ 0)
    (h1a : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt r₁ (A₁ s) s)
    (h2a : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt A₁ (A₂ s) s)
    (h3a : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt A₂ (A₃ s) s)
    (h1b : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt r₂ (B₁ s) s)
    (h2b : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt B₁ (B₂ s) s)
    (h3b : ∀ s ∈ Ioo (-ρ) ρ, HasDerivAt B₂ (B₃ s) s)
    (hbd : ∀ s ∈ Ioo (-ρ) ρ, ‖A₃ s - B₃ s‖ ≤ M₀)
    (hbound : ∀ z ∈ K, ∀ a : E,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm z) a a ≤ Λ * ‖a‖ ^ 2)
    (hKt : ∀ z ∈ K, z ∈ (extChartAt I x₀).target)
    (hin₁ : ∀ s ∈ Ioo (-ρ) ρ, r₁ s ∈ K) (hin₂ : ∀ s ∈ Ioo (-ρ) ρ, r₂ s ∈ K) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ s : ℝ, |s| < ρ' →
      Manifold.riemannianEDist I ((extChartAt I x₀).symm (r₁ s)) ((extChartAt I x₀).symm (r₂ s))
        ≤ ENNReal.ofReal (Real.sqrt Λ *
            ((M₀ / 6 * ρ + ‖A₂ 0 - B₂ 0‖ / 2) * |s| ^ 2)) := by
  -- apply the gap estimate to `V := r₂` and `g := r₁ - r₂`
  have hg0 : (fun s : ℝ => r₁ s - r₂ s) 0 = 0 := by
    simp only [hval, sub_self]
  have hg'0 : (fun s : ℝ => A₁ s - B₁ s) 0 = 0 := by
    simp only [hvel, sub_self]
  obtain ⟨ρ', hρ'pos, hρ'le, hbound'⟩ := riemannianEDist_le_sq_of_gap (x₀ := x₀) (K := K)
    (V := r₂) (g := fun s : ℝ => r₁ s - r₂ s) (g' := fun s : ℝ => A₁ s - B₁ s)
    (g'' := fun s : ℝ => A₂ s - B₂ s) (g''' := fun s : ℝ => A₃ s - B₃ s)
    (c := c) (r := r) (Λ := Λ) (M₀ := M₀) (ρ := ρ) hK hΛ hρ hg0 hg'0
    (fun s hs => (h1a s hs).sub (h1b s hs))
    (fun s hs => (h2a s hs).sub (h2b s hs))
    (fun s hs => (h3a s hs).sub (h3b s hs))
    (fun s hs => by
      have := hbd s hs
      simpa only [Pi.sub_apply] using this)
    hbound hKt
    (fun s hs => hin₂ s hs)
    (fun s hs => by
      have h : r₂ s + (r₁ s - r₂ s) = r₁ s := by abel
      rw [h]; exact hin₁ s hs)
  refine ⟨ρ', hρ'pos, hρ'le, fun s hs => ?_⟩
  have h := hbound' s hs
  have harg : r₂ s + (r₁ s - r₂ s) = r₁ s := by abel
  rw [harg] at h
  simpa only [Pi.sub_apply] using h

end

end Submission.GapEstimate
