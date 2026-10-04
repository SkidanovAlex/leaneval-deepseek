import Mathlib
import Submission.Work.Diff.L.Defs
import Submission.Work.Diff.L.Stmt
import Submission.Work.Diff.Alg.PA.Defs
import Submission.Work.Diff.L.exists_isONPair_scalAlg_div_le_secK
import Submission.Work.Diff.L.exists_isONPair_secK_le_scalAlg_div

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.L

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Finset

set_option linter.unusedVariables false

/-- Arithmetic core of the lower bound: if `ρ ≤ x`, `x / D ≤ k`, `δ * k ≤ y` and `0 < δ, D`,
then `δ * ρ / D ≤ y`. -/
private lemma lower_arith {δ ρ x k y D : ℝ} (hδ : 0 < δ) (hD : 0 < D)
    (hρ : ρ ≤ x) (hk : x / D ≤ k) (h : δ * k ≤ y) : δ * ρ / D ≤ y := by
  rw [div_le_iff₀ hD]
  have h3 : δ * ρ ≤ δ * x := mul_le_mul_of_nonneg_left hρ hδ.le
  have ha : δ * (x / D) ≤ δ * k := mul_le_mul_of_nonneg_left hk hδ.le
  have h1 : δ * x ≤ δ * k * D := by
    rw [show δ * x = δ * (x / D) * D by rw [mul_assoc, div_mul_cancel₀ x hD.ne']]
    exact mul_le_mul_of_nonneg_right ha hD.le
  have h4 : δ * k * D ≤ y * D := mul_le_mul_of_nonneg_right h hD.le
  linarith

/-- Arithmetic core of the upper bound: if `x ≤ SA`, `k ≤ x / D`, `δ * a ≤ k` and `0 < δ, D`,
then `a ≤ SA / (δ * D)`. -/
private lemma upper_arith {δ SA x k a D : ℝ} (hδ : 0 < δ) (hD : 0 < D)
    (hSA : x ≤ SA) (hk : k ≤ x / D) (h : δ * a ≤ k) : a ≤ SA / (δ * D) := by
  rw [le_div_iff₀ (mul_pos hδ hD)]
  have h2 : δ * a ≤ SA / D :=
    le_trans h (le_trans hk (div_le_div_of_nonneg_right hSA hD.le))
  have h1 : δ * a * D ≤ SA := (le_div_iff₀ hD).mp h2
  nlinarith [h1]

/-- **Two-sided pinching bounds in an orthonormal frame.**  If the curvature of `g` lies in a pinching
set `F` (`CurvIn g F`), and every element of `F` with scalar curvature `≥ ρ` is `δ`-pinched, then at
every point `x` with `ρ ≤ scalAt g x` the sectional curvatures of the frame tensor
`rmFrame g x (onFrame g x)` are bounded below by `δ ρ/(n(n-1))`, and if moreover `scalAt g x ≤ SA` they
are bounded above by `SA/(δ n(n-1))`.

This is pure algebra on the array `R := rmFrame g x (onFrame g x) ∈ F` (so `IsAlgCurv R` comes from
`IsPinchingSet.1`, the scalar curvature of `R` is `scalAt g x` by definition, and `δ`-pinching
of `R` comes from `hρ'`): `scalAlg R = 2 ∑_{i<j} R i j i j`, so `max_{i<j} R i j i j ≥ scalAlg R/(n(n-1))`
and `min_{i<j} R i j i j ≤ scalAlg R/(n(n-1))`; then apply `IsPinchedAlg δ R`
(`δ · secK R σ' ≤ secK R σ` for all orthonormal pairs) with `σ` the given pair and `σ'` the maximal
(resp. minimal) pair of standard basis vectors `stdB n i`, using `secK_stdB : secK R (stdB i) (stdB j) = R i j i j`
and `isONPair_stdB` from `Submission.Work.Diff.Alg.PA.Defs`.  (The trace identity
`scalAlg R = 2 * ∑_{i<j} R i j i j` for `IsAlgCurv R` is a short `Finset` computation from
antisymmetry in the first pair and the pair symmetry `R k l i j = R i j k l`.) -/
theorem rmFrame_pinched_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [T2Space M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (g : Submission.Diff.SMet I M) (F : Set (Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)))
    (hF : Submission.Diff.Alg.IsPinchingSet F) (hCurv : Submission.Diff.CurvIn g F)
    {δ ρ SA : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (hρ' : ∀ R ∈ F, ρ ≤ Submission.Diff.Alg.scalAlg R →
      Submission.Diff.Alg.IsPinchedAlg δ R) :
    (∀ x : M, ρ ≤ Submission.Diff.scalAt g x →
      ∀ u v : Fin (Module.finrank ℝ E) → ℝ, Submission.Diff.Alg.IsONPair u v →
      δ * ρ / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1))
        ≤ Submission.Diff.Alg.secK
            (Submission.Diff.rmFrame g x (Submission.Diff.onFrame g x)) u v) ∧
    (∀ x : M, ρ ≤ Submission.Diff.scalAt g x → Submission.Diff.scalAt g x ≤ SA →
      ∀ u v : Fin (Module.finrank ℝ E) → ℝ, Submission.Diff.Alg.IsONPair u v →
      Submission.Diff.Alg.secK
          (Submission.Diff.rmFrame g x (Submission.Diff.onFrame g x)) u v
        ≤ SA / (δ * ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)))) := by
  have hD : 0 < (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) := by
    have h2 : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
    nlinarith
  constructor
  · -- lower bound: apply `IsPinchedAlg` to the extremal plane of maximal sectional curvature
    intro x hx u v huv
    have he : IsONFrame g x (onFrame g x) := onFrame_isONFrame g x
    have hmem : rmFrame g x (onFrame g x) ∈ F := hCurv x (onFrame g x) he
    have hAlg : IsAlgCurv (rmFrame g x (onFrame g x)) := hF.1.2.2.1 _ hmem
    have hpin : IsPinchedAlg δ (rmFrame g x (onFrame g x)) := hρ' _ hmem hx
    obtain ⟨u', v', huv', hmax⟩ := exists_isONPair_scalAlg_div_le_secK hdim hAlg
    have h1 : δ * secK (rmFrame g x (onFrame g x)) u' v'
        ≤ secK (rmFrame g x (onFrame g x)) u v := hpin u v u' v' huv huv'
    exact lower_arith hδ hD hx hmax h1
  · -- upper bound: apply `IsPinchedAlg` to the extremal plane of minimal sectional curvature
    intro x hx hxSA u v huv
    have he : IsONFrame g x (onFrame g x) := onFrame_isONFrame g x
    have hmem : rmFrame g x (onFrame g x) ∈ F := hCurv x (onFrame g x) he
    have hAlg : IsAlgCurv (rmFrame g x (onFrame g x)) := hF.1.2.2.1 _ hmem
    have hpin : IsPinchedAlg δ (rmFrame g x (onFrame g x)) := hρ' _ hmem hx
    obtain ⟨u', v', huv', hmin⟩ := exists_isONPair_secK_le_scalAlg_div hdim hAlg
    have h1 : δ * secK (rmFrame g x (onFrame g x)) u v
        ≤ secK (rmFrame g x (onFrame g x)) u' v' := hpin u' v' u v huv' huv
    exact upper_arith hδ hD hxSA hmin h1

end Work.Diff.L
