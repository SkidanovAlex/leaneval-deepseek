import Mathlib
import Submission.Work.Diff.EXT.reactBase
import Submission.Work.Diff.EXT.evX.MonBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.Mono

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem MonoD_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hrm : ∀ (X Y : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)) (Mx My : ℝ), 0 ≤ Mx → 0 ≤ My →
      (∀ i j k l, |X i j k l| ≤ Mx) → (∀ i j k l, |Y i j k l| ≤ My) →
      ∀ i j k l, |Work.Diff.EXT.rmSym X Y i j k l| ≤ C₀ * Mx * My)
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (N a b : ℕ) (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (hON : Submission.Diff.IsONFrame g x (fun i => e i x))
    (F : Fin N → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F r)) :
    |Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e F x|
      ≤ (C₀ * ((Module.finrank ℝ E : ℝ) ^ 4 + 1))
        * (Real.sqrt (Work.Diff.EXT.curvNormK g x a)
            * ∏ r : Fin a, Real.sqrt (g.inner x (F (d₁ r) x) (F (d₁ r) x)))
        * (Real.sqrt (Work.Diff.EXT.curvNormK g x b)
            * ∏ r : Fin b, Real.sqrt (g.inner x (F (d₂ r) x) (F (d₂ r) x)))
        * (∏ t : Fin 4, Real.sqrt (g.inner x (F (s t) x) (F (s t) x))) := by
  -- The analytic core (componentwise `rmSym` bound + Hilbert--Schmidt entry bound for the tower
  -- array + Cauchy--Schwarz for the four pairings) is `Work.Diff.EXT.evX.MonBound_MonoD_boundV`.
  have hmain := Work.Diff.EXT.evX.MonBound_MonoD_boundV (I := I) (M := M) C₀ hC₀ hrm hLC g x
    N a b d₁ d₂ s e he hON F hF
  refine le_trans hmain ?_
  -- It remains only to relax the constant `C₀ * (finrank ℝ E)^4` to `C₀ * ((finrank ℝ E)^4 + 1)`.
  have hAa : 0 ≤ Real.sqrt (Work.Diff.EXT.curvNormK g x a)
      * ∏ r : Fin a, Real.sqrt (g.inner x (F (d₁ r) x) (F (d₁ r) x)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
  have hBb : 0 ≤ Real.sqrt (Work.Diff.EXT.curvNormK g x b)
      * ∏ r : Fin b, Real.sqrt (g.inner x (F (d₂ r) x) (F (d₂ r) x)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
  have hCc : 0 ≤ ∏ t : Fin 4, Real.sqrt (g.inner x (F (s t) x) (F (s t) x)) :=
    Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  have hle : C₀ * (Module.finrank ℝ E : ℝ) ^ 4
      ≤ C₀ * ((Module.finrank ℝ E : ℝ) ^ 4 + 1) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num)) hC₀
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hAa) hBb) hCc

end Work.Diff.EXT.Mono
