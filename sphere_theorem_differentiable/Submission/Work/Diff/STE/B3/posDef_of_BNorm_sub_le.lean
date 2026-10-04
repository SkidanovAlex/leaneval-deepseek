/-
# Layer D2: positivity persistence from a small `BNorm` of the perturbation

The Galerkin solution is run inside the positivity set of `c ↦ addSec g₀ (genMap D ε c)`.  The
a priori estimate produces a bound `BNorm k (u t) ≤ BNorm k g₀ + C t` on the *energy*, i.e. it
controls `BNorm k (u t - g₀)` by `C t`.  The present file converts that small-perturbation bound
into positive definiteness of `u t`:

  `BNorm k (h - g₀) ≤ ε  ⟹  ∀ x v, v ≠ 0 → 0 < h x v v`

for an explicit `ε > 0` depending only on `D`, `k` and the ellipticity data.  The proof is the
pointwise bound `Work.Diff.STE.B3Data.pointwise_bound` (the value of a section is controlled by
`√(BNorm k)` in the `g₀`-metric) applied to the perturbation `h - g₀`, plus the elementary
`g₀(v,v) > 0`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3Data

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **Positivity persistence.**  If the perturbation `h - g₀` of a section `h` is small in the
composite `Hᵏ` norm `D.BNorm k` (with `card (Fin (finrank ℝ E)) < 2k`), then `h` is positive
definite.  The threshold is uniform in `h`. -/
theorem posDef_of_BNorm_sub_le (D : B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k)
    (h : Bil (I := I) (M := M))
    (hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (fun x => h x - g₀.inner x) a b))
    (hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Periodic1 (D.Rper i (fun x => h x - g₀.inner x) a b))
    (hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z) :
    ∃ ε : ℝ, 0 < ε ∧ (D.BNorm k (fun x => h x - g₀.inner x) ≤ ε →
      ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v) := by
  obtain ⟨C, hC, hCb⟩ := D.pointwise_bound k hk (fun x => h x - g₀.inner x) hsm hper hdens
  -- the threshold: `√(BNorm) ≤ 1/(2 * (C + 1))`
  refine ⟨(1 / (2 * (C + 1))) ^ 2, by positivity, fun hle x v hv => ?_⟩
  have hC1 : 0 < C + 1 := by linarith
  have hnorm : Real.sqrt (D.BNorm k (fun x => h x - g₀.inner x)) ≤ 1 / (2 * (C + 1)) :=
    (Real.sqrt_le_left (by positivity)).mpr hle
  have hkey := hCb x v v
  have hCsqrt : C * Real.sqrt (D.BNorm k (fun x => h x - g₀.inner x)) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hnorm hC
    have h2 : C * (1 / (2 * (C + 1))) ≤ 1 / 2 := by
      rw [show C * (1 / (2 * (C + 1))) = C / (2 * (C + 1)) from by ring]
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith [this, h2]
  have hgpos : 0 < g₀.inner x v v := g₀.pos x v hv
  have hsqrt_v : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v :=
    Real.mul_self_sqrt (le_of_lt hgpos)
  have hsqrt_v_nonneg : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hu_nonneg : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hbound : |h x v v - g₀.inner x v v| ≤ (1 / 2) * g₀.inner x v v := by
    have h3 : C * Real.sqrt (D.BNorm k (fun x => h x - g₀.inner x))
        * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)
        ≤ (1 / 2) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by
      calc C * Real.sqrt (D.BNorm k (fun x => h x - g₀.inner x))
              * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)
          = (C * Real.sqrt (D.BNorm k (fun x => h x - g₀.inner x)))
              * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by ring
        _ ≤ (1 / 2) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) :=
              mul_le_mul_of_nonneg_right hCsqrt (mul_nonneg hu_nonneg hsqrt_v_nonneg)
    calc |h x v v - g₀.inner x v v|
        = |(fun x => h x - g₀.inner x) x v v| := rfl
      _ ≤ C * Real.sqrt (D.BNorm k (fun x => h x - g₀.inner x))
            * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) := hkey
      _ ≤ (1 / 2) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := h3
      _ = (1 / 2) * g₀.inner x v v := by rw [hsqrt_v]
  have := abs_le.mp hbound
  linarith [this.1, hgpos]

end

end Work.Diff.STE.B3Data
