import Mathlib
import Submission.Work.Diff.GE.kato_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The Gram–Schmidt step produces an orthonormal vector.**

With the bump of the normalisation equal to `1` at `y` (so that the smoothed Gram function
`katoNorm` agrees there with the honest Gram function `katoGram`), and with the previously
produced fields `W j`, `j < i`, an orthonormal family at `y` (hypotheses `hdiag`, `hoff`), the
normalised step vector `katoStep g x V W i y` has `g`-norm `1` at `y` and is `g`-orthogonal to
every `W k y`, `k < i`.

This is the purely algebraic (pointwise) content of the Gram–Schmidt induction: it does not use
smoothness of anything. -/
theorem kato_orthonormal_algebra
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) (x : M) (V W : katoIdx E → Π y : M, TangentSpace I y) (i : katoIdx E) (y : M)
    (hbump : katoBump (I := I) (katoGram g V W i) x y = 1)
    (hfy : 0 < katoGram g V W i y)
    (hdiag : ∀ j, j.val < i.val → g.inner y (W j y) (W j y) = 1)
    (hoff : ∀ j, j.val < i.val → ∀ k, k.val < j.val → g.inner y (W j y) (W k y) = 0) :
    g.inner y (katoStep g x V W i y) (katoStep g x V W i y) = 1 ∧
      (∀ k, k.val < i.val → g.inner y (katoStep g x V W i y) (W k y) = 0) := by
  -- Abbreviations for the pre-normalisation vector, the normalising scalar and the Gram function.
  set u : TangentSpace I y := katoU g V W i y with hu
  set c : ℝ := katoC g x V W i y with hc
  -- At `y` the bump is `1`, so the smoothed Gram function is the honest one.
  have hnorm : katoNorm g x V W i y = katoGram g V W i y := by
    simp only [katoNorm_apply, hbump, mul_one]
    ring
  have hcval : c = (Real.sqrt (katoGram g V W i y))⁻¹ := by
    simp only [hc, katoC_apply, hnorm]
  have hgram : g.inner y u u = katoGram g V W i y := by
    simp only [hu, katoGram_apply]
  have hstep : katoStep g x V W i y = c • u := by
    simp only [katoStep_apply, hc, hu]
  constructor
  · -- Norm `1`: `(√t)⁻¹ * ((√t)⁻¹ * t) = 1` since `t > 0`.
    rw [hstep]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [hgram, hcval]
    have hne : Real.sqrt (katoGram g V W i y) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hfy)
    field_simp
    rw [Real.sq_sqrt (le_of_lt hfy)]
  · -- Orthogonality: expand `inner (c • u) (W k y)` and use that `u` is orthogonal to `W k y`.
    intro k hk
    have expand : g.inner y u (W k y)
        = g.inner y (V i y) (W k y)
          - ∑ j ∈ katoPre (E := E) i,
              (g.inner y (V i y) (W j y)) * (g.inner y (W j y) (W k y)) := by
      rw [hu]
      simp only [katoU_apply, map_sub, map_sum, map_smul, sub_apply, sum_apply, smul_apply,
        smul_eq_mul]
    have hinner_u : g.inner y u (W k y) = 0 := by
      rw [expand]
      -- Only the term `j = k` of the sum survives, because `W` is orthonormal below `i`.
      have hsum : ∑ j ∈ katoPre (E := E) i,
            (g.inner y (V i y) (W j y)) * (g.inner y (W j y) (W k y))
          = g.inner y (V i y) (W k y) := by
        rw [Finset.sum_eq_single k]
        · rw [hdiag k hk, mul_one]
        · intro j hj hjk
          rw [katoPre_mem] at hj
          rcases lt_or_gt_of_ne (fun h => hjk (Fin.ext h)) with hlt | hgt
          · rw [g.symm y (W j y) (W k y), hoff k hk j hlt, mul_zero]
          · rw [hoff j hj k hgt, mul_zero]
        · intro hknot
          exact absurd (katoPre_mem.mpr hk) hknot
      rw [hsum, sub_self]
    rw [hstep]
    simp only [map_smul, smul_apply, smul_eq_mul, hinner_u, mul_zero]

end Work.Diff.GE
