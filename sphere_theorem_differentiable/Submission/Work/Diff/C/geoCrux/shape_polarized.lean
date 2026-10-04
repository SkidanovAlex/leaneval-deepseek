import Mathlib
import Submission.Work.Diff.C.far_sphere_size
import Submission.Work.Diff.C.geoCrux.ShapePolarizeDefs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C.geoCrux

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

set_option backward.isDefEq.respectTransparency false

/-- **Polarized shape-operator bound.**

`HessBoundRegion` bounds the *full bilinear form* of `fcos q = cos ∘ rdist q` by `ε₁‖V‖‖W‖`, so
the chain rule for `cos` (`rhess_cos_far`) converts it directly — with no polarization
identity — into the bound for *all* pairs of directions orthogonal to `∇(fcos q)`: the deviation of
the shape operator of the geodesic sphere around `q` from `cot (rdist q ·)` times the metric is at
most `ε₁ / sin (rdist q x)`.

Concretely: `rhess_cos_far` gives
`rhess (fcos q) x V W = -cos d · (dF V)(dF W) - sin d · rhess F x V W` with `F = rdist q`, and
`V, W ⊥ ∇(fcos q) x` together with `∇(fcos q) x = -sin d • ∇F x` and `sin d > 0` forces
`dF V = dF W = 0`.  Hence `HessBoundRegion` reads
`|-sin d · rhess F x V W + cos d · ⟪V,W⟫| ≤ ε₁‖V‖‖W‖`, i.e., using `sin d · cot d = cos d`,
`sin d · |rhess F x V W - cot d · ⟪V,W⟫| ≤ ε₁‖V‖‖W‖`. -/
theorem shape_polarized : Work.Diff.C.GeoCrux.ShapePolarizedProp := by
  intro E _ _ _ _ H _ I M _ _ _ _ _ _ _ _ _ _ cov _ hmet htor c ε₁ q hHess x hx hsm hpos hdπ V W hV hW
  set d : ℝ := rdist (I := I) (M := M) q x with hd
  have hsind : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hpos hdπ
  -- the orthogonal complement of `∇ (fcos q) x` is the one of `∇ (rdist q) x`
  have hgradf : rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x
      = (-Real.sin d) • rgrad (I := I) (M := M) (rdist (I := I) (M := M) q) x := by
    have h := rgrad_fcos (I := I) (M := M) (q := q) hsm
    simpa [hd] using h
  have hneg : (-Real.sin d) ≠ 0 := neg_ne_zero.mpr (ne_of_gt hsind)
  have horthV : Inner.inner ℝ (rgrad (I := I) (M := M) (rdist (I := I) (M := M) q) x) V = 0 := by
    have h := hV
    rw [hgradf, inner_smul_left] at h
    exact (mul_eq_zero.mp h).resolve_left hneg
  have horthW : Inner.inner ℝ (rgrad (I := I) (M := M) (rdist (I := I) (M := M) q) x) W = 0 := by
    have h := hW
    rw [hgradf, inner_smul_left] at h
    exact (mul_eq_zero.mp h).resolve_left hneg
  have hmfdV : mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) q z) x V = 0 := by
    rw [← inner_rgrad_mvfderiv_local]
    exact horthV
  have hmfdW : mvfderiv I (fun z : M ↦ rdist (I := I) (M := M) q z) x W = 0 := by
    rw [← inner_rgrad_mvfderiv_local]
    exact horthW
  -- the chain rule for `cos`
  have hchain := rhess_cos_far (I := I) (M := M) (cov := cov)
    (F := fun z : M ↦ rdist (I := I) (M := M) q z) hsm V W
  rw [hmfdV, hmfdW] at hchain
  have hrhs : rhess cov (fcos (I := I) (M := M) q) x V W
      = -Real.sin d * rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V W := by
    show rhess cov (fun y : M ↦ Real.cos (rdist (I := I) (M := M) q y)) x V W = _
    rw [hchain]
    ring
  -- `hHess` for the pair `(V,W)`
  have hb := hHess x V W hx
  have hfcos : fcos (I := I) (M := M) q x = Real.cos d := by rw [hd]; rfl
  rw [hrhs, hfcos] at hb
  -- `sin d * cot d = cos d`
  have hcot : Real.sin d * Real.cot d = Real.cos d := by
    rw [Real.cot_eq_cos_div_sin]
    field_simp
  -- the key inequality
  have hkey : Real.sin d * |rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V W
      - Real.cot d * Inner.inner ℝ V W| ≤ ε₁ * ‖V‖ * ‖W‖ := by
    have hAa : (-Real.sin d * rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V W
          + Real.cos d * Inner.inner ℝ V W)
        = -Real.sin d * (rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V W
            - Real.cot d * Inner.inner ℝ V W) := by
      rw [← hcot]
      ring
    rw [hAa, abs_mul, abs_neg, abs_of_pos hsind] at hb
    linarith [hb]
  have hfin : |rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V W
      - Real.cot d * Inner.inner ℝ V W| ≤ (ε₁ / Real.sin d) * ‖V‖ * ‖W‖ := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hsind]
    linarith [hkey]
  simpa [hd] using hfin

end Work.Diff.C.geoCrux
