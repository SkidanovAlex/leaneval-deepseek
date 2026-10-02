import Mathlib
import Submission.Work.Morse.flow_basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology

/-- A family of global integral curves through every point satisfies the group law, by uniqueness of
integral curves. -/
theorem flow_group_law {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    {v : (x : M) → TangentSpace (𝓡 n) x}
    (hv : ContMDiff (𝓡 n) (𝓡 n).tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle (𝓡 n) M)))
    {Φ : ℝ → M → M} (h0 : ∀ x, Φ 0 x = x) (hΦ : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v) :
    ∀ s t x, Φ (s + t) x = Φ s (Φ t x) := by
  intro s t x
  -- Both `u ↦ Φ (u + t) x` and `u ↦ Φ u (Φ t x)` are global integral curves of `v`, and they
  -- agree at `u = 0`; uniqueness of integral curves of a `C¹` vector field gives the result.
  have h1 : IsMIntegralCurve (fun u : ℝ => Φ (u + t) x) v := (hΦ x).comp_add t
  have h2 : IsMIntegralCurve (fun u : ℝ => Φ u (Φ t x)) v := hΦ (Φ t x)
  have heq : (fun u : ℝ => Φ (u + t) x) = (fun u : ℝ => Φ u (Φ t x)) :=
    isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv h1 h2
      (by simp only [zero_add]; exact (h0 (Φ t x)).symm)
  exact congrFun heq s

end Work.Morse
