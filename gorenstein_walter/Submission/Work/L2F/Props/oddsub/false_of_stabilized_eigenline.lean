import Mathlib

/-!
# A nonzero matrix with a stabilized line has no second eigen-direction

If `A` has a left inverse `B` (`B * A = 1`, so `A` is injective on `F²`), and if `A` maps a
nonzero vector `v` into the span of a vector `u` (`A v = c • u`) while stabilizing the line
`F u` (`A u = d • u`), then `u` must already lie in `F v`.  Consequently, if `u` is *not* in
`F v`, the configuration is impossible.

The proof is elementary linear algebra: `B * A = 1` makes `mulVec A` injective; the vector
`d • v - c • u` is killed by `A`, hence is zero; then either `c = 0`, forcing `A v = 0` with
`v ≠ 0`, or `c ≠ 0`, exhibiting `u = (c⁻¹ * d) • v` as a multiple of `v`.
-/

namespace Work.L2F.Props.oddsub

open Matrix

theorem false_of_stabilized_eigenline {F : Type*} [Field F] {A B : Matrix (Fin 2) (Fin 2) F}
    (hBA : B * A = 1) {v u : Fin 2 → F} {c d : F}
    (hv : v ≠ 0) (hu : u ≠ 0) (huv : u ∉ Submodule.span F ({v} : Set (Fin 2 → F)))
    (hlv : Matrix.mulVec A v = c • u) (hlu : Matrix.mulVec A u = d • u) : False := by
  -- `A` has a left inverse, hence acts injectively on column vectors.
  have hker : ∀ x : Fin 2 → F, Matrix.mulVec A x = 0 → x = 0 := by
    intro x hx
    have h1 : (B * A) *ᵥ x = x := by rw [hBA, Matrix.one_mulVec]
    have h2 : (B * A) *ᵥ x = B *ᵥ (A *ᵥ x) := (Matrix.mulVec_mulVec x B A).symm
    rw [h2, hx, Matrix.mulVec_zero] at h1
    exact h1.symm
  -- The vector `d • v - c • u` lies in the kernel of `A`.
  have hw0 : Matrix.mulVec A (d • v - c • u) = 0 := by
    calc Matrix.mulVec A (d • v - c • u)
        = Matrix.mulVec A (d • v) - Matrix.mulVec A (c • u) := Matrix.mulVec_sub A _ _
      _ = d • (Matrix.mulVec A v) - c • (Matrix.mulVec A u) := by
            rw [Matrix.mulVec_smul, Matrix.mulVec_smul]
      _ = d • (c • u) - c • (d • u) := by rw [hlv, hlu]
      _ = 0 := by rw [smul_smul, smul_smul, mul_comm d c, sub_self]
  have hw : d • v - c • u = 0 := hker _ hw0
  by_cases hc : c = 0
  · -- Then `A v = 0` with `v ≠ 0`, contradicting injectivity.
    have : Matrix.mulVec A v = 0 := by rw [hlv, hc, zero_smul]
    exact hv (hker v this)
  · -- Then `u = (c⁻¹ * d) • v` lies in the span of `v`, against `huv`.
    have hcu : c • u = d • v := (sub_eq_zero.mp hw).symm
    have hu' : u = (c⁻¹ * d) • v := by
      calc u = c⁻¹ • (c • u) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = c⁻¹ • (d • v) := by rw [hcu]
        _ = (c⁻¹ * d) • v := by rw [smul_smul]
    exact huv (Submodule.mem_span_singleton.mpr ⟨c⁻¹ * d, hu'.symm⟩)

end Work.L2F.Props.oddsub
