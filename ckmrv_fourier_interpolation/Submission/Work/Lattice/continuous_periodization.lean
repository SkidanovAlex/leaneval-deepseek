import Mathlib
import Submission.Work.Lattice.poissonBasics
import Submission.Work.Lattice.exists_summable_bound_periodization

/-!
# Continuity of the periodization over `ℤⁿ`

For a Schwartz function `f` on `ℝⁿ`, the periodization
`periodization f x = ∑' v : ℤⁿ, f (x + v)` is continuous.

The proof is the standard locally uniform domination argument.  Fix `x₀`.  By
`Work.Lattice.exists_summable_bound_periodization` there is a summable
`u : ℤⁿ → ℝ` and a neighbourhood `s` of `x₀` such that
`‖f (x + v)‖ ≤ u v` for all `x ∈ s` and all `v`.  Each term `x ↦ f (x + v)` is
continuous (it is `f` composed with the continuous map `x ↦ x + v`), so
`continuousOn_tsum` — the Weierstrass `M`-test for series of functions — shows
that the sum is continuous on `s`, hence at `x₀`.  As `x₀` is arbitrary, the
periodization is continuous.
-/

namespace Work.Lattice

open scoped SchwartzMap Topology

theorem continuous_periodization {n : ℕ} (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ) :
    Continuous (Work.Lattice.periodization f) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨u, hu, hbound⟩ := exists_summable_bound_periodization f x₀
  have hcontOn : ContinuousOn (periodization f)
      {x : Fin n → ℝ | ∀ v : Fin n → ℤ, ‖f (WithLp.toLp 2 (x + intVecToReal v))‖ ≤ u v} := by
    refine continuousOn_tsum (u := u)
      (f := fun (v : Fin n → ℤ) (x : Fin n → ℝ) => f (WithLp.toLp 2 (x + intVecToReal v)))
      ?_ hu ?_
    · intro v
      have h1 : Continuous fun x : Fin n → ℝ => WithLp.toLp 2 (x + intVecToReal v) :=
        (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp (continuous_id.add continuous_const)
      exact (f.continuous.comp h1).continuousOn
    · intro v x hx
      exact hx v
  exact hcontOn.continuousAt hbound

end Work.Lattice
