import Mathlib
import Submission.UnifDeps
import Submission.Holomorphic
import Submission.HolomorphicLog
import Submission.Conjugate

/-!
# A bounded non-constant harmonic function gives a bounded non-constant holomorphic function

On a connected Riemann surface whose fundamental group has no non-trivial homomorphism to `ℝ`
(the hypothesis `H¹(X,ℝ) = 0` of Hubbard's Theorem 1.1.2), every harmonic function is the real part
of a global holomorphic function (`Submission.exists_holomorphicOnX_re_of_harmonic`).  Taking
`f = exp F` turns a *bounded* non-constant harmonic function into a bounded non-constant
holomorphic function.

This is the bridge that makes the extremal-function machinery of `Submission.Extremal` and
`Submission.ExtremalInj` non-vacuous in the hyperbolic case, and it is the first step of the
"bounded holomorphic functions" route to uniformization.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold mℂ 1 X]

/-- **Bounded non-constant harmonic ⟹ bounded non-constant holomorphic.**  If every homomorphism
`π₁(X,x₀) → ℝ` vanishes, then a bounded non-constant harmonic function on `X` yields a bounded
non-constant holomorphic function on `X`. -/
theorem exists_bounded_holomorphic_of_bounded_harmonic (x₀ : X)
    [Subsingleton <| Additive (FundamentalGroup X x₀) →+ ℝ] {u : X → ℝ}
    (hu : HarmonicOnX u univ) (hb : ∃ M : ℝ, ∀ x, |u x| ≤ M) (hnc : ∃ a b : X, u a ≠ u b) :
    ∃ f : X → ℂ, HolomorphicOnX f univ ∧ (∃ a b : X, f a ≠ f b) ∧ ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨F, hFhol, hFre⟩ := exists_holomorphicOnX_re_of_harmonic (X := X) x₀ hu
  refine ⟨fun x => Complex.exp (F x), hFhol.cexp, ?_, ⟨Real.exp M, ?_⟩⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨a, b, hab⟩ := hnc
    have h2 : ‖Complex.exp (F a)‖ = ‖Complex.exp (F b)‖ := by rw [hcon a b]
    rw [Complex.norm_exp, Complex.norm_exp, hFre a, hFre b] at h2
    exact hab (Real.exp_injective h2)
  · intro x
    rw [Complex.norm_exp, hFre x]
    exact Real.exp_le_exp.mpr (abs_le.mp (hM x)).2

end Submission
