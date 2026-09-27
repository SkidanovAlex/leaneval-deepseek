import Mathlib
import Submission.Work.Mostow.isometryEqOfSqSubZero
import Submission.Work.Mostow.isometryEqNegOfSqAddZero

namespace Work.Mostow

/-- An isometry `T` whose symmetric part `(T + T⁻¹)/2` equals `c • id` on an invariant subspace `W`
with `c = ±1` acts on `W` as the scalar `c`. -/
theorem isometryEqOfSymPartEq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (T : V ≃ₗᵢ[ℝ] V) (W : Submodule ℝ V) (hTW : ∀ x ∈ W, T x ∈ W) (c : ℝ)
    (hc : c = 1 ∨ c = -1) (h : ∀ x ∈ W, (2⁻¹ : ℝ) • (T x + T.symm x) = c • x) :
    ∀ x ∈ W, T x = c • x := by
  intro x hx
  rcases hc with rfl | rfl
  · have htwo : ∀ y ∈ W, T y + T.symm y = (2:ℝ) • y := by
      intro y hy
      have := congrArg (fun v => (2:ℝ) • v) (h y hy)
      simpa using this
    have h' : ∀ y ∈ W, T (T y - y) = T y - y := by
      intro y hy
      have h3 : T (T y) = (2:ℝ) • T y - y := by
        rw [eq_sub_iff_add_eq]
        have := congrArg (fun v => T v) (htwo y hy)
        simpa using this
      rw [map_sub, h3, two_smul]
      abel
    have := isometryEqOfSqSubZero T W hTW h' x hx
    rw [this, one_smul]
  · have htwo : ∀ y ∈ W, T y + T.symm y = -((2:ℝ) • y) := by
      intro y hy
      have := congrArg (fun v => (2:ℝ) • v) (h y hy)
      simpa using this
    have h' : ∀ y ∈ W, T (T y + y) = -(T y + y) := by
      intro y hy
      have h3 : T (T y) = -((2:ℝ) • T y) - y := by
        rw [eq_sub_iff_add_eq]
        have := congrArg (fun v => T v) (htwo y hy)
        simpa using this
      rw [map_add, h3, two_smul]
      abel
    have := isometryEqNegOfSqAddZero T W hTW h' x hx
    rw [this, neg_smul, one_smul]

end Work.Mostow
