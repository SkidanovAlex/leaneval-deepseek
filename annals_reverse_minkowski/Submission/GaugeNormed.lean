import Mathlib

/-!
# The gauge norm as a genuine normed-space structure

For a symmetric convex body `K ⊆ ℝⁿ` the Minkowski functional `gauge K` is a norm.  Lean cannot
instantiate `NormedAddCommGroup` on `EuclideanSpace ℝ (Fin n)` itself (it already carries the
Euclidean norm), so we use the type synonym `GSp n K` and provide the structure as a *definition*
to be installed locally with `letI`.

This is the ambient space `X = (ℝⁿ, ‖·‖_K)` of the K-convexity argument
(`Submission/Blueprint.lean`, session 120): Pisier's bound `K(X) ≤ 4(1+log₂ d(X,ℓ₂ⁿ))` must be
proved in the `K`-norm, not in the Euclidean norm.
-/

open Module

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.GaugeNormed

variable {n : ℕ}

/-- `ℝⁿ` with the norm `gauge K` — a type synonym for `EuclideanSpace ℝ (Fin n)`. -/
def GSp (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : Type := EuclideanSpace ℝ (Fin n)

namespace GSp

instance (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : AddCommGroup (GSp n K) :=
  inferInstanceAs (AddCommGroup (EuclideanSpace ℝ (Fin n)))

instance (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : Module ℝ (GSp n K) :=
  inferInstanceAs (Module ℝ (EuclideanSpace ℝ (Fin n)))

noncomputable instance (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))) : Norm (GSp n K) :=
  ⟨fun x => gauge K x⟩

theorem norm_def (K : Set (EuclideanSpace ℝ (Fin n))) (x : GSp n K) :
    ‖x‖ = gauge K x := rfl

/-- A symmetric convex set is balanced. -/
theorem balanced_of_symmetric {K : Set (EuclideanSpace ℝ (Fin n))} (hcvx : Convex ℝ K)
    (hne : K.Nonempty) (hsymm : -K = K) : Balanced ℝ K := by
  rw [balanced_iff_smul_mem]
  obtain ⟨x₀, hx₀⟩ := hne
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := by
    have hneg : -x₀ ∈ K := by
      have : -x₀ ∈ -K := by simpa using hx₀
      rwa [hsymm] at this
    have h := hcvx hx₀ hneg (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) + 1/2 = 1)
    simpa using h
  intro a ha x hx
  rcases lt_or_ge a 0 with ha0 | ha0
  · have hxa : -x ∈ K := by
      have : -x ∈ -K := by simpa using hx
      rwa [hsymm] at this
    have hna1 : -a ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_neg ha0] at ha; linarith
    have h : (-a) • (-x) ∈ K := by
      have h' := hcvx hxa h0 (by linarith : (0:ℝ) ≤ -a)
        (by linarith : (0:ℝ) ≤ 1 - (-a)) (by ring : -a + (1 - (-a)) = 1)
      simpa using h'
    have heq : (-a) • (-x) = a • x := by rw [smul_neg, neg_smul, neg_neg]
    rwa [← heq]
  · have ha1 : a ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg ha0] at ha; exact ha
    have h := hcvx hx h0 ha0 (by linarith : (0:ℝ) ≤ 1 - a) (by ring : a + (1 - a) = 1)
    simpa using h

/-- The `NormedSpace.Core` for the gauge norm. -/
noncomputable def core (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (habs : Absorbent ℝ K) (hbdd : Bornology.IsVonNBounded ℝ K) (hbal : Balanced ℝ K) :
    NormedSpace.Core ℝ (GSp n K) where
  norm_nonneg x := gauge_nonneg x
  norm_smul c x := gauge_smul hbal c x
  norm_triangle x y := gauge_add_le hcvx habs x y
  norm_eq_zero_iff x := gauge_eq_zero habs hbdd

/-- The normed-group structure on `GSp n K` for `K` a symmetric convex body. -/
noncomputable def normedAddCommGroup (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (habs : Absorbent ℝ K) (hbdd : Bornology.IsVonNBounded ℝ K) (hbal : Balanced ℝ K) :
    NormedAddCommGroup (GSp n K) :=
  NormedAddCommGroup.ofCore (core K hcvx habs hbdd hbal)

end GSp

end Submission.GaugeNormed
