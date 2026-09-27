import Mathlib

/-!
# Drive interfaces for `annals_inscribed_rectangles` (written by the project lead, 2026-09-23)

Two self-contained inputs of the geometric core (Hugelmeyer's Lemmas 1–6, done by mod-2 intersection counting):

* `UmlaufProp` — Hopf's Umlaufsatz: the tangent of a smooth embedded closed plane curve turns exactly once, ±.
* `ParityProp` — a compact 1-manifold has an even number of boundary points, in the concrete form "zeros of a
  smooth `F : ℝ^{m+1} → ℝ^m` on the unit box, cut out transversally, meet the boundary of the box an even
  number of times".
-/

namespace Submission.Drive

open Manifold
open scoped Manifold ContDiff

/-- **Umlaufsatz.**  For a smooth embedding `γ : Circle → ℝ × ℝ`, the velocity of `t ↦ γ (Circle.exp t)` has a
continuous angle function `θ` that increases by exactly `2π` or exactly `-2π` over one period. -/
def UmlaufProp : Prop :=
  ∀ γ : Circle → ℝ × ℝ, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ →
    ∃ (θ ρ : ℝ → ℝ) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧ Continuous θ ∧
      (∀ t, 0 < ρ t) ∧
      (∀ t, deriv (fun s => γ (Circle.exp s)) t = ρ t • (Real.cos (θ t), Real.sin (θ t))) ∧
      ∀ t, θ (t + 2 * Real.pi) - θ t = 2 * Real.pi * ε

/-- The closed unit box `[0,1]^(m+1)`. -/
def unitBox (m : ℕ) : Set (EuclideanSpace ℝ (Fin (m + 1))) := {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The boundary of the unit box: some coordinate is `0` or `1`. -/
def unitBoxBdry (m : ℕ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {x | x ∈ unitBox m ∧ ∃ i, x i = 0 ∨ x i = 1}

/-- **Mod-2 boundary parity.**  Let `F : ℝ^{m+1} → ℝ^m` be smooth, with `0` a regular value on the box, every zero
in the boundary on exactly ONE face (no zero at a lower-dimensional face), and `F` restricted to that face having
`0` as a regular value there.  Then the zeros on the boundary are finitely many, and there is an even number of
them. -/
def ParityProp : Prop :=
  ∀ (m : ℕ) (F : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin m)),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
    (∀ x ∈ unitBox m, F x = 0 → Function.Surjective (fderiv ℝ F x)) →
    (∀ x ∈ unitBoxBdry m, F x = 0 → ∃ i, (x i = 0 ∨ x i = 1) ∧
      (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin (m + 1)) // v i = 0} =>
        fderiv ℝ F x v.1)) →
    {x | x ∈ unitBoxBdry m ∧ F x = 0}.Finite ∧
      Even (Set.ncard {x | x ∈ unitBoxBdry m ∧ F x = 0})

end Submission.Drive
