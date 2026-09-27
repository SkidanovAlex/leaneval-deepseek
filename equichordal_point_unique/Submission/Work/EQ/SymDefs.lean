import Mathlib
import Submission.Work.EQ.Defs

/-! Shared definitions for the symmetry lemma `Work.EQ.normEqCurve_symmetric`
(Rychlik, Invent. Math. 129 (1997), §2.5--2.6).

Setting: `O₁ = -a/2`, `O₂ = a/2` on the real axis of `ℂ`, chord length `1`.  The *chord
involution* `chordMap c` sends a point `P` (with `0 < ‖P - c‖ < 1`) to the other endpoint of
the unit chord through `c`, i.e. `c + (1 - 1/‖P-c‖) • (P - c)`.  The composite
`T = α₁ ∘ α₂ : chordMap O₁ ∘ chordMap O₂` is Rychlik's `T = T₁ T₂`. -/

namespace Work.EQ

open Complex

/-- The left focus `O₁ = -a/2` (on the real axis of `ℂ`). -/
noncomputable def O1_sym (a : ℝ) : ℂ := -((a / 2 : ℝ) : ℂ)

/-- The right focus `O₂ = +a/2`. -/
noncomputable def O2_sym (a : ℝ) : ℂ := ((a / 2 : ℝ) : ℂ)

/-- The chord involution about `c`: for `0 < ‖P - c‖` the point `c + (1 - 1/‖P-c‖) • (P - c)`,
which for `‖P - c‖ < 1` is the other endpoint of the unit chord through `c`. -/
noncomputable def chordMap (c P : ℂ) : ℂ := P - (P - c) / ((‖P - c‖ : ℝ) : ℂ)

/-- Rychlik's equichordal map `T = T₁ ∘ T₂`. -/
noncomputable def eqT (a : ℝ) (P : ℂ) : ℂ := chordMap (O1_sym a) (chordMap (O2_sym a) P)

/-- **Local normal hyperbolic model.**  `T` fixes the real axis near the real point `A` and
`T(A + ξ + η i) = A + (ξ + F ξ η) + (η · G ξ η) i` with `F = O(η²)`, `G` close to `lam ∈ (0,1)`
and Lipschitz bounds; these are the estimates needed to prove that two points of a small ball
around `A`, with the same imaginary part and `T`-orbits converging to `A`, coincide. -/
def LocalModel (T : ℂ → ℂ) (A : ℂ) (lam C ε : ℝ) : Prop :=
  A.im = 0 ∧ 0 < ε ∧ 0 < C ∧ 0 < lam ∧ lam < 1 ∧ C * ε ≤ (1 - lam) / 4 ∧
    (∀ ξ : ℝ, |ξ| ≤ 4 * ε → T (A + (ξ : ℂ)) = A + (ξ : ℂ)) ∧
    ∃ F G : ℝ → ℝ → ℝ,
      (∀ ξ η : ℝ, |ξ| ≤ 4 * ε → |η| ≤ 4 * ε →
          T (A + (ξ : ℂ) + (η : ℂ) * Complex.I) =
            A + ((ξ + F ξ η : ℝ) : ℂ) + ((η * G ξ η : ℝ) : ℂ) * Complex.I) ∧
      (∀ ξ η : ℝ, |ξ| ≤ 4 * ε → |η| ≤ 4 * ε → |F ξ η| ≤ C * η ^ 2) ∧
      (∀ ξ η : ℝ, |ξ| ≤ 4 * ε → |η| ≤ 4 * ε → |G ξ η - lam| ≤ C * (|ξ| + |η|)) ∧
      (∀ ξ η ξ' η' : ℝ, |ξ| ≤ 4 * ε → |η| ≤ 4 * ε → |ξ'| ≤ 4 * ε → |η'| ≤ 4 * ε →
          |F ξ η - F ξ' η'| ≤ C * (η ^ 2 * |ξ - ξ'| + (|η| + |η'|) * |η - η'|)) ∧
      (∀ ξ η ξ' η' : ℝ, |ξ| ≤ 4 * ε → |η| ≤ 4 * ε → |ξ'| ≤ 4 * ε → |η'| ≤ 4 * ε →
          |G ξ η - G ξ' η'| ≤ C * (|ξ - ξ'| + |η - η'|))

end Work.EQ
