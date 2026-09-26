import Mathlib
import Submission.Work.Drive.Generic.HeightDefs
import Submission.Work.Drive.Generic.inner_fderiv_normal_d2

/-!
# The derivative of the Gauss normal, tested against the first partial derivative

For an immersion `Φ : ℝ × ℝ → ℝ³` the Gauss map is `normal Φ p = ∂₁Φ(p) ⨯ ∂₂Φ(p)`.  This file
establishes the companion orthogonality relation to `inner_fderiv_normal_d2`:

`⟪D(normal Φ)(p) x, ∂₁Φ(p)⟫ = -⟪normal Φ p, D²Φ(p)(x, ∂₁)⟫`.

The derivative formula `D(normal Φ)(p) x = ∂₁Φ(p) ⨯ D²Φ(p)(x, ∂₂) + D²Φ(p)(x, ∂₁) ⨯ ∂₂Φ(p)` and the
elementary identities for `crossE` are taken from the sibling file `inner_fderiv_normal_d2`, whose
module is imported above.  The only new ingredient here is the observation that the scalar triple
product changes sign under the exchange of its first and third entries
(`inner_crossE_swap13`), which converts the `D²Φ(p)(x, ∂₁) ⨯ ∂₂Φ(p)` term into the desired one.
-/

namespace Work.Drive.Generic

/-- The cross product on `E3` is anticommutative. -/
lemma crossE_anticomm (u v : E3) : crossE u v = - crossE v u := by
  apply WithLp.ofLp_injective
  simp [ofLp_crossE, cross_anticomm]

/-- The scalar triple product `⟪u ⨯ v, w⟫` changes sign when its first and third entries are
exchanged. -/
lemma inner_crossE_swap13 (u v w : E3) : inner ℝ (crossE u v) w = - inner ℝ (crossE w v) u := by
  rw [inner_crossE_swap u v w, inner_crossE_swap w v u, crossE_anticomm w u]
  simp

theorem inner_fderiv_normal_d1 {Φ : ℝ × ℝ → Work.Drive.Generic.E3} (hΦ : ContDiff ℝ 3 Φ)
    (p x : ℝ × ℝ) :
    inner ℝ (fderiv ℝ (Work.Drive.Generic.normal Φ) p x) (Work.Drive.Generic.d1 Φ p) =
      - inner ℝ (Work.Drive.Generic.normal Φ p) (Work.Drive.Generic.D2 Φ p x (1, 0)) := by
  rw [fderiv_normal_apply hΦ p x, inner_add_left]
  have h1 : inner ℝ (crossE (d1 Φ p) (D2 Φ p x (0, 1))) (d1 Φ p) = 0 := by
    rw [real_inner_comm, inner_crossE_left]
  have h2 : inner ℝ (crossE (D2 Φ p x (1, 0)) (d2 Φ p)) (d1 Φ p)
      = - inner ℝ (crossE (d1 Φ p) (d2 Φ p)) (D2 Φ p x (1, 0)) :=
    inner_crossE_swap13 (D2 Φ p x (1, 0)) (d2 Φ p) (d1 Φ p)
  rw [h1, h2]
  simp [Work.Drive.Generic.normal]

end Work.Drive.Generic
