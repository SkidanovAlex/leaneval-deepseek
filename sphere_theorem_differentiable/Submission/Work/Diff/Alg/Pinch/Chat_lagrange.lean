import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatDefs
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Auxiliary double-sum lemmas

The Lagrange/Gram identity is proved by expanding both sides into double sums over `(i,j)`.
The following two lemmas do all the index manipulation that is needed. -/

/-- A four-fold product of the indexed factors `uᵢ vⱼ pⱼ qᵢ` sums to a product of dot products. -/
theorem chat_sum_four (u v p q : Fin n → ℝ) :
    (∑ i, ∑ j, u i * v j * p j * q i) = dot u q * dot v p := by
  rw [dot, dot, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/-- Symmetry of `dot`. -/
theorem chat_dot_comm (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp only [dot]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `∑ᵢⱼ (xᵢzⱼ − yᵢwⱼ)² + (xᵢwⱼ + yᵢzⱼ)² = (dot x x + dot y y) (dot z z + dot w w)`
(i.e. `∑ᵢⱼ |ζᵢ ηⱼ|² = |ζ|² |η|²` in real coordinates). -/
theorem chat_sum_sq (x y z w : Fin n → ℝ) :
    (∑ i, ∑ j, ((x i * z j - y i * w j) ^ 2 + (x i * w j + y i * z j) ^ 2))
      = (dot x x + dot y y) * (dot z z + dot w w) := by
  have h : ∀ i j, ((x i * z j - y i * w j) ^ 2 + (x i * w j + y i * z j) ^ 2)
      = (x i ^ 2 + y i ^ 2) * (z j ^ 2 + w j ^ 2) := by intro i j; ring
  simp only [h]
  have h2 : (∑ i, ∑ j, (x i ^ 2 + y i ^ 2) * (z j ^ 2 + w j ^ 2))
      = (∑ i, (x i ^ 2 + y i ^ 2)) * (∑ j, (z j ^ 2 + w j ^ 2)) := by
    rw [Finset.sum_mul_sum]
  rw [h2]
  have h3 : (∑ i, (x i ^ 2 + y i ^ 2)) = dot x x + dot y y := by
    simp only [dot, pow_two, Finset.sum_add_distrib]
  have h4 : (∑ j, (z j ^ 2 + w j ^ 2)) = dot z z + dot w w := by
    simp only [dot, pow_two, Finset.sum_add_distrib]
  rw [h3, h4]

/-- `∑ᵢⱼ (xᵢzⱼ − yᵢwⱼ)(xⱼzᵢ − yⱼwᵢ) + (xᵢwⱼ + yᵢzⱼ)(xⱼwᵢ + yⱼzᵢ)
= (dot x z + dot y w)² + (dot x w − dot y z)²` (the real form of `|∑ᵢ ζ̄ᵢ ηᵢ|²`). -/
theorem chat_sum_cross (x y z w : Fin n → ℝ) :
    (∑ i, ∑ j, ((x i * z j - y i * w j) * (x j * z i - y j * w i)
        + (x i * w j + y i * z j) * (x j * w i + y j * z i)))
      = (dot x z + dot y w) ^ 2 + (dot x w - dot y z) ^ 2 := by
  have h : ∀ i j, ((x i * z j - y i * w j) * (x j * z i - y j * w i)
        + (x i * w j + y i * z j) * (x j * w i + y j * z i))
      = x i * z j * x j * z i - x i * z j * y j * w i - y i * w j * x j * z i + y i * w j * y j * w i
        + (x i * w j * x j * w i + x i * w j * y j * z i + y i * z j * x j * w i + y i * z j * y j * z i) := by
    intro i j; ring
  simp only [h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [chat_sum_four x z x z, chat_sum_four x z y w, chat_sum_four y w x z, chat_sum_four y w y w,
      chat_sum_four x w x w, chat_sum_four x w y z, chat_sum_four y z x w, chat_sum_four y z y z]
  rw [chat_dot_comm z x, chat_dot_comm z y, chat_dot_comm w x, chat_dot_comm w y]
  ring

/-- The index-wise splitting
`|ζᵢηⱼ − ζⱼηᵢ|² = |ζᵢηⱼ|² + |ζⱼηᵢ|² − 2 Re(ζᵢηⱼ conj(ζⱼηᵢ))`, summed over `(i,j)`:
the middle terms sum to negative twice the cross sum above, while the two norm terms give
four times ... precisely, the endpoint terms combine by symmetry of the summation. -/
theorem chat_split (x y z w : Fin n → ℝ) :
    (∑ i, ∑ j, (((x i * z j - y i * w j) - (x j * z i - y j * w i)) ^ 2
        + ((x i * w j + y i * z j) - (x j * w i + y j * z i)) ^ 2))
      = 2 * (∑ i, ∑ j, ((x i * z j - y i * w j) ^ 2 + (x i * w j + y i * z j) ^ 2))
        - 2 * (∑ i, ∑ j, ((x i * z j - y i * w j) * (x j * z i - y j * w i)
          + (x i * w j + y i * z j) * (x j * w i + y j * z i))) := by
  have h : ∀ i j, (((x i * z j - y i * w j) - (x j * z i - y j * w i)) ^ 2
        + ((x i * w j + y i * z j) - (x j * w i + y j * z i)) ^ 2)
      = (((x i * z j - y i * w j) ^ 2 + (x i * w j + y i * z j) ^ 2)
          - ((x i * z j - y i * w j) * (x j * z i - y j * w i)
            + (x i * w j + y i * z j) * (x j * w i + y j * z i))
          - ((x i * z j - y i * w j) * (x j * z i - y j * w i)
            + (x i * w j + y i * z j) * (x j * w i + y j * z i)))
        + ((x j * z i - y j * w i) ^ 2 + (x j * w i + y j * z i) ^ 2) := by intro i j; ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hC1 : (∑ i, ∑ j, (x j * z i - y j * w i) ^ 2)
      = (∑ i, ∑ j, (x i * z j - y i * w j) ^ 2) := by rw [Finset.sum_comm]
  have hC2 : (∑ i, ∑ j, (x j * w i + y j * z i) ^ 2)
      = (∑ i, ∑ j, (x i * w j + y i * z j) ^ 2) := by rw [Finset.sum_comm]
  rw [hC1, hC2]
  ring

/-- The Lagrange/Gram identity in real coordinates: for `ζ = x + iy`, `η = z + iw` the squared norm of the decomposable complex `2`-form `ζ ∧ η` (whose real and imaginary parts are the functions `qfA`, `qfB` of `Diff/Alg/Pinch/ChatDefs`) equals `2 * EF (Iso n) x y z w`; i.e. the round-sphere curvature quartic form is the square of the norm on `Λ²ℂⁿ`.

Both sides are explicit polynomials in the coordinates of `x y z w`.  Expand `Cone.EF (Iso n) x y z w` using `Cone.EF_iso` from `Diff/Alg/Pinch/inPIC2_cone_basic`, which gives `(dot x x + dot y y) * (dot z z + dot w w) - ((dot x z + dot y w)^2 + (dot y z - dot x w)^2)`, expand `dot`, and turn products of sums into double sums (`Finset.sum_mul_sum`), so that both sides become double sums over `(i,j)`.  (The desired identity is *not* true index by index, only after summation: the cross terms `∑ᵢⱼ (xᵢzᵢ + yᵢwᵢ)(xⱼzⱼ + yⱼwⱼ)` and `∑ᵢⱼ (yᵢzᵢ - xᵢwᵢ)(yⱼzⱼ - xⱼwⱼ)` factor as squares of `dot x z + dot y w` resp. `dot y z - dot x w`, while `∑ᵢⱼ (xᵢ²+yᵢ²)(zⱼ²+wⱼ²)` is `(dot x x + dot y y)(dot z z + dot w w)`.)  A clean way: prove the complex form `∑ᵢⱼ |ζᵢηⱼ - ζⱼηᵢ|² = 2 (|ζ|²|η|² - |∑ᵢ conj(ζᵢ) ηᵢ|²)` by expanding `∑ᵢⱼ ζᵢ ζ̄ⱼ ηⱼ η̄ᵢ = (∑ᵢ ζᵢ η̄ᵢ)(∑ⱼ ζ̄ⱼ ηⱼ)` (`Complex.normSq`, or `Complex.normSq_eq_norm_sq` as used in `pair_cs`), then transfer to real coordinates using `qfA + I*qfB = ζᵢηⱼ - ζⱼηᵢ` and `EF_iso`. -/
theorem Chat_lagrange (n : ℕ) (x y z w : Fin n → ℝ) :
    (∑ i, ∑ j, (Work.Diff.Alg.Pinch.qfA x y z w i j ^ 2
        + Work.Diff.Alg.Pinch.qfB x y z w i j ^ 2))
      = 2 * Work.Diff.Alg.Pinch.Cone.EF (Submission.Diff.Alg.Iso n) x y z w := by
  -- `qfA` and `qfB` are the real and imaginary parts of `ζᵢηⱼ - ζⱼηᵢ`
  have hq : ∀ i j, (qfA x y z w i j ^ 2 + qfB x y z w i j ^ 2)
      = (((x i * z j - y i * w j) - (x j * z i - y j * w i)) ^ 2
          + ((x i * w j + y i * z j) - (x j * w i + y j * z i)) ^ 2) := by
    intro i j
    simp only [qfA, qfB]
    ring
  simp only [hq]
  rw [chat_split, chat_sum_sq, chat_sum_cross, Cone.EF_iso]
  ring

end Work.Diff.Alg.Pinch
