import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Rotating the Kulkarni–Nomizu square of the identity tensor

For an arbitrary `n × n` matrix `A` (no orthogonality is needed),

`rot A (knProd (id2 n) (id2 n)) = knProd (A * Aᵀ) (A * Aᵀ)`.

Since `knProd (id2 n) (id2 n) = 2 • Iso n`, the left-hand side is `2 • rot A (Iso n)`, and for
`Iso n i j k l = δᵢₖ δⱼₗ − δᵢₗ δⱼₖ` the four-fold sum

`∑ a b c d, A i a * A j b * A k c * A l d * (δ_{ac} δ_{bd} − δ_{ad} δ_{bc})`

factors as `B i k * B j l − B i l * B j k` with `B = A * Aᵀ` (each of the two terms is a product of
an `(a,c)`-contraction and a `(b,d)`-contraction).  The right-hand side is
`knProd B B i j k l = 2 (B i k B j l − B i l B j k)`, so the two agree.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary summation lemmas -/

/-- `Iso` expressed through the Kronecker delta `id2` (definitional). -/
lemma Iso_eq_id2' (i j k l : Fin n) :
    Iso n i j k l = id2 n i k * id2 n j l - id2 n i l * id2 n j k := rfl

/-- Contraction of a vector against the Kronecker delta: `∑ c, f c · δ_{a c} = f a`. -/
lemma sum_mul_id2_l (f : Fin n → ℝ) (a : Fin n) : (∑ c, f c * id2 n a c) = f a := by
  rw [Finset.sum_eq_single a]
  · simp [id2]
  · intro c _ hc
    have h : a ≠ c := fun hh => hc hh.symm
    simp [id2, h]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- Double contraction: `∑ a ∑ c, f a * g c * δ_{a c} = ∑ a, f a * g a`. -/
lemma sum_ai_id2 (f g : Fin n → ℝ) : (∑ a, ∑ c, f a * g c * id2 n a c) = ∑ a, f a * g a := by
  apply Finset.sum_congr rfl; intro a _
  exact sum_mul_id2_l (fun c => f a * g c) a

/-- A four-fold sum of a product of an `(a,c)`-factor and a `(b,d)`-factor factors into the product
of the two double sums. -/
lemma sum4_factor (f g : Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a c * g b d) = (∑ a, ∑ c, f a c) * (∑ b, ∑ d, g b d) := by
  have hswap : (∑ a, ∑ b, ∑ c, ∑ d, f a c * g b d)
      = ∑ a, ∑ c, ∑ b, ∑ d, f a c * g b d := by
    apply Finset.sum_congr rfl; intro a _
    exact Finset.sum_comm
  rw [hswap, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.mul_sum]

/-- Variant of `sum4_factor` with the two contraction patterns crossed. -/
lemma sum4_factor' (f g : Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a d * g b c) = (∑ a, ∑ d, f a d) * (∑ b, ∑ c, g b c) := by
  rw [show (∑ a, ∑ b, ∑ c, ∑ d, f a d * g b c)
      = (∑ a, ∑ b, ∑ c, ∑ d, f a c * g b d) from by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    exact Finset.sum_comm]
  exact sum4_factor f g

/-! ## The rotation of the round-sphere tensor -/

/-- `rot A (Iso n)` in frame components: the deltas contract the `A`'s into the matrix
`B = A * Aᵀ`, leaving the antisymmetrised `Iso` pattern `BᵢₖBⱼₗ − BᵢₗBⱼₖ`. -/
lemma rot_Iso (A : Matrix (Fin n) (Fin n) ℝ) (i j k l : Fin n) :
    rot A (Iso n) i j k l
      = (∑ x, A i x * A k x) * (∑ y, A j y * A l y)
        - (∑ x, A i x * A l x) * (∑ y, A j y * A k y) := by
  simp only [rot, Iso_eq_id2']
  -- Split each summand into its `(a,c)`-part and its `(b,d)`-part, after pairing up the
  -- two copies of the `δ_{ac} δ_{bd}` term (resp. `δ_{ad} δ_{bc}` term) that `knProd` produces.
  have hterm : ∀ a b c d : Fin n,
      A i a * A j b * A k c * A l d * (id2 n a c * id2 n b d - id2 n a d * id2 n b c)
      = (A i a * A k c * id2 n a c) * (A j b * A l d * id2 n b d)
        - (A i a * A l d * id2 n a d) * (A j b * A k c * id2 n b c) := by
    intro a b c d; ring
  simp only [hterm]
  simp only [Finset.sum_sub_distrib]
  rw [sum4_factor (fun a c => A i a * A k c * id2 n a c) (fun b d => A j b * A l d * id2 n b d),
    sum4_factor' (fun a d => A i a * A l d * id2 n a d) (fun b c => A j b * A k c * id2 n b c)]
  simp only [sum_ai_id2]

/-! ## The main identity -/

theorem rot_knProd_id2 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Submission.Diff.Alg.rot A (Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.id2 n) (Work.Diff.Alg.Pinch.id2 n))
      = Work.Diff.Alg.Pinch.knProd (A * A.transpose) (A * A.transpose) := by
  funext i j k l
  -- `knProd id2 id2 = 2 • Iso`: both sides are the antisymmetrised delta pattern.
  have hIso : knProd (id2 n) (id2 n) = (2 : ℝ) • Iso n := by
    funext a b c d
    simp only [knProd, Pi.smul_apply, smul_eq_mul, Iso_eq_id2']
    ring
  rw [hIso]
  -- `rot` is linear in its tensor argument.
  have hrot : rot A ((2 : ℝ) • Iso n) i j k l = 2 * rot A (Iso n) i j k l := by
    simp only [rot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    ring
  rw [hrot, rot_Iso]
  simp only [knProd, Matrix.mul_apply, Matrix.transpose_apply]
  ring

end Work.Diff.Alg.Pinch
