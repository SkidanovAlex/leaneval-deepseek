import Mathlib

/-!
# `Work.SG.weyl_conj_sum_invariant`

If `P` is a finite set of invertible real `n × n` matrices closed under multiplication, and
`A ∈ P`, then the "Weyl sum" `S = ∑_{B ∈ P} Bᵀ B` is invariant under the conjugation-like
action `S ↦ Aᵀ S A`.

The point is that right multiplication by `A` is a bijection of the finite set `P`: it is
injective (because `A` is invertible) and its image lies in `P`, whence equality by
cardinality.  Hence `∑_{B ∈ P} (B A)ᵀ (B A) = ∑_{C ∈ P} Cᵀ C`, and the left-hand side is
exactly `Aᵀ (∑_{B ∈ P} Bᵀ B) A` by bilinearity and `(B A)ᵀ = Aᵀ Bᵀ`.
-/

namespace Work.SG

theorem weyl_conj_sum_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (P : Finset (Matrix n n ℝ)) (hmul : ∀ A ∈ P, ∀ B ∈ P, A * B ∈ P)
    (hunit : ∀ A ∈ P, A.det ≠ 0) (A : Matrix n n ℝ) (hA : A ∈ P) :
    Matrix.transpose A * (∑ B ∈ P, Matrix.transpose B * B) * A =
      ∑ B ∈ P, Matrix.transpose B * B := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr (hunit A hA)
  -- Right multiplication by `A` is injective on `P` (as `A` is invertible).
  have hinj : Set.InjOn (fun B : Matrix n n ℝ => B * A) ↑P := by
    intro B _ C _ hBC
    have hBC' : B * A = C * A := hBC
    calc B = B * A * A⁻¹ := (Matrix.mul_nonsing_inv_cancel_right (A := A) B hu).symm
      _ = C * A * A⁻¹ := by rw [hBC']
      _ = C := Matrix.mul_nonsing_inv_cancel_right (A := A) C hu
  -- the image of `P` under right multiplication by `A` is contained in `P`
  have hsub : P.image (fun B => B * A) ⊆ P := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨B, hB, rfl⟩
    exact hmul B hB A hA
  have hcard : (P.image (fun B => B * A)).card = P.card :=
    Finset.card_image_of_injOn hinj
  -- hence it is all of `P`
  have heq : P.image (fun B => B * A) = P :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  -- so summation over `P` may be reindexed by `B ↦ B * A`
  have hreindex : (∑ B ∈ P, Matrix.transpose (B * A) * (B * A)) =
      ∑ C ∈ P, Matrix.transpose C * C := by
    have h1 := Finset.sum_image (s := P) (g := fun B : Matrix n n ℝ => B * A)
      (f := fun C : Matrix n n ℝ => Matrix.transpose C * C) hinj
    rw [heq] at h1
    exact h1.symm
  calc
    Matrix.transpose A * (∑ B ∈ P, Matrix.transpose B * B) * A
      = (Matrix.transpose A * (∑ B ∈ P, Matrix.transpose B * B)) * A := rfl
    _ = (∑ B ∈ P, Matrix.transpose A * (Matrix.transpose B * B)) * A := by
          rw [Finset.mul_sum]
    _ = ∑ B ∈ P, (Matrix.transpose A * (Matrix.transpose B * B)) * A := by
          rw [Finset.sum_mul]
    _ = ∑ B ∈ P, Matrix.transpose (B * A) * (B * A) := by
          apply Finset.sum_congr rfl
          intro B _
          rw [Matrix.transpose_mul]
          noncomm_ring
    _ = ∑ C ∈ P, Matrix.transpose C * C := hreindex

end Work.SG
