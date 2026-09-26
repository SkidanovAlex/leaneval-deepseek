import Mathlib
import Submission.Work.SG.SellingDefs

/-!
# `Work.SG.int_conj_sum_invariant`

Integer analogue of `Work.SG.weyl_conj_sum_invariant` (which is stated over `ℝ`).

For a finite set `S` of integer `3 × 3` matrices, closed under multiplication, all of whose
determinants are units of `ℤ` (i.e. `±1`), and for `A ∈ S`, the "Weyl sum"
`∑_{B ∈ S} Bᵀ * B` is invariant under the conjugation-like action `Q ↦ Aᵀ * Q * A`.

The proof is the same reindexing argument as in the real case, using the nonsingular inverse
`A⁻¹ = A.det⁻¹ʳ • A.adjugate` of `Mathlib` (available over any `CommRing`, in particular over
`ℤ`), which behaves as a two-sided inverse precisely because `A.det ∈ ℤˣ`:

* right multiplication `B ↦ B * A` is injective on `S` (cancel `A` against `A⁻¹`);
* it maps `S` into itself by closure, hence is a bijection of `S` onto itself (cardinality);
* so `∑_{B ∈ S} (B A)ᵀ (B A) = ∑_{C ∈ S} Cᵀ C`, and the left-hand side equals
  `Aᵀ (∑_{B ∈ S} Bᵀ B) A` by distributivity and `(B A)ᵀ = Aᵀ Bᵀ`.
-/

namespace Work.SG

theorem int_conj_sum_invariant (S : Finset IMat)
    (hmul : ∀ A ∈ S, ∀ B ∈ S, A * B ∈ S)
    (hunit : ∀ A ∈ S, IsUnit A.det) (A : IMat) (hA : A ∈ S) :
    A.transpose * (∑ B ∈ S, B.transpose * B) * A = ∑ B ∈ S, B.transpose * B := by
  have hu : IsUnit A.det := hunit A hA
  -- Right multiplication by `A` is injective on `S` (as `A.det` is a unit).
  have hinj : Set.InjOn (fun B : IMat => B * A) ↑S := by
    intro B _ C _ hBC
    have hBC' : B * A = C * A := hBC
    calc B = B * A * A⁻¹ := (Matrix.mul_nonsing_inv_cancel_right (A := A) B hu).symm
      _ = C * A * A⁻¹ := by rw [hBC']
      _ = C := Matrix.mul_nonsing_inv_cancel_right (A := A) C hu
  -- the image of `S` under right multiplication by `A` is contained in `S`
  have hsub : S.image (fun B => B * A) ⊆ S := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨B, hB, rfl⟩
    exact hmul B hB A hA
  have hcard : (S.image (fun B => B * A)).card = S.card :=
    Finset.card_image_of_injOn hinj
  -- hence it is all of `S`
  have heq : S.image (fun B => B * A) = S :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  -- so summation over `S` may be reindexed by `B ↦ B * A`
  have hreindex : (∑ B ∈ S, (B * A).transpose * (B * A)) =
      ∑ C ∈ S, C.transpose * C := by
    have h1 := Finset.sum_image (s := S) (g := fun B : IMat => B * A)
      (f := fun C : IMat => C.transpose * C) hinj
    rw [heq] at h1
    exact h1.symm
  calc
    A.transpose * (∑ B ∈ S, B.transpose * B) * A
      = (A.transpose * (∑ B ∈ S, B.transpose * B)) * A := rfl
    _ = (∑ B ∈ S, A.transpose * (B.transpose * B)) * A := by
          rw [Finset.mul_sum]
    _ = ∑ B ∈ S, (A.transpose * (B.transpose * B)) * A := by
          rw [Finset.sum_mul]
    _ = ∑ B ∈ S, (B * A).transpose * (B * A) := by
          apply Finset.sum_congr rfl
          intro B _
          rw [Matrix.transpose_mul]
          noncomm_ring
    _ = ∑ C ∈ S, C.transpose * C := hreindex

end Work.SG
