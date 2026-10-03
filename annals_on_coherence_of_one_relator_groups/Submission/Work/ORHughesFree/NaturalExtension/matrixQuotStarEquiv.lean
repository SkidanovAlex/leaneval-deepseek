import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.matrixQuotientDefs

namespace Work.ORHughesFree.NaturalExtension

/-- The entrywise quotient map on matrices is surjective. -/
theorem matrixQuotMap_surjective {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided] (n : ℕ) :
    Function.Surjective (matrixQuotMap I n) := by
  intro A
  refine ⟨fun i j => (A i j).out, ?_⟩
  ext i j
  exact Ideal.Quotient.mk_out (A i j)

/-- The kernel of the entrywise quotient map is stable under the transpose-involution of
matrices, whenever the ideal is stable under `star`. -/
theorem star_mem_ker_matrixQuotMap {R : Type*} [Ring R] [StarRing R] (I : Ideal R)
    [I.IsTwoSided] (hI : ∀ x ∈ I, star x ∈ I) (n : ℕ) :
    ∀ y ∈ RingHom.ker (matrixQuotMap I n), star y ∈ RingHom.ker (matrixQuotMap I n) := by
  intro N hN
  rw [RingHom.mem_ker] at hN ⊢
  ext i j
  show Ideal.Quotient.mk I (star N i j) = 0
  rw [Matrix.star_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI _ (Ideal.Quotient.eq_zero_iff_mem.mp
    (by simpa using congrFun (congrFun hN j) i)))

theorem matrixQuotStarEquiv {R : Type*} [Ring R] [StarRing R] (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ x ∈ I, star x ∈ I) (n : ℕ) :
    ∃ e : Matrix (Fin n) (Fin n) R ⧸ RingHom.ker (matrixQuotMap I n) ≃+*
          Matrix (Fin n) (Fin n) (R ⧸ I),
      (∀ M : Matrix (Fin n) (Fin n) R,
        e (Ideal.Quotient.mk _ M) = matrixQuotMap I n M) ∧
      (∀ x : Matrix (Fin n) (Fin n) R ⧸ RingHom.ker (matrixQuotMap I n),
        e (starQuot (RingHom.ker (matrixQuotMap I n)) x) =
          Matrix.of (fun i j => starQuot I (e x j i))) := by
  have hsurj := matrixQuotMap_surjective I n
  have hK := star_mem_ker_matrixQuotMap I hI n
  refine ⟨(matrixQuotMap I n).quotientKerEquivOfSurjective hsurj, ?_, ?_⟩
  · intro M
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hsurj M
  · intro x
    obtain ⟨N, rfl⟩ := Ideal.Quotient.mk_surjective (I := RingHom.ker (matrixQuotMap I n)) x
    rw [starQuot_mk (RingHom.ker (matrixQuotMap I n)) hK N]
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk hsurj (star N)]
    ext i j
    show Ideal.Quotient.mk I (star N i j) = starQuot I (matrixQuotMap I n N j i)
    rw [Matrix.star_apply, matrixQuotMap_apply, starQuot_mk I hI (N j i)]

end Work.ORHughesFree.NaturalExtension
