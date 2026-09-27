import Mathlib
import Submission.Work.KT.Fund.Clutch

namespace Work.KT.Fund

open Matrix

noncomputable section

/-- `Ring.inverse` (the "inverse if invertible, else `0`" operation) commutes with the entrywise
application of a ring homomorphism to a square matrix, on the locus of invertible matrices. -/
lemma Matrix.map_ringInverse {ι : Type} [Fintype ι] [DecidableEq ι]
    {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (M : Matrix ι ι R) (hM : IsUnit M) :
    (Ring.inverse M).map ⇑φ = Ring.inverse (M.map ⇑φ) := by
  obtain ⟨u, rfl⟩ := hM
  rw [Ring.inverse_unit u]
  let v : (Matrix ι ι S)ˣ :=
    { val := (u : Matrix ι ι R).map ⇑φ
      inv := ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R).map ⇑φ
      val_inv := by
        rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ φ.map_zero φ.map_one]
      inv_val := by
        rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ φ.map_zero φ.map_one] }
  have hv : Ring.inverse ((u : Matrix ι ι R).map ⇑φ) =
      (((v⁻¹ : (Matrix ι ι S)ˣ) : Matrix ι ι S)) := by
    rw [show ((u : Matrix ι ι R).map ⇑φ) = (v : Matrix ι ι S) from rfl, Ring.inverse_unit]
  rw [hv]
  rfl

/-- The orthogonal projection `B (Bᴴ B)⁻¹ Bᴴ` is natural in the coefficients: for a ring
homomorphism `φ` commuting with `star`, the entrywise image of the projection onto the image of
`B` is the projection onto the image of `B.map φ`. -/
theorem map_orthProj {n : ℕ} {R S : Type} [CommRing R] [StarRing R] [CommRing S] [StarRing S]
    (φ : R →+* S) (hφ : Function.Semiconj ⇑φ star star)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) (hQ : IsUnit (B.conjTranspose * B)) :
    (Work.KT.Fund.orthProj R B).map ⇑φ = Work.KT.Fund.orthProj S (B.map ⇑φ) := by
  unfold Work.KT.Fund.orthProj
  rw [Matrix.map_mul, Matrix.map_mul]
  rw [Matrix.map_ringInverse φ (B.conjTranspose * B) hQ]
  have hmul2 : (B.conjTranspose * B).map ⇑φ = (B.map ⇑φ).conjTranspose * (B.map ⇑φ) := by
    rw [Matrix.map_mul, Matrix.conjTranspose_map ⇑φ hφ]
  rw [hmul2, Matrix.conjTranspose_map ⇑φ hφ]

end

end Work.KT.Fund
