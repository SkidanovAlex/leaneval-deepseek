import Mathlib
import Submission.Work.KT.Fund.map_orthProj

namespace Work.KT.Fund

noncomputable section

/-- Naturality of the Murray–von Neumann data `(BᴴB)⁻¹Bᴴ` under a ring homomorphism commuting
with `star`. -/
theorem map_witness {n : ℕ} {R S : Type} [CommRing R] [Star R] [CommRing S] [Star S]
    (φ : R →+* S) (hφ : Function.Semiconj ⇑φ star star)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n) R) (h : IsUnit (B.conjTranspose * B)) :
    (Ring.inverse (B.conjTranspose * B) * B.conjTranspose).map ⇑φ
      = Ring.inverse ((B.map ⇑φ).conjTranspose * (B.map ⇑φ)) * (B.map ⇑φ).conjTranspose := by
  have hgram : (B.conjTranspose * B).map ⇑φ
      = (B.map ⇑φ).conjTranspose * (B.map ⇑φ) := by
    rw [Matrix.map_mul, Matrix.conjTranspose_map ⇑φ hφ]
  rw [Matrix.map_mul, Matrix.map_ringInverse φ (B.conjTranspose * B) h, hgram,
    Matrix.conjTranspose_map ⇑φ hφ]

end

end Work.KT.Fund

