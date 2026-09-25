import Mathlib
import Submission.Work.Tower.CyclotomicBase.Basic
import Submission.Work.Tower.CyclotomicBase.finrank_Ffield_eq_three
import Submission.Work.Tower.CubicDiscriminant

set_option linter.style.haveILetI false

namespace Work.Tower.CyclotomicBase

/-- The discriminant of the cubic field `F` cut out by the product character `χ₁⋯χ_ℓ` is a
perfect square in `ℤ`.  Indeed, `F/ℚ` is Galois of degree `3`, so the Vandermonde determinant
(`exists_sq_eq_algebraMap_discr`) exhibits a square root of `disc F` inside `F`; taking norms
shows `(disc F) ^ 3 = (disc F) ^ [F : ℚ]` is a square in `ℚ`, hence `disc F` is a square in `ℚ`,
hence in `ℤ`. -/
theorem isSquare_natAbs_discr_Ffield {ℓ : ℕ} (hℓ : 0 < ℓ) (r : Fin ℓ → ℕ) (hr : ∀ i, Nat.Prime (r i))
    (hr3 : ∀ i, r i % 3 = 1) (hrinj : Function.Injective r) [NeZero (D r)] :
    IsSquare (NumberField.discr ↥(Ffield r hr hr3)).natAbs := by
  haveI : IsGalois ℚ ↥(Ffield r hr hr3) := isGalois_Ffield r hr hr3
  have h3 : Module.finrank ℚ ↥(Ffield r hr hr3) = 3 :=
    finrank_Ffield_eq_three hℓ r hr hr3 hrinj
  obtain ⟨d, hd⟩ := Work.Tower.exists_sq_eq_algebraMap_discr ↥(Ffield r hr hr3)
  have hsq3 : IsSquare ((NumberField.discr ↥(Ffield r hr hr3) : ℚ) ^ 3) := by
    refine ⟨Algebra.norm ℚ d, ?_⟩
    have h := congrArg (Algebra.norm ℚ) hd
    simp only [map_pow] at h
    rw [Algebra.norm_algebraMap, h3] at h
    rw [← h, pow_two]
  have hsq : IsSquare ((NumberField.discr ↥(Ffield r hr hr3) : ℚ)) := by
    obtain ⟨q, hq⟩ := hsq3
    have hx0' : (NumberField.discr ↥(Ffield r hr hr3) : ℚ) ≠ 0 := by
      rw [Int.cast_ne_zero]; exact NumberField.discr_ne_zero _
    refine ⟨q / (NumberField.discr ↥(Ffield r hr hr3) : ℚ), ?_⟩
    field_simp
    nlinarith [hq]
  have hsqZ : IsSquare (NumberField.discr ↥(Ffield r hr hr3)) := Rat.isSquare_intCast_iff.mp hsq
  obtain ⟨m, hm'⟩ := hsqZ
  rw [hm', Int.natAbs_mul]
  exact ⟨m.natAbs, rfl⟩

end Work.Tower.CyclotomicBase
