import Mathlib
import Submission.Work.CFT.Kummer.Defs

namespace Work.CFT.Kummer

/-- A totally real number field contains no primitive `p`-th root of unity for an odd prime `p`:
every embedding `K →+* ℂ` lands in `ℝ`, where the only roots of unity of odd order are trivial.
Hence `δ_{K,p} = 0` (Hajir–Maire–Ramakrishna, §"Some set up"). -/
theorem deltaK_eq_zero_of_totallyReal (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Work.CFT.Kummer.deltaK K p = 0 := by
  rw [deltaK_eq_zero_iff]
  rintro ⟨ζ, hζ⟩
  -- Pick an embedding `φ : K →+* ℂ`; since `K` is totally real it factors through `ℝ`.
  obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
  have hφ : NumberField.ComplexEmbedding.IsReal φ := NumberField.IsTotallyReal.complexEmbedding_isReal φ
  -- The image `η` of `ζ` in `ℝˣ` is again a primitive `p`-th root of unity.
  have hinj : Function.Injective (Units.map hφ.embedding.toMonoidHom) :=
    Units.map_injective (RingHom.injective hφ.embedding)
  have hprim : IsPrimitiveRoot (Units.map hφ.embedding.toMonoidHom ζ) p :=
    hζ.map_of_injective hinj
  set η : ℝˣ := Units.map hφ.embedding.toMonoidHom ζ with hη
  -- But the only real roots of unity are `±1`, and `-1` has even order, contradicting `p` odd.
  have hpow : (η : ℝ) ^ p = 1 := by
    have h1 := hprim.pow_eq_one
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  rcases (pow_eq_one_iff_of_ne_zero hp.ne_zero).mp hpow with h1 | ⟨h1, heven⟩
  · exact hprim.ne_one hp.one_lt (Units.ext h1)
  · exact (Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two hp2)) heven

end Work.CFT.Kummer
