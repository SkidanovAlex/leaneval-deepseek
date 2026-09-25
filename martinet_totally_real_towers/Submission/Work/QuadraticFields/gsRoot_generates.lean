import Mathlib
import Submission.Work.QuadraticFields.CertificateReal

/-!
# The certificate roots `gsRoot` generate the multiquadratic field `gsM`

This is the totally real counterpart of `Work.QuadraticFields.certRoot_generates`: the field
`gsM = ℚ(√5, √13, √17, √29, √37, √41, √53)` is *defined* as the subfield
`ℚ(√a : a ∈ gsPrimes)` of `AlgebraicClosure ℚ`, and `gsM` is that field viewed as a type.  The
elements `gsRoot a ∈ gsM` are the chosen square roots of the certificate primes inside `gsM`; the
present lemma records that they generate `gsM` as a `ℚ`-algebra, i.e. that the quadratic subfields
`ℚ⟮gsRoot a⟯` really decompose `gsM`.

## Main result

* `Work.QuadraticFields.gsRoot_generates`:
  `multiquadSub gsPrimes gsRoot = ⊤`.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

noncomputable section

/-- `multiquadSub gsPrimes gsRoot` is the field generated inside `gsM` by the chosen square roots
of the seven certificate primes, so it is the whole of `gsM`. -/
theorem gsRoot_generates : multiquadSub gsPrimes gsRoot = ⊤ := by
  -- View `gsM` as the intermediate field `L = multiQuad gsPrimesQ ⊆ AlgebraicClosure ℚ`.
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := multiQuad gsPrimesQ
  -- The structural map `L.val : gsM →ₐ[ℚ] AlgebraicClosure ℚ` is injective, so it suffices to
  -- compare images: `(multiquadSub ...).map L.val = ⊤.map L.val = L`.
  refine IntermediateField.map_injective L.val ?_
  have hgen : (multiquadSub gsPrimes gsRoot).map (L.val) = L := by
    rw [multiquadSub, IntermediateField.adjoin_map]
    congr 1
    ext y
    simp only [Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨(a : ℚ), Finset.mem_image.mpr ⟨a, ha, rfl⟩, by rw [gsRoot_of_mem ha]; rfl⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨gsRoot a, ⟨a, ha, rfl⟩, by rw [gsRoot_of_mem ha]; rfl⟩
  rw [hgen, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]

end

end Work.QuadraticFields
