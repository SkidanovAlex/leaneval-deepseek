import Mathlib
import Submission.Work.QuadraticFields.Certificate

/-!
# The certificate roots generate the multiquadratic field `M`

The field `M = ℚ(√-3, √5, √13, √17, √29, √37)` of the certificate is *defined* as the
subfield `ℚ(√a : a ∈ certPrimes)` of `AlgebraicClosure ℚ`, and `certM` is that field viewed
as a type.  The elements `certRoot a ∈ certM` are the chosen square roots of the certificate
primes inside `certM`; the present lemma records that they generate `certM` as a `ℚ`-algebra,
i.e. that the quadratic subfields `ℚ⟮certRoot a⟯` really decompose `certM`.

The proof transports the defining property of `multiQuad certPrimesQ` along the structural
map `certM → AlgebraicClosure ℚ`.  For an intermediate field `S ≤ certM` the image
`S.map (certM).val` is an intermediate field of `AlgebraicClosure ℚ`, and `S` is recovered
from it, so `S = ⊤` may be tested after applying `.val`: the map `(certM).val` is injective
with range exactly `L = multiQuad certPrimesQ`.  On generators, each of the square roots
`sqrtVal (a : ℚ)`, `a ∈ certPrimes`, that generate `L` is the image under `(certM).val` of
the corresponding `certRoot a ∈ certM` — indeed `certRoot a = ⟨sqrtVal (a : ℚ), _⟩` by
`certRoot_of_mem`.  Hence `(multiquadSub certPrimes certRoot).map (certM).val = L` as well,
and injectivity of `(certM).val` gives the claim.

## Main result

* `Work.QuadraticFields.certRoot_generates`:
  `multiquadSub certPrimes certRoot = ⊤`.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

noncomputable section

/-- `multiquadSub certPrimes certRoot` is the field generated inside `certM` by the chosen
square roots of the six certificate primes, so it is the whole of `certM`. -/
theorem certRoot_generates : multiquadSub certPrimes certRoot = ⊤ := by
  -- View `certM` as the intermediate field `L = multiQuad certPrimesQ ⊆ AlgebraicClosure ℚ`.
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := multiQuad certPrimesQ
  -- The structural map `L.val : certM →ₐ[ℚ] AlgebraicClosure ℚ` is injective, so it suffices
  -- to compare images: `(multiquadSub ...).map L.val = ⊤.map L.val = L`.
  refine IntermediateField.map_injective L.val ?_
  have hgen : (multiquadSub certPrimes certRoot).map (L.val) = L := by
    rw [multiquadSub, IntermediateField.adjoin_map]
    congr 1
    -- `L.val ∘ certRoot` and `sqrtVal` have the same image: `certPrimesQ` is the image of
    -- `certPrimes` in `ℚ`, and `L.val (certRoot a) = sqrtVal (a : ℚ)` by `certRoot_of_mem`.
    ext y
    simp only [Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨(a : ℚ), Finset.mem_image.mpr ⟨a, ha, rfl⟩, by rw [certRoot_of_mem ha]; rfl⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
      exact ⟨certRoot a, ⟨a, ha, rfl⟩, by rw [certRoot_of_mem ha]; rfl⟩
  rw [hgen, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]

end

end Work.QuadraticFields
