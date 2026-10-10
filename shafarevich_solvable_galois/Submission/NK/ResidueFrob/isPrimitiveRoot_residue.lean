import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ResidueFrob

/-- A primitive `d`-th root of unity in a local ring remains a primitive `d`-th root of unity in
the residue field, provided the reduction map is injective on the `d`-torsion of the units
(hypothesis `hinj`, which for a residue field of characteristic prime to `d` is supplied by
`NK.ResidueFrob.rootOfUnity_eq_one_of_residue_eq_one`).

Proof: `residue ζ ^ d = residue (ζ ^ d) = 1`.  Conversely, if `residue ζ ^ l = 1`, then
`residue (ζ ^ l) = 1` and `(ζ ^ l) ^ d = (ζ ^ d) ^ l = 1`, so `hinj` gives `ζ ^ l = 1`, and
primitivity of `ζ` gives `d ∣ l`. -/
theorem isPrimitiveRoot_residue {R : Type*} [CommRing R] [IsLocalRing R] {d : ℕ}
    {ζ : R} (hζ : IsPrimitiveRoot ζ d)
    (hinj : ∀ w : R, w ^ d = 1 → IsLocalRing.residue R w = 1 → w = 1) :
    IsPrimitiveRoot (IsLocalRing.residue R ζ) d := by
  refine ⟨?_, ?_⟩
  · rw [← map_pow, hζ.pow_eq_one, map_one]
  · intro l hl
    have hl' : (ζ ^ l) ^ d = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hres : IsLocalRing.residue R (ζ ^ l) = 1 := by
      rw [map_pow]
      exact hl
    exact hζ.dvd_of_pow_eq_one l (hinj (ζ ^ l) hl' hres)

end NK.ResidueFrob
