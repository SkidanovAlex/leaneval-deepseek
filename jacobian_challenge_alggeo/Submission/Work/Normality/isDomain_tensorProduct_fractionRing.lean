import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normality

/-- The base change of a domain `A` (a flat algebra over a domain `P`) to the fraction field
of `P` is again a domain.

Proof sketch: `A ⊗[P] FractionRing P` is the localisation of `A` at the image `M` of the
nonzero divisors of `P` (`Localization.tensorLeftAlgEquiv` gives an `A`-algebra isomorphism
with `Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors P))`, and the
`IsLocalization` instance transfers along it).  Now `Module.Flat P A` makes
`algebraMap P A` injective (flat over a domain is torsion-free: tensor the injective
`algebraMap P (FractionRing P)` with the flat `A`), hence `M ≤ nonZeroDivisors A`
(because `A` is a domain, so a nonzero element is a nonzerodivisor); finally
`IsLocalization.isDomain_of_le_nonZeroDivisors` applies. -/
theorem isDomain_tensorProduct_fractionRing {P : Type*} [CommRing P] [IsDomain P]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra P A] [Module.Flat P A] :
    IsDomain (TensorProduct P A (FractionRing P)) := by
  -- Flatness over the domain `P` makes `algebraMap P A` injective: for `x ≠ 0` in `P`, `x` is a
  -- nonzerodivisor of `P`, so `x • ·` is injective on the flat module `A`; hence `x • 1 ≠ 0`.
  have hInj : Function.Injective (algebraMap P A) := fun x y hxy => by
    have hz : algebraMap P A (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    rcases eq_or_ne (x - y) 0 with h | h
    · rwa [sub_eq_zero] at h
    · exfalso
      have hmem : x - y ∈ nonZeroDivisors P := mem_nonZeroDivisors_iff_ne_zero.mpr h
      have hreg : IsSMulRegular A (x - y) := Module.Flat.isSMulRegular_of_nonZeroDivisors hmem
      have : (1 : A) = 0 := hreg (by simp [Algebra.smul_def, hz])
      exact one_ne_zero this
  -- The image `M` of the nonzerodivisors of `P` in `A` consists of nonzerodivisors of `A`.
  let M : Submonoid A := Algebra.algebraMapSubmonoid A (nonZeroDivisors P)
  have hle : M ≤ nonZeroDivisors A := by
    intro x hx
    have hx' : x ∈ Submonoid.map (algebraMap P A) (nonZeroDivisors P) := hx
    obtain ⟨p, hp, rfl⟩ := Submonoid.mem_map.mp hx'
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hp) (hInj (by rw [h, map_zero]))
  -- Thus the localisation of `A` at `M` is a domain, and `A ⊗[P] FractionRing P` is
  -- `A`-algebra isomorphic to it, so it is a domain as well.
  exact @MulEquiv.isDomain _ (Localization M) _ _
    (IsLocalization.isDomain_of_le_nonZeroDivisors (Localization M) hle)
    (Localization.tensorLeftAlgEquiv (nonZeroDivisors P) A).toRingEquiv.toMulEquiv

end Work.Normality
