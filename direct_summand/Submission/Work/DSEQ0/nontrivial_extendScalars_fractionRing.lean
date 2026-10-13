import Mathlib

namespace Work.DSEQ0

universe u

open scoped ChangeOfRings TensorProduct

theorem nontrivial_extendScalars_fractionRing {A : Type u} [CommRing A] [IsDomain A]
    (M : Type u) [CommRing M] [Algebra A M] (hinj : Function.Injective (algebraMap A M)) :
    Nontrivial ↥((ModuleCat.extendScalars (algebraMap A (FractionRing A))).obj (ModuleCat.of A M)) := by
  -- The localised module `S⁻¹M` (`S = nonZeroDivisors A`) is non-trivial: `1/1 ≠ 0`,
  -- because `1 ∈ M` is not killed by any `s ∈ S` (`algebraMap A M` is injective).
  have hne : (LocalizedModule.mk (1 : M) (1 : nonZeroDivisors A)) ≠ 0 := by
    intro h
    have h2 : (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (1 : M) = 0 := by
      rw [LocalizedModule.mkLinearMap_apply]; exact h
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)
      (LocalizedModule.mkLinearMap (nonZeroDivisors A) M)).mp h2
    have hs' : algebraMap A M (s : A) = 0 := by
      simpa [Submonoid.smul_def, Algebra.smul_def] using hs
    have hsz : (s : A) = 0 := by apply hinj; rw [hs', map_zero]
    exact (mem_nonZeroDivisors_iff_ne_zero.mp s.2) hsz
  have hP : Nontrivial (LocalizedModule (nonZeroDivisors A) M) :=
    Nontrivial.mk ⟨0, LocalizedModule.mk (1 : M) (1 : nonZeroDivisors A), hne.symm⟩
  -- Transport non-triviality across `S⁻¹M ≅ S⁻¹A ⊗[A] M`.
  have h : Nontrivial (TensorProduct A (FractionRing A) M) := by
    obtain ⟨x, y, hxy⟩ := hP
    refine ⟨(LocalizedModule.equivTensorProduct (nonZeroDivisors A) M) x,
      (LocalizedModule.equivTensorProduct (nonZeroDivisors A) M) y, fun hh => hxy ?_⟩
    exact (LocalizedModule.equivTensorProduct (nonZeroDivisors A) M).injective hh
  -- The carrier of `extendScalars` is the same tensor product, with the `A`-module structure
  -- obtained by restriction of scalars along `algebraMap A (FractionRing A)`; the two module
  -- structures agree (`Module.compHom` versus the localised module structure), so non-triviality
  -- transfers.
  have h' : Nontrivial (TensorProduct A
      ↥((ModuleCat.restrictScalars (algebraMap A (FractionRing A))).obj
        (ModuleCat.of (FractionRing A) (FractionRing A))) M) := by
    convert h using 1
    congr 1
    rw [show ((ModuleCat.restrictScalars (algebraMap A (FractionRing A))).obj
        (ModuleCat.of (FractionRing A) (FractionRing A))).isModule =
        Module.compHom (FractionRing A) (algebraMap A (FractionRing A)) from rfl]
    apply Module.ext'
    intro r m
    exact IsScalarTower.algebraMap_smul (R := A) (A := FractionRing A) r m
  exact h'

end Work.DSEQ0
