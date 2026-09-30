import Mathlib
import Submission.Work.Cohomology.uctDual
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.uctDefs
import Submission.Work.Pi6.EFACTS.tuctDefs
import Submission.Work.Pi6.EFACTS.coeffConnectingIso
import Submission.Work.Pi6.EFACTS.homComplexInjective
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The torsion universal coefficient theorem for `Hom(-, ℤ)`

For a chain complex `C` of free `ℤ`-modules whose homology in degrees `n` and `n-1` is torsion,
the `n`-th cohomology of the dual complex `Hom(C, ℤ)` is the Pontryagin dual of `H_{n-1}(C)`:
`Hⁿ(Hom(C,ℤ)) ≅ Hom(H_{n-1}(C), ℚ/ℤ)`.

The proof is the classical one: from the short exact coefficient sequence
`0 → Hom(C,ℤ) → Hom(C,ℚ) → Hom(C,ℚ/ℤ) → 0` (exact because every `Cₖ` is free) one gets the long
exact sequence
`H^{n-1}(Hom(C,ℚ)) → H^{n-1}(Hom(C,ℚ/ℤ)) → Hⁿ(Hom(C,ℤ)) → Hⁿ(Hom(C,ℚ))`,
whose two outer terms vanish because `ℚ` is torsion free: `Hᵏ(Hom(C,ℚ)) ≅ Hom(Hₖ(C), ℚ) = 0`.
Finally `H^{n-1}(Hom(C,ℚ/ℤ)) ≅ Hom(H_{n-1}(C), ℚ/ℤ)` because `Hom(-,ℚ/ℤ)` is exact (`ℚ/ℤ` is
an injective `ℤ`-module).
-/

set_option backward.isDefEq.respectTransparency false

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EFACTS

noncomputable section

/-- A `ℤ`-linear functional on a torsion module with values in `ℚ` is zero. -/
theorem subsingleton_hom_rat_of_torsion (C : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (htors : ∀ x : ↥(C.homology k), ∃ N : ℕ, 0 < N ∧ N • x = 0) :
    Subsingleton (↥(C.homology k) →ₗ[ℤ] ℚ) := by
  refine ⟨fun f g => ?_⟩
  have hzero : ∀ (f : ↥(C.homology k) →ₗ[ℤ] ℚ) (x : ↥(C.homology k)), f x = 0 := by
    intro f x
    obtain ⟨N, hNpos, hNx⟩ := htors x
    have h1 : N • f x = 0 := by
      rw [← map_nsmul, hNx, map_zero]
    have h2 : (N : ℚ) * f x = 0 := by
      simpa [nsmul_eq_mul] using h1
    have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hNpos)
    exact (mul_eq_zero.mp h2).resolve_left hN'
  ext x
  rw [hzero f x, hzero g x]

/-- Cohomology of `C` with coefficients in `ℚ` vanishes in degrees where the homology is
torsion. -/
theorem isZero_rat_homology (C : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (htors : ∀ x : ↥(C.homology k), ∃ N : ℕ, 0 < N ∧ N • x = 0) :
    IsZero ((homComplex ℚ C).homology k) := by
  haveI : Module.Injective ℤ ℚ := module_injective_rat
  obtain ⟨e⟩ := homComplexInjective ℚ C k
  have hI : IsZero (ModuleCat.of ℤ (↥(C.homology k) →ₗ[ℤ] ℚ)) :=
    ModuleCat.isZero_iff_subsingleton.mpr (subsingleton_hom_rat_of_torsion C k htors)
  exact hI.of_iso e

theorem uctTorsion (C : ChainComplex (ModuleCat ℤ) ℕ) (hfree : ∀ k : ℕ, Module.Free ℤ ↥(C.X k))
    (n : ℕ) (hn : 1 ≤ n)
    (htn : ∀ x : ↥(C.homology n), ∃ N : ℕ, 0 < N ∧ N • x = 0)
    (htn1 : ∀ x : ↥(C.homology (n - 1)), ∃ N : ℕ, 0 < N ∧ N • x = 0) :
    Nonempty ((Work.Cohomology.dualComplex ℤ C).homology n ≃ₗ[ℤ]
      (↥(C.homology (n - 1)) →ₗ[ℤ] AddCircle (1 : ℚ))) := by
  rw [← homComplex_int_eq_dualComplex C]
  haveI h1 : IsZero ((homComplex ℚ C).homology (n - 1)) :=
    isZero_rat_homology C (n - 1) htn1
  haveI h2 : IsZero ((homComplex ℚ C).homology n) := isZero_rat_homology C n htn
  obtain ⟨eδ⟩ := coeffConnectingIso C hfree n hn h1 h2
  haveI : Module.Injective ℤ (AddCircle (1 : ℚ)) := module_injective_qz
  obtain ⟨eInj⟩ := homComplexInjective (AddCircle (1 : ℚ)) C (n - 1)
  exact ⟨(Work.Cohomology.uctIsoToLinearEquiv eδ).symm.trans
    (Work.Cohomology.uctIsoToLinearEquiv eInj)⟩

end

end Work.Pi6.EFACTS
