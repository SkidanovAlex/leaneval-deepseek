import Mathlib
import Submission.Work.CFTLib.splitSetOf_density
import Submission.Work.CFTLib.splitSet_determines_field
import Submission.Work.CFTLib.splitSet_eq_imp_proportional
import Submission.Work.CFTLib.InvCharSetup
import Submission.Work.CFTLib.card_oneDim_submodules
import Submission.Work.Tower.Unramified.compositum_splits_completely_alt
import Submission.Work.CFTLib.Transport.isUnramified_algEquiv
import Submission.Work.CFTLib.Transport.splitsAt_algEquiv
import Submission.Work.CFTLib.Setup.finiteDimensional_fieldRange
import Submission.Work.CFTLib.Basic
import Submission.Work.CFTLib.Setup.charTransport

/-!
# The crux injection for `invChar_le_invCharSubmodule`: helper developments

This module collects the field-theoretic and group-theoretic ingredients of
`Work.CFTLib.exists_injective_oneDim_invChar`.
-/

open NumberField CategoryTheory
open scoped Classical

namespace Work.CFTLib

namespace InvCharCrux

variable {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field K']
  [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K']
  [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K] [IsGalois F K']

include F in
/-- `K'` is a finite extension of `K`. -/
theorem finiteDimensional_tower : FiniteDimensional K K' := Module.Finite.right (F := F) (K := K) (A := K')

include F in
/-- `K'/K` is Galois. -/
theorem isGalois_tower : IsGalois K K' := IsGalois.tower_top_of_isGalois (F := F) (K := K) (E := K')

/-- **Two finite Galois subextensions with the same completely split primes are equal.**
(Reformulation of `splitSet_determines_field` in terms of `splitsCompletelySet`.) -/
theorem splitsCompletelySet_determines_field (M₁ M₂ : IntermediateField K K')
    [FiniteDimensional K M₁] [FiniteDimensional K M₂]
    [IsGalois K ↥M₁] [IsGalois K ↥M₂]
    (h : splitsCompletelySet M₁ = splitsCompletelySet M₂) : M₁ = M₂ := by
  have hfd : FiniteDimensional K ↥(M₁ ⊔ M₂) := IntermediateField.finiteDimensional_sup M₁ M₂
  have hgal : IsGalois K ↥(M₁ ⊔ M₂) := isGalois_sup M₁ M₂
  have hdM := hasDirichletDensity_splitsCompletelySet (A := K') (M₁ ⊔ M₂)
  have hd1 := hasDirichletDensity_splitsCompletelySet (A := K') M₁
  have hd2 := hasDirichletDensity_splitsCompletelySet (A := K') M₂
  have hinter : splitsCompletelySet M₁ ∩ splitsCompletelySet M₂ = splitsCompletelySet M₁ := by
    rw [← h]; exact Set.inter_self _
  have hdM1 : NumberField.Set.HasDirichletDensity (splitsCompletelySet (M₁ ⊔ M₂))
      (1 / (Module.finrank K ↥M₁ : ℝ)) := by
    rw [splitsCompletelySet_sup_eq_inter, hinter]; exact hd1
  have hfr1 : Module.finrank K ↥M₁ = Module.finrank K ↥(M₁ ⊔ M₂) := by
    have h1 : (1 : ℝ) / (Module.finrank K ↥M₁ : ℝ) =
        (1 : ℝ) / (Module.finrank K ↥(M₁ ⊔ M₂) : ℝ) :=
      eq_of_hasDirichletDensity hdM1 hdM
    exact Nat.cast_injective (inv_inj.mp (by simpa only [one_div] using h1))
  have hM1 : M₁ = M₁ ⊔ M₂ := IntermediateField.eq_of_le_of_finrank_eq le_sup_left hfr1
  have hdM2 : NumberField.Set.HasDirichletDensity (splitsCompletelySet (M₁ ⊔ M₂))
      (1 / (Module.finrank K ↥M₂ : ℝ)) := by
    rw [splitsCompletelySet_sup_eq_inter, hinter, h]; exact hd2
  have hfr2 : Module.finrank K ↥M₂ = Module.finrank K ↥(M₁ ⊔ M₂) := by
    have h1 : (1 : ℝ) / (Module.finrank K ↥M₂ : ℝ) =
        (1 : ℝ) / (Module.finrank K ↥(M₁ ⊔ M₂) : ℝ) :=
      eq_of_hasDirichletDensity hdM2 hdM
    exact Nat.cast_injective (inv_inj.mp (by simpa only [one_div] using h1))
  have hM2 : M₂ = M₁ ⊔ M₂ := IntermediateField.eq_of_le_of_finrank_eq le_sup_right hfr2
  exact hM1.trans hM2.symm

end InvCharCrux

end Work.CFTLib


namespace Work.CFTLib.InvCharCrux

open NumberField

variable {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field K']
  [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K']
  [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K] [IsGalois F K']

/-- **The multiplicative character attached to an additive one.**  An additive character
`χ : Add(Cl(𝓞 K)) →+ ZMod p` is the same thing as a multiplicative character
`Cl(𝓞 K) →* Multiplicative (ZMod p)`; this is the conversion used to feed `χ` into the
class field interfaces. -/
noncomputable def toMulChar (p : ℕ) (χ : clInvariantChar F K p) :
    ClassGroup (𝓞 K) →* Multiplicative (ZMod p) where
  toFun c := Multiplicative.ofAdd ((χ : AddMonoidHom (Additive (ClassGroup (𝓞 K))) (ZMod p))
    (Additive.ofMul c))
  map_one' := by
    show Multiplicative.ofAdd ((χ : AddMonoidHom (Additive (ClassGroup (𝓞 K))) (ZMod p))
      (Additive.ofMul 1)) = 1
    rw [show Additive.ofMul (1 : ClassGroup (𝓞 K)) = 0 from rfl, map_zero]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd ((χ : AddMonoidHom (Additive (ClassGroup (𝓞 K))) (ZMod p))
      (Additive.ofMul (a * b))) = _
    rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl, map_add]
    rfl

@[simp]
theorem toMulChar_apply (p : ℕ) (χ : clInvariantChar F K p) (c : ClassGroup (𝓞 K)) :
    toMulChar p χ c = Multiplicative.ofAdd ((χ : AddMonoidHom (Additive (ClassGroup (𝓞 K)))
      (ZMod p)) (Additive.ofMul c)) := rfl

theorem toMulChar_eq_one_iff (p : ℕ) (χ : clInvariantChar F K p) (c : ClassGroup (𝓞 K)) :
    toMulChar p χ c = 1 ↔ (χ : AddMonoidHom (Additive (ClassGroup (𝓞 K))) (ZMod p))
      (Additive.ofMul c) = 0 := by
  rw [toMulChar_apply]
  exact Iff.rfl

theorem toMulChar_ne_one (p : ℕ) (χ : clInvariantChar F K p) (hχ : χ ≠ 0) :
    toMulChar p χ ≠ 1 := by
  intro h
  apply hχ
  ext c
  have h1 := (toMulChar_eq_one_iff p χ c).mp (by rw [h]; rfl : toMulChar p χ c = 1)
  exact h1

end Work.CFTLib.InvCharCrux

namespace Work.CFTLib.InvCharCrux

open NumberField

variable {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field K']
  [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K']
  [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K] [IsGalois F K']

/-- **Existence of the class field image in `K'`.**  For a nonzero additive character `χ` of
`clInvariantChar F K p`, the class field of the associated multiplicative character embeds into
`K'` over `K` (using the maximality hypothesis `hmax`), and we record its image together with the
splitting law, finiteness, Galois-ness, degree `p` and unramifiedness. -/
theorem exists_classFieldImage (p : ℕ) [Fact p.Prime] (hHCF : CFTLib.PClassFieldArtin)
    (hmax : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
      [IsGalois K L], (∀ a b : L ≃ₐ[K] L, a * b = b * a) → IsPGroup p (L ≃ₐ[K] L) →
      CFTLib.IsUnramified K L → Nonempty (L →ₐ[K] K'))
    (χ : clInvariantChar F K p) (hχ : χ ≠ 0) :
    ∃ M : IntermediateField K K', FiniteDimensional K M ∧ NumberField ↥M ∧ IsGalois K ↥M ∧
      Module.finrank K ↥M = p ∧ Work.Tower.IsUnramifiedExtensionForallPrimes K ↥M ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        Ideal.inertiaDegIn v.asIdeal (𝓞 ↥M) = 1 ↔
          (χ : AddMonoidHom (Additive (ClassGroup (𝓞 K))) (ZMod p))
            (Additive.ofMul (primeCls v)) = 0) := by
  classical
  obtain ⟨L, hFld, hNF, hAlg, hFD, hgal, hrank, hunr, hlaw⟩ :=
    hHCF K p (toMulChar p χ) (toMulChar_ne_one p χ hχ)
  letI := hFld
  letI := hNF
  letI := hAlg
  letI := hFD
  letI := hgal
  have hcard : Nat.card (L ≃ₐ[K] L) = p := by
    rw [IsGalois.card_aut_eq_finrank]
    exact hrank
  have hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a := by
    haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card hcard
    intro a b
    exact IsMulCommutative.is_comm.comm a b
  have hpgrp : IsPGroup p (L ≃ₐ[K] L) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hcard, pow_one]
  obtain ⟨ι⟩ := hmax L hcomm hpgrp hunr
  haveI hfdM : FiniteDimensional K ↥(ι.fieldRange) := Setup.finiteDimensional_fieldRange ι
  haveI hnfM : NumberField ↥(ι.fieldRange) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := K) (K' := K')
      ι.fieldRange
  haveI hgalM : IsGalois K ↥(ι.fieldRange) := IsGalois.of_algEquiv ι.equivFieldRange
  refine ⟨ι.fieldRange, hfdM, hnfM, hgalM, ?_, ?_, ?_⟩
  · rw [(ι.equivFieldRange.toLinearEquiv.finrank_eq).symm, hrank]
  · refine Work.CFTLib.forallPrimes_of_differentIdeal ?_
    exact (Work.CFTLib.Transport.isUnramified_algEquiv (K := K) ι.equivFieldRange hunr).1
  · intro v
    rw [← Work.CFTLib.Transport.inertiaDegIn_algEquiv_eq (K := K) (L := L)
      (L' := ↥(ι.fieldRange)) v ι.equivFieldRange, hlaw v]
    rw [toMulChar_eq_one_iff]
    simp only [primeCls]

end Work.CFTLib.InvCharCrux

namespace Work.CFTLib.InvCharCrux
open NumberField
variable {F K K' : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field K']
  [NumberField K'] [Algebra F K] [Algebra F K'] [Algebra K K'] [IsScalarTower F K K']
  [FiniteDimensional F K] [FiniteDimensional F K'] [IsGalois F K] [IsGalois F K']
end Work.CFTLib.InvCharCrux
