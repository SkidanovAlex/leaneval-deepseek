import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum
import Submission.Commons.NumberTheory.RamificationInertia.exists_map_galRestrict_eq
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Uniqueness of the Frobenius element at an unramified prime

Let `L/K` be a finite Galois extension of number fields, `p` a finite place of `K` and
`P₁`, `P₂` places of `L` over `p` which are unramified over `p` (`e(Pᵢ|p) = 1`).  If
`Gal(L/K)` is abelian and `σᵢ ∈ Gal(L/K)` acts on the residue field `𝓞 L / Pᵢ` as the
`n`-th power map, then `σ₁ = σ₂`.

The mathematical content is: for an unramified place the inertia group is trivial, so the
decomposition group embeds into the group of automorphisms of the residue field extension
(`eq_of_residue_mk_eq`); on the other hand the Frobenius elements at the different places
over `p` are conjugate, and in an abelian group conjugate elements are equal.
-/

namespace Commons.NumberTheory.NumberField

open IsDedekindDomain

namespace FrobeniusEqOfCommute

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The action of the Galois group on the ring of integers (the instance coming from the
`ℤ`-integral closure) agrees with `galRestrict`. -/
lemma smul_ringOfIntegers_eq_galRestrict (σ : Gal(L/K)) (x : NumberField.RingOfIntegers L) :
    σ • x = galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ x := by
  apply IsIntegralClosure.algebraMap_injective (NumberField.RingOfIntegers L)
    (NumberField.RingOfIntegers K) L
  rw [algebraMap_galRestrict_apply]
  rfl

/-- `galRestrict τ` undoes `galRestrict τ⁻¹` (obvious, but `galRestrict` unfolds badly). -/
lemma galRestrict_apply_apply_inv (τ : Gal(L/K)) (x : NumberField.RingOfIntegers L) :
    galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) τ
      (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) τ⁻¹ x) = x := by
  simp

/-- If two elements of the Galois group induce the same map on the residue field at a prime
`P` of `𝓞 L` which is unramified over `𝓞 K`, then they are equal: their quotient lies in the
inertia group of `P`, which is trivial because `e(P) = 1`. -/
lemma eq_of_residue_mk_eq
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hP : P.asIdeal.LiesOver p.asIdeal)
    (he : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (σ τ : Gal(L/K))
    (h : ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk P.asIdeal (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) σ x) = Ideal.Quotient.mk P.asIdeal
          (galRestrict (NumberField.RingOfIntegers K) K L
            (NumberField.RingOfIntegers L) τ x)) :
    σ = τ := by
  haveI := hP
  have hinertia : Ideal.inertia (L ≃ₐ[K] L) P.asIdeal = ⊥ :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      (F := K) (K := L) p.asIdeal P.asIdeal).mpr he
  have hmem : σ * τ⁻¹ ∈ Ideal.inertia (L ≃ₐ[K] L) P.asIdeal := by
    change σ * τ⁻¹ ∈ (P.asIdeal.toAddSubgroup).inertia (L ≃ₐ[K] L)
    rw [AddSubgroup.mem_inertia]
    intro x
    rw [smul_ringOfIntegers_eq_galRestrict]
    have hmap : galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) (σ * τ⁻¹) x =
        galRestrict (NumberField.RingOfIntegers K) K L
          (NumberField.RingOfIntegers L) σ
            (galRestrict (NumberField.RingOfIntegers K) K L
              (NumberField.RingOfIntegers L) τ⁻¹ x) := by
      rw [map_mul, AlgEquiv.mul_apply]
    have hkey := h (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) τ⁻¹ x)
    rw [Ideal.Quotient.eq] at hkey
    rw [galRestrict_apply_apply_inv] at hkey
    rw [hmap]
    exact hkey
  rw [hinertia] at hmem
  have h1 : σ * τ⁻¹ = 1 := hmem
  simpa using mul_inv_eq_one.mp h1

/-- An element of the decomposition group of an unramified prime which acts trivially on the
residue field is trivial. -/
lemma eq_one_of_residue_mk_eq_one
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hP : P.asIdeal.LiesOver p.asIdeal)
    (he : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (σ : Gal(L/K))
    (h : ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk P.asIdeal (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) σ x) = Ideal.Quotient.mk P.asIdeal x) :
    σ = 1 := by
  refine eq_of_residue_mk_eq p P hP he σ 1 (fun x => ?_)
  simpa using h x

/-- Conjugation transports the property "acts as the `n`-th power map on the residue field"
from a prime `P₁` to a conjugate prime `P₂`. -/
lemma residue_action_conj
    (P₁ P₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (τ : Gal(L/K))
    (hτ : Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) τ : NumberField.RingOfIntegers L →+*
        NumberField.RingOfIntegers L) P₁.asIdeal = P₂.asIdeal)
    (σ : Gal(L/K)) (n : ℕ)
    (hres : ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk P₁.asIdeal (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) σ x) = (Ideal.Quotient.mk P₁.asIdeal x) ^ n) :
    ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk P₂.asIdeal (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) (τ * σ * τ⁻¹) x) =
        (Ideal.Quotient.mk P₂.asIdeal x) ^ n := by
  intro x
  let φ : NumberField.RingOfIntegers L ⧸ P₁.asIdeal →+*
      NumberField.RingOfIntegers L ⧸ P₂.asIdeal :=
    Ideal.Quotient.lift P₁.asIdeal
      ((Ideal.Quotient.mk P₂.asIdeal).comp (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) τ : NumberField.RingOfIntegers L →+*
          NumberField.RingOfIntegers L))
      (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        rw [← hτ]
        exact Ideal.mem_map_of_mem _ ha)
  have hφ : ∀ z : NumberField.RingOfIntegers L,
      φ (Ideal.Quotient.mk P₁.asIdeal z) = Ideal.Quotient.mk P₂.asIdeal
        (galRestrict (NumberField.RingOfIntegers K) K L
          (NumberField.RingOfIntegers L) τ z) :=
    fun z => Ideal.Quotient.lift_mk P₁.asIdeal _ _ (a := z)
  have hkey := congrArg φ (hres (galRestrict (NumberField.RingOfIntegers K) K L
    (NumberField.RingOfIntegers L) τ⁻¹ x))
  rw [map_pow, hφ, hφ] at hkey
  have hconj : galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) τ
        (galRestrict (NumberField.RingOfIntegers K) K L
          (NumberField.RingOfIntegers L) σ
            (galRestrict (NumberField.RingOfIntegers K) K L
              (NumberField.RingOfIntegers L) τ⁻¹ x)) =
      galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) (τ * σ * τ⁻¹) x := by
    rw [map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
  rw [galRestrict_apply_apply_inv] at hkey
  rw [← hconj]
  exact hkey

end FrobeniusEqOfCommute

open FrobeniusEqOfCommute in
theorem frobenius_eq_of_commute {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P₁ P₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h₁ : P₁.asIdeal.LiesOver p.asIdeal) (h₂ : P₂.asIdeal.LiesOver p.asIdeal)
    (hu₁ : P₁.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hu₂ : P₂.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (n : ℕ) (σ₁ σ₂ : Gal(L/K))
    (hσ₁ : Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ₁ : NumberField.RingOfIntegers L →+*
        NumberField.RingOfIntegers L) P₁.asIdeal = P₁.asIdeal)
    (hres₁ : ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk P₁.asIdeal (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) σ₁ x) = (Ideal.Quotient.mk P₁.asIdeal x) ^ n)
    (hσ₂ : Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ₂ : NumberField.RingOfIntegers L →+*
        NumberField.RingOfIntegers L) P₂.asIdeal = P₂.asIdeal)
    (hres₂ : ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk P₂.asIdeal (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) σ₂ x) = (Ideal.Quotient.mk P₂.asIdeal x) ^ n) :
    σ₁ = σ₂ := by
  haveI := h₁
  haveI := h₂
  obtain ⟨τ, hτ⟩ :=
    Commons.NumberTheory.RamificationInertia.exists_map_galRestrict_eq p P₁ P₂
  have hconj := residue_action_conj P₁ P₂ τ hτ σ₁ n hres₁
  have heq : σ₂ = τ * σ₁ * τ⁻¹ :=
    eq_of_residue_mk_eq p P₂ h₂ hu₂ σ₂ (τ * σ₁ * τ⁻¹)
      (fun x => by rw [hres₂ x, hconj x])
  rw [heq, hcomm τ σ₁]
  group

end Commons.NumberTheory.NumberField
