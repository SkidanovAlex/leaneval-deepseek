import Mathlib

/-!
# Extending a derivation from a domain to its fraction field

Let `R` be an integral domain with fraction field `K`, and let `D : Derivation ℤ R R` be a
derivation.  This file constructs a derivation `D' : Derivation ℤ K K` extending `D` along the
structure map `algebraMap R K`, i.e. `D' (algebraMap R K r) = algebraMap R K (D r)` for all `r`.

The construction is the classical quotient rule: an element of `K` is a fraction `a / b`, and we
set `D' (a / b) = (D a * b - a * D b) / b ^ 2`.  Well-definedness of this formula is the content of
`fracDeriv_wellDef`, and additivity / the Leibniz rule are verified on representatives in
`fracDeriv_add` / `fracDeriv_mul`; the resulting function is then assembled into a derivation.

The main result is `Commons.RingTheory.Derivation.exists_derivation_fractionRing`.
-/

namespace Commons.RingTheory.Derivation

open scoped Classical

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- The "quotient rule" candidate for the value at `a / b` of the extension of a
`ℤ`-derivation `DK : R → K` to the fraction field. -/
noncomputable def fracDeriv (DK : Derivation ℤ R K) (a b : R) : K :=
  (DK a * algebraMap R K b - algebraMap R K a * DK b) / (algebraMap R K b) ^ 2

/-- The value `fracDeriv DK a b` only depends on the fraction `a / b`, i.e. on `mk' K a b`. -/
theorem fracDeriv_wellDef (DK : Derivation ℤ R K) {a₁ a₂ : R} {b₁ b₂ : nonZeroDivisors R}
    (h : IsLocalization.mk' K a₁ b₁ = IsLocalization.mk' K a₂ b₂) :
    fracDeriv DK a₁ (b₁ : R) = fracDeriv DK a₂ (b₂ : R) := by
  have hb₁ : algebraMap R K (b₁ : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) b₁.2
  have hb₂ : algebraMap R K (b₂ : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) b₂.2
  have hraw := (IsLocalization.mk'_eq_iff_eq' (M := nonZeroDivisors R) (S := K)).mp h
  have he1 : algebraMap R K a₁ * algebraMap R K (b₂ : R)
      = algebraMap R K a₂ * algebraMap R K (b₁ : R) := by
    simpa only [map_mul] using hraw
  have hab : a₁ * (b₂ : R) = a₂ * (b₁ : R) :=
    IsFractionRing.injective R K (by simpa only [map_mul] using hraw)
  have he2 : algebraMap R K a₁ * DK (b₂ : R) + algebraMap R K (b₂ : R) * DK a₁
      = algebraMap R K a₂ * DK (b₁ : R) + algebraMap R K (b₁ : R) * DK a₂ := by
    have hD : DK (a₁ * (b₂ : R)) = DK (a₂ * (b₁ : R)) := by rw [hab]
    simpa only [Derivation.leibniz, Algebra.smul_def] using hD
  rw [fracDeriv, fracDeriv, div_eq_div_iff (pow_ne_zero 2 hb₁) (pow_ne_zero 2 hb₂)]
  linear_combination (algebraMap R K (b₁ : R) * algebraMap R K (b₂ : R)) * he2
    - (DK (b₂ : R) * algebraMap R K (b₁ : R) + DK (b₁ : R) * algebraMap R K (b₂ : R)) * he1

/-- Addition of fractions in a fraction ring, in terms of `IsLocalization.mk'`. -/
theorem frac_mk'_add (x₁ x₂ : R) (y₁ y₂ : nonZeroDivisors R) :
    IsLocalization.mk' K x₁ y₁ + IsLocalization.mk' K x₂ y₂
      = IsLocalization.mk' K (x₁ * (y₂ : R) + x₂ * (y₁ : R)) (y₁ * y₂) := by
  have hy₁ : algebraMap R K (y₁ : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) y₁.2
  have hy₂ : algebraMap R K (y₂ : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) y₂.2
  rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div]
  rw [div_add_div _ _ hy₁ hy₂]
  simp only [Submonoid.coe_mul, map_add, map_mul]
  congr 1
  ring

/-- The quotient-rule formula is additive in the numerator. -/
theorem fracDeriv_add (DK : Derivation ℤ R K) (a₁ a₂ : R) (b₁ b₂ : nonZeroDivisors R) :
    fracDeriv DK (a₁ * (b₂ : R) + a₂ * (b₁ : R)) (((b₁ * b₂ : nonZeroDivisors R) : R))
      = fracDeriv DK a₁ (b₁ : R) + fracDeriv DK a₂ (b₂ : R) := by
  have hb₁ : algebraMap R K (b₁ : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) b₁.2
  have hb₂ : algebraMap R K (b₂ : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) b₂.2
  unfold fracDeriv
  simp only [Submonoid.coe_mul, map_add, map_mul, Derivation.leibniz, Algebra.smul_def]
  field_simp
  ring

/-- The quotient-rule formula satisfies the Leibniz rule in terms of representatives. -/
theorem fracDeriv_mul (DK : Derivation ℤ R K) (a₁ a₂ : R) (b₁ b₂ : nonZeroDivisors R) :
    fracDeriv DK (a₁ * a₂) (((b₁ * b₂ : nonZeroDivisors R) : R))
      = IsLocalization.mk' K a₁ b₁ * fracDeriv DK a₂ (b₂ : R)
        + IsLocalization.mk' K a₂ b₂ * fracDeriv DK a₁ (b₁ : R) := by
  have hb₁ : algebraMap R K (b₁ : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) b₁.2
  have hb₂ : algebraMap R K (b₂ : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) b₂.2
  unfold fracDeriv
  rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div]
  simp only [Submonoid.coe_mul, map_mul, Derivation.leibniz, Algebra.smul_def]
  field_simp
  ring

/-- The extension of `DK` to the fraction field, defined via a choice of representative. -/
noncomputable def fracDerivFun (DK : Derivation ℤ R K) (z : K) : K :=
  fracDeriv DK (IsLocalization.sec (nonZeroDivisors R) z).1
    ((IsLocalization.sec (nonZeroDivisors R) z).2 : R)

theorem fracDerivFun_mk' (DK : Derivation ℤ R K) (a : R) (b : nonZeroDivisors R) :
    fracDerivFun DK (IsLocalization.mk' K a b) = fracDeriv DK a (b : R) := by
  unfold fracDerivFun
  exact fracDeriv_wellDef DK (IsLocalization.mk'_sec K (IsLocalization.mk' K a b))

theorem fracDerivFun_zero (DK : Derivation ℤ R K) : fracDerivFun DK 0 = 0 := by
  have h : (0 : K) = IsLocalization.mk' K 0 (1 : nonZeroDivisors R) := by
    rw [IsLocalization.mk'_one, map_zero]
  rw [h, fracDerivFun_mk', fracDeriv]
  simp

theorem fracDerivFun_add (DK : Derivation ℤ R K) (z w : K) :
    fracDerivFun DK (z + w) = fracDerivFun DK z + fracDerivFun DK w := by
  obtain ⟨a₁, b₁, hz⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) z
  obtain ⟨a₂, b₂, hw⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) w
  rw [← hz, ← hw]
  rw [frac_mk'_add, fracDerivFun_mk', fracDerivFun_mk', fracDerivFun_mk']
  exact fracDeriv_add DK a₁ a₂ b₁ b₂

theorem fracDerivFun_mul (DK : Derivation ℤ R K) (z w : K) :
    fracDerivFun DK (z * w) = z * fracDerivFun DK w + w * fracDerivFun DK z := by
  obtain ⟨a₁, b₁, hz⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) z
  obtain ⟨a₂, b₂, hw⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) w
  rw [← hz, ← hw]
  rw [← IsLocalization.mk'_mul, fracDerivFun_mk', fracDerivFun_mk', fracDerivFun_mk']
  exact fracDeriv_mul DK a₁ a₂ b₁ b₂

/-- The extension of `DK` as an additive homomorphism. -/
noncomputable def fracDerivHom (DK : Derivation ℤ R K) : K →+ K where
  toFun := fracDerivFun DK
  map_zero' := fracDerivFun_zero DK
  map_add' := fracDerivFun_add DK

/-- The extension of a derivation `DK : R → K` to the fraction field `K`. -/
noncomputable def fracDerivDeriv (DK : Derivation ℤ R K) : Derivation ℤ K K :=
  Derivation.mk' (fracDerivHom DK).toIntLinearMap (by
    intro a b
    change fracDerivFun DK (a * b) = a * fracDerivFun DK b + b * fracDerivFun DK a
    exact fracDerivFun_mul DK a b)

theorem fracDerivDeriv_apply (DK : Derivation ℤ R K) (z : K) :
    fracDerivDeriv DK z = fracDerivFun DK z := by
  simp [fracDerivDeriv, fracDerivHom]

/-- The constructed derivation extends `DK` along `algebraMap R K`. -/
theorem fracDerivDeriv_algebraMap (DK : Derivation ℤ R K) (r : R) :
    fracDerivDeriv DK (algebraMap R K r) = DK r := by
  rw [fracDerivDeriv_apply]
  have h : algebraMap R K r = IsLocalization.mk' K r (1 : nonZeroDivisors R) := by
    rw [IsLocalization.mk'_one]
  rw [h, fracDerivFun_mk', fracDeriv]
  simp

/-- Any `ℤ`-derivation `R → K` with `K` the fraction field of the domain `R` extends to a
`ℤ`-derivation of `K`. -/
theorem exists_derivation_of_derivation (DK : Derivation ℤ R K) :
    ∃ D' : Derivation ℤ K K, ∀ r : R, D' (algebraMap R K r) = DK r :=
  ⟨fracDerivDeriv DK, fracDerivDeriv_algebraMap DK⟩

end Commons.RingTheory.Derivation

namespace Commons.RingTheory.Derivation

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_derivation_fractionRing {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ K K, ∀ r : R, D' (algebraMap R K r) = algebraMap R K (D r) := by
  obtain ⟨D', hD'⟩ :=
    exists_derivation_of_derivation (R := R) (K := K) ((Algebra.linearMap R K).compDer D)
  refine ⟨D', fun r => ?_⟩
  rw [hD']
  simp [Derivation.coe_comp, Algebra.linearMap_apply]

end Commons.RingTheory.Derivation
