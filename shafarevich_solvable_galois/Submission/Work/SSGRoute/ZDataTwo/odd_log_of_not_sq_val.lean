import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

open scoped WithZero

namespace Work.SSGRoute.ZDataTwo

/-- The valuation ring of a pullback valuation is the pullback of the valuation ring. -/
private theorem valuationSubring_comap_aux {K L Γ₀ : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀) (f : K →+* L) :
    (v.comap f).valuationSubring = v.valuationSubring.comap f := by
  ext x
  rw [Valuation.mem_valuationSubring_iff, Valuation.comap_apply, ValuationSubring.mem_comap,
    Valuation.mem_valuationSubring_iff]

/-- The condition "the value of `b` is not the square of the value of any unit" is insensitive to
replacing a valuation by an equivalent one. -/
private theorem not_exists_sq_val_of_isEquiv_aux {K : Type*} [Field K]
    {Γ₀ Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [LinearOrderedCommGroupWithZero Γ₀'] {w : Valuation K Γ₀} {v : Valuation K Γ₀'}
    (h : w.IsEquiv v) (b : Kˣ)
    (hw : ¬ ∃ d : Kˣ, w (b : K) = (w (d : K)) ^ 2) :
    ¬ ∃ d : Kˣ, v (b : K) = (v (d : K)) ^ 2 := by
  rintro ⟨d, hd⟩
  refine hw ⟨d, ?_⟩
  have hsq : v (b : K) = v ((d : K) * (d : K)) := by
    rw [map_mul, ← pow_two]
    exact hd
  have h' := (h.eq_iff (r := b) (s := (d : K) * (d : K))).mpr hsq
  simpa [map_mul, pow_two] using h'

/-- For a surjective valuation with values in `ℤᵐ⁰`, the value of a unit `b` is the square of the
value of a unit if and only if `-(v b).log` is even. -/
private theorem exists_sq_val_iff_even_neg_log_aux {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (hv : Function.Surjective v) (b : Kˣ) :
    (∃ d : Kˣ, v (b : K) = (v (d : K)) ^ 2) ↔ Even (-(v (b : K)).log) := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨-(v (d : K)).log, ?_⟩
    have hlog : (v (b : K)).log = 2 * (v (d : K)).log := by
      rw [hd, WithZero.log_pow]
      simp
    rw [hlog]
    ring
  · rintro ⟨k, hk⟩
    obtain ⟨y, hy⟩ := hv (WithZero.exp (-k))
    have hy0 : y ≠ 0 := (Valuation.ne_zero_iff v).mp (by rw [hy]; simp)
    refine ⟨Units.mk0 y hy0, ?_⟩
    have hb0 : v (b : K) ≠ 0 := (Valuation.ne_zero_iff v).mpr (Units.ne_zero b)
    have h1 : v (b : K) = WithZero.exp (-(2 * k)) := by
      rw [← WithZero.exp_log hb0]
      congr 1
      omega
    have h2 : (v (y : K)) ^ 2 = WithZero.exp (-(2 * k)) := by
      rw [hy, ← WithZero.exp_nsmul]
      congr 1
      simp
    rw [Units.val_mk0]
    exact h1.trans h2.symm

theorem odd_log_of_not_sq_val
    (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (A : ValuationSubring Ω) (hA : A.comap (algebraMap K Ω) ≠ ⊤)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h𝔭 : A.comap (algebraMap K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K 𝔭)
    (b : Kˣ)
    (hodd : ¬ ∃ d : Kˣ, A.valuation (algebraMap K Ω (b : K)) =
      (A.valuation (algebraMap K Ω (d : K))) ^ 2) :
    Odd (-(𝔭.valuation K (b : K)).log) := by
  classical
  set w : Valuation K A.ValueGroup := A.valuation.comap (algebraMap K Ω) with hw
  set v : Valuation K ℤᵐ⁰ := 𝔭.valuation K with hv
  have hw_apply : ∀ x : K, w x = A.valuation (algebraMap K Ω x) := fun x => by
    rw [hw, Valuation.comap_apply]
  -- the valuation induced on `K` by `A` has the same valuation ring as the `𝔭`-adic one
  have hsub : w.valuationSubring = v.valuationSubring := by
    have hwsub : w.valuationSubring = A.comap (algebraMap K Ω) := by
      rw [hw, valuationSubring_comap_aux A.valuation (algebraMap K Ω),
        ValuationSubring.valuationSubring_valuation]
    rw [hwsub, h𝔭, hv,
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  have hequiv : w.IsEquiv v := (Valuation.isEquiv_iff_valuationSubring w v).mpr hsub
  -- the hypothesis transfers to the restricted valuation
  have hodd_w : ¬ ∃ d : Kˣ, w (b : K) = (w (d : K)) ^ 2 := by
    rintro ⟨d, hd⟩
    refine hodd ⟨d, ?_⟩
    rw [hw_apply] at hd
    exact hd
  have hodd_v : ¬ ∃ d : Kˣ, v (b : K) = (v (d : K)) ^ 2 :=
    not_exists_sq_val_of_isEquiv_aux hequiv b hodd_w
  have hsurj : Function.Surjective v := by
    rw [hv]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_surjective K 𝔭
  have hmain := exists_sq_val_iff_even_neg_log_aux v hsurj b
  rw [← Int.not_even_iff_odd]
  intro hEven
  exact hodd_v (hmain.mpr hEven)

end Work.SSGRoute.ZDataTwo
