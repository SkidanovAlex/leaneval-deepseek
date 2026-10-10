import Mathlib.RingTheory.DedekindDomain.AdicValuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.RingTheory.DedekindDomain

open scoped algebraMap

open WithZero Multiplicative

/-- Comparison of two elements of `ℤᵐ⁰` which are `≤ 1` by testing against all the
thresholds `WithZero.exp (-n)`, `n : ℕ`.

This is the key "rigidity" fact making `ℤᵐ⁰`-valued valuations that are bounded by `1`
determined by the chain of their sublevel sets. -/
private theorem eq_of_forall_le_exp_neg {a b : ℤᵐ⁰} (ha : a ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  have hb : b ≤ 1 := by simpa using (h 0).mp (by simpa using ha)
  have key : ∀ {x : ℤᵐ⁰}, x ≤ 1 → (∀ n : ℕ, x ≤ WithZero.exp (-(n : ℤ))) → x = 0 := by
    intro x hx hxn
    by_contra hx0
    have hlog : ∀ n : ℕ, WithZero.log x ≤ -(n : ℤ) := fun n =>
      (WithZero.log_le_iff_le_exp hx0).mpr (hxn n)
    have hx0log : WithZero.log x ≤ 0 := (WithZero.log_le_iff_le_exp hx0).mpr (by simpa using hx)
    have hcast : (((-(WithZero.log x)).toNat : ℕ) : ℤ) = -WithZero.log x :=
      Int.toNat_of_nonneg (by omega)
    have := hlog ((-(WithZero.log x)).toNat + 1)
    omega
  rcases eq_or_ne a 0 with ha0 | ha0
  · have hb0 : b = 0 := key hb (fun n => (h n).mp (by simp [ha0]))
    rw [ha0, hb0]
  · have hb0 : b ≠ 0 := by
      rintro rfl
      exact ha0 (key ha (fun n => (h n).mpr (by simp)))
    have hlog : ∀ n : ℕ, WithZero.log a ≤ -(n : ℤ) ↔ WithZero.log b ≤ -(n : ℤ) := fun n =>
      (WithZero.log_le_iff_le_exp ha0).trans ((h n).trans (WithZero.log_le_iff_le_exp hb0).symm)
    have hla : WithZero.log a ≤ 0 := (WithZero.log_le_iff_le_exp ha0).mpr (by simpa using ha)
    have hlb : WithZero.log b ≤ 0 := (WithZero.log_le_iff_le_exp hb0).mpr (by simpa using hb)
    have heq : WithZero.log a = WithZero.log b := by
      apply le_antisymm
      · by_contra hc
        rw [not_le] at hc
        have hcast : (((-(WithZero.log b)).toNat : ℕ) : ℤ) = -WithZero.log b :=
          Int.toNat_of_nonneg (by omega)
        have h' := (hlog ((-(WithZero.log b)).toNat)).mpr (by simp [hcast])
        omega
      · by_contra hc
        rw [not_le] at hc
        have hcast : (((-(WithZero.log a)).toNat : ℕ) : ℤ) = -WithZero.log a :=
          Int.toNat_of_nonneg (by omega)
        have h' := (hlog ((-(WithZero.log a)).toNat)).mp (by simp [hcast])
        omega
    rw [← WithZero.exp_log ha0, ← WithZero.exp_log hb0, heq]

/-- Two valuations on the fraction field `K` of `R` which agree on the image of `R`
are equal. -/
private theorem valuation_ext_of_algebraMap_eq {R : Type*} [CommRing R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (V W : Valuation K Γ) (h : ∀ r : R, V (algebraMap R K r) = W (algebraMap R K r)) :
    V = W := by
  haveI : Nontrivial R :=
    ⟨0, 1, fun h => zero_ne_one (α := K) (by simpa using congrArg (algebraMap R K) h)⟩
  ext x
  obtain ⟨⟨a, b, hb⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hV := congrArg V hx
  have hW := congrArg W hx
  simp only [map_mul] at hV hW
  have hbne : algebraMap R K (b : R) ≠ 0 := fun h0 =>
    nonZeroDivisors.coe_ne_zero ⟨b, hb⟩ ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h0)
  rw [h a] at hV
  rw [h b] at hV
  exact mul_right_cancel₀ ((Valuation.ne_zero_iff W).2 hbne) (hV.trans hW.symm)

/-- The `v`-adic valuation of `e r` with respect to `w = e(v)` equals the `v`-adic valuation
of `r`. -/
private theorem intValuation_map_of_map_eq_aux {R : Type*} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (v w : IsDedekindDomain.HeightOneSpectrum R)
    (hw : w.asIdeal = v.asIdeal.map (e : R →+* R)) (r : R) :
    w.intValuation (e r) = v.intValuation r := by
  refine eq_of_forall_le_exp_neg (w.intValuation_le_one (e r)) (fun n => ?_)
  rw [w.intValuation_le_pow_iff_mem, v.intValuation_le_pow_iff_mem, hw, ← Ideal.map_pow]
  exact Ideal.apply_mem_of_equiv_iff

theorem valuation_map_of_map_eq {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K]
    (e : R ≃+* R) (σ : K ≃+* K)
    (hσ : ∀ r : R, σ (algebraMap R K r) = algebraMap R K (e r))
    (v w : IsDedekindDomain.HeightOneSpectrum R)
    (hw : w.asIdeal = v.asIdeal.map (e : R →+* R)) (x : K) :
    IsDedekindDomain.HeightOneSpectrum.valuation K w (σ x) =
      IsDedekindDomain.HeightOneSpectrum.valuation K v x := by
  have hVW : (w.valuation K).comap (σ : K →+* K) = v.valuation K := by
    apply valuation_ext_of_algebraMap_eq (R := R)
    intro r
    rw [Valuation.comap_apply,
      show (σ : K →+* K) (algebraMap R K r) = algebraMap R K (e r) from hσ r]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap w (e r),
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap v r]
    exact intValuation_map_of_map_eq_aux e v w hw r
  have := congrArg (fun f : Valuation K ℤᵐ⁰ => f x) hVW
  simpa [Valuation.comap_apply] using this

end Commons.RingTheory.DedekindDomain