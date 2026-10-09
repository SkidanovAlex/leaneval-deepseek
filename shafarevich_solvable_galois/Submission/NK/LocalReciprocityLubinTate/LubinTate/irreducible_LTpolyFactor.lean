import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Division
import Submission.NK.LocalReciprocityLubinTate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Eisenstein factor `X ^ (q - 1) + π` of the standard Lubin–Tate polynomial is irreducible

For the standard Lubin–Tate polynomial `f(X) = πX + X^q` (Milne, *Class Field Theory*, Example
2.10(a)) the factor `X^{q-1} + π = f(X)/X` is Eisenstein at the uniformiser `π` and hence
irreducible over the base field `F`; this is the first step in the construction of the Lubin–Tate
levels `K_n = F(π_n)` (Milne, *op. cit.*, §I.3: `f^{[1]}(T)` is the minimal polynomial of a
division point).

## Main results

* `irreducible_X_pow_add_C_map` — the abstract form: over a discrete valuation ring `R` with
  fraction field `K`, for an irreducible `π ∈ R` and `n > 0`, the image of `X ^ n + C π` in `K[X]`
  is irreducible.  This is Eisenstein's criterion (`Polynomial.IsEisensteinAt.irreducible`) at the
  prime ideal `(π)` — which in a discrete valuation ring is the maximal ideal, so that non-divisibility
  of the constant coefficient by `π²` is exactly `π ≠ 0` and `π` non-unit — followed by Gauss's
  lemma (`Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map`) to descend from `R[X]` to
  `K[X]`.
* `irreducible_LTpolyFactor` — the geometric case: the ring of integers `𝒪[F]` of a nonarchimedean
  local field is a discrete valuation ring, an irreducible `π ∈ 𝒪[F]` is a uniformiser, and the
  fraction field of `𝒪[F]` is `F`.
-/

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

open Polynomial

/-- **Eisenstein's criterion for `X ^ n + π`.**  Let `R` be a discrete valuation ring with
fraction field `K`, let `π ∈ R` be irreducible and `n > 0`.  Then the image in `K[X]` of
`X ^ n + C π` is irreducible: the polynomial is Eisenstein at the prime ideal `(π)` (a monic
polynomial is primitive; the constant coefficient `π` is divisible by `π` but not by `π²`), and
Gauss's lemma descends irreducibility from `R[X]` to `K[X]` for a monic polynomial. -/
theorem irreducible_X_pow_add_C_map {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) :
    Irreducible ((X ^ n + C π : R[X]).map (algebraMap R K)) := by
  -- the polynomial is monic of degree `n`
  have hmonic : (X ^ n + C π : R[X]).Monic := monic_X_pow_add_C π (by omega)
  have hdeg : (X ^ n + C π : R[X]).natDegree = n := natDegree_X_pow_add_C
  -- its Taylor coefficients
  have hcoeff : ∀ m : ℕ, (X ^ n + C π : R[X]).coeff m =
      (if m = n then (1 : R) else 0) + (if m = 0 then π else 0) := by
    intro m; rw [coeff_add, coeff_X_pow, coeff_C]
  -- `(π)` is a proper ideal
  have hspan_ne_top : Ideal.span {π} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact hπ.not_isUnit
  -- every lower coefficient lies in `(π)`
  have hmem : ∀ {m : ℕ}, m < (X ^ n + C π : R[X]).natDegree →
      (X ^ n + C π : R[X]).coeff m ∈ Ideal.span {π} := by
    intro m hm
    rw [hdeg] at hm
    rw [hcoeff m, if_neg (by omega : m ≠ n)]
    rcases eq_or_ne m 0 with h0 | h0
    · subst h0; simp
    · rw [if_neg h0]; simp
  -- the constant coefficient `π` is not divisible by `π²`
  have hnotmem2 : (X ^ n + C π : R[X]).coeff 0 ∉ (Ideal.span {π}) ^ 2 := by
    have h0 : (X ^ n + C π : R[X]).coeff 0 = π := by
      rw [hcoeff 0, if_neg (by omega : (0 : ℕ) ≠ n)]; simp
    rw [h0]
    intro hcon
    rw [pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton] at hcon
    have hdvd : π ^ 2 ∣ π := by rwa [pow_two]
    obtain ⟨a, ha⟩ := hdvd
    have h2 : π * a = 1 := by
      refine mul_left_cancel₀ hπ.ne_zero ?_
      calc π * (π * a) = π ^ 2 * a := by ring
        _ = π := ha.symm
        _ = π * 1 := by ring
    exact hπ.not_isUnit (IsUnit.of_mul_eq_one a h2)
  -- Eisenstein at the prime ideal `(π)`
  have hEis : (X ^ n + C π : R[X]).IsEisensteinAt (Ideal.span {π}) :=
    hmonic.isEisensteinAt_of_mem_of_notMem hspan_ne_top hmem hnotmem2
  have hprime : (Ideal.span {π} : Ideal R).IsPrime := by
    rw [← hπ.maximalIdeal_eq]
    exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  have hirr : Irreducible (X ^ n + C π : R[X]) :=
    hEis.irreducible hprime hmonic.isPrimitive (by rw [hdeg]; exact hn)
  -- Gauss's lemma: descend to the fraction field
  exact (hmonic.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hirr

/-- **The Eisenstein factor `X ^ (q - 1) + π` of the standard Lubin–Tate polynomial is
irreducible over `F`** (Milne, *CFT*, §I.3).

Let `F` be a nonarchimedean local field, `π ∈ 𝒪[F]` irreducible (i.e. a uniformiser) and `q ≥ 2`.
The ring of integers `𝒪[F]` is a discrete valuation ring with fraction field `F` (`π` generates its
maximal ideal), so `X ^ (q - 1) + π` is Eisenstein at `π` over `𝒪[F]` and Gauss's lemma gives its
irreducibility over `F`. -/
theorem irreducible_LTpolyFactor (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : (↥(ValuativeRel.valuation F).integer))
    (hπ : Irreducible π) (q : ℕ) (hq : 2 ≤ q) :
    Irreducible (NK.LocalReciprocityLubinTate.LTpolyFactor (π : F) q) := by
  have h := irreducible_X_pow_add_C_map (R := ↥(ValuativeRel.valuation F).integer) (K := F)
    π hπ (q - 1) (by omega)
  -- identify the image of `X ^ (q - 1) + C π` with `LTpolyFactor (π : F) q`
  have hmap : ((X ^ (q - 1) + C π : (↥(ValuativeRel.valuation F).integer)[X]).map
      (algebraMap ↥(ValuativeRel.valuation F).integer F))
      = NK.LocalReciprocityLubinTate.LTpolyFactor (π : F) q := by
    have hcoe : (algebraMap ↥(ValuativeRel.valuation F).integer F) π = (π : F) := rfl
    simp [NK.LocalReciprocityLubinTate.LTpolyFactor, hcoe]
  rwa [hmap] at h

end NK.LocalReciprocityLubinTate.LubinTate
