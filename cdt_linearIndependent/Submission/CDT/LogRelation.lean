import Mathlib
import Submission.CDT.LogMultiplicativeField
import Submission.Commons.RingTheory.Derivation.map_sum
import Submission.Commons.FieldTheory.Differential.exists_logDeriv_eq_natCast_mul_of_logDeriv_mem

/-!
# Function-field Lindemann–Weierstrass: the logarithmic form

`Submission.CDT.LogMultiplicativeField` proves the multiplicative-dependence form of the
function-field Lindemann–Weierstrass theorem in the *derivative* form: a `K`-linear relation
`Σᵢ cᵢ·(dRat fᵢ)/fᵢ = dRat h` (with `c : ι → K` not identically zero) among logarithmic derivatives
forces a nontrivial integer multiplicative relation `∏ᵢ fᵢ ^ mᵢ ∈ K`.

This file states the same theorem in its classical *logarithmic* form: if `ℓᵢ` are elements of a
differential field extension `L ⊇ K(X)` whose derivatives are the logarithmic derivatives of the
`fᵢ` (i.e. `ℓᵢ` plays the role of `log fᵢ`), and a `K`-linear combination of the `ℓᵢ` is already a
rational function, then the `fᵢ` are multiplicatively dependent.  The derivation of the derivative
form is simply the differentiation of the relation, using `DifferentialAlgebra.deriv_algebraMap`
and the fact that the coefficients `cᵢ ∈ K` have vanishing derivative.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable {L : Type*} [Field L] [Algebra (RatFunc K) L] [Differential (RatFunc K)]
  [Differential L] [DifferentialAlgebra (RatFunc K) L]

section DerivRules

/-- The sum rule for the derivation, over a finite index set (the commons lemma
`Commons.RingTheory.Derivation.map_sum`). -/
lemma deriv_finset_sum {ι : Type*} (s : Finset ι) (f : ι → L) :
    Differential.deriv (∑ i ∈ s, f i) = ∑ i ∈ s, Differential.deriv (f i) :=
  Commons.RingTheory.Derivation.map_sum _ s f

/-- The derivative of a scalar multiple of the base field, in multiplication form. -/
lemma deriv_mul_form (a b : L) :
    Differential.deriv (a * b) = a * Differential.deriv b + b * Differential.deriv a := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

/-- The derivative of a constant from `K(X)` (where the derivation on `K(X)` is `dRat`). -/
lemma deriv_base (hderiv : ∀ r : RatFunc K, Differential.deriv r = dRat r) (r : RatFunc K) :
    Differential.deriv (algebraMap (RatFunc K) L r) = algebraMap (RatFunc K) L (dRat r) := by
  rw [DifferentialAlgebra.deriv_algebraMap, hderiv]

/-- **The derivation of a logarithmic relation.**  If `ℓᵢ` have the logarithmic derivatives of the
`fᵢ`, then differentiating `Σᵢ cᵢ·ℓᵢ = g` gives the derivative-form relation
`Σᵢ cᵢ·(dRat fᵢ)/fᵢ = dRat g` in `K(X)`. -/
lemma sum_dRat_div_eq_of_sum_log_eq (hderiv : ∀ r : RatFunc K, Differential.deriv r = dRat r)
    {ι : Type*} [Fintype ι] (f : ι → RatFunc K) (c : ι → K)
    (l : ι → L)
    (hl : ∀ i, Differential.deriv (l i)
      = algebraMap (RatFunc K) L (dRat (f i) / f i))
    (g : RatFunc K)
    (hg : ∑ i, algebraMap (RatFunc K) L (algebraMap K (RatFunc K) (c i)) * l i
      = algebraMap (RatFunc K) L g) :
    ∑ i, algebraMap K (RatFunc K) (c i) * (dRat (f i) / f i) = dRat g := by
  classical
  have hinj : Function.Injective (algebraMap (RatFunc K) L) := by
    intro a b hab
    by_contra hne
    have h1 : algebraMap (RatFunc K) L (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h3 : algebraMap (RatFunc K) L ((a - b)⁻¹ * (a - b))
        = algebraMap (RatFunc K) L 1 := by rw [inv_mul_cancel₀ h2]
    rw [map_mul, map_one, h1, mul_zero] at h3
    exact one_ne_zero h3.symm
  have hL : Differential.deriv
        (∑ i, algebraMap (RatFunc K) L (algebraMap K (RatFunc K) (c i)) * l i)
      = ∑ i, algebraMap (RatFunc K) L
          (algebraMap K (RatFunc K) (c i) * (dRat (f i) / f i)) := by
    rw [deriv_finset_sum Finset.univ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [deriv_mul_form, deriv_base hderiv, hl i, dRat_const, map_zero, mul_zero, add_zero,
      ← map_mul]
  have hkey : ∑ i, algebraMap (RatFunc K) L (algebraMap K (RatFunc K) (c i) * (dRat (f i) / f i))
      = algebraMap (RatFunc K) L (dRat g) := by
    rw [← hL, hg, deriv_base hderiv]
  refine hinj ?_
  rw [map_sum]
  exact hkey

end DerivRules

/-- **Function-field Lindemann–Weierstrass, logarithmic form.**  Let `L` be a differential field
extension of `K(X)` whose derivation restricts to `dRat`.  If `ℓᵢ ∈ L` have the logarithmic
derivatives of the nonzero `fᵢ ∈ K(X)` and a *nonzero* `K`-linear combination of the `ℓᵢ` is a
rational function, then the `fᵢ` are multiplicatively dependent: some nontrivial product
`∏ᵢ fᵢ ^ mᵢ` (`mᵢ ∈ ℤ`) is a constant. -/
theorem exists_int_prod_zpow_const_of_logRelation
    (hderiv : ∀ r : RatFunc K, Differential.deriv r = dRat r)
    {ι : Type*} [Fintype ι] (f : ι → RatFunc K) (hf : ∀ i, f i ≠ 0) (c : ι → K) (hc : c ≠ 0)
    (l : ι → L)
    (hl : ∀ i, Differential.deriv (l i)
      = algebraMap (RatFunc K) L (dRat (f i) / f i))
    (g : RatFunc K)
    (hg : ∑ i, algebraMap (RatFunc K) L (algebraMap K (RatFunc K) (c i)) * l i
      = algebraMap (RatFunc K) L g) :
    ∃ m : ι → ℤ, m ≠ 0 ∧ ∃ C : K, C ≠ 0 ∧ ∏ i, f i ^ (m i) = algebraMap K (RatFunc K) C :=
  exists_int_prod_zpow_const_of_sum_dRat_div_field f hf c hc
    ⟨g, sum_dRat_div_eq_of_sum_log_eq hderiv f c l hl g hg⟩

/-- **The algebraic case of Lindemann–Weierstrass over `K(X)`.**  Let `x ≠ 0` lie in a finite
extension `L` of `K(X)` (with the derivation extending `dRat`) and suppose that its logarithmic
derivative is a rational function, `x'/x = a ∈ K(X)`.  Then `a` is, up to a positive integer
multiple, the logarithmic derivative of a rational function: `m·a = (dRat u)/u` with `u ∈ K(X)`,
`u ≠ 0` and `m > 0`.

(For instance, over `K = ℂ` with `x = √(y²+1)` one has `x'/x = y/(y²+1)`, and indeed
`2·y/(y²+1) = (dRat (y²+1))/(y²+1)`.) -/
theorem exists_dRat_div_eq_natCast_mul_of_logDeriv_mem {L : Type*} [Field L]
    [Algebra (RatFunc K) L] [FiniteDimensional (RatFunc K) L]
    (hderiv : ∀ r : RatFunc K, Differential.deriv r = dRat r) [Differential L]
    [DifferentialAlgebra (RatFunc K) L] {x : L} (hx : x ≠ 0) {a : RatFunc K}
    (ha : Differential.deriv x / x = algebraMap (RatFunc K) L a) :
    ∃ m : ℕ, 0 < m ∧ ∃ u : RatFunc K, u ≠ 0 ∧
      dRat u / u = algebraMap K (RatFunc K) ((m : ℕ) : K) * a := by
  obtain ⟨m, hmpos, u, hu, hu'⟩ :=
    Commons.FieldTheory.Differential.exists_logDeriv_eq_natCast_mul_of_logDeriv_mem
      (K := RatFunc K) (L := L) hx ha
  refine ⟨m, hmpos, u, hu, ?_⟩
  rw [Differential.logDeriv, hderiv u] at hu'
  rw [hu', ← map_natCast (algebraMap K (RatFunc K)) m]

end Submission.CDT
