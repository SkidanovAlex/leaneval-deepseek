import Mathlib
import Submission.CDT.LogProduct
import Submission.CDT.LogIndependence
import Submission.CDT.LogMultiplicativeField
import Submission.CDT.RatFuncConstants

/-!
# Function-field Lindemann–Weierstrass: the weight-two independence statement

`Submission.CDT.LogProduct` proves the *individual* transcendence-type statement that the product
`ℓ₁·ℓ₂` of two logarithms is not a rational function.  This file proves the corresponding
**independence** statement for degree-`2` monomials: for two multiplicatively independent
nonconstant rational functions `f, g ∈ K(X)` and logarithms `u, v` of them
(`u' = (dRat f)/f`, `v' = (dRat g)/g`) in a differential field extension `L` of `K(X)`,

`c₀·u·v + c₁·u + c₂·v ∉ K(X)`  whenever `c₀ ≠ 0`.

This strictly generalises `not_exists_mul_eq_algebraMap` (which is the case where `u, v` are the
logarithms of two nonconstant functions and no linear terms are present), and it is the degree-`2`
part of the algebraic independence of the logarithms of multiplicatively independent functions --
the open end of the function-field Lindemann–Weierstrass hierarchy built in
`LogTranscendence` (weight 0 and 1), `LogRelation`/`LogMultiplicative` (the dependence form at
weight 1), `LogProduct` and `WeightTwo` (weight 2).

## The proof

Write `A₁ = (dRat f)/f` and `A₂ = (dRat g)/g` for the logarithmic derivatives, and suppose
`c₀·u·v + c₁·u + c₂·v = r₀ ∈ K(X) ⊆ L`.  Two differentiations give two `L`-linear equations in the
unknowns `u, v`:

* `c₀A₂·u + c₀A₁·v = γ`, where `γ = r₀' - c₁A₁ - c₂A₂`;
* `c₀A₂'·u + c₀A₁'·v = δ`, where `δ = γ' - 2c₀A₁A₂`.

Their coefficient determinant is `-c₀²·W` with `W = A₁'A₂ - A₁A₂'` the *Wronskian* of the two
logarithmic derivatives.

* If `W ≠ 0`, Cramer's rule exhibits `v` as a rational function -- contradicting the
  transcendence of `v` (weight-one Lindemann–Weierstrass, `transcendental_of_deriv_eq_dRat_div`).
* If `W = 0`, then `dRat (A₂/A₁) = 0`, so `A₂ = λ·A₁` for a constant `λ ∈ K` (the constants of
  `K(X)`, `exists_const_of_dRat_eq_zero`), i.e. the logarithmic derivatives are proportional; by
  `exists_int_prod_zpow_const_of_logDeriv_eq_smul` this forces a nontrivial multiplicative relation
  `f^m·g^n ∈ K`, contradicting the hypothesis.

The abstract two-equation elimination is isolated as `exists_algebraMap_of_quadratic_relation`
(valid for an arbitrary differential field extension `R ⊆ L` of characteristic zero, with three
constants `c₀, c₁, c₂`); the instantiation `R = K(X)` and the degenerate case are the rational
function content of the file.
-/


set_option linter.unusedSimpArgs false

open scoped Differential

noncomputable section

namespace Submission.CDT

open Polynomial

variable {R L : Type*} [Field R] [CharZero R] [Field L] [Algebra R L]
  [Differential R] [Differential L] [DifferentialAlgebra R L]

omit [CharZero R] in
/-- The derivative of the product of an element of the base field with an element of the
extension. -/
lemma deriv_algebraMap_mul (a : R) (z : L) :
    (algebraMap R L a * z)′ = algebraMap R L a * z′ + algebraMap R L (a′) * z := by
  rw [Derivation.leibniz, DifferentialAlgebra.deriv_algebraMap, smul_eq_mul, smul_eq_mul]
  ring

omit [CharZero R] in
/-- **First case of the two-equation elimination.**  Let `u, v` in a differential field extension
`L` of the characteristic-zero differential field `R` satisfy `u' = A₁`, `v' = A₂` (with
`A₁, A₂ ∈ R`) together with a quadratic relation `c₀·u·v + c₁·u + c₂·v = r₀` with `c₀ ≠ 0` and
`c₀, c₁, c₂` constants.  If the Wronskian `A₁·A₂' - A₂·A₁'` of the two coefficients does not
vanish, then `v` already lies in `R`. -/
theorem exists_algebraMap_of_quadratic_relation
    {A₁ A₂ : R} (hΔ : A₁ * A₂′ - A₂ * A₁′ ≠ 0)
    {c₀ c₁ c₂ : R} (hc₀ : c₀ ≠ 0)
    (hc₀' : c₀′ = 0) (hc₁' : c₁′ = 0) (hc₂' : c₂′ = 0)
    {u v : L} (hu : u′ = algebraMap R L A₁) (hv : v′ = algebraMap R L A₂)
    {r₀ : R}
    (hrel : algebraMap R L r₀
      = algebraMap R L c₀ * (u * v) + algebraMap R L c₁ * u + algebraMap R L c₂ * v) :
    ∃ r : R, v = algebraMap R L r := by
  set γ : R := r₀′ - c₁ * A₁ - c₂ * A₂ with hγdef
  set δ : R := γ′ - 2 * c₀ * A₁ * A₂ with hδdef
  have hE1raw : algebraMap R L r₀′ = algebraMap R L c₀
        * (u * algebraMap R L A₂ + v * algebraMap R L A₁)
        + algebraMap R L c₁ * algebraMap R L A₁
        + algebraMap R L c₂ * algebraMap R L A₂ := by
    have h := congrArg Differential.deriv hrel
    simp only [DifferentialAlgebra.deriv_algebraMap, map_add, deriv_algebraMap_mul,
      Derivation.leibniz, smul_eq_mul, hc₀', hc₁', hc₂', hu, hv, map_zero, mul_zero, zero_mul,
      zero_add, add_zero] at h
    simpa using h
  have hE1 : algebraMap R L c₀ * (algebraMap R L A₂ * u)
      + algebraMap R L c₀ * (algebraMap R L A₁ * v) = algebraMap R L γ := by
    simp only [hγdef, map_sub, map_mul, hE1raw]
    ring
  have hE2raw : algebraMap R L γ′ = algebraMap R L c₀
        * (algebraMap R L A₂ * algebraMap R L A₁ + u * algebraMap R L (A₂′))
        + algebraMap R L c₀
        * (algebraMap R L A₁ * algebraMap R L A₂ + v * algebraMap R L (A₁′)) := by
    have h := congrArg Differential.deriv hE1
    simp only [DifferentialAlgebra.deriv_algebraMap, map_add, deriv_algebraMap_mul,
      Derivation.leibniz, smul_eq_mul, hc₀', hu, hv, map_zero, mul_zero, zero_mul, zero_add,
      add_zero] at h
    simpa using h.symm
  have hE2 : algebraMap R L c₀ * (algebraMap R L (A₂′) * u)
      + algebraMap R L c₀ * (algebraMap R L (A₁′) * v) = algebraMap R L δ := by
    simp only [hδdef, map_sub, map_mul, map_ofNat, hE2raw]
    ring
  have hkey : v * algebraMap R L (c₀ * (A₁ * A₂′ - A₂ * A₁′))
      = algebraMap R L (γ * A₂′ - δ * A₂) := by
    have h1 : algebraMap R L (A₂′) * (algebraMap R L c₀ * (algebraMap R L A₂ * u)
          + algebraMap R L c₀ * (algebraMap R L A₁ * v))
        = algebraMap R L (A₂′) * algebraMap R L γ :=
      congrArg (fun z : L => algebraMap R L (A₂′) * z) hE1
    have h2 : algebraMap R L A₂ * (algebraMap R L c₀ * (algebraMap R L (A₂′) * u)
          + algebraMap R L c₀ * (algebraMap R L (A₁′) * v))
        = algebraMap R L A₂ * algebraMap R L δ :=
      congrArg (fun z : L => algebraMap R L A₂ * z) hE2
    have hcomb : algebraMap R L (A₂′) * (algebraMap R L c₀ * (algebraMap R L A₂ * u)
            + algebraMap R L c₀ * (algebraMap R L A₁ * v))
          - algebraMap R L A₂ * (algebraMap R L c₀ * (algebraMap R L (A₂′) * u)
            + algebraMap R L c₀ * (algebraMap R L (A₁′) * v))
          = algebraMap R L (γ * A₂′ - δ * A₂) := by
      simp only [map_sub, map_mul]
      rw [h1, h2]
      ring
    rw [← hcomb]
    simp only [map_sub, map_mul]
    ring
  have hden : c₀ * (A₁ * A₂′ - A₂ * A₁′) ≠ 0 := mul_ne_zero hc₀ hΔ
  have hdenL : algebraMap R L (c₀ * (A₁ * A₂′ - A₂ * A₁′)) ≠ 0 :=
    fun h0 => hden ((algebraMap R L).injective (by rw [h0, map_zero]))
  refine ⟨(γ * A₂′ - δ * A₂) / (c₀ * (A₁ * A₂′ - A₂ * A₁′)), ?_⟩
  rw [map_div₀]
  exact (eq_div_iff hdenL).mpr hkey

omit [Differential R] [Differential L] [DifferentialAlgebra R L] in
/-- **The proportional case of the elimination (purely algebraic).**  Suppose that in the field
extension `L` of `R` the quadratic relation `c₀·u·v + c₁·u + c₂·v = r₀` holds together with
`v + λ·u = α`, where `c₀ ≠ 0` and `λ ≠ 0`.  Then `u` is algebraic over `R`.

With `μ := v - λ·u` the first relation is a quadratic equation for `u` over the field `R(μ)`, and
the second says `2λu = α - μ`; eliminating `u` between them exhibits `μ` — and then `u` — as the
root of an explicit quadratic polynomial over `R`.  (No differential hypothesis is involved: this
is the algebraic content of the degenerate case of the weight-two elimination, in which the two
logarithmic derivatives are proportional.) -/
theorem isAlgebraic_of_proportional_quadratic
    {lam c₀ c₁ c₂ r₀ α : R} (hlam : lam ≠ 0) (hc₀ : c₀ ≠ 0) {u v : L}
    (hrel : algebraMap R L r₀
      = algebraMap R L c₀ * (u * v) + algebraMap R L c₁ * u + algebraMap R L c₂ * v)
    (htv : algebraMap R L α = v + algebraMap R L lam * u) :
    IsAlgebraic R u := by
  have hlamL : algebraMap R L lam ≠ 0 :=
    fun h => hlam ((algebraMap R L).injective (by rw [h, map_zero]))
  have hc₀L : algebraMap R L c₀ ≠ 0 :=
    fun h => hc₀ ((algebraMap R L).injective (by rw [h, map_zero]))
  have h2R : (2 : R) ≠ 0 := by norm_num
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap R L)]
    exact fun h => h2R ((algebraMap R L).injective (by rw [h, map_zero]))
  have h2lamL : 2 * algebraMap R L lam ≠ 0 := mul_ne_zero h2L hlamL
  set mu : L := v - algebraMap R L lam * u with hmudef
  have hv_eq : v = algebraMap R L lam * u + mu := by rw [hmudef]; ring
  -- the relation with `v = λu + μ`
  have hquad : algebraMap R L c₀ * (algebraMap R L lam * u ^ 2)
      + (algebraMap R L c₀ * mu + algebraMap R L c₁ + algebraMap R L c₂ * algebraMap R L lam) * u
      + algebraMap R L c₂ * mu - algebraMap R L r₀ = 0 := by
    have h := hrel
    rw [hv_eq] at h
    rw [h]
    ring
  have hvm : v = algebraMap R L α - algebraMap R L lam * u := by
    rw [htv]; ring
  have hlin : 2 * algebraMap R L lam * u = algebraMap R L α - mu := by
    rw [hmudef, hvm]; ring
  have h2sq := congrArg (fun z : L => z ^ 2) hlin
  have h2m := congrArg (fun z : L => 2 * algebraMap R L lam * z) hlin
  -- the quadratic relation for `μ`
  have hq : -algebraMap R L c₀ * algebraMap R L lam * mu ^ 2
      + 2 * algebraMap R L lam * (algebraMap R L c₂ * algebraMap R L lam - algebraMap R L c₁) * mu
      + (algebraMap R L c₀ * algebraMap R L lam * algebraMap R L α ^ 2
        + 2 * algebraMap R L lam * algebraMap R L c₁ * algebraMap R L α
        + 2 * algebraMap R L c₂ * algebraMap R L lam ^ 2 * algebraMap R L α
        - 4 * algebraMap R L lam ^ 2 * algebraMap R L r₀) = 0 := by
    linear_combination (norm := ring_nf) (4 * algebraMap R L lam ^ 2) * hquad
      - (algebraMap R L c₀ * algebraMap R L lam) * h2sq
      - (algebraMap R L c₀ * mu + algebraMap R L c₁ + algebraMap R L c₂ * algebraMap R L lam) * h2m
  set P : Polynomial R := Polynomial.C (-(c₀ * lam)) * Polynomial.X ^ 2
      + Polynomial.C (2 * lam * (c₂ * lam - c₁)) * Polynomial.X
      + Polynomial.C (c₀ * lam * α ^ 2 + 2 * lam * c₁ * α + 2 * c₂ * lam ^ 2 * α
          - 4 * lam ^ 2 * r₀) with hPdef
  have hP : P ≠ 0 := by
    rw [hPdef]
    intro hzero
    have h2 := congrArg (fun p : Polynomial R => p.coeff 2) hzero
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C] at h2
    have h3 : -(c₀ * lam) = 0 := by simpa using h2
    exact (mul_ne_zero hc₀ hlam) (neg_eq_zero.mp h3)
  have hμalg : IsAlgebraic R mu := by
    refine ⟨P, hP, ?_⟩
    have hval : (Polynomial.aeval mu) P
        = (-algebraMap R L c₀ * algebraMap R L lam * mu ^ 2
          + 2 * algebraMap R L lam * (algebraMap R L c₂ * algebraMap R L lam - algebraMap R L c₁) * mu
          + (algebraMap R L c₀ * algebraMap R L lam * algebraMap R L α ^ 2
            + 2 * algebraMap R L lam * algebraMap R L c₁ * algebraMap R L α
            + 2 * algebraMap R L c₂ * algebraMap R L lam ^ 2 * algebraMap R L α
            - 4 * algebraMap R L lam ^ 2 * algebraMap R L r₀)) := by
      simp only [hPdef, Polynomial.aeval_def, Polynomial.eval₂_add, Polynomial.eval₂_sub,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow,
        map_mul, map_add, map_sub, map_neg, map_ofNat, map_pow]
      ring
    rw [hval, hq]
  have hu_eq : u = (algebraMap R L α - mu) / (2 * algebraMap R L lam) := by
    rw [eq_div_iff h2lamL]
    linear_combination (norm := ring_nf) hlin
  have h2int : IsIntegral R (2 * algebraMap R L lam) := by
    have h := isIntegral_algebraMap (R := R) (A := L) (x := (2 : R) * lam)
    rwa [map_mul, map_ofNat] at h
  have huint : IsIntegral R u := by
    rw [hu_eq, div_eq_mul_inv]
    exact ((isIntegral_algebraMap (R := R) (A := L) (x := α)).sub
      (isAlgebraic_iff_isIntegral.mp hμalg)).mul (IsIntegral.inv h2int)
  exact isAlgebraic_iff_isIntegral.mpr huint

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Proportional logarithmic derivatives force multiplicative dependence.**  If
`(dRat g)/g = λ·(dRat f)/f` for a constant `λ ∈ K`, then `f` and `g` are multiplicatively
dependent: some nontrivial product `f^m·g^n` (`(m,n) ≠ 0`) is a constant.

This is the multiplicative-dependence form of the weight-one Lindemann–Weierstrass theorem
(`exists_int_prod_zpow_const_of_sum_dRat_div_field`) applied to the relation
`(-λ)·(dRat f)/f + 1·(dRat g)/g = 0 = dRat 0`. -/
theorem exists_int_prod_zpow_const_of_logDeriv_eq_smul
    {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0) {lam : K}
    (h : dRat g / g = algebraMap K (RatFunc K) lam * (dRat f / f)) :
    ∃ m n : ℤ, (m ≠ 0 ∨ n ≠ 0) ∧ ∃ C : K, C ≠ 0 ∧
      f ^ m * g ^ n = algebraMap K (RatFunc K) C := by
  set F : Fin 2 → RatFunc K := ![f, g] with hF
  set c : Fin 2 → K := ![-lam, 1] with hc
  have hF0 : ∀ i, F i ≠ 0 := by
    intro i; fin_cases i
    · simpa [hF] using hf
    · simpa [hF] using hg
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : c 1 = 0 := congrFun h0 1
    simp [hc] at h1
  have hsum : ∃ h₀ : RatFunc K,
      ∑ i, algebraMap K (RatFunc K) (c i) * (dRat (F i) / F i) = dRat h₀ := by
    refine ⟨0, ?_⟩
    have h0 : F 0 = f := by simp [hF]
    have h1 : F 1 = g := by simp [hF]
    have hcval0 : c 0 = -lam := by simp [hc]
    have hcval1 : c 1 = 1 := by simp [hc]
    rw [Fin.sum_univ_two, h0, h1, hcval0, hcval1, dRat_zero, map_neg, map_one, one_mul]
    rw [h]
    ring
  obtain ⟨m, hm, C, hC, hprod⟩ :=
    exists_int_prod_zpow_const_of_sum_dRat_div_field F hF0 c hc0 hsum
  refine ⟨m 0, m 1, ?_, C, hC, ?_⟩
  · by_contra hmn
    push Not at hmn
    exact hm (funext (fun i => by fin_cases i <;> simp [hmn.1, hmn.2]))
  · simpa [hF, Fin.prod_univ_two] using hprod

variable {L : Type*} [Field L] [Algebra (RatFunc K) L] [Differential (RatFunc K)]
  [Differential L] [DifferentialAlgebra (RatFunc K) L]

/-- **Independence form of the weight-two function-field Lindemann–Weierstrass theorem.**

Let `f, g ∈ K(X)` be nonconstant rational functions and let `u, v` be elements of a differential
field extension `L` of `K(X)` with `u' = (dRat f)/f` and `v' = (dRat g)/g`.  Then no *quadratic*
expression `c₀·u·v + c₁·u + c₂·v` with `c₀ ≠ 0` is a rational function.

Unlike the weight-one statement (`not_exists_sum_eq_algebraMap`, which needs the multiplicative
independence of `f` and `g`), **no independence hypothesis is required here**: the quadratic term
forces the contradiction by itself.

* If the Wronskian `A₁'A₂ - A₁A₂'` of the logarithmic derivatives `A₁ = (dRat f)/f`,
  `A₂ = (dRat g)/g` is nonzero, two differentiations of the relation together with Cramer's rule
  (`exists_algebraMap_of_quadratic_relation`) exhibit `v` as a rational function, contradicting the
  transcendence of `v` (weight-one Lindemann–Weierstrass).
* If the Wronskian vanishes, then `dRat (A₂/A₁) = 0`, so `A₂ = λ·A₁` for a constant `λ ∈ K`;
  differentiating once more shows that `v + λu` is a rational function, and then
  (`isAlgebraic_of_proportional_quadratic`) `u` is algebraic over `K(X)` — contradicting the
  transcendence of `u`. -/
theorem not_exists_quadratic_eq_algebraMap
    (hderiv : ∀ r : RatFunc K, Differential.deriv r = dRat r)
    (f g : RatFunc K) (hf : dRat f ≠ 0) (hg : dRat g ≠ 0)
    (c₀ c₁ c₂ : K) (hc₀ : c₀ ≠ 0) (u v : L)
    (hu : Differential.deriv u = algebraMap (RatFunc K) L (dRat f / f))
    (hv : Differential.deriv v = algebraMap (RatFunc K) L (dRat g / g)) :
    ¬ ∃ r₀ : RatFunc K,
      algebraMap (RatFunc K) L (algebraMap K (RatFunc K) c₀) * (u * v)
        + algebraMap (RatFunc K) L (algebraMap K (RatFunc K) c₁) * u
        + algebraMap (RatFunc K) L (algebraMap K (RatFunc K) c₂) * v
      = algebraMap (RatFunc K) L r₀ := by
  rintro ⟨r₀, hrel⟩
  set A₁ : RatFunc K := dRat f / f with hA₁
  set A₂ : RatFunc K := dRat g / g with hA₂
  have hf0 : f ≠ 0 := fun h => hf (by rw [h, dRat_zero])
  have hg0 : g ≠ 0 := fun h => hg (by rw [h, dRat_zero])
  have hA₁0 : A₁ ≠ 0 := by rw [hA₁]; exact div_ne_zero hf hf0
  have hA₂0 : A₂ ≠ 0 := by rw [hA₂]; exact div_ne_zero hg hg0
  have hu' : Differential.deriv u = algebraMap (RatFunc K) L A₁ := by rw [hA₁]; exact hu
  have hv' : Differential.deriv v = algebraMap (RatFunc K) L A₂ := by rw [hA₂]; exact hv
  -- the constants `c₀,c₁,c₂` are constants
  have hc₀c : (algebraMap K (RatFunc K) c₀)′ = 0 := by rw [hderiv, dRat_const]
  have hc₁c : (algebraMap K (RatFunc K) c₁)′ = 0 := by rw [hderiv, dRat_const]
  have hc₂c : (algebraMap K (RatFunc K) c₂)′ = 0 := by rw [hderiv, dRat_const]
  have hc₀K : algebraMap K (RatFunc K) c₀ ≠ 0 := fun h =>
    hc₀ ((algebraMap K (RatFunc K)).injective (by rw [h, map_zero]))
  have hA₁L : algebraMap (RatFunc K) L A₁ ≠ 0 := fun h =>
    hA₁0 ((algebraMap (RatFunc K) L).injective (by rw [h, map_zero]))
  by_cases hW : A₁ * A₂′ - A₂ * A₁′ = 0
  · -- proportional logarithmic derivatives
    have hWu : A₁ * dRat A₂ - A₂ * dRat A₁ = 0 := by simpa only [hderiv] using hW
    have hnum : dRat A₂ * A₁ - A₂ * dRat A₁ = 0 := by
      rw [mul_comm (dRat A₂) A₁]; exact hWu
    have hquot : dRat (A₂ / A₁) = 0 := by
      have h1 : dRat (A₂ / A₁) = (dRat A₂ * A₁ - A₂ * dRat A₁) / A₁ ^ 2 := by
        rw [div_eq_mul_inv, dRat_mul, dRat_inv A₁ hA₁0]
        field_simp
        ring
      rw [h1, hnum, zero_div]
    obtain ⟨lam, hlam⟩ := exists_const_of_dRat_eq_zero hquot
    set lamR : RatFunc K := algebraMap K (RatFunc K) lam with hlamR
    have hA₂eq : A₂ = lamR * A₁ := (div_eq_iff hA₁0).mp hlam
    have hlam0 : lam ≠ 0 := by
      intro h0
      have h1 : A₂ = 0 := by rw [hA₂eq, hlamR, h0, map_zero, zero_mul]
      exact hA₂0 h1
    -- differentiate the relation: `c₀·(v + λu) = r₀'/A₁ - (c₁ + c₂λ)`
    have hdiff : algebraMap (RatFunc K) L (dRat r₀)
        = algebraMap (RatFunc K) L (algebraMap K (RatFunc K) c₀)
            * (u * algebraMap (RatFunc K) L A₂ + v * algebraMap (RatFunc K) L A₁)
          + algebraMap (RatFunc K) L (algebraMap K (RatFunc K) c₁)
            * algebraMap (RatFunc K) L A₁
          + algebraMap (RatFunc K) L (algebraMap K (RatFunc K) c₂)
            * algebraMap (RatFunc K) L A₂ := by
      have h := congrArg Differential.deriv hrel
      simp only [DifferentialAlgebra.deriv_algebraMap, hderiv, dRat_const, map_add,
        deriv_algebraMap_mul, Derivation.leibniz, smul_eq_mul, hu', hv', map_zero, mul_zero,
        zero_mul, zero_add, add_zero] at h
      simpa using h.symm
    have hV : algebraMap (RatFunc K) L (algebraMap K (RatFunc K) c₀)
          * (v + algebraMap (RatFunc K) L lamR * u)
        = algebraMap (RatFunc K) L
            (dRat r₀ / A₁ - (algebraMap K (RatFunc K) c₁ + algebraMap K (RatFunc K) c₂ * lamR)) := by
      rw [map_sub, map_div₀, map_add, map_mul, hdiff, hA₂eq, map_mul]
      field_simp
      ring
    have htv : algebraMap (RatFunc K) L
          ((dRat r₀ / A₁ - (algebraMap K (RatFunc K) c₁ + algebraMap K (RatFunc K) c₂ * lamR))
            / algebraMap K (RatFunc K) c₀)
        = v + algebraMap (RatFunc K) L lamR * u := by
      rw [map_div₀, ← hV]
      exact mul_div_cancel_left₀ _ (fun h => hc₀K ((algebraMap (RatFunc K) L).injective
        (by rw [h, map_zero])))
    exact transcendental_of_deriv_eq_dRat_div hderiv f hf u hu
      (isAlgebraic_of_proportional_quadratic (R := RatFunc K) (L := L)
        (lam := lamR) (c₀ := algebraMap K (RatFunc K) c₀)
        (c₁ := algebraMap K (RatFunc K) c₁) (c₂ := algebraMap K (RatFunc K) c₂)
        (fun h => hlam0 ((algebraMap K (RatFunc K)).injective (by rw [← hlamR, h, map_zero])))
        hc₀K hrel.symm htv)
  · -- nonzero Wronskian
    obtain ⟨r, hr⟩ := exists_algebraMap_of_quadratic_relation
      (A₁ := A₁) (A₂ := A₂) hW (c₀ := algebraMap K (RatFunc K) c₀)
      (c₁ := algebraMap K (RatFunc K) c₁) (c₂ := algebraMap K (RatFunc K) c₂)
      hc₀K hc₀c hc₁c hc₂c hu' hv' hrel.symm
    exact transcendental_notMem_range v
      (transcendental_of_deriv_eq_dRat_div hderiv g hg v hv) ⟨r, hr⟩

end Submission.CDT
