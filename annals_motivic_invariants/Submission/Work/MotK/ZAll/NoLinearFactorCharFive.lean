import Mathlib
import Submission.Work.MotK.TGen.ZS1.shape_le_one
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.ZAll

open Polynomial

private lemma add_pow_five {R : Type*} [CommSemiring R] [CharP R 5] (x y : R) :
    (x + y) ^(5:ℕ) = x ^(5:ℕ) + y ^(5:ℕ) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact add_pow_char x y 5

private lemma linear_pow_five {K : Type*} [CommSemiring K] [CharP K 5] (p q : K) :
    (Polynomial.C p * Polynomial.X + Polynomial.C q) ^(5:ℕ)
      = Polynomial.C (p ^(5:ℕ)) * Polynomial.X ^(5:ℕ) + Polynomial.C (q ^(5:ℕ)) := by
  rw [add_pow_five, mul_pow, ← Polynomial.C_pow, ← Polynomial.C_pow]

private lemma C_mul_X_pow_five {K : Type*} [CommSemiring K] (r : K) :
    (Polynomial.C r * Polynomial.X : Polynomial K) ^(5:ℕ)
      = Polynomial.C (r ^(5:ℕ)) * Polynomial.X ^(5:ℕ) := by
  rw [mul_pow, ← Polynomial.C_pow]

private lemma natDegree_C_mul_X_le {K : Type*} [Semiring K] (p : K) :
    (Polynomial.C p * Polynomial.X : Polynomial K).natDegree ≤ 1 :=
  (Polynomial.natDegree_C_mul_le p Polynomial.X).trans Polynomial.natDegree_X_le

private lemma natDegree_C_mul_X_pow_le {K : Type*} [Semiring K] (p : K) (n : ℕ) :
    (Polynomial.C p * Polynomial.X ^ n : Polynomial K).natDegree ≤ n := by
  have h1 : (Polynomial.C p : Polynomial K).natDegree = 0 := Polynomial.natDegree_C p
  have h2 : (Polynomial.X ^ n : Polynomial K).natDegree ≤ n := Polynomial.natDegree_X_pow_le n
  have h := Polynomial.natDegree_mul_le (p := Polynomial.C p) (q := Polynomial.X ^ n)
  omega

private lemma natDegree_lin_le {K : Type*} [Semiring K] (p q : K) :
    (Polynomial.C p * Polynomial.X + Polynomial.C q : Polynomial K).natDegree ≤ 1 := by
  have h1 := natDegree_C_mul_X_le p
  have h2 : (Polynomial.C q : Polynomial K).natDegree = 0 := Polynomial.natDegree_C q
  have h := Polynomial.natDegree_add_le (Polynomial.C p * Polynomial.X) (Polynomial.C q)
  omega

private lemma natDegree_sq_mul_le {K : Type*} [Semiring K] (p q r : K) :
    ((Polynomial.C p * Polynomial.X + Polynomial.C q) ^(2:ℕ) * (Polynomial.C r * Polynomial.X)
      : Polynomial K).natDegree ≤ 3 := by
  have h1 : ((Polynomial.C p * Polynomial.X + Polynomial.C q : Polynomial K) ^(2:ℕ)).natDegree
      ≤ 2 := by
    have hlin := natDegree_lin_le p q
    have h := Polynomial.natDegree_pow_le
      (p := Polynomial.C p * Polynomial.X + Polynomial.C q) (n := 2)
    omega
  have h2 := natDegree_C_mul_X_le r
  have h := Polynomial.natDegree_mul_le
    (p := (Polynomial.C p * Polynomial.X + Polynomial.C q) ^(2:ℕ))
    (q := Polynomial.C r * Polynomial.X)
  omega

private lemma natDegree_lin_mul_cube_le {K : Type*} [Semiring K] (p q r : K) :
    ((Polynomial.C p * Polynomial.X + Polynomial.C q)
      * (Polynomial.C r * Polynomial.X : Polynomial K) ^(3:ℕ)).natDegree ≤ 4 := by
  have h1 := natDegree_lin_le p q
  have h2 : ((Polynomial.C r * Polynomial.X : Polynomial K) ^(3:ℕ)).natDegree ≤ 3 := by
    have hlin := natDegree_C_mul_X_le r
    have h := Polynomial.natDegree_pow_le (p := Polynomial.C r * Polynomial.X) (n := 3)
    omega
  have h := Polynomial.natDegree_mul_le (p := Polynomial.C p * Polynomial.X + Polynomial.C q)
    (q := (Polynomial.C r * Polynomial.X) ^(3:ℕ))
  omega

private lemma coeff_five {K : Type*} [CommSemiring K] (s : K) (r : Polynomial K)
    (hr : r.natDegree ≤ 4) : (Polynomial.C s * Polynomial.X ^(5:ℕ) + r).coeff 5 = s := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hr (by norm_num : 4 < 5))]
  simp

private lemma coeff_five_C_mul_X_pow {K : Type*} [CommSemiring K] (s : K) :
    ((Polynomial.C s * Polynomial.X ^(5:ℕ) : Polynomial K)).coeff 5 = s := by
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  simp

private lemma coeff_four_lin_mul_cube {K : Type*} [CommSemiring K] (p q r : K) :
    ((Polynomial.C p * Polynomial.X + Polynomial.C q)
      * (Polynomial.C r * Polynomial.X : Polynomial K) ^(3:ℕ)).coeff 4 = p * r ^(3:ℕ) := by
  have h3 : (Polynomial.C r * Polynomial.X : Polynomial K) ^(3:ℕ)
      = Polynomial.C (r ^(3:ℕ)) * Polynomial.X ^(3:ℕ) := by
    rw [mul_pow, ← Polynomial.C_pow]
  rw [h3, add_mul, Polynomial.coeff_add]
  have hA : ((Polynomial.C p * Polynomial.X) * (Polynomial.C (r ^(3:ℕ)) * Polynomial.X ^(3:ℕ))
      : Polynomial K).coeff 4 = p * r ^(3:ℕ) := by
    rw [mul_mul_mul_comm, ← Polynomial.C_mul, ← pow_succ', Polynomial.coeff_C_mul_X_pow]
    simp
  have hB : (Polynomial.C q * (Polynomial.C (r ^(3:ℕ)) * Polynomial.X ^(3:ℕ))
      : Polynomial K).coeff 4 = 0 := by
    rw [← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
      if_neg (by norm_num : (4 : ℕ) ≠ 3)]
  rw [hA, hB, add_zero]

private lemma C_mul_lin_add {K : Type*} [CommSemiring K] (p q s : K) :
    Polynomial.C p * (Polynomial.C q * Polynomial.X + Polynomial.C s : Polynomial K)
      = Polynomial.C (p * q) * Polynomial.X + Polynomial.C (p * s) := by
  rw [mul_add, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul]

private lemma C_mul_C_mul_X {K : Type*} [CommSemiring K] (p q : K) :
    Polynomial.C p * (Polynomial.C q * Polynomial.X : Polynomial K)
      = Polynomial.C (p * q) * Polynomial.X := by
  rw [← mul_assoc, ← Polynomial.C_mul]

private lemma mul_neg_div_self {K : Type*} [Field K] (a b : K) (ha : a ≠ 0) :
    a * (-(b / a)) = -b := by
  have h3 : a * a⁻¹ = 1 := by
    rw [mul_comm a a⁻¹, inv_mul_cancel₀ ha]
  rw [mul_neg, neg_inj, div_eq_mul_inv]
  calc a * (b * a⁻¹) = (a * a⁻¹) * b := by ring
    _ = 1 * b := by rw [h3]
    _ = b := by rw [one_mul]

private lemma single_one_five_ne_zero_five :
    (Finsupp.single (1 : Fin 2) (5 : ℕ)) ≠ (Finsupp.single (0 : Fin 2) 5) := by
  intro hh
  have h1 : (Finsupp.single (1 : Fin 2) (5 : ℕ)) 0 = (Finsupp.single (0 : Fin 2) 5) 0 := by
    rw [hh]
  rw [Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), Finsupp.single_eq_same] at h1
  exact absurd h1 (by norm_num)

private lemma sum_single_zero_five :
    ∑ i ∈ (Finsupp.single (0 : Fin 2) (5 : ℕ) : Fin 2 →₀ ℕ).support,
        (Finsupp.single (0 : Fin 2) (5 : ℕ) : Fin 2 →₀ ℕ) i = 5 := by
  simp

/-- In characteristic `5`, the five-term quintic `f = a X₀⁵ + b X₀²X₁ + c X₀X₁³ + d X₁⁵ + e`
(with `a,d,e ≠ 0`) is not the product of a polynomial of total degree `≤ 1` and one of total
degree `≤ 4` unless the coefficient `c` of `X₀X₁³` vanishes.

This is the `(1,4)`-case core of `Work.MotK.TGen.ZElim2IrredCharAll` in characteristic `5`.

The shortest route (found by a reviewer, uses only `h5`, `ha` and `hd`): since `a ≠ 0` we have
`f ≠ 0` and `g.totalDegree = 1`; write `g = uX+vY+w` with `(u,v) ≠ 0`.
* If `u ≠ 0`: put `φ : MvPolynomial (Fin 2) K →ₐ[K] K[X]` by `X ↦ C (v/u) * X + C (w/u)`,
  `Y ↦ X` (restriction to the line `{g = 0}`).  Then `φ (g*h) = 0`, and in char `5`
  `φ (aX⁵) = a*(C (v/u)*X + C (w/u))^5 = C (a*(v/u)^5) * X^5 + C (a*(w/u)^5)`, `φ (dY⁵) = C d * X^5`,
  `φ (bX²Y)` has `X²`-degree `≤ 3`, so the coefficient of `X⁴` in `φ f` is `c*(v/u)`; hence
  `c*(v/u) = 0`, and if `c ≠ 0` then `v = 0`, and then the coefficient of `X⁵`, namely
  `a*(v/u)^5 + d = d`, would be `0`, contradicting `hd`.
* If `u = 0`: then `g = v(Y + w/v)` and `φ : X ↦ X, Y ↦ C (-w/v)` gives `φ f = 0` whose `X⁵`
  coefficient is `a ≠ 0`, a contradiction (whatever `c` is).

So `c = 0`.  (A longer route, with the same conclusion, is the degree-graded one sketched in the
docstring of `Work.MotK.ZAll.NoQuadFactorCharFive`: `h₄ = h₄₀(X-ρY)⁴`, `h₁ = -(g₁/p)h₀`, …,
`h₄ = cXY³/p - b·g₁X²Y/p² + g₁⁴h₀/p⁴`, then compare the `X⁴`, `X³Y` and `XY³` coefficients.) -/
theorem NoLinearFactorCharFive {K : Type} [Field K] (h5 : (5 : K) = 0) (a b c d e : K)
    (ha : a ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (g h : MvPolynomial (Fin 2) K)
    (hg : g.totalDegree ≤ 1) (hh : h.totalDegree ≤ 4)
    (hgh : g * h = MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(5:ℕ)
      + MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ) * MvPolynomial.X 1
      + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(3:ℕ)
      + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(5:ℕ) + MvPolynomial.C e) :
    c = 0 := by
  have hchar : CharP K 5 := (CharP.charP_iff_prime_eq_zero (by norm_num)).mpr h5
  haveI : CharP K 5 := hchar
  obtain ⟨u, v, w, hgu⟩ := Work.MotK.TGen.ZS1.shape_le_one g hg
  set F : MvPolynomial (Fin 2) K :=
    MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(5:ℕ)
      + MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ) * MvPolynomial.X 1
      + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(3:ℕ)
      + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(5:ℕ)
      + MvPolynomial.C e with hFdef
  have hghF : g * h = F := by rw [hFdef]; exact hgh
  let P : MvPolynomial (Fin 2) K :=
    MvPolynomial.C a * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(5:ℕ)
      + MvPolynomial.C d * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(5:ℕ)
  let R : MvPolynomial (Fin 2) K :=
    MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ) * MvPolynomial.X 1
      + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(3:ℕ)
      + MvPolynomial.C e
  have hsplit : F = P + R := by rw [hFdef]; simp only [P, R]; ring
  have hPcoeff : P.coeff (Finsupp.single (0 : Fin 2) (5 : ℕ)) = a := by
    simp only [P]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X_pow]
    rw [if_neg single_one_five_ne_zero_five]
    simp
  have hRdeg : R.totalDegree ≤ 4 := by
    simp only [R]
    have hb2 : (MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ)).totalDegree
        ≤ 2 := by
      have h := MvPolynomial.totalDegree_mul (MvPolynomial.C b)
        ((MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ))
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow] at h
      omega
    have hc1 : (MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)).totalDegree
        ≤ 1 := by
      have h := MvPolynomial.totalDegree_mul (MvPolynomial.C c)
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X] at h
      omega
    have hX1 : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K).totalDegree = 1 :=
      MvPolynomial.totalDegree_X 1
    have hX13 : ((MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^(3:ℕ)).totalDegree = 3 :=
      MvPolynomial.totalDegree_X_pow 1 3
    have hCe : (MvPolynomial.C e : MvPolynomial (Fin 2) K).totalDegree = 0 :=
      MvPolynomial.totalDegree_C e
    have ht1 : (MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ)
        * MvPolynomial.X 1 : MvPolynomial (Fin 2) K).totalDegree ≤ 3 := by
      have h := MvPolynomial.totalDegree_mul
        (MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ))
        (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K)
      omega
    have ht2 : (MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
        * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(3:ℕ)
        : MvPolynomial (Fin 2) K).totalDegree ≤ 4 := by
      have h := MvPolynomial.totalDegree_mul
        (MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K))
        ((MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) ^(3:ℕ))
      omega
    have h := MvPolynomial.totalDegree_add
      (MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ) * MvPolynomial.X 1
        + MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
          * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(3:ℕ))
      (MvPolynomial.C e)
    have h2 := MvPolynomial.totalDegree_add
      (MvPolynomial.C b * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^(2:ℕ) * MvPolynomial.X 1)
      (MvPolynomial.C c * (MvPolynomial.X 0 : MvPolynomial (Fin 2) K)
        * (MvPolynomial.X 1 : MvPolynomial (Fin 2) K) ^(3:ℕ))
    omega
  have hRcoeff : R.coeff (Finsupp.single (0 : Fin 2) (5 : ℕ)) = 0 := by
    apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
    rw [sum_single_zero_five]
    exact lt_of_le_of_lt hRdeg (by norm_num)
  have hFcoeff : F.coeff (Finsupp.single (0 : Fin 2) (5 : ℕ)) = a := by
    rw [hsplit, MvPolynomial.coeff_add, hPcoeff, hRcoeff, add_zero]
  rcases eq_or_ne u 0 with hu | hu
  · rcases eq_or_ne v 0 with hv | hv
    · -- `u = 0`, `v = 0` : `g` is constant
      exfalso
      have hconst : g = MvPolynomial.C w := by
        rw [hgu, hu, hv]
        simp
      rcases eq_or_ne w 0 with hw | hw
      · have hF0 : F = 0 := by rw [← hghF, hconst, hw, MvPolynomial.C_0, zero_mul]
        rw [hF0] at hFcoeff
        exact ha (by simpa using hFcoeff.symm)
      · have hh_eq : h = MvPolynomial.C w⁻¹ * F := by
          rw [← hghF, hconst]
          rw [← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hw, MvPolynomial.C_1, one_mul]
        have hhcoeff : h.coeff (Finsupp.single (0 : Fin 2) (5 : ℕ)) = 0 := by
          apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
          rw [sum_single_zero_five]
          omega
        rw [hh_eq, MvPolynomial.coeff_C_mul, hFcoeff] at hhcoeff
        exact absurd hhcoeff (mul_ne_zero (inv_ne_zero hw) ha)
    · -- `u = 0`, `v ≠ 0` : substitute `X₀ ↦ X`, `X₁ ↦ -w/v`
      exfalso
      have hgB : g = MvPolynomial.C v * MvPolynomial.X 1 + MvPolynomial.C w := by
        rw [hgu, hu]
        simp
      let ψ : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
        MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then Polynomial.X
          else Polynomial.C (-(w/v)))
      have hψ0 : ψ (MvPolynomial.X 0) = Polynomial.X := by
        simp only [ψ, MvPolynomial.aeval_X]
        simp
      have hψ1 : ψ (MvPolynomial.X 1) = Polynomial.C (-(w/v)) := by
        simp only [ψ, MvPolynomial.aeval_X]
        simp
      have hψC : ∀ r : K, ψ (MvPolynomial.C r) = Polynomial.C r := by
        intro r
        simp only [ψ, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
      have hψg : ψ g = 0 := by
        rw [hgB]
        simp only [map_add, map_mul, hψ0, hψ1, hψC]
        have hx : v * (-(w / v)) + w = 0 := by
          rw [mul_neg_div_self v w hv, neg_add_cancel]
        calc Polynomial.C v * Polynomial.C (-(w / v)) + Polynomial.C w
            = Polynomial.C (v * (-(w / v))) + Polynomial.C w := by
              rw [← Polynomial.C_mul]
          _ = Polynomial.C (v * (-(w / v)) + w) := by rw [← Polynomial.C_add]
          _ = Polynomial.C 0 := by rw [hx]
          _ = 0 := Polynomial.C_0
      have hψF0 : ψ F = 0 := by rw [← hghF, map_mul, hψg, zero_mul]
      have hψf : ψ F = Polynomial.C a * Polynomial.X ^(5:ℕ)
          + (Polynomial.C b * Polynomial.X ^(2:ℕ) * Polynomial.C (-(w/v))
              + Polynomial.C c * Polynomial.X * Polynomial.C (-(w/v)) ^(3:ℕ)
              + Polynomial.C d * Polynomial.C (-(w/v)) ^(5:ℕ) + Polynomial.C e) := by
        rw [hFdef]
        simp only [ψ, map_add, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
          Polynomial.algebraMap_eq]
        simp
        first | refl_ring1 | ring
      have hrest : (Polynomial.C b * Polynomial.X ^(2:ℕ) * Polynomial.C (-(w/v))
              + Polynomial.C c * Polynomial.X * Polynomial.C (-(w/v)) ^(3:ℕ)
              + Polynomial.C d * Polynomial.C (-(w/v)) ^(5:ℕ) + Polynomial.C e
              : Polynomial K).natDegree ≤ 4 := by
        have hT1 : (Polynomial.C b * Polynomial.X ^(2:ℕ) * Polynomial.C (-(w/v))
            : Polynomial K).natDegree ≤ 2 := by
          have h1 := natDegree_C_mul_X_pow_le b 2
          have h2 : (Polynomial.C (-(w/v)) : Polynomial K).natDegree = 0 :=
            Polynomial.natDegree_C _
          have h := Polynomial.natDegree_mul_le (p := Polynomial.C b * Polynomial.X ^(2:ℕ))
            (q := Polynomial.C (-(w/v)))
          omega
        have hT2 : (Polynomial.C c * Polynomial.X * (Polynomial.C (-(w/v))) ^(3:ℕ)
            : Polynomial K).natDegree ≤ 1 := by
          have h1 := natDegree_C_mul_X_le c
          have h2 : ((Polynomial.C (-(w/v)) : Polynomial K) ^(3:ℕ)).natDegree = 0 := by
            have hp := Polynomial.natDegree_pow_le (p := Polynomial.C (-(w/v))) (n := 3)
            have hc : (Polynomial.C (-(w/v)) : Polynomial K).natDegree = 0 :=
              Polynomial.natDegree_C _
            omega
          have h := Polynomial.natDegree_mul_le (p := Polynomial.C c * Polynomial.X)
            (q := (Polynomial.C (-(w/v))) ^(3:ℕ))
          omega
        have hT3 : (Polynomial.C d * (Polynomial.C (-(w/v))) ^(5:ℕ) : Polynomial K).natDegree
            ≤ 0 := by
          have h2 : ((Polynomial.C (-(w/v)) : Polynomial K) ^(5:ℕ)).natDegree = 0 := by
            have hp := Polynomial.natDegree_pow_le (p := Polynomial.C (-(w/v))) (n := 5)
            have hc : (Polynomial.C (-(w/v)) : Polynomial K).natDegree = 0 :=
              Polynomial.natDegree_C _
            omega
          have h := Polynomial.natDegree_mul_le (p := Polynomial.C d)
            (q := (Polynomial.C (-(w/v))) ^(5:ℕ))
          have hd0 : (Polynomial.C d : Polynomial K).natDegree = 0 := Polynomial.natDegree_C _
          omega
        have hT4 : (Polynomial.C e : Polynomial K).natDegree = 0 := Polynomial.natDegree_C _
        have h12 : (Polynomial.C b * Polynomial.X ^(2:ℕ) * Polynomial.C (-(w/v))
            + Polynomial.C c * Polynomial.X * (Polynomial.C (-(w/v))) ^(3:ℕ)
            : Polynomial K).natDegree ≤ 2 := by
          have h := Polynomial.natDegree_add_le
            (Polynomial.C b * Polynomial.X ^(2:ℕ) * Polynomial.C (-(w/v)))
            (Polynomial.C c * Polynomial.X * (Polynomial.C (-(w/v))) ^(3:ℕ))
          omega
        have h123 : (Polynomial.C b * Polynomial.X ^(2:ℕ) * Polynomial.C (-(w/v))
            + Polynomial.C c * Polynomial.X * (Polynomial.C (-(w/v))) ^(3:ℕ)
            + Polynomial.C d * (Polynomial.C (-(w/v))) ^(5:ℕ) : Polynomial K).natDegree ≤ 2 := by
          have h := Polynomial.natDegree_add_le
            (Polynomial.C b * Polynomial.X ^(2:ℕ) * Polynomial.C (-(w/v))
              + Polynomial.C c * Polynomial.X * (Polynomial.C (-(w/v))) ^(3:ℕ))
            (Polynomial.C d * (Polynomial.C (-(w/v))) ^(5:ℕ))
          omega
        have h := Polynomial.natDegree_add_le
          (Polynomial.C b * Polynomial.X ^(2:ℕ) * Polynomial.C (-(w/v))
            + Polynomial.C c * Polynomial.X * (Polynomial.C (-(w/v))) ^(3:ℕ)
            + Polynomial.C d * (Polynomial.C (-(w/v))) ^(5:ℕ))
          (Polynomial.C e)
        omega
      have hc5 : (ψ F).coeff 5 = a := by
        rw [hψf]
        exact coeff_five a _ hrest
      exact ha (by rw [← hc5, hψF0]; simp)
  · -- `u ≠ 0` : substitute `X₀ ↦ C (-v) * X + C (-(w/u))`, `X₁ ↦ C u * X`
    let L : Polynomial K := Polynomial.C (-v) * Polynomial.X + Polynomial.C (-(w/u))
    let M : Polynomial K := Polynomial.C u * Polynomial.X
    let φ : MvPolynomial (Fin 2) K →ₐ[K] Polynomial K :=
      MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then L else M)
    have hφg : φ g = 0 := by
      rw [hgu]
      simp only [φ, map_add, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Polynomial.algebraMap_eq]
      simp
      rw [C_mul_lin_add u (-v) (-(w/u)), C_mul_C_mul_X v u]
      rw [mul_neg_div_self u w hu, Polynomial.C_neg]
      have h3 : Polynomial.C (u * (-v)) + Polynomial.C (v * u) = 0 := by
        rw [← Polynomial.C_add, show u * (-v) + v * u = 0 by ring, Polynomial.C_0]
      have key : Polynomial.C (u * (-v)) * Polynomial.X + -Polynomial.C w
            + Polynomial.C (v * u) * Polynomial.X + Polynomial.C w
          = (Polynomial.C (u * (-v)) + Polynomial.C (v * u)) * Polynomial.X
            + (-Polynomial.C w + Polynomial.C w) := by ring
      rw [key, h3, zero_mul, neg_add_cancel, add_zero]
    have hφF0 : φ F = 0 := by rw [← hghF, map_mul, hφg, zero_mul]
    have hL5 : L ^(5:ℕ) = Polynomial.C ((-v) ^(5:ℕ)) * Polynomial.X ^(5:ℕ)
        + Polynomial.C ((-(w/u)) ^(5:ℕ)) :=
      linear_pow_five (-v) (-(w/u))
    have hM5 : M ^(5:ℕ) = Polynomial.C (u ^(5:ℕ)) * Polynomial.X ^(5:ℕ) := C_mul_X_pow_five u
    have hL2M : (L ^(2:ℕ) * M : Polynomial K).natDegree ≤ 3 :=
      natDegree_sq_mul_le (-v) (-(w/u)) u
    have hLM3 : (L * M ^(3:ℕ) : Polynomial K).natDegree ≤ 4 :=
      natDegree_lin_mul_cube_le (-v) (-(w/u)) u
    have hφf : φ F = Polynomial.C a * L ^(5:ℕ) + Polynomial.C b * (L ^(2:ℕ) * M)
        + Polynomial.C c * (L * M ^(3:ℕ)) + Polynomial.C d * M ^(5:ℕ) + Polynomial.C e := by
      rw [hFdef]
      simp only [φ, map_add, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Polynomial.algebraMap_eq]
      simp
      first | refl_ring1 | ring
    have hc5 : (φ F).coeff 5 = a * (-v) ^(5:ℕ) + d * u ^(5:ℕ) := by
      have h1 : (L ^(5:ℕ) : Polynomial K).coeff 5 = (-v) ^(5:ℕ) := by
        rw [hL5]
        refine coeff_five ((-v) ^(5:ℕ)) (Polynomial.C ((-(w/u)) ^(5:ℕ))) ?_
        have hc : (Polynomial.C ((-(w/u)) ^(5:ℕ)) : Polynomial K).natDegree = 0 :=
          Polynomial.natDegree_C _
        omega
      have h2 : (L ^(2:ℕ) * M : Polynomial K).coeff 5 = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hL2M (by norm_num))
      have h3 : (L * M ^(3:ℕ) : Polynomial K).coeff 5 = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hLM3 (by norm_num))
      have h4 : (M ^(5:ℕ) : Polynomial K).coeff 5 = u ^(5:ℕ) := by
        rw [hM5]
        exact coeff_five_C_mul_X_pow (u ^(5:ℕ))
      have h5 : (Polynomial.C e : Polynomial K).coeff 5 = 0 :=
        Polynomial.coeff_C_of_ne_zero (by norm_num : (5 : ℕ) ≠ 0)
      rw [hφf]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, h1, h2, h3, h4, h5]
      first | refl_ring1 | ring
    have hc4 : (φ F).coeff 4 = c * ((-v) * u ^(3:ℕ)) := by
      have h1 : (L ^(5:ℕ) : Polynomial K).coeff 4 = 0 := by
        rw [hL5, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C,
          if_neg (by norm_num : (4 : ℕ) ≠ 5), if_neg (by norm_num : (4 : ℕ) ≠ 0)]
        first | refl_ring1 | ring
      have h2 : (L ^(2:ℕ) * M : Polynomial K).coeff 4 = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hL2M (by norm_num))
      have h3 : (L * M ^(3:ℕ) : Polynomial K).coeff 4 = (-v) * u ^(3:ℕ) := by
        simp only [L, M]
        exact coeff_four_lin_mul_cube (-v) (-(w/u)) u
      have h4 : (M ^(5:ℕ) : Polynomial K).coeff 4 = 0 := by
        rw [hM5, Polynomial.coeff_C_mul_X_pow, if_neg (by norm_num : (4 : ℕ) ≠ 5)]
      have h5 : (Polynomial.C e : Polynomial K).coeff 4 = 0 :=
        Polynomial.coeff_C_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)
      rw [hφf]
      simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, h1, h2, h3, h4, h5]
      first | refl_ring1 | ring
    have h5 : a * (-v) ^(5:ℕ) + d * u ^(5:ℕ) = 0 := by
      rw [← hc5, hφF0]
      simp
    have h4 : c * ((-v) * u ^(3:ℕ)) = 0 := by
      rw [← hc4, hφF0]
      simp
    by_contra hc
    have hv0 : v = 0 := by
      rcases mul_eq_zero.mp h4 with h' | h'
      · exact absurd h' hc
      · have h'' : v * u ^(3:ℕ) = 0 := by
          rw [neg_mul] at h'
          exact neg_eq_zero.mp h'
        rcases mul_eq_zero.mp h'' with h''' | h'''
        · exact h'''
        · exact absurd h''' (pow_ne_zero 3 hu)
    have hd0 : d = 0 := by
      have h5' : d * u ^(5:ℕ) = 0 := by
        have hh5 := h5
        rw [hv0] at hh5
        simpa using hh5
      rcases mul_eq_zero.mp h5' with h' | h'
      · exact h'
      · exact absurd h' (pow_ne_zero 5 hu)
    exact hd hd0

end Work.MotK.ZAll
