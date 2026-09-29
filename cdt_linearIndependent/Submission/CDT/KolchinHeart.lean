import Mathlib
import Submission.Commons.Algebra.Polynomial.coeff_mul_natDegree_le
import Submission.Commons.Algebra.Polynomial.coeff_mul_natDegree_le_sub_one

/-!
# Kolchin's lemma: the algebraic heart

This file contains the algebraic core of **Kolchin's lemma** ("no new constants"): if `R` is a
characteristic-zero differential field whose constants are the image of a field `K`, if `a ∈ R` is
not a derivative, and `P`, `Q` are polynomials over `R` satisfying

`(∂P)·Q - P·(∂Q) + a·(P'·Q - P·Q') = 0`

(where `∂ = Differential.mapCoeffs` differentiates the coefficients and `'` differentiates the
variable), then `P/Q` has no dependence on the variable: `P = (algebraMap c)·Q` for some `c : K`.

This is the algebraic content of the statement that `K(x)` has no constants beyond those of
`K(x)` when `x' = a` with `a` not a derivative; the differential-field statement on top of it is
in `Submission.CDT.KolchinField`.

## The proof

Write `p = deg P`, `q = deg Q`, and let `lp`, `lq` be the leading coefficients.  Comparing the
`X ^ (p+q)` coefficients of the identity gives `(∂lp)·lq = lp·(∂lq)`, so `λ := lp/lq` is a
constant; comparing the `X ^ (p+q-1)` coefficients gives

`∂(ν/lq) = -a·(p-q)·λ`,  where `ν = (P.coeff (p-1)) - λ·(Q.coeff (q-1))`,

which exhibits `a = ∂(-ν/((p-q)·λ·lq))` as a derivative: a contradiction when `a` is not one.  So
`deg P ≤ deg Q`; by symmetry (and, for `deg P < deg Q`, swapping the roles of `P` and `Q`, which
just changes the sign of the identity) actually `deg P = deg Q`, and then subtracting
`(algebraMap c)·Q` (with `λ = algebraMap c`) from `P` lowers the degree, contradicting the same
argument.  The case `deg Q = 0` is reduced to the case `deg Q ≥ 1` by multiplying both `P` and `Q`
by `X` (the identity is homogeneous of degree `2` in that operation).
-/

open scoped Differential

set_option linter.unusedSectionVars false

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K R : Type*} [Field K] [Field R] [Algebra K R] [CharZero R] [Differential R]

/-- The coefficientwise derivative does not raise the degree. -/
lemma natDegree_mapCoeffs_le (P : Polynomial R) :
    (Differential.mapCoeffs P).natDegree ≤ P.natDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [Differential.coeff_mapCoeffs, Polynomial.coeff_eq_zero_of_natDegree_lt hN, map_zero]

omit [CharZero R] in
/-- Quotient rule for a `ℤ`-derivation of a field. -/
lemma map_div' (D : Derivation ℤ R R) (a b : R) (hb : b ≠ 0) :
    D (a / b) = (D a * b - a * D b) / b ^ 2 := by
  rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, div_eq_mul_inv, inv_pow]
  field_simp
  ring

/-- Leibniz rule for the coefficientwise derivative. -/
lemma mapCoeffs_mul (P Q : Polynomial R) :
    Differential.mapCoeffs (P * Q) = P * Differential.mapCoeffs Q + Q * Differential.mapCoeffs P := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]

/-- `mapCoeffs` kills `X`. -/
lemma mapCoeffs_X : Differential.mapCoeffs (Polynomial.X : Polynomial R) = 0 :=
  Differential.mapCoeffs_X

/-- Extraction of the coefficient of `X ^ (a + b - 1)` of a product, where the second factor is
allowed to be a constant (in which case the corresponding term is absent). -/
lemma coeff_mul_sub_one' {S : Type*} [CommRing S] (A B : Polynomial S) (a b : ℕ)
    (hA : A.natDegree ≤ a) (hB : B.natDegree ≤ b) (ha : 1 ≤ a) :
    (A * B).coeff (a + b - 1)
      = A.coeff a * (if b = 0 then 0 else B.coeff (b - 1)) + A.coeff (a - 1) * B.coeff b := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [Nat.add_zero, if_pos rfl, mul_zero, zero_add]
    obtain rfl | hB0 := eq_or_ne B 0
    · simp
    · have hdeg : B.natDegree = 0 := by omega
      have hBc : B = Polynomial.C (B.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      rw [hBc, mul_comm A (Polynomial.C (B.coeff 0)), Polynomial.coeff_C_mul, Polynomial.coeff_C]
      exact mul_comm _ _
  · rw [if_neg hb]
    exact Commons.Algebra.Polynomial.coeff_mul_natDegree_le_sub_one A B a b
      ha (by omega) hA hB

/-- **The key case of Kolchin's lemma.**  If `deg Q < deg P`, `Q ≠ 0`, `a` is not a derivative in
`R` and the quadratic identity holds, then `a` *is* a derivative: a contradiction. -/
theorem exists_deriv_of_relation_of_natDegree_lt'
    {P Q : Polynomial R} (hQ : Q ≠ 0) (hq1 : 1 ≤ Q.natDegree)
    (hlt : Q.natDegree < P.natDegree) {a : R}
    (hrel : Differential.mapCoeffs P * Q - P * Differential.mapCoeffs Q
      + Polynomial.C a * (P.derivative * Q - P * Q.derivative) = 0) :
    ∃ b : R, b′ = a := by
  have hp1 : 1 ≤ P.natDegree := by omega
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hp1
    omega
  have hle : Q.natDegree ≤ P.natDegree := le_of_lt hlt
  set lp : R := P.coeff P.natDegree with hlp
  set lq : R := Q.coeff Q.natDegree with hlq
  have hlq0 : lq ≠ 0 := by
    rw [hlq, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hlp0 : lp ≠ 0 := by
    rw [hlp, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP0
  set q1 : R := Q.coeff (Q.natDegree - 1) with hq1def
  set p1 : R := P.coeff (P.natDegree - 1) with hp1def
  have hder_le_p : P.derivative.natDegree ≤ P.natDegree := by
    have := Polynomial.natDegree_derivative_le P
    omega
  have hder_le_q : Q.derivative.natDegree ≤ Q.natDegree := by
    have := Polynomial.natDegree_derivative_le Q
    omega
  -- the coefficient of `X ^ (p+q)`
  have htop1 : (P.derivative * Q).coeff (P.natDegree + Q.natDegree) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc (P.derivative * Q).natDegree ≤ P.derivative.natDegree + Q.natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ (P.natDegree - 1) + Q.natDegree :=
            Nat.add_le_add_right (Polynomial.natDegree_derivative_le P) _
      _ < P.natDegree + Q.natDegree :=
            Nat.add_lt_add_right (Nat.sub_one_lt (by omega)) _
  have htop2 : (P * Q.derivative).coeff (P.natDegree + Q.natDegree) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc (P * Q.derivative).natDegree ≤ P.natDegree + Q.derivative.natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ P.natDegree + (Q.natDegree - 1) :=
            Nat.add_le_add_left (Polynomial.natDegree_derivative_le Q) _
      _ < P.natDegree + Q.natDegree :=
            Nat.add_lt_add_left (Nat.sub_one_lt (by omega)) _
  have h1 : lp′ * lq - lp * lq′ = 0 := by
    have h := congrArg (fun T : Polynomial R => T.coeff (P.natDegree + Q.natDegree)) hrel
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
      Commons.Algebra.Polynomial.coeff_mul_natDegree_le (Differential.mapCoeffs P) Q
        P.natDegree Q.natDegree (natDegree_mapCoeffs_le P) le_rfl,
      Commons.Algebra.Polynomial.coeff_mul_natDegree_le P (Differential.mapCoeffs Q)
        P.natDegree Q.natDegree le_rfl (natDegree_mapCoeffs_le Q),
      Polynomial.coeff_C_mul, Differential.coeff_mapCoeffs, htop1, htop2, sub_zero, mul_zero,
      add_zero] at h
    rw [show P.coeff P.natDegree = lp from by rw [hlp, Polynomial.coeff_natDegree],
      show Q.coeff Q.natDegree = lq from by rw [hlq, Polynomial.coeff_natDegree]] at h
    simpa using h
  -- the coefficients of `X ^ (p+q-1)`
  have hcoeff_deriv : ∀ (S : Polynomial R) (n : ℕ),
      S.derivative.coeff n = (↑(n + 1) : R) * S.coeff (n + 1) := by
    intro S n
    rw [Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
    ring
  have hder1 : (P.derivative).coeff (P.natDegree - 1) = (P.natDegree : R) * lp := by
    rw [hcoeff_deriv, Nat.sub_add_cancel hp1,
      show P.coeff P.natDegree = lp from by rw [hlp, Polynomial.coeff_natDegree]]
  have hder2 : (P.derivative).coeff (P.natDegree) = 0 := by
    rw [hcoeff_deriv, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  have hderQ1 : (Q.derivative).coeff (Q.natDegree - 1) = (Q.natDegree : R) * lq := by
    rw [hcoeff_deriv, Nat.sub_add_cancel hq1,
      show Q.coeff Q.natDegree = lq from by rw [hlq, Polynomial.coeff_natDegree]]
  have hderQ2 : (Q.derivative).coeff (Q.natDegree) = 0 := by
    rw [hcoeff_deriv, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  have hbot1 : (P.derivative * Q).coeff (P.natDegree + Q.natDegree - 1)
      = (P.natDegree : R) * lp * lq := by
    rw [Commons.Algebra.Polynomial.coeff_mul_natDegree_le_sub_one P.derivative Q
          P.natDegree Q.natDegree (by omega) (by omega) hder_le_p le_rfl,
        hder1, hder2, zero_mul, zero_add,
        show Q.coeff Q.natDegree = lq from by rw [hlq, Polynomial.coeff_natDegree]]
  have hbot2 : (P * Q.derivative).coeff (P.natDegree + Q.natDegree - 1)
      = (Q.natDegree : R) * lp * lq := by
    rw [Commons.Algebra.Polynomial.coeff_mul_natDegree_le_sub_one P Q.derivative
          P.natDegree Q.natDegree (by omega) (by omega) le_rfl hder_le_q,
        hderQ1, hderQ2, mul_zero, add_zero,
        show P.coeff P.natDegree = lp from by rw [hlp, Polynomial.coeff_natDegree]]
    ring
  have hcast : (((P.natDegree - Q.natDegree : ℕ)) : R)
      = (P.natDegree : R) - (Q.natDegree : R) := Nat.cast_sub hle
  have h2 : lp′ * q1 + p1′ * lq - lp * q1′ - p1 * lq′
      + a * (((P.natDegree - Q.natDegree : ℕ)) : R) * lp * lq = 0 := by
    rw [hcast]
    have h := congrArg (fun T : Polynomial R => T.coeff (P.natDegree + Q.natDegree - 1)) hrel
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
      Commons.Algebra.Polynomial.coeff_mul_natDegree_le_sub_one (Differential.mapCoeffs P) Q
        P.natDegree Q.natDegree (by omega) (by omega) (natDegree_mapCoeffs_le P) le_rfl,
      Commons.Algebra.Polynomial.coeff_mul_natDegree_le_sub_one P (Differential.mapCoeffs Q)
        P.natDegree Q.natDegree (by omega) (by omega) le_rfl (natDegree_mapCoeffs_le Q),
      Polynomial.coeff_C_mul, Differential.coeff_mapCoeffs, hbot1, hbot2] at h
    rw [show P.coeff P.natDegree = lp from by rw [hlp, Polynomial.coeff_natDegree],
      show Q.coeff Q.natDegree = lq from by rw [hlq, Polynomial.coeff_natDegree]] at h
    rw [hq1def.symm, hp1def.symm] at h
    ring_nf at h ⊢
    exact h
  -- the algebra
  set lam : R := lp / lq with hlam
  have hlp_eq : lp = lam * lq := by rw [hlam, div_mul_cancel₀ _ hlq0]
  have hlam0 : lam ≠ 0 := by rw [hlam]; exact div_ne_zero hlp0 hlq0
  have hdlam : lam′ = 0 := by
    have h := h1
    rw [hlp_eq, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h
    have hsq : lam′ * lq ^ 2 = 0 := by linear_combination h
    exact (mul_eq_zero.mp hsq).resolve_right (pow_ne_zero 2 hlq0)
  set nu : R := p1 - lam * q1 with hnu
  have hnu' : nu′ = p1′ - lam * q1′ := by
    have h : (lam * q1)′ = lam * q1′ := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hdlam, mul_zero, add_zero]
    rw [hnu, sub_eq_add_neg, map_add, map_neg, h]
    ring
  have hEq : lq * (p1′ - lam * q1′) - (p1 - lam * q1) * lq′
      + a * (((P.natDegree - Q.natDegree : ℕ)) : R) * lam * lq ^ 2 = 0 := by
    have h := h2
    rw [hlp_eq, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hdlam, mul_zero, add_zero] at h
    ring_nf at h ⊢
    linear_combination (norm := ring_nf) h
  have hnatCast : ∀ n : ℕ, (((n : ℕ)) : R)′ = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, map_add, ih, zero_add]; simp
  set dR : R := (((P.natDegree - Q.natDegree : ℕ)) : R) with hdR
  have hdR0 : dR ≠ 0 := by
    rw [hdR, Nat.cast_ne_zero]
    omega
  have hdR' : dR′ = 0 := hnatCast _
  have hkey : nu′ * lq - nu * lq′ = -(a * dR * lam) * lq ^ 2 := by
    rw [hnu', hnu]
    linear_combination (norm := ring_nf) hEq
  have hmu : (nu / lq)′ = -(a * dR * lam) := by
    rw [map_div' (Differential.deriv : Derivation ℤ R R) nu lq hlq0, hkey,
      mul_div_cancel_right₀ _ (pow_ne_zero 2 hlq0)]
  have hc0 : dR * lam ≠ 0 := mul_ne_zero hdR0 hlam0
  have hcd : (dR * lam)′ = 0 := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hdR', hdlam, mul_zero, mul_zero, add_zero]
  refine ⟨-(nu / lq) / (dR * lam), ?_⟩
  rw [map_div' (Differential.deriv : Derivation ℤ R R) _ _ hc0, map_neg, hcd, hmu, mul_zero,
    sub_zero]
  field_simp

end Submission.CDT

namespace Submission.CDT

variable {K R : Type*} [Field K] [Field R] [Algebra K R] [CharZero R] [Differential R]

/-- The `X ^ (p+q)` coefficient of `P' * Q` vanishes when `Q ≠ 0`. -/
lemma coeff_deriv_mul_top (P Q : Polynomial R) :
    (P.derivative * Q).coeff (P.natDegree + Q.natDegree) = 0 := by
  have hder : P.derivative.natDegree ≤ P.natDegree :=
    le_trans (Polynomial.natDegree_derivative_le P) (Nat.sub_le _ _)
  rw [Commons.Algebra.Polynomial.coeff_mul_natDegree_le P.derivative Q P.natDegree Q.natDegree
      hder le_rfl, Polynomial.coeff_derivative,
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)]
  ring

/-- The `X ^ (p+q)` coefficient of `P * Q'` vanishes when `Q ≠ 0`. -/
lemma coeff_mul_deriv_top (P Q : Polynomial R) :
    (P * Q.derivative).coeff (P.natDegree + Q.natDegree) = 0 := by
  have hder : Q.derivative.natDegree ≤ Q.natDegree :=
    le_trans (Polynomial.natDegree_derivative_le Q) (Nat.sub_le _ _)
  rw [Commons.Algebra.Polynomial.coeff_mul_natDegree_le P Q.derivative P.natDegree Q.natDegree
      le_rfl hder, Polynomial.coeff_derivative,
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)]
  ring

/-- **The leading-coefficient relation.**  The `X ^ (p+q)` coefficient of the quadratic identity
gives `(lead P)' · lead Q = lead P · (lead Q)'`. -/
lemma leadingCoeff_deriv_relation {P Q : Polynomial R} {a : R}
    (hrel : Differential.mapCoeffs P * Q - P * Differential.mapCoeffs Q
      + Polynomial.C a * (P.derivative * Q - P * Q.derivative) = 0) (hQ : Q ≠ 0) :
    (P.leadingCoeff)′ * Q.leadingCoeff - P.leadingCoeff * (Q.leadingCoeff)′ = 0 := by
  have h := congrArg (fun T : Polynomial R => T.coeff (P.natDegree + Q.natDegree)) hrel
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
    Commons.Algebra.Polynomial.coeff_mul_natDegree_le (Differential.mapCoeffs P) Q
      P.natDegree Q.natDegree (natDegree_mapCoeffs_le P) le_rfl,
    Commons.Algebra.Polynomial.coeff_mul_natDegree_le P (Differential.mapCoeffs Q)
      P.natDegree Q.natDegree le_rfl (natDegree_mapCoeffs_le Q),
    Polynomial.coeff_C_mul, Differential.coeff_mapCoeffs, coeff_deriv_mul_top,
    coeff_mul_deriv_top, sub_zero, mul_zero, add_zero] at h
  rwa [Polynomial.coeff_natDegree, Polynomial.coeff_natDegree] at h

end Submission.CDT

namespace Submission.CDT

variable {K R : Type*} [Field K] [Field R] [Algebra K R] [CharZero R] [Differential R]

/-- **Kolchin's key case, general form**: `deg Q < deg P` forces `a` to be a derivative. -/
theorem exists_deriv_of_relation_of_natDegree_lt
    {P Q : Polynomial R} (hQ : Q ≠ 0) (hlt : Q.natDegree < P.natDegree) {a : R}
    (hrel : Differential.mapCoeffs P * Q - P * Differential.mapCoeffs Q
      + Polynomial.C a * (P.derivative * Q - P * Q.derivative) = 0) :
    ∃ b : R, b′ = a := by
  by_cases hq0 : Q.natDegree = 0
  · have hX : (Polynomial.X : Polynomial R) ≠ 0 := Polynomial.X_ne_zero
    have hPX : P * Polynomial.X ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp h with h1 | h2
      · rw [h1, Polynomial.natDegree_zero] at hlt
        omega
      · exact hX h2
    have hP0 : P ≠ 0 := by
      intro h
      rw [h, Polynomial.natDegree_zero] at hlt
      omega
    have hmulP : (P * Polynomial.X).natDegree = P.natDegree + 1 := by
      rw [Polynomial.natDegree_mul (p := P) (q := Polynomial.X) hP0 hX, Polynomial.natDegree_X]
    have hmulQ : (Q * Polynomial.X).natDegree = Q.natDegree + 1 := by
      rw [Polynomial.natDegree_mul (p := Q) (q := Polynomial.X) hQ hX, Polynomial.natDegree_X]
    have hrel' : Differential.mapCoeffs (P * Polynomial.X) * (Q * Polynomial.X)
        - (P * Polynomial.X) * Differential.mapCoeffs (Q * Polynomial.X)
        + Polynomial.C a * ((P * Polynomial.X).derivative * (Q * Polynomial.X)
          - (P * Polynomial.X) * (Q * Polynomial.X).derivative) = 0 := by
      have hm1 : Differential.mapCoeffs (P * Polynomial.X)
          = Polynomial.X * Differential.mapCoeffs P := by
        rw [mapCoeffs_mul, Differential.mapCoeffs_X, mul_zero, zero_add]
      have hm2 : Differential.mapCoeffs (Q * Polynomial.X)
          = Polynomial.X * Differential.mapCoeffs Q := by
        rw [mapCoeffs_mul, Differential.mapCoeffs_X, mul_zero, zero_add]
      rw [hm1, hm2, Polynomial.derivative_mul, Polynomial.derivative_mul,
        Polynomial.derivative_X, mul_one]
      linear_combination (norm := ring_nf) Polynomial.X ^ 2 * hrel
    exact exists_deriv_of_relation_of_natDegree_lt' (mul_ne_zero hQ hX) (by rw [hmulQ]; omega)
      (by rw [hmulP, hmulQ]; omega) hrel'
  · exact exists_deriv_of_relation_of_natDegree_lt' hQ (by omega) hlt hrel

end Submission.CDT

namespace Submission.CDT

variable {K R : Type*} [Field K] [Field R] [Algebra K R] [CharZero R] [Differential R]

/-- **Kolchin's lemma, algebraic heart.**  Let `P ≠ 0 = Q` be polynomials over a differential
field `R` whose constants are the image of a field `K` (`hconst`, `hconst'`), let `a ∈ R` be
*not* a derivative, and suppose the quadratic identity
`(mapCoeffs P)·Q - P·(mapCoeffs Q) + a·(P'·Q - P·Q') = 0`
holds (this is `∂(P/Q) + a·(P/Q)' = 0` for the coefficientwise derivative `∂`).  Then `P/Q` has no
`X`-dependence: `P = (algebraMap c)·Q` for some `c : K`. -/
theorem exists_algebraMap_C_mul_of_relation
    (hconst : ∀ r : R, r′ = 0 → ∃ c : K, r = algebraMap K R c)
    (hconst' : ∀ c : K, (algebraMap K R c)′ = 0)
    {P Q : Polynomial R} (hQ : Q ≠ 0) {a : R} (ha : ∀ b : R, b′ ≠ a)
    (hrel : Differential.mapCoeffs P * Q - P * Differential.mapCoeffs Q
      + Polynomial.C a * (P.derivative * Q - P * Q.derivative) = 0) :
    ∃ c : K, P = Polynomial.C (algebraMap K R c) * Q := by
  rcases lt_trichotomy Q.natDegree P.natDegree with hlt | heq | hgt
  · exact absurd (exists_deriv_of_relation_of_natDegree_lt hQ hlt hrel)
      (by rintro ⟨b, hb⟩; exact ha b hb)
  · -- equal degrees: kill the leading terms
    have hQl : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    have htop : (P.leadingCoeff)′ * Q.leadingCoeff - P.leadingCoeff * (Q.leadingCoeff)′ = 0 :=
      leadingCoeff_deriv_relation hrel hQ
    have hd : (P.leadingCoeff / Q.leadingCoeff)′ = 0 := by
      rw [map_div' (Differential.deriv : Derivation ℤ R R) _ _ hQl, htop]
      simp
    obtain ⟨c, hc⟩ := hconst _ hd
    have hlead : algebraMap K R c * Q.leadingCoeff = P.leadingCoeff := by
      have h1 : P.leadingCoeff = algebraMap K R c * Q.leadingCoeff := by
        rw [← hc, div_mul_cancel₀ _ hQl]
      exact h1.symm
    set P₁ : Polynomial R := P - Polynomial.C (algebraMap K R c) * Q with hP₁def
    have hmc : Differential.mapCoeffs (Polynomial.C (algebraMap K R c) * Q)
        = Polynomial.C (algebraMap K R c) * Differential.mapCoeffs Q := by
      rw [mapCoeffs_mul, Differential.mapCoeffs_C, hconst' c, map_zero, mul_zero, add_zero]
    have hmP : Differential.mapCoeffs P₁
        = Differential.mapCoeffs P
          - Polynomial.C (algebraMap K R c) * Differential.mapCoeffs Q := by
      rw [hP₁def, map_sub, hmc]
    have hdP : P₁.derivative = P.derivative - Polynomial.C (algebraMap K R c) * Q.derivative := by
      rw [hP₁def, Polynomial.derivative_sub, Polynomial.derivative_C_mul]
    have hrel₁ : Differential.mapCoeffs P₁ * Q - P₁ * Differential.mapCoeffs Q
        + Polynomial.C a * (P₁.derivative * Q - P₁ * Q.derivative) = 0 := by
      rw [hmP, hdP, hP₁def]
      linear_combination (norm := ring_nf) hrel
    by_cases hzero : P₁ = 0
    · refine ⟨c, ?_⟩
      rw [hP₁def] at hzero
      linear_combination (norm := ring_nf) hzero
    · -- the difference has lower degree: contradiction
      have hcoeff : ∀ k, Q.natDegree ≤ k → P₁.coeff k = 0 := by
        intro k hk
        rw [hP₁def, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
        rcases eq_or_lt_of_le hk with hk' | hk'
        · rw [← hk']
          have hp : P.coeff Q.natDegree = P.leadingCoeff := by rw [heq]; rfl
          rw [hp, Polynomial.coeff_natDegree, hlead]
          ring
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero, sub_zero]
      have hle : P₁.natDegree ≤ Q.natDegree := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        exact hcoeff N (le_of_lt hN)
      have hne : P₁.natDegree ≠ Q.natDegree := by
        intro h
        have h1 := hcoeff Q.natDegree le_rfl
        rw [← h, Polynomial.coeff_natDegree] at h1
        exact (Polynomial.leadingCoeff_ne_zero.mpr hzero) h1
      have hdeg : P₁.natDegree < Q.natDegree := by omega
      have hrel₁' : Differential.mapCoeffs Q * P₁ - Q * Differential.mapCoeffs P₁
          + Polynomial.C a * (Q.derivative * P₁ - Q * P₁.derivative) = 0 := by
        linear_combination (norm := ring_nf) -hrel₁
      exact absurd (exists_deriv_of_relation_of_natDegree_lt hzero hdeg hrel₁')
        (by rintro ⟨b, hb⟩; exact ha b hb)
  · -- `deg P < deg Q`: swap the roles
    by_cases hPz : P = 0
    · exact ⟨0, by rw [hPz, map_zero, Polynomial.C_0, zero_mul]⟩
    · have hrel' : Differential.mapCoeffs Q * P - Q * Differential.mapCoeffs P
          + Polynomial.C a * (Q.derivative * P - Q * P.derivative) = 0 := by
        linear_combination (norm := ring_nf) -hrel
      exact absurd (exists_deriv_of_relation_of_natDegree_lt hPz hgt hrel')
        (by rintro ⟨b, hb⟩; exact ha b hb)

end Submission.CDT
