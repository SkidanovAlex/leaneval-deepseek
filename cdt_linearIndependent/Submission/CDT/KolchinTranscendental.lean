import Mathlib
import Submission.CDT.KolchinAlgebraic
import Submission.Commons.RingTheory.Derivation.mapCoeffs_mul_sub_of_deriv_div
import Submission.Commons.FieldTheory.Transcendental.aeval_eq_zero_iff
import Submission.Commons.FieldTheory.Transcendental.aeval_injective

/-!
# Kolchin's lemma, transcendental case

Let `R ⊆ S` be fields of characteristic zero with derivations (compatible), and let `u ∈ S` be
*transcendental* over `R` with `u′ = a` for some `a ∈ R`.

The main result is `exists_add_mul_of_deriv_div_mem`: if `v = P(u)/Q(u)` is a rational function of
`u` over `R` whose derivative lies in `R`, then `v` is affine in `u`:
`v = r₀ + c·u` with `r₀ ∈ R` and `c ∈ R` a *constant* of `S`.

Equivalently (the form used in the induction proving the algebraic independence of logarithms):
the elements of `R(u)` whose derivative lies in `R` are exactly `R + C_S·u`.

The proof has two parts:
* the *polynomial* part (`exists_add_mul_of_deriv_polynomial_mem`), which is where the hypothesis
  that the constants of `S` lie in `R` is used: if `P` has degree `d ≥ 2`, comparing the
  coefficients of `X^d` and `X^(d-1)` in the identity `Φ(P) = C ρ` (`Φ` being the "total
  derivative" `mapCoeffs + C a·d/dX`) exhibits `u + P_{d-1}/(d·P_d)` as a new constant, and hence
  `u` itself as an element of `R` — contradicting transcendence;
* the *rational* part, which removes the denominator `Q`: from the polynomial identity
  `Φ(P)·Q - P·Φ(Q) = C ρ·Q²` one gets `Q ∣ Φ(Q)`, so `Φ(Q) = c·Q`; dividing `Q` by its leading
  coefficient makes `Φ` vanish, so `Q(u)` is a constant, whence `Q` itself is constant.
-/

open scoped Differential

noncomputable section

namespace Submission.CDT

open Polynomial

variable {R S : Type*} [Field R] [Differential R] [CharZero R] [Field S] [Algebra R S]
  [Differential S] [DifferentialAlgebra R S] [Differential.ContainConstants R S]

/-- The "total derivative along `u`": `Φ(Z) = mapCoeffs Z + C a * Z′`. -/
def Phi (a : R) (Z : Polynomial R) : Polynomial R :=
  Differential.mapCoeffs Z + Polynomial.C a * Z.derivative

/-- The chain rule, in terms of `Phi`. -/
lemma aeval_Phi {u : S} {a : R} (ha : Differential.deriv u = algebraMap R S a)
    (Z : Polynomial R) :
    Differential.deriv ((Polynomial.aeval u) Z) = (Polynomial.aeval u) (Phi a Z) := by
  rw [Differential.deriv_aeval_eq, ha, Phi, Polynomial.aeval_add, Polynomial.aeval_mul,
    Polynomial.aeval_C]
  ring

/-- If the derivative of `P(u)` is the image of `ρ`, then `Φ(P) = C ρ`. -/
lemma Phi_eq_C_of_deriv_eq {u : S} {a : R} (hu : Transcendental R u)
    (ha : Differential.deriv u = algebraMap R S a) {P : Polynomial R} {ρ : R}
    (hv : Differential.deriv ((Polynomial.aeval u) P) = algebraMap R S ρ) :
    Phi a P = Polynomial.C ρ := by
  have h := aeval_Phi ha P
  rw [hv] at h
  have h1 : (Polynomial.aeval u) (Phi a P - Polynomial.C ρ) = 0 := by
    rw [Polynomial.aeval_sub, Polynomial.aeval_C, ← h, sub_self]
  exact sub_eq_zero.mp
    ((Commons.FieldTheory.Transcendental.aeval_eq_zero_iff hu _).mp h1)

/-- A polynomial of degree at most one is the sum of its constant term and its linear term. -/
lemma eq_C_add_C_mul_X_of_natDegree_le_one {P : Polynomial R} (h : P.natDegree ≤ 1) :
    P = Polynomial.C (P.coeff 0) + Polynomial.C (P.coeff 1) * Polynomial.X := by
  ext n
  match n with
  | 0 => simp
  | 1 => simp
  | (k + 2) =>
      have h0 : P.coeff (k + 2) = 0 :=
        (Polynomial.natDegree_le_iff_coeff_eq_zero.mp h) _ (by omega)
      rw [h0, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
      simp

/-- **Kolchin's lemma, transcendental case, polynomial form.**  If `P(u)` has derivative in the
base field `R` and `u` is transcendental over `R` with `u′ = a ∈ R`, then `P(u)` is affine in `u`:
`P(u) = r₀ + c·u` with `c` a constant of `S`. -/
theorem exists_add_mul_of_deriv_polynomial_mem {u : S} {a : R} (hu : Transcendental R u)
    (ha : Differential.deriv u = algebraMap R S a) {P : Polynomial R} {ρ : R}
    (hv : Differential.deriv ((Polynomial.aeval u) P) = algebraMap R S ρ) :
    ∃ r₀ c : R, Differential.deriv (algebraMap R S c) = 0 ∧
      (Polynomial.aeval u) P = algebraMap R S r₀ + algebraMap R S c * u := by
  have hPhi : Phi a P = Polynomial.C ρ := Phi_eq_C_of_deriv_eq hu ha hv
  -- `u` is not in the image of `R`
  have hnotmem : u ∉ Set.range (algebraMap R S) := by
    rintro ⟨r, hr⟩
    have h := (transcendental_iff.mp hu) (Polynomial.X - Polynomial.C r) (by
      rw [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C, hr, sub_self])
    have h1 : (Polynomial.X - Polynomial.C r : Polynomial R).coeff 1 = 1 := by simp
    rw [h, Polynomial.coeff_zero] at h1
    exact zero_ne_one h1
  have hdeg_le_one : P.natDegree ≤ 1 := by
    by_contra hle
    rw [not_le] at hle
    have hd : 2 ≤ P.natDegree := hle
    have hlead : P.coeff P.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      intro h0
      have hP0 : P = 0 := Polynomial.leadingCoeff_eq_zero.mp h0
      rw [hP0] at hd
      simp only [natDegree_zero] at hd
      omega
    have hsub : P.natDegree - 1 + 1 = P.natDegree :=
      Nat.sub_add_cancel (show 1 ≤ P.natDegree by omega)
    have hcast : ((↑(P.natDegree - 1) + 1 : R)) = (P.natDegree : R) := by
      exact_mod_cast hsub
    -- the coefficient of `X^d`
    have hcoeff_top : (P.coeff P.natDegree)′ = 0 := by
      have h := congrArg (fun (Z : Polynomial R) => Z.coeff P.natDegree) hPhi
      simp only [Phi, Polynomial.coeff_add, Polynomial.coeff_C_mul,
        Differential.coeff_mapCoeffs, Polynomial.coeff_derivative] at h
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show P.natDegree < P.natDegree + 1 by omega),
        zero_mul, mul_zero, add_zero, Polynomial.coeff_C,
        if_neg (show P.natDegree ≠ 0 by omega)] at h
      exact h
    -- the coefficient of `X^(d-1)`
    have hcoeff_sub : (P.coeff (P.natDegree - 1))′
        = -(a * ((P.natDegree : R) * P.coeff P.natDegree)) := by
      have h := congrArg (fun (Z : Polynomial R) => Z.coeff (P.natDegree - 1)) hPhi
      simp only [Phi, Polynomial.coeff_add, Polynomial.coeff_C_mul,
        Differential.coeff_mapCoeffs, Polynomial.coeff_derivative] at h
      rw [hsub, hcast, Polynomial.coeff_C,
        if_neg (show P.natDegree - 1 ≠ 0 by omega)] at h
      rw [← add_eq_zero_iff_eq_neg]
      linear_combination (norm := ring_nf) h
    have hdR : (P.natDegree : R) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hden : (P.natDegree : R) * P.coeff P.natDegree ≠ 0 := mul_ne_zero hdR hlead
    -- the derivative of this denominator vanishes
    have hdR' : ((P.natDegree : R))′ = 0 :=
      Derivation.map_natCast (Differential.deriv : Derivation ℤ R R) P.natDegree
    have hdl : (((P.natDegree : R) * P.coeff P.natDegree))′ = 0 := by
      rw [Derivation.leibniz]
      simp only [hcoeff_top, hdR', smul_zero, add_zero]
    -- `u + P_{d-1}/(d·P_d)` is a constant
    have hb : (P.coeff (P.natDegree - 1) / ((P.natDegree : R) * P.coeff P.natDegree))′ = -a := by
      rw [map_div' (Differential.deriv : Derivation ℤ R R) _ _ hden, hcoeff_sub, hdl, mul_zero,
        sub_zero]
      field_simp
    have hconst : (u + algebraMap R S
        (P.coeff (P.natDegree - 1) / ((P.natDegree : R) * P.coeff P.natDegree)))′ = 0 := by
      rw [Derivation.map_add, ha, DifferentialAlgebra.deriv_algebraMap, hb, map_neg,
        add_neg_cancel]
    obtain ⟨r, hr⟩ :=
      Differential.ContainConstants.mem_range_of_deriv_eq_zero (A := R) hconst
    refine hnotmem ⟨r - P.coeff (P.natDegree - 1) / ((P.natDegree : R) * P.coeff P.natDegree),
      ?_⟩
    rw [map_sub, hr]
    ring
  -- now `P = C r₀ + C c * X` with `c` a constant
  refine ⟨P.coeff 0, P.coeff 1, ?_, ?_⟩
  · have h := congrArg (fun (Z : Polynomial R) => Z.coeff 1) hPhi
    simp only [Phi, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Differential.coeff_mapCoeffs, Polynomial.coeff_derivative] at h
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (show P.natDegree < 1 + 1 by omega),
      zero_mul, mul_zero, add_zero, Polynomial.coeff_C,
      if_neg (show (1 : ℕ) ≠ 0 by omega)] at h
    rw [DifferentialAlgebra.deriv_algebraMap, h]
    exact map_zero _
  · rw [eq_C_add_C_mul_X_of_natDegree_le_one hdeg_le_one, Polynomial.aeval_add, Polynomial.aeval_C,
      Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp

/-- `Phi` of a multiple of a constant polynomial. -/
lemma Phi_mul_C (a r : R) (Z : Polynomial R) :
    Phi a (Z * Polynomial.C r) = Phi a Z * Polynomial.C r + Z * Polynomial.C r′ := by
  have h1 : Differential.mapCoeffs (Z * Polynomial.C r)
      = Z * Polynomial.C r′ + Polynomial.C r * Differential.mapCoeffs Z := by
    rw [Derivation.leibniz, Differential.mapCoeffs_C, smul_eq_mul, smul_eq_mul, mul_comm]
  have h2 : Polynomial.derivative (Z * Polynomial.C r)
      = Polynomial.derivative Z * Polynomial.C r := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_C, mul_zero, add_zero]
  rw [Phi, h1, h2, Phi]
  ring

/-- **Kolchin's lemma, transcendental case.**  If `v = P(u)/Q(u)` is a rational function of a
transcendental element `u` over `R` whose derivative lies in `R`, then `v` is affine in `u`. -/
theorem exists_add_mul_of_deriv_div_mem {u : S} {a : R} (hu : Transcendental R u)
    (ha : Differential.deriv u = algebraMap R S a) {P Q : Polynomial R} (hQ : Q ≠ 0)
    (hcop : IsCoprime P Q) {ρ : R}
    (hv : Differential.deriv ((Polynomial.aeval u) P / (Polynomial.aeval u) Q) = algebraMap R S ρ) :
    ∃ r₀ c : R, Differential.deriv (algebraMap R S c) = 0 ∧
      (Polynomial.aeval u) P / (Polynomial.aeval u) Q = algebraMap R S r₀ + algebraMap R S c * u := by
  -- the polynomial identity of the quotient rule
  have hident : Phi a P * Q - P * Phi a Q = Polynomial.C ρ * (Q * Q) := by
    have h := Commons.RingTheory.Derivation.mapCoeffs_mul_sub_of_deriv_div hu ha hQ hv
    simp only [Phi]
    linear_combination (norm := ring_nf) h
  -- `Q` divides `Phi a Q`
  have hdvd : Q ∣ Phi a Q := by
    have h1 : Q ∣ P * Phi a Q := by
      refine ⟨Phi a P - Polynomial.C ρ * Q, ?_⟩
      have h : P * Phi a Q = Phi a P * Q - Polynomial.C ρ * (Q * Q) := by
        rw [eq_sub_iff_add_eq, ← hident]
        ring
      rw [h]
      ring
    exact (hcop.symm).dvd_of_dvd_mul_left h1
  obtain ⟨Sp, hSp⟩ := hdvd
  -- the degree of `Phi a Q` is at most that of `Q`
  have hdegPhi : (Phi a Q).natDegree ≤ Q.natDegree := by
    rw [Phi]
    refine le_trans (natDegree_add_le _ _) (max_le (natDegree_mapCoeffs_le Q) ?_)
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_derivative,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < N + 1), zero_mul,
      mul_zero]
  have hSdeg : Sp.natDegree = 0 := by
    by_cases hS0 : Sp = 0
    · rw [hS0, natDegree_zero]
    · have h := hdegPhi
      rw [hSp, Polynomial.natDegree_mul hQ hS0] at h
      omega
  obtain ⟨s, hs⟩ := Polynomial.natDegree_eq_zero.mp hSdeg
  have hmain : Phi a Q = Q * Polynomial.C s := by rw [hSp, hs]
  -- `s` is the logarithmic derivative of the leading coefficient
  have hlne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hs_eq : s = Q.leadingCoeff′ * (Q.leadingCoeff)⁻¹ := by
    have h := congrArg (fun (Z : Polynomial R) => Z.coeff Q.natDegree) hmain
    simp only [Phi, Polynomial.coeff_add, Polynomial.coeff_C_mul, Differential.coeff_mapCoeffs,
      Polynomial.coeff_derivative, Polynomial.coeff_mul_C] at h
    simp only [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < Q.natDegree + 1),
      zero_mul, mul_zero, add_zero, Polynomial.coeff_natDegree] at h
    rw [h]
    field_simp
  -- the derivative of `Q * C (leadingCoeff)⁻¹` vanishes
  have hinv : ((Q.leadingCoeff)⁻¹)′ = -(Q.leadingCoeff′ / Q.leadingCoeff ^ 2) := by
    rw [show (Q.leadingCoeff)⁻¹ = 1 / Q.leadingCoeff by rw [one_div],
      map_div' (Differential.deriv : Derivation ℤ R R) 1 Q.leadingCoeff hlne,
      show ((1 : R))′ = 0 from Derivation.map_one_eq_zero _]
    ring
  have hPhiQm : Phi a (Q * Polynomial.C (Q.leadingCoeff)⁻¹) = 0 := by
    have h1 : Q * Polynomial.C (Q.leadingCoeff′ * Q.leadingCoeff⁻¹)
          * Polynomial.C Q.leadingCoeff⁻¹
        = Q * Polynomial.C ((Q.leadingCoeff′ * Q.leadingCoeff⁻¹) * Q.leadingCoeff⁻¹) := by
      simp only [mul_assoc, ← Polynomial.C_mul]
    have h2 : -(Q.leadingCoeff′ / Q.leadingCoeff ^ 2)
        = -((Q.leadingCoeff′ * Q.leadingCoeff⁻¹) * Q.leadingCoeff⁻¹) := by
      field_simp
    rw [Phi_mul_C, hmain, hs_eq, hinv, h1, h2, ← mul_add, ← Polynomial.C_add, add_neg_cancel,
      Polynomial.C_0, mul_zero]
  -- hence `Q * C (leadingCoeff)⁻¹` is a constant polynomial
  have hQm : Q * Polynomial.C (Q.leadingCoeff)⁻¹
      = Polynomial.C (Q.coeff 0 * (Q.leadingCoeff)⁻¹) := by
    have hconst : Differential.deriv
        ((Polynomial.aeval u) (Q * Polynomial.C (Q.leadingCoeff)⁻¹)) = 0 := by
      rw [aeval_Phi ha, hPhiQm, map_zero]
    obtain ⟨r, hr⟩ :=
      Differential.ContainConstants.mem_range_of_deriv_eq_zero (A := R) hconst
    have hz : (Polynomial.aeval u) (Q * Polynomial.C (Q.leadingCoeff)⁻¹ - Polynomial.C r) = 0 := by
      rw [Polynomial.aeval_sub, Polynomial.aeval_C, hr, sub_self]
    have hthis : Q * Polynomial.C (Q.leadingCoeff)⁻¹ = Polynomial.C r :=
      sub_eq_zero.mp ((Commons.FieldTheory.Transcendental.aeval_eq_zero_iff hu _).mp hz)
    have hc := congrArg (fun (Z : Polynomial R) => Z.coeff 0) hthis
    rw [Polynomial.coeff_mul_C, Polynomial.coeff_C_zero] at hc
    rw [hthis, ← hc]
  have hQnat : Q.natDegree = 0 := by
    have h := congrArg Polynomial.natDegree hQm
    simp only [Polynomial.natDegree_mul hQ (Polynomial.C_ne_zero.mpr (inv_ne_zero hlne)),
      Polynomial.natDegree_C, add_zero] at h
    exact h
  -- so `Q` is a constant polynomial
  obtain ⟨q, hq⟩ := Polynomial.natDegree_eq_zero.mp hQnat
  have hqne : q ≠ 0 := by
    intro h0
    rw [h0, Polynomial.C_0] at hq
    exact hQ hq.symm
  -- reduce to the polynomial case
  have hP1 : (Polynomial.aeval u) P / (Polynomial.aeval u) Q
      = (Polynomial.aeval u) (P * Polynomial.C q⁻¹) := by
    simp only [← hq, Polynomial.aeval_mul, Polynomial.aeval_C, map_inv₀, div_eq_mul_inv]
  have hv' : Differential.deriv ((Polynomial.aeval u) (P * Polynomial.C q⁻¹))
      = algebraMap R S ρ := by
    rw [← hP1]
    exact hv
  obtain ⟨r₀, c, hc, heq⟩ := exists_add_mul_of_deriv_polynomial_mem hu ha hv'
  exact ⟨r₀, c, hc, by rw [hP1, heq]⟩

end Submission.CDT