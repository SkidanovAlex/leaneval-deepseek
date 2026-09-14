import Mathlib
import Submission.Vdw.CubicSign
import Submission.Vdw.IndexCountMain
import Submission.Vdw.CubeRadical
import Submission.Commons.NumberTheory.NumberField.discr_minpoly_eq_discr_mul_sq
import Submission.Commons.FieldTheory.Polynomial.discr_X_pow_add_mul_add
import Submission.Commons.NumberTheory.Chebyshev.prod_primes_dvd
import Submission.Commons.NumberTheory.Int.ncard_binary_quadratic_repr_le_bounded

open Polynomial Filter Asymptotics
open scoped BigOperators NumberField Classical
open vanDerWaerdenConjecture

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The elementary count of cyclic cubic fields: `FieldCountBound 3 (1/2 + ε)`

The Case-II region in degree `3` consists of irreducible cubics with
`|Gal| < 3! = 6`, i.e. Galois group `C₃`: the fields cut out are *cyclic cubic*
fields, and their number of discriminant `≤ Y` is `≍ √Y` (Cohn, via the
Hasse correspondence).  This module obtains the exponent `1/2 + ε` *without*
Kronecker–Weber, from the sign of the discriminant alone.

For a class `q` of the region with `D = classDisc q` and class polynomial
`P = X³ + bX + c` (the minimal polynomial of the trace-zero generator):

* `D` is squarefull and `v_p(D) = 2` for every prime `p > 3` (Lemma 24);
* hence (`coeff_eq_zero_of_polyIndex_ge_two`) `fl | b` and `fl | c`, where
  `fl = ∏_{p | D, p > 3} p = discJ 3 D 1`;
* `D = D_small · fl²` with `D_small = discSmallPart 3 D ≤ S₀` bounded;
* the sign theorem (`discr_Kpoly_pos`) makes the Dedekind index relation
  *definite*: `disc P = D · m²` with `D > 0`, so `b < 0`;
* writing `b = -fl B₁`, `c = fl γ`, the relation becomes the *definite binary
  quadratic form equation* `27 γ² + D_small m² = 4 fl B₁³`;
* `B₁ ≤ 8·2²⁴·√S₀` is bounded, and `fl` is recovered from `(B₁, γ, m)`, so
  the class is determined by `(fl, B₁, γ, m)`;
* the number of `(γ, m)` satisfying the equation is `≪_ε (fl B₁³)^ε`
  (`ncard_binary_quadratic_repr_le_bounded`), and summing over `fl ≤ √Y`
  gives `≪ Y^{1/2 + ε}`.

Axioms: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-! ## 1. The three-term shape of the class polynomial -/

/-- A monic polynomial of degree three with vanishing `X²`-coefficient is
`X³ + c₁X + c₀`. -/
theorem eq_three_term {R : Type*} [CommRing R] {P : R[X]} (hm : P.Monic)
    (hdeg : P.natDegree = 3) (h2 : P.coeff 2 = 0) :
    P = X ^ 3 + C (P.coeff 1) * X + C (P.coeff 0) := by
  ext k
  rcases k with _ | _ | _ | k
  · simp
  · simp
  · simp [h2]
  · rcases k with _ | k
    · have h1 : P.coeff 3 = 1 := by
        rw [← hdeg, Polynomial.coeff_natDegree, hm.leadingCoeff]
      rw [h1]
      simp
    · have h0 : P.coeff (k + 4) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
      rw [h0]
      simp

theorem classPoly_eq_three_term (H : ℕ) (hn : 1 ≤ 3) (hnn : 2 ≤ 3)
    (q : Quotient (fieldIsoSetoid 3 H hn)) :
    classPoly 3 H hn hnn q =
      X ^ 3 + C ((classPoly 3 H hn hnn q).coeff 1) * X
        + C ((classPoly 3 H hn hnn q).coeff 0) :=
  eq_three_term (classPoly_monic 3 H hn hnn q) (classPoly_natDegree 3 H hn hnn q)
    (classPoly_nextCoeff 3 H hn hnn q)

/-! ## 2. The Dedekind index relation for the class polynomial -/

/-- The `Bad` condition as a `Gal`-cardinality bound with the degree. -/
theorem gal_card_lt_factorial_of_mem_irreducibleBad {n H : ℕ} {f : ℤ[X]}
    (hf : f ∈ IrreducibleBad n H) :
    Nat.card (f.map φℚ).Gal < ((f.map φℚ).natDegree).factorial := by
  obtain ⟨hmonic, hdegree, -, hcard⟩ := hf.1
  have hnd : (f.map φℚ).natDegree = n := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero φℚ
      (by rw [hmonic.leadingCoeff]; simp)]
    exact Polynomial.natDegree_eq_of_degree_eq_some hdegree
  rw [hnd]
  exact hcard

/-- **Dedekind's index relation for the class polynomial, in degree three.**
The class polynomial `P` of a class of the Case-II region is the minimal
polynomial of an integral primitive element of the field, so
`disc P = discr K · m²`; because the discriminant is positive
(`discr_Kpoly_pos`), the absolute value `classDisc` may be used on the right. -/
theorem exists_discr_classPoly_eq_classDisc_mul_sq (H : ℕ)
    (hn : 1 ≤ 3) (hnn : 2 ≤ 3) (q : Quotient (fieldIsoSetoid 3 H hn)) :
    ∃ m : ℤ, Polynomial.discr (classPoly 3 H hn hnn q) =
      (classDisc 3 H hn q : ℤ) * m ^ 2 := by
  classical
  obtain ⟨hPmonic, hPdeg, hPnext, hPbdd, hwit⟩ := classPoly_spec 3 H hn hnn q
  obtain ⟨y, hygen, hymin⟩ := hwit
  haveI hIrr0 : Fact (Irreducible (((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X]).map φℚ)) :=
    ⟨subcaseI_P2_irreducible 3 H hn (Quotient.out q)⟩
  haveI hIrrP : Fact (Irreducible ((classPoly 3 H hn hnn q).map φℚ)) := by
    have hyintq : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
    rw [← hymin]
    exact ⟨minpoly.irreducible hyintq⟩
  have hyint : IsIntegral ℤ y := by
    refine ⟨classPoly 3 H hn hnn q, hPmonic, ?_⟩
    have h1 : (Polynomial.aeval y) (minpoly ℚ y) = 0 := minpoly.aeval ℚ y
    have h2 : minpoly ℚ y = (classPoly 3 H hn hnn q).map φℚ := hymin
    rw [h2] at h1
    have h3 : (Polynomial.aeval y)
        ((classPoly 3 H hn hnn q).map (algebraMap ℤ ℚ)) = 0 := by
      simpa only [φℚ] using h1
    rw [Polynomial.aeval_map_algebraMap (A := ℚ) y (classPoly 3 H hn hnn q)] at h3
    exact h3
  set θ : 𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X])) :=
    IsIntegralClosure.mk' (R := ℤ)
      (𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X]))) y hyint
    with hθ
  have hθy : ((θ : 𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X]))) :
      Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X])) = y :=
    IsIntegralClosure.algebraMap_mk' _ y hyint
  have hminθ : minpoly ℤ θ = classPoly 3 H hn hnn q := by
    have h1 : minpoly ℤ y = classPoly 3 H hn hnn q := by
      have h2 := minpoly.isIntegrallyClosed_eq_field_fractions ℚ
        (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X])) hyint
      have h2' : minpoly ℚ y =
          Polynomial.map φℚ (minpoly ℤ y) := by
        simpa only [Algebra.algebraMap_self_apply, φℚ] using h2
      have h4 : Polynomial.map φℚ (minpoly ℤ y) = Polynomial.map φℚ (classPoly 3 H hn hnn q) :=
        h2'.symm.trans hymin
      exact (Polynomial.map_injective φℚ (fun a b h => by simpa [φℚ] using h) h4.symm).symm
    rw [← h1]
    have h3 := minpoly.algebraMap_eq
      (B := 𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X])))
      (B' := Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X]))
      (A := ℤ) (IsIntegralClosure.algebraMap_injective
        (𝓞 (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X]))) ℤ
        (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X]))) θ
    exact h3.symm.trans (congrArg (minpoly ℤ) hθy)
  have hbox : (((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X])) ∈ Box 3 H :=
    subcaseI_P2_subset_Box 3 H (Quotient.out q).2
  have hfin : Module.finrank ℚ (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X])) = 3 :=
    finrank_Kpoly hbox.1 (Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1)
  have hdegθ : (minpoly ℤ θ).natDegree =
      Module.finrank ℚ (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X])) := by
    rw [hminθ, hPdeg, hfin]
  obtain ⟨m, hm⟩ := Commons.NumberTheory.NumberField.discr_minpoly_eq_discr_mul_sq θ hdegθ
  have hpos : 0 < NumberField.discr (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X])) :=
    discr_Kpoly_pos _ hbox.1 (Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1)
      (by
        have hthis := gal_card_lt_factorial_of_mem_irreducibleBad
          (n := 3) (H := H) (Quotient.out q).2.1.1
        have hnd : (((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X]).map φℚ).natDegree = 3 := by
          rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero φℚ
            (by rw [hbox.1.leadingCoeff]; simp)]
          exact Polynomial.natDegree_eq_of_degree_eq_some hbox.2.1
        rw [hnd] at hthis
        rw [show Nat.factorial 3 = 6 from by decide] at hthis
        exact hthis)
  have hcd : (classDisc 3 H hn q : ℤ) =
      NumberField.discr (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X])) := by
    rw [classDisc_out 3 H hn q]
    show ((subcaseI_P2_disc 3 H (Quotient.out q) : ℕ) : ℤ) = _
    have h1 : subcaseI_P2_disc 3 H (Quotient.out q) =
        (NumberField.discr (Kpoly ((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X]))).natAbs := rfl
    rw [h1]
    exact Int.natAbs_of_nonneg hpos.le
  exact ⟨m, by rw [← hminθ, hm, hcd]⟩

/-! ## 3. The large-prime part divides both coefficients -/

/-- If a prime `p > 3` divides the class discriminant `D`, then `v_p(D) = 2`
(squarefullness and Lemma 24). -/
theorem factorization_classDisc_eq_two (H : ℕ) (hn : 1 ≤ 3) (hnn : 2 ≤ 3)
    (q : Quotient (fieldIsoSetoid 3 H hn)) {p : ℕ} (hp : Nat.Prime p) (hpn : 3 < p)
    (hpd : p ∣ classDisc 3 H hn q) :
    (classDisc 3 H hn q).factorization p = 2 := by
  have hne : classDisc 3 H hn q ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (one_le_classDisc 3 H hn q)
  have hle := factorization_classDisc_le 3 H hn hnn q hp hpn hpd
  have hsq : p ^ 2 ∣ classDisc 3 H hn q :=
    squarefull_classDisc 3 H hn hnn q p hp hpd
  have h2 : 2 ≤ (classDisc 3 H hn q).factorization p :=
    (hp.pow_dvd_iff_le_factorization hne).mp hsq
  omega

/-- **The large-prime part of the discriminant divides both coefficients** of
the class polynomial.  A prime `p > 3` dividing `D` has `v_p(D) = 2`, so
`polyIndexMod p P ≥ 2`, and a cubic of index `≥ 2` reduces to `X³`. -/
theorem discJ_dvd_classPoly_coeff (H : ℕ) (hn : 1 ≤ 3) (hnn : 2 ≤ 3)
    (q : Quotient (fieldIsoSetoid 3 H hn)) :
    ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ) ∣ (classPoly 3 H hn hnn q).coeff 1 ∧
      ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ) ∣ (classPoly 3 H hn hnn q).coeff 0 := by
  classical
  set D : ℕ := classDisc 3 H hn q with hD
  set P : ℤ[X] := classPoly 3 H hn hnn q with hPdef
  have hDP : D = classDisc 3 H hn q := hD
  have hP : P ∈ GoodPoly 3 D := by
    rw [hPdef, hD]; exact classPoly_mem_goodPoly 3 H hn hnn q
  have hone : 1 ≤ D := by rw [hD]; exact one_le_classDisc 3 H hn q
  have hshape : P = X ^ 3 + C (P.coeff 1) * X + C (P.coeff 0) := by
    rw [hPdef]
    exact classPoly_eq_three_term H hn hnn q
  have hkey : ∀ p ∈ discJPrimes 3 D 1, p ∣ (P.coeff 1).natAbs ∧ p ∣ (P.coeff 0).natAbs := by
    intro p hp
    have hpprime : Nat.Prime p := prime_of_mem_discJPrimes hp
    have hp3 : 3 < p := (Finset.mem_filter.mp hp).2.1
    have hpdvd : p ∣ D :=
      Nat.dvd_of_mem_primeFactors (discJPrimes_subset_primeFactors 3 D 1 hp)
    haveI : Fact (Nat.Prime p) := ⟨hpprime⟩
    have hv : padicValNat p D ≤ polyIndexMod p hpprime P := hP.2.2.2.2 p hpprime hp3 hpdvd
    have hfac : D.factorization p = 2 := by
      rw [hD]
      exact factorization_classDisc_eq_two H hn hnn q hpprime hp3 (by rw [← hD]; exact hpdvd)
    have hval : padicValNat p D = 2 := by
      rw [← Nat.factorization_def D hpprime, hfac]
    have hidx : 2 ≤ polyIndex (X ^ 3 + C ((P.coeff 1 : ZMod p)) * X + C ((P.coeff 0 : ZMod p))) := by
      have h2 : polyIndexMod p hpprime P =
          polyIndex (P.map (Int.castRingHom (ZMod p))) := rfl
      rw [h2, hval] at hv
      have hmap : P.map (Int.castRingHom (ZMod p)) =
          X ^ 3 + C ((P.coeff 1 : ZMod p)) * X + C ((P.coeff 0 : ZMod p)) := by
        conv_lhs => rw [hshape]
        simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
          Polynomial.map_C]
        norm_num
      rwa [hmap] at hv
    obtain ⟨h1, h0⟩ := coeff_eq_zero_of_polyIndex_ge_two p hp3
      ((P.coeff 1 : ZMod p)) ((P.coeff 0 : ZMod p)) hidx
    have hz1 : (p : ℤ) ∣ P.coeff 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (P.coeff 1) p).mp h1
    have hz0 : (p : ℤ) ∣ P.coeff 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (P.coeff 0) p).mp h0
    exact ⟨(Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := P.coeff 1)).mpr (by simpa using hz1),
      (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := P.coeff 0)).mpr (by simpa using hz0)⟩
  have hprod1 : discJ 3 D 1 ∣ (P.coeff 1).natAbs := by
    rw [discJ_eq_prod]
    exact Commons.NumberTheory.Chebyshev.prod_primes_dvd
      (fun p hp => prime_of_mem_discJPrimes hp) (fun p hp => (hkey p hp).1)
  have hprod0 : discJ 3 D 1 ∣ (P.coeff 0).natAbs := by
    rw [discJ_eq_prod]
    exact Commons.NumberTheory.Chebyshev.prod_primes_dvd
      (fun p hp => prime_of_mem_discJPrimes hp) (fun p hp => (hkey p hp).2)
  refine ⟨?_, ?_⟩
  · exact (Int.natAbs_dvd_natAbs (a := ((discJ 3 D 1 : ℕ) : ℤ))
      (b := P.coeff 1)).mp (by simpa using hprod1)
  · exact (Int.natAbs_dvd_natAbs (a := ((discJ 3 D 1 : ℕ) : ℤ))
      (b := P.coeff 0)).mp (by simpa using hprod0)

/-! ## 4. The class data: large-prime part, coefficients and bounds -/

/-- The constant bound on the `2,3`-part of a class discriminant in degree three. -/
noncomputable def cubicS : ℕ := primorial 3 ^ (3 + 3 * Nat.log 2 3)

/-- The constant bound on the normalised coefficient `B₁ = -b/fl`. -/
noncomputable def cubicK0 : ℕ := ⌈8 * 2 ^ 24 * Real.sqrt (cubicS : ℝ)⌉₊ + 1

/-- The large-prime part of a class discriminant is a perfect square. -/
theorem discLargePart_classDisc_eq_discJ_sq (H : ℕ) (hn : 1 ≤ 3) (hnn : 2 ≤ 3)
    (q : Quotient (fieldIsoSetoid 3 H hn)) :
    discLargePart 3 (classDisc 3 H hn q) = (discJ 3 (classDisc 3 H hn q) 1) ^ 2 := by
  classical
  set D : ℕ := classDisc 3 H hn q with hD
  have hne : D ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_classDisc 3 H hn q)
  have hfilter : (Nat.primeFactors D).filter (fun p => 3 < p) = discJPrimes 3 D 1 := by
    ext p
    simp only [discJPrimes, Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hpd, hDne⟩, h3p⟩
      exact ⟨⟨hp, hpd, hDne⟩, h3p, (hp.dvd_iff_one_le_factorization hDne).mp hpd⟩
    · rintro ⟨⟨hp, hpd, hDne⟩, h3p, -⟩
      exact ⟨⟨hp, hpd, hDne⟩, h3p⟩
  have hfac : ∀ p ∈ discJPrimes 3 D 1, D.factorization p = 2 := by
    intro p hp
    have hpp : Nat.Prime p := prime_of_mem_discJPrimes hp
    have h3p : 3 < p := (Finset.mem_filter.mp hp).2.1
    have hpd : p ∣ D :=
      Nat.dvd_of_mem_primeFactors (discJPrimes_subset_primeFactors 3 D 1 hp)
    rw [hD] at hpd ⊢
    exact factorization_classDisc_eq_two H hn hnn q hpp h3p (by rwa [← hD] at hpd)
  unfold discLargePart discJ
  rw [hfilter]
  rw [Finset.prod_congr rfl (fun p hp => by rw [hfac p hp])]
  rw [← Finset.prod_pow]

/-- The coefficient bound `cBnd 3 D 1` in closed form. -/
theorem cBnd_three_one (D : ℕ) : cBnd 3 D 1 = 8 * 2 ^ 24 * Real.sqrt D := by
  unfold cBnd
  norm_num
  rw [Real.sqrt_eq_rpow]
  have hnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have h1 : ((D : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = (D : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
    norm_num
  rw [mul_pow, h1]
  norm_num
  ring

/-- The solution set of a definite binary quadratic equation is finite. -/
theorem finite_binary_quadratic_solutions (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (n : ℕ) :
    ({p : ℤ × ℤ | (a : ℤ) * p.1 ^ 2 + (b : ℤ) * p.2 ^ 2 = (n : ℤ)}).Finite := by
  refine Set.Finite.subset (Set.Finite.prod (Set.finite_Icc (-(n : ℤ)) n)
    (Set.finite_Icc (-(n : ℤ)) n)) ?_
  rintro ⟨x, y⟩ hxy
  simp only [Set.mem_ofPred_eq] at hxy
  refine ⟨?_, ?_⟩
  · have h1 : (a : ℤ) * x ^ 2 ≤ (n : ℤ) := by
      have h2 : 0 ≤ (b : ℤ) * y ^ 2 := by positivity
      linarith [hxy]
    have h3 : x ^ 2 ≤ (a : ℤ) * x ^ 2 := by
      have : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
      nlinarith [sq_nonneg x]
    have h4 : x ^ 2 ≤ (n : ℤ) := le_trans h3 h1
    simp only [Set.mem_Icc]
    constructor <;> nlinarith [sq_nonneg x, sq_abs x, abs_nonneg x]
  · have h1 : (b : ℤ) * y ^ 2 ≤ (n : ℤ) := by
      have h2 : 0 ≤ (a : ℤ) * x ^ 2 := by positivity
      linarith [hxy]
    have h3 : y ^ 2 ≤ (b : ℤ) * y ^ 2 := by
      have : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
      nlinarith [sq_nonneg y]
    have h4 : y ^ 2 ≤ (n : ℤ) := le_trans h3 h1
    simp only [Set.mem_Icc]
    constructor <;> nlinarith [sq_nonneg y, sq_abs y, abs_nonneg y]

/-- The large-prime part of a class discriminant is at most its square root. -/
theorem discJ_le_sqrt_classDisc (H : ℕ) (hn : 1 ≤ 3) (hnn : 2 ≤ 3)
    (q : Quotient (fieldIsoSetoid 3 H hn)) :
    discJ 3 (classDisc 3 H hn q) 1 ≤ Nat.sqrt (classDisc 3 H hn q) + 1 := by
  have hDne : classDisc 3 H hn q ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (one_le_classDisc 3 H hn q)
  have hsq : (discJ 3 (classDisc 3 H hn q) 1) ^ 2 = discLargePart 3 (classDisc 3 H hn q) :=
    (discLargePart_classDisc_eq_discJ_sq H hn hnn q).symm
  have hle : discLargePart 3 (classDisc 3 H hn q) ≤ classDisc 3 H hn q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hDne) (discLargePart_dvd 3 _ hDne)
  have h2 : (discJ 3 (classDisc 3 H hn q) 1) ^ 2 ≤ classDisc 3 H hn q := by
    rw [hsq]; exact hle
  have := Nat.le_sqrt'.mpr h2
  omega


/-! ## 5. The data attached to a class -/

/-- **The normalised data of a class of the Case-II region in degree three.**
Writing `P = X³ + bX + c` for the class polynomial and `fl` for the large-prime
part of the discriminant, positivity of the discriminant forces `b < 0`; with
`b = -fl·B₁`, `c = fl·γ` and `D = d·fl²`, the Dedekind relation becomes the
definite binary quadratic equation `27γ² + d·m² = 4·fl·B₁³`, with all
quantities bounded. -/
theorem exists_cubic_data (H : ℕ) (hn : 1 ≤ 3) (hnn : 2 ≤ 3)
    (q : Quotient (fieldIsoSetoid 3 H hn)) :
    ∃ t : ℕ × ℕ × ℤ × ℕ × ℤ,
      1 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ cubicK0 ∧ 1 ≤ t.2.2.2.1 ∧ t.2.2.2.1 ≤ cubicS ∧
      (classPoly 3 H hn hnn q).coeff 1 = -((t.1 : ℕ) : ℤ) * ((t.2.1 : ℕ) : ℤ) ∧
      (classPoly 3 H hn hnn q).coeff 0 = ((t.1 : ℕ) : ℤ) * t.2.2.1 ∧
      27 * t.2.2.1 ^ 2 + ((t.2.2.2.1 : ℕ) : ℤ) * t.2.2.2.2 ^ 2
        = 4 * ((t.1 : ℕ) : ℤ) * ((t.2.1 : ℕ) : ℤ) ^ 3 ∧
      t.1 ≤ Nat.sqrt (classDisc 3 H hn q) + 1 := by
  classical
  obtain ⟨hPmonic, hPdeg, hPnext, hPbdd, hwit⟩ := classPoly_spec 3 H hn hnn q
  obtain ⟨y, hygen, hymin⟩ := hwit
  haveI hIrr0 : Fact (Irreducible (((Quotient.out q : ↥(SubcaseI_P2 3 H)) : ℤ[X]).map φℚ)) :=
    ⟨subcaseI_P2_irreducible 3 H hn (Quotient.out q)⟩
  haveI hIrrP : Fact (Irreducible ((classPoly 3 H hn hnn q).map φℚ)) := by
    have hyintq : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
    rw [← hymin]
    exact ⟨minpoly.irreducible hyintq⟩
  have hPirrQ : Irreducible ((classPoly 3 H hn hnn q).map φℚ) := hIrrP.out
  -- notation
  set b0 : ℤ := (classPoly 3 H hn hnn q).coeff 1 with hb0
  set c0 : ℤ := (classPoly 3 H hn hnn q).coeff 0 with hc0
  have hshape : classPoly 3 H hn hnn q = X ^ 3 + C b0 * X + C c0 := by
    rw [hb0, hc0]
    exact classPoly_eq_three_term H hn hnn q
  -- the discriminant of the class polynomial
  have hdisc : (classPoly 3 H hn hnn q).discr = -4 * b0 ^ 3 - 27 * c0 ^ 2 := by
    have h1 : ((classPoly 3 H hn hnn q).map φℚ).discr
        = (((classPoly 3 H hn hnn q).discr : ℤ) : ℚ) :=
      Commons.Polynomial.discr_map_of_monic φℚ hPmonic
    have hsh : (classPoly 3 H hn hnn q).map φℚ = X ^ 3 + C ((b0 : ℚ)) * X + C ((c0 : ℚ)) := by
      rw [hshape]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C]
      norm_num
    have h2 : ((classPoly 3 H hn hnn q).map φℚ).discr
        = -4 * (b0 : ℚ) ^ 3 - 27 * (c0 : ℚ) ^ 2 := by
      rw [hsh, Commons.FieldTheory.Polynomial.discr_X_pow_add_mul_add (F := ℚ) 3 (by norm_num)]
      norm_num
      ring
    have h3 : (((classPoly 3 H hn hnn q).discr : ℤ) : ℚ)
        = ((-4 * b0 ^ 3 - 27 * c0 ^ 2 : ℤ) : ℚ) := by
      rw [← h1, h2]; push_cast; ring
    exact_mod_cast h3
  obtain ⟨m, hm⟩ := exists_discr_classPoly_eq_classDisc_mul_sq H hn hnn q
  have heq : -4 * b0 ^ 3 - 27 * c0 ^ 2 = ((classDisc 3 H hn q : ℕ) : ℤ) * m ^ 2 := by
    rw [← hdisc]; exact hm
  have hDpos : (0 : ℤ) ≤ ((classDisc 3 H hn q : ℕ) : ℤ) := Nat.cast_nonneg _
  -- `b0 ≠ 0`
  have hb0ne : b0 ≠ 0 := by
    intro hbzero
    have hc0zero : c0 = 0 := by
      have h2 : -27 * c0 ^ 2 = ((classDisc 3 H hn q : ℕ) : ℤ) * m ^ 2 := by
        have := heq; rw [hbzero] at this; ring_nf at this ⊢; linarith [this]
      have h3 : (0 : ℤ) ≤ ((classDisc 3 H hn q : ℕ) : ℤ) * m ^ 2 :=
        mul_nonneg hDpos (sq_nonneg m)
      nlinarith [sq_nonneg c0, h2, h3]
    have hPX : classPoly 3 H hn hnn q = X ^ 3 := by
      rw [hshape, hbzero, hc0zero]
      simp
    have hIrrX : Irreducible (X ^ 3 : ℚ[X]) := by
      have h := hPirrQ
      rw [hPX] at h
      simpa using h
    have hirrX : Irreducible (X : ℚ[X]) := Polynomial.irreducible_X
    have hfac : (X ^ 3 : ℚ[X]) = X * X ^ 2 := by ring
    rcases hIrrX.isUnit_or_isUnit hfac with hu | hu
    · exact hirrX.not_isUnit hu
    · have hu2 : IsUnit ((X : ℚ[X]) * X) := by simpa [pow_two] using hu
      exact hirrX.not_isUnit (IsUnit.mul_iff.mp hu2).1
  -- `b0 < 0`
  have hb0neg : b0 < 0 := by
    have hm0 : (0 : ℤ) ≤ ((classDisc 3 H hn q : ℕ) : ℤ) * m ^ 2 :=
      mul_nonneg hDpos (sq_nonneg m)
    have hb3 : b0 ^ 3 ≤ 0 := by nlinarith [heq, sq_nonneg c0, hm0]
    rcases lt_trichotomy b0 0 with h | h | h
    · exact h
    · exact absurd h hb0ne
    · exfalso
      have hb2 : (0 : ℤ) < b0 ^ 2 := pow_pos h 2
      have hb3' : (0 : ℤ) < b0 ^ 3 := by
        have : b0 ^ 3 = b0 * b0 ^ 2 := by ring
        rw [this]; exact mul_pos h hb2
      linarith [hb3, hb3'.le]
  -- `c0 / fl` and `-b0 / fl`
  have hfl1 : 1 ≤ discJ 3 (classDisc 3 H hn q) 1 := by
    rcases Nat.eq_zero_or_pos (discJ 3 (classDisc 3 H hn q) 1) with h | h
    · exfalso
      have hdvd := discJ_dvd_discLargePart 3 (classDisc 3 H hn q) 1
      rw [h] at hdvd
      exact absurd (zero_dvd_iff.mp hdvd) (Nat.pos_iff_ne_zero.mp (discLargePart_pos 3 _))
    · exact h
  have hflpos : (0 : ℤ) < ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ) := by exact_mod_cast hfl1
  have hdvdb : ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ) ∣ b0 := by
    rw [hb0]; exact (discJ_dvd_classPoly_coeff H hn hnn q).1
  have hdvdc : ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ) ∣ c0 := by
    rw [hc0]; exact (discJ_dvd_classPoly_coeff H hn hnn q).2
  obtain ⟨k, hk⟩ := hdvdb
  obtain ⟨γ, hγ⟩ := hdvdc
  have hkneg : k < 0 := by nlinarith [hk, hb0neg, hflpos]
  set B₁ : ℕ := (-k).toNat with hB₁def
  have hB₁cast : (B₁ : ℤ) = -k := by
    rw [hB₁def]; exact Int.toNat_of_nonneg (by linarith)
  have hB₁pos : 1 ≤ B₁ := by
    have : (0 : ℤ) < (B₁ : ℤ) := by rw [hB₁cast]; linarith
    exact_mod_cast this
  have hb_eq : b0 = -((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ) * (B₁ : ℤ) := by
    rw [hk, hB₁cast]; ring
  -- the small part and the splitting of `D`
  set d : ℕ := discSmallPart 3 (classDisc 3 H hn q) with hddef
  have hDne : classDisc 3 H hn q ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (one_le_classDisc 3 H hn q)
  have hdvd : d ∣ classDisc 3 H hn q := by rw [hddef]; exact discSmallPart_dvd 3 _ hDne
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exfalso; rw [h] at hdvd
      exact absurd (zero_dvd_iff.mp hdvd) hDne
    · exact h
  have hdle : d ≤ cubicS := by
    rw [hddef, cubicS]
    exact discSmallPart_classDisc_le 3 H hn hnn q
  have hDsplit : classDisc 3 H hn q = d * (discJ 3 (classDisc 3 H hn q) 1) ^ 2 := by
    have h1 := (discSplit 3 (classDisc 3 H hn q) hDne).symm
    rw [discLargePart_classDisc_eq_discJ_sq H hn hnn q] at h1
    conv_lhs => rw [h1]
    rw [hddef]
    ring
  -- the definite quadratic equation
  have hfinal : 27 * γ ^ 2 + ((d : ℕ) : ℤ) * m ^ 2
      = 4 * ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ) * (B₁ : ℤ) ^ 3 := by
    have hfl2 : (0 : ℤ) < ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ) := hflpos
    have hDcast : ((classDisc 3 H hn q : ℕ) : ℤ)
        = ((d : ℕ) : ℤ) * (((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ)) ^ 2 := by
      conv_lhs => rw [hDsplit]
      push_cast; ring
    have h := heq
    rw [hb_eq, hγ, hDcast] at h
    have h2 : (((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ)) ^ 2 *
        (27 * γ ^ 2 + ((d : ℕ) : ℤ) * m ^ 2
          - 4 * ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ) * (B₁ : ℤ) ^ 3) = 0 := by
      linear_combination (-1 : ℤ) * h
    have h3 : (((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℤ)) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (ne_of_gt hfl2)
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left h3)
  -- the bound on `B₁`
  have hb_bdd : |((b0 : ℤ) : ℝ)| ≤ cBnd 3 (classDisc 3 H hn q) 1 := by
    have h := hPbdd 1 (by norm_num) (by norm_num)
    rw [hb0]
    simp only [cBnd, classDisc_out]
    exact h
  rw [cBnd_three_one] at hb_bdd
  have hbabs : (B₁ : ℝ) * ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℝ)
      = |((b0 : ℤ) : ℝ)| := by
    rw [hb_eq]
    rw [show ((-(↑(discJ 3 (classDisc 3 H hn q) 1) : ℤ) * ↑B₁ : ℤ) : ℝ)
        = -((discJ 3 (classDisc 3 H hn q) 1 : ℝ) * (B₁ : ℝ)) by push_cast; ring]
    rw [abs_neg, abs_of_nonneg (by positivity)]
    ring
  have hsqrtD : Real.sqrt (classDisc 3 H hn q : ℝ)
      = Real.sqrt (d : ℝ) * ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℝ) := by
    have harg : (classDisc 3 H hn q : ℝ)
        = (d : ℝ) * ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℝ) ^ 2 := by
      conv_lhs => rw [hDsplit]
      push_cast; ring
    rw [harg, Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg _)]
  have hB₁bound : (B₁ : ℝ) ≤ 8 * 2 ^ 24 * Real.sqrt (d : ℝ) := by
    have hflposR : (0 : ℝ) < ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℝ) := by
      exact_mod_cast hfl1
    have hmain : (B₁ : ℝ) * ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℝ)
        ≤ (8 * 2 ^ 24 * Real.sqrt (d : ℝ))
          * ((discJ 3 (classDisc 3 H hn q) 1 : ℕ) : ℝ) := by
      have hb := hb_bdd
      rw [← hbabs] at hb
      rw [hsqrtD] at hb
      linarith [hb]
    exact le_of_mul_le_mul_right hmain hflposR
  have hB₁le : B₁ ≤ cubicK0 := by
    have h1 : (B₁ : ℝ) ≤ 8 * 2 ^ 24 * Real.sqrt (cubicS : ℝ) := by
      refine le_trans hB₁bound ?_
      have : Real.sqrt (d : ℝ) ≤ Real.sqrt (cubicS : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hdle)
      nlinarith
    have h2 : (B₁ : ℝ) ≤ (⌈8 * 2 ^ 24 * Real.sqrt (cubicS : ℝ)⌉₊ : ℝ) :=
      le_trans h1 (Nat.le_ceil _)
    have h3 : B₁ ≤ ⌈8 * 2 ^ 24 * Real.sqrt (cubicS : ℝ)⌉₊ := by exact_mod_cast h2
    rw [cubicK0]; omega
  exact ⟨(discJ 3 (classDisc 3 H hn q) 1, B₁, γ, d, m),
    hfl1, hB₁pos, hB₁le, hd1, hdle, by simpa using hb_eq, by simpa using hγ,
    by simpa using hfinal, discJ_le_sqrt_classDisc H hn hnn q⟩

/-! ## 6. The field count -/

theorem one_le_cubicS : 1 ≤ cubicS := by
  rw [cubicS]
  refine Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ ?_)
  rw [primorial]
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => (Finset.mem_filter.mp hp).2.ne_zero)

/-- **The elementary count of cyclic cubic fields**: the number of
field-isomorphism classes of the Case-II region in degree three with
discriminant `≤ Y` is `≪ Y^{1/2 + 1/20}`. -/
theorem fieldCountBound_three_cyclic :
    FieldCountBound 3 (by omega : 1 ≤ 3) (1 / 2 + 1 / 20) := by
  classical
  have hεpos : (0 : ℝ) < 1 / 10 := by norm_num
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.Int.ncard_binary_quadratic_repr_le_bounded 27 (by norm_num) cubicS
      one_le_cubicS (1 / 10) hεpos
  refine ⟨2 * (cubicK0 : ℝ) * (cubicS : ℝ) * (C * (8 * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ)) + 1,
    by positivity, ?_⟩
  intro H Y hY
  have hn1 : 1 ≤ 3 := by norm_num
  have hnn : 2 ≤ 3 := by norm_num
  haveI hFp : Fintype ↥(SubcaseI_P2 3 H) :=
    ((box_finite 3 H).subset (subcaseI_P2_subset_Box 3 H)).fintype
  haveI hFq : Fintype (Quotient (fieldIsoSetoid 3 H hn1)) := Quotient.fintype _
  -- the tag
  let tag : {q : Quotient (fieldIsoSetoid 3 H hn1) // classDisc 3 H hn1 q ≤ Y}
      → ℕ × ℕ × ℤ × ℕ × ℤ :=
    fun q => Classical.choose (exists_cubic_data H hn1 hnn q.1)
  have htag : ∀ q : {q : Quotient (fieldIsoSetoid 3 H hn1) // classDisc 3 H hn1 q ≤ Y},
      1 ≤ (tag q).1 ∧ 1 ≤ (tag q).2.1 ∧ (tag q).2.1 ≤ cubicK0 ∧
      1 ≤ (tag q).2.2.2.1 ∧ (tag q).2.2.2.1 ≤ cubicS ∧
      (classPoly 3 H hn1 hnn q.1).coeff 1 = -(((tag q).1 : ℕ) : ℤ) * (((tag q).2.1 : ℕ) : ℤ) ∧
      (classPoly 3 H hn1 hnn q.1).coeff 0 = (((tag q).1 : ℕ) : ℤ) * (tag q).2.2.1 ∧
      27 * (tag q).2.2.1 ^ 2 + (((tag q).2.2.2.1 : ℕ) : ℤ) * (tag q).2.2.2.2 ^ 2
        = 4 * (((tag q).1 : ℕ) : ℤ) * (((tag q).2.1 : ℕ) : ℤ) ^ 3 ∧
      (tag q).1 ≤ Nat.sqrt (classDisc 3 H hn1 q.1) + 1 :=
    fun q => Classical.choose_spec (exists_cubic_data H hn1 hnn q.1)
  -- injectivity
  have hinj : Function.Injective tag := by
    intro q1 q2 h
    have h1 := htag q1
    have h2 := htag q2
    have hfl : (tag q1).1 = (tag q2).1 := by rw [h]
    have hB : (tag q1).2.1 = (tag q2).2.1 := by rw [h]
    have hγ : (tag q1).2.2.1 = (tag q2).2.2.1 := by rw [h]
    have hb : (classPoly 3 H hn1 hnn q1.1).coeff 1 = (classPoly 3 H hn1 hnn q2.1).coeff 1 := by
      rw [h1.2.2.2.2.2.1, h2.2.2.2.2.2.1, hfl, hB]
    have hc : (classPoly 3 H hn1 hnn q1.1).coeff 0 = (classPoly 3 H hn1 hnn q2.1).coeff 0 := by
      rw [h1.2.2.2.2.2.2.1, h2.2.2.2.2.2.2.1, hfl, hγ]
    have hpoly : classPoly 3 H hn1 hnn q1.1 = classPoly 3 H hn1 hnn q2.1 := by
      rw [classPoly_eq_three_term H hn1 hnn q1.1, classPoly_eq_three_term H hn1 hnn q2.1, hb, hc]
    exact Subtype.ext (classPoly_inj 3 H hn1 hnn hpoly)
  -- the finite set of tags
  set T : Finset (ℕ × ℕ × ℤ × ℕ × ℤ) := Finset.univ.image tag with hTdef
  have hTcard : T.card =
      Nat.card {q : Quotient (fieldIsoSetoid 3 H hn1) // classDisc 3 H hn1 q ≤ Y} := by
    rw [hTdef, Finset.card_image_of_injective _ hinj, Finset.card_univ, Nat.card_eq_fintype_card]
  -- the index finset
  set I : Finset (ℕ × (ℕ × ℕ)) :=
    (Finset.Icc 1 (Nat.sqrt Y + 1)) ×ˢ (Finset.Icc 1 cubicK0 ×ˢ Finset.Icc 1 cubicS) with hIdef
  have hT_ex : ∀ x : ℕ × ℕ × ℤ × ℕ × ℤ, x ∈ T → ∃ q, tag q = x := by
    intro x hx
    rw [hTdef] at hx
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hx
    exact ⟨q, hq⟩
  have hTmem : ∀ x ∈ T, (x.1, x.2.1, x.2.2.2.1) ∈ I := by
    intro x hx
    rw [hTdef] at hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1, h2, h3, h4, h5, -, -, -, h6⟩ := htag q
    rw [hIdef, Finset.mem_product]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨h1, le_trans h6 (Nat.add_le_add_right (Nat.sqrt_le_sqrt q.2) 1)⟩
    · rw [Finset.mem_product]
      exact ⟨by rw [Finset.mem_Icc]; exact ⟨h2, h3⟩, by rw [Finset.mem_Icc]; exact ⟨h4, h5⟩⟩
  -- the cardinal bound
  have hbound : (T.card : ℝ) ≤
      ∑ u ∈ I, C * ((4 * u.1 * u.2.1 ^ 3 : ℕ) : ℝ) ^ (1 / 10 : ℝ) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : ℕ × ℕ × ℤ × ℕ × ℤ =>
      (x.1, x.2.1, x.2.2.2.1)) (s := T) (t := I) hTmem]
    push_cast
    refine Finset.sum_le_sum (fun u hu => ?_)
    rw [hIdef, Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
      Finset.mem_Icc] at hu
    obtain ⟨⟨h1u, -⟩, ⟨h2u, -⟩, h3u, h4u⟩ := hu
    let fib : Finset (ℕ × ℕ × ℤ × ℕ × ℤ) :=
      T.filter (fun x : ℕ × ℕ × ℤ × ℕ × ℤ => (x.1, x.2.1, x.2.2.2.1) = u)
    haveI : Fintype {p : ℤ × ℤ // (27 : ℤ) * p.1 ^ 2 + ((u.2.2 : ℕ) : ℤ) * p.2 ^ 2
        = ((4 * u.1 * u.2.1 ^ 3 : ℕ) : ℤ)} :=
      (finite_binary_quadratic_solutions 27 u.2.2 (by norm_num) h3u
        (4 * u.1 * u.2.1 ^ 3)).fintype
    have hfib_eq : ∀ x : ℕ × ℕ × ℤ × ℕ × ℤ, x ∈ fib →
        27 * (x.2.2.1 : ℤ) ^ 2 + ((u.2.2 : ℕ) : ℤ) * (x.2.2.2.2 : ℤ) ^ 2
          = ((4 * u.1 * u.2.1 ^ 3 : ℕ) : ℤ) := by
      intro x hx
      obtain ⟨hxT, hmem⟩ := Finset.mem_filter.mp hx
      obtain ⟨q, hq⟩ := hT_ex x hxT
      have hspec := htag q
      have h8 := hspec.2.2.2.2.2.2.2.1
      rw [hq] at h8
      have e1 : x.1 = u.1 := by
        have := congrArg (fun z : ℕ × ℕ × ℕ => z.1) hmem
        simpa using this
      have e2 : x.2.1 = u.2.1 := by
        have := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) hmem
        simpa using this
      have e3 : x.2.2.2.1 = u.2.2 := by
        have := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) hmem
        simpa using this
      rw [e1, e2, e3] at h8
      push_cast
      exact h8
    have hinj2 : Function.Injective (fun x : ↥fib =>
        (⟨(x.1.2.2.1, x.1.2.2.2.2), hfib_eq x.1 x.2⟩ :
          {p : ℤ × ℤ // (27 : ℤ) * p.1 ^ 2 + ((u.2.2 : ℕ) : ℤ) * p.2 ^ 2
            = ((4 * u.1 * u.2.1 ^ 3 : ℕ) : ℤ)})) := by
      intro x y hxy
      have hγ : x.1.2.2.1 = y.1.2.2.1 := congrArg (fun z => z.1.1) hxy
      have hm : x.1.2.2.2.2 = y.1.2.2.2.2 := congrArg (fun z => z.1.2) hxy
      have hx1 : (x.1.1, x.1.2.1, x.1.2.2.2.1) = u := (Finset.mem_filter.mp x.2).2
      have hy1 : (y.1.1, y.1.2.1, y.1.2.2.2.1) = u := (Finset.mem_filter.mp y.2).2
      have ex1 : x.1.1 = y.1.1 := by
        have ha := congrArg (fun z : ℕ × ℕ × ℕ => z.1) hx1
        have hb := congrArg (fun z : ℕ × ℕ × ℕ => z.1) hy1
        simp only at ha hb
        omega
      have ex2 : x.1.2.1 = y.1.2.1 := by
        have ha := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) hx1
        have hb := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) hy1
        simp only at ha hb
        omega
      have ex3 : x.1.2.2.2.1 = y.1.2.2.2.1 := by
        have ha := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) hx1
        have hb := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) hy1
        simp only at ha hb
        omega
      refine Subtype.ext ?_
      exact Prod.ext ex1 (Prod.ext ex2 (Prod.ext hγ (Prod.ext ex3 hm)))
    calc ((T.filter (fun x : ℕ × ℕ × ℤ × ℕ × ℤ => (x.1, x.2.1, x.2.2.2.1) = u)).card : ℝ)
        = (Nat.card ↥fib : ℝ) := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ (Nat.card {p : ℤ × ℤ // (27 : ℤ) * p.1 ^ 2 + ((u.2.2 : ℕ) : ℤ) * p.2 ^ 2
            = ((4 * u.1 * u.2.1 ^ 3 : ℕ) : ℤ)} : ℝ) := by
          exact_mod_cast Nat.card_le_card_of_injective _ hinj2
      _ ≤ C * (4 * (u.1 : ℝ) * (u.2.1 : ℝ) ^ 3) ^ (1 / 10 : ℝ) := by
          have hcast : ((4 * u.1 * u.2.1 ^ 3 : ℕ) : ℝ) = 4 * (u.1 : ℝ) * (u.2.1 : ℝ) ^ 3 := by
            push_cast; ring
          rw [← hcast]
          exact hC u.2.2 h3u h4u (4 * u.1 * u.2.1 ^ 3)
            (by have h2 : 1 ≤ u.2.1 ^ 3 := one_le_pow₀ h2u; nlinarith [h1u, h2])
  -- the cardinality of the index set
  have hIcard : (I.card : ℝ) = ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (cubicK0 : ℝ) * (cubicS : ℝ) := by
    rw [hIdef]
    simp only [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
    push_cast
    ring
  -- bound the sum
  have hsum : ∑ u ∈ I, C * ((4 * u.1 * u.2.1 ^ 3 : ℕ) : ℝ) ^ (1 / 10 : ℝ)
      ≤ (I.card : ℝ) * (C * (4 * ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (cubicK0 : ℝ) ^ 3)
          ^ (1 / 10 : ℝ)) := by
    have h1 : ∑ u ∈ I, C * ((4 * u.1 * u.2.1 ^ 3 : ℕ) : ℝ) ^ (1 / 10 : ℝ)
        ≤ ∑ _u ∈ I, C * (4 * ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (cubicK0 : ℝ) ^ 3)
            ^ (1 / 10 : ℝ) := by
      refine Finset.sum_le_sum (fun u hu => ?_)
      rw [hIdef, Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
        Finset.mem_Icc] at hu
      obtain ⟨⟨-, h1u⟩, ⟨-, h2u⟩, -⟩ := hu
      have h1' : (u.1 : ℝ) ≤ ((Nat.sqrt Y + 1 : ℕ) : ℝ) := by exact_mod_cast h1u
      have h2' : (u.2.1 : ℝ) ≤ (cubicK0 : ℝ) := by exact_mod_cast h2u
      have h3' : (0 : ℝ) ≤ (u.2.1 : ℝ) := Nat.cast_nonneg _
      have h4' : (u.2.1 : ℝ) ^ 3 ≤ (cubicK0 : ℝ) ^ 3 := pow_le_pow_left₀ h3' h2' 3
      have h5' : ((4 * u.1 * u.2.1 ^ 3 : ℕ) : ℝ) ≤ 4 * ((Nat.sqrt Y + 1 : ℕ) : ℝ)
          * (cubicK0 : ℝ) ^ 3 := by
        push_cast
        have h0' : (0 : ℝ) ≤ (u.1 : ℝ) := Nat.cast_nonneg u.1
        have hprod := mul_le_mul h1' h4' (pow_nonneg h3' 3) (Nat.cast_nonneg _)
        push_cast at hprod
        linarith [hprod]
      have hbase : (0 : ℝ) ≤ ((4 * u.1 * u.2.1 ^ 3 : ℕ) : ℝ) :=
        Nat.cast_nonneg (4 * u.1 * u.2.1 ^ 3)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase h5' (by norm_num)) hCpos.le
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    exact h1
  -- final arithmetic
  have hYhalf : (1 : ℝ) ≤ (Y : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.one_le_sqrt.mpr (by exact_mod_cast hY)
  have hYle : ((Nat.sqrt Y + 1 : ℕ) : ℝ) ≤ 2 * (Y : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 : ((Nat.sqrt Y : ℕ) : ℝ) ≤ (Y : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt Y))]
      exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' Y)
    push_cast
    linarith
  have hYpos : (0 : ℝ) < (Y : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hY)
  have hfinal : (I.card : ℝ) * (C * (4 * ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (cubicK0 : ℝ) ^ 3)
        ^ (1 / 10 : ℝ))
      ≤ (2 * (cubicK0 : ℝ) * (cubicS : ℝ)
            * (C * (8 * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ)) + 1)
          * (Y : ℝ) ^ (1 / 2 + 1 / 20 : ℝ) := by
    rw [hIcard]
    have hK : (0 : ℝ) < (cubicK0 : ℝ) := by
      rw [cubicK0]
      push_cast
      have h := Nat.le_ceil (8 * 2 ^ 24 * Real.sqrt (cubicS : ℝ))
      linarith
    have hstep1 : (4 * ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ)
        ≤ (8 * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ) * (Y : ℝ) ^ (1 / 20 : ℝ) := by
      have h2 : 4 * ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (cubicK0 : ℝ) ^ 3
          ≤ (8 * (cubicK0 : ℝ) ^ 3) * (Y : ℝ) ^ (1 / 2 : ℝ) := by
        nlinarith [hYle, hYhalf, hK, pow_pos hK 3]
      calc (4 * ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ)
          ≤ ((8 * (cubicK0 : ℝ) ^ 3) * (Y : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 10 : ℝ) :=
            Real.rpow_le_rpow (by positivity) h2 (by norm_num)
        _ = (8 * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ) * ((Y : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 10 : ℝ) :=
            Real.mul_rpow (by positivity) (by positivity)
        _ = (8 * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ) * (Y : ℝ) ^ (1 / 20 : ℝ) := by
            rw [← Real.rpow_mul hYpos.le]; norm_num
    have hstep2 : ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (Y : ℝ) ^ (1 / 20 : ℝ)
        ≤ 2 * (Y : ℝ) ^ (1 / 2 + 1 / 20 : ℝ) := by
      calc ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (Y : ℝ) ^ (1 / 20 : ℝ)
          ≤ (2 * (Y : ℝ) ^ (1 / 2 : ℝ)) * (Y : ℝ) ^ (1 / 20 : ℝ) :=
            mul_le_mul_of_nonneg_right hYle (by positivity)
        _ = 2 * ((Y : ℝ) ^ (1 / 2 : ℝ) * (Y : ℝ) ^ (1 / 20 : ℝ)) := by ring
        _ = 2 * (Y : ℝ) ^ (1 / 2 + 1 / 20 : ℝ) := by rw [← Real.rpow_add hYpos]
    calc ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (cubicK0 : ℝ) * (cubicS : ℝ)
          * (C * (4 * ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ))
        ≤ ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (cubicK0 : ℝ) * (cubicS : ℝ)
          * (C * ((8 * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ) * (Y : ℝ) ^ (1 / 20 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep1 hCpos.le) (by positivity)
      _ = (cubicK0 : ℝ) * (cubicS : ℝ) * C * (8 * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ)
            * (((Nat.sqrt Y + 1 : ℕ) : ℝ) * (Y : ℝ) ^ (1 / 20 : ℝ)) := by ring
      _ ≤ (cubicK0 : ℝ) * (cubicS : ℝ) * C * (8 * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ)
            * (2 * (Y : ℝ) ^ (1 / 2 + 1 / 20 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left hstep2 (by positivity)
      _ = (2 * (cubicK0 : ℝ) * (cubicS : ℝ) * (C * (8 * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ)))
            * (Y : ℝ) ^ (1 / 2 + 1 / 20 : ℝ) := by ring
      _ ≤ (2 * (cubicK0 : ℝ) * (cubicS : ℝ)
            * (C * (8 * (cubicK0 : ℝ) ^ 3) ^ (1 / 10 : ℝ)) + 1)
          * (Y : ℝ) ^ (1 / 2 + 1 / 20 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hYpos.le _)
          linarith
  calc ((Nat.card {q : Quotient (fieldIsoSetoid 3 H hn1) // classDisc 3 H hn1 q ≤ Y} : ℕ) : ℝ)
      = (T.card : ℝ) := by rw [hTcard]
    _ ≤ ∑ u ∈ I, C * ((4 * u.1 * u.2.1 ^ 3 : ℕ) : ℝ) ^ (1 / 10 : ℝ) := hbound
    _ ≤ (I.card : ℝ) * (C * (4 * ((Nat.sqrt Y + 1 : ℕ) : ℝ) * (cubicK0 : ℝ) ^ 3)
          ^ (1 / 10 : ℝ)) := hsum
    _ ≤ _ := hfinal

/-! ## 7. The challenge theorem in degree three -/

/-- The exponent condition for the degree-three endpoint. -/
theorem exponent_cubic_final :
    1 + (2 + 4 / (weylM 3 : ℝ)) * (1 / 2 + 1 / 20 - 1 / ((3 : ℝ) * ((3 : ℝ) - 1)))
      < (3 : ℝ) - 1 := by
  norm_num [weylM]

/-- **The challenge theorem in degree three**, unconditionally: the Case-II
field count is `fieldCountBound_three_cyclic`, the per-field fibre bound is
`perFieldFibreBound_all` (Lemke Oliver–Thorne, a theorem in the project), and
the imprimitive input is vacuous in prime degree. -/
theorem theorem_1_three :
    (fun H : ℕ => (E 3 H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ (3 - 1) : ℝ)) :=
  theorem_1_of_field_inputs_exp 3 (by omega) (1 / 2 + 1 / 20)
    (1 / ((3 : ℝ) * ((3 : ℝ) - 1)))
    (by norm_num) exponent_cubic_final
    (perFieldFibreBound_exp_classical 3 (show 1 ≤ 3 by omega)
      (perFieldFibreBound_all 3 (show 3 ≤ 3 by omega)))
    fieldCountBound_three_cyclic
    (ImprimitiveBad_isBigO_of_prime 3 (by norm_num))

end

end Submission.Vdw
