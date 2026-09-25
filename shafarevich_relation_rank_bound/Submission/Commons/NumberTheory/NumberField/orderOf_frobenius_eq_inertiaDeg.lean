import Mathlib
import Submission.Commons.NumberTheory.NumberField.perfectField_residueField_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.frobenius_eq_of_commute

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.NumberTheory.NumberField

open Polynomial

/-! ## A finite-field counting lemma

If `F` is a finite field of cardinality `q ^ f` with `2 ≤ q`, and the `q ^ k`-th power map is the
identity on `F` with `0 < k`, then `f ≤ k`: the polynomial `X ^ (q ^ k) - X` vanishes on `F`, hence
its degree `q ^ k` is at least `#F = q ^ f`. -/
theorem le_of_forall_pow_eq_self {F : Type*} [Field F] [Fintype F] {q f k : ℕ}
    (hcard : Nat.card F = q ^ f) (hq : 2 ≤ q) (hk : 0 < k)
    (h : ∀ y : F, y ^ (q ^ k) = y) : f ≤ k := by
  by_contra hlt
  rw [not_le] at hlt
  have hq1 : 1 < q := by omega
  have hpow : q ^ k < q ^ f := Nat.pow_lt_pow_right hq1 hlt
  have hqk : 2 ≤ q ^ k := le_trans hq (Nat.le_self_pow (by omega : k ≠ 0) q)
  have hp : (X ^ (q ^ k) - X : F[X]) ≠ 0 := by
    intro hzero
    have hc := congrArg (fun p : F[X] => p.coeff (q ^ k)) hzero
    rw [coeff_sub, coeff_X_pow, coeff_X, coeff_zero] at hc
    have hne1 : ¬ (1 = q ^ k) := by omega
    simp only [if_true, hne1, if_false, sub_zero] at hc
    exact one_ne_zero hc
  have hdeg : (X ^ (q ^ k) - X : F[X]).natDegree ≤ q ^ k := by
    calc (X ^ (q ^ k) - X : F[X]).natDegree
        ≤ max (X ^ (q ^ k) : F[X]).natDegree (X : F[X]).natDegree := natDegree_sub_le _ _
      _ = max (q ^ k) 1 := by rw [natDegree_X_pow, natDegree_X]
      _ ≤ q ^ k := max_le le_rfl (by omega)
  have hcardF : Fintype.card F = q ^ f := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have hlt' : (X ^ (q ^ k) - X : F[X]).natDegree < Fintype.card F := by
    rw [hcardF]
    exact lt_of_le_of_lt hdeg hpow
  have heval : ∀ y : F, (X ^ (q ^ k) - X : F[X]).eval y = 0 := by
    intro y
    simp only [eval_sub, eval_pow, eval_X]
    rw [h y, sub_self]
  have hzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (X ^ (q ^ k) - X : F[X]) (ι := F) Function.injective_id heval hlt'
  exact hp hzero

/-- The `q`-th power map is the identity on a finite field of cardinality `q`. -/
theorem pow_natCard_eq_self {F : Type*} [Field F] [Finite F] (y : F) : y ^ Nat.card F = y := by
  haveI := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card y

/-- **Cardinality of the residue field.**  For a finite extension `L/K` of number fields and a
prime `P` of `𝓞 L` lying over `p` of `𝓞 K`, the residue field `𝓞 L / P` has cardinality
`(#(𝓞 K / p)) ^ f`, where `f` is the inertia degree of `P` over `p`. -/
theorem natCard_residue_eq_pow_inertiaDeg {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hP : P.asIdeal.LiesOver p.asIdeal) :
    Nat.card (NumberField.RingOfIntegers L ⧸ P.asIdeal) =
      (Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal)) ^
        (P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
  haveI := hP
  haveI : p.asIdeal.IsMaximal := inferInstance
  haveI : P.asIdeal.IsMaximal := inferInstance
  letI : Field (NumberField.RingOfIntegers K ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  letI : Field (NumberField.RingOfIntegers L ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  rw [Module.natCard_eq_pow_finrank (K := NumberField.RingOfIntegers K ⧸ p.asIdeal)
    (V := NumberField.RingOfIntegers L ⧸ P.asIdeal)]
  congr 1
  exact (Ideal.inertiaDeg_eq_of_isMaximal p.asIdeal P.asIdeal).symm

/-- **The residue action of powers of an element.**  If `σ ∈ Gal(L/K)` acts on the residue field
`𝓞 L / P` by `x ↦ x ^ q` with `q = #(𝓞 K / p)`, then `σ ^ m` acts by `x ↦ x ^ (q ^ m)`. -/
theorem residue_pow_galRestrict_pow {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : Gal(L/K))
    (hres : ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk P.asIdeal (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) σ x) =
      (Ideal.Quotient.mk P.asIdeal x) ^ (Nat.card ((NumberField.RingOfIntegers K) ⧸ p.asIdeal)))
    :
    ∀ (m : ℕ) (x : NumberField.RingOfIntegers L),
    Ideal.Quotient.mk P.asIdeal (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) (σ ^ m) x) =
    (Ideal.Quotient.mk P.asIdeal x) ^ ((Nat.card ((NumberField.RingOfIntegers K) ⧸ p.asIdeal)) ^ m) := by
  intro m
  induction m with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    rw [pow_succ, map_mul, AlgEquiv.mul_apply]
    rw [ih (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ x)]
    rw [hres x, ← pow_mul]
    congr 1
    rw [pow_succ, Nat.mul_comm]

/-- **The order of a Frobenius element is the inertia degree.**  Let `L/K` be a finite Galois
extension of number fields, `P` a prime of `𝓞 L` over `p` of `𝓞 K`, unramified over `p`
(`e(P|p) = 1`).  If `σ ∈ Gal(L/K)` stabilises `P` and acts on the residue field `𝓞 L / P` by the
`q`-th power map, where `q = #(𝓞 K / p)`, then `orderOf σ` is the inertia degree `f(P|p)`.

Indeed `σ` is the Frobenius element at `P`: its residue action generates the Galois group of the
finite residue field extension, whose order is `f`; the subgroup it generates acts faithfully on
the residue field because `P` is unramified, so `orderOf σ = f`. -/
theorem orderOf_frobenius_eq_inertiaDeg {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hP : P.asIdeal.LiesOver p.asIdeal)
    (hunr : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (σ : Gal(L/K))
    (hσ : Ideal.map (galRestrict (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L) σ : NumberField.RingOfIntegers L →+*
        NumberField.RingOfIntegers L) P.asIdeal = P.asIdeal)
    (hres : ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk P.asIdeal (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L) σ x) =
      (Ideal.Quotient.mk P.asIdeal x) ^ (Nat.card ((NumberField.RingOfIntegers K) ⧸ p.asIdeal))) :
    orderOf σ = P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  classical
  haveI hPlies : P.asIdeal.LiesOver p.asIdeal := hP
  haveI hmaxp : p.asIdeal.IsMaximal := inferInstance
  haveI hmaxP : P.asIdeal.IsMaximal := inferInstance
  haveI hfinL : Finite (NumberField.RingOfIntegers L ⧸ P.asIdeal) :=
    finite_quotient_heightOneSpectrum P
  haveI hfinK : Finite (NumberField.RingOfIntegers K ⧸ p.asIdeal) :=
    finite_quotient_heightOneSpectrum p
  letI hfieldL : Field (NumberField.RingOfIntegers L ⧸ P.asIdeal) :=
    Ideal.Quotient.field P.asIdeal
  letI hfieldK : Field (NumberField.RingOfIntegers K ⧸ p.asIdeal) :=
    Ideal.Quotient.field p.asIdeal
  haveI hfintypeL : Fintype (NumberField.RingOfIntegers L ⧸ P.asIdeal) := Fintype.ofFinite _
  haveI hfintypeK : Fintype (NumberField.RingOfIntegers K ⧸ p.asIdeal) := Fintype.ofFinite _
  have hq2 : 2 ≤ Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hcard : Nat.card (NumberField.RingOfIntegers L ⧸ P.asIdeal) =
      (Nat.card (NumberField.RingOfIntegers K ⧸ p.asIdeal)) ^
        (P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) :=
    natCard_residue_eq_pow_inertiaDeg p P hP
  -- ### First half: `σ ^ f = 1`
  have hres_f : ∀ x : NumberField.RingOfIntegers L,
      Ideal.Quotient.mk P.asIdeal (galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L)
        (σ ^ (P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))) x) =
      Ideal.Quotient.mk P.asIdeal x := by
    intro x
    rw [residue_pow_galRestrict_pow p P σ hres
      (P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) x]
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have hσf : σ ^ (P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) = 1 :=
    FrobeniusEqOfCommute.eq_one_of_residue_mk_eq_one p P hP hunr _ hres_f
  have horder_dvd : orderOf σ ∣ P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    orderOf_dvd_iff_pow_eq_one.mpr hσf
  -- ### Second half: `f ≤ orderOf σ`
  have hf_le : P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) ≤ orderOf σ := by
    refine le_of_forall_pow_eq_self (F := NumberField.RingOfIntegers L ⧸ P.asIdeal)
      hcard hq2 (orderOf_pos σ) (fun y => ?_)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← residue_pow_galRestrict_pow p P σ hres (orderOf σ) x, pow_orderOf_eq_one, map_one]
    rfl
  -- ### Conclusion
  have hf_pos : 0 < P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    by_contra h
    rw [not_lt] at h
    have h0 : P.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 0 :=
      Nat.eq_zero_of_le_zero h
    rw [h0, pow_zero] at hcard
    have h2 : 2 ≤ Nat.card (NumberField.RingOfIntegers L ⧸ P.asIdeal) := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
    omega
  exact le_antisymm (Nat.le_of_dvd hf_pos horder_dvd) hf_le

end Commons.NumberTheory.NumberField
