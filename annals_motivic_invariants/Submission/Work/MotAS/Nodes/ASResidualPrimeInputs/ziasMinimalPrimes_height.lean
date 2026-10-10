import Mathlib
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.minimalPrimes_height_two_of_relPrime
import Submission.Work.MotAS.ASZElimMem
import Submission.Work.MotAS.aszDpQuad
import Submission.Work.MotAS.ASZElimData
import Submission.Work.MotAS.ASZElimQ0
import Submission.Work.MotAS.ASRulV2.aszSatDataAS
import Submission.Work.MotC5N3.AK

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.Nodes.ASResidualPrimeInputs

/-
ROUTE.  `Work.MotAS.minimalPrimes_height_two_of_relPrime` (`Submission/Work/MotAS/
minimalPrimes_height_two_of_relPrime.lean`, PROVED) says: if an ideal `I` of
`K[X₀,X₁,X₂]` contains two relatively prime elements `f, g`, then `2 ≤ 𝔭.height` for all
`𝔭 ∈ I.minimalPrimes`.  So it suffices to exhibit two relatively prime elements of
`Z := ZIAS (aK D) (bK D) (fAS 𝕜)`.

Two such elements are available *without any new computation*:

* `f := MvPolynomial.rename Fin.succ (Work.MotAS.ASZElim.P (aK D) (bK D) (fAS 𝕜))` — the
  eliminant; `f ∈ Z` **and** `f ≠ 0` are the two conjuncts of
  `Work.MotAS.ASRulV2.aszElimP_mem_ne_zero` (`Submission/Work/MotAS/ASRulV2/aszSatDataAS.lean`,
  PROVED).  Note `f` is `X 0`-free.
* `g := X 0 ^ 2 + rename Fin.succ l * X 0 + rename Fin.succ A`, where `l, A` are the witnesses
  of `Work.MotAS.aszDpQuad` (`Submission/Work/MotAS/aszDpQuad.lean`, PROVED): this is a *monic*
  quadratic in `X 0` lying in `Z`.

`IsRelPrime f g`: if `d ∣ f` then (honest division in the domain `(K[X₁,X₂])[X 0]`, `f ≠ 0`
`X 0`-free) `d` is `X 0`-free; and `d ∣ g` with `g` monic in `X 0` forces `d ∣ 1` (compare the
`X 0`-leading coefficient).  Hence `d` is a unit.  This is carried out below with the
`Polynomial`/`MvPolynomial.finSuccEquiv` bookkeeping, via the lemmas

* `finSuccEquiv_rename_succ` : `finSuccEquiv K 2 (rename Fin.succ p) = Polynomial.C p`;
* `isRelPrime_C_of_monic` : a nonzero constant polynomial is relatively prime to a monic
  polynomial (degree bookkeeping in `A[X]`, `A` a domain);
* `monic_X_sq_add_linear` : `X ^ 2 + C l * X + C m` is monic;
* `isRelPrime_rename_succ_of_monic` : the transport of the first two along `finSuccEquiv`.

Side conditions: `ASGood D` gives `D.a * D.b ≠ 0`, `D.a ^ 2 - D.a * D.b - D.b ^ 2 ≠ 0`; push them
along `algebraMap 𝕜 (RatFunc 𝕜)` with `Work.MotAS.aK`, `Work.MotAS.bK`, using
`Work.MotC5N3.aK_ne_zero`, `Work.MotC5N3.bK_ne_zero`, `Work.MotC5N3.aK_sq_sub_ne`
(`Submission/Work/MotC5N3/AK.lean`); `fAS 𝕜 ∉ ℘(RatFunc 𝕜)` is
`Work.MotV5.CensusAux.fAS_notMem_pe`.
-/

/-- `MvPolynomial.finSuccEquiv` sends `rename Fin.succ p` to the constant polynomial `C p`: the
variables `X 1, …, X n` of `K[X₀,…,X_n]` are exactly the "coefficient" variables `X 0, …, X (n-1)`
of the polynomial ring `K[X₁,…,X_n][X₀]`. -/
theorem finSuccEquiv_rename_succ {R : Type*} [CommSemiring R] (n : ℕ)
    (p : MvPolynomial (Fin n) R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.rename Fin.succ p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C]
    simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_succ, hp]

/-- A nonzero constant polynomial is relatively prime to a monic polynomial: if `d ∣ C c` with
`c ≠ 0` then `d` has degree `0`, say `d = C e`; and `d ∣ p` with `p` monic compares leading
coefficients in the domain `A`, giving `e * (p / d).leadingCoeff = 1`, so `e`, hence `d`, is a
unit. -/
theorem isRelPrime_C_of_monic {A : Type*} [CommRing A] [IsDomain A] (c : A) (hc : c ≠ 0)
    (p : Polynomial A) (hp : p.Monic) : IsRelPrime (Polynomial.C c) p := by
  intro d hda hdb
  obtain ⟨q, hq⟩ := hda
  have hCc : (Polynomial.C c : Polynomial A) ≠ 0 := Polynomial.C_ne_zero.mpr hc
  have hdne : d ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hq
    exact hCc hq
  have hqne : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hCc hq
  have hd0 : d.natDegree = 0 := by
    have h := Polynomial.natDegree_mul hdne hqne
    rw [← hq, Polynomial.natDegree_C] at h
    omega
  obtain ⟨r, hr⟩ := hdb
  have hdC : d = Polynomial.C (d.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd0
  have hkey : (1 : A) = d.coeff 0 * r.leadingCoeff := by
    have h1 : (d * r).leadingCoeff = 1 := by rw [← hr, hp.leadingCoeff]
    rw [Polynomial.leadingCoeff_mul, hdC, Polynomial.leadingCoeff_C] at h1
    exact h1.symm
  have hunit : IsUnit (d.coeff 0) := isUnit_iff_dvd_one.mpr ⟨r.leadingCoeff, hkey⟩
  have h2 : IsUnit (Polynomial.C (d.coeff 0)) :=
    IsUnit.map (Polynomial.C : A →+* Polynomial A) hunit
  rw [hdC]
  exact h2

/-- `X ^ 2 + C l * X + C m` is monic in `A[X]`. -/
theorem monic_X_sq_add_linear {A : Type*} [Semiring A] [Nontrivial A] (l m : A) :
    (Polynomial.X ^ 2 + Polynomial.C l * Polynomial.X + Polynomial.C m : Polynomial A).Monic := by
  have hdeg : (Polynomial.C l * Polynomial.X + Polynomial.C m : Polynomial A).degree
      < (2 : WithBot ℕ) := by
    have h1 : (Polynomial.C l * Polynomial.X : Polynomial A).degree ≤ 1 := by
      calc (Polynomial.C l * Polynomial.X : Polynomial A).degree
          ≤ (Polynomial.C l).degree + Polynomial.X.degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + 1 := add_le_add Polynomial.degree_C_le (le_of_eq Polynomial.degree_X)
        _ = 1 := by norm_num
    have h2 : (Polynomial.C m : Polynomial A).degree ≤ 0 := Polynomial.degree_C_le
    have h : (Polynomial.C l * Polynomial.X + Polynomial.C m : Polynomial A).degree ≤ 1 :=
      le_trans (Polynomial.degree_add_le _ _) (max_le h1 (le_trans h2 (by norm_num)))
    exact lt_of_le_of_lt h (by norm_num)
  have := Polynomial.monic_X_pow_add (p := Polynomial.C l * Polynomial.X + Polynomial.C m)
    (n := 2) hdeg
  simpa only [add_assoc] using this

/-- An element of `K[X₀,X₁,X₂]` which is a nonzero `X 0`-free polynomial is relatively prime to
any polynomial whose image under `finSuccEquiv` is monic in `X 0` of degree `2`.

The proof transports along the algebra equivalence
`MvPolynomial.finSuccEquiv K 2 : K[X₀,X₁,X₂] ≃ₐ[K] (K[X₁,X₂])[X₀]`, under which the first
argument becomes the nonzero constant `C P`, and the second a monic polynomial. -/
theorem isRelPrime_rename_succ_of_monic {K : Type*} [Field K] {P : MvPolynomial (Fin 2) K}
    (hP : P ≠ 0) {p : MvPolynomial (Fin 3) K} (hp : (MvPolynomial.finSuccEquiv K 2 p).Monic) :
    IsRelPrime (MvPolynomial.rename Fin.succ P) p := by
  intro d hd1 hd2
  have hrel : IsRelPrime (Polynomial.C P) (MvPolynomial.finSuccEquiv K 2 p) :=
    isRelPrime_C_of_monic P hP _ hp
  have h1 : (MvPolynomial.finSuccEquiv K 2 d) ∣ Polynomial.C P := by
    rw [← finSuccEquiv_rename_succ 2 P]
    simpa using map_dvd (MvPolynomial.finSuccEquiv K 2).toRingHom.1 hd1
  have h2 : (MvPolynomial.finSuccEquiv K 2 d) ∣ MvPolynomial.finSuccEquiv K 2 p := by
    simpa using map_dvd (MvPolynomial.finSuccEquiv K 2).toRingHom.1 hd2
  have hu : IsUnit (MvPolynomial.finSuccEquiv K 2 d) := hrel h1 h2
  have hu2 : IsUnit ((MvPolynomial.finSuccEquiv K 2).symm (MvPolynomial.finSuccEquiv K 2 d)) :=
    IsUnit.map ((MvPolynomial.finSuccEquiv K 2).symm).toRingHom hu
  rwa [AlgEquiv.symm_apply_apply] at hu2

theorem ziasMinimalPrimes_height (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    ∀ 𝔭 ∈ (Work.MotAS.ZIAS (Work.MotAS.aK D) (Work.MotAS.bK D)
        (Work.MotV.fAS 𝕜)).minimalPrimes, 2 ≤ Ideal.height 𝔭 := by
  -- the eliminant is a nonzero `X 0`-free element of the residual chart ideal `Z`
  obtain ⟨hPne, hPmem⟩ := Work.MotAS.ASRulV2.aszElimP_mem_ne_zero 𝕜 D hD
  -- the side conditions of `aszDpQuad`, pushed to `K = RatFunc 𝕜`
  have hab : Work.MotAS.aK D * Work.MotAS.bK D ≠ 0 :=
    mul_ne_zero (Work.MotC5N3.aK_ne_zero (K := RatFunc 𝕜) D hD)
      (Work.MotC5N3.bK_ne_zero (K := RatFunc 𝕜) D hD)
  have hs : Work.MotAS.aK D ^ 2 - Work.MotAS.aK D * Work.MotAS.bK D
      - Work.MotAS.bK D ^ 2 ≠ 0 :=
    Work.MotC5N3.aK_sq_sub_ne (K := RatFunc 𝕜) D hD
  have hg : ¬ ∃ c : RatFunc 𝕜, c ^ 5 - c = Work.MotV.fAS 𝕜 := by
    simpa [Work.MotV.fAS] using Work.MotV5.CensusAux.fAS_notMem_pe 𝕜
  -- a monic quadratic in `X 0` inside `Z`
  obtain ⟨l, A, hqmem⟩ := Work.MotAS.aszDpQuad (RatFunc 𝕜) (Work.MotAS.aK D)
    (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) hs hg hab
  refine Work.MotAS.minimalPrimes_height_two_of_relPrime
    (Work.MotAS.ZIAS (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜))
    (MvPolynomial.rename Fin.succ (Work.MotAS.ASZElim.P (Work.MotAS.aK D) (Work.MotAS.bK D)
      (Work.MotV.fAS 𝕜)))
    (MvPolynomial.X 0 ^ 2 + MvPolynomial.rename Fin.succ l * MvPolynomial.X 0
      + MvPolynomial.rename Fin.succ A) hPmem hqmem ?_
  refine isRelPrime_rename_succ_of_monic hPne ?_
  have hfq : MvPolynomial.finSuccEquiv (RatFunc 𝕜) 2
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.rename Fin.succ l * MvPolynomial.X 0
        + MvPolynomial.rename Fin.succ A)
      = Polynomial.X ^ 2 + Polynomial.C l * Polynomial.X + Polynomial.C A := by
    simp only [map_add, map_mul, map_pow, MvPolynomial.finSuccEquiv_X_zero,
      finSuccEquiv_rename_succ]
  rw [hfq]
  exact monic_X_sq_add_linear l A

end Work.MotAS.Nodes.ASResidualPrimeInputs
