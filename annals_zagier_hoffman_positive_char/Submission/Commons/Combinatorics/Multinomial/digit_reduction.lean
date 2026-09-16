import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.RingTheory.MvPolynomial.Basic

set_option linter.style.haveILetI false

open Finset

namespace Commons.Combinatorics.Multinomial

variable {ι : Type*} [Fintype ι]

/-- The multinomial coefficient of a function equals that of the corresponding finitely supported
function. -/
private lemma multinomial_eq_finsupp (f : ι → ℕ) :
    Nat.multinomial Finset.univ f = (Finsupp.equivFunOnFinite.symm f).multinomial := by
  classical
  rw [Finsupp.multinomial_eq]
  refine (Nat.multinomial_congr_of_sdiff (Finset.subset_univ _) ?_ ?_).symm
  · intro i hi
    rw [Finset.mem_sdiff] at hi
    have h1 : (Finsupp.equivFunOnFinite.symm f) i = 0 := by
      by_contra h
      exact hi.2 (Finsupp.mem_support_iff.mpr h)
    simpa [Finsupp.coe_equivFunOnFinite_symm] using h1
  · intro i _
    exact congr_fun (Finsupp.coe_equivFunOnFinite_symm f) i

/-- **Dickson's digit-reduction formula for multinomial coefficients.**  Splitting every entry of a
multiset of `ℕ`'s into its lowest `l` base-`p` digits and the remaining part, the multinomial
coefficient factors modulo `p`:
`multinomial a ≡ multinomial (a mod p^l) * multinomial (a / p^l)  (mod p)`.

Equivalently: `C_ā = C_{ã} C_{ã̃}` in the notation of Chen, *Anderson–Thakur polynomials and
multizeta values in positive characteristic*, arXiv:1506.06463, §2 (with `q = p^l`). -/
theorem digit_reduction {ι : Type*} [Fintype ι] (p l : ℕ) (hp : p.Prime) (a : ι → ℕ) :
    ((Nat.multinomial Finset.univ a : ℕ) : ZMod p)
      = ((Nat.multinomial Finset.univ (fun i => a i % p ^ l) : ℕ) : ZMod p)
        * ((Nat.multinomial Finset.univ (fun i => a i / p ^ l) : ℕ) : ZMod p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set q := p ^ l with hq
  have hqpos : 0 < q := by rw [hq]; exact pow_pos hp.pos l
  set N := ∑ i, a i / q with hN
  set m := ∑ i, a i % q with hm
  have hn : ∑ i, a i = q * N + m := by
    rw [hN, hm, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (Nat.div_add_mod (a i) q).symm
  set A : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm a with hAdef
  set B : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => a i / q) with hBdef
  set R : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => a i % q) with hRdef
  have hA : ∀ i, A i = a i := fun i => by
    rw [hAdef]; exact congr_fun (Finsupp.coe_equivFunOnFinite_symm a) i
  have hB : ∀ i, B i = a i / q := fun i => by
    rw [hBdef]; exact congr_fun (Finsupp.coe_equivFunOnFinite_symm _) i
  have hR : ∀ i, R i = a i % q := fun i => by
    rw [hRdef]; exact congr_fun (Finsupp.coe_equivFunOnFinite_symm _) i
  have hAsum : A.sum (fun _ x => x) = ∑ i, a i := by
    rw [hAdef]; exact Finsupp.equivFunOnFinite_symm_sum a
  have hBsum : B.sum (fun _ x => x) = N := by
    rw [hN, hBdef]; exact Finsupp.equivFunOnFinite_symm_sum _
  have hRsum : R.sum (fun _ x => x) = m := by
    rw [hm, hRdef]; exact Finsupp.equivFunOnFinite_symm_sum _
  have hfrob : (∑ i, (MvPolynomial.X i : MvPolynomial ι (ZMod p))) ^ q
      = ∑ i, (MvPolynomial.X i) ^ q := by
    simpa [hq] using sum_pow_char_pow (R := MvPolynomial ι (ZMod p)) (p := p) (n := l)
      (Finset.univ : Finset ι) (fun i => (MvPolynomial.X i : MvPolynomial ι (ZMod p)))
  have hpoly : (∑ i, (MvPolynomial.X i : MvPolynomial ι (ZMod p))) ^ (∑ i, a i)
      = (∑ i, (MvPolynomial.X i) ^ q) ^ N * (∑ i, (MvPolynomial.X i)) ^ m := by
    rw [hn, pow_add, pow_mul, hfrob]
  have hcoeffL : MvPolynomial.coeff A
        ((∑ i, (MvPolynomial.X i : MvPolynomial ι (ZMod p))) ^ (∑ i, a i))
      = (A.multinomial : ZMod p) := by
    rw [MvPolynomial.coeff_sum_X_pow_of_fintype, if_pos hAsum]
  -- expansion of `(∑ X i ^ q)^N` into monomials
  have hexp : (∑ i, (MvPolynomial.X i : MvPolynomial ι (ZMod p)) ^ q) ^ N
      = ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) N,
          MvPolynomial.monomial
            (Finsupp.indicator (Finset.univ : Finset ι) (fun i _ => q * k i))
            ((Nat.multinomial Finset.univ k : ℕ) : ZMod p) := by
    rw [Finset.sum_pow_eq_sum_piAntidiag]
    apply Finset.sum_congr rfl
    intro k _
    rw [← MvPolynomial.C_eq_coe_nat (Nat.multinomial Finset.univ k)]
    rw [show (∏ i ∈ Finset.univ, ((MvPolynomial.X i : MvPolynomial ι (ZMod p)) ^ q) ^ k i)
          = MvPolynomial.monomial
              (Finsupp.indicator (Finset.univ : Finset ι) (fun i _ => q * k i)) (1 : ZMod p) from by
        rw [← MvPolynomial.prod_X_pow (fun i => q * k i) (Finset.univ : Finset ι)]
        apply Finset.prod_congr rfl
        intro i _
        rw [pow_mul]]
    rw [MvPolynomial.C_mul_monomial, mul_one]
  have hcoeffR : MvPolynomial.coeff A
        ((∑ i, (MvPolynomial.X i : MvPolynomial ι (ZMod p)) ^ q) ^ N
          * (∑ i, (MvPolynomial.X i : MvPolynomial ι (ZMod p))) ^ m)
      = (B.multinomial : ZMod p) * (R.multinomial : ZMod p) := by
    have hcm : ∀ k : ι → ℕ,
        MvPolynomial.coeff A
            (MvPolynomial.monomial
              (Finsupp.indicator (Finset.univ : Finset ι) (fun i _ => q * k i))
              ((Nat.multinomial Finset.univ k : ℕ) : ZMod p)
              * (∑ i, (MvPolynomial.X i : MvPolynomial ι (ZMod p))) ^ m)
          = if (Finsupp.indicator (Finset.univ : Finset ι) (fun i _ => q * k i)) ≤ A
              then ((Nat.multinomial Finset.univ k : ℕ) : ZMod p)
                * MvPolynomial.coeff
                    (A - Finsupp.indicator (Finset.univ : Finset ι) (fun i _ => q * k i))
                    ((∑ i, (MvPolynomial.X i : MvPolynomial ι (ZMod p))) ^ m)
              else 0 :=
      fun k => MvPolynomial.coeff_monomial_mul' _ _ _ _
    have hsum : (∑ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) N,
          MvPolynomial.coeff A
            (MvPolynomial.monomial
              (Finsupp.indicator (Finset.univ : Finset ι) (fun i _ => q * k i))
              ((Nat.multinomial Finset.univ k : ℕ) : ZMod p)
              * (∑ i, (MvPolynomial.X i : MvPolynomial ι (ZMod p))) ^ m))
        = MvPolynomial.coeff A
            (MvPolynomial.monomial
              (Finsupp.indicator (Finset.univ : Finset ι) (fun i _ => q * (a i / q)))
              ((Nat.multinomial Finset.univ (fun i => a i / q) : ℕ) : ZMod p)
              * (∑ i, (MvPolynomial.X i : MvPolynomial ι (ZMod p))) ^ m) := by
      refine Finset.sum_eq_single (fun i => a i / q) ?_ ?_
      · intro k hk hkne
        have hnotle : ¬ (Finsupp.indicator (Finset.univ : Finset ι) (fun i _ => q * k i)) ≤ A := by
          intro hle
          have hkA : ∀ i, k i ≤ a i / q := by
            intro i
            have h1 : q * k i ≤ a i := by
              have h2 := (Finsupp.le_def.mp hle) i
              rwa [Finsupp.indicator_of_mem (Finset.mem_univ i), hA i] at h2
            exact (Nat.le_div_iff_mul_le hqpos).mpr (by rwa [mul_comm] at h1)
          have hksum : ∑ i, k i = N := by
            simpa using (Finset.mem_piAntidiag.mp hk).1
          have hfun : k = fun i => a i / q := by
            funext i
            have hiff := Finset.sum_eq_sum_iff_of_le (s := (Finset.univ : Finset ι))
              (f := k) (g := fun i => a i / q) (fun i _ => hkA i)
            exact (hiff.mp (by rw [hksum, hN]) i (Finset.mem_univ i))
          exact absurd hfun hkne
        rw [hcm k, if_neg hnotle]
      · intro hknot
        exact absurd (Finset.mem_piAntidiag.mpr ⟨hN.symm, fun i _ => Finset.mem_univ i⟩) hknot
    rw [hexp, Finset.sum_mul, MvPolynomial.coeff_sum, hsum]
    have hAR : A = Finsupp.indicator (Finset.univ : Finset ι) (fun i _ => q * (a i / q)) + R := by
      ext i
      rw [Finsupp.add_apply, Finsupp.indicator_of_mem (Finset.mem_univ i), hA i, hR i]
      exact (Nat.div_add_mod (a i) q).symm
    have hB2 : Nat.multinomial Finset.univ (fun i => a i / q) = B.multinomial := by
      rw [hBdef]; exact multinomial_eq_finsupp _
    rw [hAR, MvPolynomial.coeff_monomial_mul, MvPolynomial.coeff_sum_X_pow_of_fintype,
      if_pos hRsum, hB2]
  have key : (A.multinomial : ZMod p) = (B.multinomial : ZMod p) * (R.multinomial : ZMod p) := by
    rw [← hcoeffL, hpoly, hcoeffR]
  have hA2 : Nat.multinomial Finset.univ a = A.multinomial := by
    rw [hAdef]; exact multinomial_eq_finsupp a
  have hR2 : Nat.multinomial Finset.univ (fun i => a i % q) = R.multinomial := by
    rw [hRdef]; exact multinomial_eq_finsupp _
  have hB2 : Nat.multinomial Finset.univ (fun i => a i / q) = B.multinomial := by
    rw [hBdef]; exact multinomial_eq_finsupp _
  rw [hA2, hR2, hB2]
  exact key.trans (mul_comm _ _)

end Commons.Combinatorics.Multinomial
