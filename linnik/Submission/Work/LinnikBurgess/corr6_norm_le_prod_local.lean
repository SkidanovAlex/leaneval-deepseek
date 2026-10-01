import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Commons.NumberTheory.DirichletCharacter.split_sum6
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation_global_sharp_aux
-- The CRT step for the double-critical predicate (requested together with the correlation bound);
-- it is proved in its own module and re-exported here.
import Submission.Work.LinnikBurgess.DLd_prod_of_DLp

/-!
# CRT factorisation of the cubic character correlation over the prime powers of `q`

This file proves `Work.LinnikBurgess.corr6_norm_le_prod_local`: for a primitive Dirichlet
character `χ` of modulus `q`, the cubic correlation

`∑_{x : ZMod q} χ (∏_{l : Fin 3} (x + a_l)) * conj (χ (∏_{l : Fin 3} (x + b_l)))`

is bounded in norm by `∏_{p | q} B p (q.factorization p)`, provided at every prime power `p^e`
the analogous correlation for a primitive character mod `p^e` is bounded by `B p e`.

The proof is a strong induction on `q`, mirroring the pattern of
`Commons.NumberTheory.DirichletCharacter.charCorrelation_global_sharp_aux`:

* if `q = p^e` is a prime power, the hypothesis `hloc` applies directly;
* if `q = 1` the triangle inequality and `‖χ ·‖ ≤ 1` give the bound `1`;
* otherwise `q = u * v` with `1 < u`, `1 < v` coprime (`exists_coprime_factorization`),
  `split_sum6` factors the correlation as the product of the correlations of the CRT components
  `factorLeft χ`, `factorRight χ`, which are primitive by `primitive_factor_coprime`, and the
  induction hypothesis applies to both factors.

The product `∏_{p | q} B p (v_p(q))` multiplies over the coprime factorisation through
`Nat.primeFactors_mul` and `Nat.factorization_mul`.

This module also re-exports the companion CRT step for the double-critical predicate,
`Work.LinnikBurgess.DLd_prod_of_DLp` (from
`Submission.Work.LinnikBurgess.DLd_prod_of_DLp`): if `DLp p (s p) a b` holds for every prime `p`
of a finite set `P`, then `DLd (∏ p ∈ P, p ^ s p) a b` holds, the witnesses being combined by the
Chinese remainder theorem.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

open Commons.NumberTheory.DirichletCharacter

/-! ### Arithmetic of the weight `∏_{p | q} B p (q.factorization p)` -/

/-- For a prime power `p ^ e` (`e ≥ 1`) the weight has a single term. -/
lemma prod_primeFactors_primePow (B : ℕ → ℕ → ℝ) {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (∏ r ∈ (p ^ e).primeFactors, B r ((p ^ e).factorization r)) = B p e := by
  have he0 : e ≠ 0 := by omega
  rw [Nat.primeFactors_pow p he0, hp.primeFactors, Finset.prod_singleton,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]

/-- The weight is multiplicative over a coprime factorisation. -/
lemma prod_primeFactors_mul (B : ℕ → ℕ → ℝ) {u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : u.Coprime v) :
    (∏ r ∈ (u * v).primeFactors, B r ((u * v).factorization r))
      = (∏ r ∈ u.primeFactors, B r (u.factorization r))
        * (∏ r ∈ v.primeFactors, B r (v.factorization r)) := by
  rw [Nat.primeFactors_mul hu hv, Finset.prod_union ((Nat.disjoint_primeFactors hu hv).mpr h)]
  congr 1
  · refine Finset.prod_congr rfl (fun r hr => ?_)
    rw [Nat.factorization_mul hu hv, Finsupp.add_apply]
    have hr0 : v.factorization r = 0 := by
      rw [Nat.factorization_eq_zero_of_not_dvd]
      intro hdvd
      have hrp : r.Prime := (Nat.mem_primeFactors.mp hr).1
      exact hrp.ne_one (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (Nat.mem_primeFactors.mp hr).2.1 h) hdvd)
    rw [hr0, add_zero]
  · refine Finset.prod_congr rfl (fun r hr => ?_)
    rw [Nat.factorization_mul hu hv, Finsupp.add_apply]
    have hr0 : u.factorization r = 0 := by
      rw [Nat.factorization_eq_zero_of_not_dvd]
      intro hdvd
      have hrp : r.Prime := (Nat.mem_primeFactors.mp hr).1
      exact hrp.ne_one (Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (Nat.mem_primeFactors.mp hr).2.1 h.symm) hdvd)
    rw [hr0, zero_add]

/-! ### The global bound by strong induction -/

/-- The correlation with the triple product written as an explicit product of three linear
factors, expanded form, summed over `ZMod n`. -/
noncomputable def corr6Expanded (n : ℕ) [NeZero n] (a b : Fin 3 → ℕ)
    (χ : DirichletCharacter ℂ n) : ℂ :=
  ∑ x : ZMod n, χ ((x + (a 0 : ZMod n)) * (x + (a 1 : ZMod n)) * (x + (a 2 : ZMod n))) *
    (starRingEnd ℂ) (χ ((x + (b 0 : ZMod n)) * (x + (b 1 : ZMod n)) * (x + (b 2 : ZMod n))))

/-- Global bound, all moduli, by strong induction on the modulus. -/
lemma corr6Expanded_le_prod_primeFactors (a b : Fin 3 → ℕ) (B : ℕ → ℕ → ℝ)
    (hB : ∀ p e, 0 ≤ B p e)
    (hloc : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 1 ≤ e → ∀ χ : DirichletCharacter ℂ (p ^ e),
      χ.IsPrimitive →
      ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖ ≤ B p e) :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ‖corr6Expanded q a b χ‖ ≤ ∏ p ∈ q.primeFactors, B p (q.factorization p) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq χ hχ
    by_cases hpp : IsPrimePow q
    · -- prime power case
      obtain ⟨p, e, hp, he, hq_eq⟩ := (isPrimePow_nat_iff q).mp hpp
      subst hq_eq
      have hfac : Fact p.Prime := ⟨hp⟩
      have hconv : (∑ x : ZMod (p ^ e),
            χ ((x + (a 0 : ZMod (p ^ e))) * (x + (a 1 : ZMod (p ^ e))) * (x + (a 2 : ZMod (p ^ e)))) *
              (starRingEnd ℂ)
                (χ ((x + (b 0 : ZMod (p ^ e))) * (x + (b 1 : ZMod (p ^ e))) *
                  (x + (b 2 : ZMod (p ^ e))))))
          = ∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
              * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e))))) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Fin.prod_univ_three (fun l : Fin 3 => (x + (a l : ZMod (p ^ e)))),
          Fin.prod_univ_three (fun l : Fin 3 => (x + (b l : ZMod (p ^ e))))]
      rw [corr6Expanded, hconv]
      exact (hloc p e he χ hχ).trans (le_of_eq (prod_primeFactors_primePow B hp he).symm)
    · by_cases hq1 : q = 1
      · -- the modulus is `1`
        subst hq1
        have hnorm : ‖corr6Expanded 1 a b χ‖ ≤ 1 := by
          rw [corr6Expanded,
            Fintype.sum_subsingleton
              (fun x : ZMod 1 => χ ((x + (a 0 : ZMod 1)) * (x + (a 1 : ZMod 1)) * (x + (a 2 : ZMod 1))) *
                (starRingEnd ℂ) (χ ((x + (b 0 : ZMod 1)) * (x + (b 1 : ZMod 1)) * (x + (b 2 : ZMod 1)))))
              (0 : ZMod 1)]
          have h2 := DirichletCharacter.norm_le_one χ
            ((0 + (a 0 : ZMod 1)) * (0 + (a 1 : ZMod 1)) * (0 + (a 2 : ZMod 1)))
          have h3 := DirichletCharacter.norm_le_one χ
            ((0 + (b 0 : ZMod 1)) * (0 + (b 1 : ZMod 1)) * (0 + (b 2 : ZMod 1)))
          rw [norm_mul, Complex.norm_conj]
          nlinarith [norm_nonneg (χ ((0 + (a 0 : ZMod 1)) * (0 + (a 1 : ZMod 1)) * (0 + (a 2 : ZMod 1)))),
            norm_nonneg (χ ((0 + (b 0 : ZMod 1)) * (0 + (b 1 : ZMod 1)) * (0 + (b 2 : ZMod 1))))]
        refine hnorm.trans (le_of_eq ?_)
        simp [Nat.primeFactors_one]
      · -- general case: `q = u * v` with `u`, `v > 1` coprime
        have hq0 : q ≠ 0 := NeZero.ne q
        have hq2 : 2 ≤ q := by omega
        obtain ⟨u, v, hu1, hv1, huv, huv_eq⟩ := exists_coprime_factorization hq2 hpp
        subst huv_eq
        have hu0 : u ≠ 0 := by omega
        have hv0 : v ≠ 0 := by omega
        have huNZ : NeZero u := ⟨hu0⟩
        have hvNZ : NeZero v := ⟨hv0⟩
        have hu_lt : u < u * v := by nlinarith [hv1]
        have hv_lt : v < u * v := by nlinarith [hu1]
        have hχu : (factorLeft huv χ).IsPrimitive := factorLeft_isPrimitive huv χ hχ
        have hχv : (factorRight huv χ).IsPrimitive := factorRight_isPrimitive huv χ hχ
        have hIu := ih u hu_lt (factorLeft huv χ) hχu
        have hIv := ih v hv_lt (factorRight huv χ) hχv
        rw [corr6Expanded, split_sum6 huv χ (a 0) (a 1) (a 2) (b 0) (b 1) (b 2), norm_mul]
        refine (mul_le_mul hIu hIv (norm_nonneg _)
          (Finset.prod_nonneg (fun r _ => hB r (u.factorization r)))).trans (le_of_eq ?_)
        exact (prod_primeFactors_mul B hu0 hv0 huv).symm

/-! ### The requested lemma -/

/-- **U10 (part 1) — CRT factorisation of the correlation over the prime powers of `q`**
(`BURGESS_ROUTE_LEAD.md` §4.1).  If at every prime power `p^e` the correlation sum is bounded by
`B p e` (uniformly in the primitive character mod `p^e`), then for a primitive `χ` mod `q` the
correlation mod `q` is bounded by `∏_{p | q} B p (q.factorization p)`.

A reviewer confirmed the claim.  The pattern is `charCorrelation_global_sharp_aux` / `split_sum6` /
the `primitive_factor_coprime` machinery: `ZMod q ≃ ∏_{p^e ‖ q} ZMod (p^e)`, the character factors
as a product of its primitive components (`chi_eq_factors`, `factorLeft`/`factorRight`, both
primitive), and the summand splits into a product; the empty product handles `q = 1`.  Needed in the
final assembly U13.  (Note `hB` is not needed by the claim itself.) -/
theorem corr6_norm_le_prod_local (a b : Fin 3 → ℕ) (B : ℕ → ℕ → ℝ) (hB : ∀ p e, 0 ≤ B p e)
    (hloc : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 1 ≤ e → ∀ χ : DirichletCharacter ℂ (p ^ e),
      χ.IsPrimitive →
      ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖ ≤ B p e)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖∑ x : ZMod q, χ (∏ l : Fin 3, (x + (a l : ZMod q)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod q))))‖
      ≤ ∏ p ∈ q.primeFactors, B p (q.factorization p) := by
  have hconv : (∑ x : ZMod q, χ (∏ l : Fin 3, (x + (a l : ZMod q)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod q)))))
      = corr6Expanded q a b χ := by
    rw [corr6Expanded]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Fin.prod_univ_three (fun l : Fin 3 => (x + (a l : ZMod q))),
      Fin.prod_univ_three (fun l : Fin 3 => (x + (b l : ZMod q)))]
  rw [hconv]
  exact corr6Expanded_le_prod_primeFactors a b B hB hloc q χ hχ

end Work.LinnikBurgess
