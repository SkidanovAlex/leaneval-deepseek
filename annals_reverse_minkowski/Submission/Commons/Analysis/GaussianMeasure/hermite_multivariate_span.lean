import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Submission.Commons.Analysis.GaussianMeasure.hermite_span_polynomials

open Polynomial MvPolynomial
open scoped BigOperators

noncomputable section

namespace Commons.Analysis.GaussianMeasure

private def hermR (n : ℕ) : Polynomial ℝ := (Polynomial.hermite n).map (Int.castRingHom ℝ)

private def hermTerm {m : ℕ} (i : Fin m) (k : ℕ) : MvPolynomial (Fin m) ℝ :=
  Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) (hermR k)

private def hermMulti {m : ℕ} (α : Fin m → ℕ) : MvPolynomial (Fin m) ℝ :=
  ∏ i, hermTerm i (α i)

private def xpow {m : ℕ} (e : Fin m → ℕ) : MvPolynomial (Fin m) ℝ :=
  ∏ i, (MvPolynomial.X i) ^ (e i)

private lemma aeval_hermR_real (a : ℝ) (k : ℕ) :
    Polynomial.aeval a (hermR k) = Polynomial.aeval a (Polynomial.hermite k) := by
  rw [hermR]
  exact (Polynomial.aeval_eq_aeval_map (R := ℤ) (T := ℝ)
    (Subsingleton.elim _ _) (Polynomial.hermite k) a).symm

private lemma prod_univ_sum_pi {ι κ M : Type*} [DecidableEq ι] [Fintype ι] [Fintype κ]
    [CommSemiring M] (F : ι → κ → M) : ∏ i, ∑ k, F i k = ∑ s : ι → κ, ∏ i, F i (s i) :=
  Fintype.prod_sum F

private lemma prod_mem_span_range {ι κ A : Type*} [DecidableEq ι] [Fintype ι] [Fintype κ]
    [CommSemiring A] [Algebra ℝ A] (g : ι → κ → A) (f : ι → A)
    (h : ∀ i, f i ∈ Submodule.span ℝ (Set.range (g i))) :
    ∏ i, f i ∈ Submodule.span ℝ (Set.range (fun s : ι → κ => ∏ i, g i (s i))) := by
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp (h i)
  have hff : ∏ i, f i = ∏ i, ∑ k, c i k • g i k := by
    apply Finset.prod_congr rfl
    intro i _
    exact (hc i).symm
  rw [hff, prod_univ_sum_pi]
  apply Submodule.sum_mem
  intro s _
  have hmem : ∏ i, g i (s i) ∈ Submodule.span ℝ (Set.range (fun s : ι → κ => ∏ i, g i (s i))) :=
    Submodule.subset_span ⟨s, rfl⟩
  have hfac : ∏ i, c i (s i) • g i (s i) = (∏ i, c i (s i)) • ∏ i, g i (s i) := by
    rw [Finset.prod_congr rfl (fun i _ => Algebra.smul_def (c i (s i)) (g i (s i))),
      Finset.prod_mul_distrib, ← map_prod, ← Algebra.smul_def]
  rw [hfac]
  exact Submodule.smul_mem _ (∏ i, c i (s i)) hmem

private lemma X_pow_mem_span {m d : ℕ} (i : Fin m) (n : ℕ) (hn : n ≤ d) :
    (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) ^ n ∈
      Submodule.span ℝ (Set.range (fun k : Fin (d + 1) => hermTerm i (k : ℕ))) := by
  have hX : (Polynomial.X : Polynomial ℝ) ^ n ∈
      Submodule.span ℝ (Set.range (fun k : Fin (d + 1) => hermR (k : ℕ))) := by
    simp only [hermR]
    rw [hermite_span_polynomials d]
    exact Submodule.subset_span ⟨⟨n, Nat.lt_succ_of_le hn⟩, rfl⟩
  have hle : Submodule.span ℝ (Set.range (fun k : Fin (d + 1) => hermR (k : ℕ))) ≤
      Submodule.comap
        (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin m) ℝ)).toLinearMap
        (Submodule.span ℝ (Set.range (fun k : Fin (d + 1) => hermTerm i (k : ℕ)))) := by
    rw [Submodule.span_le]
    rintro y ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  have hmem := hle hX
  rw [Submodule.mem_comap] at hmem
  change Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin m) ℝ)
    ((Polynomial.X : Polynomial ℝ) ^ n) ∈
      Submodule.span ℝ (Set.range (fun k : Fin (d + 1) => hermTerm i (k : ℕ))) at hmem
  rw [map_pow, Polynomial.aeval_X] at hmem
  exact hmem

private lemma xpow_mem_span {m d : ℕ} (e : Fin m → ℕ) (he : ∀ i, e i ≤ d) :
    xpow e ∈ Submodule.span ℝ
      (Set.range (fun α : Fin m → Fin (d + 1) => hermMulti (fun i => (α i : ℕ)))) := by
  have hfac : ∀ i : Fin m, (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) ^ (e i) ∈
      Submodule.span ℝ (Set.range (fun k : Fin (d + 1) => hermTerm i (k : ℕ))) :=
    fun i => X_pow_mem_span i (e i) (he i)
  have h := prod_mem_span_range (fun i (k : Fin (d + 1)) => hermTerm i (k : ℕ))
      (fun i => (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) ^ (e i)) hfac
  have hset : Set.range (fun s : Fin m → Fin (d + 1) => ∏ i, hermTerm i (s i))
      = Set.range (fun α : Fin m → Fin (d + 1) => hermMulti (fun i => (α i : ℕ))) := by
    simp only [hermMulti]
  rw [hset] at h
  simpa [xpow] using h


private lemma monomial_eq_xpow {m : ℕ} (v : Fin m →₀ ℕ) :
    MvPolynomial.monomial v (1 : ℝ) = xpow (fun i => v i) := by
  rw [xpow, ← Finset.prod_subset (Finset.subset_univ v.support)
      (fun i _ hi => by rw [Finsupp.mem_support_iff, ne_eq, not_not] at hi; rw [hi, pow_zero]),
    MvPolynomial.prod_X_pow_eq_monomial]

private lemma mem_span_of_totalDegree_le {m d : ℕ} (q : MvPolynomial (Fin m) ℝ)
    (hq : q.totalDegree ≤ d) :
    q ∈ Submodule.span ℝ
      (Set.range (fun α : Fin m → Fin (d + 1) => hermMulti (fun i => (α i : ℕ)))) := by
  rw [MvPolynomial.as_sum q]
  apply Submodule.sum_mem
  intro v hv
  have hdv : v.sum (fun _ k => k) ≤ d := le_trans (MvPolynomial.le_totalDegree hv) hq
  have hle : ∀ i, v i ≤ d := by
    intro i
    refine le_trans ?_ hdv
    rw [Finsupp.sum_fintype]
    · exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    · intro j
      rfl
  have heq : MvPolynomial.monomial v (q.coeff v) = (q.coeff v) • xpow (fun i => v i) := by
    rw [← monomial_eq_xpow, MvPolynomial.smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]
  rw [heq]
  exact Submodule.smul_mem _ (q.coeff v) (xpow_mem_span (fun i => v i) hle)

private lemma eval_aeval_X {m : ℕ} (x : Fin m → ℝ) (i : Fin m) (p : Polynomial ℝ) :
    MvPolynomial.eval x
        (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) p)
      = Polynomial.aeval (x i) p := by
  have h := Polynomial.aeval_algHom_apply (R := ℝ) (MvPolynomial.aeval x)
    (MvPolynomial.X i : MvPolynomial (Fin m) ℝ) p
  rw [MvPolynomial.aeval_X] at h
  simpa using h.symm

theorem hermite_multivariate_span {m d : ℕ} (p : (Fin m → ℝ) → ℝ)
    (hp : ∃ q : MvPolynomial (Fin m) ℝ, (∀ x, q.eval x = p x) ∧ q.totalDegree ≤ d) :
    ∃ c : (Fin m → Fin (d + 1)) → ℝ,
      ∀ x : Fin m → ℝ, p x = ∑ α, c α * ∏ i,
        Polynomial.aeval (x i) (Polynomial.hermite ((α i : Fin (d + 1)) : ℕ)) := by
  obtain ⟨q, hqp, hqd⟩ := hp
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp
    (mem_span_of_totalDegree_le q hqd)
  refine ⟨c, fun x => ?_⟩
  have key : MvPolynomial.eval x q =
      ∑ α, c α * ∏ i, Polynomial.aeval (x i) (Polynomial.hermite ((α i : Fin (d + 1)) : ℕ)) := by
    rw [← hc, map_sum]
    apply Finset.sum_congr rfl
    intro α _
    rw [MvPolynomial.smul_eval, hermMulti, MvPolynomial.eval_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [hermTerm, eval_aeval_X, aeval_hermR_real]
  rw [← hqp x]
  exact key

end Commons.Analysis.GaussianMeasure