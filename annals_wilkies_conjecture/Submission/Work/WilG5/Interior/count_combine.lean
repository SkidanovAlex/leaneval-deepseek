/-
  WilG5 / Interior — `count_combine`.

  The counting step of the interior charts: the number `b.eval ![D + K, 1]` of charts coming from
  `SharpCD` multiplied by the sum over the cell components `c j` evaluated on the controlled curve
  `(↑(cD.eval (D + K)), ↑r, ↑nn, s)` is dominated by a *single* polynomial in the three variables
  `(D, r, s)` with nonnegative coefficients.

  The two ingredients are the already established crude domination lemmas:

  * `b_shift_bound` below (the shift `D + K` absorbed into the constant of `Count.dominateNat`);
  * `Work.WilG5.Count.dominate` — each component `c j` at the curve `(↑(cD.eval (D + K)), ↑r, ↑nn, s)`,
    where the shift `D + K` is handled by composing `cD` with `Polynomial.X + Polynomial.C K`.

  The two bounds multiply: the polynomial with nonnegative coefficients is `pb * ∑ j, pc j`, and at
  `(D, r, s)` its value is `pb.eval · ∑ j, (pc j).eval` — the product of the two dominating values.
  The `0 ≤ s` hypothesis makes every argument nonnegative, which is what makes the evaluation of a
  product the product of the evaluations (no sign flip occurs).
-/
import Mathlib
import Submission.Work.WilG5.PolyEval.poly_abs_bound
import Submission.Work.WilG5.PolyEval.nat_poly_bound
import Submission.Work.WilG5.Count.dominate

namespace Work.WilG5.Interior

/-- The `SharpCD` factor `(b.eval ![D + K, 1] : ℝ)` is bounded by a polynomial in `(D, r, s)` all
of whose coefficients are nonnegative.

This is `Work.WilG5.Count.dominateNat` with the shift `K` absorbed into the constant: the crude
growth bound `nat_poly_bound` applied to `b` at `x = ![D + K, 1]` reads
`(b.eval x : ℝ) ≤ A * (1 + (D + K) + 1)^N = A * (D + K + 2)^N`, and the value of
`C A * (X 0 + C (K + 2))^N` at `(D, r, s)` is exactly `A * (D + K + 2)^N`.  The witness is the
image under `Nat.castRingHom ℝ` of a `ℕ`-coefficient polynomial, so its coefficients are
nonnegative outright. -/
private theorem b_shift_bound (b : MvPolynomial (Fin 2) ℕ) (K : ℕ) :
    ∃ p : MvPolynomial (Fin 3) ℝ, (∀ t ∈ p.support, 0 ≤ p.coeff t) ∧
      ∀ (D r : ℕ) (s : ℝ), 0 ≤ s →
        (b.eval ![D + K, 1] : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), s] p := by
  obtain ⟨A, N, hA, hbound⟩ := Work.WilG5.PolyEval.nat_poly_bound b
  obtain ⟨M, hM⟩ := exists_nat_ge A
  refine ⟨MvPolynomial.map (Nat.castRingHom ℝ)
    (MvPolynomial.C M * (MvPolynomial.X (0 : Fin 3) + MvPolynomial.C (K + 2)) ^ N), ?_, ?_⟩
  · intro m _
    rw [MvPolynomial.coeff_map]
    exact Nat.cast_nonneg _
  · intro D r s _
    have hb := hbound ![D + K, 1]
    have hsum : (∑ i : Fin 2, ((![D + K, 1] i : ℕ) : ℝ)) = (D : ℝ) + (K : ℝ) + 1 := by
      simp [Fin.sum_univ_two]
    rw [hsum] at hb
    have h1 : (1 : ℝ) + ((D : ℝ) + (K : ℝ) + 1) = (D : ℝ) + (K : ℝ) + 2 := by ring
    rw [h1] at hb
    have heval : MvPolynomial.eval ![(D : ℝ), (r : ℝ), s]
        (MvPolynomial.map (Nat.castRingHom ℝ)
          (MvPolynomial.C M * (MvPolynomial.X (0 : Fin 3) + MvPolynomial.C (K + 2)) ^ N)) =
        (M : ℝ) * ((D : ℝ) + (K : ℝ) + 2) ^ N := by
      rw [MvPolynomial.eval_map]
      simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
        MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Nat.coe_castRingHom]
      push_cast
      ring
    rw [heval]
    calc (b.eval ![D + K, 1] : ℝ) ≤ A * ((D : ℝ) + (K : ℝ) + 2) ^ N := hb
      _ ≤ (M : ℝ) * ((D : ℝ) + (K : ℝ) + 2) ^ N :=
          mul_le_mul_of_nonneg_right hM (by positivity)

theorem count_combine {m : ℕ} (c : Fin m → MvPolynomial (Fin 4) ℝ) (b : MvPolynomial (Fin 2) ℕ)
    (cD : Polynomial ℕ) (K nn : ℕ) :
    ∃ p : MvPolynomial (Fin 3) ℝ, (∀ t ∈ p.support, 0 ≤ p.coeff t) ∧
      ∀ (D r : ℕ) (s : ℝ), 0 ≤ s →
        (b.eval ![D + K, 1] : ℝ) *
          (∑ j : Fin m, |(c j).eval ![(↑(cD.eval (D + K)) : ℝ), (r : ℝ), (nn : ℝ), s]|)
          ≤ p.eval ![(D : ℝ), (r : ℝ), s] := by
  classical
  obtain ⟨pb, hpb_mem, hpb⟩ := b_shift_bound b K
  -- each component `c j`, with the shift `D + K` absorbed into `cD`
  have key : ∀ j : Fin m, ∃ p : MvPolynomial (Fin 3) ℝ,
      (∀ t ∈ p.support, 0 ≤ p.coeff t) ∧
      ∀ (D r : ℕ) (s : ℝ), 0 ≤ s →
        |(c j).eval ![(↑(cD.eval (D + K)) : ℝ), (r : ℝ), (nn : ℝ), s]| ≤
          MvPolynomial.eval ![(D : ℝ), (r : ℝ), s] p := by
    intro j
    obtain ⟨p, hmem, hp⟩ :=
      Work.WilG5.Count.dominate (c j) (cD.comp (Polynomial.X + Polynomial.C K)) 1 0 0 nn
    refine ⟨p, hmem, fun D r s hs => ?_⟩
    have h := hp D r s hs
    simpa [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X] using h
  choose pc hpc_mem hpc using key
  -- coefficients outside the support vanish, so "nonnegative on the support" is "nonnegative"
  have hpb_all : ∀ t, 0 ≤ pb.coeff t := fun t => by
    by_cases h : t ∈ pb.support
    · exact hpb_mem t h
    · rw [MvPolynomial.notMem_support_iff.mp h]
  have hpc_all : ∀ (j : Fin m) (t : Fin 3 →₀ ℕ), 0 ≤ (pc j).coeff t := fun j t => by
    by_cases h : t ∈ (pc j).support
    · exact hpc_mem j t h
    · rw [MvPolynomial.notMem_support_iff.mp h]
  refine ⟨pb * ∑ j, pc j, ?_, ?_⟩
  · intro t _
    rw [MvPolynomial.coeff_mul]
    refine Finset.sum_nonneg fun u _ => mul_nonneg (hpb_all u.1) ?_
    rw [MvPolynomial.coeff_sum]
    exact Finset.sum_nonneg fun j _ => hpc_all j u.2
  · intro D r s hs
    have h1 : (b.eval ![D + K, 1] : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), s] pb :=
      hpb D r s hs
    have h2 : (∑ j : Fin m, |(c j).eval ![(↑(cD.eval (D + K)) : ℝ), (r : ℝ), (nn : ℝ), s]|)
        ≤ ∑ j : Fin m, MvPolynomial.eval ![(D : ℝ), (r : ℝ), s] (pc j) :=
      Finset.sum_le_sum fun j _ => hpc j D r s hs
    have heval : MvPolynomial.eval ![(D : ℝ), (r : ℝ), s] (pb * ∑ j, pc j)
        = MvPolynomial.eval ![(D : ℝ), (r : ℝ), s] pb *
          (∑ j : Fin m, MvPolynomial.eval ![(D : ℝ), (r : ℝ), s] (pc j)) := by
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_sum]
    rw [heval]
    exact mul_le_mul h1 h2 (Finset.sum_nonneg fun j _ => abs_nonneg _)
      (le_trans (Nat.cast_nonneg _) h1)

end Work.WilG5.Interior
