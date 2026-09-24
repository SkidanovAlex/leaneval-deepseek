import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.dyadic_bilinear_char_large_sieve

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

noncomputable section

open Classical

/-- The bilinear character sum factors as the product of two linear character sums. -/
lemma bilinear_char_factor (q M N : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (a b : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, a m * b n * χ (((m * n : ℕ)) : ZMod q))
      = (∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q)) *
        (∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q)) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  have hcast : (((m * n : ℕ)) : ZMod q) = (m : ZMod q) * (n : ZMod q) := by
    push_cast; ring
  rw [hcast, map_mul]
  ring

/-- Weighted Cauchy–Schwarz with square roots: `∑ w √X √Y ≤ √(∑ w X) √(∑ w Y)`. -/
lemma sqrt_weighted_cs {ι : Type*} (s : Finset ι) (w X Y : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) :
    ∑ i ∈ s, w i * (Real.sqrt (X i) * Real.sqrt (Y i)) ≤
      Real.sqrt (∑ i ∈ s, w i * X i) * Real.sqrt (∑ i ∈ s, w i * Y i) := by
  have key := weighted_cs s w (fun i => Real.sqrt (X i)) (fun i => Real.sqrt (Y i)) hw
  have hFX : (∑ i ∈ s, w i * (Real.sqrt (X i)) ^ 2) = ∑ i ∈ s, w i * X i :=
    Finset.sum_congr rfl (fun i _ => by rw [Real.sq_sqrt (hX i)])
  have hFY : (∑ i ∈ s, w i * (Real.sqrt (Y i)) ^ 2) = ∑ i ∈ s, w i * Y i :=
    Finset.sum_congr rfl (fun i _ => by rw [Real.sq_sqrt (hY i)])
  have hL : (∑ i ∈ s, w i * Real.sqrt (X i) * Real.sqrt (Y i)) =
      ∑ i ∈ s, w i * (Real.sqrt (X i) * Real.sqrt (Y i)) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [hFX, hFY] at key
  rw [← hL]
  exact key

open Classical in
lemma bilinear_char_large_sieve (Q M N : ℕ) (hQ : 1 ≤ Q) (a b : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            a m * b n * χ (((m * n : ℕ)) : ZMod q)‖)
      ≤ Real.sqrt ((M + Q ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
        Real.sqrt ((N + Q ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by
  classical
  set A : (q : ℕ) → DirichletCharacter ℂ q → ℂ :=
    fun q χ => ∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q) with hA
  set B : (q : ℕ) → DirichletCharacter ℂ q → ℂ :=
    fun q χ => ∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q) with hB
  set S : (q : ℕ) → Finset (DirichletCharacter ℂ q) :=
    fun q => (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)
    with hS
  set X : ℕ → ℝ := fun q => ∑ χ ∈ S q, ‖A q χ‖ ^ 2 with hX
  set Y : ℕ → ℝ := fun q => ∑ χ ∈ S q, ‖B q χ‖ ^ 2 with hY
  have hSqdef : ∀ q, S q =
      (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive) :=
    fun q => rfl
  -- Step A: factor each inner double sum
  have hfac : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ S q,
      (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        a m * b n * χ (((m * n : ℕ)) : ZMod q)) = A q χ * B q χ := by
    intro q hq χ hχ
    have hq' : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    haveI : NeZero q := ⟨by omega⟩
    show (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        a m * b n * χ (((m * n : ℕ)) : ZMod q)) = _ * _
    rw [hA, hB]
    exact bilinear_char_factor q M N χ a b
  -- Step B: rewrite the LHS in terms of `A`, `B`, `S`
  have hLHS : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            a m * b n * χ (((m * n : ℕ)) : ZMod q)‖)
      = ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ S q, ‖A q χ‖ * ‖B q χ‖ := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    congr 1
    refine Finset.sum_congr ?_ (fun χ hχ => ?_)
    · simp only [hSqdef q]
    · rw [hfac q hq χ hχ, norm_mul]
  -- Step C: Cauchy–Schwarz in χ at each q
  have hbound : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ S q, ‖A q χ‖ * ‖B q χ‖)
      ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          (Real.sqrt (X q) * Real.sqrt (Y q)) := by
    refine Finset.sum_le_sum (fun q hq => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have h := Real.sum_mul_le_sqrt_mul_sqrt (S q) (fun χ => ‖A q χ‖) (fun χ => ‖B q χ‖)
    have hXq : X q = ∑ χ ∈ S q, ‖A q χ‖ ^ 2 := by simp only [hX]
    have hYq : Y q = ∑ χ ∈ S q, ‖B q χ‖ ^ 2 := by simp only [hY]
    rw [hXq, hYq]
    exact h
  -- Step D: Cauchy–Schwarz in q
  have hCS : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          (Real.sqrt (X q) * Real.sqrt (Y q)))
      ≤ Real.sqrt (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * X q) *
        Real.sqrt (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * Y q) := by
    refine sqrt_weighted_cs _ _ X Y (fun q _ => ?_) (fun q => ?_) (fun q => ?_)
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · simp only [hX]; exact Finset.sum_nonneg (fun χ _ => by positivity)
    · simp only [hY]; exact Finset.sum_nonneg (fun χ _ => by positivity)
  -- Step E: linear large sieve
  have hXB : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * X q)
      ≤ (M + Q ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2 := by
    have heq : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * X q) =
        ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ‖∑ m ∈ Finset.Icc 1 M, a m * χ (m : ZMod q)‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun q hq => ?_)
      congr 1
    rw [heq]
    exact char_large_sieve Q M hQ a
  have hYB : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * Y q)
      ≤ (N + Q ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
    have heq : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * Y q) =
        ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Icc 1 N, b n * χ (n : ZMod q)‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun q hq => ?_)
      congr 1
    rw [heq]
    exact char_large_sieve Q N hQ b
  calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            a m * b n * χ (((m * n : ℕ)) : ZMod q)‖)
      = ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ S q, ‖A q χ‖ * ‖B q χ‖ := hLHS
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          (Real.sqrt (X q) * Real.sqrt (Y q)) := hbound
    _ ≤ Real.sqrt (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * X q) *
        Real.sqrt (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) * Y q) := hCS
    _ ≤ Real.sqrt ((M + Q ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
        Real.sqrt ((N + Q ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt hXB) (Real.sqrt_le_sqrt hYB)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end

end Commons.NumberTheory.BombieriVinogradov
