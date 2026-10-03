import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.hyperbolaBlockAux
import Submission.Work.FIArea7.exists_separating_function
import Submission.Work.FIArea7hyper.hyperbolaLogArith

/-!
# `Work.FIArea7.PairEllAux.hyperbolaStarEps`

The hyperbola (Type II) form of *FI* Proposition 23.1 for the **coprimality restricted** bilinear
form, in the `ε`-form of the corrected `Prop231`: `‖L*(M,N)‖ ≪ τ(c)(M+N)^{1/12} u^{11/12} log(u+2)²
(MN+c+2)^ε` for the sum restricted to `mn ≤ u`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea7.PairEllAux

open Finset MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The hyperbola (Type II) form of *FI* Proposition 23.1 in the corrected `ε`-form, for the
coprimality restricted bilinear form.**  From the rectangular bound `Prop231` (whose second half
bounds `LBilinStar`) derive the same bound for the sum restricted to the hyperbola `m·n ≤ u`, with
`(MN)^{11/12}` replaced by `u^{11/12}`, a polylogarithmic loss `log(u+2)²`, and the `ε`-power
evaluated at the *unreduced* ranges `M, N`.

`hblock` is the generic single-block lemma (`hyperbolaBlockLeGen`), kept as a hypothesis so that the
two lemmas are independent. -/
theorem hyperbolaStarEps
    (hblock : ∀ (h : ℝ → ℝ) (u : ℕ), 1 ≤ u →
      (∀ k : ℕ, 1 ≤ k → (∫ t : ℝ, (h t : ℂ) * (k : ℂ) ^ (t * Complex.I))
        = if (k : ℝ) ≤ (u : ℝ) then 1 else 0) →
      ∀ (Ma Ca : ℕ) (Q : ℕ → ℕ → ℂ) (α β : ℕ → ℂ) (B : ℝ), 0 ≤ B →
        (∀ t : ℝ, ‖∑ m ∈ Finset.Icc 1 Ma, ∑ n ∈ Finset.Icc 1 Ca,
          (α m * (m : ℂ) ^ (t * Complex.I)) * (β n * (n : ℂ) ^ (t * Complex.I)) * Q m n‖ ≤ B) →
        ‖∑ m ∈ Finset.Icc 1 Ma, ∑ n ∈ Finset.Icc 1 Ca,
          (if m * n ≤ u then α m * β n * Q m n else 0)‖ ≤ B * ∫ t : ℝ, |h t|)
    (h31 : Work.FIArea7.Prop231) :
    ∀ ε : ℝ, 0 < ε → ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (chi : GaussianInt → ℂ) (k : ℤ) (c0 M N u : ℕ) (α β : ℕ → ℂ),
        1 ≤ c0 → 1 ≤ M → 1 ≤ N →
        (∀ z, ‖chi z‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        (∀ m ∈ Finset.Icc 1 M, ‖α m‖ ≤ 1) → (∀ n ∈ Finset.Icc 1 N, ‖β n‖ ≤ 1) →
        ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ u then (if Nat.Coprime m n then α m * β n
              * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * m * n) else 0) else 0)‖
          ≤ C * (((c0.divisors.card : ℕ) : ℝ)) * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
              * ((u : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((u : ℝ) + 2)) ^ A
              * (((M : ℝ) * (N : ℝ) + (c0 : ℝ) + 2) ^ ε) := by
  intro ε hε
  obtain ⟨C1, hC1, hprop⟩ := h31 ε hε
  refine ⟨C1 * (2 ^ ((11 : ℝ) / 12) * 10), 2, ?_, by norm_num, ?_⟩
  · exact mul_pos hC1 (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num))
  intro chi k c0 M N u α β hc0 hM hN hchi hchi_mul hα hβ
  set τ : ℝ := ((c0.divisors.card : ℕ) : ℝ) with hτ
  have hτnn : 0 ≤ τ := by rw [hτ]; positivity
  have hlogSlnn : 0 ≤ Real.log ((u : ℝ) + 2) :=
    Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (u : ℝ) from Nat.cast_nonneg u])
  have hRHSnn : 0 ≤ C1 * (2 ^ ((11 : ℝ) / 12) * 10) * τ * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
      * ((u : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ)
      * (((M : ℝ) * (N : ℝ) + (c0 : ℝ) + 2) ^ ε) := by positivity
  by_cases hu0 : u = 0
  · have hS : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          (if m * n ≤ u then (if Nat.Coprime m n then α m * β n
            * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * m * n) else 0) else 0)) = 0 := by
      apply Finset.sum_eq_zero; intro m hm
      apply Finset.sum_eq_zero; intro n hn
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hmn : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      rw [hu0, if_neg (by omega : ¬ m * n ≤ 0)]
    rw [hS, norm_zero]
    exact hRHSnn
  have hu : 1 ≤ u := by omega
  have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  obtain ⟨h, hL1, hspec⟩ := Work.FIArea7.exists_separating_function (u : ℝ) huR
  have hLnn : 0 ≤ ∫ t : ℝ, |h t| := integral_nonneg (fun t => abs_nonneg _)
  set Q : ℕ → ℕ → ℂ := fun m n =>
    if Nat.Coprime m n then Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * m * n) else 0
    with hQ
  have hQapply : ∀ m n : ℕ, Q m n = if Nat.Coprime m n then
      Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * m * n) else 0 := by
    intro m n; rw [hQ]
  have hQform : ∀ m n : ℕ, (if Nat.Coprime m n then α m * β n
        * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * m * n) else 0)
      = α m * β n * Q m n := by
    intro m n
    rw [hQapply m n]
    by_cases hc : Nat.Coprime m n
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, mul_zero]
  rw [show (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        (if m * n ≤ u then (if Nat.Coprime m n then α m * β n
          * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c0 * m * n) else 0) else 0))
      = (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        (if m * n ≤ u then α m * β n * Q m n else 0)) from by
    apply Finset.sum_congr rfl; intro m hm
    apply Finset.sum_congr rfl; intro n hn
    by_cases hc : m * n ≤ u
    · rw [if_pos hc, if_pos hc, hQform m n]
    · rw [if_neg hc, if_neg hc]]
  set B : ℝ := C1 * τ * (((M : ℝ) + N) ^ ((1 : ℝ) / 12)) * ((2 * (u : ℝ)) ^ ((11 : ℝ) / 12))
      * (((M : ℝ) * (N : ℝ) + (c0 : ℝ) + 2) ^ ε) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    positivity
  rw [dyadic_partition M (fun m => ∑ n ∈ Finset.Icc 1 N,
        (if m * n ≤ u then α m * β n * Q m n else 0))]
  have hterm : ∀ a ∈ Finset.range (Nat.log 2 M + 1),
      ‖∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 N,
          (if m * n ≤ u then α m * β n * Q m n else 0)‖
        ≤ B * ∫ t : ℝ, |h t| := by
    intro a ha
    rw [Finset.mem_range] at ha
    rw [Work.FIArea7.hyperbola_block_rewrite a M N u α β Q]
    set αa : ℕ → ℂ := fun m => if 2 ^ a ≤ m then α m else 0 with hαa
    have hT : (∑ m ∈ Finset.Icc 1 (min (2 ^ (a + 1) - 1) M),
            ∑ n ∈ Finset.Icc 1 (min N (u / 2 ^ a)),
            (if m * n ≤ u then (if 2 ^ a ≤ m then α m else 0) * β n * Q m n else 0))
        = (∑ m ∈ Finset.Icc 1 (min (2 ^ (a + 1) - 1) M),
            ∑ n ∈ Finset.Icc 1 (min N (u / 2 ^ a)),
            (if m * n ≤ u then αa m * β n * Q m n else 0)) := by
      apply Finset.sum_congr rfl; intro m hm
      apply Finset.sum_congr rfl; intro n hn
      rw [hαa]
    rw [hT]
    set Ma : ℕ := min (2 ^ (a + 1) - 1) M with hMa
    set Ca : ℕ := min N (u / 2 ^ a) with hCa
    by_cases hC : 1 ≤ Ca
    · have hMa1 : 1 ≤ Ma := by
        rw [hMa]
        apply le_min
        · have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
          omega
        · exact hM
      have hMaCa : Ma * Ca ≤ 2 * u := by
        rw [hMa, hCa]
        have hMa2 : min (2 ^ (a + 1) - 1) M ≤ 2 ^ (a + 1) :=
          le_trans (min_le_left _ _) (Nat.sub_le _ _)
        have hCa2 : min N (u / 2 ^ a) * 2 ^ a ≤ u :=
          le_trans (Nat.mul_le_mul_right _ (min_le_right _ _)) (Nat.div_mul_le_self u (2 ^ a))
        calc (min (2 ^ (a + 1) - 1) M) * (min N (u / 2 ^ a))
            ≤ 2 ^ (a + 1) * (min N (u / 2 ^ a)) := Nat.mul_le_mul_right _ hMa2
          _ = 2 * (min N (u / 2 ^ a) * 2 ^ a) := by rw [Nat.pow_succ]; ring
          _ ≤ 2 * u := Nat.mul_le_mul_left _ hCa2
      have hB_a : ∀ t : ℝ, ‖∑ m ∈ Finset.Icc 1 Ma, ∑ n ∈ Finset.Icc 1 Ca,
            (αa m * (m : ℂ) ^ (t * Complex.I)) * (β n * (n : ℂ) ^ (t * Complex.I)) * Q m n‖
          ≤ C1 * τ * (((Ma : ℝ) + (Ca : ℝ)) ^ ((1 : ℝ) / 12))
              * (((Ma : ℝ) * (Ca : ℝ)) ^ ((11 : ℝ) / 12))
              * ((((Ma : ℝ) * (Ca : ℝ)) + (c0 : ℝ) + 2) ^ ε) := by
        intro t
        have hαb : ∀ m ∈ Finset.Icc 1 Ma,
            ‖αa m * (m : ℂ) ^ (t * Complex.I)‖ ≤ 1 := by
          intro m hm
          have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
          have hm2 : m ≤ Ma := (Finset.mem_Icc.mp hm).2
          rw [hαa]
          change ‖(if 2 ^ a ≤ m then α m else 0) * (m : ℂ) ^ (t * Complex.I)‖ ≤ 1
          rw [norm_mul, Work.FIArea7.norm_natCast_cpow_I m hm1 t, mul_one]
          by_cases h2a : 2 ^ a ≤ m
          · rw [if_pos h2a]
            exact hα m (Finset.mem_Icc.mpr ⟨hm1, le_trans hm2 (by rw [hMa]; exact min_le_right _ _)⟩)
          · rw [if_neg h2a]; simp
        have hβb : ∀ n ∈ Finset.Icc 1 Ca,
            ‖β n * (n : ℂ) ^ (t * Complex.I)‖ ≤ 1 := by
          intro n hn
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hn2 : n ≤ Ca := (Finset.mem_Icc.mp hn).2
          rw [norm_mul, Work.FIArea7.norm_natCast_cpow_I n hn1 t, mul_one]
          exact hβ n (Finset.mem_Icc.mpr ⟨hn1, le_trans hn2 (by rw [hCa]; exact min_le_left _ _)⟩)
        rw [show (∑ m ∈ Finset.Icc 1 Ma, ∑ n ∈ Finset.Icc 1 Ca,
              (αa m * (m : ℂ) ^ (t * Complex.I)) * (β n * (n : ℂ) ^ (t * Complex.I)) * Q m n)
            = Work.FIArea7.LBilinStar Ma Ca c0 (Work.FIArea7.grossenChar chi k)
                (fun m => αa m * (m : ℂ) ^ (t * Complex.I))
                (fun n => β n * (n : ℂ) ^ (t * Complex.I)) from by
          rw [Work.FIArea7.LBilinStar]
          apply Finset.sum_congr rfl; intro m hm
          apply Finset.sum_congr rfl; intro n hn
          rw [hQapply m n]
          by_cases hc : Nat.Coprime m n
          · rw [if_pos hc, if_pos hc]
          · rw [if_neg hc, if_neg hc, mul_zero]]
        have hbb := (hprop Ma Ca c0 1 k chi (fun m => αa m * (m : ℂ) ^ (t * Complex.I))
          (fun n => β n * (n : ℂ) ^ (t * Complex.I)) hc0 hMa1 hC (le_refl 1) hchi hchi_mul hαb hβb).2
        simp only [← hτ] at hbb ⊢
        exact hbb
      have hB_ann : 0 ≤ C1 * τ * (((Ma : ℝ) + (Ca : ℝ)) ^ ((1 : ℝ) / 12))
          * (((Ma : ℝ) * (Ca : ℝ)) ^ ((11 : ℝ) / 12))
          * ((((Ma : ℝ) * (Ca : ℝ)) + (c0 : ℝ) + 2) ^ ε) := by positivity
      have hbl := hblock h u hu hspec Ma Ca Q αa β _ hB_ann hB_a
      refine le_trans hbl (mul_le_mul_of_nonneg_right ?_ hLnn)
      have hSum : (Ma : ℝ) + (Ca : ℝ) ≤ (M : ℝ) + N := by
        have h1 : (Ma : ℝ) ≤ (M : ℝ) := by rw [hMa]; exact_mod_cast min_le_right (2 ^ (a + 1) - 1) M
        have h2 : (Ca : ℝ) ≤ (N : ℝ) := by rw [hCa]; exact_mod_cast min_le_left N (u / 2 ^ a)
        linarith
      have hA1le : ((Ma : ℝ) + (Ca : ℝ)) ^ ((1 : ℝ) / 12) ≤ ((M : ℝ) + N) ^ ((1 : ℝ) / 12) :=
        Real.rpow_le_rpow (by positivity) hSum (by norm_num)
      have hMaCaR : (Ma : ℝ) * (Ca : ℝ) ≤ 2 * (u : ℝ) := by
        have h' : ((Ma * Ca : ℕ) : ℝ) ≤ ((2 * u : ℕ) : ℝ) := by exact_mod_cast hMaCa
        push_cast at h'; exact h'
      have hA2le : ((Ma : ℝ) * (Ca : ℝ)) ^ ((11 : ℝ) / 12) ≤ (2 * (u : ℝ)) ^ ((11 : ℝ) / 12) :=
        Real.rpow_le_rpow (by positivity) hMaCaR (by norm_num)
      have hMaCaMN : (Ma : ℝ) * (Ca : ℝ) ≤ (M : ℝ) * (N : ℝ) := by
        apply mul_le_mul
        · rw [hMa]; exact_mod_cast min_le_right (2 ^ (a + 1) - 1) M
        · rw [hCa]; exact_mod_cast min_le_left N (u / 2 ^ a)
        · positivity
        · exact Nat.cast_nonneg M
      have hA3le : (((Ma : ℝ) * (Ca : ℝ)) + (c0 : ℝ) + 2) ^ ε
          ≤ (((M : ℝ) * (N : ℝ)) + (c0 : ℝ) + 2) ^ ε :=
        Real.rpow_le_rpow (by positivity) (by linarith) (le_of_lt hε)
      have hndP : 0 ≤ ((M : ℝ) + N) ^ ((1 : ℝ) / 12) := Real.rpow_nonneg (by positivity) _
      have hndA2 : 0 ≤ (2 * (u : ℝ)) ^ ((11 : ℝ) / 12) := Real.rpow_nonneg (by positivity) _
      have hndA3 : 0 ≤ (((M : ℝ) * (N : ℝ)) + (c0 : ℝ) + 2) ^ ε := Real.rpow_nonneg (by positivity) _
      have hndA3a : 0 ≤ (((Ma : ℝ) * (Ca : ℝ)) + (c0 : ℝ) + 2) ^ ε := Real.rpow_nonneg (by positivity) _
      calc C1 * τ * (((Ma : ℝ) + (Ca : ℝ)) ^ ((1 : ℝ) / 12))
            * (((Ma : ℝ) * (Ca : ℝ)) ^ ((11 : ℝ) / 12))
            * ((((Ma : ℝ) * (Ca : ℝ)) + (c0 : ℝ) + 2) ^ ε)
          ≤ C1 * τ * (((M : ℝ) + N) ^ ((1 : ℝ) / 12)) * ((2 * (u : ℝ)) ^ ((11 : ℝ) / 12))
            * ((((M : ℝ) * (N : ℝ)) + (c0 : ℝ) + 2) ^ ε) := by
            apply mul_le_mul
            · apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hA1le (mul_nonneg (le_of_lt hC1) hτnn)
              · exact hA2le
              · exact Real.rpow_nonneg (by positivity) _
              · exact mul_nonneg (mul_nonneg (le_of_lt hC1) hτnn) hndP
            · exact hA3le
            · exact hndA3a
            · exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC1) hτnn) hndP) hndA2
        _ = B := by rw [hBdef]
    · have hC0 : Ca = 0 := by
        rcases lt_or_ge Ca 1 with h1 | h1
        · exact Nat.lt_one_iff.mp h1
        · exact absurd h1 hC
      have hz : (∑ m ∈ Finset.Icc 1 Ma, ∑ n ∈ Finset.Icc 1 Ca,
            (if m * n ≤ u then αa m * β n * Q m n else 0)) = 0 := by
        rw [hC0]; simp
      rw [hz, norm_zero]
      exact mul_nonneg hBnn hLnn
  have hsum0 : (∑ a ∈ Finset.range (Nat.log 2 M + 1),
        ‖∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ u then α m * β n * Q m n else 0)‖)
      ≤ (Nat.log 2 u + 1) * (B * ∫ t : ℝ, |h t|) := by
    have hfilt : ∀ a ∈ Finset.range (Nat.log 2 M + 1),
        ¬ (1 ≤ min N (u / 2 ^ a)) →
          (∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ u then α m * β n * Q m n else 0)) = 0 := by
      intro a ha hnot
      have hC0 : min N (u / 2 ^ a) = 0 := by
        rcases lt_or_ge (min N (u / 2 ^ a)) 1 with h1 | h1
        · exact Nat.lt_one_iff.mp h1
        · exact absurd h1 hnot
      rw [Work.FIArea7.hyperbola_block_rewrite a M N u α β Q]
      simp [hC0]
    rw [(Finset.sum_subset (Finset.filter_subset _ _) (fun a ha hnotin => by
          have hna : ¬ (1 ≤ min N (u / 2 ^ a)) := by
            intro hcon
            exact hnotin (Finset.mem_filter.mpr ⟨ha, hcon⟩)
          rw [hfilt a ha hna, norm_zero])).symm]
    calc (∑ a ∈ (Finset.range (Nat.log 2 M + 1)).filter (fun a => 1 ≤ min N (u / 2 ^ a)),
            ‖∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 N,
                (if m * n ≤ u then α m * β n * Q m n else 0)‖)
        ≤ ∑ a ∈ (Finset.range (Nat.log 2 M + 1)).filter (fun a => 1 ≤ min N (u / 2 ^ a)),
            (B * ∫ t : ℝ, |h t|) :=
          Finset.sum_le_sum (fun a ha => hterm a (Finset.mem_filter.mp ha).1)
      _ = (((Finset.range (Nat.log 2 M + 1)).filter (fun a => 1 ≤ min N (u / 2 ^ a))).card : ℝ)
            * (B * ∫ t : ℝ, |h t|) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Nat.log 2 u + 1) * (B * ∫ t : ℝ, |h t|) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hBnn hLnn)
          exact_mod_cast Work.FIArea7.card_dyadic_blocks M N u
  have harith : ((Nat.log 2 u : ℝ) + 1) * Real.log (6 * (u : ℝ))
      ≤ 10 * (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Work.FIArea7hyper.hyperbolaLogArith u hu
  have h2u : (2 * (u : ℝ)) ^ ((11 : ℝ) / 12)
      = (2 : ℝ) ^ ((11 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have hfinal : (Nat.log 2 u + 1) * (B * ∫ t : ℝ, |h t|)
      ≤ (C1 * (2 ^ ((11 : ℝ) / 12) * 10)) * τ * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
          * ((u : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ)
          * (((M : ℝ) * (N : ℝ) + (c0 : ℝ) + 2) ^ ε) := by
    have hLle : (∫ t : ℝ, |h t|) ≤ Real.log (6 * (u : ℝ)) := le_of_lt hL1
    have hN1 : (0 : ℝ) ≤ (Nat.log 2 u : ℝ) + 1 := by positivity
    have hF : 0 ≤ C1 * τ * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
        * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12))
        * (((M : ℝ) * (N : ℝ) + (c0 : ℝ) + 2) ^ ε) := by positivity
    have hstep1 : (Nat.log 2 u + 1) * (B * ∫ t : ℝ, |h t|)
        ≤ (Nat.log 2 u + 1) * (B * Real.log (6 * (u : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLle hBnn) hN1
    refine le_trans hstep1 ?_
    have key : (Nat.log 2 u + 1) * (B * Real.log (6 * (u : ℝ)))
        = (C1 * τ * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
            * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12))
            * (((M : ℝ) * (N : ℝ) + (c0 : ℝ) + 2) ^ ε))
          * (((Nat.log 2 u : ℝ) + 1) * Real.log (6 * (u : ℝ))) := by
      rw [hBdef, h2u]; ring
    rw [key]
    calc (C1 * τ * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
            * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12))
            * (((M : ℝ) * (N : ℝ) + (c0 : ℝ) + 2) ^ ε))
          * (((Nat.log 2 u : ℝ) + 1) * Real.log (6 * (u : ℝ)))
        ≤ (C1 * τ * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
            * ((2 : ℝ) ^ ((11 : ℝ) / 12) * (u : ℝ) ^ ((11 : ℝ) / 12))
            * (((M : ℝ) * (N : ℝ) + (c0 : ℝ) + 2) ^ ε))
          * (10 * (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ)) :=
          mul_le_mul_of_nonneg_left harith hF
      _ = (C1 * (2 ^ ((11 : ℝ) / 12) * 10)) * τ * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
            * ((u : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ)
            * (((M : ℝ) * (N : ℝ) + (c0 : ℝ) + 2) ^ ε) := by ring
  calc ‖∑ a ∈ Finset.range (Nat.log 2 M + 1),
          ∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ u then α m * β n * Q m n else 0)‖
      ≤ ∑ a ∈ Finset.range (Nat.log 2 M + 1),
          ‖∑ m ∈ Finset.Icc (2 ^ a) (min (2 ^ (a + 1) - 1) M), ∑ n ∈ Finset.Icc 1 N,
            (if m * n ≤ u then α m * β n * Q m n else 0)‖ := norm_sum_le _ _
    _ ≤ (Nat.log 2 u + 1) * (B * ∫ t : ℝ, |h t|) := hsum0
    _ ≤ (C1 * (2 ^ ((11 : ℝ) / 12) * 10)) * τ * (((M : ℝ) + N) ^ ((1 : ℝ) / 12))
          * ((u : ℝ) ^ ((11 : ℝ) / 12)) * (Real.log ((u : ℝ) + 2)) ^ (2 : ℝ)
          * (((M : ℝ) * (N : ℝ) + (c0 : ℝ) + 2) ^ ε) := hfinal

end

end Work.FIArea7.PairEllAux
