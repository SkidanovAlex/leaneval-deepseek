import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.NumberTheory.BombieriVinogradov.lam4_dyadic_sum_bound

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

theorem mean_value_small_modulus_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q : ℕ, 2 ≤ x → Q ≤ 2 →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      ≤ C * (x : ℝ) := by
  classical
  refine ⟨3 * (Real.log 4 + 4), by positivity, ?_⟩
  intro x Q hx hQ
  have hx1 : 1 ≤ x := by omega
  set M : ℝ := Chebyshev.psi (x : ℝ) with hMdef
  have hMnn : 0 ≤ M := by rw [hMdef]; exact Chebyshev.psi_nonneg _
  have hMbound : M ≤ (Real.log 4 + 4) * (x : ℝ) := by
    rw [hMdef]; exact Chebyshev.psi_le_const_mul_self (by positivity)
  -- Step 1: pointwise bound of the inner norms
  have hpt : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ), y ≤ x →
      ‖∑ n ∈ Finset.Icc 1 y,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖ ≤ M := by
    intro q χ y hy
    have h1 : ‖∑ n ∈ Finset.Icc 1 y,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖
        ≤ ∑ n ∈ Finset.Icc 1 y,
            ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖ :=
      norm_sum_le _ _
    have h2 : ∑ n ∈ Finset.Icc 1 y,
            ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖
        ≤ ∑ n ∈ Finset.Icc 1 y, ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
        (DirichletCharacter.norm_le_one χ (n : ZMod q))
    have h3 : ∑ n ∈ Finset.Icc 1 y, ArithmeticFunction.vonMangoldt n
        ≤ ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hy)
        (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    have h4 : ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.vonMangoldt n
        ≤ ∑ n ∈ Finset.Icc 0 x, ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc (by norm_num : (0:ℕ) ≤ 1) le_rfl)
        (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    have h5 : (∑ n ∈ Finset.Icc 0 x, ArithmeticFunction.vonMangoldt n) = M := by
      rw [hMdef, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    exact le_trans h1 (le_trans h2 (le_trans h3 (le_trans h4 (le_of_eq h5))))
  -- Step 2: bound of the sSup
  have hsup : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x) ≤ M := by
    intro q χ
    apply csSup_le
    · exact ⟨_, ⟨1, ⟨le_rfl, hx1⟩, rfl⟩⟩
    · rintro b ⟨y, hy, rfl⟩
      exact hpt q χ y hy.2
  -- Step 3: number of primitive characters mod q is at most q.totient
  have hcard : ∀ q : ℕ, 1 ≤ q →
      (((Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ).card : ℕ) : ℝ)
        ≤ (q.totient : ℝ) := by
    intro q hq
    have hnez : NeZero q := ⟨by omega⟩
    have hle := Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ q))
        (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
    have hc : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    have : (Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ).card
        ≤ q.totient := le_trans hle (le_of_eq hc)
    exact_mod_cast this
  -- Step 4: per-modulus bound
  have hterm : ∀ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ,
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      ≤ (q : ℝ) * M := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
      have h : 0 < q.totient := Nat.totient_pos.mpr (by omega)
      exact_mod_cast h
    have hqnn : 0 ≤ (q : ℝ) / (q.totient : ℝ) := by positivity
    have hsum : (∑ χ ∈ Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ,
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
        ≤ (((Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ).card : ℕ) : ℝ) * M := by
      have := Finset.sum_le_card_nsmul
        (Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ)
        (fun χ => sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
        M (fun χ _ => hsup q χ)
      simpa [nsmul_eq_mul] using this
    have hcardq : (((Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ).card : ℕ) : ℝ)
        ≤ (q.totient : ℝ) := hcard q hq1
    calc ((q : ℝ) / (q.totient : ℝ)) *
          (∑ χ ∈ Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ,
            sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
        ≤ ((q : ℝ) / (q.totient : ℝ)) *
            ((((Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ).card : ℕ) : ℝ) * M) :=
          mul_le_mul_of_nonneg_left hsum hqnn
      _ ≤ ((q : ℝ) / (q.totient : ℝ)) * ((q.totient : ℝ) * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcardq hMnn) hqnn
      _ = (q : ℝ) * M := by
          rw [← mul_assoc, div_mul_cancel₀ (q : ℝ) (ne_of_gt hφpos)]
  -- Step 5: sum over q
  have hsumQ : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ,
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x)))
      ≤ ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * M := Finset.sum_le_sum hterm
  have hQs : (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)) ≤ 3 := by
    calc (∑ q ∈ Finset.Icc 1 Q, (q : ℝ))
        ≤ ∑ q ∈ (Finset.Icc 1 2 : Finset ℕ), (q : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hQ)
          intro i _ _; positivity
      _ = 3 := by norm_num [Finset.sum_Icc_succ_top]
  calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ,
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x)))
      ≤ ∑ q ∈ Finset.Icc 1 Q, (q : ℝ) * M := hsumQ
    _ = (∑ q ∈ Finset.Icc 1 Q, (q : ℝ)) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ 3 * M := mul_le_mul_of_nonneg_right hQs hMnn
    _ ≤ 3 * ((Real.log 4 + 4) * (x : ℝ)) :=
        mul_le_mul_of_nonneg_left hMbound (by norm_num)
    _ = 3 * (Real.log 4 + 4) * (x : ℝ) := by ring

end Commons.NumberTheory.BombieriVinogradov