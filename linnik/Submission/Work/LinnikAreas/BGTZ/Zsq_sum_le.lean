import Mathlib
import Submission.Work.Sieve.Zfun_nonneg_le_Qfun
import Submission.Work.Sieve.gFun_theory
import Submission.Work.LinnikAreas.BGTZ.SelbergReindex

/-!
# `Σ_l Z_l² / g(l) ≤ Q(χ₁) · V(R)`

With `Z_l = Zfun χ₁ R l = Σ_{m | rad q, l m ≤ R} 1/g(m)` (`Work.Sieve.Zfun`) and
`Q(χ₁) = ∏_{p | q} (1 + 1/g(p))` (`Work.Sieve.Qfun`) we bound the weighted sum of the
squares `Z_l²` over the squarefree `l ≤ R` coprime to `q`.

The input is the two elementary facts about `Z` established in the workspace:
* `0 ≤ Z_l ≤ Q(χ₁)` (`Work.Sieve.Zfun_nonneg_le_Qfun`), and
* `Σ_{(l,q)=1, sqfree, l ≤ R} Z_l / g(l) ≤ V(R)` (`Zfun_sum_le_VFun`).

Then `Z_l² / g(l) = Z_l · (Z_l / g(l)) ≤ Q(χ₁) · (Z_l / g(l))` termwise (using `Z_l ≥ 0` and
`g(l) > 0` for squarefree `l`), and summing gives the result.
-/

open scoped BigOperators
open DirichletCharacter

namespace Work.LinnikAreas.BGTZ

theorem Zsq_sum_le {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (R : ℕ) :
    (∑ l ∈ (Finset.Icc 1 R).filter (fun l => Squarefree l ∧ Nat.Coprime l q),
        (Work.Sieve.Zfun χ₁ R l) ^ 2 / Work.LinnikAreas.Sieve.gFun χ₁ l)
      ≤ Work.Sieve.Qfun χ₁ * Work.LinnikAreas.Sieve.VFun χ₁ R := by
  classical
  obtain ⟨-, hgprime, -, -, hgpos, -, -⟩ := Work.Sieve.gFun_theory χ₁ hχ₁
  have hZle : ∀ l : ℕ, Work.Sieve.Zfun χ₁ R l ≤ Work.Sieve.Qfun χ₁ :=
    fun l => (Work.Sieve.Zfun_nonneg_le_Qfun χ₁ hχ₁ R l).2
  have hZnn : ∀ l : ℕ, 0 ≤ Work.Sieve.Zfun χ₁ R l :=
    fun l => (Work.Sieve.Zfun_nonneg_le_Qfun χ₁ hχ₁ R l).1
  have hQnn : 0 ≤ Work.Sieve.Qfun χ₁ := by
    unfold Work.Sieve.Qfun
    refine Finset.prod_nonneg (fun p hp => ?_)
    have h := hgprime p (Nat.prime_of_mem_primeFactors hp)
    have : 0 < (Work.LinnikAreas.Sieve.gPrime χ₁ p)⁻¹ := inv_pos.mpr h
    linarith
  set T : Finset ℕ := (Finset.Icc 1 R).filter (fun l => Squarefree l ∧ Nat.Coprime l q) with hT
  have hterm : ∀ l ∈ T,
      (Work.Sieve.Zfun χ₁ R l) ^ 2 / Work.LinnikAreas.Sieve.gFun χ₁ l
        ≤ Work.Sieve.Qfun χ₁
          * (1 / Work.LinnikAreas.Sieve.gFun χ₁ l * Work.Sieve.Zfun χ₁ R l) := by
    intro l hl
    rw [hT, Finset.mem_filter] at hl
    obtain ⟨-, hlsf, -⟩ := hl
    have hg : 0 < Work.LinnikAreas.Sieve.gFun χ₁ l := hgpos l hlsf
    have hmodel : (Work.Sieve.Zfun χ₁ R l) ^ 2 / Work.LinnikAreas.Sieve.gFun χ₁ l
        = Work.Sieve.Zfun χ₁ R l
          * (1 / Work.LinnikAreas.Sieve.gFun χ₁ l * Work.Sieve.Zfun χ₁ R l) := by
      ring
    rw [hmodel]
    exact mul_le_mul_of_nonneg_right (hZle l)
      (mul_nonneg (div_nonneg zero_le_one (le_of_lt hg)) (hZnn l))
  calc ∑ l ∈ T, (Work.Sieve.Zfun χ₁ R l) ^ 2 / Work.LinnikAreas.Sieve.gFun χ₁ l
      ≤ ∑ l ∈ T, Work.Sieve.Qfun χ₁
          * (1 / Work.LinnikAreas.Sieve.gFun χ₁ l * Work.Sieve.Zfun χ₁ R l) :=
        Finset.sum_le_sum hterm
    _ = Work.Sieve.Qfun χ₁
          * ∑ l ∈ T, (1 / Work.LinnikAreas.Sieve.gFun χ₁ l * Work.Sieve.Zfun χ₁ R l) := by
        rw [Finset.mul_sum]
    _ ≤ Work.Sieve.Qfun χ₁ * Work.LinnikAreas.Sieve.VFun χ₁ R := by
        refine mul_le_mul_of_nonneg_left ?_ hQnn
        have hT' : T = (Finset.Icc 1 R).filter (fun l => Nat.Coprime l q ∧ Squarefree l) := by
          rw [hT]
          exact Finset.filter_congr (fun l _ => and_comm)
        rw [hT']
        exact Zfun_sum_le_VFun χ₁ hχ₁ R

end Work.LinnikAreas.BGTZ
