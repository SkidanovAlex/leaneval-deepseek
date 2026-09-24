import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.SelbergWeights
import Submission.Work.NumberTheory.Chen.BTermCount.selbergLam_linv
import Submission.Work.NumberTheory.Chen.BTermCount.selbergLam_abs_le
import Submission.Work.NumberTheory.Chen.BTermCount.selberg_G_lower
import Submission.Work.NumberTheory.Chen.BTermCount.SelbergCommons

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# The Selberg weight vector: quadratic form and uniform bound

The weight vector `selbergLam D P` built in `SelbergWeights.lean` has Selberg quadratic form exactly
`1/G` (the diagonalisation `Commons.NumberTheory.Sieve.selberg_phi_lcm_diagonalization` together with
the Möbius inversion `selbergLam_linv`) and is uniformly bounded by `∏_{p ∣ d}(p-1)/(p-2)`.
Combined with `selberg_G_lower` (`G ≥ (1/4) log D`) this gives the weights needed by the `B`-term
sieve: quadratic form `≤ 4/log D`, uniform bound `O(log D)`.
-/

/-- `oddPrimLt Y` is squarefree. -/
theorem squarefree_oddPrimLt (Y : ℕ) : Squarefree (oddPrimLt Y) := by
  rw [oddPrimLt_eq_prod_oddLt]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (mem_oddLt'.mp hp).1.squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (mem_oddLt'.mp hp).1 (mem_oddLt'.mp hq).1).mpr hpq

/-- The prime factors of `oddPrimLt Y` are the odd primes below `Y`. -/
theorem primeFactors_oddPrimLt (Y : ℕ) : (oddPrimLt Y).primeFactors = oddLt Y := by
  rw [oddPrimLt_eq_prod_oddLt]
  exact Nat.primeFactors_prod (fun p hp => (mem_oddLt'.mp hp).1)

/-- `{d ≤ D : d ∣ P}` agrees with `P.divisors` truncated at `D` (for `P ≠ 0`). -/
theorem selbergT_eq_divisors (D P : ℕ) (hP : P ≠ 0) :
    selbergT D P = P.divisors.filter (fun l : ℕ => l ≤ D) := by
  ext l
  rw [mem_selbergT, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨-, h2, h3⟩
    exact ⟨⟨h3, hP⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨Nat.pos_of_dvd_of_pos h1 (Nat.pos_of_ne_zero hP), h2, h1⟩

/-- **The Selberg quadratic form of the optimal weights.**  It equals `1/G` exactly. -/
theorem selbergForm_eq (D P : ℕ) (hD : 1 ≤ D) (hPsq : Squarefree P) :
    selbergForm D P (selbergLam D P) = 1 / selbergG D P := by
  have hP0 : P ≠ 0 := hPsq.ne_zero
  have hGne : selbergG D P ≠ 0 := ne_of_gt (selbergG_pos D P hD)
  have hdiag :=
    Commons.NumberTheory.Sieve.selberg_phi_lcm_diagonalization P D
      (Nat.pos_of_ne_zero hP0) hPsq (selbergLam D P)
  rw [selbergForm, selbergT_eq_divisors D P hP0, hdiag]
  have hkey : ∀ l ∈ selbergT D P,
      (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) *
        (∑ d ∈ (selbergT D P).filter (fun d : ℕ => l ∣ d),
          selbergLam D P d / (Nat.totient d : ℝ)) ^ 2
      = (1 / selbergWt l) / (selbergG D P) ^ 2 := by
    intro l hl
    obtain ⟨-, hlD, hlP⟩ := mem_selbergT.mp hl
    rw [selbergLam_linv D P hD hPsq hl, selbergY_eq hlD]
    have hsqZ := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hPsq.squarefree_of_dvd hlP)
    have hsq : (ArithmeticFunction.moebius l : ℝ) ^ 2 = 1 := by
      rw [← Int.cast_pow, hsqZ]; norm_num
    simp only [selbergWt]
    have h1 : (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) *
        ((ArithmeticFunction.moebius l : ℝ)
          / (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) / selbergG D P) ^ 2
        = (ArithmeticFunction.moebius l : ℝ) ^ 2
          / (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) / (selbergG D P) ^ 2 := by
      by_cases hW : (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) = 0
      · rw [hW]; simp
      · field_simp
    rw [h1, hsq]
  rw [← selbergT_eq_divisors D P hP0]
  trans ∑ l ∈ selbergT D P, (1 / selbergWt l) / (selbergG D P) ^ 2
  · exact Finset.sum_congr rfl hkey
  · rw [← Finset.sum_div]
    rw [show (∑ l ∈ selbergT D P, 1 / selbergWt l) = selbergG D P from rfl]
    field_simp

/-- The Selberg sum of the odd primorial equals the expression in `selberg_G_lower`. -/
theorem selbergG_oddPrimLt (D Y : ℕ) :
    selbergG D (oddPrimLt Y)
      = ∑ l ∈ (Finset.Icc 1 D).filter (fun l : ℕ => l ∣ oddPrimLt Y),
          1 / (∏ p ∈ l.primeFactors, ((p : ℝ) - 2)) := rfl

/-- **Uniform bound for the optimal weights.** -/
theorem selbergLam_abs_bound (D P : ℕ) (hD : 2 ≤ D) (hPsq : Squarefree P)
    (hodd : ∀ p ∈ P.primeFactors, 3 ≤ p) {C : ℝ}
    (hC : ∀ d D' : ℕ, 2 ≤ D' → d ≤ D' →
      (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) / ((p : ℝ) - 2)))
        ≤ C * (1 + Real.log (D' : ℝ))) :
    ∀ d : ℕ, |selbergLam D P d| ≤ C * (1 + Real.log (D : ℝ)) := by
  intro d
  by_cases hd : d ∈ selbergT D P
  · refine le_trans (selbergLam_abs_le D P d (by omega) hPsq hodd hd) (hC d D hD ?_)
    exact (mem_selbergT.mp hd).2.1
  · rw [selbergLam_support hd, abs_zero]
    have h1 : (1 : ℝ) ≤ C * (1 + Real.log (D : ℝ)) := by
      simpa using hC 1 D hD (by omega)
    linarith

/-- **The Selberg weight vector at the odd primorial**: `λ 1 = 1`, supported on
`{d ≤ D : d ∣ oddPrimLt Y}`, uniformly bounded by `C (1 + log D)`, with quadratic form
at most `4/log D` for `D ≥ 2` and `D ≤ Y`. -/
theorem selbergWeights_spec (D Y : ℕ) (hD : 2 ≤ D) (hDY : D ≤ Y) {C : ℝ}
    (hC : ∀ d D' : ℕ, 2 ≤ D' → d ≤ D' →
      (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) / ((p : ℝ) - 2)))
        ≤ C * (1 + Real.log (D' : ℝ))) :
    ∃ lam : ℕ → ℝ, lam 1 = 1 ∧
      (∀ d : ℕ, d ∉ selbergT D (oddPrimLt Y) → lam d = 0) ∧
      (∀ d : ℕ, |lam d| ≤ C * (1 + Real.log (D : ℝ))) ∧
      selbergForm D (oddPrimLt Y) lam ≤ 4 / Real.log (D : ℝ) := by
  refine ⟨selbergLam D (oddPrimLt Y), ?_, ?_, ?_, ?_⟩
  · exact selbergLam_one D (oddPrimLt Y) (by omega) (squarefree_oddPrimLt Y)
  · intro d hd
    exact selbergLam_support hd
  · refine selbergLam_abs_bound D (oddPrimLt Y) hD (squarefree_oddPrimLt Y) ?_ hC
    intro p hp
    rw [primeFactors_oddPrimLt] at hp
    exact (mem_oddLt'.mp hp).2.1
  · rw [selbergForm_eq D (oddPrimLt Y) (by omega) (squarefree_oddPrimLt Y)]
    have hG := selberg_G_lower D Y hD hDY
    rw [selbergG_oddPrimLt]
    have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
    have h4 : (0 : ℝ) < (1 / 4 : ℝ) * Real.log (D : ℝ) := by positivity
    have hle := one_div_le_one_div_of_le h4 hG
    have heq : 1 / ((1 / 4 : ℝ) * Real.log (D : ℝ)) = 4 / Real.log (D : ℝ) := by
      field_simp
    linarith [hle, heq]

end

end Work.NumberTheory.Chen.BTermCount
