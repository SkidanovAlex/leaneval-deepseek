import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.Basic
import Submission.Work.NumberTheory.Chen.BTermCount.selberg_G_lower
import Submission.Commons.NumberTheory.Sieve.selberg_phi_lcm_diagonalization
import Submission.Commons.Data.Nat.moebiusInversionRoundTrip
import Submission.Commons.NumberTheory.PrimeReciprocals.prime_product_inc_le_log

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Optimal Selberg weights for the density `1/φ`

For a squarefree `P` and a level `D` we build the explicit optimal Selberg weight vector for the
`Λ²` sieve with density `ν d = 1/φ(d)` on the divisors of `P`, following the standard
construction (`y l = μ l / (w l · G)`, `λ d = φ d · Σ_{l : d ∣ l} μ(l/d) y l`, where
`w l = ∏_{p ∣ l}(p-2)` and `G = Σ_{l ≤ D, l ∣ P} 1/w l`).  The point is the exact evaluation
of the Selberg quadratic form `Σ_{d,e} λ_d λ_e / φ(lcm d e) = 1/G` and the uniform bound
`|λ d| ≤ ∏_{p ∣ d}(p-1)/(p-2) = O(log D)`.
-/

/-- The truncated divisor set `T = {d ≤ D : d ∣ P}`. -/
noncomputable def selbergT (D P : ℕ) : Finset ℕ :=
  (Finset.Icc 1 D).filter (fun d : ℕ => d ∣ P)

/-- `w l = ∏_{p ∣ l} (p - 2)`. -/
noncomputable def selbergWt (l : ℕ) : ℝ := ∏ p ∈ l.primeFactors, ((p : ℝ) - 2)

/-- The Selberg sum `G = Σ_{l ∈ T} 1 / w l`. -/
noncomputable def selbergG (D P : ℕ) : ℝ := ∑ l ∈ selbergT D P, 1 / selbergWt l

/-- The optimal `y`-coordinate `y l = μ l / (w l · G)` (zero above the level `D`). -/
noncomputable def selbergY (D P : ℕ) (l : ℕ) : ℝ :=
  if l ≤ D then (ArithmeticFunction.moebius l : ℝ) / selbergWt l / selbergG D P else 0

/-- The optimal Selberg weight `λ d = φ d · Σ_{l ∈ T, d ∣ l} μ(l/d) · y l`. -/
noncomputable def selbergLam (D P : ℕ) (d : ℕ) : ℝ :=
  if d ∈ selbergT D P then
    (Nat.totient d : ℝ) *
      ∑ l ∈ selbergT D P,
        (if d ∣ l then (ArithmeticFunction.moebius (l / d) : ℝ) * selbergY D P l else 0)
  else 0

/-- The Selberg quadratic form `Σ_{d,e ∈ T} λ d λ e / φ(lcm d e)`. -/
noncomputable def selbergForm (D P : ℕ) (lam : ℕ → ℝ) : ℝ :=
  ∑ d ∈ selbergT D P, ∑ e ∈ selbergT D P,
    lam d * lam e / (Nat.totient (Nat.lcm d e) : ℝ)

/-- The set `selbergT D P` unpacked. -/
theorem mem_selbergT {D P d : ℕ} :
    d ∈ selbergT D P ↔ 1 ≤ d ∧ d ≤ D ∧ d ∣ P := by
  rw [selbergT, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

/-- `1` always belongs to `selbergT D P` when `1 ≤ D`. -/
theorem one_mem_selbergT (D P : ℕ) (hD : 1 ≤ D) : (1 : ℕ) ∈ selbergT D P := by
  rw [mem_selbergT]; exact ⟨le_rfl, hD, one_dvd P⟩

/-- `selbergWt` is nonnegative. -/
theorem selbergWt_nonneg (l : ℕ) : 0 ≤ selbergWt l := by
  rw [selbergWt]
  refine Finset.prod_nonneg (fun p hp => ?_)
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  linarith

/-- The Selberg sum `G` is positive as soon as the level is at least `1`
(the term `l = 1` contributes `1`). -/
theorem selbergG_pos (D P : ℕ) (hD : 1 ≤ D) : 0 < selbergG D P := by
  have hmem := one_mem_selbergT D P hD
  have h1 : (0 : ℝ) < 1 / selbergWt 1 := by
    rw [selbergWt, Nat.primeFactors_one, Finset.prod_empty, div_one]; norm_num
  calc (0 : ℝ) < 1 / selbergWt 1 := h1
    _ ≤ selbergG D P := Finset.single_le_sum (fun i _ => by
          exact div_nonneg zero_le_one (selbergWt_nonneg i)) hmem

/-- Unfolding of `selbergY` below the level. -/
theorem selbergY_eq {D P l : ℕ} (hl : l ≤ D) :
    selbergY D P l = (ArithmeticFunction.moebius l : ℝ) / selbergWt l / selbergG D P := by
  rw [selbergY, if_pos hl]

/-- `selbergLam` vanishes off `selbergT`. -/
theorem selbergLam_support {D P d : ℕ} (hd : d ∉ selbergT D P) : selbergLam D P d = 0 := by
  rw [selbergLam, if_neg hd]

/-- The `d = 1` term of the Selberg weight vector is `1`. -/
theorem selbergLam_one (D P : ℕ) (hD : 1 ≤ D) (hPsq : Squarefree P) :
    selbergLam D P 1 = 1 := by
  have h1T := one_mem_selbergT D P hD
  rw [selbergLam, if_pos h1T, Nat.totient_one, Nat.cast_one, one_mul]
  have hterm : ∀ l ∈ selbergT D P,
      (if (1 : ℕ) ∣ l then (ArithmeticFunction.moebius (l / 1) : ℝ) * selbergY D P l else 0)
        = 1 / selbergWt l / selbergG D P := by
    intro l hl
    obtain ⟨-, hlD, hlP⟩ := mem_selbergT.mp hl
    rw [if_pos (one_dvd l), Nat.div_one, selbergY_eq hlD]
    have hsqZ := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hPsq.squarefree_of_dvd hlP)
    have hsq : (ArithmeticFunction.moebius l : ℝ) ^ 2 = 1 := by
      rw [← Int.cast_pow, hsqZ]; norm_num
    have : (ArithmeticFunction.moebius l : ℝ)
        * ((ArithmeticFunction.moebius l : ℝ) / selbergWt l / selbergG D P)
        = (ArithmeticFunction.moebius l : ℝ) ^ 2 / selbergWt l / selbergG D P := by ring
    rw [this, hsq]
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_div]
  rw [show (∑ l ∈ selbergT D P, 1 / selbergWt l) = selbergG D P from rfl]
  exact div_self (ne_of_gt (selbergG_pos D P hD))

end

end Work.NumberTheory.Chen.BTermCount
