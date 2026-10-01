/-
# Area 4 / HB §11 — diagonalization of the Selberg quadratic form `selQ`

The Selberg quadratic form `selQ z = Σ_{d,e ≤ z} λ_d λ_e / lcm(d,e)` (with the Selberg weights
`λ_d = μ(d) log(z/d)`) is diagonalized into squares indexed by the "coprime to `k`" Mertens sums
`selTheta (z/k) k`:

  `selQ z = Σ_{k ≤ z} (μ(k)² φ(k) / k²) · selTheta (z/k) k²`.

This is the classical Selberg identity: writing `1/lcm(d,e) = gcd(d,e)/(de)` and
`gcd(d,e) = Σ_{l ∣ d, l ∣ e} φ(l)` and exchanging the order of summation one gets
`selQ z = Σ_{l ≤ z} φ(l) (Σ_{l ∣ d ≤ z} λ_d/d)²`, and the inner sum reindexes as
`d = l·m`, where `μ(l·m) = μ(l)μ(m)` on coprime `m` and `= 0` otherwise, which is exactly
`(μ(l)/l)·selTheta (z/l) l`.

The two reindexing steps are proved in the companion files
`selLam_div_sum_reindex.lean` and `moebius_mul_sum_eq_moebius_mul_selTheta.lean`; the
diagonalization `1/lcm = gcd` is the specialization of
`Commons.NumberTheory.Sieve.sum_gcd_rpow_diagonalization` to `σ = 1`, `c = φ`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.selLam_div_sum_reindex
import Submission.Work.LinnikAreas.Density4.moebius_mul_sum_eq_moebius_mul_selTheta
import Submission.Commons.NumberTheory.Sieve.selberg_diagonalization_sigma

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Finset

noncomputable section

/-- **Step (A) of the Selberg diagonalization of `selQ`.**  The Selberg quadratic form
`selQ z = Σ_{d,e ≤ z} λ_d λ_e / lcm(d,e)` diagonalizes as
`Σ_{l ≤ z} φ(l) (Σ_{l ∣ d ≤ z} λ_d / d)²`.  This is the classical identity
`1/lcm(d,e) = gcd(d,e)/(de) = Σ_{l ∣ d, l ∣ e} φ(l)/(de)` followed by an exchange of summation. -/
lemma selQ_eq_sum_totient_inner (z : ℕ) :
    selQ z = ∑ l ∈ Finset.Icc 1 z, (Nat.totient l : ℝ) *
      (∑ d ∈ (Finset.Icc 1 z).filter (fun d => l ∣ d), selLam z d / (d : ℝ)) ^ 2 := by
  have hTpos : ∀ d ∈ Finset.Icc 1 z, 0 < d := by
    intro d hd
    have := (Finset.mem_Icc.mp hd).1
    omega
  have hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ Finset.Icc 1 z → l ∈ Finset.Icc 1 z := by
    intro l d hld hd
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hd
    have hdpos : 0 < d := by omega
    have hlpos : 0 < l := Nat.pos_of_dvd_of_pos hld hdpos
    exact Finset.mem_Icc.mpr ⟨by omega, le_trans (Nat.le_of_dvd hdpos hld) h2⟩
  have hc : ∀ n ∈ Finset.Icc 1 z, (∑ δ ∈ n.divisors, (Nat.totient δ : ℝ)) = (n : ℝ) ^ (1:ℝ) := by
    intro n _
    rw [← Nat.cast_sum, Nat.sum_totient, Real.rpow_one]
  have hQ : selQ z = ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
      (selLam z d / (d : ℝ)) * (selLam z e / (e : ℝ)) * ((Nat.gcd d e : ℝ) ^ (1:ℝ)) := by
    unfold selQ
    apply Finset.sum_congr rfl; intro d hd
    apply Finset.sum_congr rfl; intro e he
    rw [Commons.NumberTheory.Sieve.lcm_term (selLam z) (hTpos d hd).ne' (hTpos e he).ne',
      Real.rpow_one]
  rw [hQ, Commons.NumberTheory.Sieve.sum_gcd_rpow_diagonalization (Finset.Icc 1 z) hTpos
    hTclosed (1:ℝ) (fun δ => (Nat.totient δ : ℝ)) hc (fun d => selLam z d / (d : ℝ))]

/-- **The Selberg diagonalization in the shape of HB's bookkeeping.**  The Selberg quadratic form
`selQ z` equals `Σ_{k ≤ z} (μ(k)² φ(k)/k²) · selTheta (z/k) k²`, i.e. the weighted sum of the
squares of the "coprime" Mertens sums `selTheta`. -/
theorem selberg_Q_eq_sum_theta (z : ℕ) :
    Work.LinnikAreas.Density4.selQ z
      = ∑ k ∈ Finset.Icc 1 z,
          (((ArithmeticFunction.moebius k : ℝ)^2 * (Nat.totient k : ℝ)) / ((k:ℝ)^2)) *
            Work.LinnikAreas.Density4.selTheta ((z:ℝ)/k) k ^ 2 := by
  rw [selQ_eq_sum_totient_inner z]
  apply Finset.sum_congr rfl
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
  have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkpos
  rw [selLam_div_sum_reindex z k hk1, moebius_mul_sum_eq_moebius_mul_selTheta z k hk1]
  field_simp

end

end Work.LinnikAreas.Density4
