import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.Holonomy3.defs

/-!
# The minimal-degree coefficient of the diagonal composition (STEP 2, algebraic part)

The auxiliary function `F = auxSeries f Q` is a multivariable power series over `ℚ`, and a
`d`-tuple of conformal maps defines univariate power series `Φ_s`.  The pullback of `F` is the
diagonal composition `diagComp Φ g`, and this module computes its minimal-degree coefficients:
if all coefficients of `g` of total degree `< |n|` vanish, then the `zⁿ`-coefficient of the
diagonal composition is `β_n · ∏_s (Φ_s.coeff 1)^{n_s}` — the cross terms are killed by the
minimality of the total degree of `n`.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open scoped BigOperators

/-! ## Part 8: the coefficient identity of STEP 2

The auxiliary function `F = auxSeries f Q` is a multivariable power series over `ℚ`, and the maps
`φ_k` define a univariate power series `Φ_s` (in the variable `z_s`).  The pullback `G` of STEP 2 is
the diagonal composition `diagComp Φ g`, multiplied by the fixed pole-clearing polynomial
`∏_s Q(z_s)`.  The content of this part is that the `zⁿ` coefficient of `G` is *exactly*
`β_n · Q(0)^d · ∏_s φ_{k(s)}'(0)^{n_s}`, because the cross terms are killed by the minimality of the
total degree of `n`. -/

/-- `coeff m (X^m * f) = coeff 0 f`. -/
theorem coeff_X_pow_mul_self {R : Type*} [Semiring R] (f : PowerSeries R) (m : ℕ) :
    PowerSeries.coeff m (PowerSeries.X ^ m * f) = PowerSeries.coeff 0 f := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : PowerSeries.X ^ (m + 1) * f = PowerSeries.X * (PowerSeries.X ^ m * f) := by
      rw [pow_succ', mul_assoc]
    rw [h1, PowerSeries.coeff_succ_X_mul, ih]

/-- For a power series vanishing at `0`, the `m`-th coefficient of its `m`-th power is the `m`-th
power of its first coefficient. -/
theorem coeff_pow_self (Φ : PowerSeries ℂ) (h0 : PowerSeries.coeff 0 Φ = 0) (m : ℕ) :
    PowerSeries.coeff m (Φ ^ m) = (PowerSeries.coeff 1 Φ) ^ m := by
  have hc0 : PowerSeries.constantCoeff Φ = 0 := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using h0
  have hshift : PowerSeries.X * PowerSeries.mk (fun k => PowerSeries.coeff (k + 1) Φ) = Φ := by
    ext k
    rcases k with _ | k
    · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_X, zero_mul,
        hc0]
    · rw [PowerSeries.coeff_succ_X_mul]
      simp [PowerSeries.coeff_mk]
  have hpow : Φ ^ m = PowerSeries.X ^ m * (PowerSeries.mk (fun k => PowerSeries.coeff (k + 1) Φ)) ^ m := by
    conv_lhs => rw [← hshift]
    rw [mul_pow]
  rw [hpow, coeff_X_pow_mul_self, PowerSeries.coeff_zero_eq_constantCoeff, map_pow]
  congr 1

/-- Two multi-indices with `m ≤ n` and equal total degree are equal. -/
lemma eq_of_le_of_degree_eq {d : ℕ} {m n : Fin d →₀ ℕ} (h : m ≤ n) (hd : m.degree = n.degree) :
    m = n := by
  have hadd : m + (n - m) = n := add_tsub_cancel_of_le h
  have hdeg : (n - m).degree = 0 := by
    have h1 : (m + (n - m)).degree = m.degree + (n - m).degree := map_add Finsupp.degree m (n - m)
    rw [hadd, hd] at h1
    omega
  have hsub : n - m = 0 := (Finsupp.degree_eq_zero_iff (n - m)).mp hdeg
  exact le_antisymm h (tsub_eq_zero_iff_le.mp hsub)

/-- The diagonal composition vanishes in all degrees below the order of `g`. -/
theorem diagComp_coeff_eq_zero {d : ℕ} (Φ : Fin d → PowerSeries ℂ) (g : MvPowerSeries (Fin d) ℂ)
    {ν : ℕ} (hg : ∀ m : Fin d →₀ ℕ, m.degree < ν → g.coeff m = 0)
    {n : Fin d →₀ ℕ} (hn : n.degree < ν) :
    (diagComp Φ g).coeff n = 0 := by
  refine Finset.sum_eq_zero (fun m hm => ?_)
  have hmn : m ≤ n := Finset.mem_Iic.mp hm
  have hdeg : m.degree ≤ n.degree := Finsupp.degree_mono hmn
  rw [hg m (lt_of_le_of_lt hdeg hn), zero_mul]

/-- **The coefficient identity of STEP 2.** If `n` is a minimal-degree exponent of `g` (all
coefficients of strictly smaller degree vanish) and every `Φ_s` vanishes at `0`, then the `n`-th
coefficient of the diagonal composition is `g.coeff n · ∏_s (φ_s'(0))^{n_s}`: the only surviving
term is `m = n`. -/
theorem diagComp_coeff_eq {d : ℕ} (Φ : Fin d → PowerSeries ℂ) (g : MvPowerSeries (Fin d) ℂ)
    {n : Fin d →₀ ℕ} (hg : ∀ m : Fin d →₀ ℕ, m.degree < n.degree → g.coeff m = 0)
    (hΦ : ∀ s, PowerSeries.coeff 0 (Φ s) = 0) :
    (diagComp Φ g).coeff n = g.coeff n * ∏ s, (PowerSeries.coeff 1 (Φ s)) ^ (n s) := by
  have hmain : (∑ m ∈ Finset.Iic n, g.coeff m * ∏ s, (Φ s ^ (m s)).coeff (n s))
      = g.coeff n * ∏ s, (Φ s ^ (n s)).coeff (n s) := by
    refine Finset.sum_eq_single n ?_ ?_
    · intro m hm hmn
      rw [Finset.mem_Iic] at hm
      have hlt : m.degree < n.degree := by
        rcases lt_or_eq_of_le (Finsupp.degree_mono hm) with h' | h'
        · exact h'
        · exact absurd (eq_of_le_of_degree_eq hm h') hmn
      rw [hg m hlt, zero_mul]
    · intro hn
      exact absurd (Finset.mem_Iic.mpr le_rfl) hn
  rw [show (diagComp Φ g).coeff n
      = ∑ m ∈ Finset.Iic n, g.coeff m * ∏ s, (Φ s ^ (m s)).coeff (n s) from rfl, hmain]
  congr 1
  exact Finset.prod_congr rfl (fun s _ => coeff_pow_self (Φ s) (hΦ s) (n s))

/-- Multiplying by a fixed series does not change the minimal-degree coefficient: if all
coefficients of `g` vanish below degree `ν` and `n` has degree `ν`, then the `n`-th coefficient of
`u * g` is `(coeff 0 u) · (coeff n g)`.  This is the second half of STEP 2: the pole-clearing factor
`∏_s Q(z_s)` contributes only its constant term `Q(0)^d`. -/
theorem coeff_mul_eq_of_min {d : ℕ} (u g : MvPowerSeries (Fin d) ℂ) {ν : ℕ}
    (hg : ∀ m : Fin d →₀ ℕ, m.degree < ν → g.coeff m = 0)
    {n : Fin d →₀ ℕ} (hn : n.degree = ν) :
    (u * g).coeff n = u.coeff 0 * g.coeff n := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_single (0, n) ?_ ?_
  · rintro ⟨a, b⟩ hp hne
    have hp' : a + b = n := by simpa using hp
    have ha : a ≠ 0 := by
      rintro rfl
      exact hne (by simp only [Prod.mk.injEq, true_and]; simpa using hp')
    have hadeg : 0 < a.degree := by
      rcases Nat.eq_zero_or_pos a.degree with h | h
      · exact absurd ((Finsupp.degree_eq_zero_iff a).mp h) ha
      · exact h
    have hb : b.degree < ν := by
      have h1 : (a + b).degree = a.degree + b.degree := map_add Finsupp.degree a b
      rw [hp', hn] at h1
      omega
    rw [hg b hb, mul_zero]
  · intro h
    exact absurd (by simp [Finset.mem_antidiagonal]) h

end Work.Holonomy3
