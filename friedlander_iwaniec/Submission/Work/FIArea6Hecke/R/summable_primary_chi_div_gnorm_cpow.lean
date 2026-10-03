import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea5.S16Hecke.thetaHol_bound_of_summable
import Submission.Work.FIArea5.S16Hecke.thetaSph_eq_tsum_heckeLam
import Submission.Work.FIArea5.S16Hecke.primaryAux

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-!
# Absolute convergence of the primary-twisted series `Σ_z χ(z) |z|^{-2s}`

This file proves that for `re s > 1` the series
`Σ_{z primary} χ(z) / |z|^{2s}`
is absolutely convergent, for any coefficient function `χ` with `‖χ‖ ≤ 1`.  This is the elementary
analytic fact underlying the convergence of the Hecke `L`-series near `re s > 1`.

The lattice `ℤ[i] ≃ ℤ × ℤ` is separated by grouping the summand by its norm: on the primary coset
`|z|² ≥ 1`, and the count of lattice points of norm `≤ N` is `O(N)`, which is exactly the
convergence threshold `re s > 1`.
-/

/-- **A separable upper bound.**  For reals `a, b` and `σ > 0`,
`(1 + a² + b²)^{-σ} ≤ (1 + a²)^{-σ/2} (1 + b²)^{-σ/2}`,
because `(1 + a²)(1 + b²) ≤ (1 + a² + b²)²`. -/
private lemma one_add_sq_add_sq_rpow_neg_le (a b : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (1 + (a ^ 2 + b ^ 2)) ^ (-σ)
      ≤ (1 + a ^ 2) ^ (-(σ / 2)) * (1 + b ^ 2) ^ (-(σ / 2)) := by
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  have hpos1 : 0 < 1 + a ^ 2 := by linarith
  have hpos2 : 0 < 1 + b ^ 2 := by linarith
  have hpos : 0 < (1 + a ^ 2) * (1 + b ^ 2) := mul_pos hpos1 hpos2
  have hpos3 : 0 < 1 + (a ^ 2 + b ^ 2) := by linarith
  have hsq : (1 + a ^ 2) * (1 + b ^ 2) ≤ (1 + (a ^ 2 + b ^ 2)) ^ 2 := by
    nlinarith [ha, hb]
  have hexp : -(σ / 2) ≤ 0 := by linarith
  have key : (1 + (a ^ 2 + b ^ 2)) ^ (2 * (σ / 2)) = ((1 + (a ^ 2 + b ^ 2)) ^ 2) ^ (σ / 2) := by
    rw [Real.rpow_mul (le_of_lt hpos3) 2 (σ / 2), Real.rpow_two]
  have key2 : (1 + (a ^ 2 + b ^ 2)) ^ (-σ) = ((1 + (a ^ 2 + b ^ 2)) ^ 2) ^ (-(σ / 2)) := by
    rw [show (-σ) = -(2 * (σ / 2)) by ring, Real.rpow_neg (le_of_lt hpos3), key,
      Real.rpow_neg (le_of_lt (pow_pos hpos3 2))]
  calc (1 + (a ^ 2 + b ^ 2)) ^ (-σ)
      = ((1 + (a ^ 2 + b ^ 2)) ^ 2) ^ (-(σ / 2)) := key2
    _ ≤ ((1 + a ^ 2) * (1 + b ^ 2)) ^ (-(σ / 2)) :=
        Real.rpow_le_rpow_of_nonpos hpos hsq hexp
    _ = (1 + a ^ 2) ^ (-(σ / 2)) * (1 + b ^ 2) ^ (-(σ / 2)) :=
        Real.mul_rpow (le_of_lt hpos1) (le_of_lt hpos2)

/-- **One-dimensional comparison series.**  `Σ_{n ∈ ℤ} (1 + n²)^{-r}` converges for `r > 1/2`.
(Equivalently, `Σ_n |n|^{-2r}` converges for `2r > 1`.) -/
lemma summable_int_one_add_sq_rpow_neg {r : ℝ} (hr : 1 / 2 < r) :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ (-r)) := by
  have h0r : (0 : ℝ) < r := by linarith
  have h2r : (1 : ℝ) < 2 * r := by linarith
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (2 * r))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr h2r
  have hbase2 : Summable (fun n : ℕ => (((n : ℝ) ^ 2) ^ r)⁻¹) := by
    refine hbase.congr (fun n => ?_)
    rw [Real.rpow_mul (Nat.cast_nonneg n) 2 r, Real.rpow_two]
  have hcomp : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2) ^ r)⁻¹) :=
    hbase2.comp_injective (i := fun n : ℕ => n + 1)
      (fun a b h => by have h' : a + 1 = b + 1 := h; omega)
  have hshift : Summable (fun n : ℕ => (1 + ((n + 1 : ℕ) : ℝ) ^ 2) ^ (-r)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hcomp
    have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hpos2 : 0 < (((n + 1 : ℕ) : ℝ)) ^ 2 := by positivity
    have hle : (((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 + (((n + 1 : ℕ) : ℝ)) ^ 2 := by linarith
    have hstep0 : (1 + ((n + 1 : ℕ) : ℝ) ^ 2) ^ (-r) ≤ ((((n + 1 : ℕ) : ℝ)) ^ 2) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos hpos2 hle (by linarith)
    simpa only [Real.rpow_neg (le_of_lt hpos2)] using hstep0
  have hpos : Summable (fun n : ℕ => (1 + (n : ℝ) ^ 2) ^ (-r)) :=
    (summable_nat_add_iff 1).mp (by simpa using hshift)
  have hneg : Summable (fun n : ℕ => (1 + (-(n : ℝ)) ^ 2) ^ (-r)) := by
    simpa using hpos
  exact Summable.of_nat_of_neg (by simpa using hpos) (by simpa using hneg)

/-- **The two-dimensional lattice majorant.**  `Σ_{z ∈ ℤ[i]} (1 + |z|²)^{-σ}` converges for
`σ > 1`.  The summand is dominated by the product `(1+x²)^{-σ/2}(1+y²)^{-σ/2}` of the
one-dimensional series of `summable_int_one_add_sq_rpow_neg`. -/
lemma summable_one_add_gnorm_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun z : GaussianInt => (1 + (Work.FIPlan.gnorm z : ℝ)) ^ (-σ)) := by
  have hσpos : (0 : ℝ) < σ := by linarith
  have hσ2 : (1 : ℝ) / 2 < σ / 2 := by linarith
  have hφ : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ (-(σ / 2))) :=
    summable_int_one_add_sq_rpow_neg hσ2
  have hφnn : ∀ n : ℤ, 0 ≤ (1 + (n : ℝ) ^ 2) ^ (-(σ / 2)) := fun n => by positivity
  have hprod : Summable (fun p : ℤ × ℤ =>
      (1 + (p.1 : ℝ) ^ 2) ^ (-(σ / 2)) * (1 + (p.2 : ℝ) ^ 2) ^ (-(σ / 2))) :=
    Summable.mul_of_nonneg hφ hφ hφnn hφnn
  rw [Work.FIArea5.S16Hecke.summable_gaussian_iff]
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hprod
  obtain ⟨a, b⟩ := p
  rw [Work.FIArea5.S16Hecke.gnorm_mk_cast]
  exact one_add_sq_add_sq_rpow_neg_le (a : ℝ) (b : ℝ) hσpos

/-- **The lattice sum of `|z|^{-2σ}` converges for `σ > 1`.**  Compared with
`summable_one_add_gnorm_rpow_neg` through `|z|² ≤ 1 + |z|²` and `1 + |z|² ≤ 2|z|²` on `z ≠ 0`. -/
lemma summable_gnorm_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun z : GaussianInt => (Work.FIPlan.gnorm z : ℝ) ^ (-σ)) := by
  have hG : Summable (fun z : GaussianInt => (1 + (Work.FIPlan.gnorm z : ℝ)) ^ (-σ)) :=
    summable_one_add_gnorm_rpow_neg hσ
  have hG' : Summable (fun z : GaussianInt =>
      2 ^ σ * (1 + (Work.FIPlan.gnorm z : ℝ)) ^ (-σ)) := hG.mul_left _
  refine Summable.of_nonneg_of_le (fun z => ?_) (fun z => ?_) hG'
  · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · rcases eq_or_lt_of_le (Nat.zero_le (Work.FIPlan.gnorm z)) with h | h
    · have hz0 : (Work.FIPlan.gnorm z : ℝ) = 0 := by rw [← h]; norm_num
      rw [hz0, Real.zero_rpow (by linarith : (-σ) ≠ 0)]
      have h1 : (0 : ℝ) < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num) σ
      have h2 : (0 : ℝ) < (1 + (0 : ℝ)) ^ (-σ) := Real.rpow_pos_of_pos (by norm_num) (-σ)
      exact le_of_lt (mul_pos h1 h2)
    · have hg1 : (1 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by exact_mod_cast h
      have hgpos : (0 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith
      have hbase : (1 + (Work.FIPlan.gnorm z : ℝ)) ≤ 2 * (Work.FIPlan.gnorm z : ℝ) := by
        linarith
      have hkey : (2 * (Work.FIPlan.gnorm z : ℝ)) ^ (-σ)
          ≤ (1 + (Work.FIPlan.gnorm z : ℝ)) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hbase (by linarith)
      have h2pow : (2 : ℝ) ^ σ * (2 : ℝ) ^ (-σ) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      calc (Work.FIPlan.gnorm z : ℝ) ^ (-σ)
          = (2 ^ σ * 2 ^ (-σ)) * (Work.FIPlan.gnorm z : ℝ) ^ (-σ) := by
              rw [h2pow, one_mul]
        _ = 2 ^ σ * ((2 * (Work.FIPlan.gnorm z : ℝ)) ^ (-σ)) := by
              rw [Real.mul_rpow (by norm_num) (le_of_lt hgpos)]; ring
        _ ≤ 2 ^ σ * (1 + (Work.FIPlan.gnorm z : ℝ)) ^ (-σ) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)

/-- **Absolute convergence of the primary-twisted Hecke series.**  For any `χ : ℤ[i] → ℂ` bounded
by `1` and any `s` with `re s > 1`, the series `Σ_{z primary} χ(z)/|z|^{2s}` is summable: on the
primary coset `|z|² ≥ 1`, so the norm of the summand is dominated by `|z|^{-2 re s}`, which is
summable by `summable_gnorm_rpow_neg`. -/
theorem summable_primary_chi_div_gnorm_cpow {chi : GaussianInt → ℂ}
    (hbd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable ({z : GaussianInt | Work.FIPlan.IsPrimary z}.indicator
      (fun z : GaussianInt => chi z / (Work.FIPlan.gnorm z : ℂ) ^ s)) := by
  classical
  have hsum : Summable (fun z : GaussianInt => (Work.FIPlan.gnorm z : ℝ) ^ (-s.re)) :=
    summable_gnorm_rpow_neg hs
  refine Summable.of_norm_bounded hsum (fun z => ?_)
  rw [Set.indicator_apply]
  by_cases hz : z ∈ {z : GaussianInt | Work.FIPlan.IsPrimary z}
  · rw [if_pos hz]
    have hprim : Work.FIPlan.IsPrimary z := hz
    have hg1 : 1 ≤ Work.FIPlan.gnorm z := Work.FIArea5.S16Hecke.one_le_gnorm_of_isPrimary z hprim
    have hg1R : (1 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by exact_mod_cast hg1
    have hgpos : (0 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith
    have hcast : ((Work.FIPlan.gnorm z : ℂ)) = ((Work.FIPlan.gnorm z : ℝ) : ℂ) := by simp
    calc ‖chi z / (Work.FIPlan.gnorm z : ℂ) ^ s‖
        = ‖chi z‖ / (Work.FIPlan.gnorm z : ℝ) ^ s.re := by
          rw [norm_div, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hgpos s]
      _ ≤ 1 / (Work.FIPlan.gnorm z : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right (hbd z) (by positivity)
      _ = (Work.FIPlan.gnorm z : ℝ) ^ (-s.re) := by
          rw [one_div, Real.rpow_neg (le_of_lt hgpos)]
  · rw [if_neg hz, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

end

end Work.FIArea6Hecke.R
