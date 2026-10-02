/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# Boundedness of the parabolic basin from the escape (doubling) condition

`Work.FatouParabolic.BasinEscape F` says that outside some disc of radius `R > 0` the map `F`
at least doubles the modulus: `2 ‖z‖ ≤ ‖F z‖` whenever `R ≤ ‖z‖`.

Under that condition the whole basin of *any* point `z₀` is contained in the disc of radius `R`:
if `‖z‖ ≥ R` then the orbit of `z` grows at least as `2^n ‖z‖ ≥ 2^n R`, so it is unbounded, and an
unbounded orbit cannot converge to the finite point `z₀`.  Hence the punctured basin (being a
subset of the basin) is bounded — `isBounded_puncturedBasin_of_escape`.

The point of the lemma in the design of `Submission/Work/FatouParabolic/NOTES.md` §3 is exactly
this: it is the elementary half of the Liouville argument, and it is what a polynomial of degree
`≥ 2` provides for free.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter

namespace Work.FatouParabolic.Core

/-- **The basin of `z₀` is contained in the disc where the doubling condition fails.**

If `F` doubles the modulus outside the disc of radius `R > 0`, then no point of modulus `≥ R` can
have an orbit converging to the finite point `z₀`: along such an orbit `‖F^[n] z‖ ≥ 2^n ‖z‖ ≥ 2^n R`
tends to infinity, while a convergent sequence is bounded. -/
theorem norm_lt_of_mem_basin_of_escape {F : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hRpos : 0 < R) (hR : ∀ z : ℂ, R ≤ ‖z‖ → 2 * ‖z‖ ≤ ‖F z‖)
    {z : ℂ} (hz : z ∈ Work.FatouParabolic.basin F z₀) : ‖z‖ < R := by
  by_contra hcon
  have hcon : R ≤ ‖z‖ := not_lt.mp hcon
  -- The orbit dominates the geometric progression `2^n ‖z‖`.
  have hgrowth : ∀ n : ℕ, 2 ^ n * ‖z‖ ≤ ‖(F^[n]) z‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hzR : R ≤ ‖(F^[n]) z‖ := by
        have h1 : ‖z‖ ≤ 2 ^ n * ‖z‖ := by
          have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
          nlinarith [norm_nonneg z]
        linarith
      have hstep : 2 * ‖(F^[n]) z‖ ≤ ‖(F^[n+1]) z‖ := by
        rw [Function.iterate_succ_apply']
        exact hR ((F^[n]) z) hzR
      have hpow : (2 : ℝ) ^ (n+1) * ‖z‖ = 2 * (2 ^ n * ‖z‖) := by ring
      rw [hpow]
      linarith
  -- Eventually the geometric bound exceeds `‖z₀‖ + 1`.
  obtain ⟨N, hN⟩ := exists_nat_gt ((‖z₀‖ + 1) / R)
  have hNA : ‖z₀‖ + 1 < (2 : ℝ) ^ N * R := by
    have h1 : (‖z₀‖ + 1) / R * R < (N : ℝ) * R :=
      mul_lt_mul_of_pos_right hN hRpos
    rw [div_mul_cancel₀ _ (ne_of_gt hRpos)] at h1
    have h2 : (N : ℝ) < (2 : ℝ) ^ N := by exact_mod_cast (Nat.lt_two_pow_self (n := N))
    have h3 : (N : ℝ) * R < (2 : ℝ) ^ N * R := mul_lt_mul_of_pos_right h2 hRpos
    linarith
  -- Convergence to `z₀` makes the orbit eventually small.
  obtain ⟨N', hNB⟩ := (Metric.tendsto_atTop.mp hz) 1 one_pos
  set n := max N N' with hn
  have hnN : N ≤ n := le_max_left _ _
  have hnN' : N' ≤ n := le_max_right _ _
  have hbig : ‖z₀‖ + 1 < ‖(F^[n]) z‖ := by
    have hp : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hnN
    have h2 : (2 : ℝ) ^ N * R ≤ (2 : ℝ) ^ n * ‖z‖ := by
      have h3 : (2 : ℝ) ^ N * R ≤ (2 : ℝ) ^ n * R :=
        mul_le_mul_of_nonneg_right hp (le_of_lt hRpos)
      have h4 : (2 : ℝ) ^ n * R ≤ (2 : ℝ) ^ n * ‖z‖ :=
        mul_le_mul_of_nonneg_left hcon (pow_nonneg (by norm_num) n)
      linarith
    linarith [hgrowth n]
  have hsmall : ‖(F^[n]) z‖ < ‖z₀‖ + 1 := by
    have hd : dist ((F^[n]) z) z₀ < 1 := hNB n hnN'
    rw [dist_eq_norm] at hd
    have h3 : ‖(F^[n]) z‖ ≤ ‖(F^[n]) z - z₀‖ + ‖z₀‖ := by
      have h4 := norm_add_le ((F^[n]) z - z₀) z₀
      simpa using h4
    linarith
  linarith

theorem isBounded_puncturedBasin_of_escape {F : ℂ → ℂ} {z₀ : ℂ}
    (h : Work.FatouParabolic.BasinEscape F) :
    Bornology.IsBounded (Work.FatouParabolic.puncturedBasin F z₀) := by
  obtain ⟨R, hRpos, hR⟩ := h
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt (norm_lt_of_mem_basin_of_escape hRpos hR hz.2)

end Work.FatouParabolic.Core
