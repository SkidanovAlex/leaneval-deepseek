import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Maximal.poly_cutoff

/-!
# The cutoff scale at an arbitrary lacunary scale

The dyadic development (`Work.BourgainPlan.Maximal.poly_cutoff`) proves that for `k ≥ K₁ + 4m`
the sharp window `(polyDil P k)⁻¹` of the `m`-th block is inside the major arcs, is below
`1/(2c)`, and is at most a third of the block separation.  Bourgain's oscillation inequality is
stated along the *lacunary* scales `N_i = ⌊ρ^i⌋`, which are not powers of two, so the cutoff has
to be re-proved for an arbitrary scale `N` with the hypothesis `4 ^ m ≤ N` (the natural
lacunary analogue of `2 ^ (K₁ + 4m) ≤ N`).

All three conditions are elementary power comparisons.  Writing `c = P.leadingCoeff` and
`d = deg P ≥ 2`:

* `polyDilN P N = N ^ d` and `polyArcRadN P N = N ^ (-(d - 1/4)) = N ^ (1/4) · N ^ (-d)`, so the
  first condition is exactly `c ≤ N ^ (1/4)`, i.e. `c ^ 4 ≤ N`;
* the second is `2c < N ^ d`, which follows from `N ≥ 2c + 1` and `d ≥ 1`;
* the third is `3 c ^ 2 · 4 ^ (m+1) ≤ N ^ d`; since `4 ^ m ≤ N` and `d ≥ 2` it is enough that
  `12 c ^ 2 ≤ N`, for `3 c ^ 2 · 4 ^ (m+1) = 12 c ^ 2 · 4 ^ m ≤ N · N = N ^ 2 ≤ N ^ d`.

The cutoff `K₁` is the maximum of the four bounds.
-/

set_option autoImplicit false

open Finset MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Oscillation

theorem poly_cutoff_N (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ K₁ : ℕ, 4 ≤ K₁ ∧ ∀ (m N : ℕ), K₁ ≤ N → 4 ^ m ≤ N →
      (P.leadingCoeff : ℝ) * (Work.BourgainPlan.Oscillation.polyDilN P N)⁻¹
          ≤ Work.BourgainPlan.Oscillation.polyArcRadN P N ∧
      (Work.BourgainPlan.Oscillation.polyDilN P N)⁻¹ < 1 / (2 * (P.leadingCoeff : ℝ)) ∧
      (Work.BourgainPlan.Oscillation.polyDilN P N)⁻¹
          ≤ (1 / ((P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1))) / 3 := by
  -- `c` is the (positive) leading coefficient as a natural number.
  set c : ℕ := P.leadingCoeff.toNat with hcdef
  have hcc : ((c:ℕ):ℝ) = (P.leadingCoeff:ℝ) := by
    rw [hcdef]; exact_mod_cast (Int.toNat_of_nonneg hc.le)
  have hcposR : (0:ℝ) < (c:ℝ) := by
    rw [hcc]; exact_mod_cast hc
  have hd1 : 1 ≤ P.natDegree := le_trans (by norm_num) hd
  -- the cutoff, and the four numerical consequences we shall use
  refine ⟨max (max 4 (c^4)) (max (12*c^2) (2*c+1)), by omega, fun m N hKN h4m => ?_⟩
  have hN4 : 4 ≤ N := by omega
  have hc4N : c^4 ≤ N := by omega
  have h12N : 12*c^2 ≤ N := by omega
  have h2cN : 2*c+1 ≤ N := by omega
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : (0:ℕ) < N := by omega
    exact_mod_cast this
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have : (1:ℕ) ≤ N := by omega
    exact_mod_cast this
  -- condition 1 (`c ≤ N^(1/4)`), used through the monotonicity of `x ↦ x ^ d`
  have hcr : (c:ℝ) ≤ (N:ℝ)^((4:ℝ)⁻¹) := by
    refine (Real.le_rpow_inv_iff_of_pos (le_of_lt hcposR) (le_of_lt hNpos)
      (by norm_num : (0:ℝ) < 4)).mpr ?_
    have : ((c^4 : ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hc4N
    simpa using this
  have hcond1 : (P.leadingCoeff : ℝ) * (polyDilN P N)⁻¹ ≤ polyArcRadN P N := by
    have harc : (N:ℝ)^(-((P.natDegree:ℝ) - 1/4))
        = (N:ℝ)^((4:ℝ)⁻¹) * ((N:ℝ)^P.natDegree)⁻¹ := by
      rw [show -((P.natDegree:ℝ) - 1/4) = (4:ℝ)⁻¹ + (-(P.natDegree:ℝ)) by ring]
      rw [Real.rpow_add hNpos, Real.rpow_neg (le_of_lt hNpos), Real.rpow_natCast]
    rw [polyDilN, polyArcRadN, harc, ← hcc]
    exact mul_le_mul_of_nonneg_right hcr (by positivity)
  -- condition 2 (`2c < N^d`)
  have h2clt : (2:ℝ) * (c:ℝ) < (N:ℝ)^P.natDegree := by
    have h1 : (2:ℝ)*(c:ℝ) + 1 ≤ (N:ℝ) := by
      have : ((2*c+1 : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast h2cN
      push_cast at this; linarith
    have h2 : (N:ℝ) ≤ (N:ℝ)^P.natDegree := by
      calc (N:ℝ) = (N:ℝ)^1 := (pow_one _).symm
        _ ≤ (N:ℝ)^P.natDegree := pow_le_pow_right₀ hN1 hd1
    linarith
  have hcond2 : (polyDilN P N)⁻¹ < 1 / (2 * (P.leadingCoeff : ℝ)) := by
    rw [polyDilN, ← hcc, one_div]
    exact (inv_lt_inv₀ (pow_pos hNpos _) (by linarith)).mpr h2clt
  -- condition 3 (`3 c² 4^(m+1) ≤ N^d`)
  have h4mr : (4:ℝ)^m ≤ (N:ℝ) := by
    have : ((4:ℕ)^m : ℝ) ≤ (N:ℝ) := by exact_mod_cast h4m
    simpa using this
  have h12cr : (12:ℝ)*(c:ℝ)^2 ≤ (N:ℝ) := by
    have : ((12*c^2 : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast h12N
    push_cast at this; linarith
  have hkey : 3 * ((c:ℝ)^2 * (4:ℝ)^(m+1)) ≤ (N:ℝ)^P.natDegree := by
    have h4m1 : (4:ℝ)^(m+1) = 4 * (4:ℝ)^m := by rw [pow_succ]; ring
    have hNd : (N:ℝ)^2 ≤ (N:ℝ)^P.natDegree := pow_le_pow_right₀ hN1 hd
    calc 3 * ((c:ℝ)^2 * (4:ℝ)^(m+1)) = (12*(c:ℝ)^2) * (4:ℝ)^m := by rw [h4m1]; ring
      _ ≤ (N:ℝ) * (N:ℝ) := mul_le_mul h12cr h4mr (by positivity) (by positivity)
      _ = (N:ℝ)^2 := by ring
      _ ≤ (N:ℝ)^P.natDegree := hNd
  have hcond3 : (polyDilN P N)⁻¹ ≤ (1 / ((P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1))) / 3 := by
    rw [polyDilN, ← hcc]
    have h3A : (1 / ((c:ℝ)^2 * (4:ℝ)^(m+1))) / 3 = (3 * ((c:ℝ)^2 * (4:ℝ)^(m+1)))⁻¹ := by
      rw [one_div, div_eq_mul_inv, ← mul_inv, mul_comm]
    rw [h3A]
    exact (inv_le_inv₀ (pow_pos hNpos _) (by positivity)).mpr hkey
  exact ⟨hcond1, hcond2, hcond3⟩

end Work.BourgainPlan.Oscillation
