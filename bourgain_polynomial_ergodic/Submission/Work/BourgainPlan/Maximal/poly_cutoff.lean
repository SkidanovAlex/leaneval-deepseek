import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs

/-!
# The cutoff scale of a dyadic block

Below the scale `K₁ + 4m` (with `K₁` depending only on `P`) the sharp window of the `m`-th block
can fail to be contained in the major arcs and can fail to be separated enough for the
weighted-neighbourhood maximal estimate.  This file records the explicit cutoff: for all `m` and
all `k ≥ K₁ + 4m` all three conditions hold.

The two numerical identities used are `poly_cutoff_polyDil_inv` and `poly_cutoff_polyArcRad_eq`; everything else is a
comparison of powers of `2` against `Nat.clog` bounds.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.ExponentialSums

/-- The dyadic dilation is the inverse of a natural power of `2`. -/
lemma poly_cutoff_polyDil_inv (P : Polynomial ℤ) (k : ℕ) :
    (polyDil P k)⁻¹ = ((2:ℝ)^(k * P.natDegree))⁻¹ := by
  rw [polyDil, powDil, ← pow_mul]

/-- The major-arc radius is `2^{k/4}` times the sharp window. -/
lemma poly_cutoff_polyArcRad_eq (P : Polynomial ℤ) (k : ℕ) :
    polyArcRad P k = (2:ℝ)^((k:ℝ)/4) * (polyDil P k)⁻¹ := by
  rw [polyArcRad, powArcRad, polyDil, powDil, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat,
    ← Real.rpow_natCast (2:ℝ) k,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) ((k:ℝ)) (-((P.natDegree:ℝ) - 1/4)),
    show (k:ℝ) * -((P.natDegree:ℝ) - 1/4)
      = (k:ℝ)/4 + (-(((k * P.natDegree : ℕ)):ℝ)) by push_cast; ring,
    Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_neg_natCast, zpow_neg, zpow_natCast]

/-- The `Nat.clog` bound `n ≤ 2 ^ clog 2 n`, transported to `ℝ`. -/
lemma poly_cutoff_cast_le_pow_clog (n : ℕ) : ((n:ℕ) : ℝ) ≤ (2:ℝ)^(Nat.clog 2 n) := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) n
  have h' : ((n:ℕ) : ℝ) ≤ (((2:ℕ)^(Nat.clog 2 n)) : ℝ) := by exact_mod_cast h
  simpa using h'

/-- `(3x)⁻¹ = (1/x)/3`. -/
lemma poly_cutoff_mul_three_inv (x : ℝ) : (3 * x)⁻¹ = (1 / x) / 3 := by
  rw [one_div, div_eq_mul_inv, mul_inv, mul_comm]

/-- **The cutoff.**  There is `K₁` such that for every block `m` and every scale `k ≥ K₁ + 4m`, the
sharp window `(polyDil P k)⁻¹` is contained in the major arcs, is below `1/(2c)`, and is at most a
third of the block separation `1/(c² 4^{m+1})`. -/
theorem poly_cutoff (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (hd : 2 ≤ P.natDegree) :
    ∃ K₁ : ℕ, 4 ≤ K₁ ∧ ∀ m k : ℕ, K₁ + 4*m ≤ k →
      (P.leadingCoeff : ℝ) * (polyDil P k)⁻¹ ≤ polyArcRad P k ∧
      (polyDil P k)⁻¹ < 1 / (2 * (P.leadingCoeff : ℝ)) ∧
      (polyDil P k)⁻¹ ≤ (1 / ((P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1))) / 3 := by
  set c : ℕ := P.leadingCoeff.toNat with hcdef
  have hcc : ((c : ℕ) : ℝ) = (P.leadingCoeff : ℝ) := by
    rw [hcdef]; exact_mod_cast (Int.toNat_of_nonneg hc.le)
  have hCpos : (0:ℝ) < (P.leadingCoeff : ℝ) := by exact_mod_cast hc
  set l₁ : ℕ := Nat.clog 2 (c + 2) with hl1
  set l₂ : ℕ := Nat.clog 2 (3 * c^2 + 2) with hl2
  -- `2 ^ l₁ ≥ c + 2` and `2 ^ l₂ ≥ 3c² + 2`, over `ℝ`
  have hc2 : (c:ℝ) + 2 ≤ (2:ℝ)^l₁ := by
    have h : c + 2 ≤ 2^l₁ := by
      rw [hl1]; exact Nat.le_pow_clog (by norm_num : 1 < 2) (c + 2)
    have h' : ((c + 2 : ℕ) : ℝ) ≤ (((2:ℕ)^l₁ : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hc2' : 3 * (c:ℝ)^2 ≤ (2:ℝ)^l₂ := by
    have h : 3 * c^2 + 2 ≤ 2^l₂ := by
      rw [hl2]; exact Nat.le_pow_clog (by norm_num : 1 < 2) (3 * c^2 + 2)
    have h' : ((3 * c^2 + 2 : ℕ) : ℝ) ≤ (((2:ℕ)^l₂ : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  refine ⟨4 * (l₁ + l₂ + 2) + 4, by omega, fun m k hk => ?_⟩
  have hk1 : 4 * l₁ ≤ k := by omega
  -- condition 1: the sharp window lies inside the major arcs
  have hC_le : (P.leadingCoeff : ℝ) ≤ (2:ℝ)^((k:ℝ)/4) := by
    rw [← hcc]
    have hlog : ((l₁:ℕ):ℝ) ≤ (k:ℝ)/4 := by
      have h : ((4 * l₁ : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
      push_cast at h; linarith
    calc (c:ℝ) ≤ (2:ℝ)^l₁ := by linarith [hc2]
      _ ≤ (2:ℝ)^((k:ℝ)/4) := by
          rw [← Real.rpow_natCast (2:ℝ) l₁]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlog
  have hcond1 : (P.leadingCoeff : ℝ) * (polyDil P k)⁻¹ ≤ polyArcRad P k := by
    rw [poly_cutoff_polyArcRad_eq]
    exact mul_le_mul_of_nonneg_right hC_le (by
      rw [inv_nonneg]; exact le_of_lt (polyDil_pos P k))
  -- condition 2: the sharp window is below `1/(2c)`
  have hcond2 : (polyDil P k)⁻¹ < 1 / (2 * (P.leadingCoeff : ℝ)) := by
    rw [poly_cutoff_polyDil_inv, one_div]
    refine (inv_lt_inv₀ (by positivity) (mul_pos (by norm_num) hCpos)).mpr ?_
    rw [← hcc]
    have hlt : (2:ℝ) * (c:ℝ) < ((c:ℝ) + 2)^2 := by nlinarith
    have hsq : ((c:ℝ) + 2)^2 ≤ ((2:ℝ)^l₁)^2 :=
      pow_le_pow_left₀ (by positivity) hc2 2
    have hpow : ((2:ℝ)^l₁)^2 = (2:ℝ)^(2 * l₁) := by rw [← pow_mul, Nat.mul_comm]
    have hexp : 2 * l₁ ≤ k * P.natDegree := by
      calc 2 * l₁ ≤ 4 * l₁ := by omega
        _ ≤ k := hk1
        _ ≤ k * P.natDegree := Nat.le_mul_of_pos_right k (by omega)
    calc (2:ℝ) * (c:ℝ) < ((c:ℝ) + 2)^2 := hlt
      _ ≤ ((2:ℝ)^l₁)^2 := hsq
      _ = (2:ℝ)^(2 * l₁) := hpow
      _ ≤ (2:ℝ)^(k * P.natDegree) := pow_le_pow_right₀ (by norm_num) hexp
  -- condition 3: the sharp window is at most a third of the block separation
  have hcond3 : (polyDil P k)⁻¹ ≤ (1 / ((P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1))) / 3 := by
    rw [poly_cutoff_polyDil_inv]
    have h4m : (4:ℝ)^(m+1) = (2:ℝ)^(2*(m+1)) := by
      rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, pow_mul]
    have hxpos : 0 < (P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1) := by positivity
    have hkey : 3 * ((P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1)) ≤ (2:ℝ)^(k * P.natDegree) := by
      rw [← hcc, h4m]
      have hexp : l₂ + 2*(m+1) ≤ k * P.natDegree := by
        have h2 : l₂ + 2*(m+1) ≤ 2 * (4 * (l₁ + l₂ + 2) + 4 + 4*m) := by omega
        have h3 : 2 * (4 * (l₁ + l₂ + 2) + 4 + 4*m)
            ≤ P.natDegree * (4 * (l₁ + l₂ + 2) + 4 + 4*m) :=
          Nat.mul_le_mul_right _ hd
        have h4 : P.natDegree * (4 * (l₁ + l₂ + 2) + 4 + 4*m) ≤ P.natDegree * k :=
          Nat.mul_le_mul_left _ hk
        calc l₂ + 2*(m+1) ≤ 2 * (4 * (l₁ + l₂ + 2) + 4 + 4*m) := h2
          _ ≤ P.natDegree * (4 * (l₁ + l₂ + 2) + 4 + 4*m) := h3
          _ ≤ P.natDegree * k := h4
          _ = k * P.natDegree := Nat.mul_comm _ _
      calc 3 * ((c:ℝ)^2 * (2:ℝ)^(2*(m+1)))
          = 3 * (c:ℝ)^2 * (2:ℝ)^(2*(m+1)) := by ring
        _ ≤ (2:ℝ)^l₂ * (2:ℝ)^(2*(m+1)) :=
            mul_le_mul_of_nonneg_right hc2' (by positivity)
        _ = (2:ℝ)^(l₂ + 2*(m+1)) := (pow_add _ _ _).symm
        _ ≤ (2:ℝ)^(k * P.natDegree) := pow_le_pow_right₀ (by norm_num) hexp
    calc ((2:ℝ)^(k * P.natDegree))⁻¹
        ≤ (3 * ((P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1)))⁻¹ :=
          (inv_le_inv₀ (by positivity) (by positivity)).mpr hkey
      _ = (1 / ((P.leadingCoeff : ℝ)^2 * (4:ℝ)^(m+1))) / 3 := poly_cutoff_mul_three_inv _
  exact ⟨hcond1, hcond2, hcond3⟩

end Work.BourgainPlan.Maximal
