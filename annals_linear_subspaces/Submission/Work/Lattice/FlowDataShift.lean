import Mathlib
import Submission.Work.Lattice.FlowDataMax
import Submission.Work.Lattice.FlowShrink

/-!
# Two-sided shift bounds for the exponential flow on exterior powers

The exponential two-scale flow `a_h = eFlow ℓ h` (`a = e^{−h/ℓ}` on the first `ℓ` coordinates,
`b = e^{h/(d−ℓ)}` on the remaining ones) acts on `⋀^j ℝᵈ` with block eigenvalues
`a^{j−i} b^i = e^{h·σ_i}`, `σ_i = −(j−i)/ℓ + i/(d−ℓ) ∈ [−j/ℓ, j/(d−ℓ)]`.  Since the flow is
diagonal in the block decomposition `⋀^j ℝᵈ = ⊕_i (⋀^{j−i}L ⊗ ⋀^i Lᗮ)`, its action on `⋀^j ℝᵈ` is
pinched between the extreme eigenvalues (valid for **every** `j`-vector `w`, with no purity
hypothesis):

* `eFlow_norm_le_exp_mul` : `h ≥ 0` ⟹ `‖⋀^j a_h w‖ ≤ e^{h·j/(d−ℓ)} ‖w‖`;
* `eFlow_norm_le_exp_mul_inv` : `h ≥ 0` ⟹ `‖⋀^j a_{−h} w‖ ≤ e^{h·j/ℓ} ‖w‖`;
* `exp_neg_mul_le_eFlow_norm` : `h ≥ 0` ⟹ `e^{−h·j/ℓ} ‖w‖ ≤ ‖⋀^j a_h w‖`.

The first two are the *upper* shift bounds needed to compare the rank data of the flow lattice at
two different times; the third is the flow's exterior-power floor (`FlowShrink` in vector form).

They are proved from the block expansion `‖⋀^j a_h w‖² = Σ_i (e^{hσ_i})² ‖block_i w‖²`
(`sum_normSq_blockElem` + `norm_blockElem_map_twoScale`), so nothing pure-tensor is used.

The module also contains

* the generic infimum-shift lemma `sInf_setOf_le_add` (for set-builder data indexed by the same
  predicate);
* `eFlow_add` / `eFlow_iMulti_add` (the flow is a one-parameter diagonal group, so
  `⋀^j a_{t+h}(⋀v) = ⋀^j a_h (⋀^j a_t (⋀v))`);
* `flowEuclidData_shift_le` / `flowEuclidData_shift_ge`: the rank-`j` data of the flow lattice
  moves by at most `+h·j/(d−ℓ)` resp. `−h·j/ℓ`, i.e. it is Lipschitz in `t` with constant
  `j·max(1/ℓ,1/(d−ℓ))`.  Via `Submission.Polygon.abs_largestConvexMinorant_sub_le` and
  `abs_dslope_largestConvexMinorant_sub_le` this makes the Grayson polygon `t ↦ c_t` and its slope
  sequence continuous — the continuity input of the time-selection argument.

Module `Submission.Work.Lattice.FlowDataShift`, namespace `Submission.FlowDataShift`.
-/

noncomputable section

open Module exteriorPower Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Submission.FlowDataShift

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.FlowDataMax

variable {d : ℕ}

/-- The exponential flow of the §3 route is the two-scale diagonal map. -/
theorem eFlow_scaleMap (ℓ : ℕ) (h : ℝ) :
    eFlow (d := d) ℓ h = scaleMap (twoScale (Real.exp (-h / (ℓ : ℝ)))
      (Real.exp (h / ((d - ℓ : ℕ) : ℝ))) ℓ) := rfl

/-- The block eigenvalue of the flow is the exponential of `h·σ_i`. -/
theorem eFlow_eigen_eq_exp {j ℓ : ℕ} (h : ℝ) {i : ℕ} (hi : i ≤ j) :
    Real.exp (-h / (ℓ : ℝ)) ^ (j - i) * Real.exp (h / ((d - ℓ : ℕ) : ℝ)) ^ i =
      Real.exp (h * (-((j : ℝ) - (i : ℝ)) / (ℓ : ℝ) + (i : ℝ) / ((d - ℓ : ℕ) : ℝ))) := by
  have hcast : (((j - i : ℕ)) : ℝ) = (j : ℝ) - (i : ℝ) := Nat.cast_sub hi
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  rw [hcast]
  ring

section ExponentBounds

variable {j ℓ : ℕ} {i : ℕ} {h : ℝ}

/-- Exponent comparison for the upper shift bound: `(j−i)(−h/ℓ) + i·h/(d−ℓ) ≤ h·j/(d−ℓ)`. -/
lemma exp_cmp₁ (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hh : 0 ≤ h) (hi : i ≤ j) :
    (((j - i : ℕ)) : ℝ) * (-h / (ℓ : ℝ)) + (i : ℝ) * (h / ((d - ℓ : ℕ) : ℝ)) ≤
      h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ) := by
  have hcast : (((j - i : ℕ)) : ℝ) = (j : ℝ) - (i : ℝ) := Nat.cast_sub hi
  have hl : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hm : (0 : ℝ) < ((d - ℓ : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hℓd)]
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  have hnum : 0 ≤ h * (((j - i : ℕ)) : ℝ) *
      (((d - ℓ : ℕ) : ℝ) + (ℓ : ℝ)) :=
    mul_nonneg (mul_nonneg hh (Nat.cast_nonneg _)) (by positivity)
  have hden : (0 : ℝ) < (ℓ : ℝ) * ((d - ℓ : ℕ) : ℝ) := mul_pos hl hm
  have hle : -(h * (((j - i : ℕ)) : ℝ) * (((d - ℓ : ℕ) : ℝ) + (ℓ : ℝ))) /
      ((ℓ : ℝ) * ((d - ℓ : ℕ) : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnum) hden.le
  have key : (((j - i : ℕ)) : ℝ) * (-h / (ℓ : ℝ)) +
        (i : ℝ) * (h / ((d - ℓ : ℕ) : ℝ)) - h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ) =
      -(h * (((j - i : ℕ)) : ℝ) * (((d - ℓ : ℕ) : ℝ) + (ℓ : ℝ))) /
        ((ℓ : ℝ) * ((d - ℓ : ℕ) : ℝ)) := by
    rw [hcast]; field_simp; ring
  linarith [key, hle]

/-- Exponent comparison for the upper bound of the inverse flow:
`(j−i)·h/ℓ + i·(−h/(d−ℓ)) ≤ h·j/ℓ`. -/
lemma exp_cmp₂ (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hh : 0 ≤ h) (hi : i ≤ j) :
    (((j - i : ℕ)) : ℝ) * (-(-h) / (ℓ : ℝ)) + (i : ℝ) * ((-h) / ((d - ℓ : ℕ) : ℝ)) ≤
      h * (j : ℝ) / (ℓ : ℝ) := by
  have hcast : (((j - i : ℕ)) : ℝ) = (j : ℝ) - (i : ℝ) := Nat.cast_sub hi
  have hl : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hm : (0 : ℝ) < ((d - ℓ : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hℓd)]
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  have hnum : 0 ≤ h * (i : ℝ) * (((d - ℓ : ℕ) : ℝ) + (ℓ : ℝ)) :=
    mul_nonneg (mul_nonneg hh (Nat.cast_nonneg _)) (by positivity)
  have hden : (0 : ℝ) < (ℓ : ℝ) * ((d - ℓ : ℕ) : ℝ) := mul_pos hl hm
  have hle : -(h * (i : ℝ) * (((d - ℓ : ℕ) : ℝ) + (ℓ : ℝ))) /
      ((ℓ : ℝ) * ((d - ℓ : ℕ) : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnum) hden.le
  have key : (((j - i : ℕ)) : ℝ) * (-(-h) / (ℓ : ℝ)) +
        (i : ℝ) * ((-h) / ((d - ℓ : ℕ) : ℝ)) - h * (j : ℝ) / (ℓ : ℝ) =
      -(h * (i : ℝ) * (((d - ℓ : ℕ) : ℝ) + (ℓ : ℝ))) /
        ((ℓ : ℝ) * ((d - ℓ : ℕ) : ℝ)) := by
    rw [hcast]; field_simp; ring
  linarith [key, hle]

/-- Exponent comparison for the lower shift bound:
`−h·j/ℓ ≤ (j−i)(−h/ℓ) + i·h/(d−ℓ)`. -/
lemma exp_cmp₃ (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (hh : 0 ≤ h) (hi : i ≤ j) :
    -(h * (j : ℝ) / (ℓ : ℝ)) ≤
      (((j - i : ℕ)) : ℝ) * (-h / (ℓ : ℝ)) + (i : ℝ) * (h / ((d - ℓ : ℕ) : ℝ)) := by
  have hcast : (((j - i : ℕ)) : ℝ) = (j : ℝ) - (i : ℝ) := Nat.cast_sub hi
  have hl : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hm : (0 : ℝ) < ((d - ℓ : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hℓd)]
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  have hnum : 0 ≤ h * (i : ℝ) * (((d - ℓ : ℕ) : ℝ) + (ℓ : ℝ)) :=
    mul_nonneg (mul_nonneg hh (Nat.cast_nonneg _)) (by positivity)
  have hden : (0 : ℝ) < (ℓ : ℝ) * ((d - ℓ : ℕ) : ℝ) := mul_pos hl hm
  have hle : 0 ≤ h * (i : ℝ) * (((d - ℓ : ℕ) : ℝ) + (ℓ : ℝ)) /
      ((ℓ : ℝ) * ((d - ℓ : ℕ) : ℝ)) := div_nonneg hnum hden.le
  have key : (((j - i : ℕ)) : ℝ) * (-h / (ℓ : ℝ)) + (i : ℝ) * (h / ((d - ℓ : ℕ) : ℝ)) -
        (-(h * (j : ℝ) / (ℓ : ℝ))) =
      h * (i : ℝ) * (((d - ℓ : ℕ) : ℝ) + (ℓ : ℝ)) / ((ℓ : ℝ) * ((d - ℓ : ℕ) : ℝ)) := by
    rw [hcast]; field_simp; ring
  linarith [key, hle]

end ExponentBounds

/-- **Upper shift bound** for the exponential flow on `⋀^j ℝᵈ` (arbitrary `j`-vector, `h ≥ 0`). -/
theorem eFlow_norm_le_exp_mul {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {h : ℝ} (hh : 0 ≤ h)
    (w : WK d j) :
    ‖exteriorPower.map j (eFlow (d := d) ℓ h) w‖ ≤
      Real.exp (h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ)) * ‖w‖ := by
  rw [eFlow_scaleMap]
  have hkey : ∀ i : ℕ, i ≤ j →
      (Real.exp (-h / (ℓ : ℝ)) ^ (j - i) * Real.exp (h / ((d - ℓ : ℕ) : ℝ)) ^ i) ^ 2 ≤
        (Real.exp (h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ))) ^ 2 := by
    intro i hi
    have heq := eFlow_eigen_eq_exp (d := d) (j := j) (ℓ := ℓ) h hi
    rw [heq]
    apply pow_le_pow_left₀ (Real.exp_nonneg _)
    rw [Real.exp_le_exp]
    have h2 : h * (-((j : ℝ) - (i : ℝ)) / (ℓ : ℝ) + (i : ℝ) / ((d - ℓ : ℕ) : ℝ)) =
        (((j - i : ℕ)) : ℝ) * (-h / (ℓ : ℝ)) + (i : ℝ) * (h / ((d - ℓ : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hi]; ring
    rw [h2]
    exact exp_cmp₁ hℓ0 hℓd hh hi
  have hsum : ‖exteriorPower.map j (scaleMap (twoScale (Real.exp (-h / (ℓ : ℝ)))
      (Real.exp (h / ((d - ℓ : ℕ) : ℝ))) ℓ)) w‖ ^ 2 ≤
      (Real.exp (h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ)) * ‖w‖) ^ 2 := by
    rw [mul_pow]
    rw [← sum_normSq_blockElem (d := d) (k := j) (ℓ := ℓ)
      (exteriorPower.map j (scaleMap (twoScale (Real.exp (-h / (ℓ : ℝ)))
        (Real.exp (h / ((d - ℓ : ℕ) : ℝ))) ℓ)) w)]
    rw [← sum_normSq_blockElem (d := d) (k := j) (ℓ := ℓ) w, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [norm_blockElem_map_twoScale (d := d) (k := j) (ℓ := ℓ) _ _ w hij
      (Real.exp_nonneg _) (Real.exp_nonneg _), mul_pow]
    exact mul_le_mul_of_nonneg_right (hkey i hij) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsum

/-- **Upper shift bound for the inverse flow**: `‖⋀^j a_{−h} w‖ ≤ e^{h·j/ℓ}‖w‖` for `h ≥ 0`. -/
theorem eFlow_norm_le_exp_mul_inv {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {h : ℝ} (hh : 0 ≤ h)
    (w : WK d j) :
    ‖exteriorPower.map j (eFlow (d := d) ℓ (-h)) w‖ ≤
      Real.exp (h * (j : ℝ) / (ℓ : ℝ)) * ‖w‖ := by
  rw [show eFlow (d := d) ℓ (-h) = scaleMap (twoScale (Real.exp (-(-h) / (ℓ : ℝ)))
      (Real.exp ((-h) / ((d - ℓ : ℕ) : ℝ))) ℓ) from rfl]
  have hkey : ∀ i : ℕ, i ≤ j →
      (Real.exp (-(-h) / (ℓ : ℝ)) ^ (j - i) * Real.exp ((-h) / ((d - ℓ : ℕ) : ℝ)) ^ i) ^ 2 ≤
        (Real.exp (h * (j : ℝ) / (ℓ : ℝ))) ^ 2 := by
    intro i hi
    rw [show Real.exp (-(-h) / (ℓ : ℝ)) ^ (j - i) *
          Real.exp ((-h) / ((d - ℓ : ℕ) : ℝ)) ^ i =
        Real.exp ((((j - i : ℕ)) : ℝ) * (-(-h) / (ℓ : ℝ)) +
          (i : ℝ) * ((-h) / ((d - ℓ : ℕ) : ℝ))) by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, Real.exp_add]]
    apply pow_le_pow_left₀ (Real.exp_nonneg _)
    rw [Real.exp_le_exp]
    exact exp_cmp₂ hℓ0 hℓd hh hi
  have hsum : ‖exteriorPower.map j (scaleMap (twoScale (Real.exp (-(-h) / (ℓ : ℝ)))
      (Real.exp ((-h) / ((d - ℓ : ℕ) : ℝ))) ℓ)) w‖ ^ 2 ≤
      (Real.exp (h * (j : ℝ) / (ℓ : ℝ)) * ‖w‖) ^ 2 := by
    rw [mul_pow]
    rw [← sum_normSq_blockElem (d := d) (k := j) (ℓ := ℓ)
      (exteriorPower.map j (scaleMap (twoScale (Real.exp (-(-h) / (ℓ : ℝ)))
        (Real.exp ((-h) / ((d - ℓ : ℕ) : ℝ))) ℓ)) w)]
    rw [← sum_normSq_blockElem (d := d) (k := j) (ℓ := ℓ) w, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [norm_blockElem_map_twoScale (d := d) (k := j) (ℓ := ℓ) _ _ w hij
      (Real.exp_nonneg _) (Real.exp_nonneg _), mul_pow]
    exact mul_le_mul_of_nonneg_right (hkey i hij) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsum

/-- **Lower shift bound**: `e^{−h·j/ℓ}‖w‖ ≤ ‖⋀^j a_h w‖` for `h ≥ 0`. -/
theorem exp_neg_mul_le_eFlow_norm {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) {h : ℝ} (hh : 0 ≤ h)
    (w : WK d j) :
    Real.exp (-(h * (j : ℝ) / (ℓ : ℝ))) * ‖w‖ ≤
      ‖exteriorPower.map j (eFlow (d := d) ℓ h) w‖ := by
  rw [eFlow_scaleMap]
  have hkey : ∀ i : ℕ, i ≤ j →
      (Real.exp (-(h * (j : ℝ) / (ℓ : ℝ)))) ^ 2 ≤
        (Real.exp (-h / (ℓ : ℝ)) ^ (j - i) * Real.exp (h / ((d - ℓ : ℕ) : ℝ)) ^ i) ^ 2 := by
    intro i hi
    rw [show Real.exp (-h / (ℓ : ℝ)) ^ (j - i) * Real.exp (h / ((d - ℓ : ℕ) : ℝ)) ^ i =
        Real.exp ((((j - i : ℕ)) : ℝ) * (-h / (ℓ : ℝ)) +
          (i : ℝ) * (h / ((d - ℓ : ℕ) : ℝ))) by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, Real.exp_add]]
    apply pow_le_pow_left₀ (Real.exp_nonneg _)
    rw [Real.exp_le_exp]
    exact exp_cmp₃ hℓ0 hℓd hh hi
  have hsum : (Real.exp (-(h * (j : ℝ) / (ℓ : ℝ))) * ‖w‖) ^ 2 ≤
      ‖exteriorPower.map j (scaleMap (twoScale (Real.exp (-h / (ℓ : ℝ)))
        (Real.exp (h / ((d - ℓ : ℕ) : ℝ))) ℓ)) w‖ ^ 2 := by
    rw [mul_pow]
    rw [← sum_normSq_blockElem (d := d) (k := j) (ℓ := ℓ)
      (exteriorPower.map j (scaleMap (twoScale (Real.exp (-h / (ℓ : ℝ)))
        (Real.exp (h / ((d - ℓ : ℕ) : ℝ))) ℓ)) w)]
    rw [← sum_normSq_blockElem (d := d) (k := j) (ℓ := ℓ) w, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [norm_blockElem_map_twoScale (d := d) (k := j) (ℓ := ℓ) _ _ w hij
      (Real.exp_nonneg _) (Real.exp_nonneg _), mul_pow]
    exact mul_le_mul_of_nonneg_right (hkey i hij) (sq_nonneg _)
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsum

/-- The flow at parameter `0` is the identity. -/
theorem eFlow_zero (ℓ : ℕ) : eFlow (d := d) ℓ 0 = LinearMap.id := by
  ext x i
  simp [eFlow_scaleMap, scaleMap_apply, twoScale_apply]

/-- The exponential flow is a one-parameter diagonal group: `a_{t+h} = a_h ∘ a_t`. -/
theorem eFlow_add (ℓ : ℕ) (t h : ℝ) :
    eFlow (d := d) ℓ (t + h) = (eFlow (d := d) ℓ h).comp (eFlow (d := d) ℓ t) := by
  rw [show eFlow (d := d) ℓ (t + h) = scaleMap (twoScale (Real.exp (-(t + h) / (ℓ : ℝ)))
      (Real.exp ((t + h) / ((d - ℓ : ℕ) : ℝ))) ℓ) from rfl,
    show eFlow (d := d) ℓ h = scaleMap (twoScale (Real.exp (-h / (ℓ : ℝ)))
      (Real.exp (h / ((d - ℓ : ℕ) : ℝ))) ℓ) from rfl,
    show eFlow (d := d) ℓ t = scaleMap (twoScale (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d - ℓ : ℕ) : ℝ))) ℓ) from rfl]
  have h1 : Real.exp (-(t + h) / (ℓ : ℝ)) = Real.exp (-h / (ℓ : ℝ)) * Real.exp (-t / (ℓ : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp ((t + h) / ((d - ℓ : ℕ) : ℝ)) =
      Real.exp (h / ((d - ℓ : ℕ) : ℝ)) * Real.exp (t / ((d - ℓ : ℕ) : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h1, h2]
  ext x i
  simp only [LinearMap.comp_apply, scaleMap_apply, twoScale_apply]
  split_ifs <;> ring

/-- The flowed wedge of a family at time `t + h` is the time-`h` flow of its flowed wedge at `t`. -/
theorem eFlow_iMulti_add {j ℓ : ℕ} (t h : ℝ) (v : Fin j → RD d) :
    exteriorPower.map j (eFlow (d := d) ℓ (t + h)) (exteriorPower.ιMulti ℝ j v) =
      exteriorPower.map j (eFlow (d := d) ℓ h)
        (exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v)) := by
  rw [eFlow_add, exteriorPower.map_comp, LinearMap.comp_apply]

/-- **Generic infimum shift.**  If `F ≤ G + C` pointwise on a common domain `P`, the infimum of the
`F`-data is at most `C` more than the infimum of the `G`-data. -/
theorem sInf_setOf_le_add {α : Type*} {P : α → Prop} {F G : α → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a, F a ≤ G a + C) (hbd : BddBelow {r | ∃ a, P a ∧ r = F a}) :
    sInf {r | ∃ a, P a ∧ r = F a} ≤ sInf {r | ∃ a, P a ∧ r = G a} + C := by
  by_cases hne : ({r | ∃ a, P a ∧ r = G a}).Nonempty
  · have key : ∀ b ∈ {r | ∃ a, P a ∧ r = G a},
        sInf {r | ∃ a, P a ∧ r = F a} - C ≤ b := by
      rintro _ ⟨a, hpa, rfl⟩
      have h1 : sInf {r | ∃ a, P a ∧ r = F a} ≤ F a := csInf_le hbd ⟨a, hpa, rfl⟩
      linarith [h a]
    have h2 := le_csInf hne key
    linarith
  · have hG : {r | ∃ a, P a ∧ r = G a} = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hF : {r | ∃ a, P a ∧ r = F a} = ∅ := by
      rw [← Set.not_nonempty_iff_eq_empty]
      rintro ⟨r, a, hpa, rfl⟩
      exact hne ⟨G a, a, hpa, rfl⟩
    rw [hF, hG, Real.sInf_empty]
    linarith

/-- **The rank data of the flow lattice does not increase faster than `h·j/(d−ℓ)`.** -/
theorem flowEuclidData_shift_le {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (Λ₀ : Submodule ℤ (RD d))
    (hbd : ∀ t : ℝ, BddBelow (flowEuclidDataSet Λ₀ ℓ t j)) {t h : ℝ} (hh : 0 ≤ h) :
    flowEuclidData Λ₀ ℓ (t + h) j ≤
      flowEuclidData Λ₀ ℓ t j + h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ) := by
  have hm : (0 : ℝ) < ((d - ℓ : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hℓd)]
    have : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓd
    linarith
  have hC : 0 ≤ h * (j : ℝ) / ((d - ℓ : ℕ) : ℝ) := by positivity
  have hset : ∀ s : ℝ, {r | ∃ v : Fin j → RD d,
        ((∀ i, v i ∈ Λ₀) ∧ LinearIndependent ℝ v) ∧
          r = Real.log ‖exteriorPower.map j (eFlow (d := d) ℓ s) (exteriorPower.ιMulti ℝ j v)‖}
        = flowEuclidDataSet Λ₀ ℓ s j := by
    intro s
    ext r
    constructor
    · rintro ⟨v, ⟨hv, hli⟩, rfl⟩
      exact ⟨v, hv, hli, rfl⟩
    · rintro ⟨v, hv, hli, rfl⟩
      exact ⟨v, ⟨hv, hli⟩, rfl⟩
  simp only [flowEuclidData]
  rw [← hset (t + h), ← hset t]
  refine sInf_setOf_le_add hC ?_ ?_
  · intro v
    rw [eFlow_iMulti_add]
    rcases eq_or_ne (exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v)) 0
      with hX | hX
    · rw [hX, map_zero]
      simp only [norm_zero, Real.log_zero]
      linarith
    · have hpos : 0 < ‖exteriorPower.map j (eFlow (d := d) ℓ h)
          (exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v))‖ :=
        lt_of_lt_of_le
          (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hX))
          (exp_neg_mul_le_eFlow_norm (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hh _)
      have hle := eFlow_norm_le_exp_mul (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hh
        (exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v))
      have h1 := Real.log_le_log hpos hle
      rw [Real.log_mul (Real.exp_ne_zero _) (norm_pos_iff.mpr hX).ne', Real.log_exp] at h1
      linarith [h1]
  · rw [hset (t + h)]
    exact hbd (t + h)

/-- **The rank data of the flow lattice does not decrease faster than `h·j/ℓ`.** -/
theorem flowEuclidData_shift_ge {j ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (Λ₀ : Submodule ℤ (RD d))
    (hbd : ∀ t : ℝ, BddBelow (flowEuclidDataSet Λ₀ ℓ t j)) {t h : ℝ} (hh : 0 ≤ h) :
    flowEuclidData Λ₀ ℓ t j ≤
      flowEuclidData Λ₀ ℓ (t + h) j + h * (j : ℝ) / (ℓ : ℝ) := by
  have hl : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hC : 0 ≤ h * (j : ℝ) / (ℓ : ℝ) := by positivity
  have hset : ∀ s : ℝ, {r | ∃ v : Fin j → RD d,
        ((∀ i, v i ∈ Λ₀) ∧ LinearIndependent ℝ v) ∧
          r = Real.log ‖exteriorPower.map j (eFlow (d := d) ℓ s) (exteriorPower.ιMulti ℝ j v)‖}
        = flowEuclidDataSet Λ₀ ℓ s j := by
    intro s
    ext r
    constructor
    · rintro ⟨v, ⟨hv, hli⟩, rfl⟩
      exact ⟨v, hv, hli, rfl⟩
    · rintro ⟨v, hv, hli, rfl⟩
      exact ⟨v, ⟨hv, hli⟩, rfl⟩
  simp only [flowEuclidData]
  rw [← hset (t + h), ← hset t]
  refine sInf_setOf_le_add hC ?_ ?_
  · intro v
    rcases eq_or_ne (exteriorPower.map j (eFlow (d := d) ℓ (t + h)) (exteriorPower.ιMulti ℝ j v))
      0 with hX | hX
    · have hsplit0 : exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v) =
          exteriorPower.map j (eFlow (d := d) ℓ (-h))
            (exteriorPower.map j (eFlow (d := d) ℓ (t + h))
              (exteriorPower.ιMulti ℝ j v)) := by
        have heq : eFlow (d := d) ℓ t =
            (eFlow (d := d) ℓ (-h)).comp (eFlow (d := d) ℓ (t + h)) := by
          rw [← eFlow_add, show t + h + -h = t by ring]
        rw [heq, exteriorPower.map_comp, LinearMap.comp_apply]
      rw [hsplit0, hX, map_zero]
      simp only [norm_zero, Real.log_zero]
      linarith
    · have hinj : Function.Injective (exteriorPower.map j (eFlow (d := d) ℓ (-h))) :=
        exteriorPower.map_injective (f := eFlow (d := d) ℓ (-h)) (eFlow (d := d) ℓ h)
          (by rw [← eFlow_add, show -h + h = 0 by ring, eFlow_zero])
      have hXpos : 0 < ‖exteriorPower.map j (eFlow (d := d) ℓ (t + h))
          (exteriorPower.ιMulti ℝ j v)‖ := norm_pos_iff.mpr hX
      have hsplit : exteriorPower.map j (eFlow (d := d) ℓ t) (exteriorPower.ιMulti ℝ j v) =
          exteriorPower.map j (eFlow (d := d) ℓ (-h))
            (exteriorPower.map j (eFlow (d := d) ℓ (t + h))
              (exteriorPower.ιMulti ℝ j v)) := by
        have heq : eFlow (d := d) ℓ t =
            (eFlow (d := d) ℓ (-h)).comp (eFlow (d := d) ℓ (t + h)) := by
          rw [← eFlow_add, show t + h + -h = t by ring]
        rw [heq, exteriorPower.map_comp, LinearMap.comp_apply]
      rw [hsplit]
      have hpos : 0 < ‖exteriorPower.map j (eFlow (d := d) ℓ (-h))
          (exteriorPower.map j (eFlow (d := d) ℓ (t + h))
            (exteriorPower.ιMulti ℝ j v))‖ :=
        norm_pos_iff.mpr (fun h0 => hX (hinj (by rw [h0, map_zero])))
      have hle := eFlow_norm_le_exp_mul_inv (d := d) (j := j) (ℓ := ℓ) hℓ0 hℓd hh
        (exteriorPower.map j (eFlow (d := d) ℓ (t + h)) (exteriorPower.ιMulti ℝ j v))
      have h1 := Real.log_le_log hpos hle
      rw [Real.log_mul (Real.exp_ne_zero _) hXpos.ne', Real.log_exp] at h1
      linarith [h1]
  · rw [hset t]
    exact hbd t

end Submission.FlowDataShift

end
