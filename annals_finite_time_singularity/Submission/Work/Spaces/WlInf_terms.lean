/-
Copyright: work module for the Elgindi finite-time singularity project.

# Extracting bounds from the `W^{l,∞}`-norm

This file provides the pointwise consequences of membership in `𝒲^{l,∞}` that are
used whenever the `𝒲^{l,∞}`-norm serves as the "bounded coefficient" norm in a
product rule or a transport estimate:

* `WlInf_z_bound`      : `|(z+1)^k ∂_z^k f| ≤ |f|_𝒲` for `k ≤ l`;
* `WlInf_mixed_bound`  : `|(z+1)^k ∂_z^k D_θ^j f · sin(2θ)^{-α/5}/(α+sin(2θ))| ≤ |f|_𝒲`
  for `1 ≤ j`, `k + j ≤ l`;
* `pz_sup_bound`       : `|∂_z^k f| ≤ |f|_𝒲 (1+z)^{-k}`;
* `pz_Dth_sup_bound`   : `|∂_z^k D_θ^j f| ≤ |f|_𝒲 (1+z)^{-k} (α+sin(2θ)) sin(2θ)^{α/5}`.

Also recorded here: `D_θ^j f` vanishes identically where `sin(2θ) = 0` (for `j ≥ 1`),
which is what makes the last bound valid at the angular boundary.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- The `L^∞`-norm on the domain is nonnegative whenever it is honest. -/
theorem supAbs_nonneg {g : ℝ → ℝ → ℝ} (h : SupFinite g) : 0 ≤ supAbs g :=
  le_trans (abs_nonneg _) (abs_le_supAbs zero_mem_Iz zero_mem_Iθ h)

/-- `D_θ^j f` vanishes identically where `sin(2θ) = 0`, for `j ≥ 1`. -/
theorem DthIter_eq_zero_of_sin_eq_zero (f : ℝ → ℝ → ℝ) (j : ℕ) {θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) (z : ℝ) : DthIter (j + 1) f z θ = 0 := by
  rw [DthIter_succ]
  simp [Dth, hθ]

/-- `∂_z^k D_θ^j f` vanishes identically where `sin(2θ) = 0` (for `j ≥ 1`). -/
theorem pzIter_DthIter_eq_zero_of_sin_eq_zero (f : ℝ → ℝ → ℝ) (j : ℕ) {θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) (k : ℕ) :
    ∀ z : ℝ, pzIter k (DthIter (j + 1) f) z θ = 0 := by
  induction k with
  | zero => intro z; exact DthIter_eq_zero_of_sin_eq_zero f j hθ z
  | succ k ih =>
      intro z
      rw [pzIter_succ, pz]
      have : (fun z' => pzIter k (DthIter (j + 1) f) z' θ) = fun _ => (0 : ℝ) := funext ih
      rw [this]
      simp

/-- `D_θ^j f` vanishes on the angular boundary `θ = 0` for `j ≥ 1`. -/
theorem DthIter_apply_zero (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : DthIter (j + 1) f z 0 = 0 :=
  DthIter_eq_zero_of_sin_eq_zero f j (by simp) z

/-- `D_θ^j f` vanishes on the angular boundary `θ = π/2` for `j ≥ 1`. -/
theorem DthIter_apply_pi_half (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    DthIter (j + 1) f z (π / 2) = 0 :=
  DthIter_eq_zero_of_sin_eq_zero f j (by
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]) z

/-- The first sum inside `WlInf` is nonnegative. -/
theorem wlZSum_nonneg (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f) :
    0 ≤ ∑ k ∈ Finset.range (l + 1), supAbs (fun z θ => (z + 1) ^ k * pzIter k f z θ) :=
  Finset.sum_nonneg fun k hk =>
    supAbs_nonneg (hmem.1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

/-- The second sum inside `WlInf` is nonnegative. -/
theorem wlThSum_nonneg (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f) :
    0 ≤ ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        if 1 ≤ j ∧ k + j ≤ l then
          supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0 := by
  refine Finset.sum_nonneg fun j hj => Finset.sum_nonneg
    (f := fun k => if 1 ≤ j ∧ k + j ≤ l then
        supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)
    fun k hk => ?_
  by_cases h : 1 ≤ j ∧ k + j ≤ l
  · rw [if_pos h]
    exact supAbs_nonneg (hmem.2 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) h.1 h.2)
  · rw [if_neg h]

/-- Pointwise bound from the first (radial) sum of the `𝒲^{l,∞}`-norm. -/
theorem WlInf_z_bound (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f)
    (k : ℕ) (hk : k ≤ l) (z θ : ℝ) (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |(z + 1) ^ k * pzIter k f z θ| ≤ WlInf α l f := by
  have hmem' : k ∈ Finset.range (l + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  have h1 : supAbs (fun z θ => (z + 1) ^ k * pzIter k f z θ)
      ≤ ∑ a ∈ Finset.range (l + 1), supAbs (fun z θ => (z + 1) ^ a * pzIter a f z θ) := by
    refine Finset.single_le_sum
      (f := fun a => supAbs (fun z θ => (z + 1) ^ a * pzIter a f z θ)) ?_ hmem'
    intro a ha
    exact supAbs_nonneg (hmem.1 a (Nat.le_of_lt_succ (Finset.mem_range.mp ha)))
  have h2 : |(z + 1) ^ k * pzIter k f z θ|
      ≤ supAbs (fun z θ => (z + 1) ^ k * pzIter k f z θ) :=
    abs_le_supAbs hz hθ (hmem.1 k hk)
  rw [WlInf]
  exact le_trans h2 (le_trans h1 (le_add_of_nonneg_right (wlThSum_nonneg α l f hmem)))

/-- Pointwise bound from the second (angular) sum of the `𝒲^{l,∞}`-norm. -/
theorem WlInf_mixed_bound (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f)
    (j k : ℕ) (hj : 1 ≤ j) (hjk : k + j ≤ l) (z θ : ℝ) (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |(z + 1) ^ k * pzIter k (DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ WlInf α l f := by
  have hj' : j ∈ Finset.range (l + 1) := Finset.mem_range.mpr (by omega)
  have hk' : k ∈ Finset.range (l + 1) := Finset.mem_range.mpr (by omega)
  have h0 : j ≤ l := by omega
  have hmemj := hmem.2 j h0
  have h1 : |(z + 1) ^ k * pzIter k (DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
      ≤ supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
    abs_le_supAbs hz hθ (hmemj k (by omega) hj hjk)
  have hinner : supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ ∑ b ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ b + j ≤ l then
            supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter j f) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := by
    have hif : (if 1 ≤ j ∧ k + j ≤ l then
        supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)
        = supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := if_pos ⟨hj, hjk⟩
    rw [← hif]
    refine Finset.single_le_sum
      (f := fun b => if 1 ≤ j ∧ b + j ≤ l then
          supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) ?_ hk'
    intro b hb
    by_cases h : 1 ≤ j ∧ b + j ≤ l
    · rw [if_pos h]
      exact supAbs_nonneg (hmemj b (Nat.le_of_lt_succ (Finset.mem_range.mp hb)) h.1 h.2)
    · rw [if_neg h]
  have houter : (∑ b ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ b + j ≤ l then
            supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter j f) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
      ≤ ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1),
          (if 1 ≤ a ∧ b + a ≤ l then
            supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter a f) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := by
    refine Finset.single_le_sum
      (f := fun a => ∑ b ∈ Finset.range (l + 1),
          (if 1 ≤ a ∧ b + a ≤ l then
            supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter a f) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)) ?_ hj'
    intro a ha
    refine Finset.sum_nonneg
      (f := fun b => if 1 ≤ a ∧ b + a ≤ l then
          supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter a f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) ?_
    intro b hb
    by_cases h : 1 ≤ a ∧ b + a ≤ l
    · rw [if_pos h]
      exact supAbs_nonneg (hmem.2 a (Nat.le_of_lt_succ (Finset.mem_range.mp ha))
        b (Nat.le_of_lt_succ (Finset.mem_range.mp hb)) h.1 h.2)
    · rw [if_neg h]
  rw [WlInf]
  exact le_trans h1 (le_trans hinner (le_trans houter (le_add_of_nonneg_left (wlZSum_nonneg α l f hmem))))

/-- Unweighted form of the radial bound: `|∂_z^k f| ≤ |f|_𝒲 (1+z)^{-k}`. -/
theorem pz_sup_bound (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f)
    (k : ℕ) (hk : k ≤ l) (z θ : ℝ) (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |pzIter k f z θ| ≤ WlInf α l f / (z + 1) ^ k := by
  have hz1 : (0 : ℝ) < z + 1 := by
    have hz0 : (0 : ℝ) ≤ z := hz
    linarith
  have hpow : (0 : ℝ) < (z + 1) ^ k := pow_pos hz1 k
  have h1 := WlInf_z_bound α l f hmem k hk z θ hz hθ
  rw [abs_mul, abs_of_pos hpow] at h1
  rw [le_div_iff₀ hpow]
  calc |pzIter k f z θ| * (z + 1) ^ k = (z + 1) ^ k * |pzIter k f z θ| := by ring
    _ ≤ WlInf α l f := h1

/-- Unweighted form of the angular bound:
`|∂_z^k D_θ^j f| ≤ |f|_𝒲 (1+z)^{-k} (α+sin(2θ)) sin(2θ)^{α/5}` for `j ≥ 1`. -/
theorem pz_Dth_sup_bound (α : ℝ) (hα : 0 < α) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f)
    (j k : ℕ) (hj : 1 ≤ j) (hjk : k + j ≤ l) (z θ : ℝ) (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |pzIter k (DthIter j f) z θ| ≤ WlInf α l f / (z + 1) ^ k
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hα5 : (0 : ℝ) < α / 5 := by linarith
  have hz1 : (0 : ℝ) < z + 1 := by
    have hz0 : (0 : ℝ) ≤ z := hz
    linarith
  have hpow : (0 : ℝ) < (z + 1) ^ k := pow_pos hz1 k
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2]
  rcases eq_or_lt_of_le hsin0 with hs | hs
  · rw [← hs, Real.zero_rpow (ne_of_gt hα5),
      pzIter_DthIter_eq_zero_of_sin_eq_zero f j' hs.symm k z, abs_zero]
    simp
  · have hθpos : (0 : ℝ) < α + Real.sin (2 * θ) := by linarith
    have hweighted := WlInf_mixed_bound α l f hmem (j' + 1) k (by omega) hjk z θ hz hθ
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hpow,
      abs_of_nonneg (Real.rpow_nonneg hsin0 _), abs_of_pos hθpos] at hweighted
    have hrpow : (Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5) = 1 := by
      rw [← Real.rpow_add hs]
      ring_nf
      simp
    have hstep : (z + 1) ^ k * |pzIter k (DthIter (j' + 1) f) z θ| ≤
        WlInf α l f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      have h2 : (z + 1) ^ k * |pzIter k (DthIter (j' + 1) f) z θ|
          * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ WlInf α l f * (α + Real.sin (2 * θ)) := by
        rw [div_le_iff₀ hθpos] at hweighted
        exact hweighted
      calc (z + 1) ^ k * |pzIter k (DthIter (j' + 1) f) z θ|
          = ((z + 1) ^ k * |pzIter k (DthIter (j' + 1) f) z θ|
              * (Real.sin (2 * θ)) ^ (-(α / 5))) * (Real.sin (2 * θ)) ^ (α / 5) := by
            rw [mul_assoc, hrpow, mul_one]
        _ ≤ (WlInf α l f * (α + Real.sin (2 * θ))) * (Real.sin (2 * θ)) ^ (α / 5) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hsin0 _)
        _ = WlInf α l f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
    have hfinal : |pzIter k (DthIter (j' + 1) f) z θ| ≤
        WlInf α l f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          / (z + 1) ^ k := by
      rw [le_div_iff₀ hpow]
      calc |pzIter k (DthIter (j' + 1) f) z θ| * (z + 1) ^ k
          = (z + 1) ^ k * |pzIter k (DthIter (j' + 1) f) z θ| := by ring
        _ ≤ WlInf α l f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := hstep
    calc |pzIter k (DthIter (j' + 1) f) z θ|
        ≤ WlInf α l f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            / (z + 1) ^ k := hfinal
      _ = WlInf α l f / (z + 1) ^ k
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring

end Work.Spaces
