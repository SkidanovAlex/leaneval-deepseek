/-
# `FTS_RegExport/RXT/StarVopWlInf.lean` — the uniform low-order bound for a `𝒲^{4,∞}`-function

`mixed_two_le_WlInf` is the `W`-side half of `RXT/starVop.lean`: from `WlInfMem α 4 W` and
`α ≤ 1` it gives the uniform pointwise bound

  `|D_z^k D_θ^i W| ≤ 4·WlInf α 4 W`   for `k ≤ 2`, `i ≤ 2`, `z > 0`, `θ ∈ (0,π/2)`.

The ingredients are the two pointwise consequences of `WlInfMem` already available in
`Work.Spaces.WlInf_terms` (`pz_sup_bound`, `pz_Dth_sup_bound`), the elementary bound
`(α + sin 2θ)·sin(2θ)^{α/5} ≤ 2` (valid since `α ≤ 1` and `sin 2θ ≤ 1`), and the Stirling
expansion `D_z² X = z·∂_zX + z²·∂_z²X` (`DzIter_two_eq`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false

/-! ## Part 4 — the uniform `𝒲^{4,∞}`-bound on `D_z^kD_θ^i W`, `k ≤ 2`, `i ≤ 2` -/

/-- The Stirling expansion of `D_z²` in powers of `z`:
`D_z² X = z·∂_zX + z²·∂_z²X`, for a function smooth on the open quadrant. -/
theorem DzIter_two_eq {X : ℝ → ℝ → ℝ} (hX : Work.FTS.EllipticEst.SmoothOpen X) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DzIter 2 X z θ
        = z * Work.Spaces.pzIter 1 X z θ + z ^ 2 * Work.Spaces.pzIter 2 X z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 1 X z' θ)
      (Work.Spaces.pzIter 2 X z θ) z := hX.hasDerivAt_slice_pzIter 1 hθ hz
  have hmul := (hasDerivAt_id z).mul h2
  have hder : deriv (fun z' : ℝ => z' * Work.Spaces.pzIter 1 X z' θ) z
      = 1 * Work.Spaces.pzIter 1 X z θ + z * Work.Spaces.pzIter 2 X z θ := hmul.deriv
  show z * deriv (fun z' : ℝ => z' * Work.Spaces.pzIter 1 X z' θ) z
      = z * Work.Spaces.pzIter 1 X z θ + z ^ 2 * Work.Spaces.pzIter 2 X z θ
  rw [hder]; ring

/-- **The uniform bound on the low-order mixed derivatives of `W`**: from
`WlInfMem α 4 W` and `α ≤ 1`,
`|D_z^kD_θ^i W| ≤ 4·WlInf α 4 W` for `k ≤ 2`, `i ≤ 2`, `z > 0`, `θ ∈ (0,π/2)`.

(For `i = 0` the `𝒲^{4,∞}`-bound is `WlInf/(z+1)^k`; for `i ≥ 1` it carries the extra angular
factor `(α + sin 2θ)·sin(2θ)^{α/5} ≤ 2`; the Stirling expansion of `D_z²` contributes a factor
`2`, whence the constant `4`.) -/
theorem mixed_two_le_WlInf {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {W : ℝ → ℝ → ℝ}
    (hW : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.WlInfMem α 4 W) :
    ∀ k i : ℕ, k ≤ 2 → i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed k i W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W := by
  intro k i hk hi z θ hz hθ0 hθ1
  have hzI : z ∈ Work.Spaces.Iz := hz.le
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, by linarith [Real.pi_pos]⟩
  have hW₀nn : 0 ≤ Work.Spaces.WlInf α 4 W := by
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 W hmem)
      (Work.Spaces.wlThSum_nonneg α 4 W hmem)
  have hzp : (0 : ℝ) < z + 1 := by linarith
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hfac : (α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5) ≤ 2 := by
    have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
    have h2 : Real.sin (2 * θ) ^ (α / 5) ≤ 1 :=
      Real.rpow_le_one hs0.le hs1 (by linarith : (0 : ℝ) ≤ α / 5)
    have h3 : (0 : ℝ) ≤ α + Real.sin (2 * θ) := by linarith
    have h4 : (0 : ℝ) ≤ Real.sin (2 * θ) ^ (α / 5) := Real.rpow_nonneg hs0.le _
    nlinarith
  have hzbd : ∀ k' : ℕ, k' ≤ 2 →
      |Work.Spaces.pzIter k' W z θ| ≤ Work.Spaces.WlInf α 4 W / (z + 1) ^ k' :=
    fun k' hk' => Work.Spaces.pz_sup_bound α 4 W hmem k' (by omega) z θ hzI hθI
  have hjbd : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ k' : ℕ, k' ≤ 2 →
      |Work.Spaces.pzIter k' (Work.Spaces.DthIter j W) z θ|
        ≤ 2 * Work.Spaces.WlInf α 4 W / (z + 1) ^ k' := by
    intro j hj hj2 k' hk'
    have h := Work.Spaces.pz_Dth_sup_bound α hα 4 W hmem j k' hj (by omega) z θ hzI hθI
    have hpos : (0 : ℝ) < (z + 1) ^ k' := by positivity
    calc |Work.Spaces.pzIter k' (Work.Spaces.DthIter j W) z θ|
        ≤ Work.Spaces.WlInf α 4 W / (z + 1) ^ k'
            * ((α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5)) := h
      _ = Work.Spaces.WlInf α 4 W
            * ((α + Real.sin (2 * θ)) * Real.sin (2 * θ) ^ (α / 5)) / (z + 1) ^ k' := by ring
      _ ≤ Work.Spaces.WlInf α 4 W * 2 / (z + 1) ^ k' := by
          refine div_le_div_of_nonneg_right ?_ hpos.le
          exact mul_le_mul_of_nonneg_left hfac hW₀nn
      _ = 2 * Work.Spaces.WlInf α 4 W / (z + 1) ^ k' := by ring
  have key1 : ∀ (X : ℝ → ℝ → ℝ) (M : ℝ),
      |Work.Spaces.pzIter 1 X z θ| ≤ M / (z + 1) → |Work.Spaces.DzIter 1 X z θ| ≤ M := by
    intro X M hX
    have h1 : |Work.Spaces.DzIter 1 X z θ| ≤ (z + 1) * |Work.Spaces.pzIter 1 X z θ| := by
      rw [show Work.Spaces.DzIter 1 X z θ = z * Work.Spaces.pzIter 1 X z θ from rfl,
        abs_mul, abs_of_nonneg hz.le]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    calc |Work.Spaces.DzIter 1 X z θ| ≤ (z + 1) * |Work.Spaces.pzIter 1 X z θ| := h1
      _ ≤ (z + 1) * (M / (z + 1)) := mul_le_mul_of_nonneg_left hX hzp.le
      _ = M := by field_simp
  have key2 : ∀ (X : ℝ → ℝ → ℝ) (M : ℝ), Work.FTS.EllipticEst.SmoothOpen X →
      |Work.Spaces.pzIter 1 X z θ| ≤ M / (z + 1) →
      |Work.Spaces.pzIter 2 X z θ| ≤ M / (z + 1) ^ 2 →
      |Work.Spaces.DzIter 2 X z θ| ≤ 2 * M := by
    intro X M hXs hX1 hX2
    have h1 : |z * Work.Spaces.pzIter 1 X z θ| ≤ M := by
      have ha : |z * Work.Spaces.pzIter 1 X z θ|
          ≤ (z + 1) * |Work.Spaces.pzIter 1 X z θ| := by
        rw [abs_mul, abs_of_nonneg hz.le]
        exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      calc |z * Work.Spaces.pzIter 1 X z θ| ≤ (z + 1) * |Work.Spaces.pzIter 1 X z θ| := ha
        _ ≤ (z + 1) * (M / (z + 1)) := mul_le_mul_of_nonneg_left hX1 hzp.le
        _ = M := by field_simp
    have h2 : |z ^ 2 * Work.Spaces.pzIter 2 X z θ| ≤ M := by
      have ha : |z ^ 2 * Work.Spaces.pzIter 2 X z θ|
          ≤ (z + 1) ^ 2 * |Work.Spaces.pzIter 2 X z θ| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ z ^ 2)]
        exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg _)
      calc |z ^ 2 * Work.Spaces.pzIter 2 X z θ|
          ≤ (z + 1) ^ 2 * |Work.Spaces.pzIter 2 X z θ| := ha
        _ ≤ (z + 1) ^ 2 * (M / (z + 1) ^ 2) :=
            mul_le_mul_of_nonneg_left hX2 (by positivity)
        _ = M := by field_simp
    rw [DzIter_two_eq hXs z θ hz hθ0 hθ1]
    calc |z * Work.Spaces.pzIter 1 X z θ + z ^ 2 * Work.Spaces.pzIter 2 X z θ|
        ≤ |z * Work.Spaces.pzIter 1 X z θ| + |z ^ 2 * Work.Spaces.pzIter 2 X z θ| :=
          abs_add_le _ _
      _ ≤ M + M := add_le_add h1 h2
      _ = 2 * M := by ring
  interval_cases k
  · interval_cases i
    · show |W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W
      have h := hzbd 0 (by norm_num)
      simp only [pow_zero, div_one, Work.Spaces.pzIter_zero] at h
      linarith [h, hW₀nn]
    · show |Work.Spaces.DthIter 1 W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W
      have h := hjbd 1 (by norm_num) (by norm_num) 0 (by norm_num)
      simp only [pow_zero, div_one, Work.Spaces.pzIter_zero] at h
      linarith [h, hW₀nn]
    · show |Work.Spaces.DthIter 2 W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W
      have h := hjbd 2 (by norm_num) (by norm_num) 0 (by norm_num)
      simp only [pow_zero, div_one, Work.Spaces.pzIter_zero] at h
      linarith [h, hW₀nn]
  · by_cases hi0 : i = 0
    · subst hi0
      show |Work.Spaces.DzIter 1 W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W
      have h := hzbd 1 (by norm_num)
      have h2 := key1 W (Work.Spaces.WlInf α 4 W) (by simpa using h)
      linarith [h2, hW₀nn]
    · have hi1 : 1 ≤ i := by omega
      show |Work.Spaces.DzIter 1 (Work.Spaces.DthIter i W) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 W
      have h := hjbd i hi1 hi 1 (by norm_num)
      have h2 := key1 (Work.Spaces.DthIter i W) (2 * Work.Spaces.WlInf α 4 W) (by simpa using h)
      linarith [h2, hW₀nn]
  · by_cases hi0 : i = 0
    · subst hi0
      show |Work.Spaces.DzIter 2 W z θ| ≤ 4 * Work.Spaces.WlInf α 4 W
      have h1 := hzbd 1 (by norm_num)
      have h2 := hzbd 2 (by norm_num)
      have h3 := key2 W (Work.Spaces.WlInf α 4 W) hW (by simpa using h1) (by simpa using h2)
      linarith [h3, hW₀nn]
    · have hi1 : 1 ≤ i := by omega
      show |Work.Spaces.DzIter 2 (Work.Spaces.DthIter i W) z θ|
        ≤ 4 * Work.Spaces.WlInf α 4 W
      have h1 := hjbd i hi1 hi 1 (by norm_num)
      have h2 := hjbd i hi1 hi 2 (by norm_num)
      have h3 := key2 (Work.Spaces.DthIter i W) (2 * Work.Spaces.WlInf α 4 W)
        (hW.DthIter i) (by simpa using h1) (by simpa using h2)
      linarith [h3, hW₀nn]


end Work.FTS_RegExport.RXT
