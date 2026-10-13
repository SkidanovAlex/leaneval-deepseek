/-
# `Work.FTS.RegPkgGal.Der.sup_extG` — the uniform `L^∞`-bound of the extension `g̃`

The extension `g̃ = extG g` of design §4 is `0` on the closed half plane `{z ≤ 0}`, the first
order Taylor jet of `g` for `τ < 0`, and `g` itself for `z > 0, τ ≥ 0`.  This file proves that
`g̃` and its `z`-derivative are uniformly bounded on `[0,∞) × Iθ × [0,S]` under the `RegQ`-class
data of the slices plus the two class hypotheses that the `ℋ⁴`-norm does *not* see:

* `hvan` — the slices vanish on the two angular boundary lines `θ = 0`, `π/2`;
* `hquad` — `|∂_zg| ≤ Q z` on `0 ≤ z ≤ 2` (the linear vanishing of `∂_zg` at the axis).

## Route

* **`z = 0`**: `extG` vanishes identically there (`extG_of_nonpos`), and the slice of the
  extension is `0` on `(-∞,0]`, so its `z`-derivative at `0` is `0` (`R1.extG_hquad`).
* **`z > 0, τ ≥ 0`**: `g̃` is `g`, and the derivative of the extended slice is the derivative of
  the slice of `g` (`deriv` is local and `z > 0`).
* **angular boundary lines** `θ = 0, π/2`: the slice of `g` at that angle is identically `0` by
  `hvan`, so both `g` and its `z`-derivative vanish there.
* **interior** `0 < θ < π/2`: the pointwise interior `L^∞`-`ℋ⁴` trade-off of the `RegQ` class
  (`abs_mixed_le_HkNorm_RegQ`, the pointwise form of `H2.mixed_supAbsO_le`, constant `10`) bounds
  `g` by `10/√(γ-1)·C₀` and `D_zg = z∂_zg` by the same constant.  For `z ≥ 2` the second gives
  `|∂_zg| ≤ 10/√(γ-1)·C₀/z ≤ 10/√(γ-1)·C₀`, and for `0 < z ≤ 2` the class hypothesis `hquad`
  gives `|∂_zg| ≤ 2Q`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegPkgGal.Der.Defs
import Submission.Work.FTS.RegPkgGal.Der.abs_mixed_le_HkNorm_RegQ
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.R1
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.R8
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.LinfQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false
set_option linter.unusedVariables false

theorem sup_extG {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hS : 0 < S)
    (hRQ : ∀ τ ∈ Set.Icc 0 S, Work.FTS.Nonlin.RegQ (Work.FTS.Regularity.pExp α) 4
      (Work.FTS.Regularity.gSlice g τ))
    (hHkn : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ τ ∈ Set.Icc 0 S,
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (Work.FTS.Regularity.gSlice g τ) ≤ C₀)
    (hvan : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0)
    (hquad : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      0 ≤ z → z ≤ 2 → |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Q * z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.RegPkgGal.extG g z θ τ| ≤ M
        ∧ |Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ| ≤ M := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := hHkn
  obtain ⟨Q, hQ0, hQ⟩ := hquad
  -- `pExp α = 3α` sits in `(0,1]`
  have hpα0 : 0 < Work.FTS.Regularity.pExp α := by
    rw [Work.FTS.Regularity.pExp]; linarith
  have hpα1 : Work.FTS.Regularity.pExp α ≤ 1 := by
    rw [Work.FTS.Regularity.pExp]; linarith
  have hKnn : 0 ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hCb0 : 0 ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀ :=
    mul_nonneg hKnn hC₀0
  refine ⟨max (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀) (2 * Q),
    le_trans hCb0 (le_max_left _ _), ?_⟩
  intro τ hτ z θ hz hθ
  have hτ0 : 0 ≤ τ := hτ.1
  have hM1 : 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀
      ≤ max (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀) (2 * Q) :=
    le_max_left _ _
  have hM2 : 2 * Q ≤ max (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀) (2 * Q) :=
    le_max_right _ _
  -- the two pointwise interior bounds of the `RegQ` class, at the slots `(0,0)` and `(1,0)`
  have h00 : ∀ {z' θ' : ℝ}, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      |Work.FTS.Regularity.gSlice g τ z' θ'| ≤
        10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀ := by
    intro z' θ' hz' hθ' hθ''
    have h1 := abs_mixed_le_HkNorm_RegQ (β := Work.FTS.Regularity.pExp α) hpα0 hpα1 (hRQ τ hτ) 0 0
      (by norm_num) hz' hθ' hθ''
    have h2 : 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
        * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (Work.FTS.Regularity.gSlice g τ)
        ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀ :=
      mul_le_mul_of_nonneg_left (hC₀ τ hτ) hKnn
    simpa using le_trans h1 h2
  have h10 : ∀ {z' θ' : ℝ}, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z' θ'| ≤
        (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀) / z' := by
    intro z' θ' hz' hθ' hθ''
    have h1 := abs_mixed_le_HkNorm_RegQ (β := Work.FTS.Regularity.pExp α) hpα0 hpα1 (hRQ τ hτ) 1 0
      (by norm_num) hz' hθ' hθ''
    have h2 : Work.Spaces.mixed 1 0 (Work.FTS.Regularity.gSlice g τ) z' θ'
        = z' * Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z' θ' := rfl
    rw [h2, abs_mul, abs_of_pos hz'] at h1
    have h3 : z' * |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z' θ'| ≤
        10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀ :=
      le_trans h1 (mul_le_mul_of_nonneg_left (hC₀ τ hτ) hKnn)
    rw [le_div_iff₀ hz', mul_comm]
    exact h3
  constructor
  · -- the value bound
    by_cases hz0 : z ≤ 0
    · rw [Work.FTS.RegPkgGal.extG_of_nonpos hz0, abs_zero]
      exact le_trans hCb0 (le_max_left _ _)
    · simp only [not_le] at hz0
      rw [Work.FTS.RegPkgGal.extG_of_pos hz0 hτ0]
      rcases eq_or_lt_of_le hθ.1 with hθz | hθz
      · rw [← hθz, (hvan τ hτ z (le_of_lt hz0)).1, abs_zero]
        exact le_trans hCb0 (le_max_left _ _)
      · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
        · rw [hθp, (hvan τ hτ z (le_of_lt hz0)).2, abs_zero]
          exact le_trans hCb0 (le_max_left _ _)
        · exact le_trans (h00 hz0 hθz hθp) hM1
  · -- the derivative bound
    by_cases hz0 : z = 0
    · rw [hz0, Work.FTS.RegPkgGal.extG_hquad g τ θ, abs_zero]
      exact le_trans hCb0 (le_max_left _ _)
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      -- for `z > 0` and `τ ≥ 0` the extended slice is the slice of `g` near `z`
      have hderiv : Work.Spaces.pz (fun z θ => Work.FTS.RegPkgGal.extG g z θ τ) z θ
          = Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ := by
        have hev : (fun z' => Work.FTS.RegPkgGal.extG g z' θ τ)
            =ᶠ[𝓝 z] (fun z' => Work.FTS.Regularity.gSlice g τ z' θ) := by
          filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
          simp [Work.FTS.RegPkgGal.extG_of_pos hz' hτ0]
        exact hev.deriv_eq
      rw [hderiv]
      rcases eq_or_lt_of_le hθ.1 with hθz | hθz
      · -- `θ = 0`: the slice of `g` is identically zero in `z`
        have hpz0 : Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z 0 = 0 := by
          show deriv (fun z' => Work.FTS.Regularity.gSlice g τ z' 0) z = 0
          have hev : (fun z' => Work.FTS.Regularity.gSlice g τ z' 0) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
            filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
            exact (hvan τ hτ z' (le_of_lt hz')).1
          rw [hev.deriv_eq]
          exact deriv_const z 0
        rw [← hθz, hpz0, abs_zero]
        exact le_trans hCb0 (le_max_left _ _)
      · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
        · -- `θ = π/2`: same
          have hpz0 : Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z (π/2) = 0 := by
            show deriv (fun z' => Work.FTS.Regularity.gSlice g τ z' (π/2)) z = 0
            have hev : (fun z' => Work.FTS.Regularity.gSlice g τ z' (π/2)) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
              filter_upwards [isOpen_Ioi.mem_nhds hzpos] with z' hz'
              exact (hvan τ hτ z' (le_of_lt hz')).2
            rw [hev.deriv_eq]
            exact deriv_const z 0
          rw [hθp, hpz0, abs_zero]
          exact le_trans hCb0 (le_max_left _ _)
        · -- interior angle: `hquad` near the axis, the `D_z`-slot far out
          by_cases hz2 : z ≤ 2
          · have h1 := hQ τ hτ θ hθ z hz hz2
            have h2 : Q * z ≤ 2 * Q := by nlinarith [hQ0, hz, hz2]
            exact le_trans h1 (le_trans h2 hM2)
          · simp only [not_le] at hz2
            have h1 := h10 hzpos hθz hθp
            have h2 : (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀) / z
                ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀ := by
              have h4 : (1:ℝ) / z ≤ 1 := by
                rw [div_le_one hzpos]; linarith
              calc (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀) / z
                  = (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀)
                      * (1 / z) := by ring
                _ ≤ (10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀) * 1 :=
                    mul_le_mul_of_nonneg_left h4 hCb0
                _ = 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * C₀ := by ring
            exact le_trans h1 (le_trans h2 hM1)

end Work.FTS.RegPkgGal.Der
