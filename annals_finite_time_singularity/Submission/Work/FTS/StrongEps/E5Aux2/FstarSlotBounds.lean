import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FM.Defs
import Submission.Work.FM.Core
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.FTS.Nonlinear.FstarPkg.Fstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux2

/-
Sharp pointwise bounds for the fixed profile `F_* = Construction.Fstar α` and its slots,
in terms of the radial factor `hKer z = z/(1+z)^2` (`Work.Spaces.hKer`).

ROUTE.  `Fstar_eq_factored` (`Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored`) gives
`Fstar α z θ = (2α/c α) * Gam α θ * hKer z`, `Dz_Fstar_eq_Hz` (`FstarPkg.Dz_Fstar_eq_Hz`)
gives `Dz (Fstar α) z θ = (α/c α) * Gam α θ * Hz z` with `Hz z = 2z(1-z)/(1+z)^3`, and
`pzIter_DthIter_Fstar_eq α 1 0` gives `Dth (Fstar α) z θ = (2α/c α) * dthU (Gam α) θ * hKer z`.
Then `|hKer z| ≤ 1/(1+z)` is trivial, `|Hz z| ≤ 2*hKer z` for `z ≥ 0`, `Gam_bounds` gives
`0 ≤ Gam ≤ 1`, `c_bounds` gives `1/c ≤ 10`, and `Work.Spaces.dthU_Gam_le 1 le_rfl α hα hα1 θ hθ`
gives `|dthU (Gam α) θ| ≤ α * tBound 0 0 * Gam α θ` with `tBound 0 0 ≥ 0`.
The templates `Fstar_abs_le`, `DzFstar_abs_le`, `DthFstar_abs_le` in
`Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.FstarSlotPt` prove the same
statements with `1/(1+z)` instead of `hKer z` — adapt them.
The last conjunct is `FK (Fstar α) z = α * FM.Fstar z = 2α * hKer z` exactly
(`FK F z = ∫ θ in Iθ, F z θ * K θ` and `c α = ∫ θ in Iθ, Gam α θ * K θ`, use
`MeasureTheory.integral_const_mul`).
-/

/-! ## Elementary facts about the radial factor and the angular interval -/

/-- The radial factor `hKer z = z/(1+z)²` is nonnegative for `z > 0`. -/
lemma hKer_nonneg_of_pos {z : ℝ} (hz : 0 < z) : 0 ≤ Work.Spaces.hKer z := by
  rw [Work.Spaces.hKer_apply]
  exact div_nonneg hz.le (by positivity)

/-- For `z > 0` the absolute value of `hKer z` is `hKer z` itself. -/
lemma abs_hKer_of_pos {z : ℝ} (hz : 0 < z) :
    |Work.Spaces.hKer z| = Work.Spaces.hKer z :=
  abs_of_nonneg (hKer_nonneg_of_pos hz)

/-- The radial factor `Hz(z) = 2z(1-z)/(1+z)³` of `D_zF_*` obeys the sharp bound
`|Hz(z)| ≤ 2 hKer z = 2z/(1+z)²` for `z > 0` (sharper than the `2/(1+z)` used elsewhere). -/
lemma Hz_abs_le_hKer {z : ℝ} (hz : 0 < z) :
    |Work.FTS.Nonlinear.FstarPkg.Hz z| ≤ 2 * Work.Spaces.hKer z := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [Work.FTS.Nonlinear.FstarPkg.Hz, Work.Spaces.hKer_apply, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < (1 + z) ^ 3)]
  have hrew : 2 * (z / (1 + z) ^ 2) = 2 * z / (1 + z) ^ 2 := by ring
  rw [hrew, div_le_div_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 3)
    (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  have hnum : |2 * z * (1 - z)| ≤ 2 * z * (1 + z) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hz.le]
    exact mul_le_mul_of_nonneg_left
      (abs_le.mpr ⟨by linarith, by linarith⟩) (by positivity)
  calc |2 * z * (1 - z)| * (1 + z) ^ 2 ≤ (2 * z * (1 + z)) * (1 + z) ^ 2 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = 2 * z * (1 + z) ^ 3 := by ring

/-- `cos θ ≥ 0` for `θ ∈ Iθ = [0, π/2]`. -/
lemma cos_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩

/-- `sin (2θ) ≥ 0` for `θ ∈ Iθ = [0, π/2]`. -/
lemma sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- On `Iθ` the angular weight `K θ = 3 sin θ cos²θ` converts `|∂_θ F|` into
`(3/2) cos θ` times the `D_θ`-slot `|sin(2θ) ∂_θF|`. -/
lemma K_mul_abs_pth_eq (F : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.K θ * |Work.Spaces.pth F z θ|
      = (3 / 2) * Real.cos θ * |Real.sin (2 * θ) * Work.Spaces.pth F z θ| := by
  have hsin := sin_two_nonneg_of_mem_Iθ hθ
  rw [Work.Spaces.K, abs_mul, abs_of_nonneg hsin, Real.sin_two_mul]
  ring

/-- `|D_θF_*(z,θ)| ≤ 20 tBound 0 0 · hKer z` for `0 < α ≤ 1`, `z > 0`, `θ ∈ Iθ`: the sharp
`hKer`-version of `FstarSlotPt.DthFstar_abs_le`. -/
lemma DthFstar_abs_le_hKer {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
      ≤ 20 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z := by
  have hid : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      = (2 * α / Work.Spaces.c α) * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          * Work.Spaces.hKer z := by
    have h := Work.FTS.Nonlinear.FstarPkg.pzIter_DthIter_Fstar_eq α 1 0 z θ
    simpa using h
  rw [hid, abs_mul, abs_mul, abs_hKer_of_pos hz]
  have hc := Work.FTS.Nonlinear.FstarPkg.Fstar_coef_le α hα hα1
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hT : 0 ≤ Work.Spaces.tBound 0 0 := Work.Spaces.tBound_nonneg 0 0
  have hK : 0 ≤ Work.Spaces.hKer z := hKer_nonneg_of_pos hz
  have hdth : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * Work.Spaces.tBound 0 0 := by
    have h := Work.Spaces.dthU_Gam_le 1 le_rfl α hα hα1 θ hθ
    have h1 : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ := by simpa using h
    calc |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        ≤ α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ := h1
      _ ≤ α * Work.Spaces.tBound 0 0 * 1 :=
          mul_le_mul_of_nonneg_left hG.2 (mul_nonneg hα.le hT)
      _ = α * Work.Spaces.tBound 0 0 := by ring
  calc (|2 * α / Work.Spaces.c α|
        * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|) * Work.Spaces.hKer z
      ≤ ((20 * α) * (α * Work.Spaces.tBound 0 0)) * Work.Spaces.hKer z :=
        mul_le_mul (mul_le_mul hc hdth (abs_nonneg _) (mul_nonneg (by norm_num) hα.le))
          le_rfl hK (by positivity)
    _ = 20 * (α ^ 2) * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z := by ring
    _ ≤ 20 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z := by
        have hsq : α ^ 2 ≤ 1 := by nlinarith [hα.le, hα1]
        have h1 : 20 * (α ^ 2) * Work.Spaces.tBound 0 0 ≤ 20 * 1 * Work.Spaces.tBound 0 0 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) hT
        calc 20 * (α ^ 2) * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z
            ≤ 20 * 1 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z :=
              mul_le_mul_of_nonneg_right h1 hK
          _ = 20 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z := by ring

theorem FstarSlotBounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {z θ : ℝ}, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Fstar α z θ| ≤ C * (z / (1 + z) ^ 2) ∧
      |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        ≤ C * (z / (1 + z) ^ 2) ∧
      |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ C * (z / (1 + z) ^ 2) ∧
      Work.Spaces.K θ * |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        ≤ C * (z / (1 + z) ^ 2) * Real.cos θ ∧
      |Work.Construction.FK (Work.Construction.Fstar α) z| ≤ C * (z / (1 + z) ^ 2) := by
  refine ⟨30 * (Work.Spaces.tBound 0 0 + 1), by
    have h := Work.Spaces.tBound_nonneg 0 0; linarith, ?_⟩
  rintro α hαI z θ hz hθ
  obtain ⟨hα, hα1⟩ := hαI
  have hT : 0 ≤ Work.Spaces.tBound 0 0 := Work.Spaces.tBound_nonneg 0 0
  have hK : 0 ≤ Work.Spaces.hKer z := hKer_nonneg_of_pos hz
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hcoef := Work.FTS.Nonlinear.FstarPkg.Fstar_coef_le α hα hα1
  have hcoefZ : |α / Work.Spaces.c α| ≤ 10 * α := by
    have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  -- the slot `F_*`
  have hF : |Work.Construction.Fstar α z θ|
      ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z := by
    simp only [Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored]
    rw [abs_mul, abs_mul, abs_of_nonneg hG.1, abs_hKer_of_pos hz]
    have h20 : 20 * α ≤ 30 * (Work.Spaces.tBound 0 0 + 1) := by nlinarith
    calc (|2 * α / Work.Spaces.c α| * Work.Spaces.Gam α θ) * Work.Spaces.hKer z
        ≤ ((20 * α) * 1) * Work.Spaces.hKer z :=
          mul_le_mul (mul_le_mul hcoef hG.2 hG.1 (mul_nonneg (by norm_num) hα.le)) le_rfl hK
            (by positivity)
      _ = 20 * α * Work.Spaces.hKer z := by ring
      _ ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z :=
          mul_le_mul_of_nonneg_right h20 hK
  -- the slot `D_θF_*`
  have hDth := DthFstar_abs_le_hKer hα hα1 hz hθ
  have h2 : |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
      ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z := by
    have heq : |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        = |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| := by
      rw [Work.Spaces.Dth]
    rw [heq]
    have h20 : 20 * Work.Spaces.tBound 0 0 ≤ 30 * (Work.Spaces.tBound 0 0 + 1) := by
      linarith
    exact le_trans hDth (mul_le_mul_of_nonneg_right h20 hK)
  -- the slot `D_zF_*`
  have h3 : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
      ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z := by
    rw [Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα (by linarith : (-1 : ℝ) < z),
      abs_mul, abs_mul, abs_of_nonneg hG.1]
    have hHz := Hz_abs_le_hKer hz
    have h20 : 20 * α ≤ 30 * (Work.Spaces.tBound 0 0 + 1) := by nlinarith
    calc |α / Work.Spaces.c α| * (Work.Spaces.Gam α θ
          * |Work.FTS.Nonlinear.FstarPkg.Hz z|)
        ≤ (10 * α) * (1 * (2 * Work.Spaces.hKer z)) :=
          mul_le_mul hcoefZ (mul_le_mul hG.2 hHz (abs_nonneg _) (by norm_num))
            (mul_nonneg hG.1 (abs_nonneg _)) (mul_nonneg (by norm_num) hα.le)
      _ = 20 * α * Work.Spaces.hKer z := by ring
      _ ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z :=
          mul_le_mul_of_nonneg_right h20 hK
  -- the slot `K θ · |∂_θF_*|`
  have h4 : Work.Spaces.K θ * |Work.Spaces.pth (Work.Construction.Fstar α) z θ|
      ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z * Real.cos θ := by
    rw [K_mul_abs_pth_eq (Work.Construction.Fstar α) hθ]
    have heq : |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        = |Work.Spaces.Dth (Work.Construction.Fstar α) z θ| := by
      rw [Work.Spaces.Dth]
    rw [heq]
    have hcos := cos_nonneg_of_mem_Iθ hθ
    calc (3 / 2) * Real.cos θ * |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
        ≤ (3 / 2) * Real.cos θ * (20 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z) :=
          mul_le_mul_of_nonneg_left hDth (mul_nonneg (by norm_num) hcos)
      _ = 30 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z * Real.cos θ := by ring
      _ ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z * Real.cos θ := by
          have h1 : 30 * Work.Spaces.tBound 0 0 * Work.Spaces.hKer z
              ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z :=
            mul_le_mul_of_nonneg_right (by linarith) hK
          exact mul_le_mul_of_nonneg_right h1 hcos
  -- the slot `(F_*, K)_{L²_θ}`
  have h5 : |Work.Construction.FK (Work.Construction.Fstar α) z|
      ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z := by
    rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]
    have hz2 : (2 : ℝ) * z / (1 + z) ^ 2 = 2 * Work.Spaces.hKer z := by
      rw [Work.Spaces.hKer_apply]; ring
    rw [hz2, abs_of_nonneg (mul_nonneg hα.le (mul_nonneg (by norm_num) hK))]
    have h2le : (2 : ℝ) ≤ 30 * (Work.Spaces.tBound 0 0 + 1) := by linarith
    calc α * (2 * Work.Spaces.hKer z) ≤ 1 * (2 * Work.Spaces.hKer z) :=
          mul_le_mul_of_nonneg_right hα1 (mul_nonneg (by norm_num) hK)
      _ = 2 * Work.Spaces.hKer z := by ring
      _ ≤ 30 * (Work.Spaces.tBound 0 0 + 1) * Work.Spaces.hKer z :=
          mul_le_mul_of_nonneg_right h2le hK
  exact ⟨hF, h2, h3, h4, h5⟩

end Work.FTS.StrongEps.E5Aux2
