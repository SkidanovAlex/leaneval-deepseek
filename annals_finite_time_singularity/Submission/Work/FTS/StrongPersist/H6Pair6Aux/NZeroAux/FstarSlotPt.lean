import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.Nonlinear.FstarPkg.Fstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.DthFstar_W
import Submission.Work.FTS.Nonlinear.FstarPkg.DzFstar_W

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FstarSlotPt`: the pointwise slot bound for `F_*`, `D_θF_*` and `D_zF_*`

For every `0 < α ≤ 1`, every `r > 0` and every `θ ∈ Iθ`,

  `F_*(r,θ)² + (D_θF_*)(r,θ)² + (D_zF_*)(r,θ)² ≤ C α² (1+r)^{-2}`

with a universal constant `C`.

## Mathematics

Everything follows from the *separation of variables* of the fundamental profile
(paper tex 1334)

  `F_*(z,θ) = (2α/c(α)) · Γ(θ) · h(z)`,   `h(z) = z/(1+z)²`,   `Γ(θ) = (sinθ cos²θ)^{α/3}`,

and from its two associates

* `D_θF_*(z,θ) = (2α/c) · D_θΓ(θ) · h(z)` — the angular operator `D_θ` acts on `Γ` only
  (`FstarPkg.pzIter_DthIter_Fstar_eq` at `j = 1`, `k = 0`);
* `D_zF_*(z,θ) = (α/c) · Γ(θ) · H(z)`, `H(z) = 2z(1-z)/(1+z)³` — the radial operator acts on
  the radial factor only (`FstarPkg.Dz_Fstar_eq_Hz`).

The elementary inputs are

* the radial bounds `|h(z)| ≤ 1/(1+z)` and `|H(z)| ≤ 2/(1+z)` for `z ≥ 0` (proved here by
  elementary algebra);
* the angular bounds `0 ≤ Γ ≤ 1` (`Spaces.Gam_bounds`) and `|D_θΓ| ≤ α · tBound 0 0`
  (`Spaces.dthU_Gam_le`, since `D_θΓ = α · (cos 2θ - 1/3) · Γ`);
* the normalisation `1/10 ≤ c(α) ≤ 10` (`Spaces.c_bounds`).

Two powers of `α` are then available in every slot: one from the prefactor `2α/c`, and a
second in the `D_θ`-slot because the angular derivative costs a factor `α`; in the `F_*`- and
`D_zF_*`-slots the second power comes from `α ≤ 1` (`α² ≤ α`).  The decay `(1+r)^{-2}` is
paid by the radial factors, which contribute `(1+r)^{-1}` in every slot; squaring turns this
into the required `(1+r)^{-2}`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux

open scoped Real Topology

/-! ## Elementary bounds for the two radial factors -/

/-- `|h(z)| ≤ 1/(1+z)` for `h(z) = z/(1+z)²`, `z ≥ 0`. -/
lemma hKer_abs_le {z : ℝ} (hz : 0 ≤ z) : |Work.Spaces.hKer z| ≤ 1 / (1 + z) := by
  have h1z : 0 < 1 + z := by linarith
  rw [Work.Spaces.hKer_apply, abs_of_nonneg (div_nonneg hz (by positivity))]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2) (by positivity : (0:ℝ) < 1 + z)]
  nlinarith

/-- `|H(z)| ≤ 2/(1+z)` for `H(z) = 2z(1-z)/(1+z)³`, `z ≥ 0`. -/
lemma Hz_abs_le {z : ℝ} (hz : 0 ≤ z) : |Work.FTS.Nonlinear.FstarPkg.Hz z| ≤ 2 / (1 + z) := by
  have h1z : 0 < 1 + z := by linarith
  rw [Work.FTS.Nonlinear.FstarPkg.Hz, abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 + z) ^ 3)]
  have hnum : |2 * z * (1 - z)| ≤ 2 * (1 + z) ^ 2 := by
    have h1 : |2 * z * (1 - z)| = 2 * z * |1 - z| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hz, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [h1]
    have h2 : |1 - z| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
    calc 2 * z * |1 - z| ≤ 2 * z * (1 + z) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 2 * (1 + z) ^ 2 := by nlinarith
  calc |2 * z * (1 - z)| / (1 + z) ^ 3 ≤ (2 * (1 + z) ^ 2) / (1 + z) ^ 3 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 2 / (1 + z) := by
        rw [div_eq_div_iff (by positivity : (1 + z) ^ 3 ≠ 0) (by positivity : (1 + z) ≠ 0)]
        ring

/-! ## The three slot bounds -/

/-- `|F_*(z,θ)| ≤ 20 α /(1+z)`: the prefactor `2α/c ≤ 20α`, the angular factor `Γ ≤ 1` and
the radial factor `|h(z)| ≤ 1/(1+z)`. -/
lemma Fstar_abs_le {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar α z θ| ≤ 20 * α * (1 / (1 + z)) := by
  simp only [Work.FTS.Nonlinear.FstarPkg.Fstar_eq_factored]
  have hc : (1:ℝ)/10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α := by
    rw [abs_of_nonneg (div_nonneg (by linarith) hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hker := hKer_abs_le hz
  rw [abs_mul, abs_mul, abs_of_nonneg hGam.1]
  have hstep : |2 * α / Work.Spaces.c α| * Work.Spaces.Gam α θ * |Work.Spaces.hKer z|
      ≤ (20 * α) * 1 * (1 / (1 + z)) :=
    mul_le_mul (mul_le_mul hcoef hGam.2 hGam.1 (mul_nonneg (by norm_num) hα.le)) hker
      (abs_nonneg _) (by positivity)
  linarith

/-- `|D_zF_*(z,θ)| ≤ 20 α /(1+z)`: `D_z` only sees the radial factor `H`, and
`|H(z)| ≤ 2/(1+z)`. -/
lemma DzFstar_abs_le {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 20 * α * (1 / (1 + z)) := by
  rw [Work.FTS.Nonlinear.FstarPkg.Dz_Fstar_eq_Hz hα (by linarith : (-1:ℝ) < z)]
  have hc : (1:ℝ)/10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |α / Work.Spaces.c α| ≤ 10 * α := by
    rw [abs_of_nonneg (div_nonneg hα.le hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hHz := Hz_abs_le hz
  rw [abs_mul, abs_mul, abs_of_nonneg hGam.1]
  have hstep : |α / Work.Spaces.c α| * (Work.Spaces.Gam α θ * |Work.FTS.Nonlinear.FstarPkg.Hz z|)
      ≤ (10 * α) * (1 * (2 / (1 + z))) :=
    mul_le_mul hcoef (mul_le_mul hGam.2 hHz (abs_nonneg _) (by norm_num))
      (mul_nonneg hGam.1 (abs_nonneg _)) (mul_nonneg (by norm_num) hα.le)
  calc |α / Work.Spaces.c α| * (Work.Spaces.Gam α θ * |Work.FTS.Nonlinear.FstarPkg.Hz z|)
      ≤ (10 * α) * (1 * (2 / (1 + z))) := hstep
    _ = 20 * α * (1 / (1 + z)) := by ring

/-- `|D_θF_*(z,θ)| ≤ 20 (tBound 0 0) α² /(1+z)`: the angular derivative costs one factor
`α` and the remaining factor `Γ` is bounded by `1`, while the radial factor still gives
`1/(1+z)`. -/
lemma DthFstar_abs_le {α z θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dth (Work.Construction.Fstar α) z θ|
      ≤ 20 * Work.Spaces.tBound 0 0 * α ^ 2 * (1 / (1 + z)) := by
  have hid : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      = (2 * α / Work.Spaces.c α) * Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ
          * Work.Spaces.hKer z := by
    have h := Work.FTS.Nonlinear.FstarPkg.pzIter_DthIter_Fstar_eq α 1 0 z θ
    simpa using h
  rw [hid, abs_mul, abs_mul]
  have hc : (1:ℝ)/10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hcoef : |2 * α / Work.Spaces.c α| ≤ 20 * α := by
    rw [abs_of_nonneg (div_nonneg (by linarith) hcpos.le), div_le_iff₀ hcpos]
    nlinarith
  have hGam := Work.Spaces.Gam_bounds α θ hα hθ
  have hT0 : 0 ≤ Work.Spaces.tBound 0 0 := Work.Spaces.tBound_nonneg 0 0
  have hdth0 := Work.Spaces.dthU_Gam_le 1 le_rfl α hα hα1 θ hθ
  have hdth : |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
      ≤ α * Work.Spaces.tBound 0 0 := by
    refine le_trans hdth0 ?_
    calc α * Work.Spaces.tBound 0 0 * Work.Spaces.Gam α θ
        ≤ α * Work.Spaces.tBound 0 0 * 1 :=
          mul_le_mul_of_nonneg_left hGam.2 (mul_nonneg hα.le hT0)
      _ = α * Work.Spaces.tBound 0 0 := by ring
  have hker := hKer_abs_le hz
  have hstep : |2 * α / Work.Spaces.c α| * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        * |Work.Spaces.hKer z|
      ≤ (20 * α) * (α * Work.Spaces.tBound 0 0) * (1 / (1 + z)) :=
    mul_le_mul (mul_le_mul hcoef hdth (abs_nonneg _) (mul_nonneg (by norm_num) hα.le)) hker
      (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hα.le) (mul_nonneg hα.le hT0))
  calc |2 * α / Work.Spaces.c α| * |Work.Spaces.dthU (fun t => Work.Spaces.Gam α t) θ|
        * |Work.Spaces.hKer z|
      ≤ (20 * α) * (α * Work.Spaces.tBound 0 0) * (1 / (1 + z)) := hstep
    _ = 20 * Work.Spaces.tBound 0 0 * α ^ 2 * (1 / (1 + z)) := by ring

/-! ## The slot bound -/

theorem FstarSlotPt :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ r θ : ℝ, 0 < r → θ ∈ Work.Spaces.Iθ →
      (Work.Construction.Fstar α r θ) ^ 2
        + (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2
        + (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2
      ≤ C * α ^ 2 * (1 / (1 + r)) ^ 2 := by
  refine ⟨800 + (20 * Work.Spaces.tBound 0 0) ^ 2 + 1, ?_, ?_⟩
  · have h := sq_nonneg (20 * Work.Spaces.tBound 0 0); linarith
  · intro α hαI r θ hr hθ
    obtain ⟨hα, hα1⟩ := hαI
    have hT0 : 0 ≤ Work.Spaces.tBound 0 0 := Work.Spaces.tBound_nonneg 0 0
    have hq0 : 0 ≤ (1 / (1 + r)) ^ 2 := sq_nonneg _
    have hαsq1 : α ^ 2 ≤ 1 := pow_le_one₀ hα.le hα1
    have h1r : (0:ℝ) < 1 + r := by linarith
    have hqr : 0 ≤ (1:ℝ) / (1 + r) := by positivity
    have hFabs := Fstar_abs_le hα hα1 hr.le hθ
    have hDabs := DthFstar_abs_le hα hα1 hr.le hθ
    have hZabs := DzFstar_abs_le hα hα1 hr.le hθ
    have hYF : 0 ≤ 20 * α * (1 / (1 + r)) :=
      mul_nonneg (mul_nonneg (by norm_num) hα.le) hqr
    have hYD : 0 ≤ 20 * Work.Spaces.tBound 0 0 * α ^ 2 * (1 / (1 + r)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT0) (sq_nonneg α)) hqr
    have hF2 : (Work.Construction.Fstar α r θ) ^ 2
        ≤ 400 * α ^ 2 * (1 / (1 + r)) ^ 2 := by
      have h := sq_le_sq.mpr (show |Work.Construction.Fstar α r θ| ≤ |20 * α * (1 / (1 + r))| by
        rw [abs_of_nonneg hYF]; exact hFabs)
      calc (Work.Construction.Fstar α r θ) ^ 2 ≤ (20 * α * (1 / (1 + r))) ^ 2 := h
        _ = 400 * α ^ 2 * (1 / (1 + r)) ^ 2 := by ring
    have hZ2 : (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2
        ≤ 400 * α ^ 2 * (1 / (1 + r)) ^ 2 := by
      have h := sq_le_sq.mpr (show |Work.Spaces.Dz (Work.Construction.Fstar α) r θ|
          ≤ |20 * α * (1 / (1 + r))| by rw [abs_of_nonneg hYF]; exact hZabs)
      calc (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2
          ≤ (20 * α * (1 / (1 + r))) ^ 2 := h
        _ = 400 * α ^ 2 * (1 / (1 + r)) ^ 2 := by ring
    have hD2 : (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2
        ≤ (20 * Work.Spaces.tBound 0 0) ^ 2 * α ^ 2 * (1 / (1 + r)) ^ 2 := by
      have h := sq_le_sq.mpr (show |Work.Spaces.Dth (Work.Construction.Fstar α) r θ|
          ≤ |20 * Work.Spaces.tBound 0 0 * α ^ 2 * (1 / (1 + r))| by
        rw [abs_of_nonneg hYD]; exact hDabs)
      have h4 : α ^ 4 ≤ α ^ 2 := by
        calc α ^ 4 = α ^ 2 * α ^ 2 := by ring
          _ ≤ 1 * α ^ 2 := mul_le_mul_of_nonneg_right hαsq1 (sq_nonneg α)
          _ = α ^ 2 := by ring
      have hA : 0 ≤ (20 * Work.Spaces.tBound 0 0) ^ 2 := sq_nonneg _
      calc (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2
          ≤ (20 * Work.Spaces.tBound 0 0 * α ^ 2 * (1 / (1 + r))) ^ 2 := h
        _ = (20 * Work.Spaces.tBound 0 0) ^ 2 * α ^ 4 * (1 / (1 + r)) ^ 2 := by ring
        _ ≤ (20 * Work.Spaces.tBound 0 0) ^ 2 * α ^ 2 * (1 / (1 + r)) ^ 2 := by
            calc (20 * Work.Spaces.tBound 0 0) ^ 2 * α ^ 4 * (1 / (1 + r)) ^ 2
                = ((20 * Work.Spaces.tBound 0 0) ^ 2 * (1 / (1 + r)) ^ 2) * α ^ 4 := by ring
              _ ≤ ((20 * Work.Spaces.tBound 0 0) ^ 2 * (1 / (1 + r)) ^ 2) * α ^ 2 :=
                  mul_le_mul_of_nonneg_left h4 (mul_nonneg hA hq0)
              _ = (20 * Work.Spaces.tBound 0 0) ^ 2 * α ^ 2 * (1 / (1 + r)) ^ 2 := by ring
    have hsum : (Work.Construction.Fstar α r θ) ^ 2
          + (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2
          + (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2
        ≤ (400 + (20 * Work.Spaces.tBound 0 0) ^ 2 + 400) * α ^ 2 * (1 / (1 + r)) ^ 2 := by
      have h := add_le_add (add_le_add hF2 hD2) hZ2
      calc (Work.Construction.Fstar α r θ) ^ 2
            + (Work.Spaces.Dth (Work.Construction.Fstar α) r θ) ^ 2
            + (Work.Spaces.Dz (Work.Construction.Fstar α) r θ) ^ 2
          ≤ 400 * α ^ 2 * (1 / (1 + r)) ^ 2
            + (20 * Work.Spaces.tBound 0 0) ^ 2 * α ^ 2 * (1 / (1 + r)) ^ 2
            + 400 * α ^ 2 * (1 / (1 + r)) ^ 2 := h
        _ = (400 + (20 * Work.Spaces.tBound 0 0) ^ 2 + 400) * α ^ 2 * (1 / (1 + r)) ^ 2 := by ring
    refine le_trans hsum ?_
    have hcoef : 400 + (20 * Work.Spaces.tBound 0 0) ^ 2 + 400
        ≤ 800 + (20 * Work.Spaces.tBound 0 0) ^ 2 + 1 := by
      have h := sq_nonneg (20 * Work.Spaces.tBound 0 0)
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (sq_nonneg α)) hq0

end Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux
