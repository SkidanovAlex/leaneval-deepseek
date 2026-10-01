/-
# Area 7 — monotonicity of `Wf`, `Φ`, `Φ/w` and `C`

The function `Wf(λ) = w(λ) = λ/(e^{73λ/30} - e^{16λ/15})` is HB's density weight and
`Φ(λ) = e^{-aλ}B(K,λ)` (with `a = 49/10`, `K = 3/10`) the normalised per-character constant.
`C(Λ,λ) = max(0, Φ(λ) - Φ(Λ)w(λ)/w(Λ))` is the `C`-function of HB §15.

Everything here rests on one identity: writing `R = Φ/w` for the ratio,

  `C(Λ,λ) = w(λ) · max(0, R(λ) - R(Λ))`,

so that `C(Λ,·)` decreases as soon as `w` and `R` do.  Monotonicity of `w` is the proved
`Work.LinnikAreas.Density4.wHB_antitone` (HB §11, integral form `w(λ) = 1/∫_{16/15}^{73/30}e^{tλ}dt`),
and monotonicity of `R = B(3/10,·) · e^{-49λ/10}/w(λ)` follows from the antitonicity of `B(3/10,·)`
and of `λ ↦ e^{-49λ/10}/w(λ)` (the latter being `∫_{37/15}^{23/6}e^{-tλ}dt`).
-/
import Mathlib
import Submission.Work.LinnikAreas.A7.Defs
import Submission.Work.LinnikAreas.Density4.wHB_antitone
import Submission.Work.LinnikContract.API.Bfun_pos
import Submission.Work.A7.ExpWf_antitone
import Submission.Work.A7.Bfun_antitone

noncomputable section

namespace Work.A7

open Work.LinnikContract
open Work.LinnikAreas.A7

/-! ## `Wf` -/

/-- `Wf λ = w(λ)` is positive for `λ > 0` (the denominator `e^{73λ/30} - e^{16λ/15} =
e^{16λ/15}(e^{41λ/30} - 1)` is positive). -/
theorem Wf_pos {x : ℝ} (hx : 0 < x) : 0 < Wf x := by
  rw [Wf, wHB]
  refine div_pos hx (sub_pos.mpr ?_)
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- `Wf` is non-increasing on `(0,∞)`; this is HB §11 (`wHB_antitone`). -/
theorem Wf_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Wf y ≤ Wf x :=
  Work.LinnikAreas.Density4.wHB_antitone hx hxy

/-! ## The ratio `Φ/w` -/

/-- `Φ(λ)/w(λ) = B(3/10,λ) · e^{-49λ/10}/w(λ)`. -/
theorem PhiWf_eq {z : ℝ} (_hz : 0 < z) :
    Phi z / Wf z = Bfun Kc z * (Real.exp (-((49:ℝ)/10*z)) / Wf z) := by
  have hac : ac = (49:ℝ)/10 := by norm_num [ac]
  rw [Phi, hac, div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The ratio `Φ/w` is non-increasing on `(0,∞)`: it is the product of the non-negative
non-increasing functions `B(3/10,·)` and `e^{-49λ/10}/w(λ)`. -/
theorem PhiWf_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Phi y / Wf y ≤ Phi x / Wf x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hKc : (0:ℝ) < Kc := by norm_num [Kc]
  rw [PhiWf_eq hy, PhiWf_eq hx]
  refine mul_le_mul (Bfun_antitone hKc hx hxy) (ExpWf_antitone hx hxy) ?_ ?_
  · exact div_nonneg (Real.exp_pos _).le (Wf_pos hy).le
  · exact (Work.LinnikContract.API.Bfun_pos hKc hx).le

/-! ## The `C`-function -/

/-- The basic rewriting of `C`: `C(Λ,λ) = w(λ)·max(0, Φ(λ)/w(λ) - Φ(Λ)/w(Λ))`. -/
theorem Cf_eq_max {Λ z : ℝ} (hΛ : 0 < Λ) (hz : 0 < z) :
    Cf Λ z = max 0 (Wf z * (Phi z / Wf z - Phi Λ / Wf Λ)) := by
  have hΛne : Wf Λ ≠ 0 := ne_of_gt (Wf_pos hΛ)
  have hzne : Wf z ≠ 0 := ne_of_gt (Wf_pos hz)
  rw [Cf]
  congr 1
  rw [mul_sub]
  congr 1
  · field_simp
  · field_simp

/-- `C(Λ,·)` is non-increasing on `(0,∞)`.  Indeed `C(Λ,λ) = w(λ)·max(0, R(λ)-R(Λ))` with `w`
and `R` non-increasing, so for `λ ≤ Λ` both sides are the positive product `w(λ)(R(λ)-R(Λ))`
(which decreases as `w` and `R` do), while for `λ ≥ Λ` the second factor is `≤ 0` and the max
vanishes. -/
theorem Cf_antitone (hR : ∀ {x y : ℝ}, 0 < x → x ≤ y → Phi y / Wf y ≤ Phi x / Wf x) :
    ∀ {Λ x y : ℝ}, 0 < Λ → 0 < x → x ≤ y → Cf Λ y ≤ Cf Λ x := by
  intro Λ x y hΛ hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  rw [Cf_eq_max hΛ hy, Cf_eq_max hΛ hx]
  rcases le_or_gt y Λ with hyΛ | hyΛ
  · -- `y ≤ Λ`: both maxima are attained at the first branch
    have hRy : Phi Λ / Wf Λ ≤ Phi y / Wf y := hR hy hyΛ
    have hRx : Phi Λ / Wf Λ ≤ Phi x / Wf x := hR hx (le_trans hxy hyΛ)
    have hyx : Phi y / Wf y ≤ Phi x / Wf x := hR hx hxy
    have hAy : 0 ≤ Wf y * (Phi y / Wf y - Phi Λ / Wf Λ) :=
      mul_nonneg (Wf_pos hy).le (by linarith)
    have hAx : 0 ≤ Wf x * (Phi x / Wf x - Phi Λ / Wf Λ) :=
      mul_nonneg (Wf_pos hx).le (by linarith)
    rw [max_eq_right hAy, max_eq_right hAx]
    exact mul_le_mul (Wf_antitone hx hxy) (by linarith) (by linarith) (Wf_pos hx).le
  · -- `Λ < y`
    have hy' : Phi y / Wf y ≤ Phi Λ / Wf Λ := hR hΛ hyΛ.le
    have hAy : Wf y * (Phi y / Wf y - Phi Λ / Wf Λ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Wf_pos hy).le (by linarith)
    rw [max_eq_left hAy]
    rcases le_or_gt x Λ with hxΛ | hxΛ
    · exact le_max_left 0 _
    · have hx' : Phi x / Wf x ≤ Phi Λ / Wf Λ := hR hΛ hxΛ.le
      have hAx : Wf x * (Phi x / Wf x - Phi Λ / Wf Λ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Wf_pos hx).le (by linarith)
      rw [max_eq_left hAx]

/-! ## The target -/

theorem Wf_Cf_mono :
    (∀ {x : ℝ}, 0 < x → 0 < Work.LinnikAreas.A7.Wf x) ∧
    (∀ {x y : ℝ}, 0 < x → x ≤ y → Work.LinnikAreas.A7.Wf y ≤ Work.LinnikAreas.A7.Wf x) ∧
    (∀ {Λ x y : ℝ}, 0 < Λ → 0 < x → x ≤ y → Work.LinnikAreas.A7.Cf Λ y ≤ Work.LinnikAreas.A7.Cf Λ x) ∧
    (∀ {Λ x : ℝ}, 0 ≤ Work.LinnikAreas.A7.Cf Λ x) ∧
    (∀ {Λ : ℝ}, 0 < Λ → Work.LinnikAreas.A7.Cf Λ Λ = 0) ∧
    (∀ {x y : ℝ}, 0 < x → x ≤ y → Work.LinnikAreas.A7.Phi y / Work.LinnikAreas.A7.Wf y ≤ Work.LinnikAreas.A7.Phi x / Work.LinnikAreas.A7.Wf x) ∧
    (∀ {x y : ℝ}, 0 < x → x ≤ y → Real.exp (-((49:ℝ)/10*y)) / Work.LinnikAreas.A7.Wf y ≤ Real.exp (-((49:ℝ)/10*x)) / Work.LinnikAreas.A7.Wf x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; exact Wf_pos hx
  · intro x y hx hxy; exact Wf_antitone hx hxy
  · intro Λ x y hΛ hx hxy; exact Cf_antitone (fun {x y} hx hxy => PhiWf_antitone hx hxy) hΛ hx hxy
  · intro Λ x; rw [Cf]; exact le_max_left 0 _
  · intro Λ hΛ
    have hne : Wf Λ ≠ 0 := ne_of_gt (Wf_pos hΛ)
    have hzero : Phi Λ - Phi Λ * Wf Λ / Wf Λ = 0 := by
      rw [mul_div_assoc, div_self hne, mul_one, sub_self]
    rw [Cf, hzero, max_self]
  · intro x y hx hxy; exact PhiWf_antitone hx hxy
  · intro x y hx hxy; exact ExpWf_antitone hx hxy

end Work.A7
