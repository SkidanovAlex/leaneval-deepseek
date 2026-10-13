import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Submission.Work.FTS_StreamBdry.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `abs_deriv_le_of_lipschitzOn_Ioc`

If `f : ℝ → ℝ` is `C`-Lipschitz on the half-open interval `Ioc 0 1 = (0,1]`, then
`|deriv f z| ≤ C` at every point `z ∈ (0,1]`.

For `z < 1` this is the usual "Lipschitz on a neighbourhood of `x` bounds the derivative at `x`"
(`norm_deriv_le_of_lipschitzOn`, since `Ioc 0 1` is a neighbourhood of `z`).  The right endpoint
`z = 1` needs care: there `Ioc 0 1` is *not* a neighbourhood of `1`, the Lipschitz bound only
controls `f` to the left of `1`.  But `deriv f 1`, when it exists, is also the limit of the
one-sided slopes `slope f 1 t` for `t → 1⁻`, and those are bounded by `C` because both `t` and `1`
lie in `Ioc 0 1`.  (If `f` is not differentiable at `1` then `deriv f 1 = 0` by convention.)
-/

namespace Work.FTS_StreamBdry.SB4

open Set Filter
open scoped Topology

/-- The left-hand slope of `f` at the right endpoint `1` is bounded by `C` on `(0,1)`,
because both `t` and `1` lie in `Ioc 0 1`. -/
theorem norm_slope_one_le {f : ℝ → ℝ} {C : NNReal}
    (hlip : LipschitzOnWith C f (Set.Ioc 0 1)) {t : ℝ} (ht : t ∈ Set.Ioo 0 1) :
    ‖slope f 1 t‖ ≤ (C : ℝ) := by
  have hb : ‖f t - f 1‖ ≤ (C : ℝ) * ‖t - 1‖ :=
    hlip.norm_sub_le ⟨ht.1, le_of_lt ht.2⟩ ⟨zero_lt_one, le_rfl⟩
  have hnorm : ‖slope f 1 t‖ = ‖t - 1‖⁻¹ * ‖f t - f 1‖ := by
    rw [slope_def_module, norm_smul, norm_inv]
  rw [hnorm]
  calc ‖t - 1‖⁻¹ * ‖f t - f 1‖
      ≤ ‖t - 1‖⁻¹ * ((C : ℝ) * ‖t - 1‖) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg _))
    _ = (C : ℝ) * (‖t - 1‖⁻¹ * ‖t - 1‖) := by ring
    _ ≤ (C : ℝ) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ C.coe_nonneg
        have hp : 0 < ‖t - 1‖ := by
          rw [Real.norm_eq_abs]; exact abs_pos.mpr (by linarith [ht.2])
        exact le_of_eq (inv_mul_cancel₀ (ne_of_gt hp))
    _ = (C : ℝ) := mul_one _

/-- At the right endpoint `1`, the derivative of a function which is `C`-Lipschitz on `Ioc 0 1`
is bounded by `C`: the bound comes from the slopes on the left. -/
theorem abs_deriv_one_le {f : ℝ → ℝ} {C : NNReal}
    (hlip : LipschitzOnWith C f (Set.Ioc 0 1)) :
    |deriv f 1| ≤ (C : ℝ) := by
  -- `(0,1)` is eventually in the left-neighbourhood filter of `1`
  have hmem : Set.Ioo 0 1 ∈ 𝓝[Set.Iio 1] (1 : ℝ) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Ioo 0 2, Ioo_mem_nhds (by norm_num) (by norm_num),
      fun x hx => ⟨hx.1.1, hx.2⟩⟩
  have hev : ∀ᶠ t in 𝓝[Set.Iio 1] (1 : ℝ), ‖slope f 1 t‖ ≤ (C : ℝ) := by
    filter_upwards [hmem] with t ht
    exact norm_slope_one_le hlip ht
  by_cases hd : DifferentiableAt ℝ f 1
  · have hT : Tendsto (slope f 1) (𝓝[Set.Iio 1] (1 : ℝ)) (𝓝 (deriv f 1)) :=
      (hd.hasDerivAt.tendsto_slope).mono_left (nhdsWithin_mono 1 (fun x hx => ne_of_lt hx))
    have h2 : ‖deriv f 1‖ ≤ (C : ℝ) := le_of_tendsto hT.norm hev
    rwa [Real.norm_eq_abs] at h2
  · rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
    exact C.coe_nonneg

theorem abs_deriv_le_of_lipschitzOn_Ioc {f : ℝ → ℝ} {C : NNReal}
    (hlip : LipschitzOnWith C f (Set.Ioc 0 1)) :
    ∀ z ∈ Set.Ioc 0 1, |deriv f z| ≤ (C : ℝ) := by
  intro z hz
  rcases lt_or_eq_of_le hz.2 with hzlt | hzeq
  · -- `z < 1`: `Ioc 0 1` is a neighbourhood of `z`
    have hmem : Set.Ioc 0 1 ∈ 𝓝 z :=
      mem_of_superset (Ioo_mem_nhds hz.1 hzlt) fun x hx => ⟨hx.1, le_of_lt hx.2⟩
    have h1 : ‖deriv f z‖ ≤ (C : ℝ) := norm_deriv_le_of_lipschitzOn hmem hlip
    rwa [Real.norm_eq_abs] at h1
  · -- `z = 1`: one-sided slope argument
    subst hzeq
    exact abs_deriv_one_le hlip

end Work.FTS_StreamBdry.SB4
