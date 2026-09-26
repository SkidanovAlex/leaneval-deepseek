/-
# The weight-eight invariant of a rigidity input vanishes

This file proves `Work.Rigidity.WeightEightVanishes`: for a rigidity input `f` at weight `4`
and eigenvalue `1` (holomorphic of moderate growth, killed by `(T - I)²`, `S`-invariant, and
`o(1)` along the strip `-1 ≤ Re τ ≤ 1`), the weight-`8` invariant

  `I2 f = u² + u·H + H²`,   `u = fstDiff f`,   `H = sdef f = u ∣[4] S`

vanishes identically.  This is the last step in the CKMRV proof of `lem:noPsolutions` at
weight `4` (`d = 8`): the annihilation of `I2 f` is what forces `f = 0`
(`AnnMinusWeightFourP`).

## The argument

* `I2 f = u² + uH + H²` is a product/sum of elements of `𝒫 = Work.Kernels.InP`: `u` and `H`
  lie in `𝒫` because `f` does and `𝒫` is preserved by the slash action
  (`Work.Kernels.InP.slash`).  Hence `I2 f` is holomorphic.
* `I2 f` is `SL(2, ℤ)`-invariant of weight `8` (`Work.Rigidity.I2_slash_S`,
  `Work.Rigidity.I2_slash_T`, and the generation of `SL(2, ℤ)` by `S`, `T`), so it is the
  underlying function of a level-one modular form of weight `8`
  (`Work.Modular.modularForm_of_slash_invariant`).
* `u` and `H` both tend to `0` at the cusp `i∞`: for `u` this is the periodicity of the
  first difference (`Work.Rigidity.fstDiff_vadd_one_iff`) together with the strip decay
  (`Work.Rigidity.fstDiff_stripDecay`), for `H` it is `Work.Rigidity.SlashSTdefTendstoZeroInP`.
  Hence `I2 f → 0` at `i∞`, i.e. `I2 f` is a cusp form of weight `8`.
* The space of level-one cusp forms of weight `8` is zero
  (`CuspForm.rank_eq_zero_of_weight_lt_twelve`), so the corresponding cusp form — and hence
  `I2 f` — vanishes.
-/
import Mathlib
import Submission.Work.Rigidity.AnnMinusAux
import Submission.Work.Rigidity.SlashSTdefTendstoZeroInP
import Submission.Work.Modular.modularForm_of_slash_invariant

namespace Work.Rigidity

open UpperHalfPlane ModularForm ModularGroup Matrix Filter
open scoped MatrixGroups ModularForm Manifold Bundle Topology

theorem WeightEightVanishes {f : UpperHalfPlane → ℂ} (hP : Work.Kernels.InP f)
    (hT2 : Work.Rigidity.AnnT2 f) (hS : Work.Rigidity.SlashEigen 4 (1 : ℂ) f)
    (hdec : Work.Rigidity.StripDecay 0 f) : Work.Rigidity.I2 f = 0 := by
  -- ### The two component functions `u = fstDiff f` and `H = sdef f`
  set u : UpperHalfPlane → ℂ := Work.Rigidity.fstDiff f with hu
  set H : UpperHalfPlane → ℂ := Work.Rigidity.sdef f with hH
  have hI2eq : Work.Rigidity.I2 f = u * u + u * H + H * H := by
    funext τ
    simp only [Work.Rigidity.I2, Pi.add_apply, Pi.mul_apply, pow_two, hu, hH]
  -- ### `u`, `H` and `I2 f` lie in the class `𝒫`
  have hPu : Work.Kernels.InP u := by
    have h : u = f ∣[(4 : ℤ)] ModularGroup.T - f := by
      funext τ
      rw [hu]
      simp only [Work.Rigidity.fstDiff, Pi.sub_apply, Work.Kernels.slash_T_apply]
    rw [h]
    exact (Work.Kernels.InP.slash hP (4 : ℤ) ModularGroup.T).sub hP
  have hPH : Work.Kernels.InP H := by
    have h : H = u ∣[(4 : ℤ)] ModularGroup.S := by
      funext τ
      rw [hH, hu, Work.Kernels.slash_S_apply]
      simp only [Work.Rigidity.sdef]
      ring
    rw [h]
    exact Work.Kernels.InP.slash hPu (4 : ℤ) ModularGroup.S
  have hPI2 : Work.Kernels.InP (Work.Rigidity.I2 f) := by
    rw [hI2eq]
    exact ((hPu.mul hPu).add (hPu.mul hPH)).add (hPH.mul hPH)
  have hmdI2 : MDiff (Work.Rigidity.I2 f) := hPI2.1
  -- ### `I2 f` is `SL(2, ℤ)`-invariant of weight `8`
  have hsl : ∀ γ : SL(2, ℤ),
      SlashAction.map (8 : ℤ) γ (Work.Rigidity.I2 f) = Work.Rigidity.I2 f :=
    SlashInvariantForm.slash_action_generators_SL2Z (Work.Rigidity.I2_slash_S f)
      (Work.Rigidity.I2_slash_T hT2 hS)
  -- ### `u` tends to `0` at the cusp `i∞`
  have hper_u : ∀ τ : UpperHalfPlane, u ((1 : ℝ) +ᵥ τ) = u τ := by
    intro τ
    rw [hu]
    exact (Work.Rigidity.fstDiff_vadd_one_iff f).mp hT2 τ
  have hdec_u : Work.Rigidity.StripDecay 0 u := by
    rw [hu]
    exact Work.Rigidity.fstDiff_stripDecay hT2 hdec
  have hu0 : UpperHalfPlane.IsZeroAtImInfty u := by
    obtain ⟨φ, hφ, hφ'⟩ := hdec_u
    rw [UpperHalfPlane.isZeroAtImInfty_iff]
    intro ε hε
    obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ y : ℝ, A ≤ y → φ y < ε := by
      obtain ⟨A, hA⟩ := Metric.tendsto_atTop.1 hφ ε hε
      exact ⟨A, fun y hy => by
        have h := hA y hy
        rw [Real.dist_eq, sub_zero, abs_lt] at h
        exact h.2⟩
    refine ⟨max A 1, fun τ hτ => ?_⟩
    obtain ⟨n, hn⟩ := Work.Rigidity.exists_int_vadd_mem_strip τ
    have hσim : (((n : ℝ) +ᵥ τ : UpperHalfPlane)).im = τ.im := Work.Rigidity.im_vadd n τ
    have huσ : u ((n : ℝ) +ᵥ τ) = u τ := Work.Rigidity.vadd_int_of_vadd_one hper_u n τ
    have hb := hφ' ((n : ℝ) +ᵥ τ) hn
    have hexp :
        Real.exp (-(2 * Real.pi * 0 * (((n : ℝ) +ᵥ τ : UpperHalfPlane)).im)) = 1 := by
      norm_num
    rw [hexp, mul_one] at hb
    rw [← huσ]
    exact le_trans hb (le_of_lt (hA _ (by rw [hσim]; exact le_trans (le_max_left _ _) hτ)))
  -- ### `H` tends to `0` at the cusp `i∞`
  have hH0 : UpperHalfPlane.IsZeroAtImInfty H := by
    rw [hH]
    exact Work.Rigidity.SlashSTdefTendstoZeroInP hP hT2 hS hdec
  -- ### hence `I2 f` tends to `0` at the cusp `i∞`
  have hI20 : UpperHalfPlane.IsZeroAtImInfty (Work.Rigidity.I2 f) := by
    rw [hI2eq, UpperHalfPlane.IsZeroAtImInfty, Filter.ZeroAtFilter]
    have hu0' : Tendsto u atImInfty (𝓝 0) := hu0
    have hH0' : Tendsto H atImInfty (𝓝 0) := hH0
    have h1 : Tendsto (fun τ => u τ * u τ) atImInfty (𝓝 0) := by
      have h := hu0'.mul hu0'; simpa using h
    have h2 : Tendsto (fun τ => u τ * H τ) atImInfty (𝓝 0) := by
      have h := hu0'.mul hH0'; simpa using h
    have h3 : Tendsto (fun τ => H τ * H τ) atImInfty (𝓝 0) := by
      have h := hH0'.mul hH0'; simpa using h
    have h4 : Tendsto (fun τ => u τ * u τ + u τ * H τ + H τ * H τ) atImInfty (𝓝 0) := by
      have h := (h1.add (h2.add h3))
      have heq : (fun τ => u τ * u τ + (u τ * H τ + H τ * H τ))
          = (fun τ => u τ * u τ + u τ * H τ + H τ * H τ) := by
        funext τ; ring
      rw [heq] at h
      simpa using h
    exact h4
  have hbddI2 : UpperHalfPlane.IsBoundedAtImInfty (Work.Rigidity.I2 f) := hI20.isBoundedAtImInfty
  -- ### `I2 f` is the underlying function of a cusp form of weight `8`
  obtain ⟨g, hg⟩ := Work.Modular.modularForm_of_slash_invariant hsl hmdI2 hbddI2
  have hc0 : (UpperHalfPlane.qExpansion 1 g).coeff 0 = 0 := by
    rw [UpperHalfPlane.qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero g one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex g one_mem_strictPeriods_SL)]
    rw [hg]
    exact hI20.valueAtInfty_eq_zero
  have hG0 : ModularForm.toCuspForm g hc0 = 0 :=
    rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (k := (8 : ℤ)) (by norm_num))
      (ModularForm.toCuspForm g hc0)
  funext τ
  rw [← hg]
  have h1 : (ModularForm.toCuspForm g hc0 : UpperHalfPlane → ℂ) = 0 := by
    rw [hG0]; rfl
  have h2 : g τ = 0 := by
    have h3 := congrFun h1 τ
    rwa [ModularForm.toCuspForm_apply] at h3
  exact h2

end Work.Rigidity
