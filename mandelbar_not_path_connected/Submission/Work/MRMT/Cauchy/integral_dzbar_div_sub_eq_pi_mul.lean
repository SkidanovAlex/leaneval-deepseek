import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Cauchy.dzbar_star_div_normSq_add
import Submission.Work.MRMT.QC.integral_mul_dzbar_eq_neg
import Submission.Work.MRMT.Cauchy.integral_dzbar_div_eq_neg_pi_mul
import Submission.Work.MRMT.Cauchy.tendsto_integral_mul_kernelSq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

open MeasureTheory Complex Function Filter
open scoped Topology

/-- **Translation invariance of `∂̄`.**  Translating the argument of a real-differentiable
function does not change its Wirtinger derivative:
`∂̄(g(· + c))(y) = ∂̄g(c + y)`.

Indeed `fderiv ℝ (fun y => g (c + y)) y = (fderiv ℝ g (c + y)) ∘ (fderiv ℝ (fun y => c + y) y)`
and the second factor is the identity, since translation is an affine isometry. -/
theorem dzbar_comp_add (g : ℂ → ℂ) (c y : ℂ) (hg : DifferentiableAt ℝ g (c + y)) :
    Work.MRMT.dzbar (fun y => g (c + y)) y = Work.MRMT.dzbar g (c + y) := by
  have hd : DifferentiableAt ℝ (fun y : ℂ => c + y) y := by fun_prop
  have h1 : HasFDerivAt (fun y : ℂ => g (c + y))
      ((fderiv ℝ g (c + y)).comp (fderiv ℝ (fun y : ℂ => c + y) y)) y :=
    hg.hasFDerivAt.comp y hd.hasFDerivAt
  have h2 : fderiv ℝ (fun y : ℂ => c + y) y = ContinuousLinearMap.id ℝ ℂ := by
    have hh : HasFDerivAt (fun y : ℂ => c + y) (ContinuousLinearMap.id ℝ ℂ) y := by
      simpa using (hasFDerivAt_id (𝕜 := ℝ) y).const_add c
    exact hh.fderiv
  rw [Work.MRMT.dzbar, Work.MRMT.dzbar, h1.fderiv, h2]
  simp

/-- **The `ε`-smoothed Cauchy–Pompeiu identity.**  For smooth compactly supported `ψ` and
`ε > 0`, with the mollified kernel `K_ε(z) = z̄/(‖z‖²+ε²)`,

`∫ z, ∂̄ψ(z) · K_ε(z) dz = -∫ z, ψ(z) · ε²/(‖z‖²+ε²)² dz`.

This is the integration-by-parts identity `Work.MRMT.QC.integral_mul_dzbar_eq_neg` applied to
`K_ε` (which is `C¹`) and `ψ` (which is `C¹` with compact support), together with the explicit
`∂̄K_ε = ε²/(‖z‖²+ε²)²` of `Work.MRMT.Cauchy.dzbar_star_div_normSq_add`. -/
theorem eps_identity (ψ : ℂ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : HasCompactSupport ψ)
    (ε : ℝ) (hε : 0 < ε) :
    ∫ z, Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ))
      = - ∫ z, ψ z * (((ε : ℂ) ^ 2) / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2) := by
  have hK1 : ContDiff ℝ 1 (fun w : ℂ => star w / ((‖w‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) := by
    have hstar : ContDiff ℝ 1 (fun w : ℂ => star w) := by
      rw [show (fun w : ℂ => star w) = ⇑Complex.conjCLE from
        funext (fun z => (Complex.conjCLE_apply z).symm)]
      exact Complex.conjCLE.contDiff
    have hden : ContDiff ℝ 1 (fun w : ℂ => ((‖w‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) := by
      have h1 : ContDiff ℝ 1 (fun w : ℂ => (‖w‖ ^ 2 + ε ^ 2 : ℝ)) :=
        (contDiff_norm_sq ℝ).add contDiff_const
      exact Complex.ofRealCLM.contDiff.comp h1
    have hinv : ContDiff ℝ 1 (fun w : ℂ => (((‖w‖ ^ 2 + ε ^ 2 : ℝ) : ℂ))⁻¹) :=
      hden.inv (fun w => by
        have hpos : (0:ℝ) < ‖w‖ ^ 2 + ε ^ 2 := by positivity
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
    have := hstar.mul hinv
    simpa [div_eq_mul_inv] using this
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have h := Work.MRMT.QC.integral_mul_dzbar_eq_neg hK1 hψ1 hs
  rw [show (∫ z, Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)))
        = ∫ z, (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) * Work.MRMT.dzbar ψ z from
      integral_congr_ae (Eventually.of_forall (fun z => mul_comm _ _))]
  rw [h]
  congr 1
  rw [show (∫ u : ℂ, Work.MRMT.dzbar
        (fun w : ℂ => star w / ((‖w‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) u * ψ u)
        = ∫ u, (((ε : ℂ) ^ 2) / (((‖u‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2) * ψ u from by
      apply integral_congr_ae
      filter_upwards with u
      rw [dzbar_star_div_normSq_add ε u]]
  apply integral_congr_ae
  filter_upwards with u
  ring

/-- **Base identity of the Cauchy transform** (`ζ = 0` case): for smooth compactly supported
`ψ`, `∫ z, ∂̄ψ(z)/z dz = -π ψ(0)`.

Both sides of `eps_identity` have limits as `ε → 0⁺`: the smoothed `∂̄ψ`-integral tends to
`∫ ∂̄ψ/z` (`Work.MRMT.Cauchy.tendsto_integral_dzbar_mul_cauKernel`) and the other side tends to
`π ψ(0)` (`Work.MRMT.Cauchy.tendsto_integral_mul_kernelSq`).  Uniqueness of limits gives the
claim. -/
theorem integral_dzbar_div_eq_neg_pi_mul' (ψ : ℂ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : HasCompactSupport ψ) :
    ∫ z, Work.MRMT.dzbar ψ z / z = -(Real.pi : ℂ) * ψ 0 := by
  have hlim1 := tendsto_integral_dzbar_mul_cauKernel ψ hψ hs
  have hlim2 := tendsto_integral_mul_kernelSq ψ hψ.continuous hs
  have hadj : (fun ε : ℝ => ∫ z, Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)))
      =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε : ℝ => - ∫ z, ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact eps_identity ψ hψ hs ε hε
  have hlim2' : Tendsto
      (fun ε : ℝ => - ∫ z, ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (-((Real.pi : ℂ) * ψ 0))) := hlim2.neg
  have hlim1' : Tendsto
      (fun ε : ℝ => ∫ z, Work.MRMT.dzbar ψ z * (star z / ((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-((Real.pi : ℂ) * ψ 0))) :=
    Filter.Tendsto.congr' hadj.symm hlim2'
  have huniq : (∫ z, Work.MRMT.dzbar ψ z / z) = -((Real.pi : ℂ) * ψ 0) :=
    tendsto_nhds_unique hlim1 hlim1'
  simpa [neg_mul] using huniq

/-- **Cauchy–Pompeiu identity for a translated kernel.**  For `ψ : ℂ → ℂ` smooth with compact
support and any centre `ζ`,
`∫ z, ∂̄ψ(z) / (ζ - z) dz = π * ψ ζ`
(Lebesgue measure on `ℂ`, `∂̄ = Work.MRMT.dzbar` the Wirtinger derivative). -/
theorem integral_dzbar_div_sub_eq_pi_mul (ψ : ℂ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hs : HasCompactSupport ψ) (ζ : ℂ) :
    ∫ z, Work.MRMT.dzbar ψ z / (ζ - z) = (Real.pi : ℂ) * ψ ζ := by
  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by simp)
  set ψt : ℂ → ℂ := fun w => ψ (ζ + w) with hψt_def
  have hψt_smooth : ContDiff ℝ (⊤ : ℕ∞) ψt := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun w : ℂ => ζ + w) := by
      simpa using (contDiff_const (c := ζ)).add contDiff_id
    exact hψ.comp h1
  have hψt_supp : HasCompactSupport ψt := by
    have h := hs.comp_homeomorph (Homeomorph.addLeft ζ)
    simpa [ψt, Function.comp_def] using h
  have hdz : ∀ w, Work.MRMT.dzbar ψt w = Work.MRMT.dzbar ψ (ζ + w) :=
    fun w => dzbar_comp_add ψ ζ w (hdiff.differentiableAt)
  have h0 : ψt 0 = ψ ζ := by simp [ψt]
  -- the base (`ζ = 0`) identity applied to the translated function
  have hbase' : ∫ w, Work.MRMT.dzbar ψ (ζ + w) / w = -(Real.pi : ℂ) * ψ ζ := by
    have h := integral_dzbar_div_eq_neg_pi_mul' ψt hψt_smooth hψt_supp
    simp only [hdz, h0] at h
    exact h
  -- substitution `z = ζ + w` (translation invariance of Lebesgue measure)
  have htrans : ∫ w, Work.MRMT.dzbar ψ (ζ + w) / w
      = ∫ z, Work.MRMT.dzbar ψ z / (z - ζ) := by
    have h := MeasureTheory.integral_add_left_eq_self
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
      (fun z : ℂ => Work.MRMT.dzbar ψ z / (z - ζ)) ζ
    simpa using h
  have key : ∫ z, Work.MRMT.dzbar ψ z / (z - ζ) = -(Real.pi : ℂ) * ψ ζ := by
    rw [← htrans]; exact hbase'
  -- `1/(ζ - z) = -1/(z - ζ)` pointwise
  have hneg : ∫ z, Work.MRMT.dzbar ψ z / (ζ - z)
      = - ∫ z, Work.MRMT.dzbar ψ z / (z - ζ) := by
    rw [← MeasureTheory.integral_neg]
    congr 1
    funext z
    have h : ζ - z = -(z - ζ) := by ring
    rw [div_eq_mul_inv, div_eq_mul_inv, h, inv_neg, mul_neg]
  calc
    ∫ z, Work.MRMT.dzbar ψ z / (ζ - z)
        = - ∫ z, Work.MRMT.dzbar ψ z / (z - ζ) := hneg
    _ = - (-(Real.pi : ℂ) * ψ ζ) := by rw [key]
    _ = (Real.pi : ℂ) * ψ ζ := by ring

end Work.MRMT.Cauchy
