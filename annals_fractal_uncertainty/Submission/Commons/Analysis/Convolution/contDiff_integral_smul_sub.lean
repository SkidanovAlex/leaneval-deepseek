import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convex.Contractible
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable

open MeasureTheory
open scoped Convolution Topology

namespace Commons.Analysis.Convolution

/-- A real-analytic function on `Fin d → ℂ` with `d ≠ 0` and compact support is identically zero.

Indeed, a real-analytic function on the connected space `Fin d → ℂ` which vanishes on a nonempty
open set (here the complement of a closed ball containing the support) vanishes everywhere. -/
theorem eq_zero_of_contDiff_top_of_hasCompactSupport {d : ℕ} (hd : d ≠ 0)
    {f : (Fin d → ℂ) → ℝ} (hf : ContDiff ℝ ⊤ f) (hs : HasCompactSupport f) : f = 0 := by
  have han : AnalyticOnNhd ℝ f Set.univ := hf.analyticOnNhd
  obtain ⟨K, hK, hK0⟩ := exists_compact_iff_hasCompactSupport.mpr hs
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Fin d → ℂ)
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  let v : Fin d → ℂ := Pi.single ⟨0, hdpos⟩ 1
  have hv : v ≠ 0 := by simp [v]
  have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  set z₀ : Fin d → ℂ := ((|r| + 1) / ‖v‖) • v with hz₀def
  have hz₀norm : ‖z₀‖ = |r| + 1 := by
    rw [hz₀def, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (by positivity) hvn.le),
      div_mul_cancel₀ _ (ne_of_gt hvn)]
  have hz₀K : z₀ ∉ K := by
    intro hmem
    have h1 : dist z₀ 0 ≤ r := Metric.mem_closedBall.mp (hr hmem)
    rw [dist_eq_norm, sub_zero, hz₀norm] at h1
    have h2 : r ≤ |r| := le_abs_self r
    linarith
  have hnb : f =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz₀K] with y hy
    exact hK0 y hy
  exact AnalyticOnNhd.eq_of_eventuallyEq han analyticOnNhd_const hnb

/-- **Smoothness of a mollification.**  If `ρ : ℂᵈ → ℝ` is `C^n` with compact support and
`u : ℂᵈ → E` is locally integrable (`E` a real normed space), then the convolution
`z ↦ ∫ y, ρ y • u (z - y)` is `C^n`. -/
theorem contDiff_integral_smul_sub {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : (Fin d → ℂ) → ℝ} {u : (Fin d → ℂ) → E} {n : WithTop ℕ∞}
    (hρ : ContDiff ℝ n ρ) (hsρ : HasCompactSupport ρ)
    (hu : MeasureTheory.LocallyIntegrable u
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) :
    ContDiff ℝ n (fun z => ∫ y, ρ y • u (z - y)
      ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ))) := by
  by_cases hn : n = ⊤
  · -- `C^ω`: the kernel `ρ` is real-analytic with compact support, so it vanishes
    -- (unless `d = 0`, in which case the convolution is constant).
    rw [hn] at hρ ⊢
    by_cases hd : d = 0
    · subst hd
      have hconst : (fun z : Fin 0 → ℂ => ∫ y, ρ y • u (z - y)
            ∂(volume : Measure (Fin 0 → ℂ)))
          = fun _ : Fin 0 → ℂ => ∫ y, ρ y • u ((0 : Fin 0 → ℂ) - y)
            ∂(volume : Measure (Fin 0 → ℂ)) := by
        funext z
        rw [Subsingleton.elim z 0]
      rw [hconst]
      exact contDiff_const
    · rw [eq_zero_of_contDiff_top_of_hasCompactSupport hd hρ hsρ]
      simp only [Pi.zero_apply, zero_smul, integral_zero]
      exact contDiff_const
  · -- `C^n` for `n : ℕ∞`: written as a convolution with the kernel `ρ` and apply the
    -- smoothness of convolution with a compactly supported smooth factor.
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hn
    subst hm
    let L : E →L[ℝ] ℝ →L[ℝ] E := ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)
    have h := hsρ.contDiff_convolution_right (L := L) hu hρ
    have hfun : (u ⋆[L, volume] ρ) = fun z => ∫ y, ρ y • u (z - y) ∂volume := by
      funext z
      rw [convolution_eq_swap]
      simp only [L, ContinuousLinearMap.smulRightL_apply_apply,
        ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
    rw [hfun] at h
    exact h

end Commons.Analysis.Convolution