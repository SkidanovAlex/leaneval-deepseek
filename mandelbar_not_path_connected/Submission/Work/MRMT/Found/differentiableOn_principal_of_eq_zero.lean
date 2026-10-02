/-
Copyright: Work.MRMT (mandelbar) subproject.

# `∂̄φ = 0` a.e. on an open set `U` forces `φ` to be holomorphic on `U`

Let `μ` be an admissible Beltrami coefficient, `d : PrincipalData μ` the record produced by the
limit construction, `U` an open set on which `μ` vanishes almost everywhere.  Then the principal
solution `d.φ` is complex differentiable on `U`.

The proof is the "AL" weak-limit Weyl lemma
(`Work.MRMT.Found.differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto`), applied to
the sequence `G n := d.Fn n` of C¹ diffeomorphism approximants of `φ`:

* each `Fn n` is `C¹`, hence locally Lipschitz on the open set `U`;
* `Fn n → φ` locally uniformly by `PrincipalData.tendsto_Fn`;
* the `L¹`-size of `∂̄(Fn n) = μn n · ∂(Fn n)` on a compact `L ⊆ U` tends to `0`.

The third point is the only real content.  It is split into two factors:
`∫_L ‖μn n‖ · ‖∂(Fn n)‖ ≤ (∫_L ‖μn n‖²)^{1/2} · (∫_L ‖∂(Fn n)‖²)^{1/2}` by Cauchy–Schwarz
(`lintegralAbsDbar_le_sqrt_mul`), and

* `∫_L ‖μn n‖² → 0`, because `μn n → μ = 0` almost everywhere on `L ⊆ U` while
  `‖μn n‖ ≤ k` uniformly (`tendsto_integral_normSq_muN`);
* `∫_L ‖∂(Fn n)‖²` is *eventually bounded*, and this is the point where the quasiconformality of
  `Fn n` is used: the pointwise distortion inequality `(1-k²)‖∂(Fn n)‖² ≤ J_{Fn n}`, together with
  the change-of-variables formula for the injective C¹ map `Fn n`, gives
  `∫_L ‖∂(Fn n)‖² ≤ vol (Fn n '' L)/(1-k²)` (`integral_normSq_dz_le_volume_image`).  Since
  `Fn n → φ` uniformly on the compact `L`, the images `Fn n '' L` all lie in one fixed ball
  (`exists_bound_volume_image_Fn`), which bounds the volumes uniformly in `n` -- uniformly only
  for `n ≥ N`, which is exactly what an `atTop` limit needs.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.lintegralAbsDbar_comp_eq
import Submission.Work.MRMT.Found.differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto
import Submission.Work.MRMT.Found.integral_normSq_dz_le_volume_image
import Submission.Work.MRMT.Found.exists_bound_volume_image_Fn
import Submission.Work.MRMT.Found.tendsto_integral_normSq_muN
import Submission.Work.MRMT.Found.lintegralAbsDbar_le_sqrt_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-! ## Auxiliary lemmas -/

/-- A `C¹` function is locally Lipschitz on any set. -/
theorem locallyLipschitzOn_of_contDiff_one {f : ℂ → ℂ} {U : Set ℂ} (hf : ContDiff ℝ 1 f) :
    LocallyLipschitzOn U f :=
  hf.locallyLipschitz.locallyLipschitzOn

/-- Squeeze lemma for `ℝ≥0∞`-valued sequences tending to `0`. -/
theorem tendsto_nhds_zero_of_eventually_le {u v : ℕ → ℝ≥0∞}
    (h : ∀ᶠ n in Filter.atTop, u n ≤ v n) (hv : Filter.Tendsto v Filter.atTop (nhds 0)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  rw [ENNReal.tendsto_nhds_zero] at hv ⊢
  intro ε hε
  filter_upwards [hv ε hε, h] with n hn hle
  exact le_trans hle hn

/-! ## The main theorem -/

theorem differentiableOn_principal_of_eq_zero {μ : ℂ → ℂ} (hμ : Admissible μ) (d : PrincipalData μ)
    {U : Set ℂ} (hU : IsOpen U)
    (h0 : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), z ∈ U → μ z = 0) :
    DifferentiableOn ℂ (d.φ : ℂ → ℂ) U := by
  refine differentiableOn_of_tendstoLocallyUniformly_of_lintegral_tendsto hU ?_ d.tendsto_Fn ?_
  · -- the approximants are locally Lipschitz on `U`
    intro n
    exact locallyLipschitzOn_of_contDiff_one (d.contDiff_Fn n)
  · intro L hL hLU
    -- the images `Fn n '' L` stay in a fixed bounded set, so their areas are bounded
    obtain ⟨Cb, hCb⟩ := exists_bound_volume_image_Fn d hL
    have hk0 : 0 ≤ d.k := le_trans (norm_nonneg (d.μn 0 0)) (d.norm_μn 0 0)
    have hpos : 0 < 1 - d.k ^ 2 := by nlinarith [d.hk]
    -- hence `∫_L ‖∂(Fn n)‖²` is eventually bounded by `Cb / (1 - k²)`
    have hbdz : ∀ᶠ n in Filter.atTop,
        ∫ z in L, ‖dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2 ≤ Cb / (1 - d.k ^ 2) := by
      filter_upwards [hCb] with n hn
      calc ∫ z in L, ‖dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2
          ≤ ((MeasureTheory.volume : MeasureTheory.Measure ℂ) (((d.Fn n) : ℂ → ℂ) '' L)).toReal
              / (1 - d.k ^ 2) :=
            integral_normSq_dz_le_volume_image hk0 d.hk (d.contDiff_Fn n) (d.beltrami_Fn n)
              (d.norm_μn n) hL
        _ ≤ Cb / (1 - d.k ^ 2) := div_le_div_of_nonneg_right hn hpos.le
    -- `∫_L ‖μn n‖² → 0`, because `μn n → μ = 0` a.e. on `L`
    have hmu : Filter.Tendsto (fun n => ∫ z in L, ‖d.μn n z‖ ^ 2) Filter.atTop (nhds 0) :=
      tendsto_integral_normSq_muN d hL hLU h0
    have hlim : Filter.Tendsto
        (fun n => ENNReal.ofReal (Real.sqrt (∫ z in L, ‖d.μn n z‖ ^ 2)
          * Real.sqrt (Cb / (1 - d.k ^ 2)))) Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun n => Real.sqrt (∫ z in L, ‖d.μn n z‖ ^ 2)
          * Real.sqrt (Cb / (1 - d.k ^ 2))) Filter.atTop (nhds 0) := by
        simpa using hmu.sqrt.mul_const (Real.sqrt (Cb / (1 - d.k ^ 2)))
      simpa using ENNReal.tendsto_ofReal h2
    refine tendsto_nhds_zero_of_eventually_le ?_ hlim
    filter_upwards [hbdz] with n hn
    -- Cauchy–Schwarz for the two factors, then the eventual bound on the second one
    calc lintegralAbsDbar ((d.Fn n) : ℂ → ℂ) L
        ≤ ENNReal.ofReal (Real.sqrt (∫ z in L, ‖d.μn n z‖ ^ 2)
            * Real.sqrt (∫ z in L, ‖dz ((d.Fn n) : ℂ → ℂ) z‖ ^ 2)) :=
          lintegralAbsDbar_le_sqrt_mul ((d.contDiff_μn n).continuous.aestronglyMeasurable)
            (d.norm_μn n) (d.contDiff_Fn n) (d.beltrami_Fn n) hL
      _ ≤ ENNReal.ofReal (Real.sqrt (∫ z in L, ‖d.μn n z‖ ^ 2)
            * Real.sqrt (Cb / (1 - d.k ^ 2))) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hn) (Real.sqrt_nonneg _)

end Work.MRMT.Found
