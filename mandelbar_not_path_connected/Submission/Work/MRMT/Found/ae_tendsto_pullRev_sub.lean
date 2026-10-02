import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Wirtinger.beltramiOf_comp_antiholo
import Submission.Work.MRMT.AhlforsBers.null_preimage_entire

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology

/-- Complex conjugation is measure-preserving for Lebesgue measure on `ℂ`. -/
theorem measurePreserving_star :
    MeasureTheory.MeasurePreserving (star : ℂ → ℂ)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  have hfun : (star : ℂ → ℂ) = ⇑(RCLike.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) := by
    funext z; simp
  rw [hfun]
  exact LinearIsometryEquiv.measurePreserving _

/-- The pull-back of the failure set of the a.e. convergence `μn n → μ` under the
anti-holomorphic `f` is null. -/
theorem preimage_failure_null {μ : ℂ → ℂ} (d : Work.MRMT.Found.PrincipalData μ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ (star ∘ f))
    (hnc : ¬ ∃ c : ℂ, ∀ z, (star ∘ f) z = c) :
    (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      (f ⁻¹' {w : ℂ | ¬ Filter.Tendsto (fun n => d.μn n w) Filter.atTop (nhds (μ w))}) = 0 := by
  have hN0 : (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      {w : ℂ | ¬ Filter.Tendsto (fun n => d.μn n w) Filter.atTop (nhds (μ w))} = 0 :=
    MeasureTheory.ae_iff.mp d.tendsto_μn
  have hN'0 : (MeasureTheory.volume : MeasureTheory.Measure ℂ)
      ((star : ℂ → ℂ) ⁻¹' {w : ℂ | ¬ Filter.Tendsto (fun n => d.μn n w) Filter.atTop (nhds (μ w))})
        = 0 :=
    measurePreserving_star.quasiMeasurePreserving.preimage_null hN0
  have h := Work.MRMT.AhlforsBers.null_preimage_entire hf hnc hN'0
  convert h using 2
  ext z
  simp [Function.comp_apply]

theorem ae_tendsto_pullRev_sub {μ : ℂ → ℂ} (d : Work.MRMT.Found.PrincipalData μ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ (star ∘ f))
    (hnc : ¬ ∃ c : ℂ, ∀ z, (star ∘ f) z = c)
    (hinv : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      μ z = star (μ (f z)) * Work.MRMT.dzbar f z / star (Work.MRMT.dzbar f z)) :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => Work.MRMT.Found.pullRev (d.μn n) f z - d.μn n z)
        Filter.atTop (nhds 0) := by
  -- `f` is anti-holomorphic, hence `dz f` vanishes identically.
  have hdz : ∀ z, Work.MRMT.dz f z = 0 := fun z => Work.MRMT.Wirtinger.dz_of_antiholo (hf z)
  -- the failure set of the convergence `μn n → μ` pulled back by `f` is null
  have hcomp0 :
      (MeasureTheory.volume : MeasureTheory.Measure ℂ)
        (f ⁻¹' {w : ℂ | ¬ Filter.Tendsto (fun n => d.μn n w) Filter.atTop (nhds (μ w))}) = 0 :=
    preimage_failure_null d hf hnc
  have hae_comp : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => d.μn n (f z)) Filter.atTop (nhds (μ (f z))) := by
    rw [MeasureTheory.ae_iff]
    simpa using hcomp0
  filter_upwards [d.tendsto_μn, hae_comp, hinv] with z hz1 hz2 hiz
  have hdz0 : Work.MRMT.dz f z = 0 := hdz z
  -- the algebraic reduction of `pullRev` at an anti-holomorphic point
  have hpull : ∀ n, Work.MRMT.Found.pullRev (d.μn n) f z
      = star (d.μn n (f z)) * Work.MRMT.dzbar f z / star (Work.MRMT.dzbar f z) := by
    intro n
    rw [Work.MRMT.Found.pullRev, hdz0]
    simp
  -- the limit of the pull-back coefficient
  have hbase : Filter.Tendsto
      (fun n => star (d.μn n (f z)) * Work.MRMT.dzbar f z / star (Work.MRMT.dzbar f z))
      Filter.atTop
      (nhds (star (μ (f z)) * Work.MRMT.dzbar f z / star (Work.MRMT.dzbar f z))) :=
    ((Filter.Tendsto.star hz2).mul_const (Work.MRMT.dzbar f z)).div_const
      (star (Work.MRMT.dzbar f z))
  have hlim : Filter.Tendsto (fun n => Work.MRMT.Found.pullRev (d.μn n) f z)
      Filter.atTop (nhds (μ z)) := by
    rw [← hiz] at hbase
    simpa only [hpull] using hbase
  simpa using hlim.sub hz1

end Work.MRMT.Found
