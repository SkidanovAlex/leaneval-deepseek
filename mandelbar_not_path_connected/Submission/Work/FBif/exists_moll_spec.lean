import Mathlib
import Submission.Work.MRMT.Found.mollify_admissible

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

open MeasureTheory Filter Topology Function

/-- Smooth compactly supported approximations of a bounded-supported, a.e. bounded Beltrami
coefficient: the mollifications `μ_n = ρ_n ⋆ μ` by the bumps of `Work.MRMT.Weyl.bump`
(along a suitable subsequence) keep the same pointwise bound `k`, stay inside the fixed ball
of radius `R + 1`, and converge to `μ` a.e.

This is the explicit-hypotheses form of `Work.MRMT.Found.mollify_admissible`: the constants `k`
and `R` are those supplied by the caller rather than extracted from `Admissible μ`. -/
theorem exists_moll_spec {μ : ℂ → ℂ} {k R : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) (hR : 0 ≤ R)
    (hli : MeasureTheory.LocallyIntegrable μ (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    (hsup : Function.support μ ⊆ Metric.closedBall 0 R) :
    ∃ μn : ℕ → ℂ → ℂ,
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n)) ∧
      (∀ n, HasCompactSupport (μn n)) ∧
      (∀ n z, ‖μn n z‖ ≤ k) ∧
      (∀ n z, μn n z ≠ 0 → ‖z‖ ≤ R + 1) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
        Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds (μ z))) := by
  -- Package the hypotheses as an admissible coefficient, to extract integrability.
  have hAdm : Work.MRMT.Found.Admissible μ :=
    { meas := hli.aestronglyMeasurable
      bound := ⟨k, hk1, hb⟩
      bdd := Metric.isBounded_closedBall.subset hsup }
  have hintμ : MeasureTheory.Integrable μ (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    Work.MRMT.Found.mollify_admissible_integrable hAdm
  -- Smoothness of every mollification.
  have hcd : ∀ m : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.MRMT.Weyl.moll
        ((Work.MRMT.Weyl.bump m).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) μ) :=
    fun m => Work.MRMT.Weyl.contDiff_moll (Work.MRMT.Found.mollify_bump_contDiff m)
      (Work.MRMT.Found.mollify_bump_compactSupport m) hli
  -- Compact support of every mollification, with a uniform radius.
  have hcs_moll : ∀ m : ℕ, HasCompactSupport
      (Work.MRMT.Weyl.moll
        ((Work.MRMT.Weyl.bump m).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) μ) := by
    intro m
    have hsub : Function.support
        (Work.MRMT.Weyl.moll
          ((Work.MRMT.Weyl.bump m).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) μ) ⊆
        Metric.closedBall 0 (1 + R) :=
      Work.MRMT.Found.mollify_support_moll_subset (Work.MRMT.Found.mollify_bump_support_subset m)
        hsup
    have hbdd : Bornology.IsBounded (Function.support
        (Work.MRMT.Weyl.moll
          ((Work.MRMT.Weyl.bump m).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) μ)) :=
      Metric.isBounded_closedBall.subset hsub
    have hcomp := hbdd.isCompact_closure
    simpa [HasCompactSupport, tsupport] using hcomp
  -- The pointwise bound `k` is inherited.
  have hnorm : ∀ m : ℕ, ∀ z : ℂ,
      ‖Work.MRMT.Weyl.moll
        ((Work.MRMT.Weyl.bump m).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) μ z‖ ≤ k :=
    fun m z =>
      Work.MRMT.Found.mollify_norm_moll_le (Work.MRMT.Found.mollify_bump_continuous m)
        (Work.MRMT.Found.mollify_bump_compactSupport m) (Work.MRMT.Found.mollify_bump_mass m)
        (Work.MRMT.Found.mollify_bump_nonneg m) hk0 hli hb z
  -- The support bound `R + 1` is inherited.
  have hsupp_moll : ∀ m : ℕ, ∀ z : ℂ,
      Work.MRMT.Weyl.moll
        ((Work.MRMT.Weyl.bump m).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) μ z ≠ 0 →
        ‖z‖ ≤ R + 1 := by
    intro m z hz
    have h1 : z ∈ Metric.closedBall 0 (1 + R) :=
      Work.MRMT.Found.mollify_support_moll_subset (Work.MRMT.Found.mollify_bump_support_subset m)
        hsup hz
    simp only [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  -- Integrability of the mollifications (needed for the subsequence extraction).
  have hint_moll : ∀ m : ℕ, MeasureTheory.Integrable
      (Work.MRMT.Weyl.moll
        ((Work.MRMT.Weyl.bump m).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) μ)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) := fun m =>
    (hcd m).continuous.integrable_of_hasCompactSupport (hcs_moll m)
  -- Global `L¹` convergence, then a.e. convergence along a subsequence.
  have hL1 := Work.MRMT.Found.mollify_tendsto_integral_norm_moll hli hsup
  obtain ⟨ns, _hns, hae⟩ :=
    Work.MRMT.Found.mollify_ae_tendsto_of_tendsto_integral_norm hint_moll hintμ hL1
  exact ⟨fun n => Work.MRMT.Weyl.moll
      ((Work.MRMT.Weyl.bump (ns n)).normed (MeasureTheory.volume : MeasureTheory.Measure ℂ)) μ,
    fun n => hcd (ns n),
    fun n => hcs_moll (ns n),
    fun n z => hnorm (ns n) z,
    fun n z hz => hsupp_moll (ns n) z hz,
    by simpa using hae⟩

end Work.FBif
