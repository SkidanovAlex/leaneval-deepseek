/-
Work.MRMT.Found — mollification of an admissible coefficient with a *prescribed* sup-bound.

`mollify_admissible` produces smooth compactly supported approximants `μ n → μ` whose sup-norm
bound is the one carried by the `Admissible` structure.  For the uniform Courant–Lebesgue
modulus of a *family* we need the approximants to be bounded by the *given* number `k` (the
bound assumed in the hypotheses).  This file provides that variant.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.mollify_admissible

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Topology ENNReal

noncomputable section

theorem mollify_admissible_of_bound {μ : ℂ → ℂ} (hμ : Admissible μ) {k : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) :
    ∃ (M : ℝ) (μn : ℕ → ℂ → ℂ),
      0 ≤ M ∧
      (∀ z : ℂ, μ z ≠ 0 → ‖z‖ ≤ M) ∧
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n)) ∧
      (∀ n, HasCompactSupport (μn n)) ∧
      (∀ n z, ‖μn n z‖ ≤ k) ∧
      (∀ n z, μn n z ≠ 0 → ‖z‖ ≤ M) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
        Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds (μ z))) := by
  obtain ⟨R, hR0, hsupp⟩ := mollify_admissible_ball hμ
  have hli : LocallyIntegrable μ (volume : Measure ℂ) := mollify_admissible_locallyIntegrable hμ
  have hintμ : Integrable μ (volume : Measure ℂ) := mollify_admissible_integrable hμ
  have hcd : ∀ m : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ) := by
    intro m
    exact Work.MRMT.Weyl.contDiff_moll (mollify_bump_contDiff m)
      (mollify_bump_compactSupport m) hli
  have hcs_moll : ∀ m : ℕ, HasCompactSupport
      (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ) := by
    intro m
    have hsub : Function.support
        (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ) ⊆
        Metric.closedBall 0 (1 + R) :=
      mollify_support_moll_subset (mollify_bump_support_subset m) hsupp
    have hb' : Bornology.IsBounded (Function.support
        (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ)) :=
      Metric.isBounded_closedBall.subset hsub
    have hcomp := hb'.isCompact_closure
    simpa [HasCompactSupport, tsupport] using hcomp
  have hnorm_moll : ∀ m : ℕ, ∀ z : ℂ,
      ‖Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ z‖ ≤ k := by
    intro m z
    exact mollify_norm_moll_le (mollify_bump_continuous m) (mollify_bump_compactSupport m)
      (mollify_bump_mass m) (mollify_bump_nonneg m) hk0 hli hb z
  have hsupp_moll : ∀ m : ℕ, ∀ z : ℂ,
      Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ z ≠ 0 →
        ‖z‖ ≤ R + 1 := by
    intro m z hz
    have h1 : z ∈ Metric.closedBall 0 (1 + R) :=
      mollify_support_moll_subset (mollify_bump_support_subset m) hsupp hz
    simp only [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  have hint_moll : ∀ m : ℕ, Integrable
      (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ)
      (volume : Measure ℂ) := fun m =>
    (hcd m).continuous.integrable_of_hasCompactSupport (hcs_moll m)
  have hL1 := mollify_tendsto_integral_norm_moll hli hsupp
  obtain ⟨ns, hns, hae⟩ := mollify_ae_tendsto_of_tendsto_integral_norm hint_moll hintμ hL1
  refine ⟨R + 1, fun m =>
    Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump (ns m)).normed (volume : Measure ℂ)) μ,
    by linarith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h1 : z ∈ Metric.closedBall 0 R := hsupp hz
    simp only [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  · intro m
    exact hcd (ns m)
  · intro m
    exact hcs_moll (ns m)
  · intro m z
    exact hnorm_moll (ns m) z
  · intro m z hz
    exact hsupp_moll (ns m) z hz
  · exact hae


/-- Same as `mollify_admissible_of_bound`, but with the radius of the support prescribed: this is
the form needed to keep the decay constants of the approximating solutions uniform in a family. -/
theorem mollify_admissible_of_bound_ball {μ : ℂ → ℂ} (hμ : Admissible μ) {k R : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hR0 : 0 ≤ R)
    (hsupp : Function.support μ ⊆ Metric.closedBall 0 R)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) :
    ∃ (μn : ℕ → ℂ → ℂ),
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n)) ∧
      (∀ n, HasCompactSupport (μn n)) ∧
      (∀ n z, ‖μn n z‖ ≤ k) ∧
      (∀ n z, μn n z ≠ 0 → ‖z‖ ≤ R + 1) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
        Filter.Tendsto (fun n => μn n z) Filter.atTop (nhds (μ z))) := by
  have hli : LocallyIntegrable μ (volume : Measure ℂ) := mollify_admissible_locallyIntegrable hμ
  have hintμ : Integrable μ (volume : Measure ℂ) := mollify_admissible_integrable hμ
  have hcd : ∀ m : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ) := by
    intro m
    exact Work.MRMT.Weyl.contDiff_moll (mollify_bump_contDiff m)
      (mollify_bump_compactSupport m) hli
  have hcs_moll : ∀ m : ℕ, HasCompactSupport
      (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ) := by
    intro m
    have hsub : Function.support
        (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ) ⊆
        Metric.closedBall 0 (1 + R) :=
      mollify_support_moll_subset (mollify_bump_support_subset m) hsupp
    have hb' : Bornology.IsBounded (Function.support
        (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ)) :=
      Metric.isBounded_closedBall.subset hsub
    have hcomp := hb'.isCompact_closure
    simpa [HasCompactSupport, tsupport] using hcomp
  have hnorm_moll : ∀ m : ℕ, ∀ z : ℂ,
      ‖Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ z‖ ≤ k := by
    intro m z
    exact mollify_norm_moll_le (mollify_bump_continuous m) (mollify_bump_compactSupport m)
      (mollify_bump_mass m) (mollify_bump_nonneg m) hk0 hli hb z
  have hsupp_moll : ∀ m : ℕ, ∀ z : ℂ,
      Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ z ≠ 0 →
        ‖z‖ ≤ R + 1 := by
    intro m z hz
    have h1 : z ∈ Metric.closedBall 0 (1 + R) :=
      mollify_support_moll_subset (mollify_bump_support_subset m) hsupp hz
    simp only [Metric.mem_closedBall, dist_zero_right] at h1
    linarith
  have hint_moll : ∀ m : ℕ, Integrable
      (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump m).normed (volume : Measure ℂ)) μ)
      (volume : Measure ℂ) := fun m =>
    (hcd m).continuous.integrable_of_hasCompactSupport (hcs_moll m)
  have hL1 := mollify_tendsto_integral_norm_moll hli hsupp
  obtain ⟨ns, hns, hae⟩ := mollify_ae_tendsto_of_tendsto_integral_norm hint_moll hintμ hL1
  refine ⟨fun m =>
    Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump (ns m)).normed (volume : Measure ℂ)) μ,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    exact hcd (ns m)
  · intro m
    exact hcs_moll (ns m)
  · intro m z
    exact hnorm_moll (ns m) z
  · intro m z hz
    exact hsupp_moll (ns m) z hz
  · exact hae

end

end Work.MRMT.Found
