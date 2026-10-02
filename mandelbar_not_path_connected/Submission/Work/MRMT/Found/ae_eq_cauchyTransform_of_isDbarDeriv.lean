import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.weyl_lemma
import Submission.Work.MRMT.Weyl.analyticOn_eq_zero_of_ae_eq_of_decay
import Submission.Work.MRMT.Beltrami.cauchyTransform_inversion
import Submission.Work.MRMT.Beltrami.cauchyTransform_decay
import Submission.Work.MRMT.Found.sub_id_ae_eq_cauchyTransform_dzbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

/-- If `u` has weak `∂̄`-derivative `g`, where `g` is integrable with compact support, and `u`
decays like `C / ‖z‖` at infinity, then `u` agrees almost everywhere with the Cauchy transform
of `g`.

Proof.  By `∂̄(C g) = g` (`cauchyTransform_inversion`) the difference `v = u - C g` has vanishing
weak `∂̄`-derivative, so by Weyl's lemma it agrees a.e. with an entire function `F`.  Both `u`
(hypothesis) and `C g` (decay of the Cauchy transform of a compactly supported `L¹` function)
decay like `C/‖z‖`, hence so does `v`; as `F =ᵐ v`, the entire function `F` decays and must
vanish.  Therefore `u - C g =ᵐ 0`. -/
theorem ae_eq_cauchyTransform_of_isDbarDeriv {u g : ℂ → ℂ} {R : ℝ}
    (hu : MeasureTheory.LocallyIntegrable u (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hg : Work.MRMT.IsDbarDeriv u g)
    (hgint : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hgsupp : Function.support g ⊆ Metric.closedBall 0 R)
    (hdec : ∃ C R' : ℝ, ∀ z : ℂ, R' ≤ ‖z‖ → ‖u z‖ ≤ C / ‖z‖) :
    u =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)] Work.MRMT.cauchyTransform g := by
  obtain ⟨C, R', hdec⟩ := hdec
  -- a radius containing the support of `g`
  have hM : ∀ ζ : ℂ, g ζ ≠ 0 → ‖ζ‖ ≤ max R 0 := by
    intro ζ hζ
    have hmem : ζ ∈ Metric.closedBall (0 : ℂ) R := hgsupp (Function.mem_support.mpr hζ)
    have hle : ‖ζ‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hmem
    exact le_trans hle (le_max_left _ _)
  have hgnorm : Integrable (fun ζ : ℂ => ‖g ζ‖) volume := hgint.norm
  -- the weak `∂̄`-derivative of `u - C g` vanishes
  have hsub : Work.MRMT.IsDbarDeriv (fun z => u z - Work.MRMT.cauchyTransform g z)
      (fun z => g z - g z) :=
    isDbarDeriv_sub hg (Work.MRMT.Beltrami.cauchyTransform_inversion g hgint)
  have hsub0 : Work.MRMT.IsDbarDeriv (fun z => u z - Work.MRMT.cauchyTransform g z)
      (0 : ℂ → ℂ) :=
    Work.MRMT.Weyl.isDbarDeriv_congr hsub (fun z => sub_self (g z))
  have hloc : LocallyIntegrable (fun z => u z - Work.MRMT.cauchyTransform g z) volume :=
    hsub0.1
  obtain ⟨F, hFa, hFeq⟩ :=
    Work.MRMT.Weyl.weyl_lemma hloc ⟨0, hsub0, Eventually.of_forall (fun _ => rfl)⟩
  -- `u - C g` decays like `1/‖z‖`
  have hdecDiff : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖u z - Work.MRMT.cauchyTransform g z‖ ≤ C / ‖z‖ := by
    refine ⟨C + 2 * (∫ ζ, ‖g ζ‖) / Real.pi, max R' (max 1 (2 * max R 0)), fun z hz => ?_⟩
    have hzR : R' ≤ ‖z‖ := le_trans (le_max_left _ _) hz
    have hz1 : 1 ≤ ‖z‖ :=
      le_trans (le_trans (le_max_left 1 (2 * max R 0)) (le_max_right R' _)) hz
    have hz2 : 2 * max R 0 ≤ ‖z‖ :=
      le_trans (le_trans (le_max_right 1 (2 * max R 0)) (le_max_right R' _)) hz
    have hA : ‖u z‖ ≤ C / ‖z‖ := hdec z hzR
    have hB : ‖Work.MRMT.cauchyTransform g z‖ ≤
        (2 * (∫ ζ, ‖g ζ‖)) / Real.pi / ‖z‖ :=
      Work.MRMT.Beltrami.decay_cauchyTransform_le g hgnorm hM hz1 hz2
    calc ‖u z - Work.MRMT.cauchyTransform g z‖
        ≤ ‖u z‖ + ‖Work.MRMT.cauchyTransform g z‖ := norm_sub_le _ _
      _ ≤ C / ‖z‖ + (2 * (∫ ζ, ‖g ζ‖)) / Real.pi / ‖z‖ := add_le_add hA hB
      _ = (C + 2 * (∫ ζ, ‖g ζ‖) / Real.pi) / ‖z‖ := by ring
  have hF0 : F = 0 :=
    Work.MRMT.Weyl.analyticOn_eq_zero_of_ae_eq_of_decay hFa hloc hFeq.symm hdecDiff
  have hdiff0 : (fun z => u z - Work.MRMT.cauchyTransform g z) =ᵐ[volume] (0 : ℂ → ℂ) := by
    filter_upwards [hFeq] with z hz
    rw [hF0] at hz
    simpa using hz
  filter_upwards [hdiff0] with z hz
  exact sub_eq_zero.mp hz

end Work.MRMT.Found
