/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Deleg/mixedPairAux2` — the mixed slot: `MixedHon` slices and joint measurability

Second half of the helper layer of `Deleg/mixedPairLimit`: the a.e. angular slice of the mixed
slot `V = z ∂_z∂_θu` coming from `MixedHon`, the AM–GM slice integrability of `σ f g`, and the
(continuity / measurability) facts about the four uncurried angular integrands.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Deleg.mixedPairAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Deleg

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

/-! ## 6. The mixed slot: `MixedHon` slices, AM–GM slice integrability -/

/-- The a.e. mixed honesty of `V = z ∂_z∂_θu` gives, a.e. in `z`, the integrability of the
`σ`-weighted square of `V` on the open angular interval. -/
theorem integrableOn_slice_of_MixedHon {u : ℝ → ℝ → ℝ} (hM : MixedHon u) :
    Filter.Eventually (fun z => IntegrableOn (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ
        * Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
      (MeasureTheory.ae (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  filter_upwards [hM.1] with z hz
  have h1 : IntegrableOn (fun θ => Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
      * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.IntegrableOn.mono_set hz (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  exact h1.congr (ae_restrict_of_forall_mem measurableSet_Ioo (fun θ _ => by ring))

/-- The radial marginal of `σ V²`, multiplied by the cutoff bound `wtB n`, is integrable. -/
theorem integrableOn_marginal_Vz_of_MixedHon {u : ℝ → ℝ → ℝ} (hM : MixedHon u) (n : ℕ) :
    IntegrableOn (fun z => Work.FTS.EllipticEst.AeColl.wtB n
      * ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AeColl.Vz u z θ ^ 2
          * Work.FTS.EllipticEst.AeColl.sigθ θ) (Set.Ioi (0 : ℝ)) :=
  (MeasureTheory.IntegrableOn.mono_set hM.2 Set.Ioi_subset_Ici_self).const_mul _

/-- The mixed angular slice `σ f g` is integrable (in `θ`) once `f` and `g` are `ℋ⁰`-honest and
the slice is a.e. strongly measurable: AM–GM bounds `σ|f g|` by `(σ f² + σ g²)/2`. -/
theorem integrableOn_sig_mul_mul_of_HkMem (α : ℝ) {f g : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α 0 f) (hg : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z)
    (hmeas : AEStronglyMeasurable (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ)
      (volume.restrict Work.Spaces.Iθ)) :
    IntegrableOn (fun θ => Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ * g z θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hle : volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) ≤ volume.restrict Work.Spaces.Iθ :=
    MeasureTheory.Measure.restrict_mono_set volume (show Set.Ioo (0 : ℝ) (Real.pi / 2)
      ⊆ Work.Spaces.Iθ from fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hf2 := integrableOn_sig_mul_sq_of_HkMem α hf hz
  have hg2 := integrableOn_sig_mul_sq_of_HkMem α hg hz
  refine Integrable.mono' (hf2.add hg2) (hmeas.mono_measure hle) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  have hs0 := sigθ_nonneg_of_mem_Iθ
    (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have h1 : |f z θ| * |g z θ| ≤ f z θ ^ 2 + g z θ ^ 2 := by
    nlinarith [sq_nonneg (|f z θ| - |g z θ|), sq_abs (f z θ), sq_abs (g z θ)]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs0]
  have h2 := mul_le_mul_of_nonneg_left h1 hs0
  calc Work.FTS.EllipticEst.AeColl.sigθ θ * |f z θ| * |g z θ|
      = Work.FTS.EllipticEst.AeColl.sigθ θ * (|f z θ| * |g z θ|) := by ring
    _ ≤ Work.FTS.EllipticEst.AeColl.sigθ θ * (f z θ ^ 2 + g z θ ^ 2) := h2
    _ = Work.FTS.EllipticEst.AeColl.sigθ θ * f z θ ^ 2
        + Work.FTS.EllipticEst.AeColl.sigθ θ * g z θ ^ 2 := by ring

/-! ## 7. Joint measurability of the four angular integrands -/

theorem aesm_joint_Vz {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2
        * Work.FTS.EllipticEst.AeColl.Vz u p.1 p.2 ^ 2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))) := by
  have hS := Work.FTS.EllipticEst.AeColl.SmoothOpen_of_AeData hA
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_sig_Q0
  have h2 : ContinuousOn
      (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz (Work.Spaces.pth u) p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    continuousOn_fst.mul (((hS.pth).pz).continuousOn)
  exact aesm_prod_of_continuousOn_Q0 (h1.mul (h2.pow 2))

theorem aesm_joint_Uz {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2
        * Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2 ^ 2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))) := by
  have hS := Work.FTS.EllipticEst.AeColl.SmoothOpen_of_AeData hA
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_sig_Q0
  have h2 : ContinuousOn (fun p : ℝ × ℝ => p.1 * Work.Spaces.pz u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := continuousOn_fst.mul (hS.pz).continuousOn
  exact aesm_prod_of_continuousOn_Q0 (h1.mul (h2.pow 2))

/-- The uncurried `σ θ · Az u · ∂_θθu` is continuous on the open quadrant (for `AeData u G`). -/
theorem continuousOn_joint_AzB {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2
        * Work.FTS.EllipticEst.AeColl.Az u p.1 p.2
        * Work.Spaces.pthIter 2 u p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hS := Work.FTS.EllipticEst.AeColl.SmoothOpen_of_AeData hA
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_sig_Q0
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Az u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_rad2 hS
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_ang2 hS
  exact (h1.mul h2).mul h3

/-- The uncurried `σ θ · Uz u · ∂_θθu` is continuous on the open quadrant. -/
theorem continuousOn_joint_UzB {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (hA : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2
        * Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2
        * Work.Spaces.pthIter 2 u p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  have hS := Work.FTS.EllipticEst.AeColl.SmoothOpen_of_AeData hA
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.sigθ p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_sig_Q0
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeColl.Uz u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_grad hS
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 u p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.FTS.EllipticEst.AeColl.continuousOn_ang2 hS
  exact (h1.mul h2).mul h3

end

end Work.FTS.EllipticEst.Deleg
