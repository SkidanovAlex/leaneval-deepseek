import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib
import Submission.Work.FTS.EllipticEst.H2W.PropH2Base
import Submission.Work.FTS.EllipticEst.H2W.lzeroSliceFiber
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.lzeroSlicePoleBound
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SliceLocal.integrableOn_sinCos2_Lzero1
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.H2W.PsiSlices.pzIterLevelIdentities
import Submission.Work.H2W.PsiSlices.shiftedSourcePoleBound
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.H2W.PsiSlices.pzIter_dilate
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.ReductionsB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.PsiSlices

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

/-! ## The covariance reduction: it suffices to prove the conclusion at `z = 1`

Because the elliptic operator is an Euler-type operator, the class `WeakPos2` is invariant under
the radial dilation `z ↦ lam·z`, and the iterated radial derivative of a dilated datum is `lam^m`
times the dilated slice.  Hence a proof of the conclusion *at the single point* `z = 1`, for every
class datum, gives the conclusion at every `z > 0` (and so a.e.): the remaining content of the
target is a *pointwise* statement, with no measure theory in `z`. -/

/-- **The covariance reduction.**  If the conclusion of the target holds at `z = 1` for every
weak-class datum, then it holds a.e.  The two dilation inputs are the child lemmas
`H2W.PsiSlices.weakPos2_dilate` and `H2W.PsiSlices.pzIter_dilate`; they are carried as explicit
hypotheses here so that this file does not depend on their build order. -/
theorem pzIterSliceIntegrable_of_at_one
    (h1 : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ m : ℕ, m ≤ 4 →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pzIter m Ψ 1 θ * Work.Elliptic.sinCos2 θ)
          Work.Spaces.Iθ)
    (hdilate : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ lam : ℝ, 0 < lam →
        Work.FTS.EllipticEst.WeakPos2 α (fun z θ => F (lam * z) θ) (fun z θ => Ψ (lam * z) θ))
    (hchain : ∀ (Ψ : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      ∀ lam z : ℝ, 0 < lam → ∀ m : ℕ, ∀ θ : ℝ,
        Work.Spaces.pzIter m (fun z θ => Ψ (lam * z) θ) z θ
          = lam ^ m * Work.Spaces.pzIter m Ψ (lam * z) θ) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∀ m : ℕ, m ≤ 4 →
          MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Spaces.pzIter m Ψ z θ * Work.Elliptic.sinCos2 θ)
            Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
  intro m hm
  have hz0 : 0 < z := hz
  have hdil := hdilate α F Ψ h z hz0
  have hslice := h1 α (fun z' θ => F (z * z') θ) (fun z' θ => Ψ (z * z') θ) hα hα4 hdil m hm
  have hfun : (fun θ : ℝ => Work.Spaces.pzIter m (fun z' θ => Ψ (z * z') θ) 1 θ
      * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => z ^ m * (Work.Spaces.pzIter m Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    funext θ
    rw [hchain Ψ h.2.2.2.2.2.2.1 z 1 hz0 m θ, mul_one]
    ring
  rw [hfun] at hslice
  refine (hslice.const_mul ((z ^ m)⁻¹)).congr (Filter.Eventually.of_forall fun θ => ?_)
  show (z ^ m)⁻¹ * (z ^ m * (Work.Spaces.pzIter m Ψ z θ * Work.Elliptic.sinCos2 θ))
    = Work.Spaces.pzIter m Ψ z θ * Work.Elliptic.sinCos2 θ
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m (ne_of_gt hz0)), one_mul]

/-! ## The `θ`-side bridge for the *shifted* operator, and the reduction to levels 3 and 4

`H2W.PsiSlices.shiftedSourcePoleBound` (the child lemma proved from the shifted operator's own
indicial structure) converts a `sinθcos²θ`-integrable source of `Lzero1 - c` into the pole bound.
Combining it with the level-1 and level-2 identities turns the reduction around: the `z`-regress
now closes *downward*, from the top two levels.

Precisely: given the σ-integrability of `∂_z³Ψ(z,·)` and `∂_z⁴Ψ(z,·)` for a.e. `z`,
* the level-2 identity written as `(Lzero1 - γ₂)(∂_z²Ψ) = ∂_z²F + (4α²z+α(5+α)z)∂_z³Ψ + α²z²∂_z⁴Ψ`
  gives `∂_z²Ψ` (bridge with `c = γ₂ = 2α² + 2α(5+α)`);
* the level-1 identity written as `(Lzero1 - γ₁)(∂_zΨ) = ∂_zF + 2α²z∂_z²Ψ + α²z²∂_z³Ψ + α(5+α)z∂_z²Ψ`
  gives `∂_zΨ` (bridge with `c = γ₁ = α(5+α)`);
* the level-0 identity (`γ₀ = 0`) gives `Ψ` itself (the unshifted bridge).

So the remaining content of the target is exactly the case `m = 3, 4` — the datum-side endpoint
rigidity at the top two levels (the requester's "genuinely new content is `m = 4`"). -/

/-- **From the pole bound to the σ-integrability of the slice** (the arithmetic shared by the
unshifted and shifted bridges). -/
theorem sigmaIntegrable_of_poleBound {u : ℝ → ℝ}
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |u θ| ≤ C * (1 / θ + 1 / (Real.pi / 2 - θ))) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  obtain ⟨C, hC, hbound⟩ := h
  have hfin : (volume.restrict Work.Spaces.Iθ) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Work.Spaces.Iθ,
      Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    ⟨lt_top_iff_ne_top.mpr hfin⟩
  have hcont : ContinuousOn u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := (hu 1).continuousOn
  have haesm : AEStronglyMeasurable (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) := by
    have h1 : AEStronglyMeasurable (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      (hcont.mul continuous_sinCos2_psi.continuousOn).aestronglyMeasurable measurableSet_Ioo
    rw [restrict_Iθ_eq_restrict_Ioo_psi]
    exact h1
  rw [MeasureTheory.IntegrableOn]
  refine MeasureTheory.Integrable.of_bound haesm (C * (1 + Real.pi / 2)) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs, abs_mul]
  rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
  · rcases lt_or_eq_of_le hθ.2 with hθ1 | hθ1
    · have hσ : 0 ≤ Work.Elliptic.sinCos2 θ := sinCos2_nonneg_Ioo ⟨hθ0, hθ1⟩
      have hb := hbound θ ⟨hθ0, hθ1⟩
      rw [abs_of_nonneg hσ]
      calc |u θ| * Work.Elliptic.sinCos2 θ
          ≤ (C * (1 / θ + 1 / (Real.pi / 2 - θ))) * Work.Elliptic.sinCos2 θ :=
            mul_le_mul_of_nonneg_right hb hσ
        _ = C * (Work.Elliptic.sinCos2 θ * (θ⁻¹ + (Real.pi / 2 - θ)⁻¹)) := by
            rw [one_div, one_div]; ring
        _ ≤ C * (1 + Real.pi / 2) :=
            mul_le_mul_of_nonneg_left (sinCos2_mul_poleWeight_le ⟨hθ0, hθ1⟩) hC
    · rw [hθ1, show Work.Elliptic.sinCos2 (Real.pi / 2) = 0 by
            simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two]]
      simp only [abs_zero, mul_zero]
      exact mul_nonneg hC (by linarith [Real.pi_pos])
  · rw [← hθ0, show Work.Elliptic.sinCos2 0 = 0 by simp [Work.Elliptic.sinCos2]]
    simp only [abs_zero, mul_zero]
    exact mul_nonneg hC (by linarith [Real.pi_pos])

/-- **The `θ`-side bridge for the shifted operator** `Lzero1 - c`: a `sinθcos²θ`-integrable source
gives the pole bound (`H2W.PsiSlices.shiftedSourcePoleBound`) and hence the σ-integrability of the
slice. -/
theorem sigmaIntegrable_of_shiftedSourceIntegrable (c : ℝ) (u : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.sinCos2 θ * |Work.FTS.EllipticEst.Lzero1 u θ - c * u θ|)
      Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
  sigmaIntegrable_of_poleBound hu
    (Work.H2W.PsiSlices.shiftedSourcePoleBound c u hu h)

/-- **The shifted bridge in pointwise form**: if `(Lzero1 - c)u = R` on the open interval and `R`
is σ-integrable, then `u` is. -/
theorem sigmaIntegrable_of_pointwiseShiftedSource (c : ℝ) (u R : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hR : MeasureTheory.IntegrableOn (fun θ : ℝ => R θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hid : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 u θ - c * u θ = R θ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  refine sigmaIntegrable_of_shiftedSourceIntegrable c u hu ?_
  refine (sigmaIntegrable_abs_of_integrable hR).congr ?_
  filter_upwards [ae_mem_Ioo_Iθ_psi] with θ hθ
  rw [hid θ hθ]

/-- **The target from the datum-side endpoint rigidity at levels 3 and 4.** -/
theorem pzIterSliceIntegrable_of_levels34
    (h34 : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        (MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ)
            Work.Spaces.Iθ)
        ∧ (MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Spaces.pzIter 4 Ψ z θ * Work.Elliptic.sinCos2 θ)
            Work.Spaces.Iθ)) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∀ m : ℕ, m ≤ 4 →
          MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Spaces.pzIter m Ψ z θ * Work.Elliptic.sinCos2 θ)
            Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h
  have hsm := h.2.2.2.2.2.2.1
  obtain ⟨hId1, hId2⟩ := Work.H2W.PsiSlices.pzIterLevelIdentities α F Ψ hα hα4 h
  have hFm : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ m ≤ 2, MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pzIter m F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    fun z hz m hm => Work.FTS.EllipticEst.H2W.lzeroSliceFiber α F Ψ hα hα4 h z hz m hm
  filter_upwards [h34 α F Ψ hα hα4 h, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z h34z hz
  have hz0 : 0 < z := hz
  obtain ⟨hu3, hu4⟩ := h34z
  -- level 2, from the level-2 identity with c = γ₂
  have hu2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    refine sigmaIntegrable_of_pointwiseShiftedSource (2 * α ^ 2 + 2 * α * (5 + α))
      (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
      (fun θ => Work.Spaces.pzIter 2 F z θ
        + (4 * α ^ 2 * z + α * (5 + α) * z) * Work.Spaces.pzIter 3 Ψ z θ
        + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ)
      (contDiffOn_slice_pzIter_psi hsm hz0 2) ?_ ?_
    · have hp1 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pzIter 2 F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
        hFm z hz 2 (by norm_num)
      have hp2 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (4 * α ^ 2 * z + α * (5 + α) * z)
            * (Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ :=
        hu3.const_mul (4 * α ^ 2 * z + α * (5 + α) * z)
      have hp3 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => α ^ 2 * z ^ 2
            * (Work.Spaces.pzIter 4 Ψ z θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ :=
        hu4.const_mul (α ^ 2 * z ^ 2)
      refine ((hp1.add hp2).add hp3).congr (Filter.Eventually.of_forall fun θ => ?_)
      show Work.Spaces.pzIter 2 F z θ * Work.Elliptic.sinCos2 θ
          + (4 * α ^ 2 * z + α * (5 + α) * z)
            * (Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ)
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 4 Ψ z θ * Work.Elliptic.sinCos2 θ)
        = (Work.Spaces.pzIter 2 F z θ
            + (4 * α ^ 2 * z + α * (5 + α) * z) * Work.Spaces.pzIter 3 Ψ z θ
            + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 4 Ψ z θ) * Work.Elliptic.sinCos2 θ
      ring
    · intro θ hθ
      rw [hId2 z hz0 θ hθ.1 hθ.2]
      ring
  -- level 1, from the level-1 identity with c = γ₁
  have hu1 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.pzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    refine sigmaIntegrable_of_pointwiseShiftedSource (α * (5 + α))
      (fun θ => Work.Spaces.pzIter 1 Ψ z θ)
      (fun θ => Work.Spaces.pzIter 1 F z θ
        + 2 * α ^ 2 * z * Work.Spaces.pzIter 2 Ψ z θ
        + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ
        + α * (5 + α) * z * Work.Spaces.pzIter 2 Ψ z θ)
      (contDiffOn_slice_pzIter_psi hsm hz0 1) ?_ ?_
    · have hp1 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pzIter 1 F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
        hFm z hz 1 (by norm_num)
      have hp2 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => 2 * α ^ 2 * z
            * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ :=
        hu2.const_mul (2 * α ^ 2 * z)
      have hp3 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => α ^ 2 * z ^ 2
            * (Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ :=
        hu3.const_mul (α ^ 2 * z ^ 2)
      have hp4 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => α * (5 + α) * z
            * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ :=
        hu2.const_mul (α * (5 + α) * z)
      refine (((hp1.add hp2).add hp3).add hp4).congr
        (Filter.Eventually.of_forall fun θ => ?_)
      show Work.Spaces.pzIter 1 F z θ * Work.Elliptic.sinCos2 θ
          + 2 * α ^ 2 * z * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 3 Ψ z θ * Work.Elliptic.sinCos2 θ)
          + α * (5 + α) * z * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
        = (Work.Spaces.pzIter 1 F z θ
            + 2 * α ^ 2 * z * Work.Spaces.pzIter 2 Ψ z θ
            + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 3 Ψ z θ
            + α * (5 + α) * z * Work.Spaces.pzIter 2 Ψ z θ) * Work.Elliptic.sinCos2 θ
      ring
    · intro θ hθ
      rw [hId1 z hz0 θ hθ.1 hθ.2]
      ring
  -- level 0, from the level-0 identity and the unshifted bridge
  have hu0 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    refine sigmaIntegrable_of_pointwiseShiftedSource 0 (fun θ => Ψ z θ)
      (fun θ => Work.Spaces.pzIter 0 F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        + α * (5 + α) * z * Work.Spaces.pzIter 1 Ψ z θ)
      (contDiffOn_slice_pzIter_psi hsm hz0 0) ?_ ?_
    · have hp1 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pzIter 0 F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
        hFm z hz 0 (by norm_num)
      have hp2 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => α ^ 2 * z ^ 2
            * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ :=
        hu2.const_mul (α ^ 2 * z ^ 2)
      have hp3 : MeasureTheory.IntegrableOn
          (fun θ : ℝ => α * (5 + α) * z
            * (Work.Spaces.pzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ)) Work.Spaces.Iθ :=
        hu1.const_mul (α * (5 + α) * z)
      refine ((hp1.add hp2).add hp3).congr (Filter.Eventually.of_forall fun θ => ?_)
      show Work.Spaces.pzIter 0 F z θ * Work.Elliptic.sinCos2 θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
          + α * (5 + α) * z * (Work.Spaces.pzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ)
        = (Work.Spaces.pzIter 0 F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
            + α * (5 + α) * z * Work.Spaces.pzIter 1 Ψ z θ) * Work.Elliptic.sinCos2 θ
      ring
    · intro θ hθ
      rw [lzero1_slice_eq h hz0 hθ]
      simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, zero_mul, sub_zero]
      all_goals ring
  intro m hm
  interval_cases m
  · exact hu0
  · exact hu1
  · exact hu2
  · exact hu3
  · exact hu4
/-! ## The unconditional covariance reduction (the two dilation children are proved)

Both dilation inputs of `pzIterSliceIntegrable_of_at_one` are now available in the tree
(`H2W.PsiSlices.weakPos2_dilate` and `H2W.PsiSlices.pzIter_dilate`), so the reduction is
unconditional: the target is *equivalent* to the pointwise statement at `z = 1`. -/

/-- **The target from the conclusion at `z = 1`.**  Unconditional form of
`pzIterSliceIntegrable_of_at_one`: the two dilation inputs are discharged by the proved children
`H2W.PsiSlices.weakPos2_dilate` and `H2W.PsiSlices.pzIter_dilate`. -/
theorem pzIterSliceIntegrable_of_at_one_clean
    (h1 : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ m : ℕ, m ≤ 4 →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => Work.Spaces.pzIter m Ψ 1 θ * Work.Elliptic.sinCos2 θ)
          Work.Spaces.Iθ) :
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.WeakPos2 α F Ψ →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        ∀ m : ℕ, m ≤ 4 →
          MeasureTheory.IntegrableOn
            (fun θ : ℝ => Work.Spaces.pzIter m Ψ z θ * Work.Elliptic.sinCos2 θ)
            Work.Spaces.Iθ :=
  pzIterSliceIntegrable_of_at_one h1
    (fun α F Ψ h lam hlam => Work.H2W.PsiSlices.weakPos2_dilate h hlam)
    (fun Ψ hΨ lam z hlam m θ => Work.H2W.PsiSlices.pzIter_dilate hΨ hlam m θ)

end
end Work.FTS.EllipticEst.H2W.PsiSlices
