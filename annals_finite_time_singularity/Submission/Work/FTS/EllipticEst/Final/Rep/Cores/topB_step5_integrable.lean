import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.slot20_bound
import Submission.Work.FTS.EllipticEst.H2W.Step5.s20SliceIntegrable
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceRegular
import Submission.Work.FTS.EllipticEst.Mine.FSlotsTwoD
import Submission.Work.FTS.EllipticEst.Mine.SourceBoundsTwoD
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.S20SrcAux
import Submission.Work.FTS.EllipticEst.Final.Rep.H2W.Step5.s20_honesty
import Submission.Work.FTS.EllipticEst.Cores.Pieces.TL2.smoothOpen_Gsrc
import Submission.Work.FTS.EllipticEst.WeakMoment.SliceSqBoundsOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-!
# `Cores/topB_step5_integrable`: the honesty of the five Step-5 slots at level `2`

The lemma proves that the five `z`-integrals appearing in the right-hand side of the level-`2`
Step-5 estimate (the `B`-half of the top angular slot of `∂_θθΨ`) are honest for every datum of
the weak class `TT.EllWeakPos α 2 F Ψ`:

* the source slot  `∫_z w² ∫_θ (∂_θ²Gsrc)² sin(2θ)^{4-γ}`,
* the Step-4 slot  `∫_z w² ∫_θ (∂_θ³Ψ)² sin(2θ)^{2-γ}`,
* the three lower-order slots `∫_z w² ∫_θ (∂_θ²Ψ)² sin(2θ)^{-η}`, `∫_z w² ∫_θ (∂_θΨ)²`,
  `∫_z w² ∫_θ Ψ²`.

The route is pointwise domination by the level-`2` `ℋ`-integrand of `∂_θθΨ` (components
`memB` of the weak class, and `memF` / `memA` for the source), together with the weighted slice
Poincaré inequality `SliceSqBoundsOpen` for the two unweighted lower-order slots (whose slices
are continuous on the closed angular interval by `remov.weakSliceRegular`, whence the
`θ`-endpoint conditions needed by the Poincaré inequality are available).

Pre-existing ingredients consumed here: `s20src_integrableOn_slotZ_sigma4_DzIter`,
`s20src_integrableOn_slotZ_sigma4_Az`, `s20src_integrableOn_slotZ_sEta_DzIter`,
`s20src_slotZ_Gsrc_le`, the pointwise slot bounds `Mine.sig4_slot_pointwise` and
`s20_honesty`, and `Cores.Pieces.TL2.smoothOpen_Gsrc` for the smoothness of the source.
-/

/-! ## The weighted slice Poincaré constant -/

/-- The constant of the weighted slice Poincaré inequality `SliceSqBoundsOpen`. -/
private noncomputable def topB_poincC : ℝ :=
  Classical.choose Work.FTS.EllipticEst.WeakMoment.SliceSqBoundsOpen

private theorem topB_poincC_pos : 0 < topB_poincC :=
  (Classical.choose_spec Work.FTS.EllipticEst.WeakMoment.SliceSqBoundsOpen).1

private theorem topB_poincC_spec {u : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn u Work.Spaces.Iθ) (h0 : u 0 = 0) (hp : u (Real.pi / 2) = 0)
    (h5 : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ topB_poincC * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) ∧
      MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ topB_poincC * (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)) :=
  (Classical.choose_spec Work.FTS.EllipticEst.WeakMoment.SliceSqBoundsOpen).2 u
    hsm hcont h0 hp h5

/-! ## The two lower-order slices of `Ψ` -/

/-- **The weighted slice Poincaré bounds for the slice `Ψ z ·`.**  Both `∫ (Ψ z ·)²` and
`∫ (∂_θΨ z ·)²` are dominated by `topB_poincC · ∫ (∂_θ²Ψ z ·)² sin(2θ)^{-η}` for `z > 0`: the
weighted Poincaré inequality gives the weighted versions, and `sin(2θ)^{-η} ≥ 1` on the open
interval turns them into the unweighted ones. -/
private theorem topB_slicePoincare_psi {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    {z : ℝ} (hz : 0 < z) :
    ((∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
        ≤ topB_poincC * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)) ∧
      ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        ≤ topB_poincC * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)) := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have hp : ContDiffOn ℝ n (fun θ' : ℝ => (z, θ')) (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
    have h2 := (h.smooth n).comp hp (fun θ' hθ' => ⟨hz, hθ'⟩)
    simpa [Function.comp_def, Function.uncurry] using h2
  obtain ⟨hcont, -, -, -, -, -, h7⟩ :=
    Work.FTS.EllipticEst.remov.weakSliceRegular 2 (by norm_num) α F Ψ hα hα4 h z hz
  have hcont' : ContinuousOn (fun θ : ℝ => Ψ z θ) Work.Spaces.Iθ := by
    simpa only [Work.Spaces.Iθ] using hcont
  obtain ⟨h1i, h1l, h2i, h2l⟩ :=
    topB_poincC_spec hsm hcont' (h.zero z) (h.pi_half z) h7
  have hone : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (1 : ℝ) ≤ Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.H2W.Step5.s20src_one_le_sEta_ae
  have hle1 : (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) h1i
      (by
        filter_upwards [hone] with θ hθ
        nlinarith [sq_nonneg (Ψ z θ)])
  have hle2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) h2i
      (by
        filter_upwards [hone] with θ hθ
        nlinarith [sq_nonneg (Work.Spaces.pthIter 1 Ψ z θ)])
  refine ⟨hle1.trans h1l, hle2.trans h2l⟩

/-! ## The outer transfer for the two unweighted lower-order slots -/

/-- **Outer integrability of the `∂_θΨ`- and `Ψ`-slots from the `η`-slot.**  Since the slicewise
Poincaré bounds hold for every `z > 0` and the `η`-slot is outer-integrable by hypothesis, the
two unweighted slots are outer-integrable as well. -/
private theorem topB_low_slots_outer {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ)
    (hA2 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iz) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2) Work.Spaces.Iz ∧
      MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) Work.Spaces.Iz := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hmaj : MeasureTheory.IntegrableOn (fun z => topB_poincC * ((Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iz := by
    simpa only [MeasureTheory.IntegrableOn, smul_eq_mul] using hA2.const_mul topB_poincC
  have haesmΨ : MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hH : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Ψ p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_w_sq).mul (hΨ.continuousOn.pow 2)
    have hstr := Work.FTS.EllipticEst.H2W.Step5.s20src_aesm_integral_Qd
      (H := fun z θ => (Work.Spaces.w z) ^ 2 * (Ψ z θ) ^ 2) hH
    simpa only [MeasureTheory.integral_const_mul] using hstr
  have haesmD : MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hH : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.pthIter 1 Ψ p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_w_sq).mul (hΨ.pth.continuousOn.pow 2)
    have hstr := Work.FTS.EllipticEst.H2W.Step5.s20src_aesm_integral_Qd
      (H := fun z θ => (Work.Spaces.w z) ^ 2 * (Work.Spaces.pthIter 1 Ψ z θ) ^ 2) hH
    simpa only [MeasureTheory.integral_const_mul] using hstr
  constructor
  · refine MeasureTheory.Integrable.mono' hmaj haesmD ?_
    filter_upwards [Work.FTS.EllipticEst.H2W.Step5.s20src_ae_pos_mem_Iz] with z hz
    have hpo := topB_slicePoincare_psi hα hα4 h hz
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (integral_nonneg fun θ => sq_nonneg _))]
    calc (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (topB_poincC * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
          mul_le_mul_of_nonneg_left hpo.2 (sq_nonneg _)
      _ = topB_poincC * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring
  · refine MeasureTheory.Integrable.mono' hmaj haesmΨ ?_
    filter_upwards [Work.FTS.EllipticEst.H2W.Step5.s20src_ae_pos_mem_Iz] with z hz
    have hpo := topB_slicePoincare_psi hα hα4 h hz
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _)
      (integral_nonneg fun θ => sq_nonneg _))]
    calc (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (topB_poincC * (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
          mul_le_mul_of_nonneg_left hpo.1 (sq_nonneg _)
      _ = topB_poincC * ((Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring

/-! ## The `σ₄`-slot of `∂_θ²F` -/

/-- **Outer integrability of the `σ₄`-slot of `∂_θ²F`.**  The pointwise slot bound
`Mine.sig4_slot_pointwise` dominates `w²(∂_θ²F)²σ₄` by `10·HkIntegrand α 2 F`. -/
private theorem topB_slotZ_F_sigma4_outer {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hFmem : Work.Spaces.HkMem α 2 F) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ
      (Work.Spaces.pthIter 2 F)
      (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) Work.Spaces.Iz := by
  have hgam2 : Work.Spaces.gam α ≤ 3 / 2 := by rw [Work.Spaces.gam]; linarith
  have hX : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 F) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hF 2
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ
        (Work.Spaces.pthIter 2 F)
        (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.EllipticEst.H2W.Step5.s20src_aesm_integral_Qd
      (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_slotFun hX
        (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_sigma4 α))
  have hmaj : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      10 * Work.Spaces.HkIntegrand α 2 F z θ) Work.Spaces.Iz := by
    have h := hFmem.2.const_mul 10
    refine h.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    simp only [MeasureTheory.integral_const_mul]
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  rw [Real.norm_of_nonneg (Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ_nonneg
    (fun θ hθ => Work.FTS.EllipticEst.H2W.Step5.s20src_sigma4_nonneg α hθ) z)]
  refine MeasureTheory.integral_mono_of_nonneg ?_ ((hFmem.1 z hz).const_mul 10) ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact Work.FTS.EllipticEst.H2W.Step5.s20src_slotFun_nonneg
      (fun θ' hθ' => Work.FTS.EllipticEst.H2W.Step5.s20src_sigma4_nonneg α hθ') z θ hθ
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hpt := Work.FTS.EllipticEst.Mine.sig4_slot_pointwise α hα (Work.Spaces.gam α)
      hgam2 le_rfl F z θ hθ
    simpa only [Work.FTS.EllipticEst.H2W.Step5.s20src_slotFun,
      Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth] using hpt

/-! ## The `σ₄`-slot of the source `∂_θ²Gsrc` -/

/-- **Outer integrability of the `σ₄`-slot of `∂_θ²Gsrc`.**  `s20src_slotZ_Gsrc_le` bounds the
source slot by the three pieces `∂_θ²F`, `∂_θ²(Az Ψ)` and `∂_θ²(D_zΨ)`, each of which is
outer-integrable against `σ₄`. -/
private theorem topB_slotZ_Gsrc_sigma4_outer {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.IntegrableOn (fun z => Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ
      (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
      (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z) Work.Spaces.Iz := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.remov.ws_smoothOpen_F h
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hGs : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ)) :=
    Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl
      (Work.FTS.EllipticEst.Cores.Pieces.TL2.smoothOpen_Gsrc h) 2
  have hmaj : MeasureTheory.IntegrableOn (fun z => 3 *
      (Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ (Work.Spaces.pthIter 2 F)
          (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
        + α ^ 4 * Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ
            (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Az Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z
        + (α * (5 + α)) ^ 2 * Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ
            (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
            (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z)) Work.Spaces.Iz := by
    have h1 := topB_slotZ_F_sigma4_outer hα hα4 hF h.memF
    have h2 := (Work.FTS.EllipticEst.H2W.Step5.s20src_integrableOn_slotZ_sigma4_Az
      hΨ h.memB hα4).const_mul (α ^ 4)
    have h3 := (Work.FTS.EllipticEst.H2W.Step5.s20src_integrableOn_slotZ_sigma4_DzIter
      hΨ h.memB hα4 1 (by norm_num)).const_mul ((α * (5 + α)) ^ 2)
    have h4 := ((h1.add h2).add h3).const_mul 3
    simpa only [MeasureTheory.IntegrableOn, smul_eq_mul, Pi.add_apply] using h4
  have haesm := Work.FTS.EllipticEst.H2W.Step5.s20src_aesm_integral_Qd
    (H := fun z θ => Work.FTS.EllipticEst.H2W.Step5.s20src_slotFun
      (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ))
      (Work.FTS.EllipticEst.Mine.sig4 (Work.Spaces.gam α)) z θ)
    (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_slotFun hGs
      (Work.FTS.EllipticEst.H2W.Step5.s20src_continuousOn_sigma4 α))
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  rw [Real.norm_of_nonneg (Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ_nonneg
    (fun θ hθ => Work.FTS.EllipticEst.H2W.Step5.s20src_sigma4_nonneg α hθ) z)]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
  · subst h0
    simp only [Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ_zero_left, mul_zero, add_zero]
    norm_num
  · exact Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ_Gsrc_le hα hα4 hF h.memF hΨ h.memB hpos

/-! ## The Step-4 slot of `∂_θ³Ψ` -/

/-- **Outer integrability of the `σ₂`-slot of `∂_θ³Ψ`.**  This is `s20_honesty`'s second
conjunct (`s20F3 = 8 w²(∂_θ³Ψ)²σ₂`) rescaled by `1/8`. -/
private theorem topB_slot3_Psi_sigma2_outer {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) Work.Spaces.Iz := by
  obtain ⟨-, -, -, h3z⟩ := Work.FTS.EllipticEst.H2W.Step5.s20_honesty α F Ψ hα hα4 h
  have h := h3z.const_mul (1 / 8)
  have h' : MeasureTheory.IntegrableOn (fun z => (1 / 8) *
      (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)) Work.Spaces.Iz := by
    simpa only [MeasureTheory.IntegrableOn, smul_eq_mul] using h
  refine h'.congr ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  show (1 / 8) * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ)
      = (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)
  rw [show (fun θ => Work.FTS.EllipticEst.H2W.s20F3 α Ψ z θ) = fun θ =>
      (8 * (Work.Spaces.w z) ^ 2) * ((Work.Spaces.pthIter 3 Ψ z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α)) from rfl]
  rw [MeasureTheory.integral_const_mul]
  ring

/-! ## The target -/

theorem topB_step5_integrable (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 3 Ψ z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the `η`-slot of `∂_θθΨ` (the third conjunct), directly from `HkMem α 2 (∂_θθΨ)`
  have hA2 : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h0 := Work.FTS.EllipticEst.H2W.Step5.s20src_integrableOn_slotZ_sEta_DzIter
      hΨ h.memB 0 (by norm_num)
    refine h0.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    simp only [Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ,
      Work.FTS.EllipticEst.H2W.Step5.s20src_slotFun, Work.Spaces.DzIter_zero]
    rw [MeasureTheory.integral_const_mul]
  -- the two unweighted lower-order slots (the fourth and fifth conjuncts)
  obtain ⟨hA1, hA0⟩ := topB_low_slots_outer hα hα4 h hA2
  -- the source slot (the first conjunct)
  have hJ2 : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2 *
      ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.Mine.Gsrc α F Ψ) z θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (4 - Work.Spaces.gam α))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h0 := topB_slotZ_Gsrc_sigma4_outer hα hα4 h
    refine h0.congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
    simp only [Work.FTS.EllipticEst.H2W.Step5.s20src_slotZ,
      Work.FTS.EllipticEst.H2W.Step5.s20src_slotFun]
    rw [MeasureTheory.integral_const_mul]
    simp only [Work.FTS.EllipticEst.Mine.sig4]
  -- the Step-4 slot (the second conjunct)
  have hM3 := topB_slot3_Psi_sigma2_outer hα hα4 h
  exact ⟨hJ2, hM3, hA2, hA1, hA0⟩

end

end Work.FTS.EllipticEst.Cores
