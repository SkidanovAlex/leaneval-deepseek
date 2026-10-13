import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces.pzSqSeta_le_Dz1_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∂_z f · sin(2θ)^{-η/2}` is `L²` on every compact `z`-box

The `θ`-weighted `L²`-mass of the plain `z`-derivative `∂_z f` over a compact box
`z ∈ [a,b]` (`0 < a`) is finite for `f ∈ SmoothQuad ∩ ℋ⁴`:

  `IntegrableOn (fun (s,θ) => (∂_z f s θ)² · sin(2θ)^{-η}) ([a,b] × [0,π/2])`.

The point of the box is the radial weight `w(z) = (1+z)²/z²`: on `[a,b]` it is bounded
below (`1 ≤ (b²/(1+a)⁴)·z²w(z)²`), so the boxed `∂_z`-slot is dominated by the first
`D_z`-slot term `(D_z f · w/sin(2θ)^{η/2})²` of the `ℋ⁴`-integrand
(`Pieces.pzSqSeta_le_Dz1_mul`), which is integrable because `HkMem α 4 f` gives the
iterated integrability of the whole `ℋ⁴`-integrand and `SmoothQuad` its a.e. strong
measurability on the product measure (`Work.Spaces.integrable_prod_of_iterated`).
-/

namespace Work.FTS.CoercivityFix.Coer1T.Hardy

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The open quadrant `(0,∞) × (0,π/2)` and continuity of the two integrands -/

/-- The open quadrant `(0,∞) × (0,π/2)`, on which both weights `w` and `sin(2θ)^{-c}`
are honest continuous functions. -/
private def QdPos : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)

private lemma QdPos_subset_quadU : QdPos ⊆ Work.Spaces.quadU := by
  intro p hp
  rw [QdPos, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp
  rw [Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith [hp.1], hp.2⟩

private lemma sin_two_pos_of_mem_QdPos {p : ℝ × ℝ} (hp : p ∈ QdPos) :
    0 < Real.sin (2 * p.2) := by
  rw [QdPos, Set.mem_prod, Set.mem_Ioo] at hp
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
    (by linarith [hp.2.2, Real.pi_pos])

/-- `θ ↦ sin(2θ)^c` is continuous on the open quadrant (where `sin(2θ) ≠ 0`). -/
private lemma continuousOn_sin_rpow_QdPos (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) QdPos :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_of_mem_QdPos hp)))

/-- The radial weight `w` is continuous on the open quadrant. -/
private lemma continuousOn_w_QdPos :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) QdPos := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  rw [QdPos, Set.mem_prod, Set.mem_Ioi] at hp
  exact pow_ne_zero 2 (ne_of_gt hp.1)

/-- `D_z f` is continuous on the open quadrant for `SmoothQuad f`. -/
private lemma continuousOn_Dz_QdPos {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter 1 f p.1 p.2) QdPos :=
  ((Work.FTS.LocData.contDiffOn_DzIter (V := Work.Spaces.quadU) Work.Spaces.isOpen_quadU
    hsm 1).continuousOn).mono QdPos_subset_quadU

/-- The `D_z`-slot integrand `(D_z f · w/sin(2θ)^{η/2})²` of the `ℋ⁴`-integrand is
continuous on the open quadrant. -/
private lemma continuousOn_Dz1slot_QdPos {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter 1 f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)) QdPos := by
  have hDz := continuousOn_Dz_QdPos hsm
  have hw : ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) QdPos :=
    continuousOn_w_QdPos.div (continuousOn_sin_rpow_QdPos _)
      (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_of_mem_QdPos hp) _))
  show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter 1 f p.1 p.2
    * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) QdPos
  exact (hDz.mul hw).pow 2

/-- The target integrand `(∂_z f)² · sin(2θ)^{-η}` is continuous on the open quadrant. -/
private lemma continuousOn_pzSqSeta_QdPos {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (Function.uncurry (fun z θ : ℝ => (Work.Spaces.pz f z θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) QdPos := by
  have hpz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2) QdPos :=
    ((Work.FTS.LocData.contDiffOn_pz (V := Work.Spaces.quadU) Work.Spaces.isOpen_quadU
      hsm).continuousOn).mono QdPos_subset_quadU
  show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.pz f p.1 p.2) ^ 2
    * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) QdPos
  exact (hpz.pow 2).mul (continuousOn_sin_rpow_QdPos _)

/-! ## Integrability of the `D_z`-slot on the product measure -/

/-- The `ℋ⁴`-integrand of a `SmoothQuad` function is integrable for the product of the two
restricted Lebesgue measures: `HkMem` supplies the iterated integrability and `SmoothQuad`
the a.e. strong measurability on the product (`Work.Spaces.integrable_prod_of_iterated`). -/
private lemma integrable_HkIntegrand_prod (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hAESM : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    show MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 4 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    exact Work.Spaces.aesm_of_continuousOn_Qd _
      (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α 4 f hsm)
  refine (Work.Spaces.integrable_prod_of_iterated
    (G := fun z θ : ℝ => Work.Spaces.HkIntegrand α 4 f z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ) hAESM ?_ ?_).1
  · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hmem.1
  · exact hmem.2

/-- The first `D_z`-slot of the `ℋ⁴`-integrand is integrable for the product measure. -/
private lemma integrable_Dz1slot_prod (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter 1 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hHint := integrable_HkIntegrand_prod α hsm hmem
  refine MeasureTheory.Integrable.mono' hHint ?_ ?_
  · exact Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_Dz1slot_QdPos hsm)
  · filter_upwards with p
    show ‖(Work.Spaces.DzIter 1 f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2‖
      ≤ Work.Spaces.HkIntegrand α 4 f p.1 p.2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact Work.Spaces.sq_le_HkIntegrand_z α 4 f p.1 p.2 1 (by norm_num)

/-! ## The statement -/

theorem pzSqSeta_box_integrable (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn
        (Function.uncurry (fun s θ : ℝ => (Work.Spaces.pz f s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  intro a b ha hab
  set C : ℝ := b ^ 2 / (1 + a) ^ 4 with hC
  -- the `D_z`-slot integrand, integrable on the whole domain
  have hGint := integrable_Dz1slot_prod α hsm hmem
  -- the box is contained in the domain `Iz ×ˢ Iθ`
  have hsub : Set.Icc a b ×ˢ Work.Spaces.Iθ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    intro p hp
    rw [Set.mem_prod] at hp
    refine ⟨?_, hp.2⟩
    show (0 : ℝ) ≤ p.1
    exact le_trans (le_of_lt ha) hp.1.1
  -- hence the `D_z`-slot integrand is integrable on the box
  have hGbox : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => (Work.Spaces.DzIter 1 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2))
      (MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)) := by
    rw [MeasureTheory.Measure.prod_restrict] at hGint
    exact hGint.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  refine MeasureTheory.Integrable.mono' (hGbox.const_mul C) ?_ ?_
  · -- a.e. strong measurability of the target on the box
    have hA := Work.Spaces.aesm_of_continuousOn_Qd _
      (continuousOn_pzSqSeta_QdPos hsm)
    rw [MeasureTheory.Measure.prod_restrict] at hA
    exact hA.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  · -- the pointwise box bound
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp
    obtain ⟨z, θ⟩ := p
    have hsin : 0 ≤ Real.sin (2 * θ) := by
      refine Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_
      · linarith [hθ.1]
      · linarith [hθ.2, Real.pi_pos]
    have hnn : 0 ≤ (Work.Spaces.pz f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hsin _)
    show ‖(Work.Spaces.pz f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))‖
      ≤ C * (Work.Spaces.DzIter 1 f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    rw [Real.norm_of_nonneg hnn, hC]
    exact Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces.pzSqSeta_le_Dz1_mul
      (f := f) ha hab z hz θ hθ

end

end Work.FTS.CoercivityFix.Coer1T.Hardy
