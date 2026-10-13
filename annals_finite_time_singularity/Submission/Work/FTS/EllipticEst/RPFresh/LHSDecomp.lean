import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Blocks.alphaDz_pth_core_clean
import Submission.Work.EllipticEst.Core.mixedFamily_le
import Submission.Work.FTS.EllipticEst.RPFresh.OpIdentDz
import Submission.Work.FTS.EllipticEst.RPFresh.OpIdentMixed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The value decomposition of the `ℋ^k`-square of `α D_z ∂_θ V`

`Work.Spaces.HkSq α k (α D_z∂_θV)` is, by definition, the iterated integral of the nonnegative
`ℋ^k`-integrand.  This module proves that it is bounded by the sum of the integrals of the two
families of slices `mixIntS (D_z^r V)` (`r ≤ k`) and `mixedIntS α i j V` (`1 ≤ i`, `i + j ≤ k`),
*provided* the `z`-integrand of that sum is integrable (`IntegrableOn` in the statement).

The pointwise content is the Clairaut identity `D_z^j D_θ^i(D_z∂_θV) = D_z^{j+1}D_θ^i(∂_θV)` on
the open quadrant, which allows the `D_θ`-family of the `ℋ^k`-integrand of `D_z∂_θV` to be
rewritten as the `D_θ`-family of `∂_θV` shifted in `D_z`; the `D_z`-family is rewritten the same
way.  The `IntegrableOn` hypothesis is genuinely needed: the outer Bochner integral is not
monotone with respect to a non-integrable majorant (the summand Bochner integrals may be junk
`0`), so without it the two sides can lose different pieces.
-/

namespace Work.FTS.EllipticEst.RPFresh

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The two families of slice integrands -/

/-- The `D_z`-family slice integrand: the integrand of `mixIntS (D_z^r V)`. -/
def lhsZ (V : ℝ → ℝ → ℝ) (r : ℕ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.w z) ^ 2 *
    ((Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
      * Work.FTS.EllipticEst.thEta θ)

/-- The mixed-family slice integrand: the integrand of `mixedIntS α i j V` (with the same
`if`-condition as in `HkIntegrand`). -/
def lhsM (α : ℝ) (k : ℕ) (V : ℝ → ℝ → ℝ) (i j : ℕ) (z θ : ℝ) : ℝ :=
  if 1 ≤ i ∧ i + j ≤ k then
    (Work.Spaces.w z) ^ 2 *
      ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ)
  else 0

/-! ## Elementary facts -/

theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc

theorem measurableSet_Iz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici

theorem measurable_w : Measurable (fun z : ℝ => Work.Spaces.w z) := by
  have h : (fun z : ℝ => Work.Spaces.w z) = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h]
  have h1 : Measurable (fun z : ℝ => (1 + z) ^ 2) :=
    (measurable_const.add measurable_id).pow_const 2
  have h2 : Measurable (fun z : ℝ => z ^ 2) := measurable_id.pow_const 2
  exact h1.div h2

theorem pth_const_mul (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.pth g z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul_field]

theorem pz_const_mul (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.pz g z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_field]

theorem DzIter_const_mul (c : ℝ) (i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DzIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      show z * Work.Spaces.pz (fun z θ => c * Work.Spaces.DzIter i g z θ) z θ
        = c * (z * Work.Spaces.pz (Work.Spaces.DzIter i g) z θ)
      rw [pz_const_mul]
      ring

theorem DzIter_const_mul_apply (c : ℝ) (i : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter i (fun z θ => c * g z θ) z θ = c * Work.Spaces.DzIter i g z θ := by
  simpa using congrFun (congrFun (DzIter_const_mul c i g) z) θ

theorem DthIter_const_mul (c : ℝ) (i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      show Real.sin (2 * θ) * Work.Spaces.pth (fun z θ => c * Work.Spaces.DthIter i g z θ) z θ
        = c * (Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DthIter i g) z θ)
      rw [pth_const_mul]
      ring

theorem mixed_const_mul (c : ℝ) (j i : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.mixed j i g z θ := by
  rw [Work.Spaces.mixed, Work.Spaces.mixed, DthIter_const_mul, DzIter_const_mul]

theorem mixed_const_mul_apply (c : ℝ) (j i : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * g z θ) z θ
      = c * Work.Spaces.mixed j i g z θ := by
  simpa using congrFun (congrFun (mixed_const_mul c j i g) z) θ

theorem DzIter_succ_apply_pt (j : ℕ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter j (Work.Spaces.Dz g) z θ = Work.Spaces.DzIter (j + 1) g z θ := by
  simpa using congrFun (congrFun (Work.Blocks.DzIter_succ_apply j g) z) θ

theorem aesm_finset_sum {ι : Type*} {s : Finset ι} {φ : ι → ℝ → ℝ}
    {μ : MeasureTheory.Measure ℝ}
    (h : ∀ i ∈ s, AEStronglyMeasurable (φ i) μ) :
    AEStronglyMeasurable (fun a : ℝ => ∑ i ∈ s, φ i a) μ := by
  have h' : (fun a : ℝ => ∑ i ∈ s, φ i a) = ∑ i ∈ s, φ i := by
    funext a
    simp only [Finset.sum_apply]
  rw [h']
  exact Finset.aestronglyMeasurable_sum s h

theorem aesm_ite_pos {c : Prop} [Decidable c] {f : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ}
    (hc : c) (h : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun a : ℝ => if c then f a else 0) μ := by
  have h' : (fun a : ℝ => if c then f a else 0) = f := by
    funext a; rw [if_pos hc]
  rwa [h']

theorem aesm_ite_neg {c : Prop} [Decidable c] {f : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ}
    (hc : ¬c) :
    AEStronglyMeasurable (fun a : ℝ => if c then f a else 0) μ := by
  have h' : (fun a : ℝ => if c then f a else 0) = fun _ => (0 : ℝ) := by
    funext a; rw [if_neg hc]
  rw [h']
  exact aestronglyMeasurable_const

theorem mixIntS_nonneg (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ Work.EllipticEst.Core.mixIntS u z := by
  rw [Work.EllipticEst.Core.mixIntS]
  exact mul_nonneg (sq_nonneg _)
    (MeasureTheory.setIntegral_nonneg measurableSet_Iθ
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)))

theorem mixedIntS_nonneg (α : ℝ) (i j : ℕ) (u : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ Work.EllipticEst.Core.mixedIntS α i j u z := by
  rw [Work.EllipticEst.Core.mixedIntS]
  exact mul_nonneg (sq_nonneg _)
    (MeasureTheory.setIntegral_nonneg measurableSet_Iθ
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ)))

theorem lhsZ_nonneg (V : ℝ → ℝ → ℝ) (r : ℕ) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ lhsZ V r z θ := by
  rw [lhsZ]
  exact mul_nonneg (sq_nonneg _)
    (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ))

theorem lhsM_nonneg (α : ℝ) (k : ℕ) (V : ℝ → ℝ → ℝ) (i j : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ lhsM α k V i j z θ := by
  rw [lhsM]
  split_ifs with hc
  · exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))
  · exact le_refl 0

theorem thEta_zero_left : Work.FTS.EllipticEst.thEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.thEta, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
    Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]

theorem thEta_zero_right : Work.FTS.EllipticEst.thEta (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.thEta, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring,
    Real.sin_pi, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]

theorem thGam_zero_left {α : ℝ} (hα : 0 < α) : Work.FTS.EllipticEst.thGam α 0 = 0 := by
  rw [Work.FTS.EllipticEst.thGam, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
    Real.zero_rpow (by rw [Work.Spaces.gam]; intro hc; linarith)]

theorem thGam_zero_right {α : ℝ} (hα : 0 < α) :
    Work.FTS.EllipticEst.thGam α (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.thGam, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring,
    Real.sin_pi, Real.zero_rpow (by rw [Work.Spaces.gam]; intro hc; linarith)]

theorem lhsZ_zero_z (V : ℝ → ℝ → ℝ) (r : ℕ) (θ : ℝ) : lhsZ V r 0 θ = 0 := by
  have hw : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  rw [lhsZ, hw]
  ring

theorem lhsM_zero_z (α : ℝ) (k : ℕ) (V : ℝ → ℝ → ℝ) (i j : ℕ) (θ : ℝ) :
    lhsM α k V i j 0 θ = 0 := by
  have hw : Work.Spaces.w 0 = 0 := by simp [Work.Spaces.w]
  rw [lhsM]
  split_ifs with hc
  · rw [hw]; ring
  · rfl

theorem lhsZ_of_thEta_zero (V : ℝ → ℝ → ℝ) (r : ℕ) {z θ : ℝ}
    (h : Work.FTS.EllipticEst.thEta θ = 0) : lhsZ V r z θ = 0 := by
  rw [lhsZ, h, mul_zero, mul_zero]

theorem lhsM_of_thGam_zero (α : ℝ) (k : ℕ) (V : ℝ → ℝ → ℝ) (i j : ℕ) {z θ : ℝ}
    (h : Work.FTS.EllipticEst.thGam α θ = 0) : lhsM α k V i j z θ = 0 := by
  rw [lhsM]
  split_ifs with hc
  · rw [h, mul_zero, mul_zero]
  · rfl

theorem HkIntegrand_eq_zero_of_weights {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hH : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0)
    (hW : Work.Spaces.Wt α z θ = 0) :
    Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [hH, hW]

/-! ## The `θ`-integrals of the two families -/

theorem lhsZ_integral (V : ℝ → ℝ → ℝ) (r : ℕ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, lhsZ V r z θ)
      = Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z := by
  simp only [lhsZ, Work.EllipticEst.Core.mixIntS]
  rw [MeasureTheory.integral_const_mul]

theorem lhsM_integral (α : ℝ) (k : ℕ) (V : ℝ → ℝ → ℝ) (i j : ℕ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, lhsM α k V i j z θ)
      = (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0) := by
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · simp only [lhsM, if_pos hc, Work.EllipticEst.Core.mixedIntS]
    rw [MeasureTheory.integral_const_mul]
  · simp only [lhsM, if_neg hc, MeasureTheory.integral_zero]

/-! ## Subadditivity of the (Bochner) integral over nonnegative, a.e. strongly measurable
summands -/

/-- For nonnegative a.e. strongly measurable summands, the integral of the sum is bounded by
the sum of the integrals.  (The a.e. strong measurability cannot be dropped: without it the
Bochner integral of a summand may be junk `0` while the integral of the sum is not.) -/
theorem setIntegral_finset_sum_le {ι : Type*} (s : Set ℝ) (hs : MeasurableSet s) (t : Finset ι)
    (φ : ι → ℝ → ℝ)
    (hnn : ∀ i ∈ t, ∀ a ∈ s, 0 ≤ φ i a)
    (hsm : ∀ i ∈ t, AEStronglyMeasurable (φ i) (MeasureTheory.volume.restrict s)) :
    (∫ a in s, ∑ i ∈ t, φ i a) ≤ ∑ i ∈ t, ∫ a in s, φ i a := by
  by_cases h : IntegrableOn (fun a => ∑ i ∈ t, φ i a) s
  · have hEach : ∀ i ∈ t, IntegrableOn (φ i) s := by
      intro i hi
      refine MeasureTheory.Integrable.mono' h (hsm i hi) ?_
      exact MeasureTheory.ae_restrict_of_forall_mem hs (fun a ha => by
        rw [Real.norm_of_nonneg (hnn i hi a ha)]
        exact Finset.single_le_sum (fun j hj => hnn j hj a ha) hi)
    rw [MeasureTheory.integral_finsetSum t hEach]
  · rw [MeasureTheory.integral_undef h]
    exact Finset.sum_nonneg fun i hi => MeasureTheory.setIntegral_nonneg hs (hnn i hi)

/-- The two-term case of `setIntegral_finset_sum_le`. -/
theorem setIntegral_add_le (s : Set ℝ) (hs : MeasurableSet s) {f g : ℝ → ℝ}
    (hf : ∀ a ∈ s, 0 ≤ f a) (hg : ∀ a ∈ s, 0 ≤ g a)
    (hfm : AEStronglyMeasurable f (MeasureTheory.volume.restrict s))
    (hgm : AEStronglyMeasurable g (MeasureTheory.volume.restrict s)) :
    (∫ a in s, (f a + g a)) ≤ (∫ a in s, f a) + ∫ a in s, g a := by
  by_cases h : IntegrableOn (fun a => f a + g a) s
  · have hfint : IntegrableOn f s :=
      MeasureTheory.Integrable.mono' h hfm
        (MeasureTheory.ae_restrict_of_forall_mem hs (fun a ha => by
          rw [Real.norm_of_nonneg (hf a ha)]; exact le_add_of_nonneg_right (hg a ha)))
    have hgint : IntegrableOn g s :=
      MeasureTheory.Integrable.mono' h hgm
        (MeasureTheory.ae_restrict_of_forall_mem hs (fun a ha => by
          rw [Real.norm_of_nonneg (hg a ha)]; exact le_add_of_nonneg_left (hf a ha)))
    rw [MeasureTheory.integral_add hfint hgint]
  · rw [MeasureTheory.integral_undef h]
    exact add_nonneg (MeasureTheory.setIntegral_nonneg hs hf)
      (MeasureTheory.setIntegral_nonneg hs hg)

/-! ## A.e. strong measurability of the pieces -/

theorem lhsZ_slice_aesm {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ : ℝ => lhsZ V r z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hzero : (fun θ : ℝ => lhsZ V r z θ) = fun _ => (0 : ℝ) := by
      funext θ; rw [← hz0]; exact lhsZ_zero_z V r θ
    rw [hzero]; exact aestronglyMeasurable_const
  · have hX : ContinuousOn (fun θ : ℝ =>
        Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ)
        (Set.Ioo 0 (Real.pi / 2)) :=
      (((hV.DzIter r).pth).Dz).curry_θ hzpos |>.continuousOn
    have hT : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ)
        (Set.Ioo 0 (Real.pi / 2)) := by
      have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
        intro θ hθ
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))
      have h := hsin.rpow_const (p := -(Work.Spaces.eta))
        (fun θ hθ => Or.inl (hne θ hθ))
      simpa only [Work.FTS.EllipticEst.thEta] using h
    have hcont : ContinuousOn (fun θ : ℝ => lhsZ V r z θ) (Set.Ioo 0 (Real.pi / 2)) := by
      have h1 : ContinuousOn (fun θ : ℝ =>
          (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2)
          (Set.Ioo 0 (Real.pi / 2)) := hX.pow 2
      have h2 := (h1.mul hT).const_mul ((Work.Spaces.w z) ^ 2)
      simpa only [lhsZ, Pi.mul_apply] using h2
    have h1 : AEStronglyMeasurable (fun θ : ℝ => lhsZ V r z θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      ContinuousOn.aestronglyMeasurable (μ := MeasureTheory.volume) hcont measurableSet_Ioo
    have heq : MeasureTheory.volume.restrict Work.Spaces.Iθ
        = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
      rw [Work.Spaces.Iθ]
      exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
    rwa [heq]

theorem lhsM_slice_aesm {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (α : ℝ)
    (k : ℕ) (i j : ℕ) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable (fun θ : ℝ => lhsM α k V i j z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  by_cases hc : 1 ≤ i ∧ i + j ≤ k
  · rw [show (fun θ : ℝ => lhsM α k V i j z θ) = fun θ : ℝ =>
        (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) from by
      funext θ; rw [lhsM, if_pos hc]]
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · have hzero : (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ)) = fun _ => (0 : ℝ) := by
        funext θ; rw [← hz0]; simp [Work.Spaces.w]
      rw [hzero]; exact aestronglyMeasurable_const
    · have hX : ContinuousOn (fun θ : ℝ =>
          Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ)
          (Set.Ioo 0 (Real.pi / 2)) :=
        ((hV.pth).mixed (j + 1) i).curry_θ hzpos |>.continuousOn
      have hT : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.thGam α θ)
          (Set.Ioo 0 (Real.pi / 2)) := by
        have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
          (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
        have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
          intro θ hθ
          exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
            (by linarith [hθ.2, Real.pi_pos]))
        have h := hsin.rpow_const (p := -(Work.Spaces.gam α))
          (fun θ hθ => Or.inl (hne θ hθ))
        simpa only [Work.FTS.EllipticEst.thGam] using h
      have hcont : ContinuousOn (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ)) (Set.Ioo 0 (Real.pi / 2)) :=
        (((hX.pow 2).mul hT)).const_mul ((Work.Spaces.w z) ^ 2)
      have h1 : AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ))
          (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
        ContinuousOn.aestronglyMeasurable (μ := MeasureTheory.volume) hcont measurableSet_Ioo
      have heq : MeasureTheory.volume.restrict Work.Spaces.Iθ
          = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
        rw [Work.Spaces.Iθ]
        exact (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
      rwa [heq]
  · rw [show (fun θ : ℝ => lhsM α k V i j z θ) = fun _ => (0 : ℝ) from by
      funext θ; rw [lhsM, if_neg hc]]
    exact aestronglyMeasurable_const

/-- `z ↦ mixIntS (D_z^r V) z` is a.e. strongly measurable. -/
theorem mixIntS_aesm {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (r : ℕ) :
    AEStronglyMeasurable (fun z : ℝ => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.thEta p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hX : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (((hV.DzIter r).pth).Dz).continuousOn
    have hT : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
      have hne : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
          Real.sin (2 * p.2) ≠ 0 := by
        intro p hp
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
          (by linarith [hp.2.2, Real.pi_pos]))
      have h := hsin.rpow_const (p := -(Work.Spaces.eta))
        (fun p hp => Or.inl (hne p hp))
      simpa only [Work.FTS.EllipticEst.thEta] using h
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hX.pow 2
    exact h1.mul hT
  have haesm := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hint : AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    haesm.integral_prod_right'
  have hprod : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter r V)) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((measurable_w.pow_const 2).aestronglyMeasurable).mul hint
  simpa only [Work.EllipticEst.Core.mixIntS] using hprod

/-- `z ↦ mixedIntS α i j V z` is a.e. strongly measurable. -/
theorem mixedIntS_aesm {V : ℝ → ℝ → ℝ} (hV : Work.FTS.EllipticEst.SmoothOpen V) (α : ℝ)
    (i j : ℕ) :
    AEStronglyMeasurable (fun z : ℝ => Work.EllipticEst.Core.mixedIntS α i j V z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) p.1 p.2) ^ 2
        * Work.FTS.EllipticEst.thGam α p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hX : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := ((hV.pth).mixed (j + 1) i).continuousOn
    have hT : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thGam α p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
      have hne : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
          Real.sin (2 * p.2) ≠ 0 := by
        intro p hp
        exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
          (by linarith [hp.2.2, Real.pi_pos]))
      have h := hsin.rpow_const (p := -(Work.Spaces.gam α))
        (fun p hp => Or.inl (hne p hp))
      simpa only [Work.FTS.EllipticEst.thGam] using h
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hX.pow 2
    exact h1.mul hT
  have haesm := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hint : AEStronglyMeasurable (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    haesm.integral_prod_right'
  have hprod : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    ((measurable_w.pow_const 2).aestronglyMeasurable).mul hint
  simpa only [Work.EllipticEst.Core.mixedIntS] using hprod

/-! ## The pointwise value decomposition of the `ℋ^k`-integrand -/

theorem HkIntegrand_alpha_Dz_pth {k : ℕ} {α : ℝ} {V : ℝ → ℝ → ℝ}
    (hV : Work.FTS.EllipticEst.SmoothOpen V) (hα : 0 < α) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
        = α ^ 2 * ((∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ)) := by
  intro z hz θ hθ
  by_cases hQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0
  · -- interior: the Clairaut identities apply
    have hZterm : ∀ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = α ^ 2 * lhsZ V i z θ := by
      intro i hi
      have hid : Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
          = α * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ := by
        rw [DzIter_const_mul_apply, DzIter_succ_apply_pt, OpIdentDz hV i hQ]
      rw [hid]
      have hY : (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
        Work.EllipticEst.Core.w_div_sin_sq_eq z hθ
      calc (α * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = α ^ 2 * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.DzIter i V)) z θ) ^ 2
              * ((Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2) := by ring
        _ = α ^ 2 * lhsZ V i z θ := by rw [lhsZ, hY]; ring
    have hMterm : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
          = α ^ 2 * lhsM α k V i j z θ := by
      intro i hi j hj
      have hid : Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
          = α * Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ := by
        rw [mixed_const_mul_apply, OpIdentMixed hV i j hQ]
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · have hRHS : lhsM α k V i j z θ
            = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ) := by
          rw [lhsM, if_pos hc]
        rw [if_pos hc, hid, hRHS]
        have hY : (Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ :=
          Work.EllipticEst.Core.Wt_sq_eq hα z hθ
        calc (α * Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            = α ^ 2 * (Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                * (Work.Spaces.Wt α z θ) ^ 2 := by ring
          _ = α ^ 2 * ((Work.Spaces.w z) ^ 2
                * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                  * Work.FTS.EllipticEst.thGam α θ)) := by rw [hY]; ring
      · have hLHS : (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by rw [if_neg hc]
        have hRHS : lhsM α k V i j z θ = 0 := by rw [lhsM, if_neg hc]
        rw [hLHS, hRHS, mul_zero]
    rw [Work.Spaces.HkIntegrand]
    have hZ : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = α ^ 2 * ∑ i ∈ Finset.range (k + 1), lhsZ V i z θ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i hi => hZterm i hi)
    have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        = α ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            lhsM α k V i j z θ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j hj => hMterm i hi j hj)
    rw [hZ, hM]
    ring
  · -- boundary: both sides vanish
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · rw [← hz0]
      rw [Work.Blocks.HkIntegrand_zero_z]
      rw [show (∑ r ∈ Finset.range (k + 1), lhsZ V r 0 θ) = 0 from
        Finset.sum_eq_zero (fun r _ => lhsZ_zero_z V r θ)]
      rw [show (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          lhsM α k V i j 0 θ) = 0 from
        Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => lhsM_zero_z α k V i j θ))]
      ring
    · -- `z > 0` and `¬ Q0` force `θ = 0` or `θ = π/2`
      have hθb : θ = 0 ∨ θ = Real.pi / 2 := by
        rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
        rcases eq_or_lt_of_le hθ.1 with h0 | h0
        · exact Or.inl h0.symm
        · rcases eq_or_lt_of_le hθ.2 with h2 | h2
          · exact Or.inr h2
          · exact absurd ⟨hzpos, h0, h2⟩ hQ
      have hH : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
        rcases hθb with h0 | hpi
        · rw [h0, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
            Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num), div_zero]
        · rw [hpi, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi,
            Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num), div_zero]
      have hW : Work.Spaces.Wt α z θ = 0 := by
        rw [Work.Spaces.Wt, Work.Spaces.wTheta]
        rcases hθb with h0 | hpi
        · rw [h0, show (2 : ℝ) * 0 = 0 from by ring, Real.sin_zero,
            Real.zero_rpow (by rw [Work.Spaces.gam]; intro hc; linarith), mul_zero]
        · rw [hpi, show (2 : ℝ) * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi,
            Real.zero_rpow (by rw [Work.Spaces.gam]; intro hc; linarith), mul_zero]
      rw [HkIntegrand_eq_zero_of_weights hH hW]
      rw [show (∑ r ∈ Finset.range (k + 1), lhsZ V r z θ) = 0 from by
        refine Finset.sum_eq_zero (fun r _ => ?_)
        rcases hθb with h0 | hpi
        · exact lhsZ_of_thEta_zero V r (by rw [h0]; exact thEta_zero_left)
        · exact lhsZ_of_thEta_zero V r (by rw [hpi]; exact thEta_zero_right)]
      rw [show (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          lhsM α k V i j z θ) = 0 from by
        refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
        rcases hθb with h0 | hpi
        · exact lhsM_of_thGam_zero α k V i j (by rw [h0]; exact thGam_zero_left hα)
        · exact lhsM_of_thGam_zero α k V i j (by rw [hpi]; exact thGam_zero_right hα)]
      ring

/-! ## The main statement -/

theorem LHSDecomp (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α →
      Work.FTS.EllipticEst.SmoothOpen V →
      MeasureTheory.IntegrableOn (fun z : ℝ =>
          α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                Work.EllipticEst.Core.mixedIntS α i j V z
              else 0)) Work.Spaces.Iz →
      Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        ≤ C * (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
                else 0)) := by
  refine ⟨1, one_pos, ?_⟩
  intro α V hα hV hint
  -- the two families of `z`-integrands
  set A : ℝ → ℝ := fun z => ∑ r ∈ Finset.range (k + 1),
      Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z with hA
  set B : ℝ → ℝ := fun z => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0) with hB
  set T : ℝ → ℝ := fun z => α ^ 2 * (A z + B z) with hT
  -- the hypothesis, in the form of the statement's integrand
  have hintT : MeasureTheory.IntegrableOn T Work.Spaces.Iz := by
    rw [hT, hA, hB]
    simpa only [mul_add] using hint
  have hTnonneg : ∀ z : ℝ, 0 ≤ T z := by
    intro z
    rw [hT]
    refine mul_nonneg (sq_nonneg α) (add_nonneg ?_ ?_)
    · rw [hA]; exact Finset.sum_nonneg fun r _ => mixIntS_nonneg _ _
    · rw [hB]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
        by_cases hc : 1 ≤ i ∧ i + j ≤ k
        · rw [if_pos hc]; exact mixedIntS_nonneg α i j V z
        · rw [if_neg hc]
  -- a.e. strong measurability of the two `z`-integrands
  have hAaesm : AEStronglyMeasurable A (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hA]
    exact aesm_finset_sum (fun r _ => mixIntS_aesm hV r)
  have hBaesm : AEStronglyMeasurable B (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    rw [hB]
    refine aesm_finset_sum (fun i _ => ?_)
    exact aesm_finset_sum (fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · exact aesm_ite_pos hc (mixedIntS_aesm hV α i j)
      · exact aesm_ite_neg hc)
  -- the `θ`-level bound
  have hzle : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)
        ≤ T z := by
    intro z hz
    have hrew : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)
        = α ^ 2 * (∫ θ in Work.Spaces.Iθ,
            ((∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
              + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                  lhsM α k V i j z θ)) := by
      rw [MeasureTheory.setIntegral_congr_fun (μ := MeasureTheory.volume)
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Iθ)
        (fun θ hθ => HkIntegrand_alpha_Dz_pth hV hα z hz θ hθ)]
      rw [MeasureTheory.integral_const_mul]
    rw [hrew, hT]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg α)
    have hsumZ_aesm : AEStronglyMeasurable
        (fun θ : ℝ => ∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      aesm_finset_sum (fun r _ => lhsZ_slice_aesm hV r hz)
    have hsumM_aesm : AEStronglyMeasurable
        (fun θ : ℝ => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          lhsM α k V i j z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      aesm_finset_sum (fun i _ => aesm_finset_sum (fun j _ => lhsM_slice_aesm hV α k i j hz))
    have h1 : (∫ θ in Work.Spaces.Iθ,
          ((∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ))
        ≤ (∫ θ in Work.Spaces.Iθ, ∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
          + (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
              ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ) :=
      setIntegral_add_le Work.Spaces.Iθ measurableSet_Iθ
        (fun θ hθ => Finset.sum_nonneg fun r _ => lhsZ_nonneg V r hθ)
        (fun θ hθ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          lhsM_nonneg α k V i j hθ)
        hsumZ_aesm hsumM_aesm
    have h2 : (∫ θ in Work.Spaces.Iθ, ∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
        ≤ ∑ r ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ, lhsZ V r z θ :=
      setIntegral_finset_sum_le Work.Spaces.Iθ measurableSet_Iθ (Finset.range (k + 1))
        (fun r θ => lhsZ V r z θ)
        (fun r _ θ hθ => lhsZ_nonneg V r hθ)
        (fun r _ => lhsZ_slice_aesm hV r hz)
    have h3 : (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
          ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ∫ θ in Work.Spaces.Iθ, lhsM α k V i j z θ := by
      refine le_trans (setIntegral_finset_sum_le Work.Spaces.Iθ measurableSet_Iθ
        (Finset.range (k + 1))
        (fun i θ => ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ)
        (fun i _ θ hθ => Finset.sum_nonneg fun j _ => lhsM_nonneg α k V i j hθ)
        (fun i _ => aesm_finset_sum (fun j _ => lhsM_slice_aesm hV α k i j hz))) ?_
      exact Finset.sum_le_sum (fun i _ => setIntegral_finset_sum_le Work.Spaces.Iθ
        measurableSet_Iθ (Finset.range (k + 1)) (fun j θ => lhsM α k V i j z θ)
        (fun j _ θ hθ => lhsM_nonneg α k V i j hθ)
        (fun j _ => lhsM_slice_aesm hV α k i j hz))
    have h4 : (∑ r ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ, lhsZ V r z θ) = A z := by
      rw [hA]
      exact Finset.sum_congr rfl (fun r _ => lhsZ_integral V r z)
    have h5 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          ∫ θ in Work.Spaces.Iθ, lhsM α k V i j z θ) = B z := by
      rw [hB]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
        lhsM_integral α k V i j z))
    calc (∫ θ in Work.Spaces.Iθ,
          ((∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ))
        ≤ (∫ θ in Work.Spaces.Iθ, ∑ r ∈ Finset.range (k + 1), lhsZ V r z θ)
          + (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (k + 1),
              ∑ j ∈ Finset.range (k + 1), lhsM α k V i j z θ) := h1
      _ ≤ (∑ r ∈ Finset.range (k + 1), ∫ θ in Work.Spaces.Iθ, lhsZ V r z θ)
          + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              ∫ θ in Work.Spaces.Iθ, lhsM α k V i j z θ) := add_le_add h2 h3
      _ = A z + B z := by simp only [h4, h5]
  -- the `z`-level bound
  have hzT : (∫ z in Work.Spaces.Iz, T z)
      ≤ α ^ 2 * (∑ r ∈ Finset.range (k + 1),
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
            else 0) := by
    have hTexp : (∫ z in Work.Spaces.Iz, T z) = α ^ 2 * ∫ z in Work.Spaces.Iz, (A z + B z) := by
      rw [hT]
      exact MeasureTheory.integral_const_mul _ _
    rw [hTexp]
    have h1 : (∫ z in Work.Spaces.Iz, (A z + B z))
        ≤ (∫ z in Work.Spaces.Iz, A z) + ∫ z in Work.Spaces.Iz, B z :=
      setIntegral_add_le Work.Spaces.Iz measurableSet_Iz
        (fun z _ => by rw [hA]; exact Finset.sum_nonneg fun r _ => mixIntS_nonneg _ _)
        (fun z _ => by
          rw [hB]
          exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
            by_cases hc : 1 ≤ i ∧ i + j ≤ k
            · rw [if_pos hc]; exact mixedIntS_nonneg α i j V z
            · rw [if_neg hc])
        hAaesm hBaesm
    have h2 : (∫ z in Work.Spaces.Iz, A z)
        ≤ ∑ r ∈ Finset.range (k + 1),
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z := by
      rw [hA]
      exact setIntegral_finset_sum_le Work.Spaces.Iz measurableSet_Iz (Finset.range (k + 1))
        (fun r z => Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
        (fun r _ z _ => mixIntS_nonneg _ _) (fun r _ => mixIntS_aesm hV r)
    have h3 : (∫ z in Work.Spaces.Iz, B z)
        ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            if 1 ≤ i ∧ i + j ≤ k then
              ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
            else 0 := by
      have hnnij : ∀ i j : ℕ, ∀ z ∈ Work.Spaces.Iz,
          0 ≤ (if 1 ≤ i ∧ i + j ≤ k then
            Work.EllipticEst.Core.mixedIntS α i j V z else 0) := by
        intro i j z hz
        by_cases hc : 1 ≤ i ∧ i + j ≤ k
        · rw [if_pos hc]; exact mixedIntS_nonneg α i j V z
        · rw [if_neg hc]
      have haesmij : ∀ i j : ℕ, AEStronglyMeasurable
          (fun z : ℝ => if 1 ≤ i ∧ i + j ≤ k then
            Work.EllipticEst.Core.mixedIntS α i j V z else 0)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
        intro i j
        by_cases hc : 1 ≤ i ∧ i + j ≤ k
        · exact aesm_ite_pos hc (mixedIntS_aesm hV α i j)
        · exact aesm_ite_neg hc
      rw [hB]
      calc (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0))
          ≤ ∑ i ∈ Finset.range (k + 1), ∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0) :=
            setIntegral_finset_sum_le Work.Spaces.Iz measurableSet_Iz (Finset.range (k + 1))
              (fun i z => ∑ j ∈ Finset.range (k + 1),
                (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0))
              (fun i _ z hz => Finset.sum_nonneg fun j _ => hnnij i j z hz)
              (fun i _ => aesm_finset_sum (fun j _ => haesmij i j))
        _ ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              ∫ z in Work.Spaces.Iz,
                (if 1 ≤ i ∧ i + j ≤ k then Work.EllipticEst.Core.mixedIntS α i j V z else 0) :=
            Finset.sum_le_sum (fun i _ => setIntegral_finset_sum_le Work.Spaces.Iz
              measurableSet_Iz (Finset.range (k + 1))
              (fun j z => (if 1 ≤ i ∧ i + j ≤ k then
                Work.EllipticEst.Core.mixedIntS α i j V z else 0))
              (fun j _ z hz => hnnij i j z hz) (fun j _ => haesmij i j))
        _ = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              (if 1 ≤ i ∧ i + j ≤ k then
                ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z else 0) := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            by_cases hc : 1 ≤ i ∧ i + j ≤ k
            · simp only [if_pos hc]
            · simp only [if_neg hc, MeasureTheory.integral_zero]
    calc α ^ 2 * (∫ z in Work.Spaces.Iz, (A z + B z))
        ≤ α ^ 2 * ((∫ z in Work.Spaces.Iz, A z) + ∫ z in Work.Spaces.Iz, B z) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg α)
      _ ≤ α ^ 2 * ((∑ r ∈ Finset.range (k + 1),
              ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
                else 0)) := mul_le_mul_of_nonneg_left (add_le_add h2 h3) (sq_nonneg α)
      _ = α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
                else 0) := by ring
  -- the smoothness hypothesis for `HkSq_eq_lintegral`
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have h1 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth V)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hV.pth).Dz |>.forall n
    have h3 := (contDiffOn_const (c := α)).mul h1
    have h4 : Function.uncurry (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
        = fun p : ℝ × ℝ => α * Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth V)) p := by
      funext p; rfl
    rwa [h4]
  -- the `lintegral` presentation of `HkSq`
  have hfin : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (T z)) ≠ ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintT
      (Filter.Eventually.of_forall hTnonneg)]
    exact ENNReal.ofReal_ne_top
  have hbound : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (T z) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iz
      (fun z hz => ENNReal.ofReal_le_ofReal (hzle z hz))
  calc Work.Spaces.HkSq α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ)
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => α * Work.Spaces.Dz (Work.Spaces.pth V) z θ) z θ)).toReal :=
        Work.FTS.EllipticEst.HkSq_eq_lintegral α k _ hsm
    _ ≤ (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal (T z)).toReal :=
        ENNReal.toReal_mono hfin hbound
    _ = ∫ z in Work.Spaces.Iz, T z :=
        (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Iz
            (fun z _ => hTnonneg z)) hintT.aestronglyMeasurable).symm
    _ ≤ α ^ 2 * (∑ r ∈ Finset.range (k + 1),
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
          + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
              if 1 ≤ i ∧ i + j ≤ k then
                ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
              else 0) := hzT
    _ = 1 * (α ^ 2 * (∑ r ∈ Finset.range (k + 1),
              ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixIntS (Work.Spaces.DzIter r V) z)
            + α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                if 1 ≤ i ∧ i + j ≤ k then
                  ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
                else 0)) := by ring

end

end Work.FTS.EllipticEst.RPFresh
