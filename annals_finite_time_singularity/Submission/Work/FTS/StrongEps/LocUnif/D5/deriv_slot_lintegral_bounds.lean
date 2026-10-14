import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.lamDzDeriv
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen
import Submission.Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.EpsEngine.PerzTools.Exchange =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.PerzTools

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The exchange identity at a point of the open quadrant.** -/
lemma exch_point {T a b : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ} (hexch : ExchMixed)
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    {j i : ℕ} (hji : j + i ≤ k) {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
      = ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ := by
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hzmem : z ∈ Set.Ioo (z / 2) (z + 1) := ⟨by linarith, by linarith⟩
  have hθmem : θ ∈ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2) :=
    ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hboxQ : Set.Icc (z / 2) (z + 1) ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2)
      ⊆ Work.FTS.EllipticEst.Q0 := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Set.mem_prod.mp hq
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨by linarith [hq1.1], by linarith [hq2.1],
      by linarith [hq2.2, Real.pi_pos]⟩
  obtain ⟨C, hC0, hC⟩ := hsup
    (Set.Icc (z / 2) (z + 1) ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2))
    (isCompact_Icc.prod isCompact_Icc) hboxQ
  exact hexch haT hbT hab hC0 hsm hmeas
    (fun s hs j i hji q hq => hC s hs q hq j i hji) hboxQ hji z θ
    (Set.mem_prod.mpr ⟨hzmem, hθmem⟩)

/-- **The pointwise Cauchy–Schwarz (averaging) bound.** -/
lemma cv_bound {T a b : ℝ} {α : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ} (hexch : ExchMixed)
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) z θ
      ≤ (b - a) * ∫ s in a..b, Work.Spaces.HkIntegrand α k (H s) z θ := by
  obtain ⟨hz0, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  obtain ⟨C, hC0, hC⟩ := hsup {(z, θ)} isCompact_singleton (by simpa using hzθ)
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  refine Work.FTS.StrongEps.E5G5.HkIntegrand_intervalIntegral_le_gen hab hC0 hz0 hθ0 hθ1
    ?_ ?_ ?_
  · intro j i hji
    exact (hmeas j i hji z θ hzθ).mono_measure (Measure.restrict_mono hsub le_rfl)
  · intro j i hji s hs
    exact hC s (hsub hs) (z, θ) (by simp) j i hji
  · intro j i hji
    exact exch_point hexch haT hbT hab hsm hmeas hsup hji hzθ

/-- Joint measurability of a slot of the family in `(s,(z,θ))`. -/
lemma all_aesm_slot3 {T : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    {j i : ℕ} (hji : j + i ≤ k) :
    AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i (H p.1) p.2.1 p.2.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) := by
  classical
  set g : ℝ → ℝ → ℝ → ℝ := fun s z θ =>
    if (z, θ) ∈ Work.FTS.EllipticEst.Q0 then Work.Spaces.mixed j i (H s) z θ else 0
  have hmain : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod volume) := by
    refine Work.FTS.EpsEngine.aesm_uncurry_restricted measurableSet_Icc ?_ ?_ ?_
    · intro s hs
      refine ((hsm s hs).mixed j i).continuousOn.congr ?_
      intro q hq
      show (if (q.1, q.2) ∈ Work.FTS.EllipticEst.Q0 then
        Work.Spaces.mixed j i (H s) q.1 q.2 else 0) = Work.Spaces.mixed j i (H s) q.1 q.2
      rw [ite_eq_left (by simpa only [Prod.mk.eta] using hq)]
    · intro s hs q hq
      show (if (q.1, q.2) ∈ Work.FTS.EllipticEst.Q0 then
        Work.Spaces.mixed j i (H s) q.1 q.2 else 0) = 0
      exact ite_eq_right (fun h => hq h)
    · intro q
      by_cases hq : q ∈ Work.FTS.EllipticEst.Q0
      · have hthis : (fun s : ℝ => g s q.1 q.2)
            = fun s : ℝ => Work.Spaces.mixed j i (H s) q.1 q.2 :=
          funext fun s => by simp only [g]; rw [ite_eq_left hq]
        rw [hthis]
        exact hmeas j i hji q.1 q.2 hq
      · have hthis : (fun s : ℝ => g s q.1 q.2) = fun _ : ℝ => (0 : ℝ) :=
          funext fun s => by simp only [g]; rw [ite_eq_right hq]
        rw [hthis]
        exact aestronglyMeasurable_const
  rw [prod_restrict_Iz_Iθ_eq_Q0]
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod
        (volume.restrict Work.FTS.EllipticEst.Q0)) :=
    hmain.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  refine h1.congr ?_
  change ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod
      (volume.restrict Work.FTS.EllipticEst.Q0)),
    g p.1 p.2.1 p.2.2 = Work.Spaces.mixed j i (H p.1) p.2.1 p.2.2
  have hae : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod
      (volume.restrict Work.FTS.EllipticEst.Q0)), p.2 ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × (ℝ × ℝ) =>
      p.2 ∈ Work.FTS.EllipticEst.Q0) (Work.FTS.EllipticEst.isOpen_Q0.measurableSet.preimage
        measurable_snd)]
    exact Filter.Eventually.of_forall (fun _ => ae_restrict_mem
      Work.FTS.EllipticEst.isOpen_Q0.measurableSet)
  filter_upwards [hae] with p hp
  simp only [g]
  rw [ite_eq_left hp]

/-- Measurability of the `s`-integral of a slot, as a function of `(z,θ)`. -/
lemma aesm_intervalIntegral_slot {T a b : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    {j i : ℕ} (hji : j + i ≤ k) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => ∫ s in a..b, Work.Spaces.mixed j i (H s) q.1 q.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have h3 := all_aesm_slot3 hsm hmeas hji
  have h3' : AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i (H p.1) p.2.1 p.2.2)
      ((volume.restrict (Set.uIoc a b)).prod
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :=
    h3.mono_measure (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
  have hswap := h3'.prod_swap
  have hint := hswap.integral_prod_right'
  have hgoal : AEStronglyMeasurable
      (fun q : ℝ × ℝ => ∫ s in Set.Ioc a b, Work.Spaces.mixed j i (H s) q.1 q.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [← Set.uIoc_of_le hab]
    exact hint
  have hfe : (fun q : ℝ × ℝ => ∫ s in a..b, Work.Spaces.mixed j i (H s) q.1 q.2)
      = fun q : ℝ × ℝ => ∫ s in Set.Ioc a b, Work.Spaces.mixed j i (H s) q.1 q.2 := by
    funext q
    rw [intervalIntegral.integral_of_le hab]
  rw [hfe]
  exact hgoal

/-- The per-`z` version of `aesm_intervalIntegral_slot`. -/
lemma aesm_intervalIntegral_slot_perz {T a b : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hcar : CarathTheta)
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    {z : ℝ} (hz : 0 < z) {j i : ℕ} (hji : j + i ≤ k) :
    AEStronglyMeasurable (fun θ : ℝ => ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have h3 := perz_aesm_slot hcar hsm hmeas hz hji
  have h3' : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i (H p.1) z p.2)
      ((volume.restrict (Set.uIoc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    h3.mono_measure (Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl)
  have hswap := h3'.prod_swap
  have hint := hswap.integral_prod_right'
  have hgoal : AEStronglyMeasurable
      (fun θ : ℝ => ∫ s in Set.Ioc a b, Work.Spaces.mixed j i (H s) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
    rw [← Set.uIoc_of_le hab]
    exact hint
  have hfe : (fun θ : ℝ => ∫ s in a..b, Work.Spaces.mixed j i (H s) z θ)
      = fun θ : ℝ => ∫ s in Set.Ioc a b, Work.Spaces.mixed j i (H s) z θ := by
    funext θ
    rw [intervalIntegral.integral_of_le hab]
  rw [hfe]
  exact hgoal

/-- **Joint measurability of the `ℋ^k`-integrand of the primitive** (as a function of `(z,θ)`). -/
lemma aesm_HkIntegrand_primitive {T a b : ℝ} {α : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hexch : ExchMixed)
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C) :
    AEStronglyMeasurable
      (fun q : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  classical
  have hslot : ∀ (j i : ℕ), j + i ≤ k →
      AEStronglyMeasurable
        (fun q : ℝ × ℝ => Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    intro j i hji
    refine (aesm_intervalIntegral_slot haT hbT hab hsm hmeas hji).congr ?_
    filter_upwards [ae_mem_Q0] with q hq
    exact (exch_point hexch haT hbT hab hsm hmeas hsup hji hq).symm
  have hWt : AEStronglyMeasurable (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_Wt_Q0 α
  have hW : AEStronglyMeasurable
      (fun q : ℝ × ℝ => Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    aesm_wdivsin_Q0
  have hfun : (fun q : ℝ × ℝ =>
        Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2)
      = fun q : ℝ × ℝ =>
          (∑ i ∈ Finset.range (k + 1),
              (Work.Spaces.DzIter i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2
                * (Work.Spaces.w q.1 / (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
            + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                (if 1 ≤ i ∧ i + j ≤ k then
                  (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2
                    * Work.Spaces.Wt α q.1 q.2) ^ 2 else 0) :=
    funext fun q => rfl
  rw [hfun]
  refine AEStronglyMeasurable.add ?_ ?_
  · refine aesm_finsetSum_apply (fun i hi => ?_)
    have hik : i + 0 ≤ k := by
      have := Finset.mem_range.mp hi
      omega
    have h0 := hslot i 0 hik
    refine (h0.mul hW).pow 2 |>.congr ?_
    filter_upwards with p
    simp only [Pi.mul_apply, Pi.pow_apply, Work.Spaces.mixed_zero_right]
  · refine aesm_finsetSum_apply (fun i hi => aesm_finsetSum_apply (fun j hj => ?_))
    by_cases hij : 1 ≤ i ∧ i + j ≤ k
    · have hthis : (fun q : ℝ × ℝ =>
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2
              * Work.Spaces.Wt α q.1 q.2) ^ 2 else 0))
          = fun q : ℝ × ℝ =>
            (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2
              * Work.Spaces.Wt α q.1 q.2) ^ 2 :=
        funext fun q => ite_eq_left hij
      rw [hthis]
      refine ((hslot j i (by omega)).mul hWt).pow 2 |>.congr ?_
      filter_upwards with p
      simp only [Pi.mul_apply, Pi.pow_apply]
    · have hthis : (fun q : ℝ × ℝ =>
          (if 1 ≤ i ∧ i + j ≤ k then
            (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) q.1 q.2
              * Work.Spaces.Wt α q.1 q.2) ^ 2 else 0)) = fun q : ℝ × ℝ => (0 : ℝ) :=
        funext fun q => ite_eq_right hij
      rw [hthis]
      exact aestronglyMeasurable_const

/-- **Per-`z` measurability of the `ℋ^k`-integrand of the primitive.** -/
lemma aesm_slice_HkIntegrand_primitive {T a b : ℝ} {α : ℝ} {k : ℕ} {H : ℝ → ℝ → ℝ → ℝ}
    (hcar : CarathTheta) (hexch : ExchMixed)
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AEStronglyMeasurable
      (fun θ : ℝ => Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  classical
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · have hzero : (fun θ : ℝ =>
        Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) z θ)
        = fun _ : ℝ => (0 : ℝ) := by
      funext θ
      rw [← hz0, HkIntegrand_fst_zero]
    rw [hzero]
    exact aestronglyMeasurable_const
  · have hslot : ∀ (j i : ℕ), j + i ≤ k →
        AEStronglyMeasurable
          (fun θ : ℝ => Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ)
          (volume.restrict Work.Spaces.Iθ) := by
      intro j i hji
      refine (aesm_intervalIntegral_slot_perz hcar haT hbT hab hsm hmeas hzpos hji).congr ?_
      have hIθ : volume.restrict (Set.Ioo 0 (Real.pi / 2)) = volume.restrict Work.Spaces.Iθ :=
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
      rw [← hIθ]
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact (exch_point hexch haT hbT hab hsm hmeas hsup hji
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ⟩)).symm
    have hWt : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.Wt α z θ)
        (volume.restrict Work.Spaces.Iθ) := Wt_aesm_Iθ α z
    have hW : AEStronglyMeasurable
        (fun θ : ℝ => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        (volume.restrict Work.Spaces.Iθ) := wdivsin_aesm_Iθ z
    have hfun : (fun θ : ℝ =>
          Work.Spaces.HkIntegrand α k (fun z θ => ∫ s in a..b, H s z θ) z θ)
        = fun θ : ℝ =>
            (∑ i ∈ Finset.range (k + 1),
                (Work.Spaces.DzIter i (fun z θ => ∫ s in a..b, H s z θ) z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
              + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
                  (if 1 ≤ i ∧ i + j ≤ k then
                    (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
                      * Work.Spaces.Wt α z θ) ^ 2 else 0) :=
      funext fun θ => rfl
    rw [hfun]
    refine AEStronglyMeasurable.add ?_ ?_
    · refine aesm_finsetSum_apply (fun i hi => ?_)
      have hik : i + 0 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      have h0 := hslot i 0 hik
      refine (h0.mul hW).pow 2 |>.congr ?_
      filter_upwards with p
      simp only [Pi.mul_apply, Pi.pow_apply, Work.Spaces.mixed_zero_right]
    · refine aesm_finsetSum_apply (fun i hi => aesm_finsetSum_apply (fun j hj => ?_))
      by_cases hij : 1 ≤ i ∧ i + j ≤ k
      · have hthis : (fun θ : ℝ =>
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
            = fun θ : ℝ =>
              (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 :=
          funext fun θ => ite_eq_left hij
        rw [hthis]
        refine ((hslot j i (by omega)).mul hWt).pow 2 |>.congr ?_
        filter_upwards with p
        simp only [Pi.mul_apply, Pi.pow_apply]
      · have hthis : (fun θ : ℝ =>
            (if 1 ≤ i ∧ i + j ≤ k then
              (Work.Spaces.mixed j i (fun z θ => ∫ s in a..b, H s z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0)) = fun θ : ℝ => (0 : ℝ) :=
          funext fun θ => ite_eq_right hij
        rw [hthis]
        exact aestronglyMeasurable_const

end Work.FTS.EpsEngine.PerzTools
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.errAdjBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

/-! ## The one-variable iterate of `D_z = z ∂_z` -/

/-- The `b`-th iterate of the one-variable operator `f ↦ (z ↦ z f'(z))`, the `z`-part of `D_z`
acting on a function of `z` alone. -/
noncomputable def dz1 : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => fun z => z * deriv (dz1 n f) z

@[simp] theorem dz1_zero (f : ℝ → ℝ) : dz1 0 f = f := rfl

@[simp] theorem dz1_succ (n : ℕ) (f : ℝ → ℝ) :
    dz1 (n + 1) f = fun z => z * deriv (dz1 n f) z := rfl

/-- **`D_z^b` of a function of `z` alone is the one-variable iterate `dz1`.** -/
theorem errAdjDzIter_zOnly (b : ℕ) (f : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.DzIter b (fun z _ : ℝ => f z) z θ = dz1 b f z := by
  induction b generalizing z with
  | zero => rfl
  | succ b ih =>
    show z * deriv (fun z' => Work.Spaces.DzIter b (fun z _ : ℝ => f z) z' θ) z
      = dz1 (b + 1) f z
    rw [show (fun z' => Work.Spaces.DzIter b (fun z _ : ℝ => f z) z' θ) = dz1 b f from
      funext fun z' => ih z']
    rfl

/-- **`D_z^b` of a separated product minus `1`.**  For every `b`,

  `D_z^b ((z,θ) ↦ f z · g θ − 1) = (dz1 b f z) · g θ − [b = 0]`,

the constant `1` being invisible to the derivative for `b ≥ 1` and the angular factor `g θ`
being a constant along the `z`-differentiation. -/
theorem errAdj_sep (f g : ℝ → ℝ) (b : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter b (fun z θ : ℝ => f z * g θ - 1) z θ
      = dz1 b f z * g θ - (if b = 0 then 1 else 0) := by
  induction b generalizing z with
  | zero => simp
  | succ b ih =>
    show z * deriv (fun z' => Work.Spaces.DzIter b (fun z θ : ℝ => f z * g θ - 1) z' θ) z
      = dz1 (b + 1) f z * g θ - (if b + 1 = 0 then 1 else 0)
    rw [show (fun z' => Work.Spaces.DzIter b (fun z θ : ℝ => f z * g θ - 1) z' θ)
        = fun z' => dz1 b f z' * g θ - (if b = 0 then 1 else 0) from funext fun z' => ih z',
      deriv_sub_const, deriv_mul_const_field]
    rw [ite_eq_right (Nat.succ_ne_zero b)]
    simp only [dz1_succ]
    ring

/-! ## The indicator takes only the values `0` and `1` -/

theorem omegaInd_zero_or_one (n : ℕ) (z θ : ℝ) :
    Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ = 0
      ∨ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ = 1 := by
  unfold Work.FTS.PhiStar.Honesty.CptApp.omegaInd
  split_ifs <;> simp

/-! ## The main statement -/

theorem errAdjBound : ∃ K : ℕ → ℝ, (∀ b : ℕ, 0 ≤ K b) ∧
    ∀ (n b : ℕ), 2 ≤ n → ∀ (z θ : ℝ),
      |Work.Spaces.DzIter b (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ|
        ≤ K b * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := by
  obtain ⟨K₀, hK₀nn, hK₀⟩ := Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux
  refine ⟨fun b => max (K₀ b) 1, fun b => le_trans (hK₀nn b) (le_max_left _ _), ?_⟩
  intro n b hn z θ
  rcases Nat.eq_zero_or_pos b with hb | hb
  · -- order `0`: the value vanishes on the plateau, and is bounded by `1` on `Ω_n`
    subst hb
    simp only [Work.Spaces.DzIter_zero]
    have hsq := Work.FTS.PhiStar.Honesty.CptApp.chiR_zetaR_sub_one_sq_le hn z θ
    have habs : |Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1|
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := by
      rcases omegaInd_zero_or_one n z θ with h | h
      · rw [h] at hsq ⊢
        have hx : Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1 = 0 := by
          nlinarith [sq_nonneg (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1)]
        rw [hx, abs_zero]
      · rw [h] at hsq ⊢
        exact (sq_le_one_iff_abs_le_one _).mp hsq
    calc |Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1|
        ≤ Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := habs
      _ = 1 * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := (one_mul _).symm
      _ ≤ max (K₀ 0) 1 * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Work.FTS.PhiStar.Honesty.CptApp.omegaInd_nonneg n z θ)
  · -- positive order: the constant `1` drops out and only the radial factor is differentiated
    obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
    show |Work.Spaces.DzIter (k + 1) (fun z θ : ℝ =>
        Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ|
        ≤ max (K₀ (k + 1)) 1 * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ
    have hdecomp : Work.Spaces.DzIter (k + 1) (fun z θ : ℝ =>
        Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
        = dz1 (k + 1) (Work.FTS.PhiStar.Honesty.CptApp.chiR n) z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ := by
      rw [errAdj_sep (Work.FTS.PhiStar.Honesty.CptApp.chiR n)
        (Work.FTS.PhiStar.Honesty.CptApp.zetaR n) (k + 1) z θ,
        ite_eq_right (Nat.succ_ne_zero k), sub_zero]
    have hz1 : dz1 (k + 1) (Work.FTS.PhiStar.Honesty.CptApp.chiR n) z
        = Work.Spaces.DzIter (k + 1)
            (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z) z θ :=
      (errAdjDzIter_zOnly (k + 1) (Work.FTS.PhiStar.Honesty.CptApp.chiR n) z θ).symm
    by_cases hmem : (z, θ) ∈ Work.FTS.PhiStar.Honesty.CptApp.Omega n
    · -- on `Ω_n`: the indicator is `1`, `zetaR n` is bounded by `1`, `chiR n` by `K₀`
      rw [Work.FTS.PhiStar.Honesty.CptApp.omegaInd_eq_one_iff.mpr hmem, hdecomp, hz1, mul_one]
      calc |Work.Spaces.DzIter (k + 1)
              (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z) z θ
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ|
          = |Work.Spaces.DzIter (k + 1)
              (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z) z θ|
            * |Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ| := abs_mul _ _
        _ ≤ K₀ (k + 1) * 1 :=
            mul_le_mul (hK₀ n (k + 1) z θ)
              (Work.FTS.PhiStar.Honesty.CptApp.abs_zetaR_le_one n θ)
              (abs_nonneg _) (hK₀nn _)
        _ ≤ max (K₀ (k + 1)) 1 := by rw [mul_one]; exact le_max_left _ _
    · -- off `Ω_n`: both cut-offs are on their plateaus, and `D_z^{k+1}` of `chiR n` vanishes
      have hzero : Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ = 0 := by
        rcases omegaInd_zero_or_one n z θ with h | h
        · exact h
        · exact absurd (Work.FTS.PhiStar.Honesty.CptApp.omegaInd_eq_one_iff.mp h) hmem
      have hnot : ¬(z < 2 / (n : ℝ) ∨ (n : ℝ) < z ∨ θ < 2 / (n : ℝ)
          ∨ Real.pi / 2 - 2 / (n : ℝ) < θ) := by
        intro hc
        exact hmem (by
          rcases hc with h1 | h2 | h3 | h4
          · exact Or.inl h1
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr (Or.inl h3))
          · exact Or.inr (Or.inr (Or.inr h4)))
      push Not at hnot
      obtain ⟨hz1', hz2', hθ1', hθ2'⟩ := hnot
      have hzeta : Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ = 1 :=
        Work.FTS.PhiStar.Honesty.CptApp.zetaR_eq_one hn hθ1' hθ2'
      have hzeroval : Work.Spaces.DzIter (k + 1)
          (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z) z θ = 0 := by
        rw [errAdjDzIter_zOnly (k + 1) (Work.FTS.PhiStar.Honesty.CptApp.chiR n) z θ,
          ← errAdjDzIter_zOnly (k + 1) (Work.FTS.PhiStar.Honesty.CptApp.chiR n) z 0]
        exact estPlateauZero.1 n hn (k + 1) (by omega) z hz1' hz2'
      rw [hzero, hdecomp, hz1, hzeroval, hzeta]
      simp

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.LamEst.lamContDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.PhiStar.Honesty.CptApp.LamEst

/-! ## The iterated `D_z`-moments -/

/-- The angular moment of the `j`-th `D_z`-iterate of `F`:
`lamSlice n F j z = ∫ θ in Iθ, zetaR n θ · D_z^j F z θ · sinθcos²θ`. -/
def lamSlice (n : ℕ) (F : ℝ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ,
    Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ * Work.Spaces.DzIter j F z θ
      * Work.Elliptic.sinCos2 θ

/-- The `0`-th iterate is the moment `lam` itself. -/
theorem lamSlice_zero (n : ℕ) (F : ℝ → ℝ → ℝ) :
    lamSlice n F 0 = fun z => Work.FTS.PhiStar.Honesty.CptApp.lam n F z := rfl

/-- Since `D_z^{j+1} F = z · ∂_z(D_z^j F)`, pulling the factor `z` out of the angular integral
turns the derivative of the `j`-th slice into the `(j+1)`-st slice. -/
theorem inv_mul_integral_DzIter_succ (F : ℝ → ℝ → ℝ) (n j : ℕ) {z : ℝ} (hz : z ≠ 0) :
    z⁻¹ * lamSlice n F (j + 1) z = ∫ θ in Work.Spaces.Iθ,
      Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ * Work.Spaces.pz (Work.Spaces.DzIter j F) z θ
        * Work.Elliptic.sinCos2 θ := by
  have hpt : ∀ θ : ℝ, Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ *
        Work.Spaces.DzIter (j + 1) F z θ * Work.Elliptic.sinCos2 θ
      = z * (Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ *
        Work.Spaces.pz (Work.Spaces.DzIter j F) z θ * Work.Elliptic.sinCos2 θ) := by
    intro θ
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    ring
  rw [lamSlice, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul, inv_mul_cancel_left₀ hz]

/-! ## The `C^m`-bootstrap along the chain `(g j)' = z⁻¹ · g (j+1)` -/

/-- Bootstrap step: if `f` has derivative `f'` on the open set `U` and `f'` is `C^n` there,
then `f` is `C^{n+1}`. -/
theorem contDiffOn_succ_of_hasDerivAt {f f' : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (n : ℕ)
    (h : ∀ z ∈ U, HasDerivAt f (f' z) z) (hf' : ContDiffOn ℝ n f' U) :
    ContDiffOn ℝ (n + 1) f U := by
  rw [contDiffOn_succ_iff_deriv_of_isOpen hU]
  refine ⟨fun z hz => (h z hz).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro hn
    exact absurd hn (by norm_num)
  · exact hf'.congr (fun x hx => (h x hx).deriv)

/-- Given a sequence `g j` on an open set `U ⊆ (0,∞)` with derivative `(g j)' = z⁻¹ · g (j+1)`
for every `j`, the function `g 0` is `C^m` on `U`.

Indeed, `g (m-1)` is continuously differentiable because its derivative `z⁻¹ · g m` is
continuous (`g m` is differentiable by hypothesis), and one then inducts backwards on the
number of remaining derivatives. -/
theorem contDiffOn_of_hasDerivAt_inv_succ {g : ℕ → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hUpos : ∀ z ∈ U, 0 < z)
    (h : ∀ j : ℕ, ∀ z ∈ U, HasDerivAt (g j) (z⁻¹ * g (j + 1) z) z) (m : ℕ) :
    ContDiffOn ℝ m (g 0) U := by
  -- `key k` states that `g j` is `C^k` whenever `m - j = k`, i.e. `g (m-k)` is `C^k`.
  have key : ∀ k : ℕ, ∀ j : ℕ, m - j = k → ContDiffOn ℝ k (g j) U := by
    intro k
    induction k with
    | zero =>
      -- `m - j = 0` means `j ≥ m`; `g j` is merely differentiable, hence continuous.
      intro j _hj
      exact contDiffOn_zero.mpr (DifferentiableOn.continuousOn
        (fun z hz => (h j z hz).differentiableAt.differentiableWithinAt))
    | succ k ih =>
      -- If `m - j = k + 1`, then `m - (j+1) = k`, so `g (j+1)` is `C^k` by the induction
      -- hypothesis; `z⁻¹ · g (j+1) z` is then also `C^k`, and it is the derivative of `g j`.
      intro j hj
      have hjm : m - (j + 1) = k := by omega
      have hgj : ContDiffOn ℝ k (g (j + 1)) U := ih (j + 1) hjm
      have hinv : ContDiffOn ℝ k (fun z : ℝ => z⁻¹) U :=
        (contDiffOn_inv ℝ).mono (fun z hz => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact ne_of_gt (hUpos z hz))
      have hf' : ContDiffOn ℝ k (fun z : ℝ => z⁻¹ * g (j + 1) z) U := hinv.mul hgj
      exact contDiffOn_succ_of_hasDerivAt hU k (h j) hf'
  exact key m 0 (Nat.sub_zero m)

/-! ## The result -/

theorem lamContDiffOn {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ContDiffOn ℝ m (fun z : ℝ => Work.FTS.PhiStar.Honesty.CptApp.lam n F z) (Set.Ioi 0) := by
  have hderiv : ∀ j : ℕ, ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (lamSlice n F j) (z⁻¹ * lamSlice n F (j + 1) z) z := by
    intro j z hz
    have hz' : (0 : ℝ) < z := hz
    have h := Work.FTS.PhiStar.Honesty.CptApp.hasDerivAt_lamSlice hsm hn j hz'
    rw [inv_mul_integral_DzIter_succ F n j (ne_of_gt hz')]
    exact h
  have hmain : ContDiffOn ℝ m (lamSlice n F 0) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_of_hasDerivAt_inv_succ isOpen_Ioi (fun z hz => hz) hderiv m
  rw [lamSlice_zero] at hmain
  exact hmain

end Work.FTS.PhiStar.Honesty.CptApp.LamEst
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.mixed_rect_L2_bounds_level =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Arithmetic helpers

The seven rectangle integrals below are bounded by rewriting each integrand with
`mixed_partials_of_smoothOpen` into a quotient of mixed derivatives (by `z`, `sin 2θ`, `z²`,
`sin²2θ`), and then comparing, on the rectangle, the reciprocals of those factors with the
constants `a^{-2}`, `m^{-2}`, `a^{-4}`, `(am)^{-2}`, `m^{-4}` (`m` a positive lower bound for
`sin 2θ` on `[c,d]`).  The three lemmas below are the purely numerical steps; they are verbatim
copies of the `private` helpers of the level-`6` file
`Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds`. -/

/-- `(X / y)² ≤ (1 / p) · H` as soon as `X² ≤ H`, `0 ≤ H` and `0 < p ≤ y²`. -/
private lemma div_sq_le_one_div_mul {X H y p : ℝ} (hX : X ^ 2 ≤ H) (hH : 0 ≤ H) (hp : 0 < p)
    (hpy : p ≤ y ^ 2) : (X / y) ^ 2 ≤ (1 / p) * H := by
  have hy2 : 0 < y ^ 2 := lt_of_lt_of_le hp hpy
  have h1 : (X / y) ^ 2 = X ^ 2 / y ^ 2 := by rw [div_pow]
  rw [h1]
  calc X ^ 2 / y ^ 2 ≤ H / y ^ 2 := div_le_div_of_nonneg_right hX (le_of_lt hy2)
    _ ≤ H / p := div_le_div_of_nonneg_left hH hp hpy
    _ = (1 / p) * H := by ring

/-- `((A - B) / z²)² ≤ (4 / a⁴) · H` as soon as `A² ≤ H`, `B² ≤ H` and `0 < a ≤ z`. -/
private lemma div_sq_pow4_le {A B H z a : ℝ} (hz : a ≤ z) (ha : 0 < a)
    (hA : A ^ 2 ≤ H) (hB : B ^ 2 ≤ H) : ((A - B) / z ^ 2) ^ 2 ≤ (4 / a ^ 4) * H := by
  have hzpos : 0 < z := lt_of_lt_of_le ha hz
  have hz4 : 0 < z ^ 4 := by positivity
  have ha4 : 0 < a ^ 4 := by positivity
  have h1 : ((A - B) / z ^ 2) ^ 2 = (A - B) ^ 2 / z ^ 4 := by rw [div_pow]; ring_nf
  rw [h1]
  have hAB : (A - B) ^ 2 ≤ 4 * H := by nlinarith [sq_nonneg (A - B), hA, hB]
  have hz4' : a ^ 4 ≤ z ^ 4 := pow_le_pow_left₀ ha.le hz 4
  calc (A - B) ^ 2 / z ^ 4 ≤ (4 * H) / z ^ 4 := div_le_div_of_nonneg_right hAB (le_of_lt hz4)
    _ ≤ (4 * H) / a ^ 4 :=
        div_le_div_of_nonneg_left (by nlinarith [sq_nonneg (A - B)]) ha4 hz4'
    _ = (4 / a ^ 4) * H := by ring

/-- `((A - 2cB) / s²)² ≤ (12 / m⁴) · H` as soon as `A² ≤ H`, `B² ≤ H`, `|c| ≤ 1` and
`0 < m ≤ s`. -/
private lemma div_sq_pow4_cos_le {A B H s m c : ℝ} (hm : 0 < m) (hms : m ≤ s)
    (hc : |c| ≤ 1) (hA : A ^ 2 ≤ H) (hB : B ^ 2 ≤ H) :
    ((A - 2 * c * B) / s ^ 2) ^ 2 ≤ (12 / m ^ 4) * H := by
  have hs : 0 < s := lt_of_lt_of_le hm hms
  have hm4 : 0 < m ^ 4 := by positivity
  have h1 : ((A - 2 * c * B) / s ^ 2) ^ 2 = (A - 2 * c * B) ^ 2 / s ^ 4 := by
    rw [div_pow]; ring_nf
  rw [h1]
  have hnum : (A - 2 * c * B) ^ 2 ≤ 6 * (A ^ 2 + B ^ 2) := by
    have h2 : |A - 2 * c * B| ≤ |A| + |2 * c * B| := by
      simpa [sub_eq_add_neg] using abs_add_le A (-(2 * c * B))
    have h3 : |2 * c * B| = 2 * |c| * |B| := by rw [abs_mul, abs_mul]; ring
    have h4 : 2 * |c| * |B| ≤ 2 * |B| := by nlinarith [abs_nonneg B]
    have h5 : |A - 2 * c * B| ≤ |A| + 2 * |B| := by rw [h3] at h2; linarith
    have h6 : (A - 2 * c * B) ^ 2 = |A - 2 * c * B| ^ 2 := by rw [sq_abs]
    rw [h6]
    nlinarith [abs_nonneg A, abs_nonneg B, abs_nonneg (A - 2 * c * B),
      sq_nonneg (|A| - |B|), sq_abs A, sq_abs B]
  have hs4 : m ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ hm.le hms 4
  have hnn : 0 ≤ 6 * (A ^ 2 + B ^ 2) := by nlinarith [sq_nonneg A, sq_nonneg B]
  have hfinal : (6 * (A ^ 2 + B ^ 2)) / m ^ 4 ≤ (12 / m ^ 4) * H := by
    rw [div_le_iff₀ hm4]
    have he : (12 / m ^ 4) * H * m ^ 4 = 12 * H := by field_simp
    rw [he]
    nlinarith [hA, hB]
  calc (A - 2 * c * B) ^ 2 / s ^ 4 ≤ (6 * (A ^ 2 + B ^ 2)) / s ^ 4 :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (6 * (A ^ 2 + B ^ 2)) / m ^ 4 := div_le_div_of_nonneg_left hnn hm4 hs4
    _ ≤ (12 / m ^ 4) * H := hfinal

-- Route note: Submission/Work/FTS/StrongEps/E5G/NOTES_rect_L2_level.md.  This is the
-- level-`k` version of the already proved `Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds`
-- (which is the same statement with `6` in place of `k` and `j + i ≤ 4` in place of
-- `j + i + 2 ≤ k`).  Write the file at
-- Submission/Work/FTS/StrongEps/E5G/mixed_rect_L2_bounds_level.lean, namespace
-- Work.FTS.StrongEps.E5G, and build with
-- `lake build Submission.Work.FTS.StrongEps.E5G.mixed_rect_L2_bounds_level`.
theorem mixed_rect_L2_bounds_level {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c)
    (hd : d < Real.pi / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (α : ℝ), 0 < α → ∀ F : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen F → Work.Spaces.HkMem α k F → ∀ (j i : ℕ), j + i + 2 ≤ k →
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (Work.Spaces.mixed j i F z θ) ^ 2
          ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
          (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
          (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
          (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2
            ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
          (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2
            ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
          (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2
            ≤ C * Work.Spaces.HkSq α k F) ∧
      (∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
          (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2
            ≤ C * Work.Spaces.HkSq α k F) := by
  classical
  -- a positive lower bound for `sin 2θ` on `[c,d]`
  obtain ⟨m, hmpos, hmle⟩ := Work.FTS.StrongEps.LocUnif.sin_two_lower_bound_rect
    (c := c) (d := d) hc hd
  -- the constant: the sum of the seven individual constants
  refine ⟨1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2)) + 12 / m ^ 4,
    by positivity, ?_⟩
  have hKa : (0 : ℝ) ≤ 1 / a ^ 2 := by positivity
  have hKm : (0 : ℝ) ≤ 1 / m ^ 2 := by positivity
  have hKa4 : (0 : ℝ) ≤ 4 / a ^ 4 := by positivity
  have hKam : (0 : ℝ) ≤ 2 * (1 / (a ^ 2 * m ^ 2)) := by positivity
  have hKm4 : (0 : ℝ) ≤ 12 / m ^ 4 := by positivity
  have hKC1 : (1 : ℝ) ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC2 : 1 / a ^ 2 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC3 : 1 / m ^ 2 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC4 : 4 / a ^ 4 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  have hKC5 : 1 / (a ^ 2 * m ^ 2) ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4
      + 2 * (1 / (a ^ 2 * m ^ 2)) + 12 / m ^ 4 := by linarith
  have hKC7 : 12 / m ^ 4 ≤ 1 + 1 / a ^ 2 + 1 / m ^ 2 + 4 / a ^ 4 + 2 * (1 / (a ^ 2 * m ^ 2))
      + 12 / m ^ 4 := by linarith
  intro k α hα F hF hmem j i hji
  -- the six identities of `mixed_partials_of_smoothOpen`
  obtain ⟨hid1, hid2, hid3, hid4, hid5, hid6⟩ :=
    Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen j i hF
  -- congruence of `pz`/`pth` on the open quadrant: replace `∂_z pz (mixed j i F)` by the
  -- quotient functions for which the identities are stated
  have hEqz : Set.EqOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.mixed j i F)))
      (Function.uncurry fun z θ => Work.Spaces.mixed (j + 1) i F z θ / z)
      Work.FTS.EllipticEst.Q0 := fun p hp => hid1 p.1 p.2 hp
  have hEqθ : Set.EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.mixed j i F)))
      (Function.uncurry fun z θ => Work.Spaces.mixed j (i + 1) F z θ / Real.sin (2 * θ))
      Work.FTS.EllipticEst.Q0 := fun p hp => hid2 p.1 p.2 hp
  have hpzz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ :=
    fun z θ hp => Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqz hp
  have htzz : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pth (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z') z θ :=
    fun z θ hp => Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqz hp
  have hpθθ : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pz
            (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ :=
    fun z θ hp => Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqθ hp
  have htθθ : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ
        = Work.Spaces.pth
            (fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ')) z θ :=
    fun z θ hp => Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqθ hp
  -- the pointwise facts on the rectangle
  have hmQ : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    intro z hz θ hθ
    exact ⟨lt_of_lt_of_le ha hz.1, ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩⟩
  have hsinp : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d, 0 < Real.sin (2 * θ) := by
    intro z hz θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hc, hθ.1])
      (by linarith [hθ.2, hd, Real.pi_pos])
  have hHnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k F z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
  -- (P1) the mixed slot itself
  have p1 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.mixed j i F z θ) ^ 2 ≤ (1 : ℝ) * Work.Spaces.HkIntegrand α k F z θ := by
    intro z hz θ hθ
    have h := mixed_sq_le_HkIntegrand_level (F := F) α k hα j i (by omega)
      (lt_of_lt_of_le ha hz.1) (hsinp z hz θ hθ)
    simpa using h
  -- (P2) `∂_z`
  have p2 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2
        ≤ (1 / a ^ 2) * Work.Spaces.HkIntegrand α k F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hC := mixed_sq_le_HkIntegrand_level (F := F) α k hα (j + 1) i (by omega) hz0 (hsinp z hz θ hθ)
    have hp2 : 0 < a ^ 2 := by positivity
    have hy2 : a ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ ha.le hz.1 2
    rw [hid1 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P3) `∂_θ`
  have p3 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2
        ≤ (1 / m ^ 2) * Work.Spaces.HkIntegrand α k F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hC := mixed_sq_le_HkIntegrand_level (F := F) α k hα j (i + 1) (by omega) hz0 (hsinp z hz θ hθ)
    have hp2 : 0 < m ^ 2 := by positivity
    have hy2 : m ^ 2 ≤ Real.sin (2 * θ) ^ 2 := pow_le_pow_left₀ hmpos.le (hmle θ hθ) 2
    rw [hid2 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P4) `∂_z∂_z`
  have p4 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (4 / a ^ 4) * Work.Spaces.HkIntegrand α k F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hA := mixed_sq_le_HkIntegrand_level (F := F) α k hα (j + 2) i (by omega) hz0 (hsinp z hz θ hθ)
    have hB := mixed_sq_le_HkIntegrand_level (F := F) α k hα (j + 1) i (by omega) hz0 (hsinp z hz θ hθ)
    rw [hpzz z θ hQ, hid3 z θ hQ]
    exact div_sq_pow4_le hz.1 ha hA hB
  -- (P5) `∂_z∂_θ`
  have p5 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (1 / (a ^ 2 * m ^ 2)) * Work.Spaces.HkIntegrand α k F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hsi := hsinp z hz θ hθ
    have hC := mixed_sq_le_HkIntegrand_level (F := F) α k hα (j + 1) (i + 1) (by omega) hz0 hsi
    have hp2 : 0 < a ^ 2 * m ^ 2 := by positivity
    have hmul : a * m ≤ z * Real.sin (2 * θ) :=
      mul_le_mul hz.1 (hmle θ hθ) hmpos.le (le_of_lt hz0)
    have hy2 : a ^ 2 * m ^ 2 ≤ (z * Real.sin (2 * θ)) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ a * m) hmul 2
      nlinarith [h]
    rw [hpθθ z θ hQ, hid4 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P6) `∂_θ∂_z`
  have p6 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (1 / (a ^ 2 * m ^ 2)) * Work.Spaces.HkIntegrand α k F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hsi := hsinp z hz θ hθ
    have hC := mixed_sq_le_HkIntegrand_level (F := F) α k hα (j + 1) (i + 1) (by omega) hz0 hsi
    have hp2 : 0 < a ^ 2 * m ^ 2 := by positivity
    have hmul : a * m ≤ z * Real.sin (2 * θ) :=
      mul_le_mul hz.1 (hmle θ hθ) hmpos.le (le_of_lt hz0)
    have hy2 : a ^ 2 * m ^ 2 ≤ (z * Real.sin (2 * θ)) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ a * m) hmul 2
      nlinarith [h]
    rw [htzz z θ hQ, hid5 z θ hQ]
    exact div_sq_le_one_div_mul hC (hHnn z θ) hp2 hy2
  -- (P7) `∂_θ∂_θ`
  have p7 : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2
        ≤ (12 / m ^ 4) * Work.Spaces.HkIntegrand α k F z θ := by
    intro z hz θ hθ
    have hQ := hmQ z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hA := mixed_sq_le_HkIntegrand_level (F := F) α k hα j (i + 2) (by omega) hz0 (hsinp z hz θ hθ)
    have hB := mixed_sq_le_HkIntegrand_level (F := F) α k hα j (i + 1) (by omega) hz0 (hsinp z hz θ hθ)
    rw [htθθ z θ hQ, hid6 z θ hQ]
    rw [show Work.Spaces.mixed j (i + 2) F z θ / (Real.sin (2 * θ)) ^ 2
          - 2 * Real.cos (2 * θ) * Work.Spaces.mixed j (i + 1) F z θ / (Real.sin (2 * θ)) ^ 2
        = (Work.Spaces.mixed j (i + 2) F z θ
            - 2 * Real.cos (2 * θ) * Work.Spaces.mixed j (i + 1) F z θ)
          / (Real.sin (2 * θ)) ^ 2 from by ring]
    exact div_sq_pow4_cos_le hmpos (hmle θ hθ) (Real.abs_cos_le_one (2 * θ)) hA hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (rect_integral_le_of_pointwise_level k ha hab hc hd hmem (by norm_num) p1).trans
      (mul_le_mul_of_nonneg_right hKC1 (Work.Spaces.HkSq_nonneg α k F))
  · exact (rect_integral_le_of_pointwise_level k ha hab hc hd hmem hKa p2).trans
      (mul_le_mul_of_nonneg_right hKC2 (Work.Spaces.HkSq_nonneg α k F))
  · exact (rect_integral_le_of_pointwise_level k ha hab hc hd hmem hKm p3).trans
      (mul_le_mul_of_nonneg_right hKC3 (Work.Spaces.HkSq_nonneg α k F))
  · exact (rect_integral_le_of_pointwise_level k ha hab hc hd hmem hKa4 p4).trans
      (mul_le_mul_of_nonneg_right hKC4 (Work.Spaces.HkSq_nonneg α k F))
  · exact (rect_integral_le_of_pointwise_level k ha hab hc hd hmem (by positivity) p5).trans
      (mul_le_mul_of_nonneg_right hKC5 (Work.Spaces.HkSq_nonneg α k F))
  · exact (rect_integral_le_of_pointwise_level k ha hab hc hd hmem (by positivity) p6).trans
      (mul_le_mul_of_nonneg_right hKC5 (Work.Spaces.HkSq_nonneg α k F))
  · exact (rect_integral_le_of_pointwise_level k ha hab hc hd hmem hKm4 p7).trans
      (mul_le_mul_of_nonneg_right hKC7 (Work.Spaces.HkSq_nonneg α k F))

end

end Work.FTS.StrongEps.E5G
end
-- ===== merged: Submission.Work.FTS.StrongEps.HQoAux.cut_slot_L2_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HQoAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000


end Work.FTS.StrongEps.HQoAux
end
-- ===== merged: Submission.Work.FTS.StrongEps.LocUnif.D5.deriv_slot_lintegral_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif.D5

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## From a Bochner `L¹`-bound on the rectangle to the `lintegral` bound

The statements of the compactness extraction are phrased with `lintegral`s of
`ENNReal.ofReal` over the *product* rectangle `[a,b] × [c,d]`, while the elliptic
estimates of `Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds` are phrased with honest
Bochner integrals (iterated over the two intervals).  The two bridges are

* `ofReal (∫ f) = ∫⁻ ofReal f` for a nonnegative integrable `f`, and
* Fubini for the product rectangle (`eqc_setIntegral_rect_eq`). -/

/-- If `f²` is integrable on the rectangle and its (Bochner) integral is at most `K`, then the
`lintegral` of `ofReal (f²)` over the same rectangle is at most `ofReal K`. -/
private theorem lintegral_ofReal_sq_rect_le {a b c d K : ℝ} {f : ℝ × ℝ → ℝ}
    (hint : IntegrableOn (fun p : ℝ × ℝ => (f p) ^ 2) (Set.Icc a b ×ˢ Set.Icc c d))
    (hM : ∫ p in Set.Icc a b ×ˢ Set.Icc c d, (f p) ^ 2 ≤ K) :
    ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, ENNReal.ofReal ((f p) ^ 2) ≤ ENNReal.ofReal K := by
  have hms : MeasurableSet (Set.Icc a b ×ˢ Set.Icc c d) :=
    measurableSet_Icc.prod measurableSet_Icc
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (MeasureTheory.ae_restrict_of_forall_mem hms (fun p _ => sq_nonneg (f p)))]
  exact ENNReal.ofReal_le_ofReal hM

/-- The `lintegral`-form of a rectangle bound for a single (curried) slot: if the slot is
continuous on the closed rectangle and its iterated Bochner `L²`-integral over the rectangle is at
most `K`, then so is the `lintegral` of `ofReal` of its square. -/
private theorem slot_lintegral_le {a b c d K : ℝ} {g : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d))
    (hbd : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d, (g z θ) ^ 2 ≤ K) :
    ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d, ENNReal.ofReal ((g p.1 p.2) ^ 2) ≤ ENNReal.ofReal K := by
  have hint : IntegrableOn (fun p : ℝ × ℝ => (g p.1 p.2) ^ 2) (Set.Icc a b ×ˢ Set.Icc c d) :=
    (hcont.pow 2).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  refine lintegral_ofReal_sq_rect_le hint ?_
  rw [Work.FTS.StrongLWP.Sobolev.eqc_setIntegral_rect_eq hint]
  exact hbd

/-! ## Continuity of the four slots on a rectangle inside the open quadrant -/

/-- The four slots `∂_z G`, `∂_z² G`, `∂_θ G`, `∂_θ² G` of `G = D_z^j D_θ^i F` (for `F` smooth on
the open quadrant) are continuous on every closed rectangle contained in `Q0`, `z > 0`.  This is
because on `Q0` each of them is a quotient of a `mixed` slot by a power of `z` or `sin 2θ`
(`mixed_partials_of_smoothOpen`). -/
private theorem slot_cont {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2) (j i : ℕ) :
    (ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz (Work.Spaces.mixed j i F) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) ∧
    (ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) ∧
    (ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.mixed j i F) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) ∧
    (ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) := by
  have hR : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨hz, hθ⟩ := Set.mem_prod.mp hp
    obtain ⟨hz1, _⟩ := Set.mem_Icc.mp hz
    obtain ⟨hθ1, hθ2⟩ := Set.mem_Icc.mp hθ
    exact Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hz1, lt_of_lt_of_le hc hθ1, lt_of_le_of_lt hθ2 hd⟩
  have hne : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, p.1 ≠ 0 := by
    intro p hp
    obtain ⟨hz, _⟩ := Set.mem_prod.mp hp
    obtain ⟨hz1, _⟩ := Set.mem_Icc.mp hz
    exact ne_of_gt (lt_of_lt_of_le ha hz1)
  have hsne : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc c d, Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    obtain ⟨_, hθ⟩ := Set.mem_prod.mp hp
    obtain ⟨hθ1, hθ2⟩ := Set.mem_Icc.mp hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hc, hθ1])
      (by linarith [hθ2, hd, Real.pi_pos]))
  have hsin : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_snd)
  have hcos : Continuous (fun p : ℝ × ℝ => Real.cos (2 * p.2)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_snd)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `∂_z (D_z^j D_θ^i F) = D_z^{j+1}D_θ^i F / z`
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.mixed (j + 1) i F p.1 p.2 / p.1)
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      ((hF.mixed (j + 1) i).continuousOn.mono hR).div continuous_fst.continuousOn hne
    exact hcont.congr (fun p hp => pz_mixed_div j i hF p.1 p.2 (hR hp))
  · -- `∂_z ∂_z (D_z^j D_θ^i F) = (D_z^{j+2}D_θ^i F - D_z^{j+1}D_θ^i F) / z²`
    have heq : EqOn (fun p : ℝ × ℝ =>
        Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) p.1 p.2)
        (fun p : ℝ × ℝ =>
          (Work.Spaces.mixed (j + 2) i F p.1 p.2 - Work.Spaces.mixed (j + 1) i F p.1 p.2)
            / p.1 ^ 2) (Set.Icc a b ×ˢ Set.Icc c d) := by
      intro p hp
      change Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) p.1 p.2
        = (Work.Spaces.mixed (j + 2) i F p.1 p.2 - Work.Spaces.mixed (j + 1) i F p.1 p.2)
            / p.1 ^ 2
      have h1 : Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) p.1 p.2
          = Work.Spaces.pz (fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z')
              p.1 p.2 :=
        Work.Spaces.pz_congr_of_isOpen
          (f := Work.Spaces.pz (Work.Spaces.mixed j i F))
          (f' := fun z' θ' => Work.Spaces.mixed (j + 1) i F z' θ' / z')
          Work.FTS.EllipticEst.isOpen_Q0
          (fun q hq => pz_mixed_div j i hF q.1 q.2 hq) (hR hp)
      rw [h1]
      exact pz_mixed_div_div j i hF p.1 p.2 (hR hp)
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed (j + 2) i F p.1 p.2 - Work.Spaces.mixed (j + 1) i F p.1 p.2)
          / p.1 ^ 2) (Set.Icc a b ×ˢ Set.Icc c d) :=
      (((hF.mixed (j + 2) i).continuousOn.mono hR).sub
        ((hF.mixed (j + 1) i).continuousOn.mono hR)).div
        (continuous_fst.pow 2).continuousOn (fun p hp => pow_ne_zero 2 (hne p hp))
    exact hcont.congr heq
  · -- `∂_θ (D_z^j D_θ^i F) = D_z^j D_θ^{i+1} F / sin 2θ`
    have hcont : ContinuousOn
        (fun p : ℝ × ℝ => Work.Spaces.mixed j (i + 1) F p.1 p.2 / Real.sin (2 * p.2))
        (Set.Icc a b ×ˢ Set.Icc c d) :=
      ((hF.mixed j (i + 1)).continuousOn.mono hR).div hsin.continuousOn hsne
    exact hcont.congr (fun p hp => pth_mixed_div j i hF p.1 p.2 (hR hp))
  · -- `∂_θ ∂_θ (D_z^j D_θ^i F) = D_z^jD_θ^{i+2}F / sin²2θ - 2cos2θ·D_z^jD_θ^{i+1}F/sin²2θ`
    have heq : EqOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) p.1 p.2)
        (fun p : ℝ × ℝ =>
          Work.Spaces.mixed j (i + 2) F p.1 p.2 / (Real.sin (2 * p.2)) ^ 2
            - 2 * Real.cos (2 * p.2) * Work.Spaces.mixed j (i + 1) F p.1 p.2
                / (Real.sin (2 * p.2)) ^ 2) (Set.Icc a b ×ˢ Set.Icc c d) := by
      intro p hp
      change Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) p.1 p.2
        = Work.Spaces.mixed j (i + 2) F p.1 p.2 / (Real.sin (2 * p.2)) ^ 2
            - 2 * Real.cos (2 * p.2) * Work.Spaces.mixed j (i + 1) F p.1 p.2
                / (Real.sin (2 * p.2)) ^ 2
      rw [Work.Spaces.pth_congr_of_isOpen
        (f := Work.Spaces.pth (Work.Spaces.mixed j i F))
        (f' := fun z' θ' => Work.Spaces.mixed j (i + 1) F z' θ' / Real.sin (2 * θ'))
        Work.FTS.EllipticEst.isOpen_Q0
        (fun x hx => pth_mixed_div j i hF x.1 x.2 hx) (hR hp)]
      exact pth_mixed_angdiv j i hF p.1 p.2 (hR hp)
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.mixed j (i + 2) F p.1 p.2 / (Real.sin (2 * p.2)) ^ 2
          - 2 * Real.cos (2 * p.2) * Work.Spaces.mixed j (i + 1) F p.1 p.2
              / (Real.sin (2 * p.2)) ^ 2) (Set.Icc a b ×ˢ Set.Icc c d) := by
      refine (((hF.mixed j (i + 2)).continuousOn.mono hR).div
        (hsin.pow 2).continuousOn (fun p hp => pow_ne_zero 2 (hsne p hp))).sub ?_
      refine (((continuous_const.mul hcos).continuousOn).mul
        ((hF.mixed j (i + 1)).continuousOn.mono hR)).div
        (hsin.pow 2).continuousOn (fun p hp => pow_ne_zero 2 (hsne p hp))
    exact hcont.congr heq

/-! ## The four-slot rectangle bound -/

/-- Assembly: given the four iterated Bochner `L²`-bounds of the slots carried by
`mixed_rect_L2_bounds` (with a common constant `K`), the corresponding four `lintegral` bounds over
the product rectangle hold with the same constant. -/
private theorem four_slot_lintegral_le {a b c d K : ℝ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2)
    (j i : ℕ)
    (h1 : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
        (Work.Spaces.pz (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ K)
    (h2 : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
        (Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ K)
    (h3 : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
        (Work.Spaces.pth (Work.Spaces.mixed j i F) z θ) ^ 2 ≤ K)
    (h4 : ∫ z in Set.Icc a b, ∫ θ in Set.Icc c d,
        (Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F)) z θ) ^ 2 ≤ K) :
    (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.mixed j i F) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal K) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i F))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal K) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.mixed j i F) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal K) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i F))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal K) := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := slot_cont hF ha hc hd j i
  exact ⟨slot_lintegral_le hc1 h1, slot_lintegral_le hc2 h2, slot_lintegral_le hc3 h3,
    slot_lintegral_le hc4 h4⟩

/-- `HkSq` is bounded by `B²` as soon as the (square root) `HkNorm` is bounded by `B`. -/
private theorem HkSq_le_sq_of_HkNorm_le {α B : ℝ} {F : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkNorm α 6 F ≤ B) : Work.Spaces.HkSq α 6 F ≤ B ^ 2 := by
  have hnn : 0 ≤ Work.Spaces.HkSq α 6 F := Work.Spaces.HkSq_nonneg α 6 F
  have h2 : Work.Spaces.HkNorm α 6 F ^ 2 = Work.Spaces.HkSq α 6 F := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt hnn]
  rw [← h2]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

theorem deriv_slot_lintegral_bounds {α B : ℝ} (hα : 0 < α)
    {F : ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n, Work.FTS.EllipticEst.SmoothOpen (F n))
    (hmem : ∀ n, Work.Spaces.HkMem α 6 (F n))
    (hb : ∀ n, Work.Spaces.HkNorm α 6 (F n) ≤ B)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hd : d < π / 2)
    (j i : ℕ) (hji : j + i ≤ 4) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ n, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.mixed j i (F n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal M) ∧
      (∀ n, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i (F n)))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal M) ∧
      (∀ n, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.mixed j i (F n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal M) ∧
      (∀ n, ∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i (F n)))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal M) := by
  classical
  -- the universal rectangle constant of the elliptic estimate
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.LocUnif.mixed_rect_L2_bounds ha hab hc hd
  have hMnn : 0 ≤ C * B ^ 2 := mul_nonneg hCpos.le (sq_nonneg B)
  have step : ∀ n, (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.mixed j i (F n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal (C * B ^ 2)) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pz (Work.Spaces.pz (Work.Spaces.mixed j i (F n)))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal (C * B ^ 2)) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.mixed j i (F n)) p.1 p.2) ^ 2)
          ≤ ENNReal.ofReal (C * B ^ 2)) ∧
      (∫⁻ p in Set.Icc a b ×ˢ Set.Icc c d,
        ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.mixed j i (F n)))
          p.1 p.2) ^ 2) ≤ ENNReal.ofReal (C * B ^ 2)) := by
    intro n
    obtain ⟨_, b2, b3, b4, _, _, b7⟩ := hC α hα (F n) (hsm n) (hmem n) j i hji
    obtain ⟨k1, k2, k3, k4⟩ := four_slot_lintegral_le (hsm n) ha hc hd j i b2 b4 b3 b7
    have hmono : ENNReal.ofReal (C * Work.Spaces.HkSq α 6 (F n)) ≤ ENNReal.ofReal (C * B ^ 2) :=
      ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (HkSq_le_sq_of_HkNorm_le (hb n)) hCpos.le)
    exact ⟨k1.trans hmono, k2.trans hmono, k3.trans hmono, k4.trans hmono⟩
  exact ⟨C * B ^ 2, hMnn, fun n => (step n).1, fun n => (step n).2.1,
    fun n => (step n).2.2.1, fun n => (step n).2.2.2⟩

end Work.FTS.StrongEps.LocUnif.D5
end
end
