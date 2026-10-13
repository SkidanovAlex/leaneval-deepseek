import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.Core.weightedCS
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.FTS.EllipticEst.TT.lightInvBounds
import Submission.Work.FTS.EllipticEst.TT.lightDerivIntegrable
import Submission.Work.FTS.EllipticEst.TT.sqBoundTendstoPos
import Submission.Work.FTS.EllipticEst.TT.sliceFtcKey

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.EllTwoAsm

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **Slicewise rate at the two endpoints of `Iθ`, light weight case.**  Assembly of the endpoint
`C^{1-a}·θ^{1-a}`-rate from the four ingredients proved in `Submission/Work/FTS/EllipticEst/TT/`:
`lightInvBounds` (integrability and size of `sin(2θ)^{-a}`), `lightDerivIntegrable` (`∂_θf`
integrable, from `∫(∂_θf)²sin(2θ)^a < ∞` and AM–GM), `sliceFtcKey` (the fundamental theorem of
calculus on the open interval with the two endpoint constants) and `sqBoundTendstoPos` (a squared
bound by a positive power forces convergence).

This statement is the abstract form of the target; `SliceRateLightAsm` is the immediate
instantiation. -/
private theorem slice_rate_light_asm_aux
    (lightInvBounds : ∀ (a : ℝ), 0 < a → a < 1 → ∃ C : ℝ, 0 < C ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        MeasureTheory.IntegrableOn (fun t : ℝ => ((Real.sin (2 * t)) ^ a)⁻¹) (Set.Ioo 0 θ)) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) θ))
          (fun t : ℝ => ((Real.sin (2 * t)) ^ a)⁻¹) ≤ C * θ ^ (1 - a)) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        MeasureTheory.IntegrableOn (fun t : ℝ => ((Real.sin (2 * t)) ^ a)⁻¹)
          (Set.Ioo θ (Real.pi / 2))) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo θ (Real.pi / 2)))
          (fun t : ℝ => ((Real.sin (2 * t)) ^ a)⁻¹) ≤ C * (Real.pi / 2 - θ) ^ (1 - a)))
    (lightDerivIntegrable : ∀ (a : ℝ), 0 < a → a < 1 → ∀ (f : ℝ → ℝ),
      ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ a) (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
      (∀ a' b' : ℝ, Set.Ioo a' b' ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
        MeasureTheory.IntegrableOn (fun θ : ℝ => deriv f θ) (Set.Ioo a' b')))
    (sqBoundTendstoPos : ∀ {p : ℝ}, 0 < p →
      (∀ (f : ℝ → ℝ) (c M : ℝ), 0 ≤ M →
        (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ - c) ^ 2 ≤ M * θ ^ p) →
        Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c)) ∧
      (∀ (f : ℝ → ℝ) (c M : ℝ), 0 ≤ M →
        (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ - c) ^ 2 ≤ M * (Real.pi / 2 - θ) ^ p) →
        Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c)))
    (sliceFtcKey : ∀ (f : ℝ → ℝ), ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      (∀ a b : ℝ, Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
        MeasureTheory.IntegrableOn (fun t : ℝ => deriv f t) (Set.Ioo a b)) →
      (∃ c : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          f θ - c = MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) θ))
            (fun t : ℝ => deriv f t)) ∧
      (∃ c : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          f θ - c = -MeasureTheory.integral
            (MeasureTheory.volume.restrict (Set.Ioo θ (Real.pi / 2)))
            (fun t : ℝ => deriv f t)))
    : ∀ (a : ℝ), 0 < a → a < 1 → ∃ K : ℝ, 0 < K ∧
      ∀ (f : ℝ → ℝ), ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ a)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
        (∃ c : ℝ, Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
          ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ - c) ^ 2 ≤ K * θ ^ (1 - a) *
            ∫ θ' in Set.Ioo 0 θ, (deriv f θ') ^ 2 * (Real.sin (2 * θ')) ^ a)
        ∧ (∃ c : ℝ,
            Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
          ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ - c) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 - a) *
            ∫ θ' in Set.Ioo θ (Real.pi / 2), (deriv f θ') ^ 2 * (Real.sin (2 * θ')) ^ a) := by
  intro a ha ha1
  obtain ⟨C, hCpos, hInvL, hBndL, hInvR, hBndR⟩ := lightInvBounds a ha ha1
  have hCnn : 0 ≤ C := le_of_lt hCpos
  refine ⟨C, hCpos, ?_⟩
  intro f hf hint
  obtain ⟨_hDerivFull, hDerivSub⟩ := lightDerivIntegrable a ha ha1 f hf hint
  obtain ⟨⟨cL, hKeyL⟩, ⟨cR, hKeyR⟩⟩ := sliceFtcKey f hf hDerivSub
  -- regularity of the weight and of `deriv f`
  have hderiv_cont : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hwpos : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < (Real.sin (2 * t)) ^ a := by
    intro t ht
    exact Real.rpow_pos_of_pos
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])) a
  have hwcont : ContinuousOn (fun t : ℝ => (Real.sin (2 * t)) ^ a)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
      (fun t _ => Or.inr ha.le)
  -- the total energy is nonnegative and dominates every partial one
  have hEnn : 0 ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
      (le_of_lt (hwpos t ht)))
  have hmonoL : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a)
        ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a := by
    intro θ hθ
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (hwpos t ht))
    · filter_upwards with t ht
      exact ⟨ht.1, lt_trans ht.2 hθ.2⟩
  have hmonoR : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a)
        ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a := by
    intro θ hθ
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (hwpos t ht))
    · filter_upwards with t ht
      exact ⟨lt_trans hθ.1 ht.1, ht.2⟩
  -- ## Left endpoint
  have hleft : ∃ c : ℝ, Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ - c) ^ 2 ≤ C * θ ^ (1 - a) *
        ∫ θ' in Set.Ioo 0 θ, (deriv f θ') ^ 2 * (Real.sin (2 * θ')) ^ a := by
    have hbound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (f θ - cL) ^ 2 ≤ C * θ ^ (1 - a) *
          ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a := by
      intro θ hθ
      have hsub : Set.Ioo 0 θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        fun t ht => ⟨ht.1, lt_trans ht.2 hθ.2⟩
      have hcs := Work.EllipticEst.Core.weightedCS (s := Set.Ioo 0 θ) measurableSet_Ioo
        (w := fun t : ℝ => (Real.sin (2 * t)) ^ a) (g := fun t : ℝ => deriv f t)
        (fun t ht => hwpos t (hsub ht))
        (hwcont.mono hsub)
        (hderiv_cont.mono hsub)
        (hint.mono_set hsub)
        (hInvL θ hθ)
      have hAnn : 0 ≤ ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
          (le_of_lt (hwpos t (hsub ht))))
      rw [hKeyL θ hθ]
      calc (∫ t in Set.Ioo 0 θ, deriv f t) ^ 2
          ≤ (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a) *
              (∫ t in Set.Ioo 0 θ, ((Real.sin (2 * t)) ^ a)⁻¹) := hcs
        _ ≤ (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a) *
              (C * θ ^ (1 - a)) :=
            mul_le_mul_of_nonneg_left (hBndL θ hθ) hAnn
        _ = C * θ ^ (1 - a) *
              (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a) := by ring
    refine ⟨cL, ?_, hbound⟩
    refine (sqBoundTendstoPos (p := 1 - a) (by linarith)).1 f cL
      (C * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a)) (mul_nonneg hCnn hEnn) ?_
    intro θ hθ
    calc (f θ - cL) ^ 2
        ≤ C * θ ^ (1 - a) * (∫ t in Set.Ioo 0 θ,
            (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a) := hbound θ hθ
      _ ≤ C * θ ^ (1 - a) * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a) :=
          mul_le_mul_of_nonneg_left (hmonoL θ hθ)
            (mul_nonneg hCnn (Real.rpow_nonneg (le_of_lt hθ.1) _))
      _ = (C * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a)) * θ ^ (1 - a) := by ring
  -- ## Right endpoint
  have hright : ∃ c : ℝ,
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ - c) ^ 2 ≤ C * (Real.pi / 2 - θ) ^ (1 - a) *
        ∫ θ' in Set.Ioo θ (Real.pi / 2), (deriv f θ') ^ 2 * (Real.sin (2 * θ')) ^ a := by
    have hbound : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        (f θ - cR) ^ 2 ≤ C * (Real.pi / 2 - θ) ^ (1 - a) *
          ∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a := by
      intro θ hθ
      have hsub : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        fun t ht => ⟨lt_trans hθ.1 ht.1, ht.2⟩
      have hcs := Work.EllipticEst.Core.weightedCS (s := Set.Ioo θ (Real.pi / 2))
        measurableSet_Ioo
        (w := fun t : ℝ => (Real.sin (2 * t)) ^ a) (g := fun t : ℝ => deriv f t)
        (fun t ht => hwpos t (hsub ht))
        (hwcont.mono hsub)
        (hderiv_cont.mono hsub)
        (hint.mono_set hsub)
        (hInvR θ hθ)
      have hAnn : 0 ≤ ∫ t in Set.Ioo θ (Real.pi / 2),
          (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a :=
        MeasureTheory.setIntegral_nonneg measurableSet_Ioo (fun t ht => mul_nonneg (sq_nonneg _)
          (le_of_lt (hwpos t (hsub ht))))
      rw [hKeyR θ hθ, neg_sq]
      calc (∫ t in Set.Ioo θ (Real.pi / 2), deriv f t) ^ 2
          ≤ (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a) *
              (∫ t in Set.Ioo θ (Real.pi / 2), ((Real.sin (2 * t)) ^ a)⁻¹) := hcs
        _ ≤ (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a) *
              (C * (Real.pi / 2 - θ) ^ (1 - a)) :=
            mul_le_mul_of_nonneg_left (hBndR θ hθ) hAnn
        _ = C * (Real.pi / 2 - θ) ^ (1 - a) *
              (∫ t in Set.Ioo θ (Real.pi / 2),
                (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a) := by ring
    refine ⟨cR, ?_, hbound⟩
    refine (sqBoundTendstoPos (p := 1 - a) (by linarith)).2 f cR
      (C * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a)) (mul_nonneg hCnn hEnn) ?_
    intro θ hθ
    calc (f θ - cR) ^ 2
        ≤ C * (Real.pi / 2 - θ) ^ (1 - a) * (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a) := hbound θ hθ
      _ ≤ C * (Real.pi / 2 - θ) ^ (1 - a) * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a) :=
          mul_le_mul_of_nonneg_left (hmonoR θ hθ)
            (mul_nonneg hCnn (Real.rpow_nonneg (by linarith [hθ.2, Real.pi_pos]) _))
      _ = (C * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * (Real.sin (2 * t)) ^ a)) *
            (Real.pi / 2 - θ) ^ (1 - a) := by ring
  exact ⟨hleft, hright⟩

/-- The requested statement, obtained by feeding the four proved ingredients of the `TT` slice
workstream into the abstract assembly above. -/
theorem SliceRateLightAsm : ∀ (a : ℝ), 0 < a → a < 1 → ∃ K : ℝ, 0 < K ∧
      ∀ (f : ℝ → ℝ), ContDiffOn ℝ 1 f (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
        MeasureTheory.IntegrableOn
          (fun θ : ℝ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ a)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
        (∃ c : ℝ, Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) ∧
          ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ - c) ^ 2 ≤ K * θ ^ (1 - a) *
            ∫ θ' in Set.Ioo 0 θ, (deriv f θ') ^ 2 * (Real.sin (2 * θ')) ^ a)
        ∧ (∃ c : ℝ,
            Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds c) ∧
          ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ - c) ^ 2 ≤ K * (Real.pi / 2 - θ) ^ (1 - a) *
            ∫ θ' in Set.Ioo θ (Real.pi / 2), (deriv f θ') ^ 2 * (Real.sin (2 * θ')) ^ a) :=
  slice_rate_light_asm_aux
    (fun a ha ha1 => Work.FTS.EllipticEst.TT.lightInvBounds a ha ha1)
    (fun a ha ha1 f hf hint => Work.FTS.EllipticEst.TT.lightDerivIntegrable a ha ha1 f hf hint)
    (fun {p} hp => Work.FTS.EllipticEst.TT.sqBoundTendstoPos hp)
    (fun f hf hI => Work.FTS.EllipticEst.TT.sliceFtcKey f hf hI)

end Work.FTS.EllipticEst.EllTwoAsm
