/-
# The pointwise variational estimate for the model tuple (copy of the exact-height version)

This is a copy of `Submission/Work/KMTAreas/A7/modelTuple_variationalPointwise_exact.lean` in the
namespace `Work.KMTAreas.A7.Hi`, with the single missing input of that file (the Minkowski /
subadditivity / product-rule step) supplied by the separately proved
`Work.KMTAreas.A7Hi.VarNormIntegralFiber`.  It is used by `Work.KMTAreas.A7.ModelLargeHi`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.BtwistSet_eq_fiberSum
import Submission.Work.KMTAreas.A7.summable_fiberSet_family
import Submission.Work.KMTAreas.A7.exists_bound_BtwistSet_uniform
import Submission.Work.KMTAreas.A7.iwConv_varphiNt_bounded_measurable
import Submission.Work.KMTAreas.A7.iwConv_varphitildeNt_bounded_measurable
import Submission.Work.KMTAreas.A7Hi.VarNormIntegralFiber

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7.Hi

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-- The `f`-side family of the model tuple, with the **exact-height** multiplier `Tex`. -/
def HclTex (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) :
    ℕ → ℤ → ℂ :=
  fun n => if core ρ C₀ l₁ l₂ k₁ k₂ a n then
    Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f else 0

/-- The `g`-side family of the model tuple, with the **exact-height** multiplier `Tex`. -/
def GclTex (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (g : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n => if core ρ C₀ l₁ l₂ k₁ k₂ a n then
    Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g else 0

theorem BtwistExact_zero_left (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (v : ℤ → ℂ) :
    BtwistExact ρ P l₁ l₂ m₁ m₂ 0 v = 0 := by
  funext x
  simp only [BtwistExact]
  simp

theorem BtwistExact_zero_right (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (u : ℤ → ℂ) :
    BtwistExact ρ P l₁ l₂ m₁ m₂ u 0 = 0 := by
  funext x
  simp only [BtwistExact]
  simp

/-- **The definitional unfolding of the model tuple**: on the admissible scales it is the
`t`-integral of the twisted bilinear multiplier at the exact heights, applied to the clipped
exact-height families `HclTex`, `GclTex`. -/
theorem modelTuple_eq_intervalIntegral_Tex (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) :
    modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ =
      fun n x => ∫ t in (1/2 : ℝ)..1,
        BtwistExact ρ P l₁ l₂
          (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f n) (GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x := by
  funext n x
  by_cases h : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
      splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) ∧
      mainRegime ρ k₁ k₂ (Nat.floor (a n))
  · simp only [modelTuple, if_pos h]
    apply intervalIntegral.integral_congr
    intro t ht
    have hH : ∀ s : ℝ, HclTex ρ C₀ a l₁ l₂ k₁ k₂ s f n
        = Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ s) f := by
      intro s; simp only [HclTex, core]; exact if_pos h
    have hG : ∀ s : ℝ, GclTex ρ P C₀ a l₁ l₂ k₁ k₂ s g n
        = Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ s) g := by
      intro s; simp only [GclTex, core]; exact if_pos h
    simp only [hH, hG]
  · simp only [modelTuple, if_neg h]
    have hzero : (fun t : ℝ => BtwistExact ρ P l₁ l₂
        (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f n) (GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x)
        = fun _ : ℝ => (0 : ℂ) := by
      funext t
      rw [show HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f n = 0 from by
        simp only [HclTex, core]; exact if_neg h]
      exact congrFun (BtwistExact_zero_left ρ P l₁ l₂ _ _
        (GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g n)) x
    rw [hzero]
    simp


/-- **The pointwise variational estimate for the §6/§8 model tuple, with the exact-height
fibres.**  This is the consistent form of `Work.KMTAreas.A7.modelTuple_variationalPointwise`: the
right-hand side is built from the fibres of the same exact-height frequency sets that the model
tuple uses. -/
theorem modelTuple_variationalPointwiseHi (ρ : ℝ) (hρ : 0 < ρ) (P : Polynomial ℤ)
    (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (r : NNReal) (hr : 2 < r) (f g : ℤ → ℂ)
    (hf : ∃ Cf : ℝ, ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∃ Cg : ℝ, ∀ y : ℤ, ‖g y‖ ≤ Cg) (n : ℕ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ m x) ≤
      ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, (arithQ ρ (max l₁ l₂) : ENNReal)⁻¹ *
        ∑ n₀ ∈ Finset.range (arithQ ρ (max l₁ l₂)),
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => fiberOpSet (iwArithFreqsNew ρ l₁)
              (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
              (HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m) x) *
          PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => fiberOpPSet P (iwArithFreqsNew ρ l₂)
              (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
              (GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x) := by
  obtain ⟨Cf, hf'⟩ := hf
  obtain ⟨Cg, hg'⟩ := hg
  obtain ⟨hw₁, _, hw₁'⟩ := cw_etaCut_decay (-(2 * (uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
  obtain ⟨hw₂, _, hw₂'⟩ :=
    cw_etaCut_decay (-((P.natDegree : ℤ) * 2 * (uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
  have hdec₁ : ∃ Cd : ℝ, ∀ j : ℤ, ‖cw (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) j‖
      ≤ Cd / (1 + |(j : ℝ)|) ^ 2 :=
    ⟨hw₁, fun j => by simpa only [mStarF] using hw₁' j⟩
  have hdec₂ : ∃ Cd : ℝ, ∀ j : ℤ,
      ‖cw (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) j‖
        ≤ Cd / (1 + |(j : ℝ)|) ^ 2 :=
    ⟨hw₂, fun j => by simpa only [mStargF] using hw₂' j⟩
  have hKern : ∃ K : ℝ, ∀ j₁ j₂ : ℤ, ‖arithKernelSet P (arithQ ρ (max l₁ l₂))
      (iwArithFreqsNew ρ l₁) (iwArithFreqsNew ρ l₂) j₁ j₂‖ ≤ K :=
    ⟨_, fun j₁ j₂ => norm_arithKernelSet_le P _ _ _ j₁ j₂⟩
  have hboundF : ∀ m : ℕ, ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m y‖ ≤ C := by
    intro m
    obtain ⟨⟨hbm, hbm'⟩, _⟩ := iwConv_varphiNt_bounded_measurable (iwArithFreqsNew ρ l₁)
      (Nat.floor (a m)) k₁ f Cf hf'
    refine ⟨max hbm 0, fun t ht y => ?_⟩
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a m
    · simp only [HclTex, hc, if_true]
      exact le_trans (hbm' t ht y) (le_max_left _ _)
    · simp only [HclTex, hc, if_false, Pi.zero_apply, norm_zero]
      exact le_max_right _ _
  have hboundG : ∀ m : ℕ, ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m y‖ ≤ C := by
    intro m
    obtain ⟨⟨hbm, hbm'⟩, _⟩ := iwConv_varphitildeNt_bounded_measurable P (iwArithFreqsNew ρ l₂)
      (Nat.floor (a m)) k₂ g Cg hg'
    refine ⟨max hbm 0, fun t ht y => ?_⟩
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a m
    · simp only [GclTex, hc, if_true]
      exact le_trans (hbm' t ht y) (le_max_left _ _)
    · simp only [GclTex, hc, if_false, Pi.zero_apply, norm_zero]
      exact le_max_right _ _
  have hmeasF : ∀ m : ℕ, ∀ y : ℤ,
      Measurable (fun t : ℝ => HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m y) := by
    intro m y
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a m
    · simp only [HclTex, hc, if_true, Tex]
      exact (iwConv_varphiNt_bounded_measurable (iwArithFreqsNew ρ l₁)
        (Nat.floor (a m)) k₁ f Cf hf').2 y
    · simp only [HclTex, hc, if_false]
      exact measurable_const
  have hmeasG : ∀ m : ℕ, ∀ y : ℤ,
      Measurable (fun t : ℝ => GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m y) := by
    intro m y
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a m
    · simp only [GclTex, hc, if_true, Tex]
      exact (iwConv_varphitildeNt_bounded_measurable P (iwArithFreqsNew ρ l₂)
        (Nat.floor (a m)) k₂ g Cg hg').2 y
    · simp only [GclTex, hc, if_false]
      exact measurable_const
  have hZ : ∀ m : ℕ, Integrable (fun t : ℝ => BtwistExact ρ P l₁ l₂
      (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
      (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
      (HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m) (GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x)
      (volume.restrict (Set.Ioc (1/2 : ℝ) 1)) := by
    intro m
    obtain ⟨C, hC⟩ := exists_bound_BtwistSet_uniform ρ P l₁ l₂
      (iwArithFreqsNew ρ l₁) (iwArithFreqsNew ρ l₂)
      (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
      (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
      (fun t : ℝ => HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m)
      (fun t : ℝ => GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m)
      x hKern hdec₁ hdec₂ (hboundF m) (hboundG m)
    refine Integrable.of_bound ?_ C ?_
    · refine (Measurable.tsum (fun j₁ : ℤ => Measurable.tsum (fun j₂ : ℤ => ?_))).aestronglyMeasurable
      exact (measurable_const.mul (hmeasF m (x - j₁))).mul (hmeasG m (x - j₂))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      exact hC t (Set.Ioc_subset_Icc_self ht)
  have hdecomp : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, ∀ m : ℕ,
      BtwistExact ρ P l₁ l₂
        (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m) (GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x
        = ((arithQ ρ (max l₁ l₂) : ℂ))⁻¹ *
            ∑ n₀ ∈ Finset.range (arithQ ρ (max l₁ l₂)),
              fiberOpSet (iwArithFreqsNew ρ l₁)
                (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) (n₀ : ℤ)
                (HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m) x
              * fiberOpPSet P (iwArithFreqsNew ρ l₂)
                  (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) (n₀ : ℤ)
                  (GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x := by
    intro t ht m
    have hF : ∃ C : ℝ, ∀ y : ℤ, ‖HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m y‖ ≤ C :=
      ⟨Classical.choose (hboundF m), fun y => Classical.choose_spec (hboundF m) t
        (Set.Ioc_subset_Icc_self ht) y⟩
    have hG : ∃ C : ℝ, ∀ y : ℤ, ‖GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m y‖ ≤ C :=
      ⟨Classical.choose (hboundG m), fun y => Classical.choose_spec (hboundG m) t
        (Set.Ioc_subset_Icc_self ht) y⟩
    have hC₁ : ∃ Ca : ℝ, ∀ y : ℤ, ‖arithCharSet (iwArithFreqsNew ρ l₁) y‖ ≤ Ca :=
      ⟨_, fun y => norm_arithCharSet_le _ y⟩
    have hC₂ : ∃ Ca : ℝ, ∀ y : ℤ, ‖arithCharSet (iwArithFreqsNew ρ l₂) y‖ ≤ Ca :=
      ⟨_, fun y => norm_arithCharSet_le _ y⟩
    have h := BtwistSet_eq_fiberSum ρ P l₁ l₂ (iwArithFreqsNew ρ l₁) (iwArithFreqsNew ρ l₂)
      (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
      (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
      (HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m) (GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x
      (fun n₀ => summable_fiberSet_family _ _ _ x hdec₁ hC₁ hF n₀)
      (fun n₀ => summable_fiberSet_family _ _ _ x hdec₂ hC₂ hG (P.eval n₀))
    simpa only [BtwistSet_iwArithFreqsNew] using h
  have hmod : (fun m : ℕ => modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ m x)
      = fun m : ℕ => ∫ t in (1/2 : ℝ)..1, BtwistExact ρ P l₁ l₂
          (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
          (HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m) (GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x := by
    funext m
    exact congrFun (congrFun (modelTuple_eq_intervalIntegral_Tex ρ P C₀ a f g l₁ l₂ k₁ k₂) m) x
  rw [hmod]
  exact Work.KMTAreas.A7Hi.VarNormIntegralFiber r hr (arithQ ρ (max l₁ l₂)) (arithQ_pos ρ _)
      (fun t m => BtwistExact ρ P l₁ l₂
        (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m) (GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x)
      (fun t n₀ m => fiberOpSet (iwArithFreqsNew ρ l₁)
        (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
        (HclTex ρ C₀ a l₁ l₂ k₁ k₂ t f m) x)
      (fun t n₀ m => fiberOpPSet P (iwArithFreqsNew ρ l₂)
        (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
        (GclTex ρ P C₀ a l₁ l₂ k₁ k₂ t g m) x)
      hZ hdecomp

end

end Work.KMTAreas.A7.Hi

