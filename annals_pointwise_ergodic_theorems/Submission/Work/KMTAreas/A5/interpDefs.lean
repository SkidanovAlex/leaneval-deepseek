/-
# Infrastructure for the interpolation step of §5

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022), §5 uses Stein's (multi)linear interpolation of `ℓᵖ` estimates to
pass from the two endpoint estimates of the minor-arc parts to the exponents of Theorem 1.17.
The abstract interpolation theorem `Work.KMTAreas.A5.stein_trilinear_top` is stated for an
arbitrary *pairing* `Λ : (α → ℂ) → (β → ℂ) → (γ → ℂ) → ℂ` (no multilinearity is needed: the
three-lines argument only uses the level-set decomposition of the analytic families).

The operators to which the interpolation is applied (the Ionescu--Wainger projections, the
halved averages `Ã_N`) are only linear on *bounded* functions, and this is recorded in the two
hypotheses `hlin₁`, `hlin₂`.  This module provides

* the pairing `trilinearT T u v w = ∫ x, T u v x * w x ∂count` attached to such an operator;
* the elementary `BoundedZ`-bookkeeping (`boundedZ_indicator`, `boundedZ_finset_sum`,
  `boundedZ_analyticFamily`) and the resulting linearity of `T` over finite sums of bounded
  functions (`T_finset_sum_left`, `T_finset_sum_right`);
* the expansion of `T` on the analytic families of simple functions (`interpExpansion`);
* the two endpoint estimates for the pairing, at the `ℓ¹`/`ℓ^∞` and at the
  `ℓ^{r₁/(r₁-1)}`/`ℓ^{r₁}` pairs (`enorm_integral_mul_le_top`, `interpEndpointTop`,
  `interpEndpointR1`).

## Main definitions

* `Work.KMTAreas.A5.trilinearT`.
-/
import Mathlib
import Submission.Work.KMTAreas.A5.Basic
import Submission.Work.Analysis.Interpolation.analyticFamily_boundary
import Submission.Work.Analysis.Interpolation.eLpNorm_eq_iSup_simpleFunc_integral
import Submission.Work.Analysis.Interpolation.riesz_thorin_linear
import Submission.Work.Analysis.Interpolation.stein_trilinear
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A5

noncomputable section

open MeasureTheory Classical
open scoped ENNReal NNReal BigOperators

/-! ## The trilinear pairing -/

/-- The trilinear pairing `Λ u v w = ∫ x, T u v x * w x ∂count` attached to a bilinear operator
`T`.  The definition is guarded by a.e.-measurability of the test function `w`, so that the
endpoint estimates hold for *all* triples of functions (for a non-a.e.-measurable `w` the value is
`0`); on the a.e.-measurable functions occurring in the three-lines argument and in the duality
step this is the genuine pairing integral. -/
def trilinearT (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)) (u v w : ℤ → ℂ) : ℂ :=
  if AEMeasurable w Measure.count then ∫ x, T u v x * w x ∂Measure.count else 0

theorem trilinearT_of_aemeasurable {T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)} {u v w : ℤ → ℂ}
    (hw : AEMeasurable w Measure.count) :
    trilinearT T u v w = ∫ x, T u v x * w x ∂Measure.count := if_pos hw

theorem trilinearT_of_not_aemeasurable {T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)} {u v w : ℤ → ℂ}
    (hw : ¬ AEMeasurable w Measure.count) : trilinearT T u v w = 0 := if_neg hw

/-! ## `BoundedZ` bookkeeping -/

/-- The indicator of any set is bounded. -/
lemma boundedZ_indicator (S : Set ℤ) : BoundedZ (S.indicator (fun _ => (1 : ℂ))) :=
  boundedZ_of_bound (C := 1) (fun x => by
    rw [Set.indicator_apply]
    split_ifs <;> simp)

/-- A finite linear combination of bounded functions is bounded. -/
lemma boundedZ_finset_sum {ι : Type*} (a : ι → ℂ) (u : ι → ℤ → ℂ) :
    ∀ (s : Finset ι), (∀ i ∈ s, BoundedZ (u i)) → BoundedZ (∑ i ∈ s, a i • u i) := by
  intro s
  induction s using Finset.induction with
  | empty => intro _; simpa using boundedZ_zero
  | insert i s hi ih =>
      intro hu
      rw [Finset.sum_insert hi]
      exact boundedZ_add (boundedZ_smul (a i) (hu i (Finset.mem_insert_self i s)))
        (ih fun j hj => hu j (Finset.mem_insert_of_mem hj))

/-- The analytic family of a simple function is bounded (it takes finitely many values, each of
finite modulus). -/
lemma boundedZ_analyticFamily (f : SimpleFunc ℤ ℂ) (t₀ t₁ z : ℂ) :
    BoundedZ (Work.Analysis.Interpolation.analyticFamily (f : ℤ → ℂ) t₀ t₁ z) := by
  rw [Work.Analysis.Interpolation.analyticFamily_eq_sum]
  exact boundedZ_finset_sum _ _ f.range (fun c _ => boundedZ_indicator _)

/-- The level-set expansion of the analytic family of a simple function is a bounded function
(the form in which the expansion is used in the proofs below). -/
lemma boundedZ_analyticFamily_sum (f : SimpleFunc ℤ ℂ) (t₀ t₁ z : ℂ) :
    BoundedZ (∑ c ∈ f.range,
      Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily t₀ t₁ z)
        • Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) := by
  simpa only [Work.Analysis.Interpolation.analyticFamily_eq_sum] using
    boundedZ_analyticFamily f t₀ t₁ z

/-! ## Linearity of `T` over finite sums of bounded functions -/

/-- The zero function is annihilated in the first slot. -/
lemma T_zero_left {T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)}
    (hlin₁ : ∀ (u u' v : ℤ → ℂ) (c : ℂ), BoundedZ u → BoundedZ u' → BoundedZ v →
      T (u + c • u') v = T u v + c • T u' v)
    {v : ℤ → ℂ} (hv : BoundedZ v) : T 0 v = 0 := by
  have h := hlin₁ 0 0 v 1 boundedZ_zero boundedZ_zero hv
  simp only [zero_add, one_smul] at h
  exact (add_left_cancel (show T 0 v + 0 = T 0 v + T 0 v from by rw [add_zero, ← h])).symm

/-- The zero function is annihilated in the second slot. -/
lemma T_zero_right {T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ)}
    (hlin₂ : ∀ (u v v' : ℤ → ℂ) (c : ℂ), BoundedZ u → BoundedZ v → BoundedZ v' →
      T u (v + c • v') = T u v + c • T u v')
    {u : ℤ → ℂ} (hu : BoundedZ u) : T u 0 = 0 := by
  have h := hlin₂ u 0 0 1 hu boundedZ_zero boundedZ_zero
  simp only [zero_add, one_smul] at h
  exact (add_left_cancel (show T u 0 + 0 = T u 0 + T u 0 from by rw [add_zero, ← h])).symm

/-- `T` is additive and homogeneous in its first slot over finite linear combinations of bounded
functions. -/
lemma T_finset_sum_left {ι : Type*} (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    (hlin₁ : ∀ (u u' v : ℤ → ℂ) (c : ℂ), BoundedZ u → BoundedZ u' → BoundedZ v →
      T (u + c • u') v = T u v + c • T u' v)
    (a : ι → ℂ) (u : ι → ℤ → ℂ) (v : ℤ → ℂ) :
    ∀ (s : Finset ι), (∀ i ∈ s, BoundedZ (u i)) → BoundedZ v →
      T (∑ i ∈ s, a i • u i) v = ∑ i ∈ s, a i • T (u i) v := by
  intro s
  induction s using Finset.induction with
  | empty =>
      intro _ hv
      simp only [Finset.sum_empty]
      exact T_zero_left hlin₁ hv
  | insert i s hi ih =>
      intro hu hv
      have hs : BoundedZ (∑ j ∈ s, a j • u j) :=
        boundedZ_finset_sum a u s (fun j hj => hu j (Finset.mem_insert_of_mem hj))
      have hi' : BoundedZ (u i) := hu i (Finset.mem_insert_self i s)
      rw [Finset.sum_insert hi,
        show a i • u i + ∑ j ∈ s, a j • u j = (∑ j ∈ s, a j • u j) + a i • u i from
          add_comm _ _,
        hlin₁ _ _ _ (a i) hs hi' hv,
        ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)) hv,
        Finset.sum_insert hi,
        add_comm]

/-- `T` is additive and homogeneous in its second slot over finite linear combinations of bounded
functions. -/
lemma T_finset_sum_right {ι : Type*} (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    (hlin₂ : ∀ (u v v' : ℤ → ℂ) (c : ℂ), BoundedZ u → BoundedZ v → BoundedZ v' →
      T u (v + c • v') = T u v + c • T u v')
    (a : ι → ℂ) (u : ℤ → ℂ) (v : ι → ℤ → ℂ) :
    ∀ (s : Finset ι), (∀ i ∈ s, BoundedZ (v i)) → BoundedZ u →
      T u (∑ i ∈ s, a i • v i) = ∑ i ∈ s, a i • T u (v i) := by
  intro s
  induction s using Finset.induction with
  | empty =>
      intro _ hu
      simp only [Finset.sum_empty]
      exact T_zero_right hlin₂ hu
  | insert i s hi ih =>
      intro hv hu
      have hs : BoundedZ (∑ j ∈ s, a j • v j) :=
        boundedZ_finset_sum a v s (fun j hj => hv j (Finset.mem_insert_of_mem hj))
      have hi' : BoundedZ (v i) := hv i (Finset.mem_insert_self i s)
      rw [Finset.sum_insert hi,
        show a i • v i + ∑ j ∈ s, a j • v j = (∑ j ∈ s, a j • v j) + a i • v i from
          add_comm _ _,
        hlin₂ _ _ _ (a i) hu hs hi',
        ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)) hu,
        Finset.sum_insert hi,
        add_comm]

/-! ## The expansion of `T` on the analytic families -/

/-- **The expansion of `T` on the analytic families of two simple functions.**  Pushing the two
level-set expansions of `analyticFamily f t₀ t₁ z` and `analyticFamily g u₀ u₁ z` through the
linearity of `T` on bounded functions expresses `T` of the two families as the finite double sum
over the level sets with the entire coefficients `phasePow c (expFamily t₀ t₁ z) *
phasePow d (expFamily u₀ u₁ z)`. -/
lemma interpExpansion (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    (hlin₁ : ∀ (u u' v : ℤ → ℂ) (c : ℂ), BoundedZ u → BoundedZ u' → BoundedZ v →
      T (u + c • u') v = T u v + c • T u' v)
    (hlin₂ : ∀ (u v v' : ℤ → ℂ) (c : ℂ), BoundedZ u → BoundedZ v → BoundedZ v' →
      T u (v + c • v') = T u v + c • T u v')
    (f g : SimpleFunc ℤ ℂ) (t₀ t₁ u₀ u₁ z : ℂ) :
    T (Work.Analysis.Interpolation.analyticFamily (f : ℤ → ℂ) t₀ t₁ z)
        (Work.Analysis.Interpolation.analyticFamily (g : ℤ → ℂ) u₀ u₁ z)
      = ∑ c ∈ f.range, ∑ d ∈ g.range,
          (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily t₀ t₁ z)
            * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily u₀ u₁ z))
            • T (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
                (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ))) := by
  rw [Work.Analysis.Interpolation.analyticFamily_eq_sum (f := f),
      Work.Analysis.Interpolation.analyticFamily_eq_sum (f := g)]
  rw [T_finset_sum_left T hlin₁
      (fun c => Work.Analysis.Interpolation.phasePow c
        (Work.Analysis.Interpolation.expFamily t₀ t₁ z))
      (fun c => Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
      (∑ d ∈ g.range, Work.Analysis.Interpolation.phasePow d
        (Work.Analysis.Interpolation.expFamily u₀ u₁ z) •
        Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
      f.range (fun c _ => boundedZ_indicator _) (boundedZ_analyticFamily_sum g u₀ u₁ z)]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [T_finset_sum_right T hlin₂
      (fun d => Work.Analysis.Interpolation.phasePow d
        (Work.Analysis.Interpolation.expFamily u₀ u₁ z))
      (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ)))
      (fun d => Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))
      g.range (fun d _ => boundedZ_indicator _) (boundedZ_indicator _)]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun d hd => smul_smul _ _ _

/-! ## The two endpoint estimates for the pairing -/

/-- Hölder's inequality in the limit form `p = 1`, `q = ⊤` for the pairing integral. -/
lemma enorm_integral_mul_le_top {a b : ℤ → ℂ} (hb : AEMeasurable b Measure.count) :
    ‖∫ x, a x * b x ∂Measure.count‖ₑ ≤ eLpNorm a 1 Measure.count * eLpNorm b ⊤ Measure.count := by
  refine (enorm_integral_le_lintegral_enorm (fun x => a x * b x)).trans ?_
  rw [← eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  simpa using (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := Measure.count) (p := 1) (q := ⊤)
    (r := 1) (f := a) (g := b) (b := fun x y => x * y) (c := 1)
    (by first | fun_prop | exact continuous_mul | exact continuous_inner | (simp only [Function.uncurry_def]; fun_prop)) (measurable_of_countable a).aestronglyMeasurable hb.aestronglyMeasurable (by filter_upwards with x; simp))

/-- **The endpoint estimate at the `ℓ¹`/`ℓ^∞` pair.** -/
lemma interpEndpointTop (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    {p₀ q₀ : ℝ} {M₀ : ℝ≥0}
    (h₀ : ∀ u v : ℤ → ℂ, eLpNorm (T u v) 1 Measure.count
      ≤ (M₀ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₀) Measure.count
          * eLpNorm v (ENNReal.ofReal q₀) Measure.count) :
    ∀ u v w : ℤ → ℂ, ‖trilinearT T u v w‖ₑ
      ≤ (M₀ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₀) Measure.count
          * eLpNorm v (ENNReal.ofReal q₀) Measure.count * eLpNorm w ⊤ Measure.count := by
  intro u v w
  rw [trilinearT]
  by_cases hw : AEMeasurable w Measure.count
  · rw [if_pos hw]
    exact (enorm_integral_mul_le_top hw).trans (mul_le_mul_of_nonneg_right (h₀ u v) zero_le)
  · rw [if_neg hw]
    simp

/-- **The endpoint estimate at the `ℓ^{r₁/(r₁-1)}`/`ℓ^{r₁}` pair.** -/
lemma interpEndpointR1 (T : (ℤ → ℂ) → (ℤ → ℂ) → (ℤ → ℂ))
    {p₁ q₁ r₁ : ℝ} (hr₁ : 1 < r₁) {M₁ : ℝ≥0}
    (h₁ : ∀ u v : ℤ → ℂ, eLpNorm (T u v) (ENNReal.ofReal (r₁ / (r₁ - 1))) Measure.count
      ≤ (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₁) Measure.count
          * eLpNorm v (ENNReal.ofReal q₁) Measure.count) :
    ∀ u v w : ℤ → ℂ, ‖trilinearT T u v w‖ₑ
      ≤ (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₁) Measure.count
          * eLpNorm v (ENNReal.ofReal q₁) Measure.count
          * eLpNorm w (ENNReal.ofReal r₁) Measure.count := by
  intro u v w
  rw [trilinearT]
  by_cases hw : AEMeasurable w Measure.count
  · rw [if_pos hw]
    have h1 : ‖∫ x, T u v x * w x ∂Measure.count‖ₑ = ‖∫ x, w x * T u v x ∂Measure.count‖ₑ := by
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [h1]
    refine (Work.Analysis.Interpolation.enorm_integral_mul_le hr₁ hw
      (measurable_of_countable (T u v)).aemeasurable).trans ?_
    calc eLpNorm w (ENNReal.ofReal r₁) Measure.count
          * eLpNorm (T u v) (ENNReal.ofReal (r₁ / (r₁ - 1))) Measure.count
        ≤ eLpNorm w (ENNReal.ofReal r₁) Measure.count
            * ((M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₁) Measure.count
                * eLpNorm v (ENNReal.ofReal q₁) Measure.count) :=
          mul_le_mul_of_nonneg_left (h₁ u v) zero_le
      _ = (M₁ : ℝ≥0∞) * eLpNorm u (ENNReal.ofReal p₁) Measure.count
            * eLpNorm v (ENNReal.ofReal q₁) Measure.count
            * eLpNorm w (ENNReal.ofReal r₁) Measure.count := by ring
  · rw [if_neg hw]
    simp

end

end Work.KMTAreas.A5
