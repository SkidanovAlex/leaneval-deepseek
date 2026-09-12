import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps

/-!
# Bernoulli-product measure on subsets and the threshold

Foundational facts about `μ_p(𝓕) := setBer(univ, p).real 𝓕` for a finite ground set `X`.
-/

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval
open FractionalExpectationThresholds

namespace Submission

namespace FET  -- Fractional Expectation Thresholds helpers

universe u

variable {X : Type u} [Fintype X]

/-- Point mass of `S` under the `p`-Bernoulli product measure. -/
noncomputable def Pmass (p : I) (S : Set X) : ℝ :=
  (p : ℝ) ^ S.ncard * (1 - (p : ℝ)) ^ (Fintype.card X - S.ncard)

/-- The Bernoulli-`p` product measure of a family of subsets. -/
noncomputable def mu (p : I) (𝓕 : Set (Set X)) : ℝ :=
  (setBer(univ, p)).real 𝓕

lemma Pmass_nonneg (p : I) (S : Set X) : 0 ≤ Pmass p S := by
  unfold Pmass
  exact mul_nonneg (pow_nonneg (by exact p.2.1) _) (pow_nonneg (by linarith [p.2.2]) _)

lemma Pmass_eq_singleton_real (p : I) (S : Set X) :
    Pmass p S = (setBer(univ, p)).real ({S} : Set (Set X)) := by
  unfold Pmass
  have hsub : S ⊆ (univ : Set X) := by intro x hx; simp
  have hfin : (univ : Set X).Finite := Set.toFinite _
  rw [setBernoulli_real_singleton p hsub hfin]
  congr 1
  rw [Set.ncard_sdiff' hsub hfin, Set.ncard_univ, Nat.card_eq_fintype_card]

lemma mu_eq_sum (p : I) (𝓕 : Set (Set X)) :
    mu p 𝓕 = ∑ S ∈ 𝓕.toFinite.toFinset, Pmass p S := by
  classical
  let fs : Finset (Set X) := 𝓕.toFinite.toFinset
  have hcov : 𝓕 = ⋃ S ∈ fs, ({S} : Set (Set X)) := by
    ext T
    simp [fs]
  calc
    mu p 𝓕 = (setBer(univ, p)).real (⋃ S ∈ fs, ({S} : Set (Set X))) := by
      unfold mu
      rw [hcov]
    _ = ∑ S ∈ fs, (setBer(univ, p)).real ({S} : Set (Set X)) := by
      exact measureReal_biUnion_finset
        (s := fs) (f := fun S : Set X => ({S} : Set (Set X)))
        (by
          intro a ha b hb hab
          exact (Set.disjoint_singleton_left (s := ({b} : Set (Set X)))).2 (by simpa using hab))
        (by intro b hb; exact measurableSet_singleton b)
        (by intro b hb; exact measure_ne_top _ _)
    _ = ∑ S ∈ fs, Pmass p S := by
      apply Finset.sum_congr rfl
      intro S hS
      exact (Pmass_eq_singleton_real p S).symm

lemma mu_nonneg (p : I) (𝓕 : Set (Set X)) : 0 ≤ mu p 𝓕 := by
  unfold mu
  exact measureReal_nonneg

/-- At `p = 1`, the measure is the indicator of `univ ∈ 𝓕`. -/
lemma mu_one {𝓕 : Set (Set X)} (hX : (univ : Set X) ∈ 𝓕) : mu (1 : I) 𝓕 = 1 := by
  unfold mu
  have hd : (setBer(univ, (1 : I)) : Measure (Set X)) = Measure.dirac (Set.univ : Set X) := by
    simp [setBernoulli_one]
  rw [hd]
  have : Measure.dirac (Set.univ : Set X) 𝓕 = (1 : ℝ≥0∞) := by simp [hX]
  simp [measureReal_def, this]

/-- At `p = 0` and `∅ ∉ 𝓕`, the measure is `0`. -/
lemma mu_zero {𝓕 : Set (Set X)} (h0 : (∅ : Set X) ∉ 𝓕) : mu (0 : I) 𝓕 = 0 := by
  unfold mu
  have hd : (setBer(univ, (0 : I)) : Measure (Set X)) = Measure.dirac (∅ : Set X) := by
    simp [setBernoulli_zero]
  rw [hd]
  have : Measure.dirac (∅ : Set X) 𝓕 = (0 : ℝ≥0∞) := by simp [h0]
  simp [measureReal_def, this]

/-! ## Measure with respect to a finite universe `U` -/

/-- Mass of `S` with respect to universe `U` (0 unless `S ⊆ U`).  `U : Set X`. -/
noncomputable def PmassU (U : Set X) (p : I) (S : Set X) : ℝ := by
  classical
  exact if S ⊆ U then
    (p : ℝ) ^ S.ncard * (1 - (p : ℝ)) ^ (U.ncard - S.ncard)
  else 0

/-- Bernoulli measure of a family with respect to finite universe `U`. -/
noncomputable def muU (U : Set X) (p : I) (𝓕 : Set (Set X)) : ℝ := by
  classical
  exact ∑ S : Set X, if S ∈ 𝓕 then PmassU U p S else 0

lemma PmassU_of_subset {U : Set X} {p : I} {S : Set X} (hS : S ⊆ U) :
    PmassU U p S = (p : ℝ) ^ S.ncard * (1 - (p : ℝ)) ^ (U.ncard - S.ncard) := by
  classical
  unfold PmassU
  simp [hS]

lemma PmassU_nonneg (U : Set X) (p : I) (S : Set X) : 0 ≤ PmassU U p S := by
  classical
  unfold PmassU
  by_cases hS : S ⊆ U
  · rw [if_pos hS]
    exact mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  · rw [if_neg hS]

lemma muU_mono_set {U : Set X} {p : I} {𝓕 𝓖 : Set (Set X)} (h : 𝓕 ⊆ 𝓖) :
    muU U p 𝓕 ≤ muU U p 𝓖 := by
  classical
  unfold muU
  apply Finset.sum_le_sum
  intro S hS
  by_cases hS𝓕 : S ∈ 𝓕
  · have hS𝓖 : S ∈ 𝓖 := h hS𝓕
    simp [hS𝓕, hS𝓖]
  · by_cases hS𝓖 : S ∈ 𝓖
    · simp [hS𝓕, hS𝓖]
      exact PmassU_nonneg U p S
    · simp [hS𝓕, hS𝓖]

lemma muU_eq_mu {𝓕 : Set (Set X)} (p : I) : mu p 𝓕 = muU (univ : Set X) p 𝓕 := by
  classical
  calc
    mu p 𝓕 = ∑ S ∈ 𝓕.toFinite.toFinset, Pmass p S := mu_eq_sum p 𝓕
    _ = ∑ S ∈ 𝓕.toFinite.toFinset, PmassU (univ : Set X) p S := by
      apply Finset.sum_congr rfl
      intro S hS
      have hsub : S ⊆ (univ : Set X) := by intro x hx; simp
      have hcard : (univ : Set X).ncard = Fintype.card X := by simp [Set.ncard_univ]
      simp [Pmass, PmassU, hsub, hcard]
    _ = muU (univ : Set X) p 𝓕 := by
      unfold muU
      have hset : 𝓕.toFinite.toFinset =
          (Finset.univ : Finset (Set X)).filter (fun S => S ∈ 𝓕) := by
        ext S
        by_cases hS : S ∈ 𝓕 <;> simp [hS]
      rw [hset]
      rw [Finset.sum_filter]

/-- A family of subsets with all members inside universe `U`. -/
def SupportedIn (U : Set X) (𝓕 : Set (Set X)) : Prop := ∀ ⦃S⦄, S ∈ 𝓕 → S ⊆ U

/-- Bernoulli measure is monotone in the family. -/
lemma mu_mono_family {𝓕 𝓖 : Set (Set X)} (p : I) (h : 𝓕 ⊆ 𝓖) : mu p 𝓕 ≤ mu p 𝓖 := by
  unfold mu
  exact measureReal_mono h (measure_ne_top _ _)

/-- Upward shadow of the support of `ν`. -/
noncomputable def UpShadow (ν : Set X → ℝ) : Set (Set X) :=
  {Y | ∃ E : Set X, ν E ≠ 0 ∧ E ⊆ Y}

end FET
end Submission
