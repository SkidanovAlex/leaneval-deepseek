import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Monotone

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval
open FractionalExpectationThresholds

attribute [local instance] Classical.propDecidable

namespace Submission
namespace FET

universe u

variable {X : Type u} [Fintype X]

/-- Increasing-family condition relative to a universe `U`. -/
def RelUpper (U : Set X) (𝓕 : Set (Set X)) : Prop :=
  ∀ ⦃A B : Set X⦄, A ∈ 𝓕 → A ⊆ U → A ⊆ B → B ⊆ U → B ∈ 𝓕

lemma RelUpper.slice0 {U : Set X} {𝓕 : Set (Set X)} (h𝓕 : RelUpper U 𝓕) (x : X) :
    RelUpper (U \ {x}) (slice0 𝓕 x) := by
  intro A B hA hAU hAB hBU
  rcases hA with ⟨hA𝓕, hxA⟩
  refine ⟨?_, ?_⟩
  · exact h𝓕 hA𝓕 (fun y hy => (hAU hy).1) hAB (fun y hy => (hBU hy).1)
  · intro hxB
    exact (hBU hxB).2 rfl

lemma RelUpper.slice1 {U : Set X} {𝓕 : Set (Set X)} (h𝓕 : RelUpper U 𝓕) (x : X) (hxU : x ∈ U) :
    RelUpper (U \ {x}) (slice1 𝓕 x) := by
  intro A B hA hAU hAB hBU
  rcases hA with ⟨hxA, hA𝓕⟩
  refine ⟨?_, ?_⟩
  · intro hxB
    exact (hBU hxB).2 rfl
  · have hIAU : insert x A ⊆ U := by
      intro y hy
      simp at hy
      rcases hy with rfl | hyA
      · exact hxU
      · exact (hAU hyA).1
    have hIAB : insert x A ⊆ insert x B := by
      intro y hy
      simp at hy
      rcases hy with rfl | hyA
      · simp
      · simp [hAB hyA]
    have hIBU : insert x B ⊆ U := by
      intro y hy
      simp at hy
      rcases hy with rfl | hyB
      · exact hxU
      · exact (hBU hyB).1
    exact h𝓕 hA𝓕 hIAU hIAB hIBU

/-- general sum formula for `muU`. -/
lemma muU_eq_sum_F {U : Set X} (p : I) (𝓕 : Set (Set X)) :
    muU U p 𝓕 = ∑ S ∈ 𝓕.toFinite.toFinset, PmassU U p S := by
  classical
  unfold muU
  have hset : 𝓕.toFinite.toFinset = (Finset.univ : Finset (Set X)).filter (fun S : Set X => S ∈ 𝓕) := by
    ext S
    by_cases hS : S ∈ 𝓕 <;> simp [hS]
  rw [hset]
  rw [Finset.sum_filter]

lemma PmassU_empty (p : I) (S : Set X) : PmassU (∅ : Set X) p S = if S = ∅ then 1 else 0 := by
  classical
  by_cases hS0 : S = (∅ : Set X)
  · subst S
    have hS : (∅ : Set X) ⊆ (∅ : Set X) := by intro x hx; exact hx
    rw [if_pos rfl]
    rw [PmassU_of_subset (U := (∅ : Set X)) (p := p) (S := (∅ : Set X)) hS]
    simp [Set.ncard_empty]
  · have hnot : ¬ S ⊆ (∅ : Set X) := by
      intro h
      exact hS0 (Subset.antisymm h (by intro x hx; exact False.elim hx))
    unfold PmassU
    rw [if_neg hnot, if_neg hS0]

/-- base case: empty universe. -/
lemma muU_empty (p : I) (𝓕 : Set (Set X)) :
    muU (∅ : Set X) p 𝓕 = if (∅ : Set X) ∈ 𝓕 then 1 else 0 := by
  classical
  rw [muU_eq_sum_F p 𝓕]
  by_cases hF : (∅ : Set X) ∈ 𝓕
  · have hsingle : (∑ S ∈ 𝓕.toFinite.toFinset, PmassU (∅ : Set X) p S) = 1 := by
      have hsum1 : ∀ b ∈ 𝓕.toFinite.toFinset, b ≠ (∅ : Set X) → PmassU (∅ : Set X) p b = 0 := by
        intro b hb hb0
        have hpb := PmassU_empty p b
        simp [hpb, hb0]
      have hsum2 : (∅ : Set X) ∉ 𝓕.toFinite.toFinset → PmassU (∅ : Set X) p (∅ : Set X) = 0 := by
        intro hb
        exact False.elim (hb ((𝓕.toFinite.mem_toFinset).2 hF))
      have h := Finset.sum_eq_single (a := (∅ : Set X)) (s := 𝓕.toFinite.toFinset)
        (f := fun S : Set X => PmassU (∅ : Set X) p S) hsum1 hsum2
      rw [h]
      rw [PmassU_empty p (∅ : Set X)]
      simp
    rw [if_pos hF]
    exact hsingle
  · have hzero : (∑ S ∈ 𝓕.toFinite.toFinset, PmassU (∅ : Set X) p S) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      have hpb := PmassU_empty p b
      have hb0 : b ≠ ∅ := by
        intro hbEmpty
        apply hF
        have : b ∈ 𝓕 := (𝓕.toFinite.mem_toFinset).mp hb
        simpa [hbEmpty] using this
      simp [hpb, hb0]
    rw [if_neg hF]
    exact hzero

/-- pointwise version of `muU_mono_set`, valid for `PmassU`-vanishing outside `V`. -/
lemma muU_le_of_subset_on (V : Set X) (p : I) {𝓕₁ 𝓕₂ : Set (Set X)}
    (h : ∀ ⦃T : Set X⦄, T ∈ 𝓕₁ → T ⊆ V → T ∈ 𝓕₂) : muU V p 𝓕₁ ≤ muU V p 𝓕₂ := by
  classical
  unfold muU
  apply Finset.sum_le_sum
  intro T hT
  by_cases hT1 : T ∈ 𝓕₁
  · by_cases hTV : T ⊆ V
    · have hT2 : T ∈ 𝓕₂ := h hT1 hTV
      simp [hT1, hT2]
    · have h0 : PmassU V p T = 0 := by
        unfold PmassU
        simp [hTV]
      simp [hT1, h0]
  · by_cases hT2 : T ∈ 𝓕₂
    · have hnonneg : 0 ≤ PmassU V p T := PmassU_nonneg V p T
      simp [hT1, hT2, hnonneg]
    · simp [hT1, hT2]

/-- Monotonicity of `muU` in `p`, for relatively-increasing families, by induction on `|U|`. -/
theorem muU_mono_p : ∀ (U : Set X) (𝓕 : Set (Set X)), RelUpper U 𝓕 →
    ∀ p q : I, (p : ℝ) ≤ (q : ℝ) → muU U p 𝓕 ≤ muU U q 𝓕 := by
  classical
  let P : ℕ → Prop := fun n => ∀ (U : Set X), U.ncard = n → ∀ (𝓕 : Set (Set X)),
    RelUpper U 𝓕 → ∀ p q : I, (p : ℝ) ≤ (q : ℝ) → muU U p 𝓕 ≤ muU U q 𝓕
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro U hU 𝓕 h𝓕 p q hpq
        have hUempty : U = ∅ := by
          ext x
          constructor
          · intro hx
            have hp : 0 < U.ncard := (Set.ncard_pos (s := U)).2 ⟨x, hx⟩
            omega
          · intro hx
            simp at hx
        rw [hUempty]
        rw [muU_empty p 𝓕, muU_empty q 𝓕]
    | succ n ih =>
        intro U hU 𝓕 h𝓕 p q hpq
        by_cases hUempty : U = ∅
        · subst hUempty
          rw [muU_empty p 𝓕, muU_empty q 𝓕]
        · have hx : ∃ x, x ∈ U := Set.nonempty_iff_ne_empty.mpr hUempty
          rcases hx with ⟨x, hxU⟩
          rw [muU_slice U p hxU 𝓕, muU_slice U q hxU 𝓕]
          have hcard' : (U \ {x}).ncard = n := by
            have hUfin : U.Finite := by simpa using (Set.toFinite U)
            have hsd := Set.ncard_sdiff' (s := ({x} : Set X)) (t := U)
              (by intro y hy; simp at hy; simpa [hy] using hxU) hUfin
            have hcU : U.ncard = n + 1 := hU
            rw [hcU] at hsd
            simp at hsd
            omega
          let a0 := muU (U \ {x}) p (slice0 𝓕 x)
          let b0 := muU (U \ {x}) p (slice1 𝓕 x)
          let a1 := muU (U \ {x}) q (slice0 𝓕 x)
          let b1 := muU (U \ {x}) q (slice1 𝓕 x)
          have ha : a0 ≤ a1 := by
            exact ih (U \ {x}) hcard' (slice0 𝓕 x) (RelUpper.slice0 h𝓕 x) p q hpq
          have hb : b0 ≤ b1 := by
            exact ih (U \ {x}) hcard' (slice1 𝓕 x) (RelUpper.slice1 h𝓕 x hxU) p q hpq
          have h01 : a1 ≤ b1 := by
            apply muU_le_of_subset_on (U \ {x}) q
            intro T hT hTV
            rcases hT with ⟨hT𝓕, hxT⟩
            refine ⟨hxT, ?_⟩
            have hIAU : T ⊆ U := fun y hy => (hTV hy).1
            have hIAB : T ⊆ insert x T := fun y hy => by simp [hy]
            have hIBU : insert x T ⊆ U := by
              intro y hy
              simp at hy
              rcases hy with rfl | hyT
              · exact hxU
              · exact (hTV hyT).1
            exact h𝓕 hT𝓕 hIAU hIAB hIBU
          have h1 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
          have h2 : 0 ≤ a1 - a0 := sub_nonneg.mpr ha
          have h3 : 0 ≤ (p : ℝ) := p.2.1
          have h4 : 0 ≤ b1 - b0 := sub_nonneg.mpr hb
          have h5 : 0 ≤ (q : ℝ) - (p : ℝ) := sub_nonneg.mpr hpq
          have h6 : 0 ≤ b1 - a1 := sub_nonneg.mpr h01
          have hdiff : (1 - (q : ℝ)) * a1 + (q : ℝ) * b1 - ((1 - (p : ℝ)) * a0 + (p : ℝ) * b0) =
              (1 - (p : ℝ)) * (a1 - a0) + (p : ℝ) * (b1 - b0) + (q - (p : ℝ)) * (b1 - a1) := by
            ring
          have hnonneg : 0 ≤ (1 - (p : ℝ)) * (a1 - a0) + (p : ℝ) * (b1 - b0) +
              (q - (p : ℝ)) * (b1 - a1) := by
            nlinarith [mul_nonneg h1 h2, mul_nonneg h3 h4, mul_nonneg h5 h6]
          nlinarith [hdiff, hnonneg]
  intro U 𝓕 h𝓕 p q hpq
  exact hP (U.ncard) U rfl 𝓕 h𝓕 p q hpq

/-- For an upper family, `μ_p` is nondecreasing in `p`. -/
theorem mu_mono_p {𝓕 : Set (Set X)} (h𝓕 : IsUpperSet 𝓕) :
    ∀ p q : I, (p : ℝ) ≤ (q : ℝ) → mu p 𝓕 ≤ mu q 𝓕 := by
  classical
  intro p q hpq
  rw [muU_eq_mu p, muU_eq_mu q]
  apply muU_mono_p (univ : Set X) 𝓕
  · intro A B hA hAU hAB hBU
    exact h𝓕 hAB hA
  · exact hpq

end FET
end Submission
