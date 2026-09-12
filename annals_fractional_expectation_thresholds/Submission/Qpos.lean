import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Prob
import Submission.Minimals

open ProbabilityTheory MeasureTheory unitInterval Set
open scoped ENNReal NNReal BigOperators unitInterval
open FractionalExpectationThresholds

attribute [local instance] Classical.propDecidable

namespace Submission
namespace FET

universe u
variable {X : Type u} [Fintype X]

/-! ## Auxiliary results for `q_f_pos`

Everything below is self-contained: it only uses `ChallengeDeps` definitions
(`q_f`, `l`, `IsWeaklySmall`, `IsMin`) and elementary set/finset combinatorics.
-/

/-- If `∅ ∈ 𝓕` then every minimal member of `𝓕` is `∅`, hence `l 𝓕 = 0`. -/
private lemma l_le_zero_of_mem_empty {𝓕 : Set (Set X)} (h0 : (∅ : Set X) ∈ 𝓕) : l 𝓕 ≤ 0 := by
  classical
  unfold l
  have hmin : ∀ A : 𝓕, IsMin A → (A : Set X) = ∅ := by
    intro A hA
    have hbA : (⟨∅, h0⟩ : 𝓕) ≤ A := by
      exact Subtype.mk_le_mk.mpr (by simp)
    have hAb : A ≤ (⟨∅, h0⟩ : 𝓕) := hA hbA
    have hAb0 : (⟨(A : Set X), A.property⟩ : 𝓕) ≤ (⟨∅, h0⟩ : 𝓕) := hAb
    have hsub : (A : Set X) ⊆ (∅ : Set X) := by
      simpa using (Subtype.mk_le_mk.mp hAb0)
    apply Subset.antisymm hsub
    intro x hx
    simp at hx
  have hA : ∀ A : 𝓕, (⨆ (_ : IsMin A), (A : Set X).ncard) ≤ 0 := by
    intro A
    by_cases hAmin : IsMin A
    · have hAz : (A : Set X) = ∅ := hmin A hAmin
      rw [hAz]
      simp [hAmin]
    · simp [hAmin]
  have hne : Nonempty 𝓕 := ⟨⟨∅, h0⟩⟩
  exact ciSup_le hA

/-- The map `x ↦ {x}` from `X` to its singletons is injective. -/
private lemma singletonMap_inj : Function.Injective (fun x : X => ({x} : Set X)) := by
  intro x y h
  have h' : ({x} : Set X) = ({y} : Set X) := by simpa using h
  exact (Set.singleton_eq_singleton_iff.mp h')

/-- The collection of singletons of `X` has cardinality `Fintype.card X`. -/
private lemma card_singletons :
    ((Finset.univ : Finset (Set X)).filter (fun S : Set X => ∃ x : X, S = {x})).card
      = Fintype.card X := by
  classical
  have hEq : ((Finset.univ : Finset (Set X)).filter (fun S : Set X => ∃ x : X, S = {x}))
      = (Finset.univ : Finset X).image (fun x : X => ({x} : Set X)) := by
    ext S
    constructor
    · intro hS
      rcases (Finset.mem_filter.mp hS) with ⟨hSuni, ⟨x, rfl⟩⟩
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    · intro hS
      rcases Finset.mem_image.mp hS with ⟨x, hx, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, rfl⟩⟩
  rw [hEq]
  rw [Finset.card_image_of_injective _ singletonMap_inj]
  simp

/-- Arithmetic: `2·(n+1)` as a real equals `2·((n:ℝ)+1)`. -/
private lemma Q_cast (n : ℕ) : (((2 * (n + 1) : ℕ) : ℝ)) = 2 * ((n : ℝ) + 1) := by
  norm_num

/-- Indicator of the singletons of `X`, as an `ℝ≥0`-valued function on subsets. -/
private noncomputable def singFun (S : Set X) : ℝ≥0 := by
  classical
  exact if ∃ x : X, S = {x} then 1 else 0

/-- Pointwise identity used to compute the weighted sum of `singFun`. -/
private lemma singFun_term (pv : ℝ) (S : Set X) :
    (singFun S : ℝ) * pv ^ S.ncard = if ∃ x : X, S = {x} then pv ^ S.ncard else 0 := by
  classical
  by_cases hS : ∃ x : X, S = {x}
  · have hs : singFun S = 1 := by simp [singFun, hS]
    rw [hs, if_pos hS]
    simp
  · have hs : singFun S = 0 := by simp [singFun, hS]
    rw [hs, if_neg hS]
    simp

/-- `∑ S, singFun S · pv ^ |S| = pv · |X|`: only the |X| singletons contribute, each with `pv`. -/
private lemma singFun_weighted_sum (pv : ℝ) :
    (∑ S : Set X, (singFun S : ℝ) * pv ^ S.ncard) = pv * (Fintype.card X : ℝ) := by
  classical
  let Fsing : Finset (Set X) :=
    (Finset.univ : Finset (Set X)).filter (fun S : Set X => ∃ x : X, S = {x})
  let pF : Set X → Prop := fun S => ∃ x : X, S = {x}
  calc
    (∑ S : Set X, (singFun S : ℝ) * pv ^ S.ncard)
        = ∑ S : Set X, (if pF S then pv ^ S.ncard else 0) := by
            apply Finset.sum_congr rfl
            intro S hS
            simpa [pF] using singFun_term pv S
    _ = ∑ S ∈ (Finset.univ : Finset (Set X)) with pF S, pv ^ S.ncard := by
            rw [← Finset.sum_filter]
    _ = ∑ S ∈ Fsing, pv ^ S.ncard := by
            dsimp [Fsing, pF]
    _ = pv * (Fintype.card X : ℝ) := by
            have hcard : (Fsing.card : ℝ) = (Fintype.card X : ℝ) := by
              dsimp [Fsing]
              exact_mod_cast card_singletons
            rw [← hcard]
            have hterms : ∀ S ∈ Fsing, pv ^ S.ncard = pv := by
              intro S hS
              have hSx : ∃ x : X, S = {x} := (Finset.mem_filter.mp hS).2
              rcases hSx with ⟨x, rfl⟩
              simp
            calc
              (∑ S ∈ Fsing, pv ^ S.ncard) = ∑ S ∈ Fsing, pv := by
                apply Finset.sum_congr rfl
                intro S hS
                exact hterms S hS
              _ = pv * (Fsing.card : ℝ) := by
                simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- `q_f(𝓕) ≥ p` whenever `𝓕` is weakly `p`-small. -/
private lemma q_f_ge_of_weakly_small_aux {𝓕 : Set (Set X)} {p : I} (hp : IsWeaklySmall p 𝓕) :
    (q_f 𝓕 : ℝ) ≥ (p : ℝ) := by
  classical
  unfold q_f
  have hmem : p ∈ {q : I | IsWeaklySmall q 𝓕} := hp
  exact le_csSup ⟨(1 : I), by intro q hq; exact (q : I).2.2⟩ hmem

/-- An increasing family with `2 ≤ l 𝓕` never contains the empty set. -/
lemma not_mem_empty_of_two_le_l {𝓕 : Set (Set X)} (h𝓕 : IsUpperSet 𝓕) (hl : 2 ≤ l 𝓕) :
    (∅ : Set X) ∉ 𝓕 := by
  intro h0
  have hle : l 𝓕 ≤ 0 := l_le_zero_of_mem_empty h0
  omega

/-- `q_f(𝓕)` is strictly positive for increasing `𝓕` with `2 ≤ l 𝓕`. -/
lemma q_f_pos {𝓕 : Set (Set X)} (h𝓕 : IsUpperSet 𝓕) (hl : 2 ≤ l 𝓕) :
    0 < (q_f 𝓕 : ℝ) := by
  classical
  -- Because `2 ≤ l 𝓕`, the empty set is not in `𝓕`, so every member of `𝓕` is
  -- nonempty.  Giving unit `singFun`-mass to every singleton of `X` makes each
  -- member of `𝓕` contain a singleton, while the total `p`-weighted mass is
  -- `|X|·p`, which is `≤ 1/2` for `p = 1 / (2·(|X| + 1))`.
  have hnotempty : (∅ : Set X) ∉ 𝓕 := not_mem_empty_of_two_le_l h𝓕 hl
  let n : ℕ := Fintype.card X
  let pv : ℝ := ((2 * (n + 1) : ℕ) : ℝ)⁻¹
  have hQ : (0 : ℝ) < ((2 * (n + 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * (n + 1))
  have hQnz : ((2 * (n + 1) : ℕ) : ℝ) ≠ 0 := ne_of_gt hQ
  have hpv0 : 0 < pv := by
    dsimp [pv]
    positivity
  have hpv12 : pv ≤ (1 / 2 : ℝ) := by
    dsimp [pv]
    field_simp [hQnz]
    nlinarith [Q_cast n]
  have hpv1 : pv ≤ 1 := by linarith
  let p₀ : I := ⟨pv, le_of_lt hpv0, hpv1⟩
  have hp₀ : (p₀ : ℝ) = pv := rfl
  have hws : IsWeaklySmall p₀ 𝓕 := by
    refine ⟨singFun, ?_, ?_⟩
    · -- (i): every `T ∈ 𝓕` contains a singleton, whose mass alone is `1`.
      intro T hT
      have hTn : T ≠ (∅ : Set X) := by
        intro hTe
        exact hnotempty (by simpa [hTe] using hT)
      rcases Set.nonempty_iff_ne_empty.mpr hTn with ⟨x, hx⟩
      have hmemF : ({x} : Set X) ∈
          (Finset.univ : Finset (Set X)).filter (fun S : Set X => S ⊆ T) := by
        simp [hx]
      have hg1 : singFun ({x} : Set X) = 1 := by
        simp [singFun]
      have hs := Finset.single_le_sum
        (s := (Finset.univ : Finset (Set X)).filter (fun S : Set X => S ⊆ T))
        (f := singFun) (by intro b hb; exact (singFun b).2) hmemF
      rw [hg1] at hs
      exact hs
    · -- (ii): the total weighted mass is `|X|·p₀ ≤ 1/2`.
      have hsum : (∑ S : Set X, (singFun S : ℝ) * (p₀ : ℝ) ^ S.ncard) ≤ pv * (n : ℝ) := by
        have heq : (∑ S : Set X, (singFun S : ℝ) * (p₀ : ℝ) ^ S.ncard) = pv * (n : ℝ) := by
          calc
            (∑ S : Set X, (singFun S : ℝ) * (p₀ : ℝ) ^ S.ncard) = pv * (Fintype.card X : ℝ) := by
                rw [← hp₀]
                exact singFun_weighted_sum (X := X) (pv := (p₀ : ℝ))
            _ = pv * (n : ℝ) := by rw [show (Fintype.card X : ℝ) = (n : ℝ) by dsimp [n]]
        rw [heq]
      have hfin : pv * (n : ℝ) ≤ (1 / 2 : ℝ) := by
        dsimp [pv]
        field_simp [hQnz]
        nlinarith [Q_cast n]
      have hhalf : (2⁻¹ : ℝ) = (1 / 2 : ℝ) := by norm_num
      rw [hhalf]
      exact le_trans hsum hfin
  have hp₀pos : 0 < (p₀ : ℝ) := by simpa [hp₀] using hpv0
  have hle : (p₀ : ℝ) ≤ (q_f 𝓕 : ℝ) := q_f_ge_of_weakly_small_aux hws
  linarith

end FET
end Submission
