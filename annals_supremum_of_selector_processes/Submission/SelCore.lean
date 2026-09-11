import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.Frame

/-!
# Core combinatorial theorem (selector processes)
Section 2 of Park--Pham, Ann. Math. 199 (2024).
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Sel

open Frame

/-! ## p-small over a finite type -/

section pSmall

variable {X : Type*} [Fintype X]

/-- Sum of costs over a Finset of subsets. -/
noncomputable def totalCost (p : ℝ) (𝓖 : Finset (Set X)) : ℝ :=
  ∑ s ∈ 𝓖, p ^ s.ncard

/-- `p-small` for a family `𝓕 : Set (Set X)`, witnessed by a Finset cover. -/
def pSmall (p : ℝ) (𝓕 : Set (Set X)) : Prop :=
  ∃ 𝓖 : Finset (Set X), (∀ S ∈ 𝓕, ∃ g ∈ 𝓖, g ⊆ S) ∧ totalCost p 𝓖 ≤ (2 : ℝ)⁻¹

lemma totalCost_empty (p : ℝ) : totalCost p (∅ : Finset (Set X)) = 0 := by
  simp [totalCost]

lemma totalCost_union {p : ℝ} {𝓖 𝓗 : Finset (Set X)} (h : Disjoint 𝓖 𝓗) :
    totalCost p (𝓖 ∪ 𝓗) = totalCost p 𝓖 + totalCost p 𝓗 := by
  unfold totalCost
  rw [Finset.sum_union h]

lemma pSmall.empty {p : ℝ} : pSmall p (∅ : Set (Set X)) := by
  refine ⟨∅, ?_, ?_⟩ <;> simp [totalCost]

lemma pSmall.mono {p : ℝ} {𝓕 𝓖 : Set (Set X)} (h : 𝓕 ⊆ 𝓖) : pSmall p 𝓖 → pSmall p 𝓕 := by
  rintro ⟨𝓒, hcov, hcost⟩
  exact ⟨𝓒, fun S hS => hcov S (h hS), hcost⟩

/-- If every member of `𝓕'` contains a member of the p-small family `𝓕`, then `𝓕'` is p-small. -/
lemma pSmall.of_subset_replace {p : ℝ} {𝓕 𝓕' : Set (Set X)}
    (h : ∀ ⦃S'⦄, S' ∈ 𝓕' → ∃ S ∈ 𝓕, S ⊆ S') : pSmall p 𝓕 → pSmall p 𝓕' := by
  rintro ⟨𝓒, hcov, hcost⟩
  refine ⟨𝓒, ?_, hcost⟩
  intro S' hS'
  rcases h hS' with ⟨S, hS, hSS'⟩
  rcases hcov S hS with ⟨g, hg, hgS⟩
  exact ⟨g, hg, hgS.trans hSS'⟩

/-- If every member of `𝓕` contains a member of the p-small family `𝓕'`, then `𝓕` is p-small.
Talagrand's "spread" observation. -/
lemma pSmall.superset_family {p : ℝ} {𝓕 𝓕' : Set (Set X)}
    (h : ∀ ⦃S⦄, S ∈ 𝓕 → ∃ S' ∈ 𝓕', S' ⊆ S) : pSmall p 𝓕' → pSmall p 𝓕 := by
  rintro ⟨𝓒, hcov, hcost⟩
  refine ⟨𝓒, ?_, hcost⟩
  intro S hS
  rcases h hS with ⟨S', hS', hS'S⟩
  rcases hcov S' hS' with ⟨g, hg, hgS'⟩
  exact ⟨g, hg, hgS'.trans hS'S⟩

lemma pSmall.not_of_singletons_cover {p : ℝ} {𝓕 : Set (Set X)} (hnotmem : ∅ ∉ 𝓕)
    (hp : (Fintype.card X : ℝ) * p ≤ (2 : ℝ)⁻¹) : pSmall p 𝓕 := by
  classical
  let 𝓖 : Finset (Set X) := Finset.univ.image (fun x : X => ({x} : Set X))
  refine ⟨𝓖, ?_, ?_⟩
  · intro S hS
    have hSn : S.Nonempty := by
      by_contra h
      have hSempty : S = ∅ := (Set.not_nonempty_iff_eq_empty).1 h
      exact hnotmem (hSempty ▸ hS)
    rcases hSn with ⟨x, hx⟩
    refine ⟨{x}, ?_, ?_⟩
    · simp [𝓖]
    · intro y hy
      have hyx : y = x := (Set.mem_singleton_iff).mp hy
      simpa [hyx]
  · rw [totalCost]
    calc
      (∑ s ∈ 𝓖, p ^ s.ncard) = ∑ s ∈ 𝓖, p := by
        apply Finset.sum_congr rfl
        intro s hs
        have hs' : ∃ x : X, ({x} : Set X) = s := by simpa [𝓖] using hs
        rcases hs' with ⟨x, hx⟩
        rw [← hx]
        simp
      _ = (Fintype.card X : ℝ) * p := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hcard : 𝓖.card = Fintype.card X := by
          rw [Finset.card_image_of_injective]
          · simp [𝓖]
          · intro x y h; simpa using h
        rw [hcard]
      _ ≤ (2 : ℝ)⁻¹ := hp

/-- not-p-small implies `n p > 1/2` (when ∅ not in family). -/
lemma pSmall.not_of_np {p : ℝ} {𝓕 : Set (Set X)} (h : ¬ pSmall p 𝓕) (hnotmem : ∅ ∉ 𝓕) :
    (2 : ℝ)⁻¹ < (Fintype.card X : ℝ) * p := by
  by_contra hle
  have : (Fintype.card X : ℝ) * p ≤ (2 : ℝ)⁻¹ := le_of_not_gt hle
  exact h (pSmall.not_of_singletons_cover hnotmem this)

end pSmall

/-! ## weights and sums over subsets -/

section weights

variable {X : Type*} [Fintype X]

/-- Sum of the weight function `lam S` over the elements of `A` that lie in `S`. -/
noncomputable def wsum (lam : Set X → X → ℝ) (S A : Set X) : ℝ := by
  classical
  exact ∑ i ∈ (A ∩ S).toFinset, lam S i

/-- total weight of S under lam (sum over S). -/
noncomputable def wtotal (lam : Set X → X → ℝ) (S : Set X) : ℝ := by
  classical
  exact ∑ i ∈ S.toFinset, lam S i

/-- Supremum of `v S` over `S ∈ 𝓕`, as a real number (0 if 𝓕 is empty). -/
noncomputable def famSup (v : Set X → ℝ) (𝓕 : Set (Set X)) : ℝ := by
  classical
  exact if h : (𝓕.toFinset.image v).Nonempty then (𝓕.toFinset.image v).max' h else 0

lemma famSup_of_empty (v : Set X → ℝ) (𝓕 : Set (Set X)) (h𝓕 : 𝓕 = ∅) : famSup v 𝓕 = 0 := by
  classical
  have hg : (𝓕.toFinset.image v) = ∅ := by simp [h𝓕]
  unfold famSup
  by_cases h : (𝓕.toFinset.image v).Nonempty
  · exact False.elim ((Finset.not_nonempty_iff_eq_empty.mpr hg) h)
  · simp [h]

lemma le_famSup {v : Set X → ℝ} {𝓕 : Set (Set X)} {S : Set X} (hS : S ∈ 𝓕) :
    v S ≤ famSup v 𝓕 := by
  classical
  unfold famSup
  by_cases h : (𝓕.toFinset.image v).Nonempty
  · simp [h]
    exact Finset.le_max' (𝓕.toFinset.image v) (v S)
      (Finset.mem_image.mpr ⟨S, (Set.mem_toFinset).2 hS, rfl⟩)
  · exfalso
    exact h ⟨v S, (Finset.mem_image.mpr ⟨S, (Set.mem_toFinset).2 hS, rfl⟩)⟩

lemma famSup_le_of_forall {v : Set X → ℝ} {𝓕 : Set (Set X)} {c : ℝ}
    (h : ∀ S ∈ 𝓕, v S ≤ c) (hc : 0 ≤ c) : famSup v 𝓕 ≤ c := by
  classical
  unfold famSup
  by_cases hne : (𝓕.toFinset.image v).Nonempty
  · have hm : (𝓕.toFinset.image v).max' hne ≤ c :=
      Finset.max'_le (𝓕.toFinset.image v) hne c (by
        intro y hy
        rcases (Finset.mem_image).1 hy with ⟨T, hT, rfl⟩
        exact h T ((Set.mem_toFinset).1 hT))
    simpa [hne] using hm
  · simp [hne, hc]

lemma famSup_nonneg {v : Set X → ℝ} {𝓕 : Set (Set X)}
    (hv : ∀ S ∈ 𝓕, 0 ≤ v S) : 0 ≤ famSup v 𝓕 := by
  classical
  by_cases hne : 𝓕.Nonempty
  · rcases hne with ⟨S, hS⟩
    exact le_trans (hv S hS) (le_famSup (v := v) hS)
  · have h𝓕 : 𝓕 = ∅ := (Set.not_nonempty_iff_eq_empty).1 hne
    rw [famSup_of_empty v 𝓕 h𝓕]

lemma famSup_mono {v w : Set X → ℝ} {𝓕 : Set (Set X)}
    (h : ∀ S ∈ 𝓕, v S ≤ w S) (hv : ∀ S ∈ 𝓕, 0 ≤ v S) : famSup v 𝓕 ≤ famSup w 𝓕 := by
  classical
  refine famSup_le_of_forall (c := famSup w 𝓕) (fun S hS => ?_) (famSup_nonneg (fun S hS => ?_))
  · exact (h S hS).trans (le_famSup (v := w) hS)
  · exact (hv S hS).trans (h S hS)

lemma famSup_congr {v w : Set X → ℝ} {𝓕 : Set (Set X)}
    (h : ∀ S ∈ 𝓕, v S = w S) : famSup v 𝓕 = famSup w 𝓕 := by
  classical
  unfold famSup
  by_cases h1 : (𝓕.toFinset.image v).Nonempty
  · have h2 : (𝓕.toFinset.image w).Nonempty := by
      rcases h1 with ⟨y, hy⟩
      rcases (Finset.mem_image).1 hy with ⟨S, hS, rfl⟩
      exact ⟨w S, (Finset.mem_image.mpr ⟨S, hS, rfl⟩)⟩
    simp [h1, h2]
    apply le_antisymm
    · apply Finset.max'_le (𝓕.toFinset.image v) h1
      intro y hy
      rcases (Finset.mem_image).1 hy with ⟨S, hS, rfl⟩
      exact (le_of_eq (h S ((Set.mem_toFinset).1 hS))).trans
        (Finset.le_max' (𝓕.toFinset.image w) (w S)
          (Finset.mem_image.mpr ⟨S, hS, rfl⟩))
    · apply Finset.max'_le (𝓕.toFinset.image w) h2
      intro y hy
      rcases (Finset.mem_image).1 hy with ⟨S, hS, rfl⟩
      exact (le_of_eq (h S ((Set.mem_toFinset).1 hS)).symm).trans
        (Finset.le_max' (𝓕.toFinset.image v) (v S)
          (Finset.mem_image.mpr ⟨S, hS, rfl⟩))
  · have hnot : ¬(𝓕.toFinset.image w).Nonempty := by
      intro hw
      rcases hw with ⟨y, hy⟩
      rcases (Finset.mem_image).1 hy with ⟨S, hS, rfl⟩
      exact h1 ⟨v S, (Finset.mem_image.mpr ⟨S, hS, rfl⟩)⟩
    simp [h1, hnot]

lemma famSup_le_famSup_of_subset {v : Set X → ℝ} {𝓕 𝓖 : Set (Set X)} (h : 𝓕 ⊆ 𝓖)
    (hv : ∀ S ∈ 𝓖, 0 ≤ v S) : famSup v 𝓕 ≤ famSup v 𝓖 := by
  classical
  refine famSup_le_of_forall (c := famSup v 𝓖) (fun S hS => ?_) (famSup_nonneg hv)
  exact le_famSup (v := v) (h hS)

