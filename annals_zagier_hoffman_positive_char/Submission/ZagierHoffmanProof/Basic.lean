import ChallengeDeps

set_option autoImplicit false

open Polynomial RatFunc
open scoped BigOperators

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section BasicNat

/-- Every entry of a tuple of positive naturals is at most the sum. -/
lemma pnat_entry_le_sum (r : ℕ) (f : Fin r → ℕ+) (i : Fin r) :
    ((f i : ℕ) ≤ ∑ j : Fin r, (f j : ℕ)) := by
  exact Finset.single_le_sum (fun j hj => Nat.zero_le ((f j : ℕ))) (Finset.mem_univ i)

/-- If a tuple of `r` positive naturals has sum `w`, then `r ≤ w`. -/
lemma card_le_sum_pnat (r : ℕ) (f : Fin r → ℕ+) :
    (r ≤ ∑ j : Fin r, (f j : ℕ)) := by
  have h1 : ∀ j ∈ (Finset.univ : Finset (Fin r)), 1 ≤ (f j : ℕ) := by
    intro j hj
    exact PNat.pos _
  calc
    r = ∑ j : Fin r, (1 : ℕ) := by simp
    _ ≤ ∑ j : Fin r, (f j : ℕ) := Finset.sum_le_sum h1

end BasicNat

/-- membership in 𝔖_w --/
lemma 𝔖_w_mem_iff (w r : ℕ) (𝔰 : Fin r → ℕ+) :
    𝔰 ∈ 𝔖_w w r ↔ (∑ i : Fin r, (𝔰 i : ℕ)) = w := by
  rfl

/-- membership in ζ_A_weight --/
lemma ζ_A_weight_mem_iff (w r : ℕ) (x : CompletionAtInfty F) :
    x ∈ ζ_A_weight F w r ↔
      ∃ 𝔰 : Fin r → ℕ+, (∑ i : Fin r, (𝔰 i : ℕ)) = w ∧ x = ζ_A F 𝔰 := by
  simp [ζ_A_weight, 𝔖_w, eq_comm]

/-- every weight-w MZV value lies in 𝒵 w --/
lemma ζ_A_weight_subset_span (w r : ℕ) :
    ζ_A_weight F w r ⊆ 𝒵 F w := by
  intro x hx
  exact Submodule.subset_span (by
    simp [𝒵]
    exact ⟨r, hx⟩)

/-- For `w ≥ 1`, there are no empty weight-`w` tuples: `𝔖_w w 0 = ∅`. -/
lemma 𝔖_w_zero_eq_empty (w : ℕ) (hw : 1 ≤ w) : 𝔖_w w 0 = ∅ := by
  ext 𝔰
  simp [𝔖_w]
  omega

/-- The weight-`w` MZVs of depth `0` are empty for `w ≥ 1`. -/
lemma ζ_A_weight_zero_eq_empty (w : ℕ) (hw : 1 ≤ w) : ζ_A_weight F w 0 = ∅ := by
  ext x
  constructor <;> intro hx
  · rw [ζ_A_weight_mem_iff F w 0] at hx
    rcases hx with ⟨𝔰, hsum, hx⟩
    have : (0 : ℕ) = w := by simpa using hsum
    omega
  · simpa using hx

/-- If `r > w` then there are no weight-`w` tuples of length `r`. -/
lemma 𝔖_w_empty_of_lt {w r : ℕ} (h : w < r) : 𝔖_w w r = ∅ := by
  ext f
  constructor
  · intro hf
    have hr : r ≤ ∑ j : Fin r, (f j : ℕ) := card_le_sum_pnat r f
    rw [𝔖_w_mem_iff] at hf
    omega
  · intro hf
    simp at hf

/-- membership in 𝒯_aux --/
lemma mem_𝒯_aux_iff (w : ℕ) (r : ℕ+) (x : CompletionAtInfty F) :
    x ∈ 𝒯_aux F w r ↔
      ∃ 𝔰 : Fin r → ℕ+,
        (𝔰 ∈ 𝔖_w w r ∧
          (∀ i : Fin r, i < (r - 1 : ℕ) → (𝔰 i : ℕ) ≤ Nat.card F) ∧
          ((𝔰 ⟨r - 1, by simp⟩ : ℕ) < Nat.card F) ∧ x = ζ_A F 𝔰) := by
  classical
  unfold 𝒯_aux
  simp only [Set.mem_setOf_eq, 𝔖_w]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, hs.1.1, hs.1.2.1, hs.1.2.2, hs.2.symm⟩
  · rintro ⟨s, hsum, h1, h2, hx⟩
    exact ⟨s, ⟨hsum, ⟨h1, h2⟩⟩, hx.symm⟩

/-- membership in 𝒯0_aux --/
lemma mem_𝒯0_aux_iff (w : ℕ) (r : ℕ+) (x : CompletionAtInfty F) :
    x ∈ 𝒯0_aux F w r ↔
      ∃ 𝔰 : Fin r → ℕ+,
        (𝔰 ∈ 𝔖_w w r ∧ (∀ i : Fin r, (𝔰 i : ℕ) < Nat.card F) ∧ x = ζ_A F 𝔰) := by
  classical
  unfold 𝒯0_aux
  simp only [Set.mem_setOf_eq, 𝔖_w]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, hs.1.1, hs.1.2, hs.2.symm⟩
  · rintro ⟨s, hsum, h1, hx⟩
    exact ⟨s, ⟨hsum, h1⟩, hx.symm⟩

/-- 𝒯0_aux ⊆ 𝒯_aux --/
lemma 𝒯0_aux_subset_𝒯_aux (w : ℕ) (r : ℕ+) : 𝒯0_aux F w r ⊆ 𝒯_aux F w r := by
  intro x hx
  rw [mem_𝒯0_aux_iff F w r] at hx
  rw [mem_𝒯_aux_iff F w r]
  rcases hx with ⟨𝔰, h𝔖, hall, rfl⟩
  refine ⟨𝔰, h𝔖, ?_, ?_, rfl⟩
  · intro i hi
    exact le_of_lt (hall i)
  · exact hall ⟨r - 1, by simp⟩

lemma mem_𝒯_iff (w : ℕ) (x : CompletionAtInfty F) :
    x ∈ 𝒯 F w ↔ ∃ r : ℕ+, x ∈ 𝒯_aux F w r := by
  simp [𝒯]

lemma mem_𝒯0_iff (w : ℕ) (x : CompletionAtInfty F) :
    x ∈ 𝒯0 F w ↔ ∃ r : ℕ+, x ∈ 𝒯0_aux F w r := by
  simp [𝒯0]

lemma 𝒯0_subset_𝒯 (w : ℕ) : 𝒯0 F w ⊆ 𝒯 F w := by
  intro x hx
  rw [mem_𝒯0_iff] at hx
  rw [mem_𝒯_iff]
  rcases hx with ⟨r, hr⟩
  exact ⟨r, 𝒯0_aux_subset_𝒯_aux F w r hr⟩

/-- Elements of `𝒯_aux` are weight-`w` MZVs, hence lie in `𝒵 w`. -/
lemma 𝒯_aux_subset_𝒵 (w : ℕ) (r : ℕ+) : (𝒯_aux F w r : Set (CompletionAtInfty F)) ⊆ 𝒵 F w := by
  intro x hx
  rw [mem_𝒯_aux_iff F w r] at hx
  rcases hx with ⟨𝔰, h𝔖, h1, h2, rfl⟩
  exact Submodule.subset_span (by
    simp [𝒵]
    refine ⟨(r : ℕ), ⟨𝔰, ?_, rfl⟩⟩
    simpa [𝔖_w] using h𝔖)

/-- Elements of `𝒯 w` lie in `𝒵 w`. -/
lemma 𝒯_subset_𝒵 (w : ℕ) : (𝒯 F w : Set (CompletionAtInfty F)) ⊆ 𝒵 F w := by
  intro x hx
  rw [mem_𝒯_iff F w] at hx
  rcases hx with ⟨r, hr⟩
  exact 𝒯_aux_subset_𝒵 F w r hr


/-- If `r > w`, there are no weight-`w` MZVs of depth `r`. -/
lemma ζ_A_weight_eq_empty_of_lt {w r : ℕ} (h : w < r) : ζ_A_weight F w r = ∅ := by
  ext x
  constructor <;> intro hx
  · rw [ζ_A_weight_mem_iff F w r] at hx
    rcases hx with ⟨𝔰, hsum, hx⟩
    exfalso
    have hr : r ≤ ∑ j : Fin r, (𝔰 j : ℕ) := card_le_sum_pnat r 𝔰
    omega
  · simpa using hx

/-- For `w ≥ 1` the family of weight-`w` MZVs is supported on depths `r ≤ w`. -/
lemma ζ_A_weight_iUnion_eq_range (w : ℕ) (hw : 1 ≤ w) :
    (⋃ r : ℕ, ζ_A_weight F w r) = ⋃ r ∈ Finset.range (w + 1), ζ_A_weight F w r := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨r, hr⟩
    rw [Set.mem_iUnion₂]
    by_cases hrw : r ≤ w
    · exact ⟨r, Finset.mem_range.mpr (Nat.lt_succ_of_le hrw), hr⟩
    · have h0 : ζ_A_weight F w r = ∅ := ζ_A_weight_eq_empty_of_lt F (by omega)
      simp [h0] at hr
  · intro hx
    rw [Set.mem_iUnion]
    rw [Set.mem_iUnion₂] at hx
    rcases hx with ⟨r, hr, hxr⟩
    exact ⟨r, hxr⟩

/-- `𝒵 w` is spanned by the weight-`w` MZVs of depth at most `w` (finite family). -/
lemma 𝒵_eq_span_range (w : ℕ) (hw : 1 ≤ w) :
    𝒵 F w = Submodule.span (RatFunc F) (⋃ r ∈ Finset.range (w + 1), ζ_A_weight F w r) := by
  rw [𝒵, ζ_A_weight_iUnion_eq_range F w hw]


end ZagierHoffmanPositiveChar
