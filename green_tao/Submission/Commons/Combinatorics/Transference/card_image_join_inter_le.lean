import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval

namespace Commons.Combinatorics.Transference

/-- Coordinate bound: for `|g x| ≤ M`, `0 ≤ α < ε` and `ε > 0`, the level index
`⌊(g x - α)/ε⌋` lies in the integer interval `[-⌈M/ε⌉ - 2, ⌈M/ε⌉ + 2]`. -/
private lemma floor_div_mem_Icc {g : ℝ} {ε : ℝ} (hε : 0 < ε) {α : ℝ}
    (hα0 : 0 ≤ α) (hαε : α < ε) {M : ℝ} (hg : |g| ≤ M) :
    ⌊(g - α) / ε⌋ ∈ Finset.Icc (-(⌈M / ε⌉ + 2)) (⌈M / ε⌉ + 2) := by
  rw [Finset.mem_Icc]
  constructor
  · rw [Int.le_floor]
    rw [le_div_iff₀ hε]
    have hgm : -M ≤ g := (abs_le.mp hg).1
    have hαle : α ≤ ε := le_of_lt hαε
    have hc : M / ε ≤ (⌈M / ε⌉ : ℤ) := Int.le_ceil _
    have hM : M ≤ (⌈M / ε⌉ : ℤ) * ε := by
      have := mul_le_mul_of_nonneg_right hc (le_of_lt hε)
      rwa [div_mul_cancel₀ M (ne_of_gt hε)] at this
    push_cast
    nlinarith
  · have hx : (g - α) / ε ≤ M / ε := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hε)
      have hgm : g ≤ M := (abs_le.mp hg).2
      linarith
    have h1 : ⌊(g - α) / ε⌋ ≤ ⌊M / ε⌋ := Int.floor_le_floor hx
    have h2 : ⌊M / ε⌋ ≤ ⌈M / ε⌉ := Int.floor_le_ceil _
    have h3 : (⌈M / ε⌉ : ℤ) ≤ ⌈M / ε⌉ + 2 := by omega
    exact h1.trans (h2.trans h3)

theorem card_image_join_inter_le {X : Type*} [Fintype X] [DecidableEq X] {K : ℕ}
    (P : X → Finset X) (hPmem : ∀ x, x ∈ P x) (hPeq : ∀ x y : X, y ∈ P x → P y = P x)
    (g : Fin K → X → ℝ) {ε : ℝ} (hε : 0 < ε) (α : Fin K → ℝ)
    (hα0 : ∀ j, 0 ≤ α j) (hαε : ∀ j, α j < ε) {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ (j : Fin K) (x : X), |g j x| ≤ M) :
    (Finset.univ.image (fun x => P x ∩ Finset.univ.filter
        (fun y => ∀ j : Fin K, ⌊(g j y - α j) / ε⌋ = ⌊(g j x - α j) / ε⌋))).card
      ≤ (Finset.univ.image P).card * (2 * (⌈M / ε⌉ + 2) + 1).toNat ^ K := by
  -- The map `x ↦ P x ∩ (level set of `x`)` factors through the pair
  -- `x ↦ (P x, (⌊(g j x - α j)/ε⌋)_j)`.  Bounding the image of this pair by the
  -- product of the number of parts of `P` and the number of possible level tuples
  -- gives the claim.
  let tup : X → (Fin K → ℤ) := fun x j => ⌊(g j x - α j) / ε⌋
  let F : X → Finset X := fun x => P x ∩ Finset.univ.filter
        (fun y => ∀ j : Fin K, ⌊(g j y - α j) / ε⌋ = ⌊(g j x - α j) / ε⌋)
  let φ : Finset X × (Fin K → ℤ) → Finset X := fun p => p.1 ∩ Finset.univ.filter
        (fun y => ∀ j : Fin K, ⌊(g j y - α j) / ε⌋ = p.2 j)
  let T : X → Finset X × (Fin K → ℤ) := fun x => (P x, tup x)
  have hFT : ∀ x, φ (T x) = F x := by
    intro x
    simp only [φ, T, F, tup]
  have hcard : (Finset.univ.image F).card ≤ (Finset.univ.image T).card := by
    have hsub : Finset.univ.image F ⊆ (Finset.univ.image T).image φ := by
      intro A hA
      rw [Finset.mem_image] at hA
      obtain ⟨x, -, rfl⟩ := hA
      exact Finset.mem_image.mpr ⟨T x, Finset.mem_image_of_mem T (Finset.mem_univ x), hFT x⟩
    calc (Finset.univ.image F).card ≤ ((Finset.univ.image T).image φ).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.image T).card := Finset.card_image_le
  have hcardT : (Finset.univ.image T).card
      ≤ (Finset.univ.image P).card * (Finset.univ.image tup).card := by
    have hsub : Finset.univ.image T ⊆ (Finset.univ.image P) ×ˢ (Finset.univ.image tup) := by
      intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨x, -, rfl⟩ := ha
      rw [Finset.mem_product]
      exact ⟨Finset.mem_image_of_mem P (Finset.mem_univ x),
             Finset.mem_image_of_mem tup (Finset.mem_univ x)⟩
    calc (Finset.univ.image T).card
        ≤ ((Finset.univ.image P) ×ˢ (Finset.univ.image tup)).card := Finset.card_le_card hsub
      _ = (Finset.univ.image P).card * (Finset.univ.image tup).card := Finset.card_product _ _
  have htup : (Finset.univ.image tup).card ≤ (2 * (⌈M / ε⌉ + 2) + 1).toNat ^ K := by
    let I : Finset ℤ := Finset.Icc (-(⌈M / ε⌉ + 2)) (⌈M / ε⌉ + 2)
    have hIcc : ∀ (j : Fin K) (x : X), tup x j ∈ I := by
      intro j x
      simp only [tup, I]
      exact floor_div_mem_Icc hε (hα0 j) (hαε j) (hg j x)
    have hIcard : I.card = (2 * (⌈M / ε⌉ + 2) + 1).toNat := by
      simp only [I]
      rw [Int.card_Icc]
      congr 1
      ring
    have hsub : Finset.univ.image tup ⊆ Fintype.piFinset (fun _ : Fin K => I) := by
      intro f hf
      rw [Finset.mem_image] at hf
      obtain ⟨x, -, rfl⟩ := hf
      rw [Fintype.mem_piFinset]
      intro j
      exact hIcc j x
    calc (Finset.univ.image tup).card
        ≤ (Fintype.piFinset (fun _ : Fin K => I)).card := Finset.card_le_card hsub
      _ = ∏ _ : Fin K, I.card := Fintype.card_piFinset _
      _ = I.card ^ K := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (2 * (⌈M / ε⌉ + 2) + 1).toNat ^ K := by rw [hIcard]
  calc (Finset.univ.image F).card ≤ (Finset.univ.image T).card := hcard
    _ ≤ (Finset.univ.image P).card * (Finset.univ.image tup).card := hcardT
    _ ≤ (Finset.univ.image P).card * (2 * (⌈M / ε⌉ + 2) + 1).toNat ^ K :=
        Nat.mul_le_mul_left _ htup

end Commons.Combinatorics.Transference