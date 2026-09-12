import Mathlib

set_option linter.unusedVariables false

namespace Commons.Nat.Card

open scoped BigOperators

/-- The number of elements of `Fin k` whose value is `< B` is exactly `B`, provided `B ≤ k`. -/
lemma card_filter_val_lt {B k : ℕ} (h : B ≤ k) :
    ((Finset.univ : Finset (Fin k)).filter (fun j : Fin k => j.val < B)).card = B := by
  let T : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun j : Fin k => j.val < B)
  have hT : Fintype.card {j : Fin k // j.val < B} = T.card := by
    exact Fintype.card_of_subtype (s := T) (p := fun j : Fin k => j.val < B) (by intro j; simp [T])
  let e : {j : Fin k // j.val < B} ≃ Fin B :=
    Equiv.ofBijective (fun j : {j : Fin k // j.val < B} => ⟨j.1.val, j.2⟩)
      (by
        constructor
        · intro a b hab
          apply Subtype.ext
          apply Fin.ext
          exact congrArg (fun z : Fin B => z.val) hab
        · intro b
          refine ⟨⟨⟨b.val, lt_of_lt_of_le b.isLt h⟩, b.isLt⟩, ?_⟩
          rfl)
  have h2 : Fintype.card {j : Fin k // j.val < B} = Fintype.card (Fin B) :=
    Fintype.card_congr e
  calc
    T.card = Fintype.card {j : Fin k // j.val < B} := hT.symm
    _ = Fintype.card (Fin B) := h2
    _ = B := Fintype.card_fin B

lemma big_coords_prefix_count {n k : ℕ} {δ₀ δ : ℝ} (hδ₀ : 0 < δ₀)
    (hδle : δ₀ ≤ δ) (hk : δ₀ * (n : ℝ) ≤ k) (hslack : (1 : ℝ) ≤ (δ - δ₀) * (n : ℝ)) :
    δ₀ * (n : ℝ) ≤ (((Finset.univ : Finset (Fin k)).filter
        (fun j : Fin k => (j.val : ℝ) + 1 ≤ δ * (n : ℝ))).card : ℝ) := by
  let S : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter
    (fun j : Fin k => (j.val : ℝ) + 1 ≤ δ * (n : ℝ))
  let B : ℕ := ⌈δ₀ * (n : ℝ)⌉₊
  change δ₀ * (n : ℝ) ≤ (S.card : ℝ)
  have hδ₀n_nonneg : 0 ≤ δ₀ * (n : ℝ) := mul_nonneg (le_of_lt hδ₀) (Nat.cast_nonneg n)
  have hB1 : δ₀ * (n : ℝ) ≤ (B : ℝ) := by
    simpa [B] using (Nat.le_ceil (a := δ₀ * (n : ℝ)))
  have hB2 : B ≤ k := by
    exact (Nat.ceil_le (a := δ₀ * (n : ℝ)) (n := k)).2 hk
  have hδn : δ₀ * (n : ℝ) + 1 ≤ δ * (n : ℝ) := by
    nlinarith [hslack]
  have hB3 : (B : ℝ) < δ₀ * (n : ℝ) + 1 := by
    simpa [B] using (Nat.ceil_lt_add_one (a := δ₀ * (n : ℝ)) hδ₀n_nonneg)
  have hBδ : (B : ℝ) ≤ δ * (n : ℝ) := le_of_lt (lt_of_lt_of_le hB3 hδn)
  let T : Finset (Fin k) := (Finset.univ : Finset (Fin k)).filter (fun j : Fin k => j.val < B)
  have hTcard : T.card = B := by
    simpa [T] using (card_filter_val_lt (B := B) (k := k) hB2)
  have hTsubS : T ⊆ S := by
    intro j hj
    have hjlt : j.val < B := (Finset.mem_filter.mp hj).2
    have hleB : j.val + 1 ≤ B := by omega
    have hcast : (j.val : ℝ) + 1 ≤ (B : ℝ) := by exact_mod_cast hleB
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, le_trans hcast hBδ⟩
  have hcardS : T.card ≤ S.card := Finset.card_le_card hTsubS
  calc
    δ₀ * (n : ℝ) ≤ (B : ℝ) := hB1
    _ = (T.card : ℝ) := by rw [hTcard]
    _ ≤ (S.card : ℝ) := by exact_mod_cast hcardS

end Commons.Nat.Card
