import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ConditionallyCompleteOrder

namespace Commons.Analysis.Sampling

/-- **Counting a separated finite set of reals.**  If `s` is a finite set of reals
lying in `[a,b]` (`a ≤ b`) whose distinct elements are pairwise `δ`-separated
(`δ ≤ |x - y|` for `x ≠ y` in `s`, with `δ > 0`), then
`card s ≤ (b - a)/δ + 1`.

The proof assigns to each `x ∈ s` the integer `⌊(x - a)/δ⌋`; separation makes this
map injective (consecutive values differ by at least one) and the bound `x ≤ b`
confines its image to `{0, 1, …, ⌊(b-a)/δ⌋}`. -/
lemma card_le_separated_finset {s : Finset ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ x ∈ s, a ≤ x) (hb : ∀ x ∈ s, x ≤ b) :
    (s.card : ℝ) ≤ (b - a) / δ + 1 := by
  classical
  have hδne : δ ≠ 0 := ne_of_gt hδ
  -- The floors `⌊(x - a)/δ⌋` are nonnegative on `s`.
  have hfloor_nn : ∀ x ∈ s, 0 ≤ ⌊(x - a) / δ⌋ := by
    intro x hx
    rw [Int.floor_nonneg]
    exact div_nonneg (by linarith [ha x hx]) (le_of_lt hδ)
  -- They are strictly increasing along `s`.
  have hstrict : ∀ x ∈ s, ∀ y ∈ s, x < y → ⌊(x - a) / δ⌋ < ⌊(y - a) / δ⌋ := by
    intro x hx y hy hxy
    have hd : δ ≤ y - x := by
      have h := hsep x hx y hy (ne_of_lt hxy)
      rw [abs_sub_comm, abs_of_pos (by linarith)] at h
      linarith
    have h1 : (x - a) / δ + 1 ≤ (y - a) / δ := by
      rw [div_add_one hδne]
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hδ)
    calc ⌊(x - a) / δ⌋ < ⌊(x - a) / δ⌋ + 1 := lt_add_one _
      _ = ⌊(x - a) / δ + 1⌋ := (Int.floor_add_one _).symm
      _ ≤ ⌊(y - a) / δ⌋ := Int.floor_le_floor h1
  -- In particular `x ↦ ⌊(x - a)/δ⌋.toNat` is injective on `s`.
  have hinj : Set.InjOn (fun x : ℝ => (⌊(x - a) / δ⌋).toNat) ↑s := by
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlt' := hstrict x hx y hy hlt
      have hpos : 0 < ⌊(y - a) / δ⌋ := lt_of_le_of_lt (hfloor_nn x hx) hlt'
      have : (⌊(x - a) / δ⌋).toNat < (⌊(y - a) / δ⌋).toNat :=
        (Int.toNat_lt_toNat hpos).mpr hlt'
      exact absurd hxy (ne_of_lt this)
    · have hgt' := hstrict y hy x hx hgt
      have hpos : 0 < ⌊(x - a) / δ⌋ := lt_of_le_of_lt (hfloor_nn y hy) hgt'
      have : (⌊(y - a) / δ⌋).toNat < (⌊(x - a) / δ⌋).toNat :=
        (Int.toNat_lt_toNat hpos).mpr hgt'
      exact absurd hxy.symm (ne_of_lt this)
  -- The image is contained in `{0, …, ⌊(b-a)/δ⌋}`.
  set K : ℤ := ⌊(b - a) / δ⌋ with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef, Int.floor_nonneg]
    exact div_nonneg (by linarith) (le_of_lt hδ)
  have hsub : Finset.image (fun x : ℝ => (⌊(x - a) / δ⌋).toNat) s ⊆
      Finset.range (K.toNat + 1) := by
    intro z hz
    rw [Finset.mem_range]
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    have hle : ⌊(x - a) / δ⌋ ≤ K := by
      rw [hKdef]
      exact Int.floor_le_floor (div_le_div_of_nonneg_right (by linarith [hb x hx]) (le_of_lt hδ))
    have : (⌊(x - a) / δ⌋).toNat ≤ K.toNat := Int.toNat_le_toNat hle
    omega
  have hcard : (Finset.image (fun x : ℝ => (⌊(x - a) / δ⌋).toNat) s).card ≤ K.toNat + 1 := by
    calc (Finset.image (fun x : ℝ => (⌊(x - a) / δ⌋).toNat) s).card
        ≤ (Finset.range (K.toNat + 1)).card := Finset.card_le_card hsub
      _ = K.toNat + 1 := Finset.card_range _
  have hsr : (s.card : ℝ) ≤ (K.toNat : ℝ) + 1 := by
    rw [← Finset.card_image_of_injOn hinj]
    exact_mod_cast hcard
  have hcast : (K.toNat : ℝ) = (K : ℝ) := by
    have h := Int.toNat_of_nonneg hKnn
    exact_mod_cast h
  have hfle : (K : ℝ) ≤ (b - a) / δ := by
    rw [hKdef]
    exact Int.floor_le _
  linarith

end Commons.Analysis.Sampling