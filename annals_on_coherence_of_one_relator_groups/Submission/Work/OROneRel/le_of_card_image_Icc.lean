import Mathlib

namespace Work.OROneRel

/-- Pigeonhole principle for integer intervals: an injective map from the
`C` integers `0, …, C - 1` into an interval `[lo, hi]` forces `hi - lo + 1 ≥ C`. -/
theorem le_of_card_image_Icc {lo hi C : ℤ} (hC : 1 ≤ C) (S : ℤ → ℤ)
    (hmem : ∀ v : ℤ, 0 ≤ v → v ≤ C - 1 → lo ≤ S v ∧ S v ≤ hi)
    (hinj : ∀ v w : ℤ, 0 ≤ v → v ≤ C - 1 → 0 ≤ w → w ≤ C - 1 → S v = S w → v = w) :
    C - 1 ≤ hi - lo := by
  -- `S` maps the finite set `{0, …, C - 1}` injectively into `[lo, hi]`.
  have hmaps : Set.MapsTo S ↑(Finset.Icc (0 : ℤ) (C - 1)) ↑(Finset.Icc lo hi) := by
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_Icc] at hx ⊢
    exact hmem x hx.1 hx.2
  have hinjOn : Set.InjOn S ↑(Finset.Icc (0 : ℤ) (C - 1)) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
    exact hinj x y hx.1 hx.2 hy.1 hy.2 hxy
  have hcard := Finset.card_le_card_of_injOn S hmaps hinjOn
  -- Evaluate the two cardinalities as integers.
  have hsimp : (C - 1 + 1 - 0 : ℤ) = C := by ring
  rw [Int.card_Icc, Int.card_Icc, hsimp] at hcard
  have h1 : (C.toNat : ℤ) = C := Int.toNat_of_nonneg (by linarith)
  have h2 : ((hi + 1 - lo).toNat : ℤ) = hi + 1 - lo := by
    apply Int.toNat_of_nonneg
    by_contra hneg
    have hneg' : hi + 1 - lo < 0 := not_le.mp hneg
    have hz : (hi + 1 - lo).toNat = 0 := Int.toNat_of_nonpos (le_of_lt hneg')
    rw [hz] at hcard
    have hC0 : C.toNat = 0 := Nat.le_zero.mp hcard
    have : C = 0 := by rw [← h1, hC0]; norm_num
    linarith
  have : (C.toNat : ℤ) ≤ ((hi + 1 - lo).toNat : ℤ) := by exact_mod_cast hcard
  rw [h1, h2] at this
  linarith

end Work.OROneRel
