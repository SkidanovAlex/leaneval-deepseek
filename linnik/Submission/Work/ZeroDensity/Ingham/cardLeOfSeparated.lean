import Mathlib

namespace Work.ZeroDensity.Ingham

/-- A finite set of reals contained in `[a, b]` whose points are pairwise at
distance at least `1` has at most `b - a + 1` elements.  (Packing bound: the
floor map `x ↦ ⌊x - a⌋₊` is injective on such a set and lands in
`{0, …, ⌊b - a⌋}`.) -/
theorem cardLeOfSeparated {S : Finset ℝ} {a b : ℝ} (hab : a ≤ b)
    (hbdd : ∀ x ∈ S, a ≤ x ∧ x ≤ b)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    (S.card : ℝ) ≤ b - a + 1 := by
  classical
  -- Successive elements of `S` are at least `1` apart, so `x ↦ ⌊x - a⌋₊` is
  -- strictly increasing, hence injective, along `S`.
  have key : ∀ u v : ℝ, u ∈ S → v ∈ S → u < v → ⌊u - a⌋₊ + 1 ≤ ⌊v - a⌋₊ := by
    intro u v hu hv huv
    have huv' : 1 ≤ v - u := by
      have h := hsep u hu v hv (ne_of_lt huv)
      rw [abs_of_neg (by linarith : u - v < 0)] at h
      linarith
    have h1 : (⌊u - a⌋₊ : ℝ) ≤ u - a := Nat.floor_le (by linarith [(hbdd u hu).1])
    apply Nat.le_floor
    push_cast
    linarith
  have hinj : Set.InjOn (fun x : ℝ => ⌊x - a⌋₊) ↑S := by
    intro x hx y hy hxy
    change ⌊x - a⌋₊ = ⌊y - a⌋₊ at hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := key x y hx hy hlt
      rw [hxy] at this
      omega
    · have := key y x hy hx hlt
      rw [hxy] at this
      omega
  -- Hence `S` has the same cardinality as a subset of `{0, …, ⌊b - a⌋}`.
  have hcard : (S.image fun x : ℝ => ⌊x - a⌋₊).card = S.card :=
    Finset.card_image_of_injOn hinj
  have hsub : S.image (fun x : ℝ => ⌊x - a⌋₊) ⊆ Finset.range (⌊b - a⌋₊ + 1) := by
    intro n hn
    rw [Finset.mem_range]
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    have : ⌊x - a⌋₊ ≤ ⌊b - a⌋₊ := Nat.floor_mono (by linarith [(hbdd x hx).2])
    omega
  have hle : S.card ≤ ⌊b - a⌋₊ + 1 := by
    rw [← hcard]
    calc (S.image fun x : ℝ => ⌊x - a⌋₊).card
        ≤ (Finset.range (⌊b - a⌋₊ + 1)).card := Finset.card_le_card hsub
      _ = ⌊b - a⌋₊ + 1 := Finset.card_range _
  have hfin : (S.card : ℝ) ≤ (⌊b - a⌋₊ : ℝ) + 1 := by
    exact_mod_cast hle
  linarith [Nat.floor_le (show (0 : ℝ) ≤ b - a by linarith)]

end Work.ZeroDensity.Ingham
