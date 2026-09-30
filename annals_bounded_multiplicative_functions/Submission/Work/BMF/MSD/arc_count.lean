import Mathlib
import Submission.Work.BMF.MSD.basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.MSD

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions
open Work.BMF

/-- `circDist` is the distance to the nearest integer, i.e. the distance to `round θ`. -/
lemma circDist_eq_abs_sub_round (θ : ℝ) : circDist θ = |θ - (round θ : ℝ)| := by
  rw [circDist, round_eq]

/-- **Packing bound on a line interval.** A finite set of reals contained in `[0, L]` whose
elements are pairwise `δ`-separated (in the linear sense, `δ ≤ |u a - u b|`) has at most
`L/δ + 1` elements. Proof: the map `u s ↦ ⌊u s / δ⌋₊` is injective on `T` (a gap of at least
`δ` increases the floor by at least one) and its image lies in `{0, 1, …, ⌊L/δ⌋}`. -/
theorem card_le_of_sep {ι : Type*} (T : Finset ι) (u : ι → ℝ) (δ L : ℝ) (hδ : 0 < δ)
    (hL : 0 ≤ L) (hu0 : ∀ s ∈ T, 0 ≤ u s) (huL : ∀ s ∈ T, u s ≤ L)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → δ ≤ |u a - u b|) :
    (T.card : ℝ) ≤ L / δ + 1 := by
  classical
  have hfloor : ∀ {x z : ℝ}, 0 ≤ x → δ ≤ z - x → ⌊x / δ⌋₊ + 1 ≤ ⌊z / δ⌋₊ := by
    intro x z hx hxz
    have hq : x / δ + 1 ≤ z / δ := by
      have h2 : (x + δ) / δ ≤ z / δ := div_le_div_of_nonneg_right (by linarith) (le_of_lt hδ)
      rwa [add_div, div_self (ne_of_gt hδ)] at h2
    rw [← Nat.floor_add_one (show 0 ≤ x / δ by positivity)]
    exact Nat.floor_le_floor hq
  let f : ι → ℕ := fun s => ⌊u s / δ⌋₊
  have hinj : Set.InjOn f T := by
    intro a ha b hb hab
    by_contra hne
    have hd : δ ≤ |u a - u b| := hsep a ha b hb hne
    have hne' : u a ≠ u b := by intro h; rw [h, sub_self, abs_zero] at hd; linarith
    have hab' : ⌊u a / δ⌋₊ = ⌊u b / δ⌋₊ := hab
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hz : δ ≤ u b - u a := by
        rw [abs_of_neg (by linarith)] at hd; linarith
      have := hfloor (hu0 a ha) hz
      omega
    · have hz : δ ≤ u a - u b := by
        rw [abs_of_pos (by linarith)] at hd; linarith
      have := hfloor (hu0 b hb) hz
      omega
  have himg : T.image f ⊆ Finset.range (⌊L / δ⌋₊ + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨s, hs, rfl⟩
    rw [Finset.mem_range]
    have h1 : u s / δ ≤ L / δ := div_le_div_of_nonneg_right (huL s hs) (le_of_lt hδ)
    have h2 : ⌊u s / δ⌋₊ ≤ ⌊L / δ⌋₊ := Nat.floor_le_floor h1
    change ⌊u s / δ⌋₊ < ⌊L / δ⌋₊ + 1
    omega
  calc (T.card : ℝ) = ((T.image f).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ ((Finset.range (⌊L / δ⌋₊ + 1)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card himg
    _ = ((⌊L / δ⌋₊ + 1 : ℕ) : ℝ) := by rw [Finset.card_range]
    _ ≤ L / δ + 1 := by
        have h3 : (⌊L / δ⌋₊ : ℝ) ≤ L / δ := Nat.floor_le (div_nonneg hL (le_of_lt hδ))
        push_cast; linarith

/-- Counting bound for a `δ`-separated set of frequencies: for any base point `r` and radius
`y ≥ 0`, the number of `s ∈ S` with `circDist (α r - α s) ≤ y` is at most `2y/δ + 1`. -/
theorem arc_count {ι : Type*} [DecidableEq ι] (S : Finset ι) (α : ι → ℝ) (r : ι) (δ y : ℝ)
    (hδ : 0 < δ) (hy : 0 ≤ y)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ circDist (α a - α b)) :
    ((S.filter (fun s => circDist (α r - α s) ≤ y)).card : ℝ) ≤ 2 * y / δ + 1 := by
  classical
  -- Unwrap each frequency to its nearest integer representative: `w s = ‖α r - α s‖ ∈ [-1/2,1/2]`.
  let w : ι → ℝ := fun s => (α r - α s) - (round (α r - α s) : ℝ)
  -- Shift so that the good set lives in `[0, 2y]`; this does not change the differences.
  let u : ι → ℝ := fun s => w s + y
  have hu0 : ∀ s ∈ S.filter (fun s => circDist (α r - α s) ≤ y), 0 ≤ u s := by
    intro s hs
    have hsG : circDist (α r - α s) ≤ y := (Finset.mem_filter.mp hs).2
    have hws : |w s| = circDist (α r - α s) := by
      simp only [w, circDist_eq_abs_sub_round]
    have hneg : -y ≤ w s := by
      have : |w s| ≤ y := by rw [hws]; exact hsG
      linarith [neg_abs_le (w s)]
    simp only [u]; linarith
  have huL : ∀ s ∈ S.filter (fun s => circDist (α r - α s) ≤ y), u s ≤ 2 * y := by
    intro s hs
    have hsG : circDist (α r - α s) ≤ y := (Finset.mem_filter.mp hs).2
    have hws : |w s| = circDist (α r - α s) := by
      simp only [w, circDist_eq_abs_sub_round]
    have hpos : w s ≤ y := by
      have : |w s| ≤ y := by rw [hws]; exact hsG
      linarith [le_abs_self (w s)]
    simp only [u]; linarith
  -- Separation is preserved: `δ ≤ ‖α a - α b‖ ≤ |u a - u b|` since `u a - u b ≡ α a - α b`.
  have hsepG : ∀ a ∈ S.filter (fun s => circDist (α r - α s) ≤ y),
      ∀ b ∈ S.filter (fun s => circDist (α r - α s) ≤ y), a ≠ b → δ ≤ |u a - u b| := by
    intro a ha b hb hab
    have haS : a ∈ S := (Finset.mem_filter.mp ha).1
    have hbS : b ∈ S := (Finset.mem_filter.mp hb).1
    have hbase : δ ≤ circDist (α a - α b) := hsep a haS b hbS hab
    have hkey : circDist (α a - α b) ≤ |u a - u b| := by
      have h1 : circDist (α a - α b) = |(α a - α b) - (round (α a - α b) : ℝ)| :=
        circDist_eq_abs_sub_round _
      rw [h1]
      -- `round` is a nearest integer: `circDist` is at most the distance to any integer, in
      -- particular to `round (α r - α b) - round (α r - α a)`.
      have hle := round_le (α a - α b)
        ((round (α r - α b) : ℤ) - (round (α r - α a) : ℤ))
      have hEq : (α a - α b)
          - ((((round (α r - α b) : ℤ) - (round (α r - α a) : ℤ)) : ℤ) : ℝ)
            = -(u a - u b) := by
        simp only [u, w]; push_cast; ring
      rw [hEq, abs_neg] at hle
      exact hle
    linarith
  have hmain := card_le_of_sep (S.filter (fun s => circDist (α r - α s) ≤ y)) u δ (2 * y)
    hδ (by linarith) hu0 huL hsepG
  simpa using hmain

end Work.BMF.MSD
