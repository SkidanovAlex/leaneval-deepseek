import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Cardinality bound for an `(X, L)`-family

An `(X, L)`-family of left endpoints (`IsFam X L S`) consists of points `x ∈ S` with
`X/10 ≤ x`, `x + L ≤ 10 X`, pairwise at distance at least `500 L`.  All points therefore lie
in the interval `[X/10, 10X]` and are `500L`-separated, so their count is at most
`(10X - X/10)/(500L) + 1`.  Since `10X - X/10 = 99X/10 < 100X/10`, this is
`≤ 10 X / (500 L) + 1`.

The counting is done with the injection `x ↦ ⌊(x - a)/d⌋₊` into `ℕ`, which is injective on any
`d`-separated set of `[a, b]` and takes values in `[0, ⌊(b-a)/d⌋₊]`.
-/

open Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

namespace Work.BMF

/-- If `u, v ≥ 0` and `|u - v| ≥ 1` then `⌊u⌋₊ ≠ ⌊v⌋₊`: two naturals differing by at least one
cannot have the same (natural) floor. -/
theorem floor_ne_of_abs_sub_ge_one {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : 1 ≤ |u - v|) :
    ⌊u⌋₊ ≠ ⌊v⌋₊ := by
  intro hEq
  have h3 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu
  have h4 : (⌊v⌋₊ : ℝ) ≤ v := Nat.floor_le hv
  have hu' : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
  have hv' : v < (⌊v⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one v
  have hlt1 : u - v < 1 := by rw [hEq] at hu'; linarith only [hu', h4]
  have hlt2 : v - u < 1 := by rw [hEq] at h3; linarith only [hv', h3]
  have habs : |u - v| < 1 := by
    rw [abs_sub_lt_iff]; exact ⟨hlt1, hlt2⟩
  linarith only [h, habs]

/-- Cardinality bound for a `d`-separated finite set of reals contained in `[a, b]`:
`#S ≤ (b - a)/d + 1`. -/
theorem card_le_of_sep {S : Finset ℝ} {a b d : ℝ} (hab : a ≤ b) (hd : 0 < d)
    (ha : ∀ x ∈ S, a ≤ x) (hb : ∀ x ∈ S, x ≤ b)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|) :
    (S.card : ℝ) ≤ (b - a) / d + 1 := by
  have hd0 : 0 ≤ d := le_of_lt hd
  have hinj : Set.InjOn (fun x : ℝ => ⌊(x - a) / d⌋₊) (S : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    refine floor_ne_of_abs_sub_ge_one (u := (x - a) / d) (v := (y - a) / d) ?_ ?_ ?_ hxy
    · exact div_nonneg (sub_nonneg.mpr (ha x hx)) hd0
    · exact div_nonneg (sub_nonneg.mpr (ha y hy)) hd0
    · have hkey : (x - a) / d - (y - a) / d = (x - y) / d := by ring
      rw [hkey, abs_div, abs_of_pos hd]
      rw [le_div_iff₀ hd]
      simpa using hsep x hx y hy hne
  have hsub : S.image (fun x : ℝ => ⌊(x - a) / d⌋₊) ⊆ Finset.Icc 0 ⌊(b - a) / d⌋₊ := by
    intro n hn
    simp only [Finset.mem_image] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    simp only [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Nat.floor_le_floor (by
      apply div_le_div_of_nonneg_right _ hd0
      linarith [hb x hx])⟩
  have hcard : (S.card : ℝ) ≤ (⌊(b - a) / d⌋₊ : ℝ) + 1 := by
    have h1 : (S.image (fun x : ℝ => ⌊(x - a) / d⌋₊)).card = S.card :=
      Finset.card_image_of_injOn hinj
    have h2 : (S.image (fun x : ℝ => ⌊(x - a) / d⌋₊)).card ≤ ⌊(b - a) / d⌋₊ + 1 := by
      calc (S.image (fun x : ℝ => ⌊(x - a) / d⌋₊)).card
          ≤ (Finset.Icc 0 ⌊(b - a) / d⌋₊).card := Finset.card_le_card hsub
        _ = ⌊(b - a) / d⌋₊ + 1 := by rw [Nat.card_Icc]; simp
    rw [h1] at h2
    exact_mod_cast h2
  have hNle : (⌊(b - a) / d⌋₊ : ℝ) ≤ (b - a) / d :=
    Nat.floor_le (div_nonneg (sub_nonneg.mpr hab) hd0)
  linarith

theorem fam_card_le (X L : ℝ) (hX : 0 < X) (hL : 0 < L) (S : Finset ℝ) (hS : IsFam X L S) :
    (S.card : ℝ) ≤ 10 * X / (500 * L) + 1 := by
  unfold IsFam at hS
  obtain ⟨hbound, hsep⟩ := hS
  have hmain : (S.card : ℝ) ≤ (10 * X - X / 10) / (500 * L) + 1 :=
    card_le_of_sep (S := S) (a := X / 10) (b := 10 * X) (d := 500 * L)
      (by linarith) (by linarith)
      (fun x hx => (hbound x hx).1)
      (fun x hx => by have := (hbound x hx).2; linarith)
      (fun x hx y hy hne => hsep x hx y hy hne)
  have hle : (10 * X - X / 10) / (500 * L) ≤ 10 * X / (500 * L) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    linarith
  linarith

end Work.BMF
