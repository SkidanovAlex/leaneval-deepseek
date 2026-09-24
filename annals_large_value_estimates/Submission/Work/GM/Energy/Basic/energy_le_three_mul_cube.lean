import Mathlib
import Submission.Work.GM.Energy.Defs

namespace Work.GM.Energy.Basic

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- Two reals with equal integer parts are at distance strictly less than one. -/
private lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  rw [abs_lt]
  constructor
  · have hle : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have hlt : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    rw [← h] at hlt
    linarith
  · have hle : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have hlt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    rw [h] at hlt
    linarith

/-- A `1`-separated finite set of reals inside the interval `[0,2]` has at most `3` elements:
the floors `⌊x⌋` are pairwise distinct integers lying in `{0,1,2}`. -/
private lemma card_le_three_of_sep {A : Finset ℝ} (hA : ∀ x ∈ A, 0 ≤ x ∧ x ≤ 2)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ |x - y|) : A.card ≤ 3 := by
  classical
  have hinj : Set.InjOn (fun x : ℝ => (⌊x⌋ : ℤ)) (A : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hsep' : 1 ≤ |x - y| := hsep x hx y hy hne
    have hlt : |x - y| < 1 := abs_sub_lt_one_of_floor_eq hxy
    linarith
  have hcard : A.card = (A.image (fun x => (⌊x⌋ : ℤ))).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsub : A.image (fun x => (⌊x⌋ : ℤ)) ⊆ Finset.Icc (0:ℤ) 2 := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    simp only [Finset.mem_Icc]
    constructor
    · exact Int.floor_nonneg.mpr (hA x hx).1
    · have h3 : x < ((3:ℤ) : ℝ) := by
        push_cast
        linarith [(hA x hx).2]
      have := (Int.floor_lt).mpr h3
      omega
  calc A.card = (A.image (fun x => (⌊x⌋ : ℤ))).card := hcard
    _ ≤ (Finset.Icc (0:ℤ) 2).card := Finset.card_le_card hsub
    _ = 3 := by decide

/-- For a `1`-separated `W` and any real `c`, at most `3` elements of `W` lie in `[c-1,c+1]`. -/
private lemma card_filter_le_three {W : Finset ℝ} (hsep : Submission.GM.Separated W 1)
    (c : ℝ) : (W.filter (fun t => |c - t| ≤ 1)).card ≤ 3 := by
  classical
  set S : Finset ℝ := W.filter (fun t => |c - t| ≤ 1) with hSdef
  have hsub : S ⊆ W := by rw [hSdef]; exact Finset.filter_subset _ _
  have hsepS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y| := by
    intro x hx y hy hxy
    exact hsep x (hsub hx) y (hsub hy) hxy
  have hshift_inj : ∀ x ∈ S, ∀ y ∈ S, x - (c - 1) = y - (c - 1) → x = y := by
    intro x _ y _ h; linarith
  have hcardimg : (S.image (fun t => t - (c-1))).card = S.card :=
    Finset.card_image_of_injOn hshift_inj
  have hA : ∀ x ∈ S.image (fun t => t - (c-1)), 0 ≤ x ∧ x ≤ 2 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    have ht' : t ∈ W ∧ |c - t| ≤ 1 := by rw [hSdef, Finset.mem_filter] at ht; exact ht
    have h := ht'.2
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have hsepS' : ∀ x ∈ S.image (fun t => t - (c-1)), ∀ y ∈ S.image (fun t => t - (c-1)),
      x ≠ y → 1 ≤ |x - y| := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have hab : a ≠ b := by intro h; exact hxy (by rw [h])
    have heq : (a - (c-1)) - (b - (c-1)) = a - b := by ring
    rw [heq]
    exact hsepS a ha b hb hab
  have hthis : (S.image (fun t => t - (c-1))).card ≤ 3 := card_le_three_of_sep hA hsepS'
  rw [hcardimg] at hthis
  exact hthis

/-- Membership in a `4`-fold product gives membership of all four coordinates. -/
private lemma proj_mem {W : Finset ℝ} {a : ℝ × ℝ × ℝ × ℝ}
    (ha : a ∈ W ×ˢ W ×ˢ W ×ˢ W) :
    a.1 ∈ W ∧ a.2.1 ∈ W ∧ a.2.2.1 ∈ W ∧ a.2.2.2 ∈ W := by
  rw [Finset.mem_product] at ha
  obtain ⟨h1, h2⟩ := ha
  rw [Finset.mem_product] at h2
  obtain ⟨h21, h22⟩ := h2
  rw [Finset.mem_product] at h22
  exact ⟨h1, h21, h22.1, h22.2⟩

/-- A `1`-separated finite set of reals has energy at most `3 |W|³`: for each triple
`(t₁,t₂,t₃) ∈ W³` there are at most three `t₄ ∈ W` with `|t₁+t₂-t₃-t₄| ≤ 1`, since such `t₄`
lie in an interval of length `2` and are `1`-separated. -/
theorem energy_le_three_mul_cube {W : Finset ℝ} (hsep : Submission.GM.Separated W 1) :
    (Submission.GM.energy W : ℝ) ≤ 3 * (W.card : ℝ) ^ 3 := by
  classical
  set s : Finset (ℝ × ℝ × ℝ × ℝ) :=
    (W ×ˢ W ×ˢ W ×ˢ W).filter
      (fun q : ℝ × ℝ × ℝ × ℝ => |q.1 + q.2.1 - q.2.2.1 - q.2.2.2| ≤ 1) with hsdef
  have henergy : Submission.GM.energy W = s.card := by
    unfold Submission.GM.energy
    rw [hsdef]
  let f : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun q => (q.1, q.2.1, q.2.2.1)
  have hmem : ∀ a : ℝ × ℝ × ℝ × ℝ, a ∈ s ↔
      a ∈ W ×ˢ W ×ˢ W ×ˢ W ∧ |a.1 + a.2.1 - a.2.2.1 - a.2.2.2| ≤ 1 := by
    intro a
    rw [hsdef, Finset.mem_filter]
  -- each fibre of the projection onto the first three coordinates has at most `3` elements
  have hfiber : ∀ b ∈ s.image f, (s.filter (fun a => f a = b)).card ≤ 3 := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨q0, hq0, hq0eq⟩
    have hb1 : b.1 = q0.1 := by rw [← hq0eq]
    have hb2 : b.2.1 = q0.2.1 := by rw [← hq0eq]
    have hb3 : b.2.2 = q0.2.2.1 := by rw [← hq0eq]
    set S : Finset ℝ := W.filter (fun t => |(b.1 + b.2.1 - b.2.2) - t| ≤ 1) with hSdef
    have hS3 : S.card ≤ 3 := card_filter_le_three hsep _
    have hmaps : Set.MapsTo (fun a : ℝ × ℝ × ℝ × ℝ => a.2.2.2)
        (↑(s.filter (fun a => f a = b))) (↑S) := by
      intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha
      obtain ⟨has, hfa⟩ := ha
      have haW : a ∈ W ×ˢ W ×ˢ W ×ˢ W := ((hmem a).mp has).1
      have haP : |a.1 + a.2.1 - a.2.2.1 - a.2.2.2| ≤ 1 := ((hmem a).mp has).2
      have ha4 : a.2.2.2 ∈ W := (proj_mem haW).2.2.2
      have e1 : a.1 = b.1 := congrArg (fun p : ℝ × ℝ × ℝ => p.1) hfa
      have e2 : a.2.1 = b.2.1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hfa
      have e3 : a.2.2.1 = b.2.2 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hfa
      rw [Finset.mem_coe, hSdef, Finset.mem_filter]
      refine ⟨ha4, ?_⟩
      rw [e1, e2, e3] at haP
      exact haP
    have hinj : Set.InjOn (fun a : ℝ × ℝ × ℝ × ℝ => a.2.2.2)
        (↑(s.filter (fun a => f a = b))) := by
      intro a ha a' ha' h
      rw [Finset.mem_coe, Finset.mem_filter] at ha ha'
      obtain ⟨_, hfa⟩ := ha
      obtain ⟨_, hfa'⟩ := ha'
      have hfaa' : f a = f a' := by rw [hfa, hfa']
      have e1 : a.1 = a'.1 := congrArg (fun p : ℝ × ℝ × ℝ => p.1) hfaa'
      have e2 : a.2.1 = a'.2.1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hfaa'
      have e3 : a.2.2.1 = a'.2.2.1 := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hfaa'
      exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 h))
    have := Finset.card_le_card_of_injOn (fun a : ℝ × ℝ × ℝ × ℝ => a.2.2.2) hmaps hinj
    linarith
  have h1 : s.card ≤ 3 * (s.image f).card := Finset.card_le_mul_card_image (f := f) s 3 hfiber
  -- the image lies in the triple product `W × W × W`
  have h2 : (s.image f).card ≤ W.card ^ 3 := by
    have hsub : s.image f ⊆ W ×ˢ W ×ˢ W := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨a, ha, hfap⟩
      rw [← hfap]
      have haW : a ∈ W ×ˢ W ×ˢ W ×ˢ W := ((hmem a).mp ha).1
      obtain ⟨h1, h2, h3, -⟩ := proj_mem haW
      rw [Finset.mem_product]
      exact ⟨h1, by rw [Finset.mem_product]; exact ⟨h2, h3⟩⟩
    calc (s.image f).card ≤ (W ×ˢ W ×ˢ W).card := Finset.card_le_card hsub
      _ = W.card ^ 3 := by rw [Finset.card_product, Finset.card_product]; ring
  have hnat : s.card ≤ 3 * W.card ^ 3 :=
    calc s.card ≤ 3 * (s.image f).card := h1
      _ ≤ 3 * W.card ^ 3 := Nat.mul_le_mul_left 3 h2
  rw [henergy]
  have hcast : ((3 * W.card ^ 3 : ℕ) : ℝ) = 3 * (W.card : ℝ)^3 := by push_cast; ring
  have hle : (s.card : ℝ) ≤ ((3 * W.card^3 : ℕ) : ℝ) := by exact_mod_cast hnat
  linarith [hcast]

end Work.GM.Energy.Basic
