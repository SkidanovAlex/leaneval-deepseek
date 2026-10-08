import Mathlib
import Submission.Work.BG.c4TripleAux

/-!
# Area BG: four `±Irr` characters split off three mutually orthogonal norm-`4` combinations

Let `a, b, c, d` be signed irreducible characters of a finite group `K` and let

`D₁ = a + b + c + d`, `D₂ = a - b + c - d`, `D₃ = a + b - c - d`

be the first three (Hadamard) combinations.  If the three `Dᵢ` have squared norm `4` and are
pairwise orthogonal, then `a, b, c, d` are pairwise orthogonal.

The mechanism is entirely elementary.  Grouping the `Dᵢ`:

`D₁ + D₂ = (a+c) + (a+c)`, `D₁ + D₃ = (a+b) + (a+b)`, `D₂ + D₃ = (a-d) + (a-d)`,
`D₁ - D₂ = (b+d) + (b+d)`, `D₁ - D₃ = (c+d) + (c+d)`, `D₂ - D₃ = (c-b) + (c-b)`.

Each of these has squared norm `8` (bilinearity plus the hypotheses), hence `‖x ± y‖² = 2`
for the corresponding pair, and since `‖x‖² = ‖y‖² = 1` this says
`⟨x, y⟩ + star ⟨x, y⟩ = 0`, i.e. `Re ⟨x, y⟩ = 0`.  As `x` and `y` are signed irreducibles,
`⟨x, y⟩` is a real integer (`0`, `1` or `-1`, by `pmIrr_inner_eq_zero_or_one_or_neg_one`),
so the vanishing of its real part forces `⟨x, y⟩ = 0`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- The negative of a signed irreducible character is again a signed irreducible. -/
private theorem isPmIrr_neg' {K : Type} [Group K] {φ : ClassFunction K ℂ} (h : IsPmIrr φ) :
    IsPmIrr (-φ) := by
  rcases h with h | h
  · exact Or.inr (by rw [neg_neg]; exact h)
  · exact Or.inl h

/-- For signed irreducibles `x`, `y`, `‖x + y‖² = 2` forces `⟨x, y⟩ = 0`.

Indeed `‖x + y‖² = ‖x‖² + ‖y‖² + (⟨x, y⟩ + star ⟨x, y⟩) = 2 + (⟨x, y⟩ + star ⟨x, y⟩)`,
so the hypothesis says `⟨x, y⟩ + star ⟨x, y⟩ = 0`; with `⟨x, y⟩ ∈ {0, ±1}` this gives `0`. -/
private theorem pmIrr_inner_zero_of_add_norm_two {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {x y : ClassFunction K ℂ} (hx : IsPmIrr x) (hy : IsPmIrr y)
    (h : ClassFunction.inner (x + y) (x + y) = 2) : ClassFunction.inner x y = 0 := by
  refine pmIrr_inner_eq_zero_of_add_star_eq_zero hx hy ?_
  have hexp : ClassFunction.inner (x + y) (x + y)
      = ClassFunction.inner x x + ClassFunction.inner x y + ClassFunction.inner y x
        + ClassFunction.inner y y := by
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right]
    ring
  rw [hexp, IsPmIrr.inner_self hx, IsPmIrr.inner_self hy,
    ClassFunction.inner_star_comm y x] at h
  linear_combination h

/-- For signed irreducibles `x`, `y`, `‖x - y‖² = 2` forces `⟨x, y⟩ = 0`.

Reduced to the `x + y` case by replacing `y` with `-y`. -/
private theorem pmIrr_inner_zero_of_sub_norm_two {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {x y : ClassFunction K ℂ} (hx : IsPmIrr x) (hy : IsPmIrr y)
    (h : ClassFunction.inner (x - y) (x - y) = 2) : ClassFunction.inner x y = 0 := by
  rw [sub_eq_add_neg] at h
  have h' := pmIrr_inner_zero_of_add_norm_two hx (isPmIrr_neg' hy) h
  rw [ClassFunction.inner_neg_right] at h'
  exact neg_eq_zero.mp h'

/-- `‖u + u‖² = 8` gives `‖u‖² = 2` (over `ℂ`, where `4 ≠ 0`). -/
private theorem norm_two_of_norm_eight {K : Type} [Group K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] {u : ClassFunction K ℂ}
    (h : ClassFunction.inner (u + u) (u + u) = 8) : ClassFunction.inner u u = 2 := by
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right] at h
  linear_combination (1 / 4 : ℂ) * h

open OddOrder.RepresentationTheory Work.BG in
theorem c4FourOrthogonal {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)]
    {a b c d : ClassFunction K ℂ} (D1 D2 D3 : ClassFunction K ℂ)
    (ha : Work.BG.IsPmIrr a) (hb : Work.BG.IsPmIrr b) (hc : Work.BG.IsPmIrr c)
    (hd : Work.BG.IsPmIrr d)
    (h1 : D1 = a + b + c + d) (h2 : D2 = a - b + c - d) (h3 : D3 = a + b - c - d)
    (g11 : ClassFunction.inner D1 D1 = 4) (g22 : ClassFunction.inner D2 D2 = 4)
    (g33 : ClassFunction.inner D3 D3 = 4)
    (g12 : ClassFunction.inner D1 D2 = 0) (g13 : ClassFunction.inner D1 D3 = 0)
    (g23 : ClassFunction.inner D2 D3 = 0) :
    ClassFunction.inner a b = 0 ∧ ClassFunction.inner a c = 0 ∧ ClassFunction.inner a d = 0 ∧
      ClassFunction.inner b c = 0 ∧ ClassFunction.inner b d = 0 ∧ ClassFunction.inner c d = 0 := by
  -- the adjoint cross terms are also zero
  have hD2D1 : ClassFunction.inner D2 D1 = 0 := by
    rw [ClassFunction.inner_star_comm, g12, star_zero]
  have hD3D1 : ClassFunction.inner D3 D1 = 0 := by
    rw [ClassFunction.inner_star_comm, g13, star_zero]
  have hD3D2 : ClassFunction.inner D3 D2 = 0 := by
    rw [ClassFunction.inner_star_comm, g23, star_zero]
  -- squared norms of the six signed combinations of two of the `Dᵢ`
  have nP12 : ClassFunction.inner (D1 + D2) (D1 + D2) = 8 := by
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right]
    rw [g11, g12, hD2D1, g22]; norm_num
  have nP13 : ClassFunction.inner (D1 + D3) (D1 + D3) = 8 := by
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right]
    rw [g11, g13, hD3D1, g33]; norm_num
  have nP23 : ClassFunction.inner (D2 + D3) (D2 + D3) = 8 := by
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right]
    rw [g22, g23, hD3D2, g33]; norm_num
  have nM12 : ClassFunction.inner (D1 - D2) (D1 - D2) = 8 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right]
    rw [g11, hD2D1, g12, g22]; norm_num
  have nM13 : ClassFunction.inner (D1 - D3) (D1 - D3) = 8 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right]
    rw [g11, hD3D1, g13, g33]; norm_num
  have nM23 : ClassFunction.inner (D2 - D3) (D2 - D3) = 8 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right]
    rw [g22, hD3D2, g23, g33]; norm_num
  -- the six regroupings `Dᵢ ± Dⱼ = u + u`
  have eP12 : D1 + D2 = (a + c) + (a + c) := by
    rw [h1, h2]
    ext x
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply]
    ring
  have eP13 : D1 + D3 = (a + b) + (a + b) := by
    rw [h1, h3]
    ext x
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply]
    ring
  have eP23 : D2 + D3 = (a - d) + (a - d) := by
    rw [h2, h3]
    ext x
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply]
    ring
  have eM12 : D1 - D2 = (b + d) + (b + d) := by
    rw [h1, h2]
    ext x
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply]
    ring
  have eM13 : D1 - D3 = (c + d) + (c + d) := by
    rw [h1, h3]
    ext x
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply]
    ring
  have eM23 : D2 - D3 = (c - b) + (c - b) := by
    rw [h2, h3]
    ext x
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply]
    ring
  have hab : ClassFunction.inner a b = 0 := by
    have h := nP13
    rw [eP13] at h
    exact pmIrr_inner_zero_of_add_norm_two ha hb (norm_two_of_norm_eight h)
  have hac : ClassFunction.inner a c = 0 := by
    have h := nP12
    rw [eP12] at h
    exact pmIrr_inner_zero_of_add_norm_two ha hc (norm_two_of_norm_eight h)
  have had : ClassFunction.inner a d = 0 := by
    have h := nP23
    rw [eP23] at h
    exact pmIrr_inner_zero_of_sub_norm_two ha hd (norm_two_of_norm_eight h)
  have hbd : ClassFunction.inner b d = 0 := by
    have h := nM12
    rw [eM12] at h
    exact pmIrr_inner_zero_of_add_norm_two hb hd (norm_two_of_norm_eight h)
  have hcd : ClassFunction.inner c d = 0 := by
    have h := nM13
    rw [eM13] at h
    exact pmIrr_inner_zero_of_add_norm_two hc hd (norm_two_of_norm_eight h)
  have hbc : ClassFunction.inner b c = 0 := by
    have h := nM23
    rw [eM23] at h
    have hcb := pmIrr_inner_zero_of_sub_norm_two hc hb (norm_two_of_norm_eight h)
    rw [ClassFunction.inner_star_comm b c, hcb, star_zero]
  exact ⟨hab, hac, had, hbc, hbd, hcd⟩

end Work.BG
