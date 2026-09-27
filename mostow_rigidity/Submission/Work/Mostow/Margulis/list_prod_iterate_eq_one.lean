import Mathlib

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Mostow.Margulis

/-- Let `σ : Q → Q` be a function whose `d`-th iterate is the identity (pointwise),
`d > 0`, and `c : Q`.  Then the product of `σ^[i] c` over `i = 0, …, d * |Q| - 1`
is trivial.

The sequence `i ↦ σ^[i] c` is `d`-periodic, so the list of length `d * |Q|` is the
period block `σ^[0] c, …, σ^[d-1] c` repeated `|Q|` times; its product is therefore the
`|Q|`-th power of that block, which is `1` by Lagrange since `|Q|` is the order of the
group.  When `Q` is infinite, `Nat.card Q = 0` and the list is empty. -/
theorem list_prod_iterate_eq_one {Q : Type*} [Group Q] (σ : Q → Q) {d : ℕ} (hd : 0 < d)
    (hper : ∀ y : Q, σ^[d] y = y) (c : Q) :
    ((List.range (d * Nat.card Q)).map (fun i => σ^[i] c)).prod = 1 := by
  -- `σ^[d*k]` is the identity, pointwise.
  have hfix' : ∀ k : ℕ, ∀ y : Q, σ^[d * k] y = y := by
    intro k
    induction k with
    | zero => intro y; rw [Nat.mul_zero, Function.iterate_zero_apply]
    | succ k ih =>
      intro y
      rw [Nat.mul_succ, Function.iterate_add_apply, hper, ih]
  -- The `d`-block starting at any multiple of `d` is the same block.
  have hblock (k : ℕ) : ((fun i => σ^[i] c) ∘ (fun x => d * k + x)) = (fun i => σ^[i] c) := by
    funext i
    simp only [Function.comp_apply]
    rw [Function.iterate_add_apply, hfix' k]
  -- The product over `d * m` terms is the `m`-th power of the period block.
  have hmain : ∀ m : ℕ, ((List.range (d * m)).map (fun i => σ^[i] c)).prod =
      ((List.range d).map (fun i => σ^[i] c)).prod ^ m := by
    intro m
    induction m with
    | zero => rw [Nat.mul_zero, List.range_zero, List.map_nil, List.prod_nil, pow_zero]
    | succ m ih =>
      rw [Nat.mul_succ, List.range_add, List.map_append, List.prod_append, ih, List.map_map,
        hblock m, pow_succ]
  rw [hmain (Nat.card Q)]
  by_cases hfin : Finite Q
  · -- finite case: the period block has order dividing `|Q|`, so its `|Q|`-th power is `1`
    haveI hF : Finite Q := hfin
    haveI : Fintype Q := Fintype.ofFinite Q
    rw [Nat.card_eq_fintype_card]
    exact pow_card_eq_one
  · -- infinite case: `Nat.card Q = 0`, the list is empty
    haveI : Infinite Q := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite, pow_zero]

end Work.Mostow.Margulis
