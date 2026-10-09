import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The three-term shoe-box principle of Schmidt–Wingberg §4 (`p = 2`)

`Work.SSGRoute.ZDataTwo.pigeonhole_three`: for any function `a : ℕ → ι` into a finite type there
are indices `i < j < N` with `a i = a j = a N`.

This is the "shoe box principle" in the form used in the `p = 2` case of the construction of the
class `z` in §4 of Schmidt–Wingberg (arXiv:math/9809211, p. 16–17): "Now choose `N` minimal, such
that `Ψ_N(z_i) = Ψ_N(z_j) = Ψ_N(z_N)` for numbers `i < j < N`", where `Ψ_n` takes its values in the
finite set `∏_{σ ≠ 1} 𝔽₂`.  (The two-term version, enough for odd `p`, is `pigeonhole_two_eq` in
`Submission/Work/SSGRoute/z_data_mup_arith.lean`.)

## Proof

The map `k ↦ (a k, decide (∃ i < k, a i = a k)) : Fin (2 · #ι + 1) → ι × Bool` lands in a finite
type of strictly smaller cardinality, so two of its values coincide.  If `i < j` are the two
indices, then `a i = a j` makes the flag of `j` true; equality of the flags therefore makes the
flag of `i` true, i.e. `a` already took the value `a i` at some `k < i`.  Then `k < i < j` are
three indices with the same value.  The case `j < i` is symmetric.
-/

namespace Work.SSGRoute.ZDataTwo

/-- **Three-term pigeonhole**: some value of `a` is taken at three distinct indices. -/
theorem pigeonhole_three {ι : Type} [Fintype ι] (a : ℕ → ι) :
    ∃ i j N : ℕ, i < j ∧ j < N ∧ a i = a j ∧ a j = a N := by
  classical
  have hcard : Fintype.card (ι × Bool) < Fintype.card (Fin (2 * Fintype.card ι + 1)) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  obtain ⟨x, y, hxy, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (2 * Fintype.card ι + 1) => (a k, decide (∃ i < (k : ℕ), a i = a k))) hcard
  have hfst : a (x : ℕ) = a (y : ℕ) := congrArg Prod.fst heq
  have hsnd : decide (∃ i < (x : ℕ), a i = a (x : ℕ)) =
      decide (∃ i < (y : ℕ), a i = a (y : ℕ)) := congrArg Prod.snd heq
  have hltval : ∀ {p q : Fin (2 * Fintype.card ι + 1)}, p < q → (p : ℕ) < (q : ℕ) :=
    fun h => h
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hfy : ∃ i < (y : ℕ), a i = a (y : ℕ) := ⟨(x : ℕ), hltval hlt, hfst⟩
    have hfx : ∃ i < (x : ℕ), a i = a (x : ℕ) := by
      have h1 : decide (∃ i < (x : ℕ), a i = a (x : ℕ)) = true := by
        rw [hsnd]; exact decide_eq_true hfy
      exact of_decide_eq_true h1
    obtain ⟨k, hkx, hkax⟩ := hfx
    exact ⟨k, (x : ℕ), (y : ℕ), hkx, hltval hlt, hkax, hfst⟩
  · have hfx : ∃ i < (x : ℕ), a i = a (x : ℕ) := ⟨(y : ℕ), hltval hgt, hfst.symm⟩
    have hfy : ∃ i < (y : ℕ), a i = a (y : ℕ) := by
      have h1 : decide (∃ i < (y : ℕ), a i = a (y : ℕ)) = true := by
        rw [← hsnd]; exact decide_eq_true hfx
      exact of_decide_eq_true h1
    obtain ⟨k, hky, hkay⟩ := hfy
    exact ⟨k, (y : ℕ), (x : ℕ), hky, hltval hgt, hkay, hfst.symm⟩

end Work.SSGRoute.ZDataTwo
