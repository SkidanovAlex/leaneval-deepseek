import Mathlib.NumberTheory.LegendreSymbol.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- For a prime `p ≡ 3 (mod 4)`, the equation `α ^ 2 = -1` has no solution
in `ZMod (p ^ e)` for any `e ≥ 1`.

Indeed `-1` is not a square modulo `p` (see
`ZMod.mod_four_ne_three_of_sq_eq_neg_one`), and a root modulo `p ^ e`
reduces, along the canonical homomorphism `ZMod (p ^ e) → ZMod p` (which
exists because `p ∣ p ^ e`), to a root modulo `p`.  Hence the solution set is
empty and its cardinality is `0`. -/
lemma sq_roots_neg_one_mod_prime_pow_eq_zero {p e : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (he : 1 ≤ e) : ({α : ZMod (p ^ e) | α ^ 2 = -1}.ncard) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p ∣ p ^ e` since `e ≥ 1`, giving the reduction homomorphism
  have hpdvd : p ∣ p ^ e := dvd_pow_self p (by omega : e ≠ 0)
  let f : ZMod (p ^ e) →+* ZMod p := ZMod.castHom hpdvd (ZMod p)
  -- the solution set modulo `p ^ e` is empty
  have h_empty : {α : ZMod (p ^ e) | α ^ 2 = -1} = (∅ : Set (ZMod (p ^ e))) := by
    ext α
    constructor
    · intro hα
      -- reduce a solution modulo `p ^ e` to a solution modulo `p`
      have hf : (f α) ^ 2 = -1 := by
        calc
          (f α) ^ 2 = f (α ^ 2) := by rw [map_pow]
          _ = f (-1) := by rw [hα]
          _ = -1 := by simp
      -- but `-1` is not a square modulo a prime `p ≡ 3 (mod 4)`
      exact (ZMod.mod_four_ne_three_of_sq_eq_neg_one hf) hp4
    · intro hmem
      exact False.elim hmem
  rw [h_empty]
  simp

end Commons.NumberTheory.FriedlanderIwaniec
