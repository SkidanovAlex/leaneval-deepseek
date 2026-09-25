import Mathlib
import Submission.Work.LT.lr_local_defs

/-!
# Layer-constant value of `M₀` along the `B`-direction

For a function `k` on the vertex set which is *constant on the `G`-coordinate*, i.e.
`k (α,β,g) = c α β`, every B-neighbour of a vertex `(a,b,g)` lies in the layer
`(a, b+1, ·)` and the coefficient `c (nB B (a,b,g) j).1 (nB B (a,b,g) j).2.1` equals
`c a (b+1)`, *independently of `j`*.  Hence the inner sum over `j : Fin Δ` contributes a
factor `Δ`, and each of the four layers `(a,b)` contributes `|G|` vertices:

`∑_v c v.1 v.2.1 * ∑_j c (nB v j).1 (nB v j).2.1
   = |G| · Δ · ∑_{a,b} c a b · c a (b+1)`
`   = 2 · |G| · Δ · (c 0 0 * c 0 1 + c 1 0 * c 1 1)`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.LT

open scoped BigOperators

theorem lr_M0_layerConst_B {G : Type} [Group G] [Fintype G] {Δ : ℕ} (B : Fin Δ → G)
    (c : Fin 2 → Fin 2 → ℝ) :
    (∑ v : Vtx G, c v.1 v.2.1 * (∑ j : Fin Δ, c (nB B v j).1 (nB B v j).2.1))
      = 2 * (Fintype.card G : ℝ) * (Δ : ℝ) * (c 0 0 * c 0 1 + c 1 0 * c 1 1) := by
  -- A `B`-step out of layer `(a,b)` lands in layer `(a, b+1)` whatever the direction `j` is,
  -- so the inner sum is `Δ` copies of a fixed value.
  have hstep : ∀ (a b : Fin 2) (g : G),
      (∑ j : Fin Δ, c (nB B (a, b, g) j).1 (nB B (a, b, g) j).2.1)
        = (Δ : ℝ) * c a (b + 1) := by
    intro a b g
    have hconst : ∀ j : Fin Δ,
        c (nB B (a, b, g) j).1 (nB B (a, b, g) j).2.1 = c a (b + 1) := by
      intro j
      fin_cases b <;> simp [nB]
    rw [Finset.sum_congr rfl (fun j _ => hconst j)]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Fibre the vertex sum over the two `Fin 2` coordinates and the group coordinate.
  rw [show (∑ v : Vtx G,
        c v.1 v.2.1 * (∑ j : Fin Δ, c (nB B v j).1 (nB B v j).2.1))
      = ∑ a : Fin 2, ∑ b : Fin 2, ∑ g : G,
          c a b * (∑ j : Fin Δ, c (nB B (a, b, g) j).1 (nB B (a, b, g) j).2.1) from by
        simp [Vtx, Fintype.sum_prod_type]]
  simp only [hstep]
  -- The summand no longer depends on `g`, contributing `|G|`.
  simp_rw [← Finset.mul_sum]
  -- The remaining sum over `Fin 2 × Fin 2` is a four-term explicit sum.
  simp [Fin.sum_univ_two]
  ring

end Work.LT
