import Mathlib
import Submission.Work.MotV.TpAux
import Submission.Work.MotV.tp_ident

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Route V, node TP: strict dominance of the square monomial

`Work.MotV.tp_cmp` is the comparison step of the proof of `Work.MotV.tp`: if the weight
`wt v h y i = (v h)^i * (v (y i))^5` attains its maximum at `j`, the maximum is positive, and the
successor of every maximiser is not a maximiser (`hstep`), then the square monomial `y_j * y_j` of
the quadric with `2 * k = j` strictly dominates the other two monomials `y_{j+2} * y_{j+3}` and
`y_{j+1} * y_{j+4}` of that quadric.

The proof reduces, through the fifth-power monomial identities `tp_ident`, to the two weight
inequalities `M (j+1) * M (j+4) < M j * M j` and `M (j+2) * M (j+3) < M j * M j` with
`M i = wt v h y i`: `hstep` at `j` makes `M (j+1) < M j`, and `hstep` at `j+2` shows that
`M (j+2)` and `M (j+3)` cannot both equal `M j`.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

noncomputable section

/-- **Strict dominance of the square monomial.**  Under the standing hypotheses of node TP
(`v h ≠ 0`, `wt` maximised and positive at `j`, and no two cyclically consecutive maximisers),
the two non-square monomials of the quadric with square monomial `y_j ^ 2` have strictly smaller
valuation than the square. -/
theorem tp_cmp {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation F Γ₀) {h : F} (hv : v h ≠ 0) (y : Fin 5 → F) {j : Fin 5}
    (hm : 0 < wt v h y j) (hjmax : ∀ i, wt v h y i ≤ wt v h y j)
    (hstep : ∀ i, wt v h y i = wt v h y j → wt v h y (i + 1) ≠ wt v h y j) :
    v (twMon h y (j + 2) (j + 3)) < v (twMon h y j j) ∧
      v (twMon h y (j + 1) (j + 4)) < v (twMon h y j j) := by
  -- `hstep` at `j` forces the successor weight to be strictly smaller.
  have hlt1 : wt v h y (j + 1) < wt v h y j :=
    lt_of_le_of_ne (hjmax (j + 1)) (hstep j rfl)
  -- hence the product of the `(j+1, j+4)` pair is strictly below the square.
  have hP3 : wt v h y (j + 1) * wt v h y (j + 4) < wt v h y j * wt v h y j :=
    mul_lt_mul_self hm (hjmax (j + 1)) (hjmax (j + 4)) (Or.inl hlt1)
  -- for the `(j+2, j+3)` pair: they cannot both be maximisers.
  have hP2 : wt v h y (j + 2) * wt v h y (j + 3) < wt v h y j * wt v h y j := by
    rcases lt_or_eq_of_le (hjmax (j + 2)) with h2 | h2
    · exact mul_lt_mul_self hm h2.le (hjmax (j + 3)) (Or.inl h2)
    · have hfin : (j + 2) + 1 = j + 3 := by fin_cases j <;> rfl
      have hne : wt v h y (j + 3) ≠ wt v h y j := by
        have hh := hstep (j + 2) h2
        rwa [hfin] at hh
      have h3 : wt v h y (j + 3) < wt v h y j := lt_of_le_of_ne (hjmax (j + 3)) hne
      calc wt v h y (j + 2) * wt v h y (j + 3) = wt v h y j * wt v h y (j + 3) := by rw [h2]
        _ < wt v h y j * wt v h y j := mul_lt_mul_of_pos_left h3 hm
  -- the fifth-power identities turn the weight comparisons into valuation comparisons
  obtain ⟨hid1, hid2, hid3⟩ := tp_ident v h y j
  exact ⟨(pow5_mul_lt_iff hv (rr j)).mp (by rw [hid2, hid1]; exact hP2),
    (pow5_mul_lt_iff hv (rr j)).mp (by rw [hid3, hid1]; exact hP3)⟩

end

end Work.MotV
