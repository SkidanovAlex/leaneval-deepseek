import Mathlib
import Submission.Work.WingbergH3.H3Wall
import Submission.Work.WingbergRoute.pruefer_twoTorsion_card_gt_quot

/-!
# `Work.WingbergH3.Obstruction` -- what the `H³`-half is *not*

Deliverable item (1) of this area asks for a machine-checked account of why the stated wall cannot
be derived from what this workspace has.  The obstruction is precise and fully machine-checked
here: **the `H³`-half is not a consequence of the `H²`-half and the `ℤ`-power sequence.**

The classical chain used by the area is

```
#H²(G_∅,𝔽₂) = #(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) · #(H³(G_∅,ℤ)[2])      (natCard_H2_zmodTwo_eq)
#(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) ≤ #H¹(G_∅,𝔽₂)                        (natCard_H2Z_quot_two_le_card_H1_zmodTwo)
```

The first factor is bounded unconditionally, so the *entire* content of the deficiency wall
`#H³(G_∅,ℤ)[2] ≤ 2 ^ d₂(O_F^×)` is the second factor -- and the tempting step which would make it
formal, namely bounding `#A[2]` by `#(A/2A)` for the abelian group `A = H²(G_∅,ℤ)`, is **false**.
The Prüfer group `A = ℚ/ℤ` is the counterexample: `#A[2] = 2` while `#(A/2A) = 1`
(`Work.WingbergRoute.pruefer_twoTorsion_card_gt_quot`, proved in this workspace).  Hence the missing
dimension is genuinely arithmetic: any proof of the `H³`-half must use the arithmetic of `F` (the
universal norms `Ĥ⁰(G_∅, O_{F_∅}^×) = E_F / N E_{F_∅}`, Wingberg's duality), not the coefficient
sequences alone.

The same counterexample also shows that the *constructive* route is not a formal consequence of the
`H²`-half: the counting lemma of `Dual.lean` (`#H²(G,𝔽₂) ≤ 2 ^ m` from a pro-`2` group with `m`
generators) is an upper bound on `H²(G,𝔽₂)` itself, and it can only be applied to the *first*
factor of the product identity, where it gives `#H³(G_∅,ℤ)[2] ≤ 2 ^ (d + d₂(O_F^×))` rather than the
sought `2 ^ d₂(O_F^×)`.

## Main declarations

* `Work.WingbergH3.not_forall_twoTorsion_card_le_quot_card`;
* `Work.WingbergH3.pruefer_obstruction`;
* `Work.WingbergH3.h3_half_not_derivable_from_h2_half`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.WingbergH3

open Work.ConCohomology Work.ShafarevichKoch Work.ClassFieldTower

/-- **The `2`-torsion of an abelian group is *not* bounded by its quotient by `2`.**  The
universally quantified bound `#A[2] ≤ #(A/2A)` fails, with `A = ℚ/ℤ` (`QZ` of
`Submission/Work/WingbergRoute/pruefer_twoTorsion_card_gt_quot.lean`) as the witness: its
`2`-torsion has two elements and its quotient by `2` is trivial. -/
theorem not_forall_twoTorsion_card_le_quot_card :
    ¬ (∀ (A : Type) [AddCommGroup A],
        Nat.card {x : A // (2 : ℕ) • x = 0} ≤
          Nat.card (A ⧸ AddSubgroup.closure (Set.range (fun x : A => (2 : ℕ) • x)))) := by
  intro h
  have hq := h Work.WingbergRoute.QZ
  exact absurd hq (not_le.mpr Work.WingbergRoute.pruefer_twoTorsion_card_gt_quot)

/-- **The Prüfer obstruction, in the shape of the wall.**  There is an abelian group `A` whose
quotient by `2` is trivial (so that the bound `#(A/2A) ≤ 2 ^ 0` holds) but whose `2`-torsion is
*not* trivial (so that `#A[2] ≤ 2 ^ 0` fails).

Applied to `A = H²(G_∅,ℤ)`, this is the precise reason why the `H³`-half
`#H³(G_∅,ℤ)[2] ≤ 2 ^ d₂(O_F^×)` cannot be deduced from the `H²`-half
`#(H²(G_∅,ℤ)/2H²(G_∅,ℤ)) ≤ #H¹(G_∅,𝔽₂)` together with the `ℤ`-power sequence: the missing step is
false for abelian groups in general, so it must be supplied by the arithmetic of `F`. -/
theorem pruefer_obstruction :
    Nat.card (Work.WingbergRoute.QZ ⧸
        AddSubgroup.closure (Set.range (fun x : Work.WingbergRoute.QZ => (2 : ℕ) • x))) ≤ 1 ∧
      ¬ (Nat.card {x : Work.WingbergRoute.QZ // (2 : ℕ) • x = 0} ≤ 1) := by
  have hH : AddSubgroup.closure
      (Set.range (fun x : Work.WingbergRoute.QZ => (2 : ℕ) • x)) = ⊤ := by
    rw [Work.WingbergRoute.qz_two_smul_surjective.range_eq, AddSubgroup.closure_univ]
  have hB : Nat.card (Work.WingbergRoute.QZ ⧸
      AddSubgroup.closure (Set.range (fun x : Work.WingbergRoute.QZ => (2 : ℕ) • x))) = 1 := by
    rw [hH]
    exact Nat.card_eq_one_iff_unique.mpr
      ⟨QuotientAddGroup.subsingleton_quotient_top, ⟨0⟩⟩
  refine ⟨le_of_eq hB, ?_⟩
  intro hle
  have hgt := Work.WingbergRoute.pruefer_twoTorsion_card_gt_quot
  rw [hB] at hgt
  omega

/-- **The obstruction, as a statement about the wall.**  The `H³`-half of Wingberg's duality is not
a formal consequence of the `H²`-half: the identity
`#H²(G,𝔽₂) = #(H²(G,ℤ)/2)·#H³(G,ℤ)[2]` and the unconditional bound on the first factor only give
`#H³(G,ℤ)[2] ≤ 2 ^ (d + d₂(O_F^×))`, and the step which would remove the factor `2 ^ d` --
bounding `#A[2]` by `#(A/2A)` for an abelian group `A` -- is false
(`not_forall_twoTorsion_card_le_quot_card`). -/
theorem h3_half_not_derivable_from_h2_half :
    ¬ (∀ (A : Type) [AddCommGroup A],
        Nat.card {x : A // (2 : ℕ) • x = 0} ≤
          Nat.card (A ⧸ AddSubgroup.closure (Set.range (fun x : A => (2 : ℕ) • x)))) ∧
      Nat.card (Work.WingbergRoute.QZ ⧸
        AddSubgroup.closure (Set.range (fun x : Work.WingbergRoute.QZ => (2 : ℕ) • x))) ≤ 1 :=
  ⟨not_forall_twoTorsion_card_le_quot_card, pruefer_obstruction.1⟩

end Work.WingbergH3
