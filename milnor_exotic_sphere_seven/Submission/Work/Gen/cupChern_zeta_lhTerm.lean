import Mathlib
import Submission.Work.Gen.LhCalc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Gen

open Work.TangentClasses Work.Thom

/-! ## A cast lemma for the graded product

`ζ ⌣ (u ⌣ v) = u ⌣ (v ⌣ ζ)` when `ζ` has degree `2`: the graded product is associative and
commutative in even degrees.  Both sides live in `H^{2(1+a+b)}`, and the degree bookkeeping is
`Work.Thom.cohTransport`. -/
theorem cupChern_zeta_cupChern {B : Type} [TopologicalSpace B]
    (ζ : Coh ℤ 2 B) (a b : ℕ) (u : Coh ℤ (2 * a) B) (v : Coh ℤ (2 * b) B) :
    Work.Whitney.cupChern 1 (a + b) ζ (Work.Whitney.cupChern a b u v)
      = cohTransport (by omega : 2 * (a + (b + 1)) = 2 * (1 + (a + b)))
          (Work.Whitney.cupChern a (b + 1) u (Work.Whitney.cupChern b 1 v ζ)) := by
  rw [Work.Whitney.ChernRel.cupChern_comm 1 (a + b) ζ (Work.Whitney.cupChern a b u v)]
  rw [Work.Gen.cupChern_assoc a b 1 u v ζ]
  rw [Work.Whitney.cohTransport_trans]

open Work.TangentClasses Work.Thom in
/-- **Multiplying the `i`-th Leray–Hirsch summand by `ζ` shifts the Leray–Hirsch index.**
`Work.LerayHirsch.lhTerm Z k i y = π^*(y) ⌣ ζ^i`, so `ζ ⌣ lhTerm Z k i y = π^*(y) ⌣ ζ^{i+1}`, which
is the summand of `lhMap Z (k+1)` at the index `j` (with `↑j = ↑i + 1`) and the coefficient `y`
(transported along `k - i = (k+1) - (i+1)`).  This is the multiplication of the free
`H^*(B)`-module `H^*(P(Z))` by `ζ`; there is no index overflow since `↑j < m`. -/
theorem cupChern_zeta_lhTerm {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {k : ℕ} (i j : Fin m) (hi : (i : ℕ) ≤ k) (hj : (j : ℕ) = (i : ℕ) + 1)
    (y : Work.Thom.Coh ℤ (2 * (k - (i : ℕ))) B) :
    Work.Whitney.cupChern 1 k (Work.LerayHirsch.zeta Z)
        (Work.LerayHirsch.lhTerm Z k ⟨i, hi⟩ y)
      = Work.Thom.cohTransport (by omega : 2 * (k + 1) = 2 * (1 + k))
          (Work.LerayHirsch.lhTerm Z (k + 1) ⟨j, by omega⟩
            (Work.Thom.cohTransport (by omega : 2 * (k - (i : ℕ)) = 2 * ((k + 1) - (j : ℕ))) y)) := by
  -- Rewrite the index `j` of the right-hand side as the explicit `Fin` `i + 1`; this makes the
  -- two sides syntactically comparable (they are then equal up to definitional reduction of the
  -- subtype projections).
  have him1 : (i:ℕ) + 1 < m := by omega
  have hjfin : j = ⟨(i:ℕ) + 1, him1⟩ := Fin.ext hj
  subst j
  -- Unfold `lhTerm` on both sides and get rid of the subtype projections.
  rw [Work.LerayHirsch.lhTerm_def, Work.LerayHirsch.lhTerm_def]
  simp only [Subtype.coe_mk, Fin.val_mk]
  -- Right-hand side: move the coefficient transport `2*(k-i) = 2*((k+1)-(i+1))` out of the
  -- pullback and out of the graded product, so that `ζ^{i+1}` becomes the second factor.
  rw [Work.Whitney.cohTransport_CohMap]
  rw [Work.Gen.cupChern_cast_left]
  rw [Work.LerayHirsch.zetaPow_succ]
  -- Left-hand side: hoist the transport built into `lhTerm`, then apply the graded-product
  -- identity `ζ ⌣ (u ⌣ ζ^i) = u ⌣ (ζ^i ⌣ ζ)`.
  rw [Work.Gen.cupChern_cast_right]
  rw [cupChern_zeta_cupChern]
  -- Both sides are now degree casts of the same class; compose the casts.
  rw [Work.Whitney.cohTransport_trans]
  rw [Work.Whitney.cohTransport_trans]
  rw [Work.Whitney.cohTransport_trans]

end Work.Gen
