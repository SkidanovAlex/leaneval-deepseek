import Submission.Work.PTGeometric.TransAtApply

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: the explicit concatenation of a finite family of loops

`GenLoop.transAt i` is Mathlib's concatenation of two cube loops along the coordinate `i`, and the
product in `π_N(X, x)` is its class (`HomotopyGroup.mul_spec`).  The geometric half of
Pontryagin–Thom needs the **explicit** concatenation of the pieces' collapse loops, and not merely a
loop with the right class: the zero set of the concatenation is the union of the pieces' zero sets
(each piece sitting in its own block of the cube — `TransAtApply.lean`), which is what makes the
`0`-end of the null-homotopy have the pieces as its preimage of the core.

The recursion below is written so that the class formula is the *direct* product of the classes of
the list (`HomotopyGroup.mul_spec` reads `⟦p⟧ * ⟦q⟧ = ⟦transAt i q p⟧`, so the new element must be
the *second* argument): the first element of the list lands in the last block of the cube, which is
geometrically irrelevant.

## Note on the instance of `π_N`

`Work.ThomBordism.PontryaginThom.HomotopyGroup` is a plain `def` of a `Quotient`, so type class
search does not see its group structure at the `Quotient` type (this is why the workspace's
`GenuineTransversality` provides it with `letI`).  The statements below carry the same `letI`.

## Main results

* `Work.PTGeometric.genLoopListConcat`
* `Work.PTGeometric.genLoopListConcat_class`
* `Work.PTGeometric.genLoop_listConcat_replicate_class`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Topology unitInterval
open Function Set

namespace Work.PTGeometric

noncomputable section

variable {N : Type*} [DecidableEq N] {X : Type} [TopologicalSpace X] {x : X}

/-- **The concatenation of a list of cube loops along the coordinate `i`.** -/
def genLoopListConcat (i : N) : List (GenLoop N X x) → GenLoop N X x
  | [] => GenLoop.const
  | g :: l => GenLoop.transAt i (genLoopListConcat i l) g

@[simp] theorem genLoopListConcat_nil (i : N) :
    genLoopListConcat (X := X) (x := x) i [] = GenLoop.const := rfl

@[simp] theorem genLoopListConcat_cons (i : N) (g : GenLoop N X x) (l : List (GenLoop N X x)) :
    genLoopListConcat i (g :: l) = GenLoop.transAt i (genLoopListConcat i l) g := rfl

/-- **The class of the concatenation is the product of the classes of the list.** -/
theorem genLoopListConcat_class [Nonempty N] (i : N) (l : List (GenLoop N X x)) :
    letI : Group (Quotient (GenLoop.Homotopic.setoid N x)) := HomotopyGroup.group N
    (Quotient.mk _ (genLoopListConcat (X := X) (x := x) i l) : HomotopyGroup N X x)
      = (l.map (fun g => (Quotient.mk _ g : HomotopyGroup N X x))).prod := by
  letI : Group (Quotient (GenLoop.Homotopic.setoid N x)) := HomotopyGroup.group N
  induction l with
  | nil =>
    show (Quotient.mk _ (GenLoop.const : GenLoop N X x) : HomotopyGroup N X x) = _
    rw [List.map_nil, List.prod_nil]
    exact HomotopyGroup.one_def.symm
  | cons g l ih =>
    rw [genLoopListConcat_cons, List.map_cons, List.prod_cons]
    calc (Quotient.mk _ (GenLoop.transAt i (genLoopListConcat (X := X) (x := x) i l) g) :
          HomotopyGroup N X x)
        = (Quotient.mk _ g : HomotopyGroup N X x)
          * (Quotient.mk _ (genLoopListConcat (X := X) (x := x) i l) : HomotopyGroup N X x) :=
          (HomotopyGroup.mul_spec (i := i) (p := g)
            (q := genLoopListConcat (X := X) (x := x) i l)).symm
      _ = (Quotient.mk _ g : HomotopyGroup N X x)
          * (l.map (fun g => (Quotient.mk _ g : HomotopyGroup N X x))).prod := by rw [ih]

/-- **`m` copies of one loop**: the concatenation of `List.replicate m g` has class the `m`-th power
of the class of `g`. -/
theorem genLoop_listConcat_replicate_class [Nonempty N] (i : N) (m : ℕ)
    (g : GenLoop N X x) :
    letI : Group (Quotient (GenLoop.Homotopic.setoid N x)) := HomotopyGroup.group N
    (Quotient.mk _ (genLoopListConcat (X := X) (x := x) i (List.replicate m g)) :
        HomotopyGroup N X x)
      = (Quotient.mk _ g : HomotopyGroup N X x) ^ m := by
  letI : Group (Quotient (GenLoop.Homotopic.setoid N x)) := HomotopyGroup.group N
  rw [genLoopListConcat_class]
  simp [List.map_replicate, List.prod_replicate]


/-- The product of the `m`-fold flattening of a list is the `m`-th power of its product. -/
theorem list_prod_flatten_replicate {α : Type*} [CommMonoid α] (m : ℕ) (l : List α) :
    (List.flatten (List.replicate m l)).prod = l.prod ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, List.prod_append, ih, pow_succ']

/-- **The `m`-fold concatenation of a list of loops has class the `m`-th power of the product of
their classes.**  This is the form in which the `0`-end of the null-homotopy is produced: take `l` to
be the pieces' collapse loops and `m` the multiplicity of the trivialising power. -/
theorem genLoop_listConcat_flatten_class [Nontrivial N] [Nonempty N] (i : N) (m : ℕ)
    (l : List (GenLoop N X x)) :
    letI : CommGroup (Quotient (GenLoop.Homotopic.setoid N x)) :=
      inferInstanceAs (CommGroup (HomotopyGroup N X x))
    (Quotient.mk _ (genLoopListConcat (X := X) (x := x) i (List.flatten (List.replicate m l))) :
        HomotopyGroup N X x)
      = ((l.map (fun g => (Quotient.mk _ g : HomotopyGroup N X x))).prod) ^ m := by
  letI : CommGroup (Quotient (GenLoop.Homotopic.setoid N x)) :=
    inferInstanceAs (CommGroup (HomotopyGroup N X x))
  have h : (Quotient.mk _ (genLoopListConcat (X := X) (x := x) i
        (List.flatten (List.replicate m l))) : HomotopyGroup N X x)
      = ((List.flatten (List.replicate m l)).map
          (fun g => (Quotient.mk _ g : HomotopyGroup N X x))).prod :=
    genLoopListConcat_class (X := X) (x := x) (N := N) i (List.flatten (List.replicate m l))
  rw [h, List.map_flatten, List.map_replicate]
  exact list_prod_flatten_replicate m
    (l.map (fun g => (Quotient.mk _ g : HomotopyGroup N X x)))

end

end Work.PTGeometric
