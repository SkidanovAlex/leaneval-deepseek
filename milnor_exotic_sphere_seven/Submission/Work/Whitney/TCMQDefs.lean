import Mathlib
import Submission.Work.Whitney.TCMDefs
import Submission.Work.Thom.naturalModelClass_punct

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# The model product formula as a `Prop`

`Work.Whitney.tcmQ B p q` is the *model product formula* over the base `B`: the relative-relative
cup of the two pulled-back model Thom classes is the model class of the sum,

`tcmRelCup (pr₁^* Mpun p B) (pr₂^* Mpun q B) = tcmF^* (Mpun (p+q) B)`.

It is the statement of `Work.Whitney.tcmModelMul`, isolated as a `Prop` so that reductions and
inductions can refer to it without repeating the long term.  The target of the present stretch is
its specialisation to a one-point base, `Work.Whitney.tcmModelMul_point_subsingleton`.
-/

namespace Work.Whitney

open Work.Thom

noncomputable section

/-- **The model product formula over a base `B`**: the relative-relative cup of the two pulled-back
model Thom classes is the model class of the sum. -/
abbrev tcmQ (B : Type) [TopologicalSpace B] (p q : ℕ) : Prop :=
    Work.Whitney.tcmRelCup (Work.Whitney.tcmA B p q) (Work.Whitney.tcmC B p q)
        (Work.Whitney.isOpen_tcmA B p q) (Work.Whitney.isOpen_tcmC B p q) p q
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr1 B p q) (Work.Whitney.tcmA B p q)
        (Work.Thom.Punct B p) (fun x hx => hx) ℤ p).hom (Work.Thom.Mpun p B))
      ((Work.Thom.relCohMap (Work.Whitney.tcmPr2 B p q) (Work.Whitney.tcmC B p q)
        (Work.Thom.Punct B q) (fun x hx => hx) ℤ q).hom (Work.Thom.Mpun q B))
    = (Work.Thom.relCohMap (Work.Whitney.tcmF B p q)
        (Work.Whitney.tcmA B p q ∪ Work.Whitney.tcmC B p q) (Work.Thom.Punct B (p + q))
        (Work.Whitney.tcmF_mem B p q) ℤ (p + q)).hom (Work.Thom.Mpun (p + q) B)

/-- The associativity of the canonical relative-relative cup product, with the set and degree
transports made explicit. -/
def tcmRelCupAssoc : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (A B C : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hC : IsOpen C) (p q r : ℕ) (a : RelCoh ℤ p X A) (b : RelCoh ℤ q X B) (c : RelCoh ℤ r X C),
    (Nat.add_assoc p q r) ▸ (Set.union_assoc A B C) ▸
      (Work.Whitney.tcmRelCup (A ∪ B) C (hA.union hB) hC (p + q) r
        (Work.Whitney.tcmRelCup A B hA hB p q a b) c)
    = (Work.Whitney.tcmRelCup A (B ∪ C) hA (hB.union hC) p (q + r) a
        (Work.Whitney.tcmRelCup B C hB hC q r b c))

end

end Work.Whitney
