/-
  WilC5 — the canonical instance bundle at an `LRc`-structure modelling `TR`.

  vdDMM's §3–§4, and area C2's o-minimality input `OMinModels` / the cut/type theorem
  `Work.WilC5.cut_determines_type_of_omin`, are stated for a type that carries, besides an
  `LRc`-structure, the instances `Field`, `LinearOrder` (whose order *is* the ring-definable order
  `leE`), `IsStrictOrderedRing` and `Ring.CompatibleRing`.  A `κ`-saturated elementary extension of
  a model of `TR` — the amalgamation tool for the two-model cut comparison of vdDMM Lemmas 4.2–4.3
  — comes out of `Work.WilC5.ExistsSaturated` as a bare `LRc`-structure, so the instances have to be
  produced from `M ⊨ TR`.  This module does that:

  * `Work.WilC5.trField` — `Field M` from `Work.WilC5.tr_ring_field` and Mathlib's
    `fieldOfModelField`;
  * `Work.WilC5.trLinearOrder` — `LinearOrder M` with `≤` = `leEL`, from `Work.WilC5.tr_leE_axioms`;
  * `Work.WilC5.trCompatRing` — `Ring.CompatibleRing M` (this is `compatibleRingOfModelField`);
  * `Work.WilC5.tr_isStrictOrderedRing` — delegated, in
    `Submission/Work/WilC5/tr_isStrictOrderedRing.lean`.

  Together with `Work.WilC5.lrcRexpReduct` and `Work.WilC5.lrcConstReduct` (`LRcReduct.lean`) and
  the hypothesis `M ⊨ TR` this is exactly the instance list of `OMinModels`.
-/
import Submission.Work.WilC5.LRcReduct
import Submission.Work.WilC5.tr_ring_field
import Submission.Work.WilC5.tr_leE_axioms

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-- **`Field M` at an `LRc`-structure modelling `TR`.**  The ring axioms are
`Work.WilC5.tr_ring_field`; this is Mathlib's `FirstOrder.Field.fieldOfModelField`.

A caller who needs `Ring.CompatibleRing M` or the canonical instances of `OMinModels` should write
`letI : Field M := Work.WilC5.trField M h` and then
`letI := FirstOrder.Field.compatibleRingOfModelField M`, which is compatible with the `ring`
structure supplied by `Work.WilC5.lrcRingReduct`. -/
noncomputable def trField (M : Type) [LRc.Structure M] (h : M ⊨ TR) : Field M :=
  letI : Theory.field.Model M := tr_ring_field M h
  FirstOrder.Field.fieldOfModelField M

/-- **`LinearOrder M` whose order is the ring-definable order `leE`**, at an `LRc`-structure
modelling `TR`.  The four order axioms are `Work.WilC5.tr_leE_axioms`; the strict order is
`x < y ↔ x ≤ y ∧ ¬ y ≤ x`. -/
noncomputable def trLinearOrder (M : Type) [LRc.Structure M] (h : M ⊨ TR) : LinearOrder M :=
  let A := tr_leE_axioms M h
  { le := leEL
    lt := fun x y => leEL x y ∧ ¬ leEL y x
    le_refl := A.1
    le_trans := fun x y z hxy hyz => A.2.2.1 x y z hxy hyz
    lt_iff_le_not_ge := fun x y => Iff.rfl
    le_antisymm := fun x y hxy hyx => A.2.1 x y hxy hyx
    le_total := A.2.2.2
    toDecidableLE := fun x y => Classical.dec (leEL x y) }

@[simp] theorem trLinearOrder_le (M : Type) [LRc.Structure M] (h : M ⊨ TR) (x y : M) :
    @LE.le M (trLinearOrder M h).toLE x y ↔ leEL x y :=
  Iff.rfl

end Work.WilC5
