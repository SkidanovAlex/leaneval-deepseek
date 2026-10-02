import Mathlib
import Submission.Work.Gen.LhCalc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}

/-- The degree cast `Work.Thom.cohTransport` is additive, including over a finite sum (it is the
underlying function of the linear map `Work.Thom.cohTransportLM`). -/
theorem cohTransport_sum {n n' : ℕ} (h : n = n') {α : Type} [Fintype α]
    (f : α → Coh ℤ n B) :
    cohTransport h (∑ i, f i) = ∑ i, cohTransport h (f i) :=
  map_sum (cohTransportLM h) f Finset.univ

end

open Work.TangentClasses Work.Thom in
/-- **The `H⁰(B)`-module structure of the Leray–Hirsch decomposition.**  For a degree-`0` class
`y : H⁰(B)` and a Leray–Hirsch combination `lhMap Z k c = Σ_i π^*(c i) ⌣ ζ^i`, multiplying by the
pullback `π^*(y)` multiplies each coefficient:
`π^*(y) ⌣ lhMap Z k c = lhMap Z k (fun i => y ⌣ c i)`. -/
theorem cupChern_zero_lhMap {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    {k : ℕ} (y : Work.Thom.Coh ℤ 0 B)
    (c : (i : {i : Fin m // (i : ℕ) ≤ k}) → Work.Thom.Coh ℤ (2 * (k - (i : ℕ))) B) :
    Work.Whitney.cupChern 0 k
        ((ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ 0)) y)
        (Work.LerayHirsch.lhMap Z k c)
      = Work.Thom.cohTransport (by omega : 2 * k = 2 * (0 + k))
          (Work.LerayHirsch.lhMap Z k
            (fun i => Work.Thom.cohTransport
              (by omega : 2 * (0 + (k - (i : ℕ))) = 2 * (k - (i : ℕ)))
              (Work.Whitney.cupChern 0 (k - (i : ℕ)) y (c i)))) := by
  rw [Work.LerayHirsch.lhMap_apply, Work.LerayHirsch.lhMap_apply]
  rw [Work.Gen.cupChern_sum_right]
  rw [Work.Gen.cohTransport_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Per index: `π^*(y) ⌣ (π^*(c i) ⌣ ζ^i) = π^*(y ⌣ c i) ⌣ ζ^i`, i.e. associativity of the
  -- graded product with the degree-`0` factor `π^*(y)`, plus the cast bookkeeping.
  set Y := (ModuleCat.Hom.hom (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ 0)) y
  set C := (ModuleCat.Hom.hom
    (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ (2 * (k - (i : ℕ))))) (c i)
  set Zp := Work.LerayHirsch.zetaPow Z i
  rw [Work.LerayHirsch.lhTerm_def, Work.LerayHirsch.lhTerm_def]
  rw [Work.Whitney.cohTransport_CohMap]
  rw [Work.Whitney.cupChern_CohMap]
  rw [Work.Gen.cupChern_cast_right, Work.Gen.cupChern_cast_left]
  rw [Work.Whitney.cohTransport_trans, Work.Whitney.cohTransport_trans]
  have hA := Work.Gen.cupChern_assoc (a := 0) (b := k - (i : ℕ)) (c := (i : ℕ))
      (u := Y) (v := C) (w := Zp)
  rw [hA, Work.Whitney.cohTransport_trans]

end Work.Gen
