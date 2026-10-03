import Mathlib
import Submission.Work.OROneRel.NoZeroDefs
import Submission.Work.OROneRel.mk_of_infinite_order

/-!
# Injectivity of the first amalgamation map `amPhi r t p true`

The map

  `amPhi r t p true : ULift (Multiplicative ℤ) →* ⟨α | r⟩`,   `n ↦ (mk (of t)) ^ (toAdd n.down)`

is the map `ℤ → ⟨α | r⟩`, `n ↦ t ^ n` on the image of the letter `t`; it is injective exactly when
`mk (of t)` has infinite order in `⟨α | r⟩`.

That is the case whenever `r` is cyclically reduced and the generator `t` is accompanied in the
relator by a *second* generator `x ≠ t`: the Freiheitssatz applied to the Magnus subgroup generated
by all generators except `x` puts `⟨t⟩` inside `⟨α | r⟩` as the image of the free group `F({t})`,
where `t` has infinite order (`Work.OROneRel.mk_of_infinite_order`).  This is the Freiheitssatz for
the Magnus subgroup `⟨t⟩` of the one-relator group `⟨α | r⟩`.

Everything here is sorry-free and depends only on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Work.OROneRel

universe u

/-- The canonical map `ℤ → ⟨α | r⟩`, `n ↦ (mk t) ^ n`, is injective: the class of `t` in `⟨α | r⟩`
has infinite order. -/
theorem zpow_mk_of_injective {α : Type u} (r : FreeGroup α) {t x : α} (hxt : x ≠ t)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hx : x ∈ Work.OROneRel.relatorLetters r) :
    Function.Injective (fun n : ℤ =>
      (PresentedGroup.mk ({r} : Set (FreeGroup α)) (FreeGroup.of t)) ^ n) := by
  refine (injective_zpow_iff_not_isOfFinOrder).mpr fun hfin => ?_
  obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have h0 : (n : ℤ) = 0 :=
    mk_of_infinite_order r hxt hcyc hx (n : ℤ) (by simpa using hgn)
  omega

theorem amPhi_true_injective {α : Type u} (r : FreeGroup α) {t x : α} (hxt : x ≠ t)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hx : x ∈ Work.OROneRel.relatorLetters r) (p : ℤ) :
    Function.Injective (Work.OROneRel.amPhi r t p true) := by
  have hz := zpow_mk_of_injective r hxt hcyc hx
  intro n m h
  rw [Work.OROneRel.amPhi_true_apply, Work.OROneRel.amPhi_true_apply] at h
  exact ULift.ext (x := n) (y := m) (Multiplicative.toAdd.injective (hz h))

end Work.OROneRel
