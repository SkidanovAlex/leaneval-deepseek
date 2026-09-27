import Mathlib
import Submission.Work.Drive.OrderBase

/-! # The pairwise order relation on the rotations of the configuration Möbius strip

Following the project lead's guidance: the geometric core should be organised around a **pairwise**
relation `≺` on the strips `u · M` (rotations of the configuration Möbius strip of `γ`), not around the
`ZMod 2`-valued function `b` itself.  Two points matter:

* antisymmetry is a statement about *pairs of disjoint strips* — for disjoint `M` and `Q = u · M`,
  exactly one of `M ≺ Q`, `Q ≺ M` holds;
* `≺` is invariant under simultaneous rotation: `P ≺ Q ↔ v · P ≺ v · Q`.

At `u = 1/2` this *forces* `M ∩ (1/2)·M ≠ ∅`: rotating the pair `(M, (1/2)M)` by `1/2` gives
`((1/2)M, M)` (because `1/2 + 1/2 = 0` in `ℝ/ℤ`), so `M ≺ (1/2)M ↔ (1/2)M ≺ M`, contradicting
antisymmetry.  Hence `1/2 ∈ GoodC γ`, i.e. the inscribed square theorem comes for free from the order
machinery and must **not** be proved separately.  `one_half_mem_GoodC_of_stripRel` below records that
derivation.

Everything else about `b` — local constancy, antisymmetry for every `u ∈ Zc γ`, and transitivity — is
then immediate from `StripRel` (`parityCore_of_stripRel`, delegated).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- A pairwise relation on the rotations of the configuration Möbius strip `M` of `γ`, intended to be
`u · M ≺ v · M`.  Only pairs of *disjoint* strips are required to be comparable, i.e. pairs with
`v - u ∈ Zc γ`.  The four clauses are the paper's Lemma 3 (antisymmetry), the invariance of `≺` under the
rotation action, the paper's Lemma 4 (transitivity), and the openness of `≺`.

The last clause uses **separate** neighbourhoods `U ∋ u` and `V ∋ v`.  A single neighbourhood containing
both would be unsatisfiable: applying it to the swapped pair `(v,u)` (legal, since `Zc γ` is invariant
under negation) would give `Rel v u`, contradicting antisymmetry as soon as `Zc γ ≠ ∅`.  With separate
neighbourhoods it says exactly that `≺` is an open condition on disjoint pairs, and the argument
`Rel 0 u` (resp. `Rel u 0`) with `u' ∈ U` small still gives the local constancy of `b`. -/
def StripRel (γ : Circle → ℝ × ℝ) (Rel : UnitAddCircle → UnitAddCircle → Prop) : Prop :=
  (∀ u v : UnitAddCircle, v - u ∈ Zc γ → (Rel u v ↔ ¬ Rel v u)) ∧
  (∀ u v w : UnitAddCircle, Rel u v ↔ Rel (u + w) (v + w)) ∧
  (∀ u v w : UnitAddCircle, v - u ∈ Zc γ → w - v ∈ Zc γ → w - u ∈ Zc γ →
      Rel u v → Rel v w → Rel u w) ∧
  (∀ u v : UnitAddCircle, v - u ∈ Zc γ → Rel u v → ∃ U V : Set UnitAddCircle,
      IsOpen U ∧ IsOpen V ∧ u ∈ U ∧ v ∈ V ∧
        ∀ u' ∈ U, ∀ v' ∈ V, v' - u' ∈ Zc γ → Rel u' v')

/-- **The inscribed square comes for free.**  If a pairwise relation with the properties of `StripRel`
exists, then `1/2` is a collision angle of `γ`: the strips `M` and `(1/2)·M` cannot be disjoint, because
antisymmetry at the pair `(0, 1/2)` together with rotation invariance (rotating by `1/2` exchanges the two
strips) would force `M ≺ (1/2)M ↔ ¬ M ≺ (1/2)M`. -/
theorem one_half_mem_GoodC_of_stripRel {γ : Circle → ℝ × ℝ}
    {Rel : UnitAddCircle → UnitAddCircle → Prop} (h : StripRel γ Rel) :
    (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) ∈ Submission.Configuration.GoodC γ := by
  by_contra hmem
  set h2 : UnitAddCircle := (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) with h2def
  have hZ : h2 ∈ Zc γ := by
    rw [Zc, Set.mem_compl_iff]
    exact hmem
  have hanti := (h.1 0 h2) (by simpa using hZ)
  have hrot := h.2.1 0 h2 h2
  have hsum : h2 + h2 = 0 := by
    rw [h2def, ← AddCircle.coe_add]
    norm_num
  rw [zero_add, hsum] at hrot
  rw [hrot] at hanti
  by_cases hr : Rel h2 0
  · exact hanti.mp hr hr
  · exact hr (hanti.mpr hr)

end Work.Drive
