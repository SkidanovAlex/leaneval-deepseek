import Mathlib
import Submission.Work.ZassenhausTwoGroup.FeitThm2
import Submission.Work.ZassenhausTwoGroup.feit_lemma3_4
import Submission.Work.ZassenhausTwoGroup.feit_lemma3_5_classes

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit 1960, Lemmas 3.4 and 3.5 (`BrauerFowlerProp`)

The literature input `BrauerFowlerProp` of the area `ZassenhausTwoGroup` (see `FeitThm2`) is the
conjunction of the two named lemmas of Feit's §3 (`Illinois J. Math. **4** (1960), pp. 181–182):

* **Lemma 3.4**: in a finite simple group `G` with rank-one Zassenhaus data `H = Q ⋊ D`,
  `G` has exactly one conjugacy class of involutions.  This is proved in-area by
  `Work.ZassenhausTwoGroup.feit_lemma3_4` (from Peterfalvi I Ch. I §1 (10)(a) and §2 Prop. 2(b)).
* **Lemma 3.5**: at least `q = |D|` conjugacy classes of `G` avoid `Q^G`, where
  `D = twoPoint H t`; the form proved in-area is the class count
  `Work.ZassenhausTwoGroup.feit_lemma3_5_classes`, which counts classes whose elements are
  non-trivial products of two involutions, are not involutions and are never conjugate into `Q`.

Here we assemble the consumer form used by the area: `k(G) > q + 1`, i.e.
`|twoPoint H t| + 1 < |ConjClasses G|`.  The two extra classes are the class of `1` and the
class of the involution `t`: both fail the four conditions of the counted classes (the first
because its elements are `≠ 1`, the second because its elements have order `2`), and they are
distinct since `orderOf 1 = 1 ≠ 2 = orderOf t`.

The only glue needed is the elementary counting fact that a predicate failing on two distinct
elements of a finite type misses at least two elements.
-/

set_option autoImplicit false

namespace Work.ZassenhausTwoGroup

open Submission.Blueprint

/-- Counting glue: if a predicate `p` on a finite type fails at two distinct elements, then the
subtype of `p` is at least two elements short of the whole type. -/
private theorem card_subtype_add_two_le_aux {α : Type*} [Fintype α] (p : α → Prop)
    [Fintype {x // p x}] [Fintype {x // ¬ p x}] {a b : α} (ha : ¬ p a) (hb : ¬ p b)
    (hab : a ≠ b) : Fintype.card {x // p x} + 2 ≤ Fintype.card α := by
  classical
  have h2 : 2 ≤ Fintype.card {x // ¬ p x} := by
    have hsub : ({(⟨a, ha⟩ : {x // ¬ p x}), ⟨b, hb⟩} : Finset {x // ¬ p x}) ⊆ Finset.univ :=
      Finset.subset_univ _
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ] at h1
    rw [Finset.card_insert_of_notMem, Finset.card_singleton] at h1
    · simpa using h1
    · simp only [Finset.mem_singleton]
      exact fun h => hab (Subtype.ext_iff.mp h)
  have hcompl := Fintype.card_subtype_compl p
  have hle := Fintype.card_subtype_le p
  omega

theorem brauerFowlerProp : BrauerFowlerProp := by
  intro G _ _ _ H Q t h hZ hQ2
  classical
  refine ⟨feit_lemma3_4 H Q t h, ?_⟩
  set P : ConjClasses G → Prop := fun c =>
    ∀ x ∈ c.carrier, x ≠ 1 ∧ orderOf x ≠ 2 ∧
      (∃ u v : G, orderOf u = 2 ∧ orderOf v = 2 ∧ x = u * v) ∧
      ∀ g : G, g * x * g⁻¹ ∉ Q with hP
  -- `1` and `t` both fail the four conditions
  have h1 : ¬ P (ConjClasses.mk (1 : G)) := by
    intro hc
    exact (hc 1 (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl)).1 rfl
  have ht : ¬ P (ConjClasses.mk t) := by
    intro hc
    exact (hc t (ConjClasses.mem_carrier_iff_mk_eq.mpr rfl)).2.1 h.invol
  -- and they are distinct classes
  have hne : ConjClasses.mk (1 : G) ≠ ConjClasses.mk t := by
    intro hEq
    have hconj : IsConj (1 : G) t := ConjClasses.mk_eq_mk_iff_isConj.mp hEq
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have ht1 : t = 1 := by simpa using hg.symm
    have hinvol := h.invol
    rw [ht1, orderOf_one] at hinvol
    exact absurd hinvol (by norm_num)
  have htwo' : Fintype.card {c : ConjClasses G // P c} + 2 ≤ Fintype.card (ConjClasses G) :=
    card_subtype_add_two_le_aux P h1 ht hne
  have htwo : Nat.card {c : ConjClasses G // P c} + 2 ≤ Nat.card (ConjClasses G) := by
    simpa [Nat.card_eq_fintype_card] using htwo'
  have hK : Nat.card (twoPoint H t) ≤ Nat.card {c : ConjClasses G // P c} :=
    feit_lemma3_5_classes H Q t h hZ hQ2
  omega

end Work.ZassenhausTwoGroup
