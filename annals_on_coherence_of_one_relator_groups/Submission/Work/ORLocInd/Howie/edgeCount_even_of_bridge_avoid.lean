/-
# L5b for the *honest* bridge hypothesis: parity of the crossings of an edge `e`

`edgeCount P.edgeOf r e` counts the arrows of `r` whose code is the code of `e`; under
`P.CodeSeparates` these are exactly the arrows `e` and `e⁻¹`, so it is the number of times `r`
crosses the unoriented edge `{e, e⁻¹}`.  The lemma below says that if `e` is a *bridge of `Γ∖e`*,
i.e. there is no path from `e.right` to `e.left` avoiding the edge `e` (this is the hypothesis
`hbr`, phrased with `Avoids`), then every closed path crosses `{e, e⁻¹}` evenly.

## The formalisation trap this file avoids

The sibling file `edgeCount_even_of_bridge.lean` states `hbr` as

    `¬ Nonempty (Quiver.Path (e.right : DelV K) (e.left : DelV K))`,

and *that* hypothesis is vacuous: the vertex ascriptions are erased by elaboration, so it says
"there is no path of `Γ` from `e.right` to `e.left`", which is refuted by `e.toPath.reverse`.  Its
parity induction is therefore carried out for the *ambient* reachability relation `ReachFrom e`
(reachability in all of `Γ`), and its conclusion is true but vacuous.

Here the hypothesis is the genuine one: no path from `e.right` to `e.left` *avoiding* `e`
(`DelReach P e e.right` fails).  The ambient relation `ReachFrom e` is then useless — `e.left` is
always reachable from `e.right` through the arrow `e⁻¹` — and the induction must be carried out for
reachability *in the deleted graph* `Γ∖e`, which is the relation `DelReach` of `DelReach.lean`:

    `DelReach P e y := ∃ q : Quiver.Path e.left y, Avoids P e q`.

That relation has the right two properties (and `DelReach.lean` already provides them):

* an arrow `g` with `P.edgeOf g ≠ P.edgeOf e` preserves `DelReach` (append `g` in one direction,
  `g⁻¹` in the other — both paths stay inside `Γ∖e`);
* an arrow `g` with `P.edgeOf g = P.edgeOf e` is `e` or `e⁻¹` (`P.CodeSeparates`), so it *flips*
  `DelReach`: one of its endpoints is `e.left`, which is reachable by the empty path, and the other
  is `e.right`, which is not (that is exactly `hbr`).

Reading a path `p` from `a` to `b` arrow by arrow, the parity of the number of crossings of `e` is
the parity of the number of flips of `DelReach`, i.e.
`Even (edgeCount P.edgeOf p e) ↔ (DelReach P e a ↔ DelReach P e b)`; for a closed path the two ends
coincide and the count is even.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.DelReach
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.edgeCount_cons

namespace Work.ORLocInd.Howie

/-- The parity of an indicator: `if Q then 1 else 0` is even exactly when `Q` is false. -/
theorem even_ite_one_zero_of_avoid (Q : Prop) [Decidable Q] :
    Even (if Q then (1 : ℕ) else 0) ↔ ¬ Q := by
  by_cases h : Q <;> simp [h]

/-- An arrow of `Γ` whose code differs from the code of `e` preserves reachability from `e.left`
inside `Γ ∖ e`: a path of `Γ ∖ e` to the source can be extended by the arrow, and a path of
`Γ ∖ e` to the target can be extended by its reverse, and in both cases the new arrow still avoids
the code of `e`. -/
theorem delReach_iff_of_code_ne {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (e : Quiver.Total V) {a b : V} (g : a ⟶ b)
    (hg : P.edgeOf (Quiver.Total.mk a b g) ≠ P.edgeOf e) :
    DelReach P e a ↔ DelReach P e b :=
  ⟨fun h => delReach_of_delArrow' P e g hg h,
    fun h => delReach_of_delArrow P e g hg h⟩

/-- An arrow of `Γ` whose code is the code of `e` is `e` or `e⁻¹` (this is `P.CodeSeparates`), so
it flips reachability from `e.left` inside `Γ ∖ e`: one endpoint is `e.left` (reachable by the empty
path), the other is `e.right`, which is not reachable — this is the bridge hypothesis `hbr`. -/
theorem not_delReach_iff_of_code_eq {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V)
    (hbr : ¬ DelReach P e e.right) {a b : V} (g : a ⟶ b)
    (hg : P.edgeOf (Quiver.Total.mk a b g) = P.edgeOf e) :
    ¬ (DelReach P e a ↔ DelReach P e b) := by
  have hself : DelReach P e e.left := delReach_self P e
  rcases hsep (Quiver.Total.mk a b g) e hg with h | h
  · -- `g` is `e` itself: its source is `e.left`, its target is `e.right`
    have ha : a = e.left := by simpa using congrArg Quiver.Total.left h
    have hb : b = e.right := by simpa using congrArg Quiver.Total.right h
    rw [ha, hb]
    exact fun hc => hbr (hc.mp hself)
  · -- `g` is `e⁻¹`: its source is `e.right`, its target is `e.left`
    have ha : a = e.right := by simpa using congrArg Quiver.Total.left h
    have hb : b = e.left := by simpa using congrArg Quiver.Total.right h
    rw [ha, hb]
    exact fun hc => hbr (hc.mpr hself)

/-- **Parity of the crossings of `e` along a path.**  The number of arrows of `p` carrying the code
of `e` is even if and only if `DelReach P e` (reachability from `e.left` inside `Γ ∖ e`) has the
same truth value at the two endpoints of `p`. -/
theorem even_edgeCount_iff_delReach {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V)
    (hbr : ¬ DelReach P e e.right) {a b : V} (p : Quiver.Path a b) :
    Even (edgeCount P.edgeOf p e) ↔ (DelReach P e a ↔ DelReach P e b) := by
  induction p with
  | nil => simp [edgeCount]
  | cons p g ih =>
      rw [edgeCount_cons, Nat.even_add, ih, even_ite_one_zero_of_avoid]
      by_cases hcode : P.edgeOf (Quiver.Total.mk _ _ g) = P.edgeOf e
      · have h := not_delReach_iff_of_code_eq P hsep e hbr g hcode
        tauto
      · have h := delReach_iff_of_code_ne P e g hcode
        tauto

theorem edgeCount_even_of_bridge_avoid {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V)
    (hbr : ∀ q : Quiver.Path e.right e.left, Work.ORLocInd.Howie.Avoids P e q → False)
    {w : V} (r : Quiver.Path w w) : Even (Work.ORLocInd.Howie.edgeCount P.edgeOf r e) := by
  have hbr' : ¬ DelReach P e e.right := (not_delReach_right_iff P e).mpr hbr
  exact (even_edgeCount_iff_delReach P hsep e hbr' r).mpr Iff.rfl

end Work.ORLocInd.Howie
