/-
# L5e (Case 2): a cyclically reduced closed path cannot *carry* the code of a bridge

This is the variant of `Work.ORLocInd.Howie.L5.false_of_bridge_forest_side_del` in which the
conclusion `e ∈ r.arrowList` is weakened to the hypothesis `he` actually available in Howie's
Case 2, namely

    `∃ g ∈ r.arrowList, P.edgeOf g = P.edgeOf e`

(`r` contains *some* arrow carrying the code of the unoriented edge `{e, e⁻¹}`; by
`P.CodeSeparates` that arrow is `e` or `e⁻¹`).  As before, `hbr` is the honest bridge hypothesis of
the deleted graph `Γ ∖ e` (`∀ q : Quiver.Path e.right e.left, Avoids P e q → False`) and `hfor`
localises the forest hypothesis at `e.left`.

## The two cases

Split `r` at its **first** crossing of the code of `e` (`avoid_or_split`):

    r = α ∗ g ∗ β,     α avoiding the code of `e`,   P.edgeOf g = P.edgeOf e.

* If `g = e`, then `e ∈ r.arrowList` and the earlier L5 lemma
  (`false_of_bridge_forest_side_del`) applies unchanged.
* If `g = e⁻¹`, then `α : w ⟶ e.right` avoids the code of `e`, and only the tail `β : e.left ⟶ w`
  is left.  Splitting `β` at *its* first crossing (or finding that it has none):
  * if `β` avoids the code, then `α.reverse ∗ β.reverse : e.right ⟶ e.left` avoids it too,
    contradicting `hbr`;
  * if `β = γ ∗ g' ∗ δ` with `γ` avoiding the code, then `g'` is `e` or `e⁻¹`:
    - `g' = e⁻¹` gives `γ.reverse : e.right ⟶ e.left` avoiding the code, i.e. `hbr`;
    - `g' = e` gives a reduced closed path `γ : e.left ⟶ e.left` avoiding the code, which `hfor`
      forces to be empty; but then `r` contains the consecutive pair `e⁻¹, e`, i.e. a backtrack,
      contradicting `r.IsReduced`.

Note that only the second bullet uses `hfor`, and only the last subcase uses `hcr` (indirectly,
through `false_of_bridge_forest_side_del`) — the case `g = e⁻¹` is disposed of by the bridge
hypothesis `hbr` and reducedness alone, except when the tail starts by returning immediately
across the bridge.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Case2Bridge
import Submission.Work.ORLocInd.Howie.L5.false_of_bridge_forest_side_del
import Submission.Work.ORLocInd.Howie.C2.avoid_or_split

set_option backward.isDefEq.respectTransparency false

namespace Work.ORLocInd.Howie.C2

/-- If a path splits as `p = α ∗ g ∗ β` at an arrow `g`, then `g` belongs to the arrow list of `p`.
(The `Quiver.Total` record of `g` is `Quiver.Total.mk g.left g.right g.hom`.) -/
theorem mem_arrowList_of_eq_comp_toPath {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {a b : V} {p : Quiver.Path a b} {g : Quiver.Total V} {α : Quiver.Path a g.left}
    {β : Quiver.Path g.right b} (h : p = α.comp (g.hom.toPath.comp β)) :
    Quiver.Total.mk g.left g.right g.hom ∈ p.arrowList := by
  rw [h, Work.ORLocInd.Howie.Quiver.Path.arrowList_comp',
    Work.ORLocInd.Howie.Quiver.Path.arrowList_comp',
    Work.ORLocInd.Howie.Quiver.Path.arrowList_toPath']
  simp

theorem false_of_bridge_forest_side_exists {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V)
    (hbr : ∀ q : Quiver.Path e.right e.left, Work.ORLocInd.Howie.Avoids P e q → False)
    (hfor : ∀ q : Quiver.Path e.left e.left, Work.ORLocInd.Howie.Avoids P e q → q.IsReduced →
      q = Quiver.Path.nil)
    {w : V} (r : Quiver.Path w w) (hr : r.IsReduced)
    (hcr : Work.ORLocInd.Howie.IsCyclicallyReduced r)
    (he : ∃ g ∈ r.arrowList, P.edgeOf g = P.edgeOf e) : False := by
  -- Split `r` at its first crossing of the code of `e`.
  rcases avoid_or_split P e r with hrav | ⟨g, α, β, hα, hg, hr_eq⟩
  · -- `r` carries no arrow of the code of `e` at all, contradicting `he`.
    obtain ⟨g0, hg0, hcg0⟩ := he
    exact hrav g0 hg0 hcg0
  · -- `g` is `e` or `e⁻¹` (`P.CodeSeparates`).
    rcases hsep g e hg with hge | hge
    · -- `g = e`: `e ∈ r.arrowList`, and the earlier L5 lemma applies.
      subst g
      have hmem : e ∈ r.arrowList := by
        have h1 := mem_arrowList_of_eq_comp_toPath hr_eq
        have heta : Quiver.Total.mk e.left e.right e.hom = e := by cases e; rfl
        rwa [heta] at h1
      exact Work.ORLocInd.Howie.L5.false_of_bridge_forest_side_del P hsep e hbr hfor r hr hcr hmem
    · -- `g = e⁻¹`: `α : w ⟶ e.right` avoids the code of `e`, and `β : e.left ⟶ w`.
      subst g
      rcases avoid_or_split P e β with hβav | ⟨g', γ, δ, hγ, hg', hβ_eq⟩
      · -- `β` avoids the code: `α.reverse ∗ β.reverse : e.right ⟶ e.left` avoids it too.
        have h1 : Work.ORLocInd.Howie.Avoids P e (α.reverse.comp β.reverse) :=
          (Work.ORLocInd.Howie.avoids_comp_iff P e α.reverse β.reverse).mpr
            ⟨Work.ORLocInd.Howie.avoids_reverse P e hα,
             Work.ORLocInd.Howie.avoids_reverse P e hβav⟩
        exact hbr _ h1
      · rcases hsep g' e hg' with hg'e | hg'e
        · -- `g' = e`: `γ : e.left ⟶ e.left` is a reduced path avoiding the code, so `hfor` makes
          -- it empty, and then `r` contains the backtrack `e⁻¹ ∗ e`.
          subst g'
          have hr2 : (α.comp (((Quiver.totalReverse e).hom).toPath.comp β)).IsReduced :=
            hr_eq ▸ hr
          have hβred : β.IsReduced :=
            (Quiver.Path.isReduced_comp_iff.mp
              (Quiver.Path.isReduced_comp_iff.mp hr2).2.1).2.1
          have hγred : γ.IsReduced :=
            (Quiver.Path.isReduced_comp_iff.mp (hβ_eq ▸ hβred)).1
          have hγnil : γ = Quiver.Path.nil := hfor γ hγ hγred
          have hdb : Quiver.Path.DeleteBacktrack r (α.comp δ) := by
            rw [hr_eq, hβ_eq, hγnil, Quiver.Path.nil_comp]
            have h := Quiver.Path.DeleteBacktrack.intro α ((Quiver.totalReverse e).hom) δ
            simpa using h
          exact hr (α.comp δ) hdb
        · -- `g' = e⁻¹`: `γ.reverse : e.right ⟶ e.left` avoids the code, contradicting `hbr`.
          subst g'
          have h1 : Work.ORLocInd.Howie.Avoids P e γ.reverse :=
            Work.ORLocInd.Howie.avoids_reverse P e hγ
          exact hbr γ.reverse h1

end Work.ORLocInd.Howie.C2
