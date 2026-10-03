import Mathlib
import Submission.Work.ORAssembly.Defs
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORBassSerre.Interface
import Submission.Work.ORDunwoody.Lemmas.ofGTree_quiverTree

namespace Work.ORBassSerre.Assembly

universe u

set_option linter.style.haveILetI false

open Work.ORDunwoody

/-- `Work.ORDunwoody.FreeOnTreeIsFree` with the "no inversion" hypothesis added (the missing
hypothesis: `ZMod 2` acting on the line `ℤ` by `n ↦ 1 - n` has trivial vertex stabilizers but is
not free): a group acting on a tree with trivial vertex stabilizers and without inverting any
edge is a free group.  Use the bridge `Work.ORDunwoody.Lemmas.ofGTree_quiverTree` together with
`Work.ORBassSerre.Action.isFreeGroup_of_actsFreely_on_tree`. -/
theorem freeOnTreeIsFree_of_noInversions (Y : Type u) :
    ∀ (G : Type u) [Group G] {V : Type u} [MulAction G V] (S : Work.ORDunwoody.GTree G V),
      (∀ v : V, S.vertexStab v = ⊥) →
      (∀ (g : G) ⦃u v : V⦄, S.Adj u v → g • u = v → g • v = u → g = 1) →
      ∃ (α : Type u), Nonempty (G ≃* FreeGroup α) := by
  intro G _instG V _instV S hstab hninv
  obtain ⟨Q, hR, hA, htree, hadj, -⟩ :=
    Work.ORDunwoody.Lemmas.ofGTree_quiverTree.{u, u, u} S
  letI : Quiver V := Q
  letI : Quiver.HasInvolutiveReverse V := hR
  letI : Work.ORBassSerre.GraphAction G V := hA
  haveI : Nonempty V := S.isTree.connected.nonempty
  -- Trivial vertex stabilizers give a free action.
  have hfree : Work.ORBassSerre.ActsFreely G V := by
    rw [Work.ORBassSerre.actsFreely_iff_stabilizer_bot]
    intro v
    exact hstab v
  -- The "no inversion" hypothesis, translated to the edge quiver of the graph.
  have hninv' : Work.ORBassSerre.ActsWithoutInversions G V := by
    rintro g ⟨a, b, φ⟩ he
    have hab : S.Adj a b := (hadj a b).mp ⟨φ⟩
    have hleft : g • a = b := by
      have h := congrArg Quiver.Total.left he
      simpa only [GraphAction.smul_left, Quiver.Total.reverse_left] using h
    have hright : g • b = a := by
      have h := congrArg Quiver.Total.right he
      simpa only [GraphAction.smul_right, Quiver.Total.reverse_right] using h
    have hg : g = 1 := hninv g hab hleft hright
    have hba : b = a := by rw [← hleft, hg, one_smul]
    exact (S.adj_self a) (hba ▸ hab)
  haveI : IsFreeGroup G :=
    Work.ORBassSerre.Action.isFreeGroup_of_actsFreely_on_tree (G := G) (V := V) htree hfree hninv'
  exact ⟨IsFreeGroup.Generators G, ⟨IsFreeGroup.toFreeGroup G⟩⟩

end Work.ORBassSerre.Assembly
