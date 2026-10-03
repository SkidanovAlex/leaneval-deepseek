import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.ArrowSupport

namespace Work.ORLocInd.FKSKernel.Kurosh

/-- In a tree, a family of arrows which connects every two vertices (through paths using only
those arrows, and closed under reversal) must be everything.

Proof: given an arrow `f : a ⟶ b`, choose an `S`-path `p` from `a` to `b` (it exists by
`hconn`), reduce it to a reduced `S`-path `q` (reduction preserves the property of using only
`S`-arrows).  Both `q` and the one-arrow path `f.toPath` are reduced paths from `a` to `b`, so
they coincide by the uniqueness of reduced paths in a tree; hence the single arrow of `f.toPath`
belongs to `S`. -/
theorem spanning_arrows {X : Type*} [Quiver X] [Quiver.HasInvolutiveReverse X]
    (hT : Work.ORBassSerre.IsTree X) (S : Set (Quiver.Total X))
    (hS : ∀ e : Quiver.Total X, e ∈ S ↔ Quiver.Total.reverse e ∈ S)
    (hconn : ∀ a b : X, ∃ p : Quiver.Path a b, p.AllArrows S) :
    ∀ e : Quiver.Total X, e ∈ S := by
  rintro ⟨a, b, f⟩
  -- an `S`-path from `a` to `b`
  obtain ⟨p, hp⟩ := hconn a b
  -- reduce it, staying inside `S`
  obtain ⟨q, hpq, hqred⟩ :=
    Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced p
  have hqS : q.AllArrows S := Quiver.Path.allArrows_of_reducesTo hpq hp
  -- the one-arrow path is reduced, and in a tree it is the unique reduced path
  have hfto : f.toPath.IsReduced :=
    Quiver.Path.IsReduced.of_length_lt_two (by rw [Quiver.Path.length_toPath]; norm_num)
  have heq : q = f.toPath :=
    Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree hT hqred hfto
  rw [heq] at hqS
  exact (Quiver.Path.allArrows_toPath f).mp hqS

end Work.ORLocInd.FKSKernel.Kurosh
