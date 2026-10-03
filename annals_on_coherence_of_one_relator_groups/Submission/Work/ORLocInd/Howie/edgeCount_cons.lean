import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2

universe u

namespace Work.ORLocInd.Howie

/-- `edgeCount` of a path extended by one arrow: the count of arrows whose code is `ω e`
increases by `1` exactly when the new arrow's own code is `ω e`. -/
theorem edgeCount_cons {V : Type u} [Quiver V] {α : Type u} [LinearOrder α]
    (ω : Quiver.Total V → α) {a b c : V} (p : Quiver.Path a b) (g : b ⟶ c)
    (e : Quiver.Total V) :
    Work.ORLocInd.Howie.edgeCount ω (p.cons g) e =
      Work.ORLocInd.Howie.edgeCount ω p e +
        (if ω (Quiver.Total.mk b c g) = ω e then 1 else 0) := by
  simp only [Work.ORLocInd.Howie.edgeCount, Quiver.Path.arrowList_cons, List.filter_append,
    List.filter_cons]
  by_cases h : ω (Quiver.Total.mk b c g) = ω e <;> simp [h]

end Work.ORLocInd.Howie
