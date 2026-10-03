import Mathlib
import Submission.Work.ORBassSerre.Action.Lift.Basic

namespace Work.ORBassSerre.Action.Lift

theorem isFinitelyPresented_of_LGroup {G : Type*} {V : Type*} [Group G] [Quiver V]
    (h : Group.IsFinitelyPresented (Work.ORBassSerre.Action.Lift.LGroup G V)) :
    Group.IsFinitelyPresented G := by
  exact Group.IsFinitelyPresented.equiv (Work.ORBassSerre.Action.Lift.LGroupEquiv G V)

end Work.ORBassSerre.Action.Lift
