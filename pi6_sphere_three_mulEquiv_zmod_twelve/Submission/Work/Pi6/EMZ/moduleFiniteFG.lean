import Mathlib
import Submission.Work.Pi6.EMZ.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMZ

/-- A finitely generated `ℤ`-module is a finitely generated abelian group.

Any two `ℤ`-module structures on an abelian group agree (`Subsingleton (Module ℤ G)`), so the
explicit structure `m` in the hypothesis may be replaced by the canonical one, for which
`Module.Finite.iff_addGroup_fg` applies. -/
theorem moduleFiniteFG {G : Type} [AddCommGroup G] (m : Module ℤ G)
    (h : @Module.Finite ℤ G _ _ m) : AddGroup.FG G := by
  have hm : m = AddCommGroup.toIntModule G := Subsingleton.elim m _
  rw [hm] at h
  exact Module.Finite.iff_addGroup_fg.mp h

end Work.Pi6.EMZ
