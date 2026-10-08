import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.DihOrCycSub

namespace Work.CORE4

/-- **LEAF C10.N1 `NineShape`**: "This proves that `E/Z(E)` is isomorphic to some `L₂(q)`"
(`E = layerIn C.D.M`, after the `A₇` case is excluded).

`NineShapeProp I` gives, from `Hyp9 G B C` and `¬ IsA7Case C.D`:

    ∃ p e : ℕ, Fact p.Prime ∧ NineShape C.D p e

with `NineShape C.D p e = Odd p ∧ 5 ≤ p ^ e ∧ Nonempty (E/Z(E) ≃* PSL(2, GF p e)) ∧ Odd |Z(E)|`.

This is a wrapper of the already-proved `Submission.Work.CORE4.LayerCtx6`: feed it
`hH.1 : BenderCtx G` and `DihOrCycSylow ↥C.D.M` (from `BenderCtx.sylow` by the proved
`Submission.Work.CORE4.DihOrCycSub`), and use that `IsA7Case C.D` is by definition the first
disjunct of its conclusion (`Nonempty (E/Z(E) ≃* A₇)`) so that `¬ IsA7Case C.D` selects the
`PSL(2, GF p e)` branch. -/
theorem NineShape (I : Work.GW2.C4Inputs) : Work.GW2.NineShapeProp I := by
  intro G _ _ B C hH hnA
  have hbc : Work.GW2.BenderCtx G := hH.1
  have hD : Work.GW2.DihOrCycSylow ↥C.D.M := DihOrCycSub hbc.sylow C.D.M
  obtain ⟨-, hodd, hshape⟩ := LayerCtx6 I hbc C hD
  rcases hshape with hA7 | ⟨p, e, hp, hpodd, h5, hiso⟩
  · exact absurd hA7 hnA
  · exact ⟨p, e, hp, hpodd, h5, hiso, hodd⟩

end Work.CORE4
