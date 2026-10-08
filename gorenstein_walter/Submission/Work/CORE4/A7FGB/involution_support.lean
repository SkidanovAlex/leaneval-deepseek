import Mathlib
import Submission.Work.AUTA7.A7.EvenInvolutionCycleType

namespace Work.CORE4.A7FGB

theorem involution_support (z : alternatingGroup (Fin 7)) (hz : z * z = 1) (hz1 : z ≠ 1) :
    (z : Equiv.Perm (Fin 7)).support.card = 4 := by
  have hZZ : (z : Equiv.Perm (Fin 7)) * (z : Equiv.Perm (Fin 7)) = 1 := by
    have h := congrArg (fun x : alternatingGroup (Fin 7) => (x : Equiv.Perm (Fin 7))) hz
    simpa using h
  have hZ1 : (z : Equiv.Perm (Fin 7)) ≠ 1 := fun h => hz1 (Subtype.coe_injective h)
  have hsign : Equiv.Perm.sign (z : Equiv.Perm (Fin 7)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp z.2
  have hct : (z : Equiv.Perm (Fin 7)).cycleType = ({2, 2} : Multiset ℕ) :=
    Work.AUTA7.A7.EvenInvolutionCycleType hZZ hZ1 hsign
  have hsum := Equiv.Perm.sum_cycleType (z : Equiv.Perm (Fin 7))
  rw [hct] at hsum
  simpa using hsum.symm

end Work.CORE4.A7FGB
