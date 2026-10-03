import Mathlib
import Submission.Work.Peluse.ExpA.slotProdReindex
import Submission.Work.Peluse.Holds.ExpPET.petExpansion

namespace Work.Peluse.ExpA

theorem expCubeSlotIdentity {s : ℕ} (c : ℤ) (b n n' : Fin s → ℤ) (f : ℤ → ℂ) (a x : ℤ) :
    Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * a + b i) n n' f
        (x - ∑ i : Fin s, n' i * (c * a + b i))
      = f x * ∏ i : Fin (2 ^ s - 1),
          Work.Peluse.ExpA.slotFn s b (fun j => n j - n' j) f i.succ
            (x + Work.Peluse.ExpA.cSlot s c (fun j => n j - n' j) i.succ * a) := by
  rw [Work.Peluse.Holds.ExpPET.expCube_eq_multilinear c f n n' a x]
  rw [slotProdReindex s (fun ω : Fin s → Bool =>
    (star^[Work.Peluse.weight ω])
      (f (x + (c * a) * (∑ j : Fin s, if ω j then n j - n' j else 0)
          + (∑ j : Fin s, (if ω j then n j - n' j else 0) * b j))))]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [slotFn, cSlot, Function.comp_apply, Work.Peluse.shift, dotU, dotB]
  congr 2
  ring

end Work.Peluse.ExpA
