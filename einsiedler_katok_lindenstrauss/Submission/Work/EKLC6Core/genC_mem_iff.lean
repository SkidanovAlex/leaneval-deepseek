import Mathlib
import Submission.Work.EKLC6Core.CellSysDefs
import Submission.Work.EKLC6Core.atom_MSig

namespace Work.EKLC6Core

/-- Membership of a point of the `k`-th cell in the clipped cylinder generator `genC S O k m` is
membership of its lift `lift S k y` in the `U`-saturation `satU U (O m)` of `O m`.

This is the characterisation of the clipped generators used in the atom computation
(`Work.EKLC6Core.atom_MSig`): inside the cell `Q k`, `mkX` is injective on the lifted ball
`lifted (δ k) (g k)`, so the `mkX`-preimage of `y` inside that ball is the single point
`lift S k y ∈ lifted (δ k) (g k)`; hence the preimage of `genC S O k m` inside the ball is
nonempty exactly when `lift S k y` already lies in `satU U (O m)`. -/
theorem genC_mem_iff {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3} (S : Work.EKLC6Core.CellSys μ U)
    (O : ℕ → Set Work.EKLContract.SL3) (k m : ℕ) {y : Work.EKLContract.X3} (hy : y ∈ S.Q k) :
    y ∈ Work.EKLC6Core.genC S O k m ↔ Work.EKLC6Core.lift S k y ∈ Work.EKLC6Core.satU U (O m) :=
  atomMSig_mem_genC_iff S O hy

end Work.EKLC6Core
