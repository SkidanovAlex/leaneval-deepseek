import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.isClosed_Thick

namespace Work.EKLComp.ErgMax

open Work.EKLContract

/-- `Drho ρ` is the set of points whose whole `A⁺`-orbit lies in `Thick ρ`.  Since `Thick ρ` is
closed (for *every* `ρ`, with no compactness/Mahler input) and `x ↦ aPlus r s • x` is continuous,
`Drho ρ` is an intersection of closed sets. -/
theorem isClosed_Drho (ρ : ℝ) : IsClosed (Work.EKLContract.Drho ρ) := by
  have hT : IsClosed (Thick ρ) := Work.EKLContract.Lemmas.isClosed_Thick ρ
  have hEq : Drho ρ = ⋂ (r : {r : ℝ // 0 ≤ r}) (s : {s : ℝ // 0 ≤ s}),
      (fun x : X3 => aPlus (r : ℝ) (s : ℝ) • x) ⁻¹' (Thick ρ) := by
    ext x
    simp only [Drho, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h r s; exact h r s r.2 s.2
    · intro h r s hr hs; exact h ⟨r, hr⟩ ⟨s, hs⟩
  rw [hEq]
  exact isClosed_iInter fun r => isClosed_iInter fun s =>
    hT.preimage (continuous_const_smul _)

end Work.EKLComp.ErgMax
