import Mathlib
import Submission.Work.Holonomy3.log_den_defs

namespace Work.Holonomy3

/-- Every prime `p > l` that divides a nonzero element `m` of the window `[n-D, n]` divides the
window product `L^{≥ l}_{n,D}` (it is one of the factors). -/
lemma prime_dvd_Lge {l n D m p : ℕ} (hp : p.Prime) (hlp : l < p)
    (hm : m ∈ (Finset.Icc (n - D) n).erase 0) (hpm : p ∣ m) :
    p ∣ Submission.CDT.LcmGe.Lge l n D := by
  rw [Submission.CDT.LcmGe.Lge]
  apply Finset.dvd_prod_of_mem
  rw [Finset.mem_filter]
  refine ⟨?_, hp, hlp, ⟨m, hm, hpm⟩⟩
  rw [Finset.mem_erase, Finset.mem_Icc] at hm
  rw [Finset.mem_Icc]
  exact ⟨hp.one_le, le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hm.1) hpm) hm.2.2⟩

end Work.Holonomy3
