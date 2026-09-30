import Mathlib
import Submission.Work.BMF.mr_direct.ebound_defs
import Submission.Work.BMF.mr_direct.buchstab_aux
import Submission.Work.BMF.mr_direct.omegaCount_mul_prime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

theorem omegaCount_le_of_mem_ebFiber (K P Q X : ℝ) (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (n : ℕ) (i : Σ _ : ℕ, ℕ) (hi : i ∈ Work.BMF.mr_direct.ebFiber K P Q X n) :
    Work.BMF.mrDirect.omegaCount P Q n ≤ Work.BMF.mrDirect.omegaCount P Q i.2 + 1 := by
  rw [Work.BMF.mr_direct.ebFiber, Finset.mem_filter] at hi
  obtain ⟨hiB, hieq⟩ := hi
  rw [Work.BMF.mrDirect.pSetB, Finset.mem_sigma] at hiB
  obtain ⟨hpp_mem, -⟩ := hiB
  have hQ0 : 0 ≤ Q := by linarith
  obtain ⟨hpp, hPp, hpQ⟩ := (Work.BMF.mrDirect.mem_primeSet hQ0).mp hpp_mem
  rw [← hieq, Work.BMF.mr_direct.ebnn]
  have h := omegaCount_mul_prime (P := P) (Q := Q) (p := i.1) (m := i.2) hpp hPp hpQ
  rw [mul_comm, h]
  have hif : (if i.1 ∣ i.2 then (0 : ℕ) else 1) ≤ 1 := by split <;> omega
  omega

end Work.BMF.mr_direct
