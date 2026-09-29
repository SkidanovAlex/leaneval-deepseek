import Mathlib
import Submission.CDTPlan.InterfacesA

/-! Basic divisibility facts for `lcmUpto = [1,2,…,m]`. -/

namespace Work.ZagC

open Finset

lemma lcmUpto_dvd_of_le {m n : ℕ} (h : m ≤ n) :
    Submission.CDTPlan.lcmUpto m ∣ Submission.CDTPlan.lcmUpto n := by
  unfold Submission.CDTPlan.lcmUpto
  refine Finset.lcm_mono ?_
  intro x hx
  simp only [Finset.mem_Icc] at hx ⊢
  omega


end Work.ZagC
