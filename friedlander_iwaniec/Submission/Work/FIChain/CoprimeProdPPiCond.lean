import Mathlib
import Submission.Work.FIChain.BpWinDefs

namespace Work.FIChain

/-- Any divisor `n₁` of the small-prime product `Π(Pz) = ∏_{p ≤ Pz} p` is coprime to every `n₀`
satisfying the `Π`-condition `(n₀, Π) = 1` (i.e. no prime `≤ Pz` divides `n₀`). -/
theorem CoprimeProdPPiCond (Pz n₁ n₀ : ℕ) (h₁ : n₁ ∣ Work.FIChain.ProdP Pz)
    (h₀ : Work.FITop4.PiCond Pz n₀) : n₁.Coprime n₀ := by
  refine Nat.coprime_of_dvd (fun q hq hqdvd hnq => ?_)
  have hqP : q ∣ ProdP Pz := hqdvd.trans h₁
  have hqle : q ≤ Pz := (hq.dvd_primorial_iff).mp hqP
  exact h₀ q hq hqle hnq

end Work.FIChain
