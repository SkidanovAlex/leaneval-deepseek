import Mathlib
import Submission.Work.GlaubermanZJ.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ

/-- For a prime `p`, a natural number all of whose prime divisors are `≠ p` is
exactly a number coprime to `p`.  This bridges the two encodings of `p'`-numbers
used in the project (`IsPiNat (· ≠ p)` and `Nat.Coprime · p`). -/
theorem isPiNat_ne_iff_coprime {p n : ℕ} (hp : p.Prime) :
    Work.Fitting.IsPiNat (fun q => q ≠ p) n ↔ Nat.Coprime n p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  constructor
  · intro h hd
    exact h p hp hd rfl
  · intro h q _hq hqd hqp
    exact h (hqp ▸ hqd)

/-- The blueprint's `O_{p'}(G)` (defined as the supremum of the normal subgroups
of order coprime to `p`) coincides with the Feit–Thompson project's `π`-core
`Work.Fitting.pPrimeCore p G = O_{p'}(G)` (defined as the supremum of the normal
subgroups whose order has all prime divisors `≠ p`). -/
theorem pPrimeCore_eq_fitting {G : Type*} [Group G] (p : ℕ) (hp : p.Prime) :
    Submission.Blueprint.pPrimeCore p G = Work.Fitting.pPrimeCore p G := by
  unfold Submission.Blueprint.pPrimeCore Work.Fitting.pPrimeCore Work.Fitting.piCore
  congr 1
  ext N
  exact ⟨fun h => ⟨h.1, (isPiNat_ne_iff_coprime hp).mpr h.2⟩,
         fun h => ⟨h.1, (isPiNat_ne_iff_coprime hp).mp h.2⟩⟩

end Work.GlaubermanZJ
