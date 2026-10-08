/-
# BMAX — auxiliary vocabulary for Bender 1970, 1.6 (the `D`-group form)

Definitions used by `Work.BMAX.Bender16DGroup` and by the two core lemmas it is assembled
from:

* `piCoreIn π K = O_π(K)`, the `π`-core of a subgroup, as a subgroup of the ambient group
  (the analogue of `Work.GW2.pCoreIn` for an arbitrary set of primes);
* `opPrimeIn p K = O_{p'}(K)`.
-/
import Mathlib
import Submission.Work.BMAX.Defs

namespace Work.BMAX

open Subgroup

/-- `O_π(K)` as a subgroup of the ambient group (`K.subtype`-image of `Work.GW2.piCore π K`). -/
def piCoreIn {G : Type*} [Group G] (π : Set ℕ) (K : Subgroup G) : Subgroup G :=
  (Work.GW2.piCore π K).map K.subtype

/-- `O_{p'}(K)`: the largest normal subgroup of `K` of order prime to `p`, as a subgroup of the
ambient group. -/
def opPrimeIn {G : Type*} [Group G] (p : ℕ) (K : Subgroup G) : Subgroup G :=
  piCoreIn ({p} : Set ℕ)ᶜ K

theorem piCoreIn_le {G : Type*} [Group G] (π : Set ℕ) (K : Subgroup G) :
    piCoreIn π K ≤ K := by
  rw [piCoreIn]
  exact Subgroup.map_subtype_le _

theorem opPrimeIn_le {G : Type*} [Group G] (p : ℕ) (K : Subgroup G) : opPrimeIn p K ≤ K :=
  piCoreIn_le _ K

end Work.BMAX
