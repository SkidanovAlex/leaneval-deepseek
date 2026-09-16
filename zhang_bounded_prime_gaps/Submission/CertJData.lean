import Submission.CertJTabs
import Submission.CertEval

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The flat `J`-side data of the `k = 50` certificate

`certJKappaD a v = a!·v!·(50!/(a+v+1)!)` is the integer form of the coefficient `50!·κ(a,v)`
of the `(j,v)`-term of the certificate's marginal function, and
`cJTrips` is the flat list of the triples `(eraseOne α v, a+v+1, c·κ(a,v))` over the certificate
basis `cTrips` and the parts `v ∈ {0} ∪ α.dedup`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- `50! · κ(a,v)` as a natural number. -/
def certJKappaD (a v : ℕ) : ℕ :=
  a.factorial * v.factorial * ((50).factorial / (a + v + 1).factorial)

/-- The flat `(β, ã, W)` data of the `J`-form (one entry per `(j,v)`-term). -/
def cJTrips : List (List ℕ × ℕ × ℤ) :=
  cTrips.flatMap (fun u => (0 :: u.1.dedup).map (fun v =>
    (eraseOne u.1 v, u.2.1 + v + 1, u.2.2 * (certJKappaD u.2.1 v : ℤ))))

theorem mem_cJTrips {w : List ℕ × ℕ × ℤ} (h : w ∈ cJTrips) :
    ∃ u ∈ cTrips, ∃ v ∈ (0 :: u.1.dedup),
      w = (eraseOne u.1 v, u.2.1 + v + 1, u.2.2 * (certJKappaD u.2.1 v : ℤ)) := by
  rw [cJTrips, List.mem_flatMap] at h
  obtain ⟨u, hu, hw⟩ := h
  rw [List.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  exact ⟨u, hu, v, hv, rfl⟩

end Commons.NumberTheory.MaynardSieve
