import Mathlib
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.sigmaN_farey_helpers
import Submission.Work.BourgainPlan.IonescuWainger.farey_cover_by_taoSetS

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Finset
open Work.BourgainPlan.IonescuWainger

/-- **(Σ2)** Every Farey fraction `a/q` with `1 ≤ q ≤ N`, `gcd(a,q) = 1` belongs to Tao's Ionescu–Wainger superset `Σ_N = Σ_{≤k}(taoSetS ρ N)`, `k = iwK ρ = ⌊2/ρ⌋ + 1` (Tao, Lemma `iwac`(i); the divisibility form is the landed `farey_cover_by_taoSetS`). -/
theorem sigmaN_contains_farey (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ)
    (hN : 2 ^ Work.BourgainPlan.Maximal.iwK ρ ≤ N) :
    ∀ (q a : ℕ), 1 ≤ q → q ≤ N → Nat.Coprime a q →
      Work.BourgainPlan.IonescuWainger.arcPt q (a : ℤ) ∈ Work.BourgainPlan.Maximal.iwSigma ρ N := by
  intro q a hq1 hqN _
  -- Tao's Lemma `iwac`(i): `q` divides the product of at most `k = iwK ρ` elements of `taoSetS ρ N`
  obtain ⟨A, hAS, hAcard, hdiv⟩ :=
    farey_cover_by_taoSetS ρ hρ N (by simpa [iwK] using hN) q hq1 hqN
  -- so `q ∣ Q_A`, i.e. the Farey point `a/q` lies in the torsion subgroup `Σ_{⊆A} ⊆ Σ_{≤k}`
  rw [iwSigma, sigmaLeFinset, Finset.mem_biUnion]
  refine ⟨A, ?_, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hAS, by rw [iwK]; exact hAcard⟩
  · exact arcPt_mem_sigmaSubAFinset_of_dvd hq1 (QA_ne_zero_of_subset_taoSetS hAS) hdiv (a : ℤ)

end Work.BourgainPlan.Maximal
