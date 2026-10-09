import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.twistLayer
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.step4_transport_of_sha13
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Involutions in the fixing subgroup die on any cocycle that vanishes on a set of involution
representatives.**  A `1`-cocycle `y` for the `Gal(K/ℚ)`-action `restrict K` that is zero on a
Finset `C` containing a conjugate of every involution of `G_ℚ` vanishes at each involution lying in
`K.fixingSubgroup`.

The point is the conjugation formula for a `1`-cocycle: if `c = σ * c₀ * σ⁻¹` then
`y c = y σ + (restrict K σ) • y c₀ - (restrict K c) • y σ`.  Since `y c₀ = 0` and `restrict K c = 1`
(because `c ∈ K.fixingSubgroup`), this collapses to `y σ - y σ = 0`. -/
theorem step4_involution_vanish (p : ℕ)
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ)
    (C : Finset SSGRoute.GalQ)
    (y : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j)
    (hy : SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) ⊤ y)
    (hC : ∀ c ∈ C, y c = 0)
    (hCcov : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → ∃ c₀ ∈ C, ∃ σ : SSGRoute.GalQ, c = σ * c₀ * σ⁻¹) :
    ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0 := by
  intro c hc hc2
  obtain ⟨c₀, hc₀C, σ, hσ⟩ := hCcov c hc2
  have hy₀ : y c₀ = 0 := hC c₀ hc₀C
  have hconj : y c = y σ + (restrict K) σ • y c₀ - (restrict K) c • y σ := by
    have h := step4_cocycle_conj hy σ c₀
    rwa [← hσ] at h
  rw [hy₀, smul_zero, add_zero, restrict_eq_one_of_mem_fixingSubgroup K hc, one_smul,
    sub_self] at hconj
  exact hconj

end Work.SSGRoute
