import Mathlib
import Submission.Work.TMComp.RedC8.ell_le_lyap
import Submission.Work.TMComp.Kotani.lyap_usc

namespace Work.TMComp.RedC8

open Filter Topology Set

/-- If the Lyapunov exponent vanishes on the real interval `(a,b)`, then for every `x ∈ (a,b)`
the averaged log-modulus `ℓ` tends to `0` as the energy approaches `x` from the upper half
plane.  Indeed `ℓ ≤ lyap` on the upper half plane (`ell_le_lyap`) and `lyap` is upper
semicontinuous (`lyap_usc`), so near the real point `x` we have `lyap E < η`, whence
`ℓ E ≤ lyap E < η`. -/
theorem ell_tendsto_zero_near_real (α lam a b : ℝ)
    (hL : ∀ E ∈ Set.Ioo a b, Work.TMContract.lyap α lam (E : ℂ) = 0) :
    ∀ x ∈ Set.Ioo a b, ∀ η : ℝ, 0 < η →
      ∀ᶠ E in nhdsWithin (x : ℂ) {z : ℂ | 0 < z.im},
        Work.TMComp.Kotani.ell α lam E ≤ η := by
  intro x hx η hη
  have husc : ∀ᶠ E in nhds ((x : ℂ)), Work.TMContract.lyap α lam E < η := by
    have h := (Work.TMComp.Kotani.lyap_usc α lam).2 (x : ℂ) η hη
    rw [hL x hx] at h
    simpa using h
  filter_upwards [husc.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with E hE hmem
  exact le_trans (ell_le_lyap α lam E hmem) (le_of_lt hE)

end Work.TMComp.RedC8
