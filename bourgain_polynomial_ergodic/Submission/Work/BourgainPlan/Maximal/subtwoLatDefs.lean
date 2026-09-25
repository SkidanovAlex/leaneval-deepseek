/-
# Definitions for the lattice maximal-vs-values principle (the corrected `hLattice`)

Owner: the `subtwo` owner.  See `LATTICE_PRINCIPLE_STATUS.md` (same directory) for the statement,
the refutation of the uncorrected binder in `Submission/Work/Maximal/`, and the verified proof
route of the corrected one.
-/
import Mathlib
import Submission.Work.Maximal.band_schwartz_fourier_bump

open MeasureTheory
open scoped BigOperators ENNReal FourierTransform

namespace Work.BourgainPlan.Maximal

/-- **The centred two-sided discrete Hardy--Littlewood maximal function** on `ℤ`:
`M a x = ⨆_{N>0} N⁻¹ Σ_{|j-x| ≤ N} a j`.  Its `ℓᵖ` boundedness (`p > 1`) is
`latDiscMaxC_lintegral_rpow_le`; it is the object that controls the *large-interval* averages of the
maximal function of a band-limited function in the two-regime proof of `mstLatticePrinciple`. -/
noncomputable def latDiscMaxC (a : ℤ → ENNReal) (x : ℤ) : ENNReal :=
  ⨆ N : ℕ, ⨆ (_ : 0 < N), ((N : ENNReal))⁻¹ * ∑ j ∈ Finset.Icc (x - (N : ℤ)) (x + (N : ℤ)), a j

/-- The auxiliary summable lattice kernel `u ↦ ofReal ((1+|u|)^{-2})` of the two-regime estimate: it
carries the contribution of the *far* lattice points (those at distance `> 3L` from the averaging
interval of length `L`), where the sampling kernel `ψ` has decayed. -/
noncomputable def latKernel (u : ℝ) : ENNReal := ENNReal.ofReal (((1 + |u|) : ℝ) ^ (-2 : ℝ))

/-- The fixed sampling bump of band `1/4`: a Schwartz function `ψ` with `𝓕ψ = 1` on `[-1/4,1/4]`
and `𝓕ψ = 0` off `[-1/2,1/2]`.  It is the kernel in the sampling/reproduction identity
`H y = ∑'_j ψ (y-j) H j` for continuous band-`1/4` `L¹` functions (`lat_sampling_reproduce`). -/
noncomputable def latPsi : SchwartzMap ℝ ℂ :=
  (Work.Maximal.band_schwartz_fourier_bump (c0 := 1 / 4) (by norm_num) (by norm_num)).choose

theorem latPsi_one : ∀ ξ ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4),
    FourierTransform.fourier (⇑latPsi) ξ = 1 :=
  (Work.Maximal.band_schwartz_fourier_bump (c0 := 1 / 4)
    (by norm_num) (by norm_num)).choose_spec.1

theorem latPsi_zero : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) →
    FourierTransform.fourier (⇑latPsi) ξ = 0 :=
  (Work.Maximal.band_schwartz_fourier_bump (c0 := 1 / 4)
    (by norm_num) (by norm_num)).choose_spec.2

end Work.BourgainPlan.Maximal
