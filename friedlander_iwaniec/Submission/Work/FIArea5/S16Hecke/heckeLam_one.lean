import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- A primary Gaussian integer of norm `1` is a unit of `ℤ[i]` of norm `1`, hence `1`
(`Commons.NumberTheory.GaussianInt.units_classification`; the other three units,
`-1`, `i`, `-i`, are not primary). -/
lemma isPrimary_of_gnorm_eq_one {z : GaussianInt} (hz : IsPrimary z) (h : gnorm z = 1) :
    z = 1 :=
  isPrimary_unit hz
    (Zsqrtd.norm_eq_one_iff.mp (by simpa [Work.FIPlan.gnorm] using h))

/-- **(16.30) at `n = 1`.** The only primary Gaussian integer of norm `1` is `1`, so the Hecke
eigenvalue at `1` is `ψ(1) = χ(1)`. -/
theorem heckeLam_one (chi : GaussianInt → ℂ) (k : ℤ) : heckeLam chi k 1 = chi 1 := by
  classical
  unfold heckeLam
  -- the filtered box over which `heckeLam` sums is the singleton `{1}`
  have hS : (gBox ((1 : ℕ) : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = 1)
      = {(1 : GaussianInt)} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter, mem_gBox_iff, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨?_, ?_⟩, isPrimary_one, gnorm_one⟩ <;> simp
    · intro z hz
      rw [Finset.mem_filter] at hz
      exact isPrimary_of_gnorm_eq_one hz.2.1 hz.2.2
  rw [hS, Finset.sum_singleton]
  exact psi_one chi k

end

end Work.FIArea5.S16Hecke
