import Mathlib
import Submission.Work.TMComp.PerfectDefs
import Submission.Work.TMC7Core.Scale.spectral_continuity
import Submission.Work.TMComp.Perfect.amoOp_covariance
import Submission.Work.TMComp.Perfect.exists_int_approx
import Submission.Work.TMComp.Perfect.exists_spectrum_close

/-!
# Phase independence of the almost Mathieu spectrum for irrational frequency

For irrational frequency `α` the spectrum of the almost Mathieu operator does not depend on
the phase `θ`.  The argument is the classical one, and has three ingredients:

* *Covariance*: the shift `sh k` intertwines `amoOp θ` with `amoOp (θ + kα)`
  (`amoOp_covariance`, proved in the sibling module `amoOp_covariance.lean`), so that
  `amoOp (θ + kα) = sh k * amoOp θ * (sh k)⁻¹` is a conjugate of `amoOp θ` by a unit and
  therefore has the same spectrum;
* *Density of the orbit*: for irrational `α` the set `ℤα + ℤ` is dense in `ℝ`, so any phase
  `θ'` can be approximated by a point `θ + mα + k` of the orbit of `θ` (`exists_int_approx`);
* *Continuity in the phase*: two self-adjoint operators at distance `≤ γ` have spectra at
  Hausdorff distance `≤ γ` (`exists_spectrum_close`), and the hypothesis `hnc` bounds the
  distance between `amoOp θ₁` and `amoOp θ₂` by `4π|λ| |θ₁ - θ₂|`.

Combining the three gives for every spectral point `z` of `amoOp θ` and every `ε > 0` a
spectral point of `amoOp θ'` within `ε` of `z`; as the spectrum of `amoOp θ'` is closed,
`z` itself is a spectral point of `amoOp θ'`.
-/

open LeanEval.Analysis.TenMartini
open Work.TMContract (amoPot)

noncomputable section

namespace Work.TMComp.Perfect

/-! ## Periodicity in the phase -/

/-- The almost Mathieu operator is periodic in the phase with period one: shifting the phase
by an integer does not change the operator. -/
theorem amoOp_add_int (α lam : ℝ) (θ : ℝ) (k : ℤ) :
    amoOp α lam (θ + (k : ℝ)) = amoOp α lam θ := by
  have hp : ∀ n : ℤ, potC α lam (θ + (k : ℝ)) n = potC α lam θ n := by
    intro n
    have harg : 2 * Real.pi * ((θ + (k : ℝ)) + (n : ℝ) * α)
        = 2 * Real.pi * (θ + (n : ℝ) * α) + k * (2 * Real.pi) := by ring
    rw [potC_apply, potC_apply, amoPot, amoPot, harg, Real.cos_add_int_mul_two_pi]
  unfold amoOp
  rw [diag_congr (potC_bound α lam (θ + (k : ℝ))) (potC_bound α lam θ) hp]

/-- The spectrum of the almost Mathieu operator is invariant under integer phase shifts. -/
theorem spectrum_amoOp_add_int (α lam θ : ℝ) (k : ℤ) :
    spectrum ℂ (amoOp α lam (θ + (k : ℝ))) = spectrum ℂ (amoOp α lam θ) := by
  rw [amoOp_add_int]

/-! ## The shift as a unit of the operator algebra -/

/-- The shift `sh k` on `ℓ²(ℤ)`, as a unit of the algebra of bounded operators (with inverse
`sh (-k)`). -/
noncomputable def shUnit (k : ℤ) : (EllTwo →L[ℂ] EllTwo)ˣ where
  val := sh k
  inv := sh (-k)
  val_inv := by rw [sh_comp, add_neg_cancel, sh_zero]
  inv_val := by rw [sh_comp, neg_add_cancel, sh_zero]

theorem shUnit_val (k : ℤ) : (↑(shUnit k) : EllTwo →L[ℂ] EllTwo) = sh k := rfl

theorem shUnit_inv_val (k : ℤ) : (↑((shUnit k)⁻¹) : EllTwo →L[ℂ] EllTwo) = sh (-k) := rfl

/-- The almost Mathieu operator at phase `θ + kα` is the conjugate of the operator at phase
`θ` by the shift unit `sh k`. -/
theorem amoOp_orbit_conj (α lam θ : ℝ) (k : ℤ) :
    amoOp α lam (θ + (k : ℝ) * α)
      = (↑(shUnit k) : EllTwo →L[ℂ] EllTwo) * amoOp α lam θ * ↑((shUnit k)⁻¹) := by
  have h := amoOp_covariance α lam θ k
  have hinv : sh k * sh (-k) = 1 := by rw [sh_comp, add_neg_cancel, sh_zero]
  rw [shUnit_val, shUnit_inv_val]
  calc amoOp α lam (θ + (k : ℝ) * α)
      = amoOp α lam (θ + (k : ℝ) * α) * (sh k * sh (-k)) := by rw [hinv, mul_one]
    _ = amoOp α lam (θ + (k : ℝ) * α) * sh k * sh (-k) := by rw [mul_assoc]
    _ = sh k * amoOp α lam θ * sh (-k) := by rw [← h]

/-- The spectrum of the almost Mathieu operator is invariant along the orbit `θ + ℤα`. -/
theorem spectrum_amoOp_orbit (α lam θ : ℝ) (k : ℤ) :
    spectrum ℂ (amoOp α lam (θ + (k : ℝ) * α)) = spectrum ℂ (amoOp α lam θ) := by
  rw [amoOp_orbit_conj]
  exact spectrum.units_conjugate (R := ℂ) (a := amoOp α lam θ) (u := shUnit k)

/-! ## One inclusion -/

/-- One direction of phase independence: a spectral point at phase `θ` is a spectral point at
phase `θ'`.  The orbit of `θ` under the irrational rotation is dense, so `θ` can be moved to
within `ε` of `θ'` by a shift `θ ↦ θ + mα + k` which does not change the spectrum; the
operators at the two nearby phases are `ε`-close in norm, and `exists_spectrum_close`
transfers spectral points. -/
theorem mem_spectrum_of_irrational_phase (α lam : ℝ) (hα : Irrational α) (θ θ' : ℝ)
    (hsa : ∀ θ₀ : ℝ, IsSelfAdjoint (amoOp α lam θ₀))
    (hnc : ∀ θ₁ θ₂ : ℝ, ‖amoOp α lam θ₁ - amoOp α lam θ₂‖
      ≤ 4 * Real.pi * |lam| * |θ₁ - θ₂|)
    {z : ℂ} (hz : z ∈ spectrum ℂ (amoOp α lam θ)) :
    z ∈ spectrum ℂ (amoOp α lam θ') := by
  have hcl : z ∈ closure (spectrum ℂ (amoOp α lam θ')) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set C : ℝ := 4 * Real.pi * |lam| with hCdef
    have hCnn : 0 ≤ C := by rw [hCdef]; positivity
    have hε'pos : 0 < ε / (2 * (C + 1)) := by positivity
    obtain ⟨m, k, hmk⟩ := exists_int_approx α hα (θ' - θ) hε'pos
    have hphase : |(θ + (m : ℝ) * α + (k : ℝ)) - θ'| < ε / (2 * (C + 1)) := by
      have heq : (θ + (m : ℝ) * α + (k : ℝ)) - θ' = (m : ℝ) * α + (k : ℝ) - (θ' - θ) := by
        ring
      rw [heq]; exact hmk
    have hnorm : ‖amoOp α lam (θ + (m : ℝ) * α + (k : ℝ)) - amoOp α lam θ'‖ ≤ ε / 2 := by
      have h1 : ‖amoOp α lam (θ + (m : ℝ) * α + (k : ℝ)) - amoOp α lam θ'‖
          ≤ C * |(θ + (m : ℝ) * α + (k : ℝ)) - θ'| := by
        rw [hCdef]; exact hnc _ _
      have h2 : C * |(θ + (m : ℝ) * α + (k : ℝ)) - θ'| ≤ ε / 2 := by
        have h3 : |(θ + (m : ℝ) * α + (k : ℝ)) - θ'| ≤ ε / (2 * (C + 1)) := hphase.le
        calc C * |(θ + (m : ℝ) * α + (k : ℝ)) - θ'|
            ≤ C * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_left h3 hCnn
          _ ≤ (C + 1) * (ε / (2 * (C + 1))) := by
              exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = ε / 2 := by field_simp
      linarith
    have hspec : spectrum ℂ (amoOp α lam (θ + (m : ℝ) * α + (k : ℝ)))
        = spectrum ℂ (amoOp α lam θ) := by
      rw [spectrum_amoOp_add_int, spectrum_amoOp_orbit]
    have hzmem : z ∈ spectrum ℂ (amoOp α lam (θ + (m : ℝ) * α + (k : ℝ))) := by
      rw [hspec]; exact hz
    obtain ⟨z', hz'mem, hclose⟩ := exists_spectrum_close (hsa _) (hsa θ') hnorm z hzmem
    exact ⟨z', hz'mem, by rw [dist_eq_norm]; linarith⟩
  exact (spectrum.isClosed (𝕜 := ℂ) (amoOp α lam θ')).closure_eq ▸ hcl

/-! ## Phase independence -/

/-- For irrational frequency the spectrum of the almost Mathieu operator does not depend on the
phase.  (`hsa` and `hnc` are the self-adjointness and the phase-Lipschitz bound for the family;
`Work.TMC7Core.Scale.exists_approx_eigenvector` and `Work.TMC7Core.Scale.norm_le_of_spectrum_avoid`
in `TMC7Core/Scale/spectral_continuity.lean` are proved and useful here.) -/
theorem phase_independence (α lam : ℝ) (hα : Irrational α) (θ θ' : ℝ)
    (hsa : ∀ θ₀ : ℝ, IsSelfAdjoint (Work.TMComp.Perfect.amoOp α lam θ₀))
    (hnc : ∀ θ₁ θ₂ : ℝ, ‖Work.TMComp.Perfect.amoOp α lam θ₁ - Work.TMComp.Perfect.amoOp α lam θ₂‖
      ≤ 4 * Real.pi * |lam| * |θ₁ - θ₂|) :
    spectrum ℂ (Work.TMComp.Perfect.amoOp α lam θ) = spectrum ℂ (Work.TMComp.Perfect.amoOp α lam θ') :=
  Set.Subset.antisymm
    (fun _z hz => mem_spectrum_of_irrational_phase α lam hα θ θ' hsa hnc hz)
    (fun _z hz => mem_spectrum_of_irrational_phase α lam hα θ' θ hsa hnc hz)

end Work.TMComp.Perfect
