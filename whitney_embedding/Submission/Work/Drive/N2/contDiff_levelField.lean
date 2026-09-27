import Mathlib
import Submission.Work.Drive.N2.FieldData

/-!
# Smoothness and compact support of the ambient level field

This file proves `Work.Drive.N2.contDiff_levelField`: for `C^∞` maps
`E : ℝ^N → ℝ^N`, `G : ℝ^N → ℝ` and a compactly supported `C^∞` cutoff `χ` whose topological
support is contained in the open set `{z | auxField E G z ≠ 0}`, the level field

  `levelField E G χ z = χ z • ((‖auxField E G z‖ ^ 2)⁻¹ • dE_z (auxField E G z))`

is `C^∞` and has compact support.

The only subtlety is that `δ := ‖auxField E G ·‖ ^ 2` (equivalently `⟪auxField, auxField⟫`) may
vanish somewhere, so `δ⁻¹` is not smooth on all of `ℝ^N`; but it is smooth on the *open* set where
`δ ≠ 0`, which contains `tsupport χ`, and off `tsupport χ` the field is identically `0` in a
neighbourhood.  The case distinction is made pointwise with `contDiff_iff_contDiffAt`.
-/

open scoped Manifold ContDiff Topology
open Set Function

namespace Work.Drive.N2

/-- The gradient field of a `C^∞` function is `C^∞`. -/
theorem contDiff_grad {N : ℕ} (G : EuclideanSpace ℝ (Fin N) → ℝ)
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (grad G) := by
  unfold grad
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin N))).symm.contDiff.comp
    (hG.fderiv_right (le_refl _))

/-- The aux field `(dE)ᵀ ∇G` is `C^∞` when `E` and `G` are. -/
theorem contDiff_auxField {N : ℕ} (E : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → ℝ)
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (auxField E G) := by
  have hadj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ContinuousLinearMap.adjoint (fderiv ℝ E z)) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ)).contDiff.comp (hE.fderiv_right (le_refl _))
  unfold auxField
  exact hadj.clm_apply (contDiff_grad G hG)

/-- The map `z ↦ dE_z (auxField E G z)` is `C^∞`. -/
theorem contDiff_fderiv_auxField {N : ℕ}
    (E : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → ℝ)
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => fderiv ℝ E z (auxField E G z)) :=
  (hE.fderiv_right (le_refl _)).clm_apply (contDiff_auxField E G hE hG)

theorem contDiff_levelField {N : ℕ} (E : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → ℝ) (χ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) E) (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hcχ : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ {z | auxField E G z ≠ 0}) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (levelField E G χ) ∧
      HasCompactSupport (levelField E G χ) := by
  have haux : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (auxField E G) := contDiff_auxField E G hE hG
  have hW : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => fderiv ℝ E z (auxField E G z)) := contDiff_fderiv_auxField E G hE hG
  constructor
  · rw [contDiff_iff_contDiffAt]
    intro z
    unfold levelField
    by_cases hz : auxField E G z = 0
    · -- Off the support of `χ` (where `auxField` vanishes) the field is locally `0`.
      have hzts : z ∉ tsupport χ := fun hmem => (hsupp hmem) hz
      refine ContDiffAt.congr_of_eventuallyEq
        (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin N)))) ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzts] with y hy
      simp [hy]
    · -- Where `auxField E G z ≠ 0`, the norm square is invertible smoothly.
      have hne : (‖auxField E G z‖) ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
      exact (hχ.contDiffAt).smul
        (((ContDiffAt.norm ℝ haux.contDiffAt hz).pow 2).inv hne |>.smul hW.contDiffAt)
  · -- The support of the level field is contained in that of `χ`.
    refine hcχ.mono' ?_
    intro z hz
    by_contra hzts
    have hχz : χ z = 0 := by
      simpa using (notMem_tsupport_iff_eventuallyEq.mp hzts).eq_of_nhds
    exact hz (by simp [levelField, hχz])

end Work.Drive.N2
