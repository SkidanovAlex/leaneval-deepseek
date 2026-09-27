import Mathlib
import Submission.Work.Drive.interpSweep

/-!
# Smoothness of the interpolation sweep

`Submission/Work/Drive/interpSweep.lean` builds the chain

> `interpSweep c hc ℓ hℓ V W hV hW hne x = cappingVecPoint (level) (lift)`

from a plane presentation `(ℓ, V)` at `x 2 = 1` to a linear plane presentation `(c, W)` at `x 2 = 0`,
in the *transparent* coordinates `cappingVecPoint` of the capping space.  This file proves that it is
`C^∞` for the smooth structure `cappingCharted` (`Submission/Work/Drive/cappingCharted.lean`): the
smoothness is that of the capping point `Work.Drive.contMDiffAt_cappingVecPoint'`
(`Submission/Work/Drive/linearPlaneChart.lean`, the clash-free copy) applied to the two smooth pieces

* the multiplicatively interpolated level `x ↦ interpLevel ℓ c (mk2 (x 0) (x 1)) (x 2)`, a product of
  two `rpow`s with positive base (`ContDiffAt.rpow`), and
* the clamped straight-line interpolation of the two lifts
  `x ↦ interpLiftStep V W (mk2 (x 0) (x 1)) (x 2)`, a combination of the smooth step `interpRho`
  and the two smooth lifts.

The second result is the engine assembly: `Work.Drive.meet3Hyp_of_generic` turns the smoothness of the
three chains together with their genericity data (`Meet3Generic`) and their seam invariance
(`Work.Drive.interpSweep_seamInv`) into the packaged hypotheses `Work.Drive.Meet3Hyp` of the
manifold triple-intersection parity (`Submission/Work/Drive/planeChain.lean`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. The smooth pieces -/

/-- Precomposition of a `C^n` map on the plane parameter with the projection
`x ↦ (x 0, x 1) : ℝ³ → ℝ²` of the sweep's parameter space. -/
lemma contDiff_comp_mk2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} {f : EuclideanSpace ℝ (Fin 2) → F} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x : EuclideanSpace ℝ (Fin 3) => f (mk2 (x 0) (x 1))) :=
  hf.comp (mk2CLM.contDiff (n := n))

/-- The reversed smooth step `interpRho` is `C^∞`. -/
lemma interpRho_contDiff : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) interpRho := by
  unfold interpRho
  fun_prop

/-- The second coordinate `x ↦ x 2` of the parameter space is `C^∞`. -/
lemma contDiff_coord_two :
    ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x : EuclideanSpace ℝ (Fin 3) => x 2) := by
  fun_prop

/-- **The interpolated level is `C^∞`**: it is a product of two `rpow`s, whose bases are the positive
level functions `ℓ` and the constant `c`. -/
lemma contDiffAt_interpLevel (c : ℝ) (hc : 0 < c) (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hℓ : ∀ y, 0 < ℓ y) (hℓs : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) ℓ)
    (x₀ : EuclideanSpace ℝ (Fin 3)) :
    ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x => interpLevel ℓ c (mk2 (x 0) (x 1)) (x 2)) x₀ := by
  have hexp : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x : EuclideanSpace ℝ (Fin 3) => interpRho (x 2)) x₀ :=
    (interpRho_contDiff.comp contDiff_coord_two).contDiffAt
  have h1 : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        (ℓ (mk2 (x 0) (x 1))) ^ (1 - interpRho (x 2))) x₀ :=
    ContDiffAt.rpow ((contDiff_comp_mk2 hℓs).contDiffAt) (contDiffAt_const.sub hexp)
      (ne_of_gt (hℓ _))
  have h2 : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x : EuclideanSpace ℝ (Fin 3) => c ^ (interpRho (x 2))) x₀ :=
    ContDiffAt.rpow contDiffAt_const hexp (ne_of_gt hc)
  simpa only [interpLevel] using h1.mul h2

/-- **The clamped straight-line interpolation of two `C^∞` lifts is `C^∞` at every point.** -/
lemma contDiffAt_interpLiftStep (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3)
    (hV : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) V)
    (hW : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) W) (x₀ : EuclideanSpace ℝ (Fin 3)) :
    ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x => interpLiftStep V W (mk2 (x 0) (x 1)) (x 2)) x₀ := by
  have hVx : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x : EuclideanSpace ℝ (Fin 3) => V (mk2 (x 0) (x 1))) x₀ :=
    (contDiff_comp_mk2 hV).contDiffAt
  have hWx : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x : EuclideanSpace ℝ (Fin 3) => W (mk2 (x 0) (x 1))) x₀ :=
    (contDiff_comp_mk2 hW).contDiffAt
  have hρ : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x : EuclideanSpace ℝ (Fin 3) => interpRho (x 2)) x₀ :=
    (interpRho_contDiff.comp contDiff_coord_two).contDiffAt
  have h1 : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x : EuclideanSpace ℝ (Fin 3) =>
        (1 - interpRho (x 2)) • V (mk2 (x 0) (x 1))) x₀ :=
    (contDiffAt_const.sub hρ).smul hVx
  have h2 : ContDiffAt ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun x : EuclideanSpace ℝ (Fin 3) => interpRho (x 2) • W (mk2 (x 0) (x 1))) x₀ :=
    hρ.smul hWx
  simpa only [interpLiftStep] using h1.add h2

/-! ## 2. The smoothness of the interpolation sweep -/

/-- **Smoothness of the interpolation sweep** (`Submission/Work/Drive/interpSweep.lean`): the chain
running from a plane presentation `(ℓ, V)` at `x 2 = 1` to a linear plane presentation `(c, W)` at
`x 2 = 0`, through the transparent coordinates `cappingVecPoint` of the capping space, is `C^∞` (for
the `cappingCharted` smooth structure on `CappingSpace`) as soon as the level function `ℓ` and the two
lifts `V`, `W` are `C^∞`, the level is positive, the lifts are non-vanishing and the straight-line
interpolation `interpLift V W` does not vanish on the parameter interval.  Please place the result in
`namespace Work.Drive`.  Use the clash-free tool `Work.Drive.contMDiffAt_cappingVecPoint'`
(`Submission/Work/Drive/linearPlaneChart.lean`) rather than the copy in `StripDiskAux.lean`, which
cannot be imported together with `interpSweep`.  Bonus if the API allows: the engine assembly obtained
by applying `Work.Drive.meet3Hyp_of_generic` to this result and to
`Work.Drive.interpSweep_seamInv` (`Work.Drive.Meet3Hyp`, `Work.Drive.meet3Hyp_of_generic` are in
`Submission/Work/Drive/planeChain.lean`). -/
theorem contMDiff_interpSweep (c : ℝ) (hc : 0 < c) (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hℓ : ∀ y, 0 < ℓ y) (V W : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (hV : ∀ y, V y ≠ 0) (hW : ∀ y, W y ≠ 0)
    (hne : ∀ y t, 0 ≤ t → t ≤ 1 → Work.Drive.interpLift V W y t ≠ 0)
    (hℓs : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) (((⊤ : ℕ∞) : WithTop ℕ∞)) ℓ)
    (hVs : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (((⊤ : ℕ∞) : WithTop ℕ∞)) V)
    (hWs : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (((⊤ : ℕ∞) : WithTop ℕ∞)) W) :
    letI := Work.Drive.cappingCharted
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (((⊤ : ℕ∞) : WithTop ℕ∞))
      (Work.Drive.interpSweep c hc ℓ hℓ V W hV hW hne) := by
  have hℓc : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) ℓ := hℓs.contDiff
  have hVc : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) V := hVs.contDiff
  have hWc : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) W := hWs.contDiff
  let r : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun x => interpLevel ℓ c (mk2 (x 0) (x 1)) (x 2)
  let L : EuclideanSpace ℝ (Fin 3) → Eucl 3 :=
    fun x => interpLiftStep V W (mk2 (x 0) (x 1)) (x 2)
  have hr : ∀ x, 0 < r x := fun x => interpLevel_pos ℓ c hℓ hc _ _
  have hL : ∀ x, L x ≠ 0 := fun x => interpLiftStep_ne_zero V W hV hW hne _ _
  have hrs : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) (((⊤ : ℕ∞) : WithTop ℕ∞)) r :=
    fun x => (contDiffAt_interpLevel c hc ℓ hℓ hℓc x).contMDiffAt
  have hLs : ContMDiff (𝓡 3) 𝓘(ℝ, Eucl 3) (((⊤ : ℕ∞) : WithTop ℕ∞)) L :=
    fun x => (contDiffAt_interpLiftStep V W hVc hWc x).contMDiffAt
  exact fun x => contMDiffAt_cappingVecPoint' r L x hr hL (hrs x) (hLs x)

/-! ## 3. The engine assembly

`Work.Drive.meet3Hyp_of_generic` (`planeChain.lean`) needs the smoothness of the three chains and
their seam invariance; both are supplied, for the interpolation sweeps, by the theorem above and by
`Work.Drive.interpSweep_seamInv`.  The genericity data (`Meet3Generic`: triple transversality, the
face condition, the radial non-degeneracy) is the only input left to the caller — exactly as for the
clamped radial sweeps (`Work.Drive.meet3Hyp_clampedSweeps`, `clampedSweep.lean`).

`Work.Drive.meet3Hyp_interpSweeps` (`interpSweep.lean`, §9) already packages the assembly, but takes
the smoothness of the three sweeps as a hypothesis; the corollary below *discharges* it from the
smoothness of the presentations, so that the chains of `INTERP_DIAGONAL_NOTES.md` §5 are engine-ready
from the data `(ℓ_k, V_k, W_k)` alone. -/

section Engine

-- The transparent smooth structure of the capping space, as a local instance: it is the structure
-- under which the smoothness statements of this file are made.
set_option warn.classDefReducibility false in
attribute [local instance] Work.Drive.cappingCharted
set_option warn.classDefReducibility false in
attribute [local instance] Work.Drive.isManifold_cappingCharted

/-- **The three interpolation sweeps satisfy the engine's hypotheses, from the smoothness of the
presentations**: this is `Work.Drive.meet3Hyp_interpSweeps` (`interpSweep.lean`) with its hypothesis
`hsm` discharged by `Work.Drive.contMDiff_interpSweep`.  So the genericity data (`Meet3Generic`) is
the only input the endgame has to supply. -/
theorem meet3Hyp_interpSweeps_of_contMDiff (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k)
    (ℓ : Fin 3 → EuclideanSpace ℝ (Fin 2) → ℝ) (hℓ : ∀ k y, 0 < ℓ k y)
    (V W : Fin 3 → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4))
    (hV : ∀ k y, V k y ≠ 0) (hW : ∀ k y, W k y ≠ 0)
    (hne : ∀ k y t, 0 ≤ t → t ≤ 1 → interpLift (V k) (W k) y t ≠ 0)
    (hℓsm : ∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) (((⊤ : ℕ∞) : WithTop ℕ∞)) (ℓ k))
    (hVsm : ∀ k, ContMDiff (𝓡 2) (𝓡 4) (((⊤ : ℕ∞) : WithTop ℕ∞)) (V k))
    (hWsm : ∀ k, ContMDiff (𝓡 2) (𝓡 4) (((⊤ : ℕ∞) : WithTop ℕ∞)) (W k))
    (hℓseam : ∀ k y, onSeam2 y → ℓ k (seamInv2 y) = ℓ k y)
    (hVseam : ∀ k y, onSeam2 y → V k (seamInv2 y) = - V k y)
    (hWseam : ∀ k y, onSeam2 y → W k (seamInv2 y) = - W k y)
    (hgen : Meet3Generic CappingSpace
      (fun k => interpSweep (c k) (hc k) (ℓ k) (hℓ k) (V k) (W k) (hV k) (hW k) (hne k))) :
    Meet3Hyp CappingSpace
      (fun k => interpSweep (c k) (hc k) (ℓ k) (hℓ k) (V k) (W k) (hV k) (hW k) (hne k)) :=
  meet3Hyp_interpSweeps c hc ℓ hℓ V W hV hW hne hℓseam hVseam hWseam
    (fun k => contMDiff_interpSweep (c k) (hc k) (ℓ k) (hℓ k) (V k) (W k) (hV k) (hW k)
      (hne k) (hℓsm k) (hVsm k) (hWsm k)) hgen

end Engine

end

end Work.Drive
