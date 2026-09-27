import Mathlib
import Submission.Work.Drive.CapSmooth.sweepChainSmooth
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff
import Submission.Work.Drive.contMDiffAt_cappingSpace_configPiece
import Submission.Work.Drive.planeChain

/-!
# The *radial* sweep: a chain whose bottom face is a level, not a dilated plane

`Work.Drive.sweepChain a ha P` presents the sweep of a plane by *scaling* it: its `x 2 = 0` face is the
dilated plane `Work.Drive.scaleCapping (pos a ha) (P ·)`
(`Work.Drive.sweepChain_face_zero`), which is ambiently isotopic to the plane itself (`scaleCapping` is
a flow).  For the *end contribution* of the chain route (`ENDS_AND_SEAMS_NOTES.md` §2,
`RADIAL_CHAIN_NOTES.md`) the bottom face must instead be a `2`-cycle lying in **one level**
`{c} × ℝP³`: the sweep has to be a *radial* one, running from the plane down to the level `c` along
the radial coordinate, keeping the projective class fixed.  That is the set
`Work.Drive.radialBelow` (`Submission/Work/Drive/radialSweep.lean`), which until now existed only as a
*set*, not as a parametrised chain.

This file turns it into a box map.  With `levelOf p = (cappingSpaceHomeoProj p).1` the radial
coordinate of a point of the capping space and `ψ` a smooth cutoff with `ψ 0 = 1`, `ψ 1 = 0`
(e.g. `ψ = fun t => 1 - foldFun t`),

> `clampedSweep c ψ P x = scaleCapping (pos (clampScale c ψ P x) _) (P (x 0, x 1))`,
> `clampScale c ψ P x = exp (ψ (x 2) * (log c - log (levelOf (P (x 0, x 1)))))`,

so that

* (`clampedSweep_face_one`) at `x 2 = 1` the scale is `exp 0 = 1` and the face is the **plane**
  `P (x 0, x 1)` itself;
* (`clampedSweep_face_zero`) at `x 2 = 0` the scale is `exp (log c - log r) = c / r` and the face is
  the **shadow** `shadow c (P (x 0, x 1))`, the point of the level `c` with the same projective class
  — `RADIAL_CHAIN_NOTES.md`'s `π (P)` with multiplicity;
* (`clampedSweep_seamInv`) it inherits the seam invariance of `P` (`sweepChain_seamInv`'s argument);
* (`contMDiff_clampedSweep`) it is `C^∞` whenever `P` is, by
  `Work.Drive.CapSmooth.contMDiffAt_scaleCapping`, the scale being smooth by
  `contMDiff_clampScale` (which uses `Work.Drive.contMDiffAt_halfLineProjective_iff` to see that
  `log` of the radial coordinate of a smooth map into the capping space is smooth).

So `clampedSweep c ψ P` is a `Meet3Hyp`-legitimate chain (`Work.Drive.meet3Hyp_of_generic`) with the
*asymmetric* faces the end contribution needs, exactly as `ENDS_AND_SEAMS_NOTES.md` §2 prescribes.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- The radial coordinate ("level") of a point of the capping space. -/
def levelOf (p : CappingSpace) : ℝ := ((cappingSpaceHomeoProj p).1 : ℝ)

@[simp] lemma levelOf_pos (p : CappingSpace) : 0 < levelOf p := (cappingSpaceHomeoProj p).1.2

/-- **The shadow of a point on a level**: the point of the level `c` with the same projective class. -/
def shadow (c : ℝ) (hc : 0 < c) (p : CappingSpace) : CappingSpace :=
  scaleCapping (pos (c / levelOf p) (div_pos hc (levelOf_pos p))) p

/-- The level of the shadow is `c`. -/
theorem levelOf_shadow (c : ℝ) (hc : 0 < c) (p : CappingSpace) :
    levelOf (shadow c hc p) = c := by
  rw [shadow, levelOf, CapSmooth.cappingSpaceHomeoProj_scaleCapping]
  exact div_mul_cancel₀ c (ne_of_gt (levelOf_pos p))

/-- The projective class of the shadow is that of the point. -/
theorem cls_shadow (c : ℝ) (hc : 0 < c) (p : CappingSpace) :
    (cappingSpaceHomeoProj (shadow c hc p)).2 = (cappingSpaceHomeoProj p).2 := by
  rw [shadow, CapSmooth.cappingSpaceHomeoProj_scaleCapping]

/-- **The radial scale of the clamped sweep**: the factor interpolating between `1` (at `x 2 = 1`,
when `ψ 1 = 0`) and `c / levelOf (P ·)` (at `x 2 = 0`, when `ψ 0 = 1`). -/
def clampScale (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Real.exp (ψ (x 2) * (Real.log c - Real.log (levelOf (P (mk2 (x 0) (x 1))))))

lemma clampScale_pos (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (x : EuclideanSpace ℝ (Fin 3)) : 0 < clampScale c ψ P x := Real.exp_pos _

/-- **The radial sweep of a plane presentation**, as a chain: the plane at `x 2 = 1`, the level `c` at
`x 2 = 0`. -/
def clampedSweep (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) :
    EuclideanSpace ℝ (Fin 3) → CappingSpace :=
  fun x => scaleCapping (pos (clampScale c ψ P x) (clampScale_pos c ψ P x))
    (P (mk2 (x 0) (x 1)))

@[simp] lemma clampedSweep_apply (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3)) :
    clampedSweep c ψ P x
      = scaleCapping (pos (clampScale c ψ P x) (clampScale_pos c ψ P x))
        (P (mk2 (x 0) (x 1))) := rfl

/-- Dilation by the scale `1` is the identity, with the positivity proof carried along. -/
lemma scaleCapping_pos_one {h : 0 < (1 : ℝ)} (p : CappingSpace) :
    scaleCapping (pos 1 h) p = p := by
  rw [show pos (1 : ℝ) h = pos 1 one_pos from Subtype.ext rfl, scaleCapping_one]
  rfl

/-- **The `x 2 = 1` face of the radial sweep is the plane itself.** -/
theorem clampedSweep_face_one (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (hψ : ψ 1 = 0)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x 2 = 1) :
    clampedSweep c ψ P x = P (mk2 (x 0) (x 1)) := by
  have hsc : clampScale c ψ P x = 1 := by
    rw [clampScale, hx, hψ, zero_mul, Real.exp_zero]
  have hpos : pos (clampScale c ψ P x) (clampScale_pos c ψ P x) = pos 1 one_pos :=
    Subtype.ext hsc
  rw [clampedSweep_apply, hpos, scaleCapping_pos_one]

/-- **The `x 2 = 0` face of the radial sweep is the shadow of the plane on the level `c`.** -/
theorem clampedSweep_face_zero (c : ℝ) (hc : 0 < c) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (hψ : ψ 0 = 1)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x 2 = 0) :
    clampedSweep c ψ P x
      = shadow c hc (P (mk2 (x 0) (x 1))) := by
  have hr : 0 < levelOf (P (mk2 (x 0) (x 1))) := levelOf_pos _
  have hscale : clampScale c ψ P x = c / levelOf (P (mk2 (x 0) (x 1))) := by
    rw [clampScale, hx, hψ, one_mul, Real.exp_sub, Real.exp_log hc, Real.exp_log hr]
  have hpos : pos (clampScale c ψ P x) (clampScale_pos c ψ P x)
      = pos (c / levelOf (P (mk2 (x 0) (x 1)))) (div_pos hc hr) :=
    Subtype.ext hscale
  rw [clampedSweep_apply, hpos, shadow]

/-- **The radial sweep inherits the seam invariance of the plane.** -/
theorem clampedSweep_seamInv (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P y = P (seamInv2 y))
    (x : EuclideanSpace ℝ (Fin 3)) (hx : onSeam x) :
    clampedSweep c ψ P x = clampedSweep c ψ P (seamInv x) := by
  have hp : mk2 ((seamInv x) 0) ((seamInv x) 1) = seamInv2 (mk2 (x 0) (x 1)) := mk2_seamInv x
  have h2 : (seamInv x) 2 = x 2 := seamInv_apply_two x
  have hPa : P (mk2 ((seamInv x) 0) ((seamInv x) 1)) = P (mk2 (x 0) (x 1)) := by
    rw [hp]
    exact (hP (mk2 (x 0) (x 1)) hx).symm
  have hsc : clampScale c ψ P (seamInv x) = clampScale c ψ P x := by
    rw [clampScale, clampScale, h2, hPa]
  have hpos : pos (clampScale c ψ P (seamInv x)) (clampScale_pos c ψ P (seamInv x))
      = pos (clampScale c ψ P x) (clampScale_pos c ψ P x) := Subtype.ext hsc
  rw [clampedSweep_apply, clampedSweep_apply, hpos, hPa]

/-! ## The smoothness of the radial sweep -/

section Smoothness

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.halfLineProjectiveCharted Work.Drive.isManifold_halfLineProjectiveCharted
  Work.Drive.t2Space_cappingSpace

/-- The coordinate projection `x ↦ (x 0, x 1)` of `ℝ³` onto `ℝ²` is smooth. -/
lemma contMDiffAt_mk2_proj (x : EuclideanSpace ℝ (Fin 3)) :
    ContMDiffAt (𝓡 3) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : EuclideanSpace ℝ (Fin 3) => mk2 (w 0) (w 1)) x := by
  rw [contMDiffAt_iff_contDiffAt]
  have hf : (fun w : EuclideanSpace ℝ (Fin 3) => mk2 (w 0) (w 1))
      = fun w => WithLp.toLp 2 (![w 0, w 1] : Fin 2 → ℝ) := rfl
  rw [hf, contDiffAt_piLp (p := 2) (E := fun _ : Fin 2 => ℝ)]
  intro i
  fin_cases i
  · simpa using (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 0)).contDiff.contDiffAt :
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : EuclideanSpace ℝ (Fin 3) => w 0) x)
  · simpa using (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 1)).contDiff.contDiffAt :
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : EuclideanSpace ℝ (Fin 3) => w 1) x)

/-- **The logarithm of the radial coordinate of a smooth map into the capping space is smooth.**  The
radial coordinate is only a chart-dependent function on the capping space; the content of the lemma is
that `Work.Drive.expHomeo.symm ∘ (cappingSpaceHomeoProj ·).1` is smooth, which is the first component
of `Work.Drive.contMDiffAt_halfLineProjective_iff`. -/
theorem contMDiffAt_log_levelOf {k : ℕ} (f : EuclideanSpace ℝ (Fin k) → CappingSpace) (x₀ : EuclideanSpace ℝ (Fin k))
    (hf : ContMDiffAt (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) f x₀) :
    ContMDiffAt (𝓡 k) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => Real.log (levelOf (f w))) x₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    Work.Drive.halfLineProjectiveCharted
  have hg : ContMDiffAt (𝓡 k) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => cappingSpaceHomeoProj (f w)) x₀ := by
    have hiff := Work.Drive.chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := EuclideanSpace ℝ (Fin k)) (H' := EuclideanSpace ℝ (Fin k)) (𝓡 k)
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := Work.Drive.CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      Work.Drive.cappingSpaceHomeoProj.symm f Set.univ x₀
    exact hiff.mp hf
  obtain ⟨hρ, -⟩ := (Work.Drive.contMDiffAt_halfLineProjective_iff
    (fun w => cappingSpaceHomeoProj (f w)) x₀).mp hg
  have key : (fun w => Real.log (levelOf (f w)))
      = fun w => Work.Drive.CapSmooth.euclLog (Work.Drive.expHomeo.symm
          ((fun w => cappingSpaceHomeoProj (f w)) w).1) := by
    funext w
    rw [levelOf, Work.Drive.expHomeo_symm_apply, Work.Drive.CapSmooth.euclLog_logEucl]
  rw [key, contMDiffAt_iff_contDiffAt]
  exact (Work.Drive.CapSmooth.euclLog.contDiff.contDiffAt).comp x₀ (contMDiffAt_iff_contDiffAt.mp hρ)

/-- **The radial scale `clampScale` is smooth.** -/
theorem contMDiffAt_clampScale (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (x₀ : EuclideanSpace ℝ (Fin 3)) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (clampScale c ψ P) x₀ := by
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => ψ (x 2)) x₀ :=
    hψ.contDiffAt.comp x₀
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2)).contDiff.contDiffAt
  have hlog : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Real.log (levelOf (P (mk2 (x 0) (x 1))))) x₀ :=
    contMDiffAt_log_levelOf _ x₀ (hP.contMDiffAt.comp x₀ (contMDiffAt_mk2_proj x₀))
  have key : clampScale c ψ P
      = fun x => Real.exp (ψ (x 2) * (Real.log c
          - Real.log (levelOf (P (mk2 (x 0) (x 1)))))) := rfl
  rw [key, contMDiffAt_iff_contDiffAt]
  exact (Real.contDiff_exp.contDiffAt).comp x₀ (h2.mul
    (contDiffAt_const.sub (contMDiffAt_iff_contDiffAt.mp hlog)))

/-- **The radial sweep is smooth.** -/
theorem contMDiffAt_clampedSweep (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (x₀ : EuclideanSpace ℝ (Fin 3)) :
    ContMDiffAt (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (clampedSweep c ψ P) x₀ :=
  CapSmooth.contMDiffAt_scaleCapping (k := 3) (A := clampScale c ψ P)
    (clampScale_pos c ψ P) (fun x => P (mk2 (x 0) (x 1))) x₀
    (contMDiffAt_clampScale c ψ P hψ hP x₀)
    (hP.contMDiffAt.comp x₀ (contMDiffAt_mk2_proj x₀))

/-- **The radial sweep is a `C^∞` chain.** -/
theorem contMDiff_clampedSweep (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hP : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P) :
    ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (clampedSweep c ψ P) :=
  fun x => contMDiffAt_clampedSweep c ψ P hψ hP x

/-- **The three *radial* sweeps of disk-presented planes satisfy the engine's hypotheses.**  This is
`Work.Drive.meet3Hyp_sweeps` for the chain whose bottom face is the level `c k` instead of the dilated
plane: smoothness is `Work.Drive.contMDiff_clampedSweep`, the seam invariance is
`Work.Drive.clampedSweep_seamInv`, and the rest is the genericity data. -/
theorem meet3Hyp_clampedSweeps
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y))
    (hgen : Meet3Generic CappingSpace (fun k => clampedSweep (c k) ψ (P k))) :
    Meet3Hyp CappingSpace (fun k => clampedSweep (c k) ψ (P k)) :=
  meet3Hyp_of_generic _ (fun k => contMDiff_clampedSweep (c k) ψ (P k) hψ (hP k)) hgen
    (fun k x hx => clampedSweep_seamInv (c k) ψ (P k) (hPseam k) x hx)

/-- **The parity identity `Σ_k top_k ≡ Σ_k bottom_k` for the radial sweeps**, whose bottoms all lie in
their own level `c k`: this is the form in which `ENDS_AND_SEAMS_NOTES.md` §2 needs it (the bottoms are
now genuine level cycles, not ambiently isotopic copies of the tops). -/
theorem even_sum_topBdryMeet_add_bottomBdryMeet_clamped
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hP : ∀ k, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → P k y = P k (seamInv2 y))
    (hgen : Meet3Generic CappingSpace (fun k => clampedSweep (c k) ψ (P k))) :
    Even (((topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
        + (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 0).ncard)
      + ((topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1).ncard
        + (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 1).ncard)
      + ((topBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2).ncard
        + (bottomBdryMeet CappingSpace (fun k => clampedSweep (c k) ψ (P k)) 2).ncard)) :=
  even_sum_topBdryMeet_add_bottomBdryMeet CappingSpace _
    (meet3Hyp_clampedSweeps P c ψ hψ hP hPseam hgen)
    (not_seam_and_slice_of_generic _ hgen)

end Smoothness

end

end Work.Drive
