import Mathlib
import Submission.Work.Drive.projImmersion
import Submission.Work.Drive.planePt
import Submission.Work.Drive.LinChart.linPlaneChart_immersion

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The immersion condition `hc` of the genericity lane: the data form and the Cartesian case

`COUNTING_HALF_REMAINING.md` §2 and `PROJ_IMMERSION_STATUS.md` §7 reduce the four geometric inputs of
the counting engine (`ha`, `hc`, `hV`, `hface`) to two plane-local conditions and the genericity of the
triple-point set.  For a plane presentation `P : ℝ² → CappingSpace` the immersion condition is
(`Work.Drive.planeClassDeriv_injective_iff`)

> `hc` : `Function.Injective (mfderiv (𝓡 2) (𝓡 3) (fun y ↦ (cappingSpaceHomeoProj (P y)).2) z)`,

the immersion of the *class map* of the plane.  Session 19 turned `hc` into a statement about a vector
lift (`Work.Drive.injective_mfderiv_projMk_confProjVecOf_data`).  This file closes the remaining gap:
it identifies the class map of a presentation given through the **unified plane point**
`Work.Drive.planePt u r d` (one formula covering the configuration piece and the cap piece) with the
projectivised lift `y ↦ [confProjVecOf (U y) (D y)]`, and hence

* **`Work.Drive.injective_class_of_planePt_data`** — `hc` follows from the *radial* joint-kernel
  condition of `PROJ_IMMERSION_STATUS.md` §5 on the data map `y ↦ (U y, D y)` (the disk coordinate `D`
  is only needed up to the direction of its derivative);
* **`Work.Drive.injective_class_of_planePt_immersion`** — in particular `hc` is **free as soon as the
  disk coordinate `D` is an immersion** (`fderiv ℝ D y` injective at every `y`): a presentation whose
  disk coordinate is an honest *chart* of the plane needs no genericity at all;
* **`Work.Drive.injective_fderiv_cplxOf`** and **`Work.Drive.injective_class_of_cartesian`** — the
  standard instance: a presentation whose parameter *is* the disk coordinate
  (`D = cplxOf`, i.e. `planePt (U y) (r y) (cplxOf y)`) has `hc`, on the ball `‖y‖ < √2`.  This is the
  design recorded in `PROJ_IMMERSION_STATUS.md` §7 item 3 / `CAP_APEX_STATUS.md` §3 (the *Cartesian*
  cap chart): with it the only remaining input of `hc` is the *existence* of such a presentation, a
  construction and not a genericity statement.

The companion `Work.Drive.contMDiff_planePt_of_data` records the smoothness half at the same level of
generality (global form of `Work.Drive.contMDiffAt_planePt`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-- **The class of a plane point is the projective class of its sphere lift.**  This is the defining
property of `Work.Drive.planePt` read in the second (projective) transparent coordinate. -/
theorem planePt_snd_eq (u : ℂ) (r : ℝ) (hr : 0 < r) (d : ℂ) (hu : ‖u‖ = 1)
    (hv : confProjVecOf u d ≠ 0) :
    (cappingSpaceHomeoProj (planePt u r hr d hu hv)).2
      = Projectivization.mk ℝ (confProjVecOf u d) hv :=
  congrArg Prod.snd (cappingSpaceHomeoProj_planePt u r hr d hu hv)

/-- **`hc` from the data of a plane presentation through the unified plane point.**
For `C^∞` data `(U, D)` with `U` circle-valued and `D` in the disk `‖D‖ < √2`, if the only direction
in which `U` moves radially (`dU(y) w ∈ ℝ∙U y`) while `D` stands still (`dD(y) w = 0`) is the zero
direction, then the class map of the presentation `y ↦ planePt (U y) (r y) (D y)` is an immersion at
every `y`.  This is `Work.Drive.injective_mfderiv_projMk_confProjVecOf_data` transported to the class
map through `Work.Drive.planePt_snd_eq`; no chart and no projective geometry is left in the
statement. -/
theorem injective_class_of_planePt_data {U D : EuclideanSpace ℝ (Fin 2) → ℂ}
    (r : EuclideanSpace ℝ (Fin 2) → ℝ) (hr : ∀ y, 0 < r y) (hU : ∀ y, ‖U y‖ = 1)
    (hv : ∀ y, confProjVecOf (U y) (D y) ≠ 0)
    (hD : ∀ y, 0 < 1 - ‖D y‖ ^ 2 / 2)
    (hUd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hDd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hι : ∀ y w, (∃ l : ℝ, fderiv ℝ U y w = l • U y) → fderiv ℝ D y w = 0 → w = 0)
    (y : EuclideanSpace ℝ (Fin 2)) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) (fun y' : EuclideanSpace ℝ (Fin 2) =>
      (cappingSpaceHomeoProj (planePt (U y') (r y') (hr y') (D y') (hU y') (hv y'))).2) y) := by
  have hfun : (fun y' : EuclideanSpace ℝ (Fin 2) =>
      (cappingSpaceHomeoProj (planePt (U y') (r y') (hr y') (D y') (hU y') (hv y'))).2)
      = (fun y' : EuclideanSpace ℝ (Fin 2) =>
        Projectivization.mk ℝ (confProjVecOf (U y') (D y'))
          (confProjVecOf_ne_zero_of_norm_eq_one (hU y') (D y'))) := by
    funext y'
    exact planePt_snd_eq (U y') (r y') (hr y') (D y') (hU y') (hv y')
  rw [hfun]
  exact injective_mfderiv_projMk_confProjVecOf_data hU hD hUd hDd hι y

/-- **`hc` is free when the disk coordinate of the presentation is an immersion.**  If `fderiv ℝ D y`
is injective at every `y` — the case of a presentation whose second coordinate really is a *chart* of
the disk — then the joint-kernel hypothesis of `Work.Drive.injective_class_of_planePt_data` is
automatic, and the class map is an immersion with no genericity assumption. -/
theorem injective_class_of_planePt_immersion {U D : EuclideanSpace ℝ (Fin 2) → ℂ}
    (r : EuclideanSpace ℝ (Fin 2) → ℝ) (hr : ∀ y, 0 < r y) (hU : ∀ y, ‖U y‖ = 1)
    (hv : ∀ y, confProjVecOf (U y) (D y) ≠ 0)
    (hD : ∀ y, 0 < 1 - ‖D y‖ ^ 2 / 2)
    (hUd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hDd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hDinj : ∀ y, Function.Injective (fderiv ℝ D y))
    (y : EuclideanSpace ℝ (Fin 2)) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) (fun y' : EuclideanSpace ℝ (Fin 2) =>
      (cappingSpaceHomeoProj (planePt (U y') (r y') (hr y') (D y') (hU y') (hv y'))).2) y) :=
  injective_class_of_planePt_data r hr hU hv hD hUd hDd
    (fun y' w _ hw => hDinj y' (by rw [hw, map_zero])) y

/-- **The complex disk coordinate is an immersion**: `fderiv ℝ cplxOf y` is the linear isometry
equivalence `ℝ² ≅ ℂ`, hence injective. -/
theorem injective_fderiv_cplxOf (y : EuclideanSpace ℝ (Fin 2)) :
    Function.Injective (fderiv ℝ cplxOf y) := by
  have hcoe : cplxOf = (fun y' : EuclideanSpace ℝ (Fin 2) =>
      (Work.Drive.LinChart.cplxOfLIE : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ) y') := by
    funext y'
    exact (Work.Drive.LinChart.cplxOfLIE_apply y').symm
  have hfd : fderiv ℝ cplxOf y
      = (Work.Drive.LinChart.cplxOfLIE : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ) := by
    rw [hcoe]
    exact ContinuousLinearMap.fderiv (f := (Work.Drive.LinChart.cplxOfLIE :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ))
  rw [hfd]
  exact fun a b hab => Work.Drive.LinChart.cplxOfLIE.injective hab

/-- The complex disk coordinate is isometric: `‖cplxOf y‖ = ‖y‖`. -/
theorem norm_cplxOf (y : EuclideanSpace ℝ (Fin 2)) : ‖cplxOf y‖ = ‖y‖ := by
  have h : cplxOf y = Work.Drive.LinChart.cplxOfLIE y :=
    (Work.Drive.LinChart.cplxOfLIE_apply y).symm
  rw [h]
  exact Work.Drive.LinChart.cplxOfLIE.norm_map y

/-- **The Cartesian presentation has `hc` for free.**  For the presentation whose parameter *is* the
disk coordinate, `y ↦ planePt (U y) (r y) (cplxOf y)`, the class map is an immersion at every `y` with
`‖y‖ < √2` (the region on which the configuration lift does not cross the Clifford torus).  This is the
form in which `PROJ_IMMERSION_STATUS.md` §7 item 3 proposes to discharge `hc`: the remaining input is
the *construction* of such a presentation, not any genericity. -/
theorem injective_class_of_cartesian {U : EuclideanSpace ℝ (Fin 2) → ℂ}
    (r : EuclideanSpace ℝ (Fin 2) → ℝ) (hr : ∀ y, 0 < r y) (hU : ∀ y, ‖U y‖ = 1)
    (hUd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hbd : ∀ y : EuclideanSpace ℝ (Fin 2), ‖y‖ < Real.sqrt 2)
    (y : EuclideanSpace ℝ (Fin 2)) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3) (fun y' : EuclideanSpace ℝ (Fin 2) =>
      (cappingSpaceHomeoProj (planePt (U y') (r y') (hr y') (cplxOf y') (hU y')
        (confProjVecOf_ne_zero_of_norm_eq_one (hU y') (cplxOf y')))).2) y) := by
  have hfun : (fun y' : EuclideanSpace ℝ (Fin 2) =>
      (cappingSpaceHomeoProj (planePt (U y') (r y') (hr y') (cplxOf y') (hU y')
        (confProjVecOf_ne_zero_of_norm_eq_one (hU y') (cplxOf y')))).2)
      = (fun y' : EuclideanSpace ℝ (Fin 2) =>
        Projectivization.mk ℝ (confProjVecOf (U y') (cplxOf y'))
          (confProjVecOf_ne_zero_of_norm_eq_one (hU y') (cplxOf y'))) := by
    funext y'
    exact planePt_snd_eq (U y') (r y') (hr y') (cplxOf y') (hU y')
      (confProjVecOf_ne_zero_of_norm_eq_one (hU y') (cplxOf y'))
  rw [hfun]
  refine injective_mfderiv_projMk_confProjVecOf_data hU (fun y' => ?_) hUd contDiff_cplxOf
    (fun y' w _ hw => injective_fderiv_cplxOf y' (by rw [hw, map_zero])) y
  rw [norm_cplxOf y']
  have hsq : ‖y'‖ ^ 2 < 2 := by
    have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [hbd y', Real.sqrt_nonneg 2, norm_nonneg y']
  linarith

/-- **Smoothness of a plane presentation through the unified plane point.**  The global form of
`Work.Drive.contMDiffAt_planePt`: from `C^∞` data `(u, r, d)` with a positive radius, a circle-valued
halving and `1 - ‖d y‖²/2 ≠ 0` everywhere, the presentation `y ↦ planePt (u y) (r y) (d y)` is `C^∞`
into the capping space with its transparent smooth structure. -/
theorem contMDiff_planePt_of_data (u d : EuclideanSpace ℝ (Fin 2) → ℂ)
    (r : EuclideanSpace ℝ (Fin 2) → ℝ) (hr : ∀ y, 0 < r y) (hu : ∀ y, ‖u y‖ = 1)
    (hne : ∀ y, 1 - ‖d y‖ ^ 2 / 2 ≠ 0) (hv : ∀ y, confProjVecOf (u y) (d y) ≠ 0)
    (hrs : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hus : ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hds : ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) d) :
    letI := cappingCharted
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => planePt (u y) (r y) (hr y) (d y) (hu y) (hv y)) := by
  intro y
  exact contMDiffAt_planePt r u d y hr hu (hne y) hv (hrs.contMDiffAt) (hus.contMDiffAt)
    (hds.contMDiffAt)

end

end Work.Drive
