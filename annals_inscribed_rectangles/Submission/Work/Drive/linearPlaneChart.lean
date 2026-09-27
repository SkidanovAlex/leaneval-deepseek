import Mathlib
import Submission.Work.Drive.planePt
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff
import Submission.Work.Drive.projImmersion
import Submission.Work.Drive.ProjectiveTopology
import Submission.Work.Drive.projective_planes_meet_oddly

/-!
# The *linear* projective plane of the capping space: an explicit `C^∞` disk presentation

The counting half of the chain route (`Submission/Work/Drive/CONCRETE_CHAINS_STATUS.md`,
`ENDS_AND_SEAMS_NOTES.md`) needs, besides the capped plane `P_u = u · (M ∪ cap)` of the smooth Jordan
curve `γ`, a **linear** projective plane of a fixed level `{c} × ℝP³` of the capping space
`Y ≅ (0,∞) × ℝP³`, presented in exactly the same form as the plane chart — a `C^∞` map of the disk
whose boundary circle is antipodally identified (`diskPlane`'s input, `planeChain.lean`).  The reason is
the end contribution `Σ_k bottom_k ≡ 1` of Hugelmeyer's Lemmas 3–4: the three radial sweeps may be
*chosen* so that their bottom faces are three linear projective planes in general position, whereupon
the count `#(Z_0 ⋔ Z_1 ⋔ Z_2) = 1` is the proved linear fact `projective_planes_meet_oddly`
(`ENDS_AND_SEAMS_NOTES.md` §2).

This file builds that object.  The construction is the standard disk model of `ℝP²` pushed into the
transparent coordinates of the capping space: with the sphere lift

> `linVecC z = ofComplex z (1 - ‖z‖²) ∈ ℂ² ≅ ℝ⁴`   (`‖z‖ ≤ 1`),

the class `[linVecC z]` sweeps the projective plane of the `3`-dimensional subspace
`linStd = span {linVecC z}` = `{v : v 3 = 0}`, the boundary circle `‖z‖ = 1` maps onto its projective
line `[z : 0]` **antipodally** (`linVecC (-z) = -linVecC z` there), and the map is injective off the
antipodal pairs, so it is a chart of `ℝP²`.  Composing with any linear equivalence `φ : ℝ⁴ ≃ ℝ⁴` and
placing the result on the level `c > 0` gives the linear plane `φ(linStd)` of that level:

> `linPlaneChart φ c hc z = cappingVecPoint c hc (φ (linVecC z))`.

Main results:

* `Work.Drive.cappingVecPoint` (`cappingSpaceHomeoProj_cappingVecPoint`) — the capping point of a
  radius and a *vector*, in the transparent coordinates;
* `Work.Drive.contMDiffAt_cappingVecPoint'` — its smoothness from smoothness of the radius and the
  vector (a clash-free copy of the corresponding tool of the strip lane, cf. `PAIRPT_CLASH.md`: this
  file lives in the counting world and therefore cannot import `StripDiskAux`);
* `Work.Drive.linPlaneChart_contMDiff` — the chart is `C^∞`;
* `Work.Drive.cappingSpaceHomeoProj_linPlaneChart` — its value in the transparent coordinates (level
  `c`, class `[φ (linVecC z)]`);
* `Work.Drive.linPlaneChart_neg` — `linPlaneChart φ c hc (-z) = linPlaneChart φ c hc z` for
  `‖z‖ = 1`, i.e. `diskPlane_seamInv2` applies to it;
* `Work.Drive.linSub`, `Work.Drive.linPlaneChart_mem_projLine` — the plane's class lies in
  `projLine (φ(linStd))`, the projective plane of the model.

The identification of the *count* `#(Z_0 ⋔ Z_1 ⋔ Z_2) = 1` for three such planes in general position
(and the passage from the level `{c} × ℝP³` to the engine's box maps) is not in this file.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. The capping point of a radius and a vector -/

/-- **The capping point of a radius and a vector**: in the transparent coordinates
`cappingSpaceHomeoProj : CappingSpace ≃ₜ (0,∞) × ℝP³` it is `(r, [V])`.  This is the capping-space
point used by every plane chart (`planePt` is the special case in which the vector is the
configuration sphere lift `confProjVecOf u d`). -/
def cappingVecPoint (r : ℝ) (hr : 0 < r) (V : Eucl 3) (hV : V ≠ 0) : CappingSpace :=
  cappingSpaceHomeoProj.symm (⟨r, hr⟩, Projectivization.mk ℝ V hV)

/-- The defining property of `cappingVecPoint`. -/
lemma cappingSpaceHomeoProj_cappingVecPoint (r : ℝ) (hr : 0 < r) (V : Eucl 3) (hV : V ≠ 0) :
    cappingSpaceHomeoProj (cappingVecPoint r hr V hV)
      = (⟨r, hr⟩, Projectivization.mk ℝ V hV) :=
  cappingSpaceHomeoProj.apply_symm_apply _

/-- Two capping points of the same radius and non-zero vectors agree exactly when their projective
classes do. -/
lemma cappingVecPoint_eq_iff {r : ℝ} (hr : 0 < r) {V V' : Eucl 3} (hV : V ≠ 0) (hV' : V' ≠ 0) :
    cappingVecPoint r hr V hV = cappingVecPoint r hr V' hV' ↔
      Projectivization.mk ℝ V hV = Projectivization.mk ℝ V' hV' := by
  constructor
  · intro h
    have h' := congrArg cappingSpaceHomeoProj h
    rw [cappingSpaceHomeoProj_cappingVecPoint, cappingSpaceHomeoProj_cappingVecPoint] at h'
    exact (Prod.ext_iff.mp h').2
  · intro h
    rw [cappingVecPoint, cappingVecPoint, h]

/-! ## 2. Smoothness of the capping point (clash-free copy of the strip-lane tool)

`PAIRPT_CLASH.md`: this file must live in the *counting* world (it uses `diskPlane` and the
projective-plane counting facts), hence it cannot import `StripDiskAux`, where
`Work.Drive.contMDiffAt_cappingVecPoint` is stated.  The proof below is the same argument, recopied;
the statement is deliberately named with a prime so that no environment ever contains both. -/

open Classical in
/-- **Smoothness of the capping point with prescribed radius and physical vector.** -/
theorem contMDiffAt_cappingVecPoint' {k : ℕ}
    (r : EuclideanSpace ℝ (Fin k) → ℝ) (V : EuclideanSpace ℝ (Fin k) → Eucl 3)
    (x₀ : EuclideanSpace ℝ (Fin k))
    (hr : ∀ w, 0 < r w) (hV : ∀ w, V w ≠ 0)
    (hrs : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) r x₀)
    (hVs : ContMDiffAt (𝓡 k) 𝓘(ℝ, Eucl 3) ((⊤ : ℕ∞) : WithTop ℕ∞) V x₀) :
    letI := cappingCharted
    ContMDiffAt (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => cappingVecPoint (r w) (hr w) (V w) (hV w)) x₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ)) :=
    Homeomorph.chartedSpace expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  let F : EuclideanSpace ℝ (Fin k) → CappingSpace := fun w =>
    cappingVecPoint (r w) (hr w) (V w) (hV w)
  let g : EuclideanSpace ℝ (Fin k) →
      Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => cappingSpaceHomeoProj (F w)
  have hg : ∀ w, g w = (⟨r w, hr w⟩, Projectivization.mk ℝ (V w) (hV w)) := fun w =>
    cappingSpaceHomeoProj_cappingVecPoint (r w) (hr w) (V w) (hV w)
  have hchart : (letI := cappingCharted
        ContMDiffAt (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((⊤ : ℕ∞) : WithTop ℕ∞) F x₀) ↔
      ContMDiffAt (𝓡 k) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g x₀ :=
    chartedStructure_contMDiffWithinAt (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4))
      (H := EuclideanSpace ℝ (Fin 4)) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := EuclideanSpace ℝ (Fin k)) (H' := EuclideanSpace ℝ (Fin k)) (𝓡 k)
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      cappingSpaceHomeoProj.symm F Set.univ x₀
  have hfirst : ContMDiffAt (𝓡 k) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => expHomeo.symm (g w).1) x₀ := by
    have hcomp : (fun w => expHomeo.symm (g w).1)
        = fun w => expHomeo.symm ⟨r w, hr w⟩ := by
      funext w
      rw [hg w]
    rw [hcomp]
    exact contMDiffAt_expHomeo_symm hr x₀ hrs
  have hsecond : ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (g w).2) x₀ := by
    have hcomp : (fun w => (g w).2)
        = fun w => Projectivization.mk ℝ (V w) (hV w) := by
      funext w
      rw [hg w]
    rw [hcomp]
    exact contMDiffAt_projMk V hV x₀ hVs
  exact hchart.mpr ((contMDiffAt_halfLineProjective_iff g x₀).mpr ⟨hfirst, hsecond⟩)

/-! ## 3. The standard linear plane of `ℂ² ≅ ℝ⁴`

`linVecC z = (z, 1 - ‖z‖²)` in the complex coordinates of `ℂ²`.  Its class sweeps the projective plane
`{[z : 1 - ‖z‖²]}` of `ℂ²`, whose span is the hyperplane `{v : v 3 = 0}`: substituting `z = 1`,
`z = i`, `z = 0` gives the three vectors `e₁, e₂, e₃`. -/

/-- The sphere lift `z ↦ (z, 1 - ‖z‖²) ∈ ℂ²` of the standard disk model of `ℝP²`. -/
def linVecC (z : ℂ) : Eucl 3 := ofComplex z (Complex.ofReal (1 - ‖z‖ ^ 2))

/-- `linVecC` never vanishes: its first complex coordinate vanishes only at `z = 0`, where the second
is `1`. -/
lemma linVecC_ne_zero (z : ℂ) : linVecC z ≠ 0 := by
  intro h
  have h1 : c₁ (linVecC z) = 0 := by rw [h]; simp [c₁]
  have h2 : c₂ (linVecC z) = 0 := by rw [h]; simp [c₂]
  rw [linVecC, c₁_ofComplex] at h1
  rw [linVecC, c₂_ofComplex] at h2
  rw [h1, norm_zero] at h2
  norm_num at h2

/-- `linVecC` is `C^∞` as a map `ℂ → ℝ⁴`. -/
theorem linVecC_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) linVecC := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : ℂ => Complex.ofReal (1 - ‖w‖ ^ 2)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_const.sub (contDiff_norm_sq (𝕜 := ℝ) (E := ℂ)))
  exact confProjVecOf_contDiffAt_ofComplex (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (x := z)
    (a := fun w : ℂ => w) (b := fun w : ℂ => Complex.ofReal (1 - ‖w‖ ^ 2))
    contDiff_id.contDiffAt hb.contDiffAt

/-- The boundary circle of the disk model maps to the antipode of the image of `z`:
`linVecC (-z) = - linVecC z` for `‖z‖ = 1`. -/
lemma linVecC_neg {z : ℂ} (hz : ‖z‖ = 1) : linVecC (-z) = -linVecC z := by
  have h1 : ‖-z‖ = 1 := by rw [norm_neg, hz]
  simp only [linVecC, h1, hz]
  norm_num
  simpa using ofComplex_neg z 0

/-- The standard linear plane `linStd = span {linVecC z}`, i.e. `{v : v 3 = 0}` in the real
coordinates of `ℂ² ≅ ℝ⁴`. -/
def linStd : Submodule ℝ (Eucl 3) := Submodule.span ℝ (Set.range linVecC)

lemma linVecC_mem_linStd (z : ℂ) : linVecC z ∈ linStd :=
  Submodule.subset_span ⟨z, rfl⟩

/-! ## 4. The chart on the parameter square and on the disk -/

/-- The same disk model in the real coordinates of the parameter square: `linVec = linVecC ∘ cplxOf`. -/
def linVec (a : EuclideanSpace ℝ (Fin 2)) : Eucl 3 := linVecC (cplxOf a)

lemma linVec_ne_zero (a : EuclideanSpace ℝ (Fin 2)) : linVec a ≠ 0 := linVecC_ne_zero (cplxOf a)

theorem linVec_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) linVec :=
  linVecC_contDiff.comp contDiff_cplxOf

/-- The image under `φ` of the standard lift never vanishes (`φ` is a linear equivalence and the
lift never vanishes). -/
lemma phi_linVec_ne_zero (φ : Eucl 3 ≃L[ℝ] Eucl 3) (a : EuclideanSpace ℝ (Fin 2)) :
    φ (linVec a) ≠ 0 := fun h => linVec_ne_zero a (φ.injective (h.trans (map_zero φ).symm))

lemma phi_linVecC_ne_zero (φ : Eucl 3 ≃L[ℝ] Eucl 3) (z : ℂ) : φ (linVecC z) ≠ 0 :=
  fun h => linVecC_ne_zero z (φ.injective (h.trans (map_zero φ).symm))

/-- **The linear plane point, parametrised by the parameter square.** -/
def linPlanePt (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (a : EuclideanSpace ℝ (Fin 2)) : CappingSpace :=
  cappingVecPoint c hc (φ (linVec a)) (phi_linVec_ne_zero φ a)

/-- The value of `linPlanePt` in the transparent coordinates. -/
lemma cappingSpaceHomeoProj_linPlanePt (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (a : EuclideanSpace ℝ (Fin 2)) :
    cappingSpaceHomeoProj (linPlanePt φ c hc a)
      = (⟨c, hc⟩, Projectivization.mk ℝ (φ (linVec a)) (phi_linVec_ne_zero φ a)) :=
  cappingSpaceHomeoProj_cappingVecPoint c hc (φ (linVec a)) (phi_linVec_ne_zero φ a)

/-- **Smoothness of the linear plane point.** -/
theorem linPlanePt_contMDiff (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    letI := cappingCharted
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (linPlanePt φ c hc) := by
  intro a
  have hVsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : EuclideanSpace ℝ (Fin 2) =>
      φ (linVec w)) := φ.contDiff.comp linVec_contDiff
  exact contMDiffAt_cappingVecPoint' (fun _ : EuclideanSpace ℝ (Fin 2) => c) (fun w => φ (linVec w))
    a (fun _ => hc) (fun w => phi_linVec_ne_zero φ w)
    (contMDiffAt_const) (contMDiff_iff_contDiff.mpr hVsm |>.contMDiffAt)

/-! ## 5. The inverse of the real/complex identification -/

/-- The inverse of `Work.Drive.cplxOf : ℝ² → ℂ`. -/
def cplxOfInv (z : ℂ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z.re, z.im]

@[simp] lemma cplxOfInv_apply_zero (z : ℂ) : cplxOfInv z 0 = z.re := rfl
@[simp] lemma cplxOfInv_apply_one (z : ℂ) : cplxOfInv z 1 = z.im := rfl

@[simp] lemma cplxOf_cplxOfInv (z : ℂ) : cplxOf (cplxOfInv z) = z := by
  rw [cplxOf]
  simp [cplxOfInv]

@[simp] lemma cplxOfInv_cplxOf (a : EuclideanSpace ℝ (Fin 2)) : cplxOfInv (cplxOf a) = a := by
  ext i
  fin_cases i <;> simp [cplxOfInv, cplxOf]

lemma cplxOfInv_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cplxOfInv := by
  have hre : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · convert hre using 1
    ext z
    simp [cplxOfInv]
  · convert him using 1
    ext z
    simp [cplxOfInv]

lemma cplxOfInv_neg (z : ℂ) : cplxOfInv (-z) = -cplxOfInv z := by
  ext i
  fin_cases i <;> simp [cplxOfInv]

lemma linVec_cplxOfInv (z : ℂ) : linVec (cplxOfInv z) = linVecC z := by
  simp only [linVec, linVecC, cplxOf_cplxOfInv]

/-! ## 6. The linear plane chart of the disk -/

/-- **The linear plane chart**: the disk model of `ℝP²` pushed into the level `c` of the capping space
along the linear equivalence `φ`.  Its image is the projective plane `φ(linStd)` of that level. -/
def linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) (z : ℂ) : CappingSpace :=
  linPlanePt φ c hc (cplxOfInv z)

/-- **Smoothness of the linear plane chart.** -/
theorem linPlaneChart_contMDiff (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    letI := cappingCharted
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (linPlaneChart φ c hc) := by
  letI := cappingCharted
  exact (linPlanePt_contMDiff φ c hc).comp (contMDiff_iff_contDiff.mpr cplxOfInv_contDiff)

/-- **The value of the linear plane chart in the transparent coordinates**: level `c` and the
projective class of `φ (linVecC z)`. -/
lemma cappingSpaceHomeoProj_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) (z : ℂ) :
    cappingSpaceHomeoProj (linPlaneChart φ c hc z)
      = (⟨c, hc⟩, Projectivization.mk ℝ (φ (linVecC z)) (phi_linVecC_ne_zero φ z)) := by
  rw [linPlaneChart, cappingSpaceHomeoProj_linPlanePt]
  refine Prod.ext rfl ?_
  refine (Projectivization.mk_eq_mk_iff ℝ (φ (linVec (cplxOfInv z))) (φ (linVecC z)) _ _).mpr
    ⟨1, ?_⟩
  rw [one_smul, linVec_cplxOfInv]

/-- The **level** of a linear plane chart point (the `(0,∞)`-coordinate of
`cappingSpaceHomeoProj`) is `c`. -/
lemma level_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) (z : ℂ) :
    ((cappingSpaceHomeoProj (linPlaneChart φ c hc z)).1 : ℝ) = c := by
  rw [cappingSpaceHomeoProj_linPlaneChart]

/-- **The disk model's antipodal identification**: on the boundary circle the linear plane chart is
invariant under `z ↦ -z`.  This is the input of `Work.Drive.diskPlane_seamInv2`. -/
theorem linPlaneChart_neg (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) {z : ℂ}
    (hz : ‖z‖ = 1) : linPlaneChart φ c hc (-z) = linPlaneChart φ c hc z := by
  apply cappingSpaceHomeoProj.injective
  rw [cappingSpaceHomeoProj_linPlaneChart φ c hc (-z),
    cappingSpaceHomeoProj_linPlaneChart φ c hc z]
  refine Prod.ext rfl ?_
  refine projectivizationMk_eq_of_eq_neg ?_ (phi_linVecC_ne_zero φ z) (phi_linVecC_ne_zero φ (-z))
  rw [linVecC_neg hz, map_neg]

/-! ## 7. The projective plane of the model -/

/-- The `3`-dimensional subspace whose projectivisation is the plane of the chart: the image of the
standard plane `linStd` under `φ`. -/
def linSub (φ : Eucl 3 ≃L[ℝ] Eucl 3) : Submodule ℝ (Eucl 3) :=
  linStd.map φ.toLinearEquiv.toLinearMap

/-- The linear functional whose kernel is the plane `linSub φ`: `v ↦ (φ⁻¹ v) 3`.  This is the
vocabulary in which the *general position* of three linear planes (the hypothesis of
`projective_planes_meet_oddly`) becomes a statement about three functionals. -/
def linFun (φ : Eucl 3 ≃L[ℝ] Eucl 3) : Eucl 3 →ₗ[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) 3).comp φ.symm.toContinuousLinearMap |>.toLinearMap

@[simp] lemma linFun_apply (φ : Eucl 3 ≃L[ℝ] Eucl 3) (v : Eucl 3) :
    linFun φ v = φ.symm v 3 := by simp [linFun]

lemma linVecC_mem_linSub (φ : Eucl 3 ≃L[ℝ] Eucl 3) (z : ℂ) : φ (linVecC z) ∈ linSub φ :=
  ⟨linVecC z, linVecC_mem_linStd z, rfl⟩

/-- **The class of a linear plane chart point lies in the projective plane `φ(linStd)`.** -/
theorem linPlaneChart_mem_projLine (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) (z : ℂ) :
    (cappingSpaceHomeoProj (linPlaneChart φ c hc z)).2 ∈ projLine (linSub φ) := by
  rw [cappingSpaceHomeoProj_linPlaneChart φ c hc z]
  exact ⟨φ (linVecC z), phi_linVecC_ne_zero φ z, linVecC_mem_linSub φ z, rfl⟩

end

end Work.Drive
