import Mathlib
import Submission.Work.Drive.encodedShear
import Submission.Work.Drive.contDiff_shear_thetaS
import Submission.Work.Drive.shear_box_bijOn
import Submission.Work.Drive.shear_fderiv
import Submission.Work.Drive.thetaS_props
import Submission.Work.Drive.meet3HypReparam
import Submission.Work.Drive.encodedTransverse
import Submission.Work.Drive.mk2CLM

/-!
# The box reparametrisation of the `hodd` family, lifted to `𝔼³`

`Work.Drive.meet3Hyp_of_boxReparam` (`Submission/Work/Drive/meet3HypReparam.lean`, §2.4 of the
project lead's `NOTES_LEAD_hodd_blockT6.md`) transfers `Meet3Hyp` from a *sheared* family
`k ↦ D k ∘ Θ k` back to the original chains `D`, provided each `Θ k` is a `C^∞` self-map of `𝔼³`
which is a bijection of the unit box, preserves each face, has a bijective derivative on the box and
a derivative preserving the coordinate hyperplanes along the faces.

The *design's* reparametrisations (§2.2 of the note) act on the plane coordinates `(x 0, x 1)` by the
clamped cross-shear `Work.Drive.shear` and on the level coordinate `x 2` by the twist
`Work.Drive.thetaS`.  All the *two-dimensional* data (box bijectivity and face preservation
`shear_box_bijOn`, the derivative `shear_fderiv`, the twist `thetaS_props`) is already on disk; what is
missing is the **lift to `𝔼³`** together with its four `meet3Hyp_of_boxReparam` conditions.  This file
supplies exactly that:

* `Work.Drive.boxReparam q r : 𝔼³ → 𝔼³`, the lift `x ↦ mk3 (shear q (mk2 (x 0) (x 1))) (thetaS r (x 2))`;
* `Work.Drive.contDiff_boxReparam`, `boxReparam_bijOn`, `boxReparam_face`, `boxReparam_fderiv_bijective`,
  `boxReparam_fderiv_normal` — the five conditions of `meet3Hyp_of_boxReparam`;
* `Work.Drive.meet3Hyp_of_boxReparam_family` — the packaged transfer for a family of lifts, the form in
  which the `hodd` chapter consumes it.

The lift is *not* the product of the two one-dimensional reparametrisations alone: the twist is applied
only to the third coordinate, and the shear only to the first two, so the derivative splits as the
direct sum of `d shear` (composed with the projection `mk2CLM`) and the scalar derivative of `thetaS`
(composed with `coordCLM2`).  Because the two projections together are injective and `d shear` is
injective on the box while the twist's derivative is a non-zero scalar, the composite derivative is
injective, hence (equal dimensions) bijective.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology

noncomputable section

/-- **The box reparametrisation of the `hodd` family**: shear the first two coordinates and twist the
third.  `r = 0` gives the pure shear (`thetaS 0 = id`), which is the reparametrisation of block `0` of
the design's family (whose level is constant). -/
def boxReparam (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  mk3 (shear q (mk2CLM x)) (thetaS r (coordCLM2 x))

@[simp] lemma boxReparam_apply_zero (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : boxReparam q r x 0 = (shear q (mk2CLM x)) 0 := by
  simp [boxReparam]

@[simp] lemma boxReparam_apply_one (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : boxReparam q r x 1 = (shear q (mk2CLM x)) 1 := by
  simp [boxReparam]

@[simp] lemma boxReparam_apply_two (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : boxReparam q r x 2 = thetaS r (x 2) := by
  simp [boxReparam]

/-- The coordinate projections `mk2CLM : 𝔼³ → 𝔼²` and `coordCLM2 : 𝔼³ → ℝ` together form a
continuous linear equivalence. -/
def projEquivFun : EuclideanSpace ℝ (Fin 3) →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  mk2CLM.prod coordCLM2

@[simp] lemma projEquivFun_apply (x : EuclideanSpace ℝ (Fin 3)) :
    projEquivFun x = (mk2 (x 0) (x 1), x 2) := by
  simp [projEquivFun, mk2CLM_apply]

lemma projEquivFun_injective : Function.Injective projEquivFun := by
  intro x y h
  have h1 : mk2CLM x = mk2CLM y := by simpa [projEquivFun] using congrArg Prod.fst h
  have h2 : coordCLM2 x = coordCLM2 y := by simpa [projEquivFun] using congrArg Prod.snd h
  exact coord_eq_of x y h1 h2

lemma projEquivFun_surjective : Function.Surjective projEquivFun := by
  rintro ⟨a, t⟩
  refine ⟨mk3 a t, ?_⟩
  rw [projEquivFun_apply]
  ext i
  · simp
    fin_cases i <;> simp
  · simp

/-- **The continuous linear equivalence `𝔼³ ≅ 𝔼² × ℝ`** of the coordinates `(x 0, x 1)` and `x 2`. -/
def projEquiv : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  ContinuousLinearEquiv.ofBijective projEquivFun
    (LinearMap.ker_eq_bot.mpr projEquivFun_injective)
    (LinearMap.range_eq_top.mpr projEquivFun_surjective)

@[simp] lemma projEquiv_apply (x : EuclideanSpace ℝ (Fin 3)) :
    projEquiv x = (mk2 (x 0) (x 1), x 2) := by
  simp only [projEquiv, ContinuousLinearEquiv.coeFn_ofBijective, projEquivFun_apply]

/-- **The inverse `𝔼² × ℝ → 𝔼³` of the coordinate equivalence**, i.e. the map
`p ↦ mk3 p.1 p.2`, as a continuous linear map. -/
def mk3CLM : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  projEquiv.symm.toContinuousLinearMap

@[simp] lemma mk3CLM_apply (p : EuclideanSpace ℝ (Fin 2) × ℝ) : mk3CLM p = mk3 p.1 p.2 := by
  have h : projEquiv (mk3 p.1 p.2) = p := by
    rw [projEquiv_apply]
    ext i
    · simp
      fin_cases i <;> simp
    · simp
  have h3 : projEquiv.symm (projEquiv (mk3 p.1 p.2)) = mk3 p.1 p.2 :=
    ContinuousLinearEquiv.symm_apply_apply projEquiv (mk3 p.1 p.2)
  rw [h] at h3
  simpa [mk3CLM] using h3

@[simp] lemma mk3CLM_apply_zero (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    mk3CLM p 0 = p.1 0 := by simp
@[simp] lemma mk3CLM_apply_one (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    mk3CLM p 1 = p.1 1 := by simp
@[simp] lemma mk3CLM_apply_two (p : EuclideanSpace ℝ (Fin 2) × ℝ) :
    mk3CLM p 2 = p.2 := by simp

lemma mk3CLM_injective : Function.Injective mk3CLM := by
  intro p p' h
  have h' : projEquiv.symm p = projEquiv.symm p' := h
  exact projEquiv.symm.injective h'

lemma mk3CLM_bijective : Function.Bijective mk3CLM :=
  projEquiv.symm.bijective

/-- The two coordinate projections `mk2CLM`, `coordCLM2` together separate points. -/
lemma mk3_mk2CLM_coordCLM2 (x : EuclideanSpace ℝ (Fin 3)) :
    mk3 (mk2CLM x) (coordCLM2 x) = x := by
  ext i
  fin_cases i <;> simp

/-! ## The box data of the lift -/

/-- Membership in the unit box of `𝔼³`, in the three coordinates. -/
lemma mem_unitBox2_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ Submission.Drive.unitBox 2 ↔
      x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ x 1 ∈ Set.Icc (0 : ℝ) 1 ∧ x 2 ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · intro h i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2

/-- The plane coordinates of a box point of `𝔼³` lie in the plane box. -/
lemma mk2CLM_mem_unitBox_one {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ Submission.Drive.unitBox 2) : mk2CLM x ∈ Submission.Drive.unitBox 1 := by
  rw [mem_unitBox1_iff, mk2CLM_apply]
  rw [mem_unitBox2_iff] at hx
  exact ⟨by simpa using hx.1, by simpa using hx.2.1⟩

lemma boxReparam_mapsTo (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    Set.MapsTo (boxReparam q r) (Submission.Drive.unitBox 2) (Submission.Drive.unitBox 2) := by
  intro x hx
  have hx' := hx
  rw [mem_unitBox2_iff] at hx'
  have hy : mk2CLM x ∈ Submission.Drive.unitBox 1 := mk2CLM_mem_unitBox_one hx
  have hshy : shear q (mk2CLM x) ∈ Submission.Drive.unitBox 1 := (shear_box_bijOn q).1.1 hy
  have htx : thetaS r (x 2) ∈ Set.Icc (0 : ℝ) 1 := (thetaS_props r).1.1 hx'.2.2
  rw [mem_unitBox2_iff]
  exact ⟨by rw [boxReparam_apply_zero]; exact hshy 0,
         by rw [boxReparam_apply_one]; exact hshy 1,
         by rw [boxReparam_apply_two]; exact htx⟩

lemma boxReparam_injOn (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    Set.InjOn (boxReparam q r) (Submission.Drive.unitBox 2) := by
  intro x hx x' hx' heq
  have hx'2 := hx; rw [mem_unitBox2_iff] at hx'2
  have hy' := hx'; rw [mem_unitBox2_iff] at hy'
  have hy : mk2CLM x ∈ Submission.Drive.unitBox 1 := mk2CLM_mem_unitBox_one hx
  have hy1 : mk2CLM x' ∈ Submission.Drive.unitBox 1 := mk2CLM_mem_unitBox_one hx'
  have hshear : shear q (mk2CLM x) = shear q (mk2CLM x') := by
    ext i
    fin_cases i
    · have h := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 0) heq
      simpa using h
    · have h := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 1) heq
      simpa using h
  have hyeq : mk2CLM x = mk2CLM x' := (shear_box_bijOn q).1.2.1 hy hy1 hshear
  have ht : thetaS r (x 2) = thetaS r (x' 2) := by
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 2) heq
    simpa using h
  have h2 : x 2 = x' 2 := (thetaS_props r).1.2.1 hx'2.2.2 hy'.2.2 ht
  have h0 : x 0 = x' 0 := by
    have h := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 0) hyeq; simpa using h
  have h1 : x 1 = x' 1 := by
    have h := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 1) hyeq; simpa using h
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

lemma boxReparam_surjOn (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    Set.SurjOn (boxReparam q r) (Submission.Drive.unitBox 2) (Submission.Drive.unitBox 2) := by
  intro z hz
  have hz' := hz; rw [mem_unitBox2_iff] at hz'
  have hz2 : mk2CLM z ∈ Submission.Drive.unitBox 1 := mk2CLM_mem_unitBox_one hz
  obtain ⟨y, hy, hyeq⟩ := (shear_box_bijOn q).1.2.2 hz2
  obtain ⟨t, ht, ht2⟩ := (thetaS_props r).1.2.2 hz'.2.2
  refine ⟨mk3 y t, ?_, ?_⟩
  · rw [mem_unitBox2_iff]
    have hy' := hy; rw [mem_unitBox1_iff] at hy'
    exact ⟨by simpa using hy'.1, by simpa using hy'.2, by simpa using ht⟩
  · have h1 : mk2CLM (mk3 y t) = y := by
      rw [mk2CLM_apply]; exact mk2_mk3 y t
    have h2 : coordCLM2 (mk3 y t) = t := by simp
    rw [boxReparam, h1, h2, hyeq, ht2]
    exact mk3_mk2CLM_coordCLM2 z

theorem boxReparam_bijOn (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    Set.BijOn (boxReparam q r) (Submission.Drive.unitBox 2) (Submission.Drive.unitBox 2) :=
  ⟨boxReparam_mapsTo q r, boxReparam_injOn q r, boxReparam_surjOn q r⟩

theorem boxReparam_face (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    ∀ x ∈ Submission.Drive.unitBox 2, ∀ i : Fin 3,
      (boxReparam q r x i = 0 ↔ x i = 0) ∧ (boxReparam q r x i = 1 ↔ x i = 1) := by
  intro x hx i
  have hx' := hx; rw [mem_unitBox2_iff] at hx'
  have hy : mk2CLM x ∈ Submission.Drive.unitBox 1 := mk2CLM_mem_unitBox_one hx
  fin_cases i
  · have h := (shear_box_bijOn q).2 (mk2CLM x) hy 0
    exact ⟨by simpa [boxReparam, mk2CLM_apply] using h.1,
           by simpa [boxReparam, mk2CLM_apply] using h.2⟩
  · have h := (shear_box_bijOn q).2 (mk2CLM x) hy 1
    exact ⟨by simpa [boxReparam, mk2CLM_apply] using h.1,
           by simpa [boxReparam, mk2CLM_apply] using h.2⟩
  · have h := (thetaS_props r).2.1 (x 2) hx'.2.2
    exact ⟨by simpa [boxReparam] using h.1, by simpa [boxReparam] using h.2⟩

/-! ## The point derivative of the shear and of the twist -/

/-- The cross-shear is differentiable at every point, with derivative its `fderiv`. -/
lemma hasFDerivAt_shear (q : EuclideanSpace ℝ (Fin 4)) (y : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (shear q) (fderiv ℝ (shear q) y) y := by
  have hdiff : DifferentiableAt ℝ (shear q) y := by
    have hcomp : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 2) => shear₂ q (shear₁ q z)) _ y :=
      (hasFDerivAt_shear₂ q (shear₁ q y)).comp y (hasFDerivAt_shear₁ q y)
    show DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin 2) => shear₂ q (shear₁ q z)) y
    exact hcomp.differentiableAt
  exact hdiff.hasFDerivAt

/-- The derivative of the level twist at a point, as a scalar multiple of the identity. -/
def thetaSDeriv (r x : ℝ) : ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ (1 + clamp1 r * (1 - 2 * x))

@[simp] lemma thetaSDeriv_apply (r x w : ℝ) :
    thetaSDeriv r x w = w * (1 + clamp1 r * (1 - 2 * x)) := by
  simp [thetaSDeriv, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The twist is differentiable at every point, with the explicit derivative `thetaSDeriv`. -/
lemma hasFDerivAt_thetaS (r x : ℝ) : HasFDerivAt (thetaS r) (thetaSDeriv r x) x := by
  have hd : HasDerivAt (thetaS r) (1 + clamp1 r * (1 - 2 * x)) x := by
    have h1 : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
    have h2 : HasDerivAt (fun z : ℝ => clamp1 r * hb z) (clamp1 r * (1 - 2 * x)) x :=
      (hasDerivAt_hb x).const_mul (clamp1 r)
    have h3 : HasDerivAt (fun z : ℝ => z + clamp1 r * hb z) (1 + clamp1 r * (1 - 2 * x)) x :=
      h1.add h2
    change HasDerivAt (fun z : ℝ => z + clamp1 r * hb z) (1 + clamp1 r * (1 - 2 * x)) x
    exact h3
  simpa only [thetaSDeriv] using hd.hasFDerivAt


/-- **The box reparametrisation of the `hodd` family is smooth.** -/
theorem contDiff_boxReparam (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (boxReparam q r) := by
  have hsh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => shear q (mk2CLM x)) :=
    contDiff_shear_thetaS.1.comp (contDiff_const.prodMk mk2CLM.contDiff)
  have htw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => thetaS r (coordCLM2 x)) :=
    contDiff_shear_thetaS.2.comp (contDiff_const.prodMk coordCLM2.contDiff)
  rw [show boxReparam q r = fun x : EuclideanSpace ℝ (Fin 3) =>
      WithLp.toLp 2 (![(shear q (mk2CLM x)) 0, (shear q (mk2CLM x)) 1,
        thetaS r (coordCLM2 x)] : Fin 3 → ℝ) from rfl]
  rw [contDiff_piLp 2]
  intro i
  fin_cases i
  · exact (coordCLM 0).contDiff.comp hsh
  · exact (coordCLM 1).contDiff.comp hsh
  · exact htw

/-! ## The derivative of the lift -/

/-- The two-component map whose composite with the linear equivalence `mk3CLM` is the box
reparametrisation. -/
def boxPre (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) × ℝ :=
  (shear q (mk2CLM x), thetaS r (coordCLM2 x))

@[simp] lemma mk3CLM_boxPre (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    mk3CLM (boxPre q r x) = boxReparam q r x := by
  dsimp only [boxPre]
  rw [mk3CLM_apply]
  rfl

lemma boxReparam_eq_mk3CLM (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    boxReparam q r = fun x => mk3CLM (boxPre q r x) := by
  funext x
  rw [mk3CLM_boxPre]

/-- **The derivative of the box reparametrisation**: the direct sum of `d shear` (on the plane
coordinates) and of the scalar derivative of the twist (on the level). -/
def boxDeriv (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  mk3CLM.comp (((fderiv ℝ (shear q) (mk2CLM x)).comp mk2CLM).prod
    ((thetaSDeriv r (x 2)).comp coordCLM2))

lemma fderiv_thetaS (r x : ℝ) : fderiv ℝ (thetaS r) x = thetaSDeriv r x :=
  (hasFDerivAt_thetaS r x).fderiv

@[simp] lemma boxDeriv_apply_zero (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    (x v : EuclideanSpace ℝ (Fin 3)) :
    boxDeriv q r x v 0 = ((fderiv ℝ (shear q) (mk2CLM x)) (mk2CLM v)) 0 := by
  simp [boxDeriv]

@[simp] lemma boxDeriv_apply_one (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    (x v : EuclideanSpace ℝ (Fin 3)) :
    boxDeriv q r x v 1 = ((fderiv ℝ (shear q) (mk2CLM x)) (mk2CLM v)) 1 := by
  simp [boxDeriv]

@[simp] lemma boxDeriv_apply_two (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    (x v : EuclideanSpace ℝ (Fin 3)) :
    boxDeriv q r x v 2 = (coordCLM2 v) * (1 + clamp1 r * (1 - 2 * (x 2))) := by
  simp [boxDeriv, thetaSDeriv_apply, coordCLM2_apply]

lemma hasFDerivAt_boxPre (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (boxPre q r) (((fderiv ℝ (shear q) (mk2CLM x)).comp mk2CLM).prod
      ((fderiv ℝ (thetaS r) (coordCLM2 x)).comp coordCLM2)) x := by
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 3) => shear q (mk2CLM x))
      ((fderiv ℝ (shear q) (mk2CLM x)).comp mk2CLM) x :=
    (hasFDerivAt_shear q (mk2CLM x)).comp x mk2CLM.hasFDerivAt
  have h2 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 3) => thetaS r (coordCLM2 x))
      ((thetaSDeriv r (coordCLM2 x)).comp coordCLM2) x :=
    (hasFDerivAt_thetaS r (coordCLM2 x)).comp x coordCLM2.hasFDerivAt
  exact (h1.prodMk h2).congr_fderiv (by simp only [fderiv_thetaS])

/-- **The derivative of the box reparametrisation.** -/
theorem hasFDerivAt_boxReparam (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : HasFDerivAt (boxReparam q r) (boxDeriv q r x) x := by
  have h := (mk3CLM.hasFDerivAt (x := boxPre q r x)).comp x (hasFDerivAt_boxPre q r x)
  rw [boxReparam_eq_mk3CLM q r]
  refine h.congr_fderiv ?_
  ext v
  simp only [boxDeriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderiv_thetaS, coordCLM2_apply]

/-- The twist's derivative at a box point is non-zero: `|clamp1 r| ≤ 1/2` and the level lies in
`[0,1]`. -/
lemma one_add_clamp1_mul_pos {r t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 < 1 + clamp1 r * (1 - 2 * t) := by
  have h1 : |1 - 2 * t| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have h2 : |clamp1 r * (1 - 2 * t)| ≤ 1 / 2 := by
    rw [abs_mul]
    calc |clamp1 r| * |1 - 2 * t| ≤ (1 / 2) * 1 :=
          mul_le_mul (abs_clamp1_le r) h1 (abs_nonneg _) (by norm_num)
      _ = 1 / 2 := by norm_num
  linarith [(abs_le.mp h2).1]

/-- **The derivative of the lift is bijective on the box** (the `hinv` condition). -/
theorem boxReparam_fderiv_bijective (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ Submission.Drive.unitBox 2) :
    Function.Bijective (fderiv ℝ (boxReparam q r) x) := by
  rw [(hasFDerivAt_boxReparam q r x).fderiv]
  have hx' := hx; rw [mem_unitBox2_iff] at hx'
  set c : ℝ := 1 + clamp1 r * (1 - 2 * (x 2)) with hcdef
  have hc : c ≠ 0 := ne_of_gt (by rw [hcdef]; exact one_add_clamp1_mul_pos hx'.2.2)
  set dS : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    fderiv ℝ (shear q) (mk2CLM x) with hdS
  have hSbij : Function.Bijective dS :=
    (shear_fderiv q (y := mk2CLM x) (mk2CLM_mem_unitBox_one hx)).1
  set d : EuclideanSpace ℝ (Fin 3) →L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    (dS.comp mk2CLM).prod ((thetaSDeriv r (x 2)).comp coordCLM2) with hd
  have hker : ∀ z : EuclideanSpace ℝ (Fin 3), d z = 0 → z = 0 := by
    intro z hz
    have hz1 : dS (mk2CLM z) = 0 := by
      have := congrArg Prod.fst hz
      simpa [hd, ContinuousLinearMap.comp_apply] using this
    have hz2 : (thetaSDeriv r (x 2)) (coordCLM2 z) = 0 := by
      have := congrArg Prod.snd hz
      simpa [hd, ContinuousLinearMap.comp_apply] using this
    have h1 : mk2CLM z = 0 := hSbij.1 (by simpa using hz1)
    have h2 : coordCLM2 z = 0 := by
      rw [thetaSDeriv_apply] at hz2
      rcases mul_eq_zero.mp hz2 with h' | h'
      · exact h'
      · exact absurd h' hc
    ext i
    fin_cases i
    · have hh := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 0) h1
      simpa [mk2CLM_apply, mk2] using hh
    · have hh := congrArg (fun y : EuclideanSpace ℝ (Fin 2) => y 1) h1
      simpa [mk2CLM_apply, mk2] using hh
    · simpa [coordCLM2_apply] using h2
  have hinj : Function.Injective d := by
    intro u v huv
    have h0 : d (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker (u - v) h0)
  have hsurj : Function.Surjective d := by
    rintro ⟨a, t⟩
    obtain ⟨w, hw⟩ := hSbij.2 a
    refine ⟨mk3 w (t / c), ?_⟩
    have e1 : mk2CLM (mk3 w (t / c)) = w := by
      rw [mk2CLM_apply]; exact mk2_mk3 w (t / c)
    have e2 : coordCLM2 (mk3 w (t / c)) = t / c := by simp
    simp only [hd, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply, e1, e2,
      thetaSDeriv_apply, hw, Prod.mk.injEq, true_and]
    rw [div_mul_cancel₀ t hc]
  have hcomp : Function.Bijective (mk3CLM.comp d) := mk3CLM_bijective.comp ⟨hinj, hsurj⟩
  have heq : boxDeriv q r x = mk3CLM.comp d := rfl
  rw [heq]
  exact hcomp

/-- **The derivative of the lift preserves the coordinate hyperplanes along the faces** (the
`hnormal` condition). -/
theorem boxReparam_fderiv_normal (q : EuclideanSpace ℝ (Fin 4)) (r : ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ Submission.Drive.unitBox 2) :
    ∀ i : Fin 3, (x i = 0 ∨ x i = 1) → ∀ v : EuclideanSpace ℝ (Fin 3),
      (fderiv ℝ (boxReparam q r) x v) i = 0 ↔ v i = 0 := by
  have hx' := hx; rw [mem_unitBox2_iff] at hx'
  have hy : mk2CLM x ∈ Submission.Drive.unitBox 1 := mk2CLM_mem_unitBox_one hx
  have hS := (shear_fderiv q (y := mk2CLM x) hy).2
  have hc : (0 : ℝ) < 1 + clamp1 r * (1 - 2 * (x 2)) := one_add_clamp1_mul_pos hx'.2.2
  intro i hxi v
  rw [(hasFDerivAt_boxReparam q r x).fderiv]
  fin_cases i
  · have hy0 : (mk2CLM x) 0 = 0 ∨ (mk2CLM x) 0 = 1 := by simpa [mk2CLM_apply] using hxi
    have h := hS 0 hy0 (mk2CLM v)
    simpa [boxDeriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, mk2CLM_apply]
      using h
  · have hy1 : (mk2CLM x) 1 = 0 ∨ (mk2CLM x) 1 = 1 := by simpa [mk2CLM_apply] using hxi
    have h := hS 1 hy1 (mk2CLM v)
    simpa [boxDeriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, mk2CLM_apply]
      using h
  · show (boxDeriv q r x v) 2 = 0 ↔ v 2 = 0
    rw [boxDeriv_apply_two, coordCLM2_apply]
    constructor
    · intro hzero
      rcases mul_eq_zero.mp hzero with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hc)
    · intro hv
      rw [hv, zero_mul]

/-! ## The packaged transfer -/

/-- **The `Meet3Hyp` transfer along a family of box reparametrisations.**  If the chains
`D k ∘ boxReparam (q k) (r k)` satisfy the triple-intersection hypothesis, then so do the chains
`D k`.  This is the form in which the `hodd` chapter consumes `meet3Hyp_of_boxReparam`: its family is
the design's `encFamQ0`, which is `encodedChains (H') A B c₀` composed with the shears and the level
twists.  Block `0` (constant level) is the case `r 0 = 0`. -/
theorem meet3Hyp_of_boxReparam_family {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hsm : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (hseam : ∀ (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)), onSeam x → D k x = D k (seamInv x))
    (q : Fin 3 → EuclideanSpace ℝ (Fin 4)) (r : Fin 3 → ℝ)
    (h : Meet3Hyp M (fun k => D k ∘ boxReparam (q k) (r k))) :
    Meet3Hyp M D :=
  meet3Hyp_of_boxReparam D (fun k => boxReparam (q k) (r k)) hsm hseam
    (fun k => contDiff_boxReparam (q k) (r k))
    (fun k => boxReparam_bijOn (q k) (r k))
    (fun k => boxReparam_face (q k) (r k))
    (fun k x hx => boxReparam_fderiv_bijective (q k) (r k) hx)
    (fun k x hx => boxReparam_fderiv_normal (q k) (r k) hx)
    h

end

end Work.Drive
