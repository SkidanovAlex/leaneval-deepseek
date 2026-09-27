import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.SphereSetup
import Submission.Work.KT.DiskAux
import Submission.Work.KT.diskQuotSurj
import Submission.Work.KT.diskQuot
import Submission.Work.KT.SphereAux

/-!
# Definitions for the disc-model Hopf clutching lemma

The disc-model Hopf idempotent `Work.KT.D2.PAM` is the rank-one projection onto the line spanned
by the Hopf vector `(1 + x₂, x₀ + i x₁)` at the point `x = qc 2 y ∈ S²`.

To stay independent of `Submission.Work.KT.D2.Basic` (and of the modules that file imports), this
file contains self-contained copies of the few definitions of that file which are needed here:

* `qcMapA`, `PsiA`, `X0A`, `X1A`, `X2A`, `PAMA` — a copy of the disc-model Hopf idempotent
  `Work.KT.D2.PAM`, with `PAMA` definitionally equal to `PAM`;
* `inBallA` — a copy of `inBall`;
* `sphCoord k`, `sphCoordR` — the coordinates of `qc 2 y ∈ S²`, as continuous functions;
* `hv1 y = 1 + x₂`, `hv2 y = x₀ + i x₁` — the components of the (unnormalised) Hopf vector;
* `hvN2 y` — its squared norm;
* `hopfU y` — the matrix with first column the Hopf vector and second column its perpendicular;
* `PyA y` — the value of the Hopf idempotent at `y`;
* `Cm u y = (hvN2 y)⁻¹ • (hopfU y)ᴴ * u y` — the clutching family `u_c^* u`;
* `radCM r` — the radial map `S¹ → D²`, `x ↦ r • x`;
* `loopC u r …` — the loop `x ↦ (Cm u (r • x)) 0 0` in `ℂˣ`.
-/

namespace Work.KT.D2

open Matrix

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

/-- The euclidean plane `ℝ²`. -/
abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

/-- The closed unit disc `D² ⊂ ℝ²`. -/
abbrev Dc : Type := Work.KT.Ball E2

/-- The unit circle `S¹ ⊂ ℝ²`. -/
abbrev Sc : Type := Work.KT.Sph E2

/-- The unit circle `S¹ ⊂ ℂ`. -/
abbrev Circ : Type := Metric.sphere (0 : ℂ) 1

lemma norm_coe_sphere (x : Sc) : ‖(x : E2)‖ = 1 := by
  have h := Metric.mem_sphere.mp x.2
  rwa [dist_eq_norm, sub_zero] at h

lemma ne_zero_of_sphere (x : Sc) : (x : E2) ≠ 0 := by
  intro h
  have h1 := norm_coe_sphere x
  rw [h, norm_zero] at h1
  exact one_ne_zero h1.symm

/-- The centre of the disc. -/
def dctr : Dc := ⟨0, by rw [Metric.mem_closedBall, dist_self]; norm_num⟩

@[simp] lemma dctr_coe : ((dctr : Dc) : E2) = 0 := rfl

/-! ## Self-contained copy of the disc-model Hopf idempotent -/

/-- The `i`-th coordinate of a point of `S² = Sph (ModelSphere 2)`, as a complex function. -/
def mcEA (i : Fin 2) : C(Work.KT.ModelSphere 2, ℂ) :=
  ⟨fun x => (((x.fst) i : ℝ) : ℂ),
    Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj i).continuous.comp (WithLp.fstL 2 ℝ (Euc 2) ℝ).continuous)⟩

/-- The last coordinate of a point of `S²`, as a complex function. -/
def mcRA : C(Work.KT.ModelSphere 2, ℂ) :=
  ⟨fun x => (((x.snd : ℝ)) : ℂ),
    Complex.continuous_ofReal.comp (WithLp.sndL 2 ℝ (Euc 2) ℝ).continuous⟩

/-- The first two coordinates on `S²`. -/
def scEA (i : Fin 2) : C(Work.KT.Sph (Work.KT.ModelSphere 2), ℂ) :=
  (mcEA i).comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The third coordinate on `S²`. -/
def scRA : C(Work.KT.Sph (Work.KT.ModelSphere 2), ℂ) :=
  mcRA.comp ⟨Subtype.val, continuous_subtype_val⟩

lemma qcMapA_isQuot :
    Topology.IsQuotientMap (Work.KT.qc 2 : C(Dc, Work.KT.Sph (Work.KT.ModelSphere 2))) :=
  Topology.IsQuotientMap.of_surjective_continuous (Work.KT.diskQuotSurj 2 (by norm_num))
    (Work.KT.qc 2).continuous

lemma qcMapA_fib : ∀ x x' : Dc, Work.KT.qc 2 x = Work.KT.qc 2 x' →
    x = x' ∨ (x ∈ Work.KT.bdry E2 ∧ x' ∈ Work.KT.bdry E2) :=
  fun x x' h => (Work.KT.qc_eq_iff 2 x x').mp h

lemma qcMapA_bdry : ∀ x ∈ Work.KT.bdry E2,
    Work.KT.qc 2 x = Work.KT.sphKT_northPole 2 :=
  fun x hx => Work.KT.qc_bdry 2 x hx

/-- The algebra isomorphism `C(S², ℂ) ≅ Kpair ℝ²` of the disc model. -/
def PsiA : C(Work.KT.Sph (Work.KT.ModelSphere 2), ℂ) ≃ₐ[ℂ] Work.KT.Kpair E2 :=
  Work.KT.sphKT_diskQuotAlgEquiv 2 (Work.KT.qc 2) qcMapA_isQuot qcMapA_fib qcMapA_bdry

/-- The coordinate functions of `S²`, pulled back to `Kpair ℝ²`. -/
def X0A : Work.KT.Kpair E2 := PsiA (scEA 0)
def X1A : Work.KT.Kpair E2 := PsiA (scEA 1)
def X2A : Work.KT.Kpair E2 := PsiA scRA

/-- A copy of the disc-model Hopf idempotent `Work.KT.D2.PAM`. -/
def PAMA : Matrix (Fin 2) (Fin 2) (Work.KT.Kpair E2) :=
  !![algebraMap ℂ (Work.KT.Kpair E2) (1 / 2) * (1 + X2A),
     algebraMap ℂ (Work.KT.Kpair E2) (1 / 2)
       * (X0A - algebraMap ℂ (Work.KT.Kpair E2) Complex.I * X1A);
     algebraMap ℂ (Work.KT.Kpair E2) (1 / 2)
       * (X0A + algebraMap ℂ (Work.KT.Kpair E2) Complex.I * X1A),
     algebraMap ℂ (Work.KT.Kpair E2) (1 / 2) * (1 - X2A)]

/-- The inclusion of the unit circle in the disc. -/
def inBallA (x : Sc) : Dc := ⟨(x : E2), by rw [Metric.mem_closedBall, dist_zero_right, norm_coe_sphere]⟩

@[simp] lemma inBallA_coe (x : Sc) : ((inBallA x : Dc) : E2) = (x : E2) := rfl

/-- The evaluation of `PsiA` at a point of the disc. -/
lemma augPair_PsiA (y : Dc) (h : C(Work.KT.Sph (Work.KT.ModelSphere 2), ℂ)) :
    Work.KT.augPair E2 y (PsiA h) = h (Work.KT.qc 2 y) := rfl

/-! ## Coordinates and the Hopf vector -/

/-- The `k`-th coordinate of the point `qc 2 y` of `S²`, as a continuous real function. -/
def sphCoord (k : Fin 2) : C(Dc, ℝ) :=
  ⟨fun y => (((Work.KT.qc 2 y : Work.KT.ModelSphere 2).fst) k), by
    exact Complex.continuous_re.comp
      ((mcEA k).continuous.comp (continuous_subtype_val.comp (Work.KT.qc 2).continuous))⟩

/-- The last coordinate of the point `qc 2 y` of `S²`, as a continuous real function. -/
def sphCoordR : C(Dc, ℝ) :=
  ⟨fun y => ((Work.KT.qc 2 y : Work.KT.ModelSphere 2).snd), by
    exact Complex.continuous_re.comp
      (mcRA.continuous.comp (continuous_subtype_val.comp (Work.KT.qc 2).continuous))⟩

@[simp] lemma sphCoord_apply (k : Fin 2) (y : Dc) :
    sphCoord k y = (((Work.KT.qc 2 y : Work.KT.ModelSphere 2).fst) k) := rfl

@[simp] lemma sphCoordR_apply (y : Dc) :
    sphCoordR y = ((Work.KT.qc 2 y : Work.KT.ModelSphere 2).snd) := rfl

lemma continuous_sphCoord (k : Fin 2) : Continuous (sphCoord k) := (sphCoord k).continuous

lemma continuous_sphCoordR : Continuous sphCoordR := sphCoordR.continuous

/-- The norm of `qc 2 y` is one. -/
lemma qc_norm (y : Dc) : ‖(Work.KT.qc 2 y : Work.KT.ModelSphere 2)‖ = 1 := by
  have h := Metric.mem_sphere.mp (Work.KT.qc 2 y).2
  rwa [dist_eq_norm, sub_zero] at h

/-- The coordinates of `qc 2 y` satisfy the sphere relation. -/
lemma sphCoord_sq (y : Dc) : sphCoord 0 y ^ 2 + sphCoord 1 y ^ 2 + sphCoordR y ^ 2 = 1 := by
  have h := qc_norm y
  have h2 : ‖((Work.KT.qc 2 y : Work.KT.ModelSphere 2).fst)‖ ^ 2
      + ‖((Work.KT.qc 2 y : Work.KT.ModelSphere 2).snd)‖ ^ 2 = 1 := by
    rw [← WithLp.prod_norm_sq_eq_of_L2 (Work.KT.qc 2 y : Work.KT.ModelSphere 2), h, one_pow]
  have hfst : ‖((Work.KT.qc 2 y : Work.KT.ModelSphere 2).fst)‖ ^ 2
      = sphCoord 0 y ^ 2 + sphCoord 1 y ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ)
      ((Work.KT.qc 2 y : Work.KT.ModelSphere 2).fst), Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  have hsnd : ‖((Work.KT.qc 2 y : Work.KT.ModelSphere 2).snd)‖ ^ 2 = sphCoordR y ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    rfl
  linarith

/-- The first component `1 + x₂` of the Hopf vector. -/
def hv1 (y : Dc) : ℝ := 1 + sphCoordR y

/-- The second component `x₀ + i x₁` of the Hopf vector. -/
def hv2 (y : Dc) : ℂ := (sphCoord 0 y : ℂ) + Complex.I * (sphCoord 1 y : ℂ)

/-- The squared norm of the Hopf vector `(1 + x₂, x₀ + i x₁)`. -/
def hvN2 (y : Dc) : ℝ := hv1 y ^ 2 + sphCoord 0 y ^ 2 + sphCoord 1 y ^ 2

lemma continuous_hv1 : Continuous hv1 := continuous_const.add continuous_sphCoordR

lemma continuous_hv2 : Continuous hv2 :=
  (Complex.continuous_ofReal.comp (continuous_sphCoord 0)).add
    (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_sphCoord 1)))

lemma continuous_hvN2 : Continuous hvN2 :=
  ((continuous_hv1.pow 2).add ((continuous_sphCoord 0).pow 2)).add
    ((continuous_sphCoord 1).pow 2)

lemma hvN2_eq (y : Dc) : hvN2 y = 2 * hv1 y := by
  have h := sphCoord_sq y
  unfold hvN2 hv1
  nlinarith [h]

lemma hvN2_nonneg (y : Dc) : 0 ≤ hvN2 y := by
  unfold hvN2; positivity

/-- The (unnormalised) unitary matrix `u_c` whose first column is the Hopf vector. -/
def hopfU (y : Dc) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(hv1 y : ℂ), -(star (hv2 y)); hv2 y, star (hv1 y : ℂ)]

/-- The rank-one projection `diag(1,0)`. -/
def e0 : Matrix (Fin 2) (Fin 2) ℂ := !![(1 : ℂ), 0; 0, 0]

/-- The disc-model Hopf idempotent, evaluated at `y`. -/
def PyA (y : Dc) : Matrix (Fin 2) (Fin 2) ℂ := PAMA.map (Work.KT.augPair E2 y)

/-- The clutching family `u_c^* u` on the punctured disc (`u_c` normalised by the *squared* norm
of the Hopf vector, `u_c^*` the conjugate transpose). -/
def Cm (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ)) (y : Dc) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((hvN2 y : ℂ))⁻¹ • ((hopfU y)ᴴ * u y)

/-- The `(0,0)`-entry of the clutching family, in terms of the Hopf vector. -/
lemma Cm_00 (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ)) (y : Dc) :
    (Cm u y) 0 0 = ((hvN2 y : ℂ))⁻¹ *
      ((hv1 y : ℂ) * (u y) 0 0 + (star (hv2 y)) * (u y) 1 0) := by
  simp [Cm, hopfU, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Complex.conj_ofReal, Matrix.smul_apply]

/-- The point of `S²` above the centre of the disc: the south pole `(0, -1)`. -/
lemma qc_dctr_eq : (Work.KT.qc 2 dctr : Work.KT.ModelSphere 2)
    = WithLp.toLp 2 ((0 : E2), (-1 : ℝ)) := by
  have h : (Work.KT.qc 2 dctr : Work.KT.ModelSphere 2)
      = WithLp.toLp 2 (Work.KT.sfun ‖((dctr : Dc) : E2)‖ • ((dctr : Dc) : E2),
          -Real.cos (Real.pi * ‖((dctr : Dc) : E2)‖)) := rfl
  rw [h, dctr_coe, (WithLp.toLp_injective 2).eq_iff, Prod.mk.injEq]
  constructor
  · rw [show ‖(0 : E2)‖ = (0 : ℝ) from norm_zero, Work.KT.sfun_zero]
    simp
  · simp

/-- The coordinates of the centre of the disc. -/
lemma sphCoord_dctr (k : Fin 2) : sphCoord k dctr = 0 := by
  show (((Work.KT.qc 2 dctr : Work.KT.ModelSphere 2).fst) k) = 0
  rw [qc_dctr_eq]
  simp

lemma sphCoordR_dctr : sphCoordR dctr = -1 := by
  show ((Work.KT.qc 2 dctr : Work.KT.ModelSphere 2).snd) = -1
  rw [qc_dctr_eq]
  simp

lemma hv1_dctr : hv1 dctr = 0 := by
  rw [hv1, sphCoordR_dctr]; norm_num

lemma hvN2_dctr : hvN2 dctr = 0 := by
  rw [hvN2_eq, hv1_dctr]; norm_num

lemma scEA_dctr (i : Fin 2) : scEA i (Work.KT.qc 2 dctr) = 0 := by
  simp only [scEA, ContinuousMap.comp_apply, ContinuousMap.coe_mk, mcEA]
  rw [qc_dctr_eq]
  simp

lemma scRA_dctr : scRA (Work.KT.qc 2 dctr) = -1 := by
  simp only [scRA, ContinuousMap.comp_apply, ContinuousMap.coe_mk, mcRA]
  rw [qc_dctr_eq]
  simp

/-- The disc-model Hopf idempotent at the centre of the disc is `diag(0,1)`. -/
lemma PyA_ctr : PyA dctr = !![(0 : ℂ), 0; 0, 1] := by
  have hX0 : Work.KT.augPair E2 dctr X0A = 0 := by
    rw [X0A, augPair_PsiA, scEA_dctr]
  have hX1 : Work.KT.augPair E2 dctr X1A = 0 := by
    rw [X1A, augPair_PsiA, scEA_dctr]
  have hX2 : Work.KT.augPair E2 dctr X2A = -1 := by
    rw [X2A, augPair_PsiA, scRA_dctr]
  have hI : Work.KT.augPair E2 dctr (algebraMap ℂ (Work.KT.Kpair E2) Complex.I) = Complex.I :=
    AlgHom.commutes _ _
  have hh : Work.KT.augPair E2 dctr (algebraMap ℂ (Work.KT.Kpair E2) (1 / 2 : ℂ))
      = (1 / 2 : ℂ) := AlgHom.commutes _ _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [PyA, Matrix.map_apply, PAMA, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.zero_apply]
  · show Work.KT.augPair E2 dctr (algebraMap ℂ (Work.KT.Kpair E2) (1 / 2) * (1 + X2A)) = 0
    rw [map_mul, map_add, map_one, hh, hX2]; norm_num
  · show Work.KT.augPair E2 dctr
        (algebraMap ℂ (Work.KT.Kpair E2) (1 / 2)
          * (X0A - algebraMap ℂ (Work.KT.Kpair E2) Complex.I * X1A)) = 0
    rw [map_mul, map_sub, map_mul, hh, hX0, hI, hX1]; norm_num
  · show Work.KT.augPair E2 dctr
        (algebraMap ℂ (Work.KT.Kpair E2) (1 / 2)
          * (X0A + algebraMap ℂ (Work.KT.Kpair E2) Complex.I * X1A)) = 0
    rw [map_mul, map_add, map_mul, hh, hX0, hI, hX1]; norm_num
  · show Work.KT.augPair E2 dctr (algebraMap ℂ (Work.KT.Kpair E2) (1 / 2) * (1 - X2A)) = 1
    rw [map_mul, map_sub, map_one, hh, hX2]; norm_num

/-! ## Radial loops -/

/-- The radial map `x ↦ r • x` from the unit circle to the closed disc. -/
def radCM (r : unitInterval) : C(Sc, Dc) where
  toFun x := ⟨(r : ℝ) • (x : E2), by
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg r.2.1, norm_coe_sphere, mul_one]
    exact r.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const : Continuous fun _ : Sc => ((r : ℝ))).smul continuous_subtype_val

@[simp] lemma radCM_coe (r : unitInterval) (x : Sc) :
    ((radCM r x : Dc) : E2) = (r : ℝ) • (x : E2) := rfl

lemma inBallA_eq_radCM_one (x : Sc) : inBallA x = radCM 1 x := by
  apply Subtype.ext
  simp

lemma radCM_ne_ctr {r : unitInterval} (hr : (r : ℝ) ≠ 0) (x : Sc) : radCM r x ≠ dctr := by
  intro h
  have h1 : (r : ℝ) • (x : E2) = 0 := by
    have h2 := congrArg (fun z : Dc => (z : E2)) h
    simpa using h2
  rcases smul_eq_zero.mp h1 with h2 | h2
  · exact hr h2
  · exact ne_zero_of_sphere x h2

/-- A `ℂˣ`-valued map given by a nowhere-vanishing continuous complex function is continuous. -/
lemma continuous_units_mk0 {X : Type*} [TopologicalSpace X] {e : X → ℂ} (he : Continuous e)
    (hne : ∀ x, e x ≠ 0) : Continuous fun x => Units.mk0 (e x) (hne x) := by
  rw [Units.continuous_iff]
  refine ⟨he, ?_⟩
  have h2 : Continuous fun x => (e x)⁻¹ := he.inv₀ hne
  simpa [Units.val_inv_eq_inv_val] using h2

/-- The loop `x ↦ (Cm u (r • x)) 0 0` in `ℂˣ`, for a radius `r ≠ 0`.  The hypotheses `hne` and
`hcont` record the non-vanishing and continuity of `Cm u` off the centre of the disc. -/
def loopC (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ)) (r : unitInterval) (hr : (r : ℝ) ≠ 0)
    (hne : ∀ y : Dc, y ≠ dctr → (Cm u y) 0 0 ≠ 0)
    (hcont : ∀ y : Dc, y ≠ dctr → ContinuousAt (Cm u) y) : C(Sc, ℂˣ) where
  toFun x := Units.mk0 ((Cm u (radCM r x)) 0 0) (hne _ (radCM_ne_ctr hr x))
  continuous_toFun := by
    refine continuous_units_mk0 ?_ (fun x => hne _ (radCM_ne_ctr hr x))
    have h1 : Continuous fun x : Sc => Cm u (radCM r x) := by
      rw [continuous_iff_continuousAt]
      intro x
      exact (hcont _ (radCM_ne_ctr hr x)).comp (radCM r).continuous.continuousAt
    have h2 : Continuous fun x : Sc => (Cm u (radCM r x)) 0 :=
      (continuous_apply (0 : Fin 2)).comp h1
    exact (continuous_apply (0 : Fin 2)).comp h2

@[simp] lemma loopC_coe (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ)) (r : unitInterval)
    (hr : (r : ℝ) ≠ 0) (hne : ∀ y : Dc, y ≠ dctr → (Cm u y) 0 0 ≠ 0)
    (hcont : ∀ y : Dc, y ≠ dctr → ContinuousAt (Cm u) y) (x : Sc) :
    ((loopC u r hr hne hcont x : ℂˣ) : ℂ) = (Cm u (radCM r x)) 0 0 := rfl

end

end Work.KT.D2
