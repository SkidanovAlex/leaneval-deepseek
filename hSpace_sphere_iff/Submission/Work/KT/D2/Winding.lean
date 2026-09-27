import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.D2.Basic
import Submission.Work.KT.D2.circle_degree
import Submission.Work.KT.D2.disc_boundary_log
import Submission.Work.KT.D2.loop_cone_extend
import Submission.Work.KT.D2.idem_conj_target_boundary
import Submission.Work.KT.D2.idem_conj_of_rank_eq

/-!
# `Work.KT.D2.Winding` — the winding invariant of an idempotent over `D²/S¹`

The reduced group `K̃(D²/S¹)` is classified by two integers: the rank at the boundary point and a
winding number.  This file builds the winding number.

* §1 transports Mathlib's winding number of loops in `ℂˣ` from `S¹ ⊂ ℂ` to `S¹ ⊂ ℝ²`
  (`Work.KT.D2.circle_degree`), and records the fact (`deg2_comp_inBall`) that the boundary loop of
  a nowhere-zero function that extends over the closed disc has winding `0`.
* §2 sets up the disc model: a matrix `M` over `Kpair ℝ²` is a continuous matrix-valued function on
  the closed disc whose restriction to the boundary circle is constant (`toCM`, `bval`,
  `toCM_inBall`).
* §3 produces, for an idempotent over the disc, a continuous family of units trivialising it to its
  boundary value (`exists_triv`).
* §4 defines the winding of a nowhere-zero complex loop (`degNZ`) and of a loop of units at an
  idempotent `e` (`windLoop`), given by the determinant of its restriction to `im e`.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.KT.D2

open Matrix
open Classical

noncomputable section

/-! ## 1. Winding numbers for loops on `S¹ ⊂ ℝ²` -/

/-- The linear isometry `ℝ² → ℂ`, `(x, y) ↦ x + y·I`. -/
def euc2C : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

@[simp] lemma euc2C_apply (x : EuclideanSpace ℝ (Fin 2)) :
    euc2C x = x 0 + x 1 * Complex.I := rfl

/-- The unit circle of `ℝ²`, mapped into the unit circle of `ℂ`. -/
def sphToC : C(Sph (Euc 2), Metric.sphere (0 : ℂ) 1) :=
  ⟨fun x => ⟨euc2C x, by
      rw [mem_sphere_zero_iff_norm, euc2C.norm_map]
      exact mem_sphere_zero_iff_norm.mp x.2⟩, by
    apply Continuous.subtype_mk
    exact euc2C.continuous.comp continuous_subtype_val⟩

/-- The inverse of `sphToC`. -/
def sphToCInv : C(Metric.sphere (0 : ℂ) 1, Sph (Euc 2)) :=
  ⟨fun z => ⟨euc2C.symm z, by
      rw [mem_sphere_zero_iff_norm, euc2C.symm.norm_map]
      exact mem_sphere_zero_iff_norm.mp z.2⟩, by
    apply Continuous.subtype_mk
    exact euc2C.symm.continuous.comp continuous_subtype_val⟩

@[simp] lemma sphToCInv_sphToC (x : Sph (Euc 2)) : sphToCInv (sphToC x) = x := by
  refine Subtype.ext ?_
  show euc2C.symm (euc2C ↑x) = ↑x
  exact euc2C.symm_apply_apply ↑x

@[simp] lemma sphToC_sphToCInv (z : Metric.sphere (0 : ℂ) 1) : sphToC (sphToCInv z) = z := by
  refine Subtype.ext ?_
  show euc2C (euc2C.symm ↑z) = ↑z
  exact euc2C.apply_symm_apply ↑z

/-- A winding number for loops in `ℂˣ` on the unit circle of `ℂ` (`Work.KT.D2.circle_degree`). -/
def circleDeg : C(Metric.sphere (0 : ℂ) 1, ℂˣ) → ℤ := Classical.choose circle_degree

/-- The winding number of a loop in `ℂˣ` on the unit circle of `ℝ²`. -/
def deg2 (f : C(Sph (Euc 2), ℂˣ)) : ℤ := circleDeg (f.comp sphToCInv)

lemma circleDeg_zero_iff (f : C(Metric.sphere (0 : ℂ) 1, ℂˣ)) :
    circleDeg f = 0 ↔ ∃ F : C(Metric.sphere (0 : ℂ) 1, ℂ),
      ∀ x, Complex.exp (F x) = (f x : ℂ) :=
  (Classical.choose_spec circle_degree).1 f

lemma circleDeg_mul (f g : C(Metric.sphere (0 : ℂ) 1, ℂˣ)) :
    circleDeg (f * g) = circleDeg f + circleDeg g :=
  (Classical.choose_spec circle_degree).2.1 f g

lemma circleDeg_one : circleDeg (1 : C(Metric.sphere (0 : ℂ) 1, ℂˣ)) = 0 :=
  (Classical.choose_spec circle_degree).2.2.1

/-- `deg2 f = 0` exactly when `f` admits a continuous logarithm. -/
lemma deg2_zero_iff (f : C(Sph (Euc 2), ℂˣ)) :
    deg2 f = 0 ↔ ∃ F : C(Sph (Euc 2), ℂ), ∀ x, Complex.exp (F x) = (f x : ℂ) := by
  rw [deg2, circleDeg_zero_iff]
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F.comp sphToC, fun x => by simpa using hF (sphToC x)⟩
  · rintro ⟨F, hF⟩
    exact ⟨F.comp sphToCInv, fun z => by simpa using hF (sphToCInv z)⟩

lemma deg2_mul (f g : C(Sph (Euc 2), ℂˣ)) : deg2 (f * g) = deg2 f + deg2 g := by
  have h : (f * g).comp sphToCInv = (f.comp sphToCInv) * (g.comp sphToCInv) := by
    ext x; rfl
  rw [deg2, deg2, deg2, h, circleDeg_mul]

lemma deg2_one : deg2 (1 : C(Sph (Euc 2), ℂˣ)) = 0 := by
  have h : (1 : C(Sph (Euc 2), ℂˣ)).comp sphToCInv = 1 := by ext x; rfl
  rw [deg2, h, circleDeg_one]

/-- The boundary loop of a `ℂˣ`-valued function on the closed disc has winding zero. -/
lemma deg2_comp_inBall (g : C(Ball (Euc 2), ℂˣ)) : deg2 (g.comp inBallCM) = 0 := by
  rw [deg2_zero_iff]
  simpa [ContinuousMap.comp_apply] using disc_boundary_log g

/-! ## 2. Matrices over `Kpair ℝ²` as disc families -/

/-- Evaluation at a point of the disc, as a ring homomorphism on `Kpair ℝ²`. -/
def evalAt (x : Ball (Euc 2)) : Kpair (Euc 2) →+* ℂ :=
  ((evalC x).comp (Kpair (Euc 2)).val).toRingHom

/-- A matrix over `Kpair ℝ²`, viewed as a continuous matrix-valued function on the closed disc. -/
def toCM (n : ℕ) (M : Matrix (Fin n) (Fin n) (Kpair (Euc 2))) :
    C(Ball (Euc 2), Matrix (Fin n) (Fin n) ℂ) where
  toFun x := M.map (evalAt x)
  continuous_toFun := by
    apply continuous_pi; intro i; apply continuous_pi; intro j
    have h : (fun x : Ball (Euc 2) => M.map (evalAt x) i j)
        = fun x => ((M i j : Kpair (Euc 2)) : C(Ball (Euc 2), ℂ)) x := by
      funext x; rfl
    rw [h]
    exact ((M i j : Kpair (Euc 2)) : C(Ball (Euc 2), ℂ)).continuous

@[simp] lemma toCM_apply (n : ℕ) (M : Matrix (Fin n) (Fin n) (Kpair (Euc 2)))
    (x : Ball (Euc 2)) : toCM n M x = M.map (evalAt x) := rfl

lemma toCM_mul_apply (n : ℕ) (M N : Matrix (Fin n) (Fin n) (Kpair (Euc 2)))
    (x : Ball (Euc 2)) : toCM n (M * N) x = toCM n M x * toCM n N x := by
  rw [toCM_apply, toCM_apply, toCM_apply]
  exact Matrix.map_mul (f := evalAt x)

lemma toCM_one_apply (n : ℕ) (x : Ball (Euc 2)) :
    toCM n (1 : Matrix (Fin n) (Fin n) (Kpair (Euc 2))) x = 1 := by
  rw [toCM_apply]
  exact Matrix.map_one (evalAt x) (map_zero (evalAt x)) (map_one (evalAt x))

/-- The disc family of an idempotent matrix is pointwise idempotent. -/
lemma toCM_idem (n : ℕ) (M : Matrix (Fin n) (Fin n) (Kpair (Euc 2))) (hM : M * M = M)
    (x : Ball (Euc 2)) : toCM n M x * toCM n M x = toCM n M x := by
  rw [← toCM_mul_apply n M M x, hM]

/-- The (constant) boundary value of a matrix over `Kpair ℝ²`. -/
def bval (n : ℕ) (y0 : Ball (Euc 2)) (M : Matrix (Fin n) (Fin n) (Kpair (Euc 2))) :
    Matrix (Fin n) (Fin n) ℂ :=
  M.map (augPair (Euc 2) y0).toRingHom

/-- The unit circle sits in the boundary sphere of the disc. -/
lemma inBall_mem_bdry (x : Sph (Euc 2)) : inBall x ∈ bdry (Euc 2) := by
  show ‖((inBall x : Ball (Euc 2)) : Euc 2)‖ = 1
  rw [inBall_coe, mem_sphere_zero_iff_norm.mp x.2]

lemma evalAt_inBall (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) (x : Sph (Euc 2)) :
    evalAt (inBall x) = (augPair (Euc 2) y0).toRingHom := by
  ext f
  simp only [evalAt, augPair, evalC, AlgHom.comp_apply, AlgHom.coe_toRingHom,
    ContinuousMap.evalAlgHom_apply]
  exact f.2 (inBall x) (inBall_mem_bdry x) y0 hy0

/-- On the boundary circle, the disc family of a matrix over `Kpair ℝ²` is its boundary value. -/
lemma toCM_inBall (n : ℕ) (M : Matrix (Fin n) (Fin n) (Kpair (Euc 2)))
    (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) (x : Sph (Euc 2)) :
    toCM n M (inBall x) = bval n y0 M := by
  rw [toCM_apply, bval, evalAt_inBall y0 hy0 x]

/-! ## 3. Trivialising an idempotent at its boundary value -/

/-- The straight-line homotopy from the constant map at `y0` to the identity of the disc. -/
def Kline (y0 : Ball (Euc 2)) : C(unitInterval × Ball (Euc 2), Ball (Euc 2)) :=
  ⟨fun p => ⟨(1 - (p.1 : ℝ)) • (y0 : Euc 2) + (p.1 : ℝ) • (p.2 : Euc 2), by
      have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
      have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
      have hy : ‖(y0 : Euc 2)‖ ≤ 1 := norm_le_one_ball y0
      have hx : ‖(p.2 : Euc 2)‖ ≤ 1 := norm_le_one_ball p.2
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      calc ‖(1 - (p.1 : ℝ)) • (y0 : Euc 2) + (p.1 : ℝ) • (p.2 : Euc 2)‖
          ≤ ‖(1 - (p.1 : ℝ)) • (y0 : Euc 2)‖ + ‖(p.1 : ℝ) • (p.2 : Euc 2)‖ := norm_add_le _ _
        _ = (1 - (p.1 : ℝ)) * ‖(y0 : Euc 2)‖ + (p.1 : ℝ) * ‖(p.2 : Euc 2)‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (p.1 : ℝ)), abs_of_nonneg ht0]
        _ ≤ 1 := by nlinarith [hy, hx, ht0, ht1]⟩, by fun_prop⟩

@[simp] lemma Kline_zero (y0 : Ball (Euc 2)) (x : Ball (Euc 2)) :
    Kline y0 (0, x) = y0 := by
  apply Subtype.ext; simp [Kline]

@[simp] lemma Kline_one (y0 : Ball (Euc 2)) (x : Ball (Euc 2)) :
    Kline y0 (1, x) = x := by
  apply Subtype.ext; simp [Kline]

/-- Every idempotent matrix on the closed disc is trivialised, by continuous families of units,
to its value at `y0`. -/
lemma exists_triv (y0 : Ball (Euc 2)) (n : ℕ)
    (p : C(Ball (Euc 2), Matrix (Fin n) (Fin n) ℂ)) (hp : ∀ x, p x * p x = p x) :
    ∃ u v : C(Ball (Euc 2), Matrix (Fin n) (Fin n) ℂ),
      (∀ x, u x * v x = 1 ∧ v x * u x = 1) ∧ (∀ x, u x * p x * v x = p y0) :=
  idem_conj_target_boundary (Ball (Euc 2)) y0 (Kline y0) (Kline_zero y0) (Kline_one y0) n p hp

/-! ## 4. Winding numbers of nowhere-zero loops and of loops of units -/

/-- The value of the homeomorphism `ℂˣ ≃ₜ {z : ℂ // z ≠ 0}` on an inverse image. -/
lemma unitsHomeo_symm_val (z : {z : ℂ // z ≠ 0}) :
    (((unitsHomeomorphNeZero (G₀ := ℂ)).symm z : ℂˣ) : ℂ) = ↑z := by
  have h := congrArg Subtype.val
    (Homeomorph.apply_symm_apply (unitsHomeomorphNeZero (G₀ := ℂ)) z)
  have h' : (↑((unitsHomeomorphNeZero (G₀ := ℂ))
      ((unitsHomeomorphNeZero (G₀ := ℂ)).symm z)) : ℂ)
      = ↑((unitsHomeomorphNeZero (G₀ := ℂ)).symm z) := rfl
  rw [h'] at h
  exact h

/-- The units underlying a nowhere-zero complex loop. -/
def toUnits (f : C(Sph (Euc 2), ℂ)) (hf : ∀ x, f x ≠ 0) : C(Sph (Euc 2), ℂˣ) :=
  ⟨fun x => (unitsHomeomorphNeZero (G₀ := ℂ)).symm ⟨f x, hf x⟩,
    (unitsHomeomorphNeZero (G₀ := ℂ)).symm.continuous.comp
      (Continuous.subtype_mk f.continuous hf)⟩

@[simp] lemma toUnits_apply (f : C(Sph (Euc 2), ℂ)) (hf : ∀ x, f x ≠ 0) (x : Sph (Euc 2)) :
    toUnits f hf x = (unitsHomeomorphNeZero (G₀ := ℂ)).symm ⟨f x, hf x⟩ := rfl

@[simp] lemma toUnits_val (f : C(Sph (Euc 2), ℂ)) (hf : ∀ x, f x ≠ 0) (x : Sph (Euc 2)) :
    ((toUnits f hf x : ℂˣ) : ℂ) = f x :=
  unitsHomeo_symm_val ⟨f x, hf x⟩

/-- The units underlying a nowhere-zero complex function on the closed disc. -/
def toUnitsBall (g : C(Ball (Euc 2), ℂ)) (hg : ∀ y, g y ≠ 0) : C(Ball (Euc 2), ℂˣ) :=
  ⟨fun y => (unitsHomeomorphNeZero (G₀ := ℂ)).symm ⟨g y, hg y⟩,
    (unitsHomeomorphNeZero (G₀ := ℂ)).symm.continuous.comp
      (Continuous.subtype_mk g.continuous hg)⟩

@[simp] lemma toUnitsBall_apply (g : C(Ball (Euc 2), ℂ)) (hg : ∀ y, g y ≠ 0)
    (y : Ball (Euc 2)) :
    toUnitsBall g hg y = (unitsHomeomorphNeZero (G₀ := ℂ)).symm ⟨g y, hg y⟩ := rfl

@[simp] lemma toUnitsBall_val (g : C(Ball (Euc 2), ℂ)) (hg : ∀ y, g y ≠ 0)
    (y : Ball (Euc 2)) : ((toUnitsBall g hg y : ℂˣ) : ℂ) = g y :=
  unitsHomeo_symm_val ⟨g y, hg y⟩

/-- The winding number of a nowhere-zero complex loop on `S¹ ⊂ ℝ²`. -/
def degNZ (f : C(Sph (Euc 2), ℂ)) (hf : ∀ x, f x ≠ 0) : ℤ := deg2 (toUnits f hf)

lemma degNZ_zero_iff (f : C(Sph (Euc 2), ℂ)) (hf : ∀ x, f x ≠ 0) :
    degNZ f hf = 0 ↔ ∃ F : C(Sph (Euc 2), ℂ), ∀ x, Complex.exp (F x) = f x := by
  have h0 : degNZ f hf = deg2 (toUnits f hf) := rfl
  rw [h0, deg2_zero_iff]
  refine exists_congr fun F => ?_
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rw [h x, toUnits_val]
  · rw [h x, toUnits_val]

lemma degNZ_proof_irrel (f : C(Sph (Euc 2), ℂ)) (h h' : ∀ x, f x ≠ 0) :
    degNZ f h = degNZ f h' := by
  unfold degNZ
  congr 1

lemma degNZ_mul (f g : C(Sph (Euc 2), ℂ)) (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0)
    (hfg : ∀ x, (f * g) x ≠ 0) : degNZ (f * g) hfg = degNZ f hf + degNZ g hg := by
  have h : toUnits (f * g) hfg = toUnits f hf * toUnits g hg := by
    apply ContinuousMap.ext
    intro x
    apply Units.ext
    simp only [toUnits_apply, Units.val_mul, ContinuousMap.mul_apply, unitsHomeo_symm_val]
  have h0 : degNZ (f * g) hfg = deg2 (toUnits (f * g) hfg) := rfl
  have h1 : degNZ f hf = deg2 (toUnits f hf) := rfl
  have h2 : degNZ g hg = deg2 (toUnits g hg) := rfl
  rw [h0, h1, h2, h, deg2_mul]

/-- The boundary loop of a nowhere-zero complex function on the closed disc has winding zero. -/
lemma degNZ_comp_inBall (g : C(Ball (Euc 2), ℂ)) (hg : ∀ y, g y ≠ 0) :
    degNZ (g.comp inBallCM) (fun x => hg (inBall x)) = 0 := by
  have hf : ∀ x : Sph (Euc 2), (g.comp inBallCM) x ≠ 0 := fun x => hg (inBall x)
  change degNZ (g.comp inBallCM) hf = 0
  have h : toUnits (g.comp inBallCM) hf = (toUnitsBall g hg).comp inBallCM := by
    apply ContinuousMap.ext
    intro x
    apply Units.ext
    rw [ContinuousMap.comp_apply, toUnits_val, toUnitsBall_val]
    rfl
  have h0 : degNZ (g.comp inBallCM) hf = deg2 (toUnits (g.comp inBallCM) hf) := rfl
  rw [h0, h, deg2_comp_inBall (toUnitsBall g hg)]

/-- The winding of a loop of units `γ` at an idempotent `e`, measured through `im e`: the degree
of the determinant of the restriction of `γ` to `im e`. -/
def windLoop (n : ℕ) (e : Matrix (Fin n) (Fin n) ℂ)
    (γ : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ x, Matrix.det (e * γ x * e + (1 - e)) ≠ 0) : ℤ :=
  degNZ ⟨fun x => Matrix.det (e * γ x * e + (1 - e)), by
    have hcont : Continuous fun x : Sph (Euc 2) => e * γ x * e + (1 - e) := by fun_prop
    exact hcont.matrix_det⟩ h

/-! ## 5. Trivialisations of an idempotent over `Kpair ℝ²` -/

/-- The boundary value of an idempotent matrix over `Kpair ℝ²` is idempotent. -/
lemma bval_idem (n : ℕ) (y0 : Ball (Euc 2)) (M : Matrix (Fin n) (Fin n) (Kpair (Euc 2)))
    (hM : M * M = M) : bval n y0 M * bval n y0 M = bval n y0 M := by
  show M.map (augPair (Euc 2) y0).toRingHom * M.map (augPair (Euc 2) y0).toRingHom
      = M.map (augPair (Euc 2) y0).toRingHom
  rw [← Matrix.map_mul, hM]

/-- The disc family evaluated at `y0` is the boundary value. -/
@[simp] lemma toCM_bval (n : ℕ) (y0 : Ball (Euc 2))
    (M : Matrix (Fin n) (Fin n) (Kpair (Euc 2))) : toCM n M y0 = bval n y0 M := rfl

/-- Every idempotent matrix over `Kpair ℝ²` is trivialised, by continuous families of units on the
disc, to its boundary value (in the "conjugated" form). -/
lemma exists_triv' (y0 : Ball (Euc 2)) (P : Mat (Kpair (Euc 2))) (hP : P.IsIdem) :
    ∃ u v : C(Ball (Euc 2), Matrix (Fin P.1) (Fin P.1) ℂ),
      (∀ x, u x * v x = 1) ∧ (∀ x, v x * u x = 1) ∧
      (∀ x, u x * toCM P.1 P.2 x = bval P.1 y0 P.2 * u x) := by
  obtain ⟨u, v, huv, hpv⟩ := exists_triv y0 P.1 (toCM P.1 P.2) (fun x => toCM_idem P.1 P.2 hP x)
  refine ⟨u, v, fun x => (huv x).1, fun x => (huv x).2, fun x => ?_⟩
  have h : u x * toCM P.1 P.2 x * v x = bval P.1 y0 P.2 := hpv x
  calc u x * toCM P.1 P.2 x
      = u x * toCM P.1 P.2 x * (v x * u x) := by rw [(huv x).2, Matrix.mul_one]
    _ = (u x * toCM P.1 P.2 x * v x) * u x := by noncomm_ring
    _ = bval P.1 y0 P.2 * u x := by rw [h]

/-- A chosen trivialising family for an idempotent over `Kpair ℝ²`. -/
noncomputable def trivU (y0 : Ball (Euc 2)) (P : Mat (Kpair (Euc 2))) (hP : P.IsIdem) :
    C(Ball (Euc 2), Matrix (Fin P.1) (Fin P.1) ℂ) :=
  Classical.choose (exists_triv' y0 P hP)

/-- The chosen companion (inverse family) of `trivU`. -/
noncomputable def trivV (y0 : Ball (Euc 2)) (P : Mat (Kpair (Euc 2))) (hP : P.IsIdem) :
    C(Ball (Euc 2), Matrix (Fin P.1) (Fin P.1) ℂ) :=
  Classical.choose (Classical.choose_spec (exists_triv' y0 P hP))

lemma trivU_spec (y0 : Ball (Euc 2)) (P : Mat (Kpair (Euc 2))) (hP : P.IsIdem) :
    (∀ x, trivU y0 P hP x * trivV y0 P hP x = 1) ∧
    (∀ x, trivV y0 P hP x * trivU y0 P hP x = 1) ∧
    (∀ x, trivU y0 P hP x * toCM P.1 P.2 x = bval P.1 y0 P.2 * trivU y0 P hP x) :=
  Classical.choose_spec (Classical.choose_spec (exists_triv' y0 P hP))

end

end Work.KT.D2
