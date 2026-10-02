import Mathlib
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.PTGeometric.flatCoordModel
import Submission.Work.PTGeometric.exists_model_submersion_at_mem_core
import Submission.Work.ThomBordism.genLoopListConcatStep_snd_eq_of_index
import Submission.Work.PTGeometric.genLoopListConcat_eq_block

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.ThomBordism.LeadChapter` — definitions for the tube determinant (S3)

The vocabulary of the proof of `Work.ThomBordism.LeadChapter.chapter_tubeDet`: the affine block
model of the tube point (`affLoc`), its explicit inverse (`affInv`), and the spatial map of the
collar chart (`xiCoord`, `spatialMap`).

No `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open CategoryTheory

namespace Work.ThomBordism.LeadChapter

open Work.PTGeometric

noncomputable section

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k} {ι : Type} [Fintype ι]
  {Fam : ι → Work.ThomBordism.Man8}

/-! ## The affine block model of the tube point -/

/-- The source point (in the half-space) whose spatial coordinates are `v` and whose time is `0`. -/
def srcOfSpatial (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 8))) :
    EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
  srcCastInv k (consCLM (k + 8) (0, v))

/-- **The affine block model of the tube point**: the tube point of the piece, read through the
block reparametrisation of the cube of the source construction. -/
def affLoc (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) : EuclideanSpace ℝ (Fin (8 + k)) :=
  modelEuc G (cZero k) (cOne k) k₀ j₀ (srcOfSpatial k v)

/-- The cube coordinate of a point of the tube: the inverse of the affine realisation of the cube
of radius `G.R`. -/
def cubeOfTube (G : GenuineTubeGeometry k D ι Fam) (u : EuclideanSpace ℝ (Fin (8 + k)))
    (i : Fin (8 + k)) : ℝ :=
  u i / (2 * G.R) + 1 / 2

/-- The affine inverse expression of the block reparametrisation, as a real number. -/
def affInvExpn (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (k₀ j₀ : ℕ)
    (u : EuclideanSpace ℝ (Fin (8 + k))) (j : Fin (k + 8)) : ℝ :=
  let W : Fin (k + 8) → ℝ := fun j => cubeOfTube G u (finKR k j)
  if j = cZero k then (W (cZero k) + 1) / (2 : ℝ) ^ (k₀ + 1)
  else if j = cOne k then (W (cOne k) + 1) / (2 : ℝ) ^ (j₀ + 1)
  else W j

/-- **The explicit inverse of the affine block model**: the spatial coordinates of the point whose
tube point is `u`. -/
def affInv (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (k₀ j₀ : ℕ)
    (u : EuclideanSpace ℝ (Fin (8 + k))) : EuclideanSpace ℝ (Fin (k + 8)) :=
  cubeCoordInv (k + 8) (fun j => ptProj (affInvExpn G m k₀ j₀ u j))

/-! ## The spatial coordinates of the collar chart -/

/-- **The spatial coordinates of the source point over the piece point `y'`** in the block of the
piece `a`: the vector `ξ` with `x = h.symm (a, y')` and `ξ = tail (srcCast x)`. -/
def xiCoord (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (a : Fin m × ι) (y' : (Fam a.2).pt) : EuclideanSpace ℝ (Fin (k + 8)) :=
  tail (k + 8) (srcCast k ((h.symm ⟨a, y'⟩).1).1)

/-- **The spatial map of the collar chart**: the piece chart coordinates `w` of a point of the piece
give the spatial coordinates of the corresponding point of the boundary zero set. -/
def spatialMap (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (a : Fin m × ι) (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) :
    EuclideanSpace ℝ (Fin 8) → EuclideanSpace ℝ (Fin (k + 8)) :=
  fun w => xiCoord G m hpow h a
    ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1.symm w)

/-- The source point of the spatial coordinate: its spatial part is `v` and its time coordinate is
`0`. -/
theorem tail_srcCast_srcOfSpatial (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 8))) :
    tail (k + 8) (srcCast k (srcOfSpatial k v)) = v := by
  rw [srcOfSpatial, srcCast_srcCastInv]
  show tailCLM (k + 8) (consCLM (k + 8) (0, v)) = v
  rw [tailCLM_consCLM]

/-! ## The model and its explicit inverse -/

/-- **The block model of the tube point**, as a function of the spatial coordinates of the source. -/
def theta (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) : EuclideanSpace ℝ (Fin (8 + k)) :=
  modelEuc G (cZero k) (cOne k) k₀ j₀ (srcOfSpatial k v)

/-- The inverse of the affine block reparametrisation `modelAffine`, on real coordinate functions. -/
def modelAffineInv (k : ℕ) (k₀ j₀ : ℕ) (w : Fin (8 + k) → ℝ) : Fin (k + 8) → ℝ :=
  fun m => if m = cZero k then (w (finKR k (cZero k)) + 1) / (2 : ℝ) ^ (k₀ + 1)
    else if m = cOne k then (w (finKR k (cOne k)) + 1) / (2 : ℝ) ^ (j₀ + 1)
    else w (finKR k m)

/-- **The explicit inverse of the block model**, as a function of the tube point. -/
def thetaInv (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (k₀ j₀ : ℕ)
    (u : EuclideanSpace ℝ (Fin (8 + k))) : EuclideanSpace ℝ (Fin (k + 8)) :=
  piToEucl (k + 8) (ptCubeInvFun (k + 8) (modelAffineInv k k₀ j₀
    (fun i => (euToPi (8 + k) u) i / (2 * G.R) + 1 / 2)))

/-- The derivative of the block model, in the `Euc`-spelling. -/
def dtheta (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    EuclideanSpace ℝ (Fin (k + 8)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
  fderiv ℝ (theta G m k₀ j₀) v

/-- The derivative of the inverse block model, in the `Euc`-spelling. -/
def dthetaInv (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (k₀ j₀ : ℕ)
    (u : EuclideanSpace ℝ (Fin (8 + k))) :
    EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)) :=
  fderiv ℝ (thetaInv G m k₀ j₀) u


/-- The coordinate reindexing `Euc (Fin (k+8)) → Euc (Fin (8+k))` (the identity on the underlying
values of the indices). -/
def reEK (k : ℕ) : EuclideanSpace ℝ (Fin (k + 8)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
  (piToEucl (8 + k)).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin (8 + k) =>
      (ContinuousLinearMap.proj (R := ℝ) (finKRInv k i)).comp (euToPi (k + 8))))

/-- The inverse coordinate reindexing `Euc (Fin (8+k)) → Euc (Fin (k+8))`. -/
def reEKInv (k : ℕ) : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)) :=
  (piToEucl (k + 8)).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin (k + 8) =>
      (ContinuousLinearMap.proj (R := ℝ) (finKR k i)).comp (euToPi (8 + k))))

/-- The derivative of the block model, as an endomorphism of the space of spatial coordinates. -/
def dthetaEndo (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (k₀ j₀ : ℕ)
    (v : EuclideanSpace ℝ (Fin (k + 8))) :
    EuclideanSpace ℝ (Fin (k + 8)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)) :=
  (reEKInv k).comp (dtheta G m k₀ j₀ v)


/-! ## The block reparametrisation of `blockTubePoint` -/

theorem cZero_eq_outerCoord (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) :
    Work.PTGeometric.cZero k = outerCoord G m := Fin.ext rfl

theorem cOne_eq_innerCoord (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) :
    Work.PTGeometric.cOne k = innerCoord G m := Fin.ext rfl

theorem upd_cZero_eq (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (k₀ : ℕ)
    (Z : Fin (k + 8) → Set.Icc (0 : ℝ) 1) :
    Work.PTGeometric.upd (Work.PTGeometric.cZero k) k₀ Z = Work.PTGeometric.upd (outerCoord G m) k₀ Z := by
  rw [cZero_eq_outerCoord G m]

theorem upd_cOne_eq (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ) (j₀ : ℕ)
    (Z : Fin (k + 8) → Set.Icc (0 : ℝ) 1) :
    Work.PTGeometric.upd (Work.PTGeometric.cOne k) j₀ Z = Work.PTGeometric.upd (innerCoord G m) j₀ Z := by
  rw [cOne_eq_innerCoord G m]

/-- On the open block, `blockTubePoint` is the affine reparametrisation. -/
theorem blockTubePoint_eq_reIdx_upd (G : Work.PTGeometric.GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (Z : Fin (k + 8) → Set.Icc (0 : ℝ) 1) (k₀ j₀ : ℕ) (hk₀ : k₀ < m)
    (hj₀ : j₀ < Fintype.card ι)
    (hlo : 1 < (2 : ℝ) ^ (k₀ + 1) * (Z (Work.PTGeometric.cZero k) : ℝ))
    (hhi : (2 : ℝ) ^ k₀ * (Z (Work.PTGeometric.cZero k) : ℝ) < 1)
    (hlo2 : 1 < (2 : ℝ) ^ (j₀ + 1) * (Z (Work.PTGeometric.cOne k) : ℝ))
    (hhi2 : (2 : ℝ) ^ j₀ * (Z (Work.PTGeometric.cOne k) : ℝ) < 1) :
    blockTubePoint G m Z = Work.PTGeometric.reIdx k
      (Work.PTGeometric.upd (Work.PTGeometric.cOne k) j₀
        (Work.PTGeometric.upd (Work.PTGeometric.cZero k) k₀ Z)) := by
  have hlenOut : (List.ofFn (fun _ : Fin m => Work.PTGeometric.blockInner (D := D) (Fam := Fam) G)).length
      = m := List.length_ofFn
  have hlenIn : (List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)).length
      = Fintype.card ι := List.length_ofFn
  -- the outer block
  have hloO : 1 < (2 : ℝ) ^ (k₀ + 1) * (Z (outerCoord G m) : ℝ) := by
    rw [← cZero_eq_outerCoord G m]; exact hlo
  have hhiO : (2 : ℝ) ^ k₀ * (Z (outerCoord G m) : ℝ) < 1 := by
    rw [← cZero_eq_outerCoord G m]; exact hhi
  have hout : outerStep G m Z = (k₀, Work.PTGeometric.upd (Work.PTGeometric.cZero k) k₀ Z) := by
    rw [outerStep_eq,
      Work.PTGeometric.genLoopListConcatStep_eq_block (outerCoord G m) _ Z k₀ (by rw [hlenOut]; exact hk₀)
        hloO hhiO,
      Work.PTGeometric.blockPt_eq_upd, cZero_eq_outerCoord G m]
  -- the inner block
  have hne' : innerCoord G m ≠ Work.PTGeometric.cZero k := by
    intro h
    have hv : (innerCoord G m).val = (Work.PTGeometric.cZero k).val := congrArg Fin.val h
    simp [Work.ThomBordism.innerCoord, Work.PTGeometric.cZero] at hv
  have hpt : ((outerStep G m Z).2 (innerCoord G m) : ℝ) = (Z (Work.PTGeometric.cOne k) : ℝ) := by
    rw [hout]
    show ((Work.PTGeometric.upd (Work.PTGeometric.cZero k) k₀ Z) (innerCoord G m) : ℝ)
      = (Z (Work.PTGeometric.cOne k) : ℝ)
    rw [Work.PTGeometric.upd_apply_of_ne (Work.PTGeometric.cZero k) k₀ Z hne']
    exact congrArg (fun i => (Z i : ℝ)) (cOne_eq_innerCoord G m).symm
  have hlo2' : 1 < (2 : ℝ) ^ (j₀ + 1) * ((outerStep G m Z).2 (innerCoord G m) : ℝ) := by
    rw [hpt]; exact hlo2
  have hhi2' : (2 : ℝ) ^ j₀ * ((outerStep G m Z).2 (innerCoord G m) : ℝ) < 1 := by
    rw [hpt]; exact hhi2
  have hin : innerStep G m Z = (j₀, Work.PTGeometric.upd (Work.PTGeometric.cOne k) j₀
      (Work.PTGeometric.upd (Work.PTGeometric.cZero k) k₀ Z)) := by
    have h := Work.PTGeometric.genLoopListConcatStep_eq_block (innerCoord G m)
      (List.ofFn (Work.PTGeometric.blockLoop (D := D) (Fam := Fam) G)) (outerStep G m Z).2 j₀
      (by rw [hlenIn]; exact hj₀) hlo2' hhi2'
    rw [innerStep_eq, h, Work.PTGeometric.blockPt_eq_upd, hout, cOne_eq_innerCoord G m]
  rw [blockTubePoint_eq, hin]
  rfl



/-! ## The linear maps of the collar chart -/

/-- **The spatial embedding** `v ↦ (0, v)` of the source: the linear map underlying `srcOfSpatial`. -/
def srcOfSpatialCLM (k : ℕ) :
    EuclideanSpace ℝ (Fin (k + 8)) →L[ℝ] EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
  (srcCastInv k).comp ((consCLM (k + 8)).comp
    (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin (k + 8)))))

theorem srcOfSpatialCLM_apply (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 8))) :
    srcOfSpatialCLM k v = srcOfSpatial k v := rfl

/-- The spatial embedding lands in the boundary stratum: its first coordinate vanishes. -/
theorem srcOfSpatial_zero (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 8))) :
    (srcOfSpatial k v) 0 = 0 := by
  show ((srcCastInv k) ((consCLM (k + 8)) (0, v))) (0 : Fin ((8 + k) + 1)) = 0
  rw [srcCastInv_apply]
  have hc : (Fin.cast (show (8 + k) + 1 = (k + 8) + 1 by omega) (0 : Fin ((8 + k) + 1)))
      = (0 : Fin ((k + 8) + 1)) := Fin.ext rfl
  rw [hc, consCLM_apply_zero]

/-- **The collar direction** `t ↦ t • e₀` of the source. -/
def collarDirCLM (k : ℕ) : ℝ →L[ℝ] EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
  (1 : ℝ →L[ℝ] ℝ).smulRight (eZero (n := (8 + k) + 1))

/-- **The collar coordinate of the source** `z ↦ (z 0) • e₀`, as a continuous linear map. -/
def collarCLM (k : ℕ) :
    Work.ThomBordism.CofAtlas.E9 →L[ℝ] EuclideanSpace ℝ (Fin ((8 + k) + 1)) :=
  (EuclideanSpace.proj (0 : Fin 9) :
      Work.ThomBordism.CofAtlas.E9 →L[ℝ] ℝ).smulRight (eZero (n := (8 + k) + 1))

theorem collarCLM_apply (k : ℕ) (z : Work.ThomBordism.CofAtlas.E9) :
    collarCLM k z = (z 0) • (eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1))) := by
  simp [collarCLM, ContinuousLinearMap.smulRight_apply]

/-- **The spatial frame of the collar chart as a block linear map**: the collar direction and the
spatial frame `[∂_t | A]`. -/
def collarB (k : ℕ) (A : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8))) :
    Work.ThomBordism.CofAtlas.E9 →L[ℝ] Work.ThomBordism.CofAtlas.ModN k :=
  (srcOfSpatialCLM k).comp (A.comp (tailCLM 8)) + collarCLM k

theorem srcOfSpatial_tail_srcCast (u : EuclideanSpace ℝ (Fin ((8 + k) + 1)))
    (h0 : u 0 = 0) :
    srcOfSpatial k (tail (k + 8) (srcCast k u)) = u := by
  have hhead : (srcCast k u) 0 = 0 := by
    show head (k + 8) (srcCast k u) = 0
    rw [head_srcCast]; exact h0
  rw [srcOfSpatial, ← hhead]
  show (srcCastInv k) (consCLM (k + 8) ((srcCast k u) 0, tailCLM (k + 8) (srcCast k u))) = u
  rw [consCLM_tail, srcCastInv_srcCast]


/-! ## The spatial derivative of the collar chart and the canonical normal frame -/

/-- **The spatial derivative of the collar chart**: the derivative of the spatial map at the piece
point `y`, i.e. `dθ⁻¹ ∘ d(e_a ∘ φ⁻¹)`. -/
def spatialDeriv (G : GenuineTubeGeometry k D ι Fam) (m : ℕ) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt) :
    EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin (k + 8)) :=
  (dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) ((G.emb a.2).e y)).comp
    (fderiv ℝ (Work.ThomBordism.PontryaginThom.chartRep (G.emb a.2).e
      (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i))
      ((Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1 y))

/-- **The canonical normal frame of the collar chart**: the model inverse of the Gauss frame of the
collapse, transported to the source coordinates. -/
def frameN (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) (y : (Fam a.2).pt)
    (z : Work.ThomBordism.CofAtlas.E9)
    (hne : srcHf G m hpow (collarPiece G m hpow h a i z) ≠ D.t₀) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] Work.ThomBordism.CofAtlas.ModN k :=
  (srcOfSpatialCLM k).comp
    ((dthetaInv G m (a.1 : ℕ) (Fintype.equivFin ι a.2 : ℕ) ((G.emb a.2).e y)).comp
      ((projEuc k G.mU G.hmU).comp
        (ogFrameCLM (G.gauss ⟨srcHf G m hpow (collarPiece G m hpow h a i z), hne⟩))))


/-- The reindexing sends the first basis vector to the first basis vector. -/
theorem srcCast_eZero (k : ℕ) :
    srcCast k (eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))
      = (eZero : EuclideanSpace ℝ (Fin ((k + 8) + 1))) := by
  ext i
  show (srcCast k (eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))).ofLp i
    = (eZero : EuclideanSpace ℝ (Fin ((k + 8) + 1))).ofLp i
  rw [srcCast_apply]
  by_cases hi : i = 0
  · subst hi
    rw [Fin.cast_zero, eZero_apply, eZero_apply]
  · have hcast : (Fin.cast (show (k + 8) + 1 = (8 + k) + 1 by omega) i
        : Fin ((8 + k) + 1)) ≠ 0 := by
      intro hh
      exact hi (Fin.ext (by simpa using congrArg Fin.val hh))
    rw [eZero_apply_ne hcast, eZero_apply_ne hi]

/-- The tail of the reindexed first basis vector vanishes. -/
theorem tailCLM_srcCast_eZero (k : ℕ) :
    tailCLM (k + 8) (srcCast k (eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))) = 0 := by
  ext i
  show tailCLM (k + 8) (srcCast k (eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))) i = 0
  rw [tailCLM_apply, srcCast_apply, eZero_apply_ne]
  intro h
  exact absurd (congrArg Fin.val h) (by simp)

/-- **The spatial part of the collar point**: the spatial coordinates of the source point with the
collar coordinate `t` are those of the spatial embedding. -/
theorem tail_srcCast_srcOfSpatial_add (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 8))) (t : ℝ) :
    tail (k + 8) (srcCast k ((srcOfSpatial k v) + t • (eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))))
      = v := by
  have h1 : srcCast k ((srcOfSpatial k v) + t • (eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1))))
      = srcCast k (srcOfSpatial k v) + t • srcCast k (eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1))) := by
    rw [map_add, map_smul]
  rw [h1]
  show tailCLM (k + 8) (srcCast k (srcOfSpatial k v)
      + t • srcCast k (eZero : EuclideanSpace ℝ (Fin ((8 + k) + 1)))) = v
  rw [map_add, map_smul, tailCLM_srcCast_eZero, smul_zero, add_zero]
  show tailCLM (k + 8) (srcCast k (srcOfSpatial k v)) = v
  rw [srcOfSpatial, srcCast_srcCastInv, tailCLM_consCLM]

end

end Work.ThomBordism.LeadChapter
