import Mathlib
import Submission.Work.KT.HopfK.Disk
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.hk_relprod
import Submission.Work.KT.ball_K
import Submission.Work.KT.homotopy_inv
import Submission.Work.KT.k0_basic
import Submission.Work.KT.SphereAux
import Submission.Work.KT.diskQuot
import Submission.Work.KT.homotopy_inv

import Submission.Work.KT.Fund.Disc
import Submission.Work.KT.HopfK.augPair_K0_independent

open _root_.Matrix
open Filter

open _root_.Matrix

namespace Work.KT.HopfK

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The lower chart of the target sphere -/

/-- The lower-hemisphere parametrisation in the model `V × ℝ` with the `ℓ²`-norm. -/
def hemiDownF {V : Type} [NormedAddCommGroup V] (v : Ball V) : WithLp 2 (V × ℝ) :=
  WithLp.toLp 2 ((v : V), -Real.sqrt (1 - ‖(v : V)‖ ^ 2))

@[simp] lemma hemiDownF_fst {V : Type} [NormedAddCommGroup V] (v : Ball V) :
    (hemiDownF v).fst = (v : V) := rfl

@[simp] lemma hemiDownF_snd {V : Type} [NormedAddCommGroup V] (v : Ball V) :
    (hemiDownF v).snd = -Real.sqrt (1 - ‖(v : V)‖ ^ 2) := rfl

lemma norm_hemiDownF {V : Type} [NormedAddCommGroup V] (v : Ball V) : ‖hemiDownF v‖ = 1 := by
  have hv : ‖(v : V)‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp v.2
    rwa [dist_eq_norm, sub_zero] at h
  have h1 : (0 : ℝ) ≤ 1 - ‖(v : V)‖ ^ 2 := by nlinarith [hv, norm_nonneg (v : V)]
  have h2 : ‖hemiDownF v‖ ^ 2 = 1 := by
    rw [hemiDownF, WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd, norm_neg,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt h1]
    ring
  nlinarith [norm_nonneg (hemiDownF v), h2]

lemma continuous_hemiDownF {V : Type} [NormedAddCommGroup V] : Continuous (hemiDownF (V := V)) := by
  unfold hemiDownF
  refine (WithLp.prod_continuous_toLp 2 V ℝ).comp ?_
  exact continuous_subtype_val.prodMk (by fun_prop)

/-- The `V`-coordinate of a point of the unit sphere of `V × ℝ`. -/
def modelFst {V : Type} [NormedAddCommGroup V] (x : Sph (WithLp 2 (V × ℝ))) : Ball V :=
  ⟨WithLp.fst (x : WithLp 2 (V × ℝ)), by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖(x : WithLp 2 (V × ℝ))‖ = 1 := by
      have h := Metric.mem_sphere.mp x.2
      rwa [dist_eq_norm, sub_zero] at h
    calc ‖WithLp.fst (x : WithLp 2 (V × ℝ))‖ ≤ ‖(x : WithLp 2 (V × ℝ))‖ :=
          WithLp.norm_fst_le V (x : WithLp 2 (V × ℝ))
      _ = 1 := h1⟩

@[simp] lemma modelFst_coe {V : Type} [NormedAddCommGroup V]
    (x : Sph (WithLp 2 (V × ℝ))) : ((modelFst x : Ball V) : V)
      = WithLp.fst (x : WithLp 2 (V × ℝ)) := rfl

lemma continuous_modelFst {V : Type} [NormedAddCommGroup V] :
    Continuous (modelFst (V := V)) := by
  refine Continuous.subtype_mk ?_ _
  exact (WithLp.continuous_fst (p := 2) (α := V) (β := ℝ)).comp continuous_subtype_val

/-- The lower chart `y ↦ (y, -√(1 - ‖y‖²))`, as a point of `Tgt m`. -/
def hopfChart (m : ℕ) : C(Ball (Eu m), Tgt m) where
  toFun v := ⟨euclTgtIso m (hemiDownF v), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, (euclTgtIso m).norm_map, norm_hemiDownF]⟩
  continuous_toFun := Continuous.subtype_mk
    ((euclTgtIso m).continuous.comp (continuous_hemiDownF (V := Eu m))) _

/-- The model sphere point associated to a point of `Tgt m`. -/
def tgtSph (m : ℕ) (t : Tgt m) : Sph (WithLp 2 (Eu m × ℝ)) :=
  ⟨(euclTgtIso m).symm (t : EuclideanSpace ℝ (Fin (2 * m + 1))), by
    have ht : ‖(t : EuclideanSpace ℝ (Fin (2 * m + 1)))‖ = 1 := by
      have h := Metric.mem_sphere.mp t.2
      rwa [dist_eq_norm, sub_zero] at h
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, (euclTgtIso m).symm.norm_map, ht]⟩

@[simp] lemma tgtSph_coe (m : ℕ) (t : Tgt m) :
    ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))
      = (euclTgtIso m).symm (t : EuclideanSpace ℝ (Fin (2 * m + 1))) := rfl

lemma ptSnd_norm (m : ℕ) (e : Sph (Eu m)) (y : Ball (Eu m)) :
    ‖((ptSnd m e y : Ball (Eu m × Eu m)) : Eu m × Eu m)‖ = 1 := by
  have h1 : ‖(e : Eu m)‖ = 1 := by
    have h := Metric.mem_sphere.mp e.2
    rwa [dist_eq_norm, sub_zero] at h
  have hy : ‖(y : Eu m)‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp y.2
    rwa [dist_eq_norm, sub_zero] at h
  show ‖((e : Eu m), (y : Eu m))‖ = 1
  rw [Prod.norm_def, max_eq_left (by rw [h1]; exact hy), h1]

/-- The point `(e, y)` of the sphere `Sph (Eu m × Eu m)`. -/
def ptSndSph (m : ℕ) (e : Sph (Eu m)) (y : Ball (Eu m)) : Sph (Eu m × Eu m) :=
  ⟨(ptSnd m e y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr (ptSnd_norm m e y)⟩

@[simp] lemma ptSndSph_coe (m : ℕ) (e : Sph (Eu m)) (y : Ball (Eu m)) :
    ((ptSndSph m e y : Sph (Eu m × Eu m)) : Eu m × Eu m) = ((e : Eu m), (y : Eu m)) := rfl

lemma tgtSph_inj {m : ℕ} {t t' : Tgt m}
    (h : ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))
      = ((tgtSph m t' : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))) : t = t' := by
  refine Subtype.ext ?_
  have h1 : (euclTgtIso m).symm (t : EuclideanSpace ℝ (Fin (2 * m + 1)))
      = (euclTgtIso m).symm (t' : EuclideanSpace ℝ (Fin (2 * m + 1))) := by
    rw [tgtSph_coe, tgtSph_coe] at h
    exact h
  have h2 := congrArg (euclTgtIso m) h1
  rwa [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply] at h2

@[simp] lemma tgtSph_snd (m : ℕ) (t : Tgt m) :
    ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ)).snd = tgtHeight m t := rfl

lemma norm_tgtSph (m : ℕ) (t : Tgt m) :
    ‖((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))‖ = 1 := by
  have h := Metric.mem_sphere.mp (tgtSph m t).2
  rwa [dist_eq_norm, sub_zero] at h

/-- The first coordinate `(v, s) ↦ v` of the target sphere, as a point of `Ball (Eu m)`. -/
def lowerPt (m : ℕ) : C(Tgt m, Ball (Eu m)) where
  toFun t := modelFst (tgtSph m t)
  continuous_toFun := (continuous_modelFst (V := Eu m)).comp (Continuous.subtype_mk
    ((euclTgtIso m).symm.continuous.comp continuous_subtype_val) _)

@[simp] lemma lowerPt_coe (m : ℕ) (t : Tgt m) :
    ((lowerPt m t : Ball (Eu m)) : Eu m)
      = WithLp.fst ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ)) := rfl

/-- `tgtHeight` of the chart. -/
lemma tgtHeight_hopfChart (m : ℕ) (v : Ball (Eu m)) :
    tgtHeight m (hopfChart m v) = -Real.sqrt (1 - ‖(v : Eu m)‖ ^ 2) := by
  have h : (euclTgtIso m).symm ((hopfChart m v : Tgt m) : EuclideanSpace ℝ (Fin (2 * m + 1)))
      = hemiDownF v := by
    show (euclTgtIso m).symm (euclTgtIso m (hemiDownF v)) = hemiDownF v
    exact LinearIsometryEquiv.symm_apply_apply _ _
  unfold tgtHeight
  rw [h]
  exact hemiDownF_snd v

lemma lowerPt_hopfChart (m : ℕ) (v : Ball (Eu m)) : lowerPt m (hopfChart m v) = v := by
  have h : (tgtSph m (hopfChart m v) : WithLp 2 (Eu m × ℝ)) = hemiDownF v := by
    show (euclTgtIso m).symm (euclTgtIso m (hemiDownF v)) = hemiDownF v
    exact LinearIsometryEquiv.symm_apply_apply _ _
  refine Subtype.ext ?_
  rw [lowerPt_coe, h, hemiDownF_fst]

lemma fst_sq_add_snd_sq (m : ℕ) (t : Tgt m) :
    ‖((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ)).fst‖ ^ 2
      + (tgtHeight m t) ^ 2 = 1 := by
  have h' := WithLp.prod_norm_sq_eq_of_L2
    ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))
  rw [norm_tgtSph, one_pow, tgtSph_snd] at h'
  rw [Real.norm_eq_abs, sq_abs] at h'
  exact h'.symm

/-- On the closed lower hemisphere the chart is a section of `lowerPt`. -/
lemma hopfChart_lowerPt (m : ℕ) (t : Tgt m) (ht : tgtHeight m t ≤ 0) :
    hopfChart m (lowerPt m t) = t := by
  have h2 := fst_sq_add_snd_sq m t
  have hval : -Real.sqrt (1 - ‖((lowerPt m t : Ball (Eu m)) : Eu m)‖ ^ 2) = tgtHeight m t := by
    rw [lowerPt_coe]
    have h1 : (1 : ℝ) - ‖((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ)).fst‖ ^ 2
        = (tgtHeight m t) ^ 2 := by linarith [h2]
    rw [h1, Real.sqrt_sq_eq_abs, abs_of_nonpos ht, neg_neg]
  have key : hemiDownF (lowerPt m t) = (tgtSph m t : WithLp 2 (Eu m × ℝ)) := by
    apply WithLp.ofLp_injective
    rw [show WithLp.ofLp (hemiDownF (lowerPt m t))
        = (((lowerPt m t : Ball (Eu m)) : Eu m),
            -Real.sqrt (1 - ‖((lowerPt m t : Ball (Eu m)) : Eu m)‖ ^ 2)) from rfl]
    rw [hval, lowerPt_coe]
    rfl
  refine Subtype.ext ?_
  show euclTgtIso m (hemiDownF (lowerPt m t)) = (t : EuclideanSpace ℝ (Fin (2 * m + 1)))
  rw [key]
  rw [tgtSph_coe]
  exact LinearIsometryEquiv.apply_symm_apply _ _

/-- On the equator the projection lands on the boundary sphere. -/
lemma lowerPt_mem_bdry (m : ℕ) (t : Tgt m) (ht : tgtHeight m t = 0) :
    lowerPt m t ∈ bdry (Eu m) := by
  show ‖((lowerPt m t : Ball (Eu m)) : Eu m)‖ = 1
  rw [lowerPt_coe]
  have h2 := fst_sq_add_snd_sq m t
  have h : ‖((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ)).fst‖ ^ 2 = 1 := by
    rw [ht] at h2; simpa using h2
  nlinarith [norm_nonneg ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ)).fst, h]


/-! ## The hom `Ψ : Kpair (Eu m) → C(Tgt m)` -/

lemma sphToBall_mem_bdry {V : Type} [NormedAddCommGroup V] (x : Sph V) :
    sphToBall x ∈ bdry V := by
  show ‖((sphToBall x : Ball V) : V)‖ = 1
  rw [sphToBall_coe]
  simpa [dist_eq_norm] using Metric.mem_sphere.mp x.2

/-- The underlying function of `hopfPsi u`. -/
def hopfPsiFun (m : ℕ) (hS : HSpace (Sph (Eu m))) (u : Kpair (Eu m)) (t : Tgt m) : ℂ :=
  (u : C(Ball (Eu m), ℂ))
    (if tgtHeight m t ≤ 0 then lowerPt m t else sphToBall hS.e)

lemma continuous_hopfPsiFun (m : ℕ) (hS : HSpace (Sph (Eu m))) (u : Kpair (Eu m)) :
    Continuous (hopfPsiFun m hS u) := by
  have hs1 : IsClosed {t : Tgt m | tgtHeight m t ≤ 0} :=
    isClosed_le (hk_continuous_tgtHeight m) continuous_const
  have hs2 : IsClosed {t : Tgt m | 0 ≤ tgtHeight m t} :=
    isClosed_le continuous_const (hk_continuous_tgtHeight m)
  have hcov : {t : Tgt m | tgtHeight m t ≤ 0} ∪ {t : Tgt m | 0 ≤ tgtHeight m t} = Set.univ := by
    ext t
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total (tgtHeight m t) 0
  rw [← continuousOn_univ, ← hcov]
  refine ContinuousOn.union_of_isClosed ?_ ?_ hs1 hs2
  · refine ContinuousOn.congr
      ((u : C(Ball (Eu m), ℂ)).continuous.comp (lowerPt m).continuous).continuousOn ?_
    intro t ht
    show hopfPsiFun m hS u t = (u : C(Ball (Eu m), ℂ)) ((lowerPt m) t)
    simp only [hopfPsiFun, if_pos (show tgtHeight m t ≤ 0 from ht)]
  · refine ContinuousOn.congr
      (continuousOn_const (c := (u : C(Ball (Eu m), ℂ)) (sphToBall hS.e))) ?_
    intro t ht
    by_cases h : tgtHeight m t ≤ 0
    · simp only [hopfPsiFun, if_pos h]
      exact (u : Kpair (Eu m)).2 (lowerPt m t)
        (lowerPt_mem_bdry m t (le_antisymm h ht)) (sphToBall hS.e) (sphToBall_mem_bdry hS.e)
    · simp only [hopfPsiFun, if_neg h]

/-- Restrict a boundary-trivialised function on the disc to the closed lower hemisphere (via the
chart) and extend by the constant value `u (sphToBall hS.e)` on the closed upper hemisphere. -/
def hopfPsi (m : ℕ) (hS : HSpace (Sph (Eu m))) : Kpair (Eu m) →ₐ[ℂ] C(Tgt m, ℂ) where
  toFun u := ⟨hopfPsiFun m hS u, continuous_hopfPsiFun m hS u⟩
  map_one' := by ext t; simp [hopfPsiFun]
  map_mul' := by intro u v; ext t; simp [hopfPsiFun]
  map_zero' := by ext t; simp [hopfPsiFun]
  map_add' := by intro u v; ext t; simp [hopfPsiFun]
  commutes' := by intro c; ext t; simp [hopfPsiFun]

@[simp] lemma hopfPsi_apply (m : ℕ) (hS : HSpace (Sph (Eu m))) (u : Kpair (Eu m)) (t : Tgt m) :
    hopfPsi m hS u t = hopfPsiFun m hS u t := rfl

lemma hopfPsi_injective (m : ℕ) (hS : HSpace (Sph (Eu m))) :
    Function.Injective (hopfPsi m hS) := by
  intro u v h
  refine Subtype.ext ?_
  ext y
  have h0 : tgtHeight m (hopfChart m y) ≤ 0 := by
    rw [tgtHeight_hopfChart]
    exact neg_nonpos.mpr (Real.sqrt_nonneg _)
  have h1 := congrArg (fun w : C(Tgt m, ℂ) => w (hopfChart m y)) h
  simp only [hopfPsi_apply, hopfPsiFun, if_pos h0, lowerPt_hopfChart] at h1
  exact h1

/-! ## Auxiliary: `diagMat` under a ring homomorphism -/

lemma diagMat_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (r n : ℕ) :
    (diagMat R r n).map φ = diagMat S r n := by
  unfold diagMat Mat.map
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext i j
  simp only [Matrix.map_apply, Matrix.diagonal_apply]
  by_cases h : i = j <;> simp [h]

/-! ## `hclsP` in the form needed -/

lemma cls_coneToT_sub (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (n r : ℕ)
    (P : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m μ))) (hP : P * P = P) :
    K0.mapA (coneToT (hopfKMap m μ))
        (cls (⟨n, P⟩ : Mat (coneAlg (hopfKMap m μ))) - cls (diagMat (coneAlg (hopfKMap m μ)) r n))
      = cls (⟨n, P.map (coneToT (hopfKMap m μ))⟩ : Mat C(Tgt m, ℂ))
        - cls (diagMat C(Tgt m, ℂ) r n) := by
  rw [map_sub]
  congr 1
  · rw [K0.mapA, K0map.map_cls, mapCls, if_pos (show Mat.IsIdem ⟨n, P⟩ from hP)]
    rfl
  · rw [K0.mapA, K0map.map_cls, mapCls, if_pos (diagMat_isIdem _ r n)]
    congr 1
    exact diagMat_map _ r n

/-! ## Auxiliary definitions for the homotopy -/

/-- The normalised point of `Eu m` (junk value `hS.e` at `0`). -/
def sphereArg (m : ℕ) (hS : HSpace (Sph (Eu m))) (v : Eu m) : Sph (Eu m) :=
  if h : v = 0 then hS.e else normPt m ⟨v, h⟩

/-- `s ↦ ‖v‖ • H s v̂`, where `H` is the homotopy `μ (e, ·) ≃ id` of the `H`-space structure. -/
def scalePt (m : ℕ) (hS : HSpace (Sph (Eu m))) (s : unitInterval) (v : Eu m) : Eu m :=
  ‖v‖ • ((hS.eHmul (s, sphereArg m hS v)) : Eu m)

lemma norm_scalePt (m : ℕ) (hS : HSpace (Sph (Eu m))) (s : unitInterval) (v : Eu m) :
    ‖scalePt m hS s v‖ = ‖v‖ := by
  rw [scalePt, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
  have h := Metric.mem_sphere.mp (hS.eHmul (s, sphereArg m hS v)).2
  rw [dist_eq_norm, sub_zero] at h
  rw [h, mul_one]

lemma continuousOn_scalePt (m : ℕ) (hS : HSpace (Sph (Eu m))) :
    ContinuousOn (fun p : unitInterval × Eu m => scalePt m hS p.1 p.2) {p | p.2 ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : {p : unitInterval × Eu m | p.2 ≠ 0}.domRestrict
        (fun p => scalePt m hS p.1 p.2)
      = fun p : {p : unitInterval × Eu m // p.2 ≠ 0} =>
          ‖(p.1.2 : Eu m)‖ • ((hS.eHmul (p.1.1, normPt m ⟨p.1.2, p.2⟩)) : Eu m) := by
    funext p
    show scalePt m hS p.1.1 p.1.2 = _
    rw [scalePt, sphereArg, dif_neg p.2]
  rw [hfun]
  refine Continuous.smul (f := fun p : {p : unitInterval × Eu m // p.2 ≠ 0} => ‖(p.1.2 : Eu m)‖)
    (g := fun p : {p : unitInterval × Eu m // p.2 ≠ 0} =>
      ((hS.eHmul (p.1.1, normPt m ⟨p.1.2, p.2⟩)) : Eu m)) ?_ ?_
  · exact continuous_norm.comp continuous_subtype_val.snd
  · exact continuous_subtype_val.comp
      ((hS.eHmul.toContinuousMap.continuous).comp
        ((continuous_subtype_val.fst).prodMk
          ((continuous_normPt m).comp (Continuous.subtype_mk continuous_subtype_val.snd _))))

lemma continuous_scalePt (m : ℕ) (hS : HSpace (Sph (Eu m))) :
    Continuous fun p : unitInterval × Eu m => scalePt m hS p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, v⟩
  by_cases hv : v = 0
  · subst hv
    refine continuousAt_smul_of_norm_le_one (x := (s, (0 : Eu m)))
      (f := fun p : unitInterval × Eu m => ‖p.2‖) (by fun_prop)
      (g := fun p : unitInterval × Eu m =>
        ((hS.eHmul (p.1, sphereArg m hS p.2)) : Eu m)) (fun p => ?_) (by simp)
    have h := Metric.mem_sphere.mp (hS.eHmul (p.1, sphereArg m hS p.2)).2
    rw [dist_eq_norm, sub_zero] at h
    exact le_of_eq h
  · exact (continuousOn_scalePt m hS).continuousAt
      ((isOpen_ne.preimage continuous_snd).mem_nhds hv)

lemma scalePt_one (m : ℕ) (hS : HSpace (Sph (Eu m))) (v : Eu m) :
    scalePt m hS 1 v = v := by
  have h1 : ((hS.eHmul (1, sphereArg m hS v) : Sph (Eu m)) : Eu m)
      = ((sphereArg m hS v : Sph (Eu m)) : Eu m) :=
    congrArg Subtype.val (hS.eHmul.map_one_left (sphereArg m hS v))
  rw [scalePt, h1]
  by_cases hv : v = 0
  · simp [hv, sphereArg]
  · rw [sphereArg, dif_neg hv]
    show ‖v‖ • ((normPt m ⟨v, hv⟩ : Sph (Eu m)) : Eu m) = v
    rw [show ((normPt m ⟨v, hv⟩ : Sph (Eu m)) : Eu m) = unitV v from rfl, unitV, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

lemma scalePt_zero (m : ℕ) (hS : HSpace (Sph (Eu m))) (y : Ball (Eu m)) :
    scalePt m hS 0 (y : Eu m) = hopfFst m hS.hmul ((hS.e : Eu m), (y : Eu m)) := by
  have he1 : ‖(hS.e : Eu m)‖ = 1 := by
    have h := Metric.mem_sphere.mp hS.e.2
    rwa [dist_eq_norm, sub_zero] at h
  have hene : (hS.e : Eu m) ≠ 0 := by
    intro h; rw [h, norm_zero] at he1; exact one_ne_zero he1.symm
  have hyl : ‖(y : Eu m)‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp y.2
    rwa [dist_eq_norm, sub_zero] at h
  have hmin : min ‖(hS.e : Eu m)‖ ‖(y : Eu m)‖ = ‖(y : Eu m)‖ := by
    rw [he1]; exact min_eq_right hyl
  have h0 : scalePt m hS 0 (y : Eu m)
      = ‖(y : Eu m)‖ • ((hS.hmul (hS.e, sphereArg m hS (y : Eu m)) : Sph (Eu m)) : Eu m) := by
    rw [scalePt]; exact congrArg _ (congrArg Subtype.val (hS.eHmul.map_zero_left _))
  rw [h0, hopfFst, hmin]
  by_cases hv : (y : Eu m) = 0
  · rw [hv]; simp
  · congr 1
    rw [sphereArg, dif_neg hv, muNorm, dif_neg (by push Not; exact ⟨hene, hv⟩)]
    have hnp : (normPt m ⟨(hS.e : Eu m), hene⟩ : Sph (Eu m)) = hS.e :=
      Subtype.ext (by
        show unitV (hS.e : Eu m) = (hS.e : Eu m)
        rw [unitV, he1, inv_one, one_smul])
    rw [hnp]

/-! ## The model point `mkTgt` -/

/-- The point of `Tgt m` with model coordinates `(v, s)`. -/
def mkTgt (m : ℕ) (v : Eu m) (s : ℝ) (h : ‖v‖ ^ 2 + s ^ 2 = 1) : Tgt m :=
  ⟨euclTgtIso m (WithLp.toLp 2 (v, s)), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, (euclTgtIso m).norm_map]
    have h2 : ‖WithLp.toLp 2 (v, s)‖ ^ 2 = 1 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd]
      rw [Real.norm_eq_abs, sq_abs]
      exact h
    nlinarith [norm_nonneg (WithLp.toLp 2 (v, s) : WithLp 2 (Eu m × ℝ))]⟩

lemma tgtSph_mkTgt (m : ℕ) (v : Eu m) (s : ℝ) (h : ‖v‖ ^ 2 + s ^ 2 = 1) :
    ((tgtSph m (mkTgt m v s h) : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))
      = WithLp.toLp 2 (v, s) := by
  show (euclTgtIso m).symm (euclTgtIso m (WithLp.toLp 2 (v, s))) = WithLp.toLp 2 (v, s)
  exact LinearIsometryEquiv.symm_apply_apply _ _

@[simp] lemma tgtHeight_mkTgt (m : ℕ) (v : Eu m) (s : ℝ) (h : ‖v‖ ^ 2 + s ^ 2 = 1) :
    tgtHeight m (mkTgt m v s h) = s := by
  unfold tgtHeight mkTgt
  rw [LinearIsometryEquiv.symm_apply_apply]

@[simp] lemma lowerPt_mkTgt (m : ℕ) (v : Eu m) (s : ℝ) (h : ‖v‖ ^ 2 + s ^ 2 = 1) :
    (lowerPt m (mkTgt m v s h : Tgt m) : Eu m) = v := by
  show ((tgtSph m (mkTgt m v s h) : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ)).fst = v
  rw [tgtSph_mkTgt]
  rfl

lemma mkTgt_lowerPt (m : ℕ) (t : Tgt m) :
    mkTgt m (lowerPt m t : Eu m) (tgtHeight m t) (fst_sq_add_snd_sq m t) = t := by
  refine Subtype.ext ?_
  show euclTgtIso m (WithLp.toLp 2 ((lowerPt m t : Eu m), tgtHeight m t)) = _
  rw [show WithLp.toLp 2 ((lowerPt m t : Eu m), tgtHeight m t)
      = ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ)) from ?_]
  · rw [tgtSph_coe]
    exact LinearIsometryEquiv.apply_symm_apply _ _
  · apply WithLp.ofLp_injective
    show WithLp.ofLp (WithLp.toLp 2 ((lowerPt m t : Eu m), tgtHeight m t))
      = WithLp.ofLp ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))
    rw [WithLp.ofLp_toLp]
    refine Prod.ext ?_ ?_
    · show ((lowerPt m t : Ball (Eu m)) : Eu m)
        = ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ)).fst
      exact lowerPt_coe m t
    · show tgtHeight m t
        = ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ)).snd
      exact tgtSph_snd m t

/-- The point obtained by applying the `H`-homotopy in the first coordinate of the model. -/
def homPt (m : ℕ) (hS : HSpace (Sph (Eu m))) (s : unitInterval) (t : Tgt m) : Tgt m :=
  mkTgt m (scalePt m hS s (lowerPt m t : Eu m)) (tgtHeight m t) (by
    rw [norm_scalePt]; exact fst_sq_add_snd_sq m t)

lemma tgtSph_homPt (m : ℕ) (hS : HSpace (Sph (Eu m))) (s : unitInterval) (t : Tgt m) :
    ((tgtSph m (homPt m hS s t) : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))
      = WithLp.toLp 2 (scalePt m hS s (lowerPt m t : Eu m), tgtHeight m t) :=
  tgtSph_mkTgt m _ _ _

lemma tgtHeight_homPt (m : ℕ) (hS : HSpace (Sph (Eu m))) (s : unitInterval) (t : Tgt m) :
    tgtHeight m (homPt m hS s t) = tgtHeight m t := tgtHeight_mkTgt m _ _ _

@[simp] lemma homPt_one (m : ℕ) (hS : HSpace (Sph (Eu m))) (t : Tgt m) :
    homPt m hS 1 t = t := by
  apply tgtSph_inj
  rw [tgtSph_homPt, scalePt_one]
  show WithLp.toLp 2 ((lowerPt m t : Eu m), tgtHeight m t)
    = ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))
  rw [← WithLp.toLp_ofLp 2 ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))]
  rfl

lemma continuous_homPt (m : ℕ) (hS : HSpace (Sph (Eu m))) :
    Continuous fun p : unitInterval × Tgt m => homPt m hS p.1 p.2 := by
  have h1 : Continuous fun p : unitInterval × Tgt m =>
      WithLp.toLp 2 (scalePt m hS p.1 (lowerPt m p.2 : Eu m), tgtHeight m p.2) :=
    (WithLp.prod_continuous_toLp 2 (Eu m) ℝ).comp
      (((continuous_scalePt m hS).comp (continuous_fst.prodMk
        (continuous_subtype_val.comp
          ((lowerPt m).continuous.comp continuous_snd)))).prodMk
        ((hk_continuous_tgtHeight m).comp continuous_snd))
  refine Continuous.subtype_mk ?_ _
  refine ((euclTgtIso m).continuous.comp h1).congr ?_
  intro p
  rfl

/-- The model coordinates of `hopfKMap m μ (ptSnd m e y)`. -/
lemma tgtSph_hopfKMap_ptSnd (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (e : Sph (Eu m)) (y : Ball (Eu m)) :
    ((tgtSph m (hopfKMap m μ (ptSndSph m e y)) : Sph (WithLp 2 (Eu m × ℝ)))
        : WithLp 2 (Eu m × ℝ))
      = WithLp.toLp 2 (hopfFst m μ ((e : Eu m), (y : Eu m)),
          hopfSnd m ((e : Eu m), (y : Eu m))) := by
  have h1 : (euclTgtIso m).symm ((hopfKMap m μ (ptSndSph m e y) : Tgt m)
      : EuclideanSpace ℝ (Fin (2 * m + 1)))
      = hopfRaw m μ ((e : Eu m), (y : Eu m)) :=
    LinearIsometryEquiv.symm_apply_apply _ _
  rw [tgtSph_coe, h1]
  rfl

/-- `homPt 0` applied to the chart is the Hopf construction at `(e, y)`. -/
lemma tgtSph_homPt_zero_hopfChart (m : ℕ) (hS : HSpace (Sph (Eu m))) (y : Ball (Eu m)) :
    ((tgtSph m (homPt m hS 0 (hopfChart m y)) : Sph (WithLp 2 (Eu m × ℝ)))
        : WithLp 2 (Eu m × ℝ))
      = ((tgtSph m (hopfKMap m hS.hmul (ptSndSph m hS.e y)) : Sph (WithLp 2 (Eu m × ℝ)))
        : WithLp 2 (Eu m × ℝ)) := by
  have hyl : ‖(y : Eu m)‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp y.2
    rwa [dist_eq_norm, sub_zero] at h
  have he1 : ‖(hS.e : Eu m)‖ = 1 := by
    have h := Metric.mem_sphere.mp hS.e.2
    rwa [dist_eq_norm, sub_zero] at h
  have hsnd : hopfSnd m ((hS.e : Eu m), (y : Eu m)) = -Real.sqrt (1 - ‖(y : Eu m)‖ ^ 2) := by
    rw [hopfSnd_of_ge m (z := ((hS.e : Eu m), (y : Eu m))) (by rw [he1]; exact hyl), he1,
      one_pow]
  rw [tgtSph_homPt, tgtSph_hopfKMap_ptSnd]
  refine WithLp.toLp_injective 2 ?_
  rw [scalePt_zero, tgtHeight_hopfChart, lowerPt_hopfChart, hsnd]

lemma homPt_zero_hopfChart (m : ℕ) (hS : HSpace (Sph (Eu m))) (y : Ball (Eu m)) :
    homPt m hS 0 (hopfChart m y) = hopfKMap m hS.hmul (ptSndSph m hS.e y) :=
  tgtSph_inj (tgtSph_homPt_zero_hopfChart m hS y)

/-! ## The homotopy `Ψ (P i j) ≃ g i j` -/

lemma map_evalC_eq_map_evalT (m : ℕ) (hS : HSpace (Sph (Eu m))) (n : ℕ)
    (P : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m hS.hmul))) (t : Tgt m) :
    (P.map (coneToT (hopfKMap m hS.hmul))).map (evalC t)
      = P.map (evalT m (hopfKMap m hS.hmul) t) := by
  ext i j
  rfl

/-- The `H`-homotopy on matrices over `C(Tgt m, ℂ)`. -/
def hopfGHom (m : ℕ) (hS : HSpace (Sph (Eu m))) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) C(Tgt m, ℂ)) (p : unitInterval × Tgt m) :
    Matrix (Fin n) (Fin n) ℂ :=
  if tgtHeight m p.2 ≤ 0 then g.map (evalC (homPt m hS p.1 p.2))
    else g.map (evalC p.2)

lemma hopfGHom_idem (m : ℕ) (hS : HSpace (Sph (Eu m))) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) C(Tgt m, ℂ)) (hg : g * g = g) (p : unitInterval × Tgt m) :
    hopfGHom m hS g p * hopfGHom m hS g p = hopfGHom m hS g p := by
  unfold hopfGHom
  split_ifs with h
  · rw [← Matrix.map_mul, hg]
  · rw [← Matrix.map_mul, hg]

lemma continuous_hopfGHom (m : ℕ) (hS : HSpace (Sph (Eu m))) (n r : ℕ)
    (P : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m hS.hmul)))
    (hcap : ∀ t : Tgt m, t ∈ capTplus m →
      P.map (evalT m (hopfKMap m hS.hmul) t) = diagIdemMat r n) :
    Continuous (hopfGHom m hS (P.map (coneToT (hopfKMap m hS.hmul)))) := by
  have hcont1 : Continuous fun p : unitInterval × Tgt m =>
      (P.map (coneToT (hopfKMap m hS.hmul))).map (evalC (homPt m hS p.1 p.2)) := by
    refine continuous_matrix fun i j => ?_
    exact ((P.map (coneToT (hopfKMap m hS.hmul))) i j).continuous.comp (continuous_homPt m hS)
  have hcont2 : Continuous fun p : unitInterval × Tgt m =>
      (P.map (coneToT (hopfKMap m hS.hmul))).map (evalC p.2) := by
    refine continuous_matrix fun i j => ?_
    exact ((P.map (coneToT (hopfKMap m hS.hmul))) i j).continuous.comp continuous_snd
  unfold hopfGHom
  refine continuous_if ?_ hcont1.continuousOn hcont2.continuousOn
  intro p hp
  have ht0 : tgtHeight m p.2 = 0 := by
    have h1 : tgtHeight m p.2 ≤ 0 := by
      have h2 : p ∈ closure {q : unitInterval × Tgt m | tgtHeight m q.2 ≤ 0} := hp.1
      have h3 : IsClosed {q : unitInterval × Tgt m | tgtHeight m q.2 ≤ 0} :=
        isClosed_le ((hk_continuous_tgtHeight m).comp continuous_snd) continuous_const
      rw [h3.closure_eq] at h2
      exact h2
    have h4 : 0 ≤ tgtHeight m p.2 := by
      have h2 : p ∈ closure {q : unitInterval × Tgt m | ¬ (tgtHeight m q.2 ≤ 0)} := by
        have hh : p ∈ closure ({x : unitInterval × Tgt m | tgtHeight m x.2 ≤ 0}ᶜ) := by
          rw [closure_compl]
          exact hp.2
        exact hh
      have h2' : p ∈ closure ((fun q : unitInterval × Tgt m => tgtHeight m q.2) ⁻¹'
          Set.Ioi (0 : ℝ)) := by
        simpa [Set.preimage, Set.mem_Ioi] using h2
      have h3 := ((hk_continuous_tgtHeight m).comp continuous_snd).closure_preimage_subset
        (Set.Ioi (0 : ℝ)) h2'
      rw [closure_Ioi' (⟨1, by norm_num⟩ : (Set.Ioi (0 : ℝ)).Nonempty)] at h3
      exact h3
    exact le_antisymm h1 h4
  rw [map_evalC_eq_map_evalT m hS n P, map_evalC_eq_map_evalT m hS n P,
    hcap _ (by simp only [capTplus, Set.mem_setOf_eq, tgtHeight_homPt, ht0]; norm_num),
    hcap _ (by simp only [capTplus, Set.mem_setOf_eq, ht0]; norm_num)]

lemma map_evalC_g_eq_diag (m : ℕ) (hS : HSpace (Sph (Eu m))) (n r : ℕ)
    (P : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m hS.hmul)))
    (hcap : ∀ t : Tgt m, t ∈ capTplus m →
      P.map (evalT m (hopfKMap m hS.hmul) t) = diagIdemMat r n)
    {t : Tgt m} (ht : t ∈ capTplus m) :
    (P.map (coneToT (hopfKMap m hS.hmul))).map (evalC t) = diagIdemMat r n := by
  rw [map_evalC_eq_map_evalT m hS n P]
  exact hcap t ht

/-- **The slice class is the class of the base component.** -/
theorem hopfPsi_cls (m : ℕ) (hS : HSpace (Sph (Eu m))) (n r : ℕ)
    (P : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m hS.hmul))) (hP : P * P = P)
    (hcap : ∀ t : Tgt m, t ∈ capTplus m →
      P.map (evalT m (hopfKMap m hS.hmul) t) = diagIdemMat r n)
    (u : Matrix (Fin n) (Fin n) (Kpair (Eu m)))
    (hu : Mat.IsIdem (⟨n, u⟩ : Mat (Kpair (Eu m))))
    (huP : ∀ (i j : Fin n) (y : Ball (Eu m)),
      ((u i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) y
        = evalD m (hopfKMap m hS.hmul) (ptSnd m hS.e y) (P i j)) :
    cls (⟨n, u.map (hopfPsi m hS)⟩ : Mat C(Tgt m, ℂ))
      = cls (⟨n, P.map (coneToT (hopfKMap m hS.hmul))⟩ : Mat C(Tgt m, ℂ)) := by
  classical
  set g : Matrix (Fin n) (Fin n) C(Tgt m, ℂ) := P.map (coneToT (hopfKMap m hS.hmul)) with hg
  have hgg : g * g = g := by
    rw [hg, ← Matrix.map_mul, hP]
  -- (a) pointwise value of `u`
  have hu_eq : ∀ (i j : Fin n) (y : Ball (Eu m)),
      ((u i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) y
        = g i j (hopfKMap m hS.hmul (ptSndSph m hS.e y)) := by
    intro i j y
    rw [huP i j y]
    show (P i j).1.2 (ptSnd m hS.e y)
      = (coneToT (hopfKMap m hS.hmul) (P i j)) (hopfKMap m hS.hmul (ptSndSph m hS.e y))
    exact (P i j).2 (ptSnd m hS.e y) (ptSnd_norm m hS.e y)
  -- (b) values on the boundary
  have hu_bdry : ∀ (i j : Fin n) (y : Ball (Eu m)), y ∈ bdry (Eu m) →
      ((u i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) y = diagIdemMat r n i j := by
    intro i j y hy
    rw [hu_eq i j y]
    have ht : hopfKMap m hS.hmul (ptSndSph m hS.e y) ∈ capTplus m := by
      rw [capTplus, Set.mem_setOf_eq]
      have h2 : tgtHeight m (hopfKMap m hS.hmul (ptSndSph m hS.e y))
          = hopfSnd m ((hS.e : Eu m), (y : Eu m)) := by
        rw [tgtHeight_hopfKMap]
        rfl
      have he1 : ‖(hS.e : Eu m)‖ = 1 := by
        have h := Metric.mem_sphere.mp hS.e.2
        rwa [dist_eq_norm, sub_zero] at h
      have hy1 : ‖(y : Eu m)‖ = 1 := hy
      have hsnd0 : hopfSnd m ((hS.e : Eu m), (y : Eu m)) = 0 := by
        rw [hopfSnd_of_le m (by rw [he1, hy1])]
        simp only [Prod.fst, Prod.snd, hy1, he1, one_pow, sub_self, Real.sqrt_zero]
      rw [h2, hsnd0]
      norm_num
    have hmat := map_evalC_g_eq_diag m hS n r P hcap ht
    rw [← hg] at hmat
    have := congrFun (congrFun hmat i) j
    rw [Matrix.map_apply] at this
    exact this
  -- (c) the pointwise homotopy endpoints
  have hG0 : ∀ (i j : Fin n) (t : Tgt m),
      hopfGHom m hS g (0, t) i j = hopfPsi m hS (u i j) t := by
    intro i j t
    by_cases ht : tgtHeight m t ≤ 0
    · rw [show hopfGHom m hS g (0, t) = g.map (evalC (homPt m hS 0 t)) from by
        unfold hopfGHom; rw [if_pos ht]]
      rw [Matrix.map_apply, hopfPsi_apply, hopfPsiFun, if_pos ht]
      rw [show homPt m hS 0 t
          = hopfKMap m hS.hmul (ptSndSph m hS.e (lowerPt m t)) from ?_]
      · show (g i j) (hopfKMap m hS.hmul (ptSndSph m hS.e (lowerPt m t)))
          = ((u i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) (lowerPt m t)
        rw [← hu_eq i j (lowerPt m t)]
      · have h1 := homPt_zero_hopfChart m hS (lowerPt m t)
        rwa [hopfChart_lowerPt m t ht] at h1
    · push Not at ht
      rw [show hopfGHom m hS g (0, t) = g.map (evalC t) from by
        unfold hopfGHom; rw [if_neg (not_le.mpr ht)]]
      rw [Matrix.map_apply, hopfPsi_apply, hopfPsiFun, if_neg (not_le.mpr ht)]
      rw [hu_bdry i j (sphToBall hS.e) (sphToBall_mem_bdry hS.e)]
      rw [hg]
      have hmat := map_evalC_g_eq_diag m hS n r P hcap
        (show t ∈ capTplus m by
          rw [capTplus, Set.mem_setOf_eq]; linarith)
      have := congrFun (congrFun hmat i) j
      rw [Matrix.map_apply] at this
      exact this
  have hG1 : ∀ (i j : Fin n) (t : Tgt m), hopfGHom m hS g (1, t) i j = g i j t := by
    intro i j t
    by_cases ht : tgtHeight m t ≤ 0
    · rw [show hopfGHom m hS g (1, t) = g.map (evalC (homPt m hS 1 t)) from by
        unfold hopfGHom; rw [if_pos ht]]
      rw [Matrix.map_apply, homPt_one]
      rfl
    · push Not at ht
      rw [show hopfGHom m hS g (1, t) = g.map (evalC t) from by
        unfold hopfGHom; rw [if_neg (not_le.mpr ht)]]
      rw [Matrix.map_apply]
      rfl
  -- (d) the homotopy of matrices over `C(Tgt m, ℂ)`
  let Gc : unitInterval → Matrix (Fin n) (Fin n) C(Tgt m, ℂ) := fun s i j =>
    ⟨fun t => hopfGHom m hS g (s, t) i j,
      ((continuous_hopfGHom m hS n r P hcap).matrix_elem i j).comp
        (continuous_const.prodMk continuous_id)⟩
  have hGc_cont : Continuous Gc := by
    apply continuous_matrix
    intro i j
    exact (ContinuousMap.curry ⟨fun st : unitInterval × Tgt m => hopfGHom m hS g st i j,
      (continuous_hopfGHom m hS n r P hcap).matrix_elem i j⟩).continuous
  have hGcmap : ∀ (s : unitInterval) (t : Tgt m),
      (Gc s).map (evalC t) = hopfGHom m hS g (s, t) := by
    intro s t
    ext i j
    rfl
  have hGc_idem : ∀ s : unitInterval, Gc s * Gc s = Gc s := by
    intro s
    apply Matrix.ext
    intro i j
    apply ContinuousMap.ext
    intro t
    have h2 : (Gc s * Gc s).map (evalC t) = (Gc s).map (evalC t) := by
      rw [Matrix.map_mul, hGcmap s t, hopfGHom_idem m hS g hgg (s, t)]
    exact congrFun (congrFun h2 i) j
  have hcls := Work.KT.Fund.cls_eq_of_path (C(Tgt m, ℂ)) Gc hGc_cont hGc_idem
  have hGc0 : Gc 0 = u.map (hopfPsi m hS) := by
    ext i j t
    exact hG0 i j t
  have hGc1 : Gc 1 = g := by
    ext i j t
    exact hG1 i j t
  rw [hGc0, hGc1, hg] at hcls
  exact hcls

/-! ## `K₀` along algebra isomorphisms -/

section TransportHK

variable {A B C : Type} [Ring A] [Ring B] [Ring C] [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]

lemma hkK0.mapA_comp (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) :
    K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) := by
  have hto : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := by ext x; rfl
  change K0.map (ψ.comp φ).toRingHom = (K0.map ψ.toRingHom).comp (K0.map φ.toRingHom)
  rw [hto]
  exact k0_basic.2.2.1 (A := A) (B := B) (C := C) φ.toRingHom ψ.toRingHom

lemma hkK0.mapA_id : K0.mapA (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) :=
  k0_basic.2.2.2.1 (A := A)

lemma hkK0.mapA_symm_apply (Φ : A ≃ₐ[ℂ] B) (x : K0 A) :
    K0.mapA (Φ.symm).toAlgHom (K0.mapA Φ.toAlgHom x) = x := by
  have h2 : (K0.mapA (Φ.symm).toAlgHom).comp (K0.mapA Φ.toAlgHom) =
      AddMonoidHom.id (K0 A) := by
    rw [← hkK0.mapA_comp Φ.toAlgHom (Φ.symm).toAlgHom, AlgEquiv.symm_comp (e := Φ)]
    exact hkK0.mapA_id
  exact congrFun (congrArg DFunLike.coe h2) x

lemma hkK0.mapA_apply_symm (Φ : A ≃ₐ[ℂ] B) (x : K0 B) :
    K0.mapA Φ.toAlgHom (K0.mapA (Φ.symm).toAlgHom x) = x := by
  have h2 : (K0.mapA Φ.toAlgHom).comp (K0.mapA (Φ.symm).toAlgHom) =
      AddMonoidHom.id (K0 B) := by
    rw [← hkK0.mapA_comp (Φ.symm).toAlgHom Φ.toAlgHom, AlgEquiv.comp_symm (e := Φ)]
    exact hkK0.mapA_id
  exact congrFun (congrArg DFunLike.coe h2) x

end TransportHK

/-! ## The algebra isomorphism `C(Tgt m, ℂ) ≃ Kpair (Eu m)` -/

section RingIsoHK

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- `C(Sph V, ℂ) ≃ Kpair (ℝ^d)` when `finrank ℝ V = d + 1`, compatible with the augmentations. -/
lemma hk_exists_algEquiv_Kpair (t0 : Sph V) (d : ℕ) (hd1 : 1 ≤ d)
    (hd : Module.finrank ℝ V = d + 1) :
    ∃ Φ : C(Sph V, ℂ) ≃ₐ[ℂ] Kpair (Euc d),
      ∀ (y0 : Ball (Euc d)) (hy0 : y0 ∈ bdry (Euc d)), ∀ h : C(Sph V, ℂ),
        augPair (Euc d) y0 (Φ h) = evalC t0 h := by
  obtain ⟨e, he⟩ := sphKT_exists_sphereHomeo_modelSphere V t0 d hd
  obtain ⟨q, hq, hnp, hfib⟩ := diskQuot d hd1
  let hf : ∀ x x' : Ball (Euc d), q x = q x' →
      x = x' ∨ (x ∈ bdry (Euc d) ∧ x' ∈ bdry (Euc d)) := fun x x' h => (hfib x x').mp h
  let Ψ : C(Sph (ModelSphere d), ℂ) ≃ₐ[ℂ] Kpair (Euc d) := sphKT_diskQuotAlgEquiv d q hq hf hnp
  refine ⟨(sphKT_pullAlgEquiv e.symm).trans Ψ, ?_⟩
  intro y0 hy0 h
  rw [AlgEquiv.trans_apply]
  have hΨ : augPair (Euc d) y0 (Ψ ((sphKT_pullAlgEquiv e.symm) h))
      = evalC (sphKT_northPole d) ((sphKT_pullAlgEquiv e.symm) h) :=
    diskQuotAlgEquiv_aug d q hq hf hnp y0 hy0 _
  rw [hΨ]
  have hsymm : e.symm (sphKT_northPole d) = t0 := by rw [← he, Homeomorph.symm_apply_apply]
  change ((sphKT_pullAlgEquiv e.symm) h) (sphKT_northPole d) = h t0
  rw [pullAlgEquiv_apply_apply, hsymm]

end RingIsoHK

/-! ## The slice generator -/

theorem hk_slice_gen (m : ℕ) (hm : 1 ≤ m) (hS : HSpace (Sph (Eu m))) (n r : ℕ)
    (t0 : Tgt m)
    (α : K0 C(Tgt m, ℂ)) (hαred : K0.mapA (evalC t0) α = 0)
    (hαnz : ∀ k : ℤ, k • α = 0 → k = 0)
    (hαgen : ∀ z, K0.mapA (evalC t0) z = 0 → ∃ k : ℤ, z = k • α)
    (P : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m hS.hmul)))
    (hP : P * P = P)
    (hcap : ∀ t : Tgt m, t ∈ capTplus m →
      P.map (evalT m (hopfKMap m hS.hmul) t) = diagIdemMat r n)
    (hcol : ∀ z : Ball (Eu m × Eu m), Real.sqrt 3 / 2 ≤ ‖(z : Eu m × Eu m).2‖ →
      P.map (evalD m (hopfKMap m hS.hmul) z) = diagIdemMat r n)
    (hclsP : K0.mapA (coneToT (hopfKMap m hS.hmul))
      (cls (⟨n, P⟩ : Mat (coneAlg (hopfKMap m hS.hmul)))
        - cls (diagMat (coneAlg (hopfKMap m hS.hmul)) r n)) = α)
    (u : Matrix (Fin n) (Fin n) (Kpair (Eu m)))
    (hu : Mat.IsIdem (⟨n, u⟩ : Mat (Kpair (Eu m))))
    (huP : ∀ (i j : Fin n) (y : Ball (Eu m)),
      ((u i j : Kpair (Eu m)) : C(Ball (Eu m), ℂ)) y
        = evalD m (hopfKMap m hS.hmul) (ptSnd m hS.e y) (P i j)) :
    K0.mapA (augPair (Eu m) (sphToBall hS.e)) (cls (⟨n, u⟩ : Mat (Kpair (Eu m)))
        - cls (diagMat (Kpair (Eu m)) r n)) = 0 ∧
      (∀ k : ℤ, k • (cls (⟨n, u⟩ : Mat (Kpair (Eu m)))
          - cls (diagMat (Kpair (Eu m)) r n)) = 0 → k = 0) ∧
      (∀ z : K0 (Kpair (Eu m)), K0.mapA (augPair (Eu m) (sphToBall hS.e)) z = 0 →
        ∃ k : ℤ, z = k • (cls (⟨n, u⟩ : Mat (Kpair (Eu m)))
          - cls (diagMat (Kpair (Eu m)) r n))) := by
  classical
  set γ : K0 (Kpair (Eu m)) :=
    cls (⟨n, u⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n) with hγdef
  set yt : Ball (Eu m) := (if tgtHeight m t0 ≤ 0 then lowerPt m t0 else sphToBall hS.e) with hyt
  -- the composition `evalC t0 ∘ hopfPsi` is evaluation of the disc function at `yt`
  have hcomp : (evalC t0).comp (hopfPsi m hS) = augPair (Eu m) yt := by
    apply AlgHom.ext
    intro u'
    show hopfPsi m hS u' t0 = (u' : C(Ball (Eu m), ℂ)) yt
    rw [hopfPsi_apply]
    simp only [hopfPsiFun]
    rw [hyt]
  have key_eval : ∀ z : K0 (Kpair (Eu m)),
      K0.mapA (evalC t0) (K0.mapA (hopfPsi m hS) z) = K0.mapA (augPair (Eu m) yt) z := by
    intro z
    have h1 : ((K0.mapA (evalC t0)).comp (K0.mapA (hopfPsi m hS))) z
        = K0.mapA ((evalC t0).comp (hopfPsi m hS)) z :=
      congrFun (congrArg DFunLike.coe (hkK0.mapA_comp (hopfPsi m hS) (evalC t0))).symm z
    rw [hcomp] at h1
    exact h1
  have key_indep : ∀ z : K0 (Kpair (Eu m)),
      K0.mapA (augPair (Eu m) yt) z = K0.mapA (augPair (Eu m) (sphToBall hS.e)) z := by
    intro z
    have h := congrFun (congrArg DFunLike.coe
      (Work.KT.HopfK.augPair_K0_independent m yt (sphToBall hS.e))) z
    exact h
  -- `α` written in terms of the two matrices
  have hαeq : α = cls (⟨n, P.map (coneToT (hopfKMap m hS.hmul))⟩ : Mat C(Tgt m, ℂ))
      - cls (diagMat C(Tgt m, ℂ) r n) :=
    hclsP.symm.trans (cls_coneToT_sub m hS.hmul n r P hP)
  have hpsi_u : K0.mapA (hopfPsi m hS) (cls (⟨n, u⟩ : Mat (Kpair (Eu m))))
      = cls (⟨n, u.map (hopfPsi m hS)⟩ : Mat C(Tgt m, ℂ)) := by
    rw [sphKT_K0.map_cls (hopfPsi m hS).toRingHom hu]
    rfl
  have hpsi_diag : K0.mapA (hopfPsi m hS) (cls (diagMat (Kpair (Eu m)) r n))
      = cls (diagMat C(Tgt m, ℂ) r n) := by
    rw [sphKT_K0.map_cls (hopfPsi m hS).toRingHom (diagMat_isIdem (Kpair (Eu m)) r n),
      diagMat_map (hopfPsi m hS).toRingHom r n]
  have hpsi_gamma : K0.mapA (hopfPsi m hS) γ = α := by
    have hsub : K0.mapA (hopfPsi m hS)
        (cls (⟨n, u⟩ : Mat (Kpair (Eu m))) - cls (diagMat (Kpair (Eu m)) r n))
        = cls (⟨n, u.map (hopfPsi m hS)⟩ : Mat C(Tgt m, ℂ))
          - cls (diagMat C(Tgt m, ℂ) r n) := by
      rw [map_sub, hpsi_u, hpsi_diag]
    rw [hγdef, hsub, hopfPsi_cls m hS n r P hP hcap u hu huP, ← hαeq]
  have hkerγ : K0.mapA (augPair (Eu m) (sphToBall hS.e)) γ = 0 := by
    rw [← key_indep γ, ← key_eval γ, hpsi_gamma]
    exact hαred
  -- the algebra isomorphism exhibiting `Kpair (Eu m)` as `C(Tgt m, ℂ)`
  obtain ⟨Φ, hΦ⟩ := hk_exists_algEquiv_Kpair (EuclideanSpace ℝ (Fin (2 * m + 1))) t0 (2 * m)
    (by omega) (by simp)
  have hΦev : (augPair (Eu m) (sphToBall hS.e)).comp Φ.toAlgHom
      = (evalC t0 : C(Tgt m, ℂ) →ₐ[ℂ] ℂ) :=
    AlgHom.ext fun h => hΦ (sphToBall hS.e) (sphToBall_mem_bdry hS.e) h
  let g0 : K0 (Kpair (Eu m)) := K0.mapA Φ.toAlgHom α
  have keyΦ : ∀ w : K0 C(Tgt m, ℂ),
      K0.mapA (augPair (Eu m) (sphToBall hS.e)) (K0.mapA Φ.toAlgHom w)
        = K0.mapA (evalC t0) w := by
    intro w
    have h1 : ((K0.mapA (augPair (Eu m) (sphToBall hS.e))).comp (K0.mapA Φ.toAlgHom)) w
        = K0.mapA ((augPair (Eu m) (sphToBall hS.e)).comp Φ.toAlgHom) w :=
      congrFun (congrArg DFunLike.coe
        (hkK0.mapA_comp Φ.toAlgHom (augPair (Eu m) (sphToBall hS.e)))).symm w
    rw [hΦev] at h1
    exact h1
  have hg0_mem : K0.mapA (augPair (Eu m) (sphToBall hS.e)) g0 = 0 := by
    have h := keyΦ α
    rw [hαred] at h
    exact h
  -- every element of the kernel is a multiple of `g0`
  have hunit : ∀ z : K0 (Kpair (Eu m)),
      K0.mapA (augPair (Eu m) (sphToBall hS.e)) z = 0 → ∃ k : ℤ, z = k • g0 := by
    intro z hz
    have hz' : K0.mapA (evalC t0) (K0.mapA (Φ.symm).toAlgHom z) = 0 := by
      have h := keyΦ (K0.mapA (Φ.symm).toAlgHom z)
      rw [hkK0.mapA_apply_symm Φ z] at h
      exact h.symm.trans hz
    obtain ⟨k, hk⟩ := hαgen _ hz'
    refine ⟨k, ?_⟩
    rw [← hkK0.mapA_apply_symm Φ z, hk, map_zsmul]
  -- `g0` and `γ` differ by a sign, because `hopfPsi_* γ = α` has infinite order
  have hgenγ : ∀ z : K0 (Kpair (Eu m)),
      K0.mapA (augPair (Eu m) (sphToBall hS.e)) z = 0 → ∃ k : ℤ, z = k • γ := by
    intro z hz
    obtain ⟨ℓ, hℓ⟩ := hunit z hz
    obtain ⟨ℓ', hℓ'⟩ := hunit γ hkerγ
    have hmem : K0.mapA (evalC t0) (K0.mapA (hopfPsi m hS) g0) = 0 := by
      have h1 : K0.mapA (evalC t0) (K0.mapA (hopfPsi m hS) g0)
          = K0.mapA (augPair (Eu m) yt) g0 := key_eval g0
      rw [h1, key_indep g0]
      exact hg0_mem
    obtain ⟨mm, hmm⟩ := hαgen _ hmem
    have hαeq2 : (ℓ' * mm) • α = α := by
      rw [← smul_smul, ← hmm, ← map_zsmul, ← hℓ', ← hpsi_gamma]
    have hprod : (ℓ' * mm - 1) • α = 0 := by
      rw [sub_smul, hαeq2, one_smul, sub_self]
    have h1 : ℓ' * mm - 1 = 0 := hαnz _ hprod
    have h2 : ℓ' * mm = 1 := sub_eq_zero.mp h1
    have h3 : ℓ' = 1 ∨ ℓ' = -1 := Int.eq_one_or_neg_one_of_mul_eq_one h2
    have hg0 : g0 = ℓ' • γ := by
      rcases h3 with h | h
      · rw [hℓ', h]; simp
      · rw [hℓ', h]; simp
    refine ⟨ℓ * ℓ', ?_⟩
    rw [hℓ, hg0, smul_smul]
  refine ⟨hkerγ, ?_, hgenγ⟩
  · intro k hk
    have h := congrArg (K0.mapA (hopfPsi m hS)) hk
    rw [map_zsmul, map_zero, hpsi_gamma] at h
    exact hαnz k h

end

end Work.KT.HopfK
