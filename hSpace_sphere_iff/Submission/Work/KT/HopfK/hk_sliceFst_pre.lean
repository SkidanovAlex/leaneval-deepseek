/-
# Preliminaries for the first-slice generator statement (`hk_slice_gen_fst`)

This module builds the mirror image of the "`(e,·)`-slice" theory of
`Submission.Work.KT.HopfK.hk_slice_gen` for the "`(·,e)`-slice":

* `hemiUp m` : the closed upper chart `x ↦ (x, √(1-‖x‖²))` of `Tgt m`;
* `scalePtFst` : the deformation `s ↦ ‖v‖ • H s v̂` for the *right* action homotopy
  `hS.hmulE : (· * e) ≃ id`;
* `homPtFst` : the induced deformation of `Tgt m` fixing the height;
* `hopfPsiFst` : the hom `Kpair (Eu m) → C(Tgt m, ℂ)` restricting a boundary-trivialised
  function on the disc to the closed *upper* hemisphere and extending by a constant;
* `hopfGHomFst` : the homotopy of matrices over `C(Tgt m, ℂ)` deforming the base part into the
  first slice.
-/
import Mathlib
import Submission.Work.KT.HopfK.hk_slice_gen
import Submission.Work.KT.HopfK.Interface
import Submission.Work.KT.HopfK.Disk
import Submission.Work.KT.HopfK.hk_sliceFst

namespace Work.KT.HopfK

open _root_.Matrix

noncomputable section

set_option maxHeartbeats 4000000

/-! ## The upper chart of `Tgt m` -/

lemma hemiUp_key (m : ℕ) (x : Ball (Eu m)) :
    ‖(x : Eu m)‖ ^ 2 + (Real.sqrt (1 - ‖(x : Eu m)‖ ^ 2)) ^ 2 = 1 := by
  have hx : ‖(x : Eu m)‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp x.2
    rwa [dist_eq_norm, sub_zero] at h
  have h1 : (0 : ℝ) ≤ 1 - ‖(x : Eu m)‖ ^ 2 := by nlinarith [norm_nonneg (x : Eu m)]
  rw [Real.sq_sqrt h1]; ring

/-- The closed upper chart `x ↦ (x, √(1-‖x‖²))` of `Tgt m`. -/
def hemiUp (m : ℕ) : C(Ball (Eu m), Tgt m) where
  toFun x := mkTgt m (x : Eu m) (Real.sqrt (1 - ‖(x : Eu m)‖ ^ 2)) (hemiUp_key m x)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (euclTgtIso m).continuous.comp ((WithLp.prod_continuous_toLp 2 (Eu m) ℝ).comp ?_)
    exact continuous_subtype_val.prodMk (Real.continuous_sqrt.comp (by fun_prop))

@[simp] lemma tgtHeight_hemiUp (m : ℕ) (x : Ball (Eu m)) :
    tgtHeight m (hemiUp m x) = Real.sqrt (1 - ‖(x : Eu m)‖ ^ 2) := by
  show tgtHeight m (mkTgt m (x : Eu m) (Real.sqrt (1 - ‖(x : Eu m)‖ ^ 2))
    (hemiUp_key m x)) = _
  rw [tgtHeight_mkTgt]

@[simp] lemma lowerPt_hemiUp (m : ℕ) (x : Ball (Eu m)) : lowerPt m (hemiUp m x) = x :=
  Subtype.ext (by
    show ((lowerPt m (mkTgt m (x : Eu m) (Real.sqrt (1 - ‖(x : Eu m)‖ ^ 2))
      (hemiUp_key m x)) : Ball (Eu m)) : Eu m) = (x : Eu m)
    rw [lowerPt_mkTgt])

lemma tgtHeight_hemiUp_nonneg (m : ℕ) (x : Ball (Eu m)) : 0 ≤ tgtHeight m (hemiUp m x) := by
  rw [tgtHeight_hemiUp]; exact Real.sqrt_nonneg _

lemma hemiUp_bdry (m : ℕ) (x : Ball (Eu m)) (hx : x ∈ bdry (Eu m)) :
    tgtHeight m (hemiUp m x) = 0 := by
  have hx' : ‖(x : Eu m)‖ = 1 := hx
  rw [tgtHeight_hemiUp, hx']; norm_num

/-- On the closed upper hemisphere the upper chart is a section of `lowerPt`. -/
lemma mkTgt_congr {m : ℕ} {v v' : Eu m} {s s' : ℝ} (hv : v = v') (hs : s = s')
    (h : ‖v‖ ^ 2 + s ^ 2 = 1) (h' : ‖v'‖ ^ 2 + s' ^ 2 = 1) :
    mkTgt m v s h = mkTgt m v' s' h' := by
  subst hv; subst hs; rfl

/-- On the closed upper hemisphere the upper chart is a section of `lowerPt`. -/
lemma hemiUp_lowerPt (m : ℕ) (t : Tgt m) (ht : 0 ≤ tgtHeight m t) :
    hemiUp m (lowerPt m t) = t := by
  have hsq : ‖((lowerPt m t : Ball (Eu m)) : Eu m)‖ ^ 2 + (tgtHeight m t) ^ 2 = 1 := by
    rw [lowerPt_coe]; exact fst_sq_add_snd_sq m t
  have hval : Real.sqrt (1 - ‖((lowerPt m t : Ball (Eu m)) : Eu m)‖ ^ 2) = tgtHeight m t := by
    have h1 : (1 : ℝ) - ‖((lowerPt m t : Ball (Eu m)) : Eu m)‖ ^ 2 = (tgtHeight m t) ^ 2 := by
      linarith [hsq]
    rw [h1, Real.sqrt_sq ht]
  show mkTgt m (((lowerPt m t : Ball (Eu m)) : Eu m))
    (Real.sqrt (1 - ‖((lowerPt m t : Ball (Eu m)) : Eu m)‖ ^ 2)) (hemiUp_key m (lowerPt m t)) = t
  rw [mkTgt_congr (m := m) (v := ((lowerPt m t : Ball (Eu m)) : Eu m)) rfl hval
    (hemiUp_key m (lowerPt m t)) hsq]
  exact mkTgt_lowerPt m t

/-! ## The right-action deformation -/

/-- `s ↦ ‖v‖ • H s v̂`, where `H` is the homotopy `(· * e) ≃ id` of the `H`-space structure. -/
def scalePtFst (m : ℕ) (hS : HSpace (Sph (Eu m))) (s : unitInterval) (v : Eu m) : Eu m :=
  ‖v‖ • ((hS.hmulE (s, sphereArg m hS v)) : Eu m)

lemma norm_scalePtFst (m : ℕ) (hS : HSpace (Sph (Eu m))) (s : unitInterval) (v : Eu m) :
    ‖scalePtFst m hS s v‖ = ‖v‖ := by
  rw [scalePtFst, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
  have h := Metric.mem_sphere.mp (hS.hmulE (s, sphereArg m hS v)).2
  rw [dist_eq_norm, sub_zero] at h
  rw [h, mul_one]

lemma continuousOn_scalePtFst (m : ℕ) (hS : HSpace (Sph (Eu m))) :
    ContinuousOn (fun p : unitInterval × Eu m => scalePtFst m hS p.1 p.2) {p | p.2 ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hfun : {p : unitInterval × Eu m | p.2 ≠ 0}.domRestrict
        (fun p => scalePtFst m hS p.1 p.2)
      = fun p : {p : unitInterval × Eu m // p.2 ≠ 0} =>
          ‖(p.1.2 : Eu m)‖ • ((hS.hmulE (p.1.1, normPt m ⟨p.1.2, p.2⟩)) : Eu m) := by
    funext p
    show scalePtFst m hS p.1.1 p.1.2 = _
    rw [scalePtFst, sphereArg, dif_neg p.2]
  rw [hfun]
  refine Continuous.smul (f := fun p : {p : unitInterval × Eu m // p.2 ≠ 0} => ‖(p.1.2 : Eu m)‖)
    (g := fun p : {p : unitInterval × Eu m // p.2 ≠ 0} =>
      ((hS.hmulE (p.1.1, normPt m ⟨p.1.2, p.2⟩)) : Eu m)) ?_ ?_
  · exact continuous_norm.comp continuous_subtype_val.snd
  · exact continuous_subtype_val.comp
      ((hS.hmulE.toContinuousMap.continuous).comp
        ((continuous_subtype_val.fst).prodMk
          ((continuous_normPt m).comp (Continuous.subtype_mk continuous_subtype_val.snd _))))

lemma continuous_scalePtFst (m : ℕ) (hS : HSpace (Sph (Eu m))) :
    Continuous fun p : unitInterval × Eu m => scalePtFst m hS p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s, v⟩
  by_cases hv : v = 0
  · subst hv
    refine continuousAt_smul_of_norm_le_one (x := (s, (0 : Eu m)))
      (f := fun p : unitInterval × Eu m => ‖p.2‖) (by fun_prop)
      (g := fun p : unitInterval × Eu m =>
        ((hS.hmulE (p.1, sphereArg m hS p.2)) : Eu m)) (fun p => ?_) (by simp)
    have h := Metric.mem_sphere.mp (hS.hmulE (p.1, sphereArg m hS p.2)).2
    rw [dist_eq_norm, sub_zero] at h
    exact le_of_eq h
  · exact (continuousOn_scalePtFst m hS).continuousAt
      ((isOpen_ne.preimage continuous_snd).mem_nhds hv)

lemma scalePtFst_one (m : ℕ) (hS : HSpace (Sph (Eu m))) (v : Eu m) :
    scalePtFst m hS 1 v = v := by
  have h1 : ((hS.hmulE (1, sphereArg m hS v) : Sph (Eu m)) : Eu m)
      = ((sphereArg m hS v : Sph (Eu m)) : Eu m) :=
    congrArg Subtype.val (hS.hmulE.map_one_left (sphereArg m hS v))
  rw [scalePtFst, h1]
  by_cases hv : v = 0
  · simp [hv, sphereArg]
  · rw [sphereArg, dif_neg hv]
    show ‖v‖ • ((normPt m ⟨v, hv⟩ : Sph (Eu m)) : Eu m) = v
    rw [show ((normPt m ⟨v, hv⟩ : Sph (Eu m)) : Eu m) = unitV v from rfl, unitV, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

lemma scalePtFst_zero (m : ℕ) (hS : HSpace (Sph (Eu m))) (y : Ball (Eu m)) :
    scalePtFst m hS 0 (y : Eu m) = hopfFst m hS.hmul ((y : Eu m), (hS.e : Eu m)) := by
  have he1 : ‖(hS.e : Eu m)‖ = 1 := by
    have h := Metric.mem_sphere.mp hS.e.2
    rwa [dist_eq_norm, sub_zero] at h
  have hene : (hS.e : Eu m) ≠ 0 := by
    intro h; rw [h, norm_zero] at he1; exact one_ne_zero he1.symm
  have hyl : ‖(y : Eu m)‖ ≤ 1 := mem_closedBall_zero_iff.mp y.2
  have hmin : min ‖(y : Eu m)‖ ‖(hS.e : Eu m)‖ = ‖(y : Eu m)‖ := by
    rw [he1]; exact min_eq_left hyl
  have h0 : scalePtFst m hS 0 (y : Eu m)
      = ‖(y : Eu m)‖ • ((hS.hmul (sphereArg m hS (y : Eu m), hS.e) : Sph (Eu m)) : Eu m) := by
    rw [scalePtFst]
    exact congrArg _ (congrArg Subtype.val (hS.hmulE.map_zero_left _))
  rw [h0, hopfFst, hmin]
  by_cases hv : (y : Eu m) = 0
  · rw [hv]; simp
  · congr 1
    rw [sphereArg, dif_neg hv, muNorm, dif_neg (by push Not; exact ⟨hv, hene⟩)]
    have hnp : (normPt m ⟨(hS.e : Eu m), hene⟩ : Sph (Eu m)) = hS.e :=
      Subtype.ext (by
        show unitV (hS.e : Eu m) = (hS.e : Eu m)
        rw [unitV, he1, inv_one, one_smul])
    rw [hnp]

/-! ## The deformation of `Tgt m` -/

/-- The point obtained by applying the right-action `H`-homotopy in the first model coordinate. -/
def homPtFst (m : ℕ) (hS : HSpace (Sph (Eu m))) (s : unitInterval) (t : Tgt m) : Tgt m :=
  mkTgt m (scalePtFst m hS s (lowerPt m t : Eu m)) (tgtHeight m t) (by
    rw [norm_scalePtFst]; exact fst_sq_add_snd_sq m t)

lemma tgtSph_homPtFst (m : ℕ) (hS : HSpace (Sph (Eu m))) (s : unitInterval) (t : Tgt m) :
    ((tgtSph m (homPtFst m hS s t) : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))
      = WithLp.toLp 2 (scalePtFst m hS s (lowerPt m t : Eu m), tgtHeight m t) :=
  tgtSph_mkTgt m _ _ _

lemma tgtHeight_homPtFst (m : ℕ) (hS : HSpace (Sph (Eu m))) (s : unitInterval) (t : Tgt m) :
    tgtHeight m (homPtFst m hS s t) = tgtHeight m t := tgtHeight_mkTgt m _ _ _

@[simp] lemma homPtFst_one (m : ℕ) (hS : HSpace (Sph (Eu m))) (t : Tgt m) :
    homPtFst m hS 1 t = t := by
  apply tgtSph_inj
  rw [tgtSph_homPtFst, scalePtFst_one]
  show WithLp.toLp 2 ((lowerPt m t : Eu m), tgtHeight m t)
    = ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))
  rw [← WithLp.toLp_ofLp 2 ((tgtSph m t : Sph (WithLp 2 (Eu m × ℝ))) : WithLp 2 (Eu m × ℝ))]
  rfl

lemma continuous_homPtFst (m : ℕ) (hS : HSpace (Sph (Eu m))) :
    Continuous fun p : unitInterval × Tgt m => homPtFst m hS p.1 p.2 := by
  have h1 : Continuous fun p : unitInterval × Tgt m =>
      WithLp.toLp 2 (scalePtFst m hS p.1 (lowerPt m p.2 : Eu m), tgtHeight m p.2) :=
    (WithLp.prod_continuous_toLp 2 (Eu m) ℝ).comp
      (((continuous_scalePtFst m hS).comp (continuous_fst.prodMk
        (continuous_subtype_val.comp
          ((lowerPt m).continuous.comp continuous_snd)))).prodMk
        ((hk_continuous_tgtHeight m).comp continuous_snd))
  refine Continuous.subtype_mk ?_ _
  refine ((euclTgtIso m).continuous.comp h1).congr ?_
  intro p
  rfl

/-- The model coordinates of `hopfKMap m μ (ptFst m e y)`. -/
lemma tgtSph_hopfKMap_ptFst (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (e : Sph (Eu m)) (y : Ball (Eu m)) :
    ((tgtSph m (hopfKMap m μ (ptFstSph m e y)) : Sph (WithLp 2 (Eu m × ℝ)))
        : WithLp 2 (Eu m × ℝ))
      = WithLp.toLp 2 (hopfFst m μ ((y : Eu m), (e : Eu m)),
          hopfSnd m ((y : Eu m), (e : Eu m))) := by
  have h1 : (euclTgtIso m).symm ((hopfKMap m μ (ptFstSph m e y) : Tgt m)
      : EuclideanSpace ℝ (Fin (2 * m + 1)))
      = hopfRaw m μ ((y : Eu m), (e : Eu m)) :=
    LinearIsometryEquiv.symm_apply_apply _ _
  rw [tgtSph_coe, h1]
  rfl

/-- `homPtFst 0` applied to the upper chart is the Hopf construction at `(y, e)`. -/
lemma tgtSph_homPtFst_zero_hemiUp (m : ℕ) (hS : HSpace (Sph (Eu m))) (y : Ball (Eu m)) :
    ((tgtSph m (homPtFst m hS 0 (hemiUp m y)) : Sph (WithLp 2 (Eu m × ℝ)))
        : WithLp 2 (Eu m × ℝ))
      = ((tgtSph m (hopfKMap m hS.hmul (ptFstSph m hS.e y)) : Sph (WithLp 2 (Eu m × ℝ)))
        : WithLp 2 (Eu m × ℝ)) := by
  have hyl : ‖(y : Eu m)‖ ≤ 1 := mem_closedBall_zero_iff.mp y.2
  have he1 : ‖(hS.e : Eu m)‖ = 1 := by
    have h := Metric.mem_sphere.mp hS.e.2
    rwa [dist_eq_norm, sub_zero] at h
  have hsnd : hopfSnd m ((y : Eu m), (hS.e : Eu m)) = Real.sqrt (1 - ‖(y : Eu m)‖ ^ 2) := by
    rw [hopfSnd_of_le m (z := ((y : Eu m), (hS.e : Eu m))) (by rw [he1]; exact hyl), he1,
      one_pow]
  rw [tgtSph_homPtFst, tgtSph_hopfKMap_ptFst]
  refine WithLp.toLp_injective 2 ?_
  rw [scalePtFst_zero, tgtHeight_hemiUp, lowerPt_hemiUp, hsnd]

lemma homPtFst_zero_hemiUp (m : ℕ) (hS : HSpace (Sph (Eu m))) (y : Ball (Eu m)) :
    homPtFst m hS 0 (hemiUp m y) = hopfKMap m hS.hmul (ptFstSph m hS.e y) :=
  tgtSph_inj (tgtSph_homPtFst_zero_hemiUp m hS y)

/-! ## The hom `Kpair (Eu m) → C(Tgt m, ℂ)` for the first slice -/

/-- The underlying function of `hopfPsiFst u`. -/
def hopfPsiFstFun (m : ℕ) (hS : HSpace (Sph (Eu m))) (u : Kpair (Eu m)) (t : Tgt m) : ℂ :=
  (u : C(Ball (Eu m), ℂ))
    (if 0 ≤ tgtHeight m t then lowerPt m t else sphToBall hS.e)

lemma continuous_hopfPsiFstFun (m : ℕ) (hS : HSpace (Sph (Eu m))) (u : Kpair (Eu m)) :
    Continuous (hopfPsiFstFun m hS u) := by
  have hs1 : IsClosed {t : Tgt m | 0 ≤ tgtHeight m t} :=
    isClosed_le continuous_const (hk_continuous_tgtHeight m)
  have hs2 : IsClosed {t : Tgt m | tgtHeight m t ≤ 0} :=
    isClosed_le (hk_continuous_tgtHeight m) continuous_const
  have hcov : {t : Tgt m | 0 ≤ tgtHeight m t} ∪ {t : Tgt m | tgtHeight m t ≤ 0} = Set.univ := by
    ext t
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact le_total 0 (tgtHeight m t)
  rw [← continuousOn_univ, ← hcov]
  refine ContinuousOn.union_of_isClosed ?_ ?_ hs1 hs2
  · refine ContinuousOn.congr
      ((u : C(Ball (Eu m), ℂ)).continuous.comp (lowerPt m).continuous).continuousOn ?_
    intro t ht
    show hopfPsiFstFun m hS u t = (u : C(Ball (Eu m), ℂ)) ((lowerPt m) t)
    simp only [hopfPsiFstFun, if_pos (show 0 ≤ tgtHeight m t from ht)]
  · refine ContinuousOn.congr
      (continuousOn_const (c := (u : C(Ball (Eu m), ℂ)) (sphToBall hS.e))) ?_
    intro t ht
    by_cases h : 0 ≤ tgtHeight m t
    · simp only [hopfPsiFstFun, if_pos h]
      exact (u : Kpair (Eu m)).2 (lowerPt m t)
        (lowerPt_mem_bdry m t (le_antisymm ht h)) (sphToBall hS.e) (sphToBall_mem_bdry hS.e)
    · simp only [hopfPsiFstFun, if_neg h]

/-- Restrict a boundary-trivialised function on the disc to the closed upper hemisphere (via the
chart) and extend by the constant value `u (sphToBall hS.e)` on the closed lower hemisphere. -/
def hopfPsiFst (m : ℕ) (hS : HSpace (Sph (Eu m))) : Kpair (Eu m) →ₐ[ℂ] C(Tgt m, ℂ) where
  toFun u := ⟨hopfPsiFstFun m hS u, continuous_hopfPsiFstFun m hS u⟩
  map_one' := by ext t; simp [hopfPsiFstFun]
  map_mul' := by intro u v; ext t; simp [hopfPsiFstFun]
  map_zero' := by ext t; simp [hopfPsiFstFun]
  map_add' := by intro u v; ext t; simp [hopfPsiFstFun]
  commutes' := by intro c; ext t; simp [hopfPsiFstFun]

@[simp] lemma hopfPsiFst_apply (m : ℕ) (hS : HSpace (Sph (Eu m))) (u : Kpair (Eu m))
    (t : Tgt m) : hopfPsiFst m hS u t = hopfPsiFstFun m hS u t := rfl

lemma hopfPsiFst_injective (m : ℕ) (hS : HSpace (Sph (Eu m))) :
    Function.Injective (hopfPsiFst m hS) := by
  intro u v h
  refine Subtype.ext ?_
  ext y
  have h0 : 0 ≤ tgtHeight m (hemiUp m y) := tgtHeight_hemiUp_nonneg m y
  have h1 := congrArg (fun w : C(Tgt m, ℂ) => w (hemiUp m y)) h
  simp only [hopfPsiFst_apply, hopfPsiFstFun, if_pos h0, lowerPt_hemiUp] at h1
  exact h1

/-! ## The homotopy of matrices over `C(Tgt m, ℂ)` -/

/-- The right-action `H`-homotopy on matrices over `C(Tgt m, ℂ)`. -/
def hopfGHomFst (m : ℕ) (hS : HSpace (Sph (Eu m))) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) C(Tgt m, ℂ)) (p : unitInterval × Tgt m) :
    Matrix (Fin n) (Fin n) ℂ :=
  if 0 ≤ tgtHeight m p.2 then g.map (evalC (homPtFst m hS p.1 p.2))
    else g.map (evalC p.2)

lemma hopfGHomFst_idem (m : ℕ) (hS : HSpace (Sph (Eu m))) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) C(Tgt m, ℂ)) (hg : g * g = g) (p : unitInterval × Tgt m) :
    hopfGHomFst m hS g p * hopfGHomFst m hS g p = hopfGHomFst m hS g p := by
  unfold hopfGHomFst
  split_ifs with h
  · rw [← Matrix.map_mul, hg]
  · rw [← Matrix.map_mul, hg]

lemma continuous_hopfGHomFst (m : ℕ) (hS : HSpace (Sph (Eu m))) (n r : ℕ)
    (Q : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m hS.hmul)))
    (hcap : ∀ t : Tgt m, t ∈ capTminus m →
      Q.map (evalT m (hopfKMap m hS.hmul) t) = diagIdemMat r n) :
    Continuous (hopfGHomFst m hS (Q.map (coneToT (hopfKMap m hS.hmul)))) := by
  have hcont1 : Continuous fun p : unitInterval × Tgt m =>
      (Q.map (coneToT (hopfKMap m hS.hmul))).map (evalC (homPtFst m hS p.1 p.2)) := by
    refine continuous_matrix fun i j => ?_
    exact ((Q.map (coneToT (hopfKMap m hS.hmul))) i j).continuous.comp (continuous_homPtFst m hS)
  have hcont2 : Continuous fun p : unitInterval × Tgt m =>
      (Q.map (coneToT (hopfKMap m hS.hmul))).map (evalC p.2) := by
    refine continuous_matrix fun i j => ?_
    exact ((Q.map (coneToT (hopfKMap m hS.hmul))) i j).continuous.comp continuous_snd
  unfold hopfGHomFst
  refine continuous_if ?_ hcont1.continuousOn hcont2.continuousOn
  intro p hp
  have ht0 : tgtHeight m p.2 = 0 := by
    have h1 : 0 ≤ tgtHeight m p.2 := by
      have h2 : p ∈ closure {q : unitInterval × Tgt m | 0 ≤ tgtHeight m q.2} := hp.1
      have h3 : IsClosed {q : unitInterval × Tgt m | 0 ≤ tgtHeight m q.2} :=
        isClosed_le continuous_const ((hk_continuous_tgtHeight m).comp continuous_snd)
      rw [h3.closure_eq] at h2
      exact h2
    have h4 : tgtHeight m p.2 ≤ 0 := by
      have hh : p ∈ closure ({x : unitInterval × Tgt m | 0 ≤ tgtHeight m x.2}ᶜ) := by
        rw [closure_compl]; exact hp.2
      have hset : ({x : unitInterval × Tgt m | 0 ≤ tgtHeight m x.2}ᶜ)
          = {q : unitInterval × Tgt m | tgtHeight m q.2 < 0} := by
        ext q; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
      have h2 : p ∈ closure {q : unitInterval × Tgt m | tgtHeight m q.2 < 0} := by
        rw [hset] at hh; exact hh
      exact closure_lt_subset_le ((hk_continuous_tgtHeight m).comp continuous_snd)
        continuous_const h2
    exact le_antisymm h4 h1
  rw [map_evalC_eq_map_evalT m hS n Q, map_evalC_eq_map_evalT m hS n Q,
    hcap _ (by simp only [capTminus, Set.mem_setOf_eq, tgtHeight_homPtFst, ht0]; norm_num),
    hcap _ (by simp only [capTminus, Set.mem_setOf_eq, ht0]; norm_num)]

lemma map_evalC_g_eq_diagFst (m : ℕ) (hS : HSpace (Sph (Eu m))) (n r : ℕ)
    (Q : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m hS.hmul)))
    (hcap : ∀ t : Tgt m, t ∈ capTminus m →
      Q.map (evalT m (hopfKMap m hS.hmul) t) = diagIdemMat r n)
    {t : Tgt m} (ht : t ∈ capTminus m) :
    (Q.map (coneToT (hopfKMap m hS.hmul))).map (evalC t) = diagIdemMat r n := by
  rw [map_evalC_eq_map_evalT m hS n Q]
  exact hcap t ht

end

end Work.KT.HopfK
