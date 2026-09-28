import Submission.Work.ThomBordism.Grassmann.Grassmannian
import Submission.Work.ThomBordism.Grassmann.Coord
import Submission.Work.Thom.thomClass_of_oriented_fintype
import Submission.Work.Cohomology.relComplex_empty_homology_iso

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The tautological oriented bundle: the sign correction that makes its trivialisations
orientation-consistent, and the Thom isomorphism theorem for it

The naive gluing data of `Grassmannian.lean` presents the tautological oriented rank-`k` bundle over
`G̃r_k(ℝ^{k+m})` by the coordinate projections `p_S` of the frames, whose transition functions
`frameMatrix T f * (frameMatrix S f)⁻¹` have determinant of *either* sign (the projection `p_S` is
orientation-preserving exactly when the frame is positively oriented in the coordinates `S`, and the
sign of `det (frameMatrix S f)` is a nowhere-zero, non-constant continuous function on `baseSet S`).

This module corrects the trivialisations by a **sign gauge**: on `baseSet S` the gauge
`orientMat S` is the diagonal matrix `diag(ε, 1, …, 1)` with `ε = det A_S / |det A_S| ∈ {±1}`.
Since `ε` is a *continuous* (locally constant) function on `baseSet S`, the corrected transitions
`D_T ∘ (A_T A_S⁻¹) ∘ D_S` are again continuous, satisfy the cocycle (because `D_S² = 1`) and now
have **positive determinant** — because `sign (det D_S) = sign (det A_S)`, so the sign of the
transition determinant is `ε_T · ε_T ε_S · ε_S = 1`.

The payoff is `hasTautologicalThomClass`: the corrected bundle is oriented in the strict sense
required by `Work.Thom.thomClass_of_oriented_fintype`, so it carries a Thom class.  `Tautological
bundle` in this chapter *is* the corrected one (`Oriented.tautologicalBundle`), the naive gluing
data being kept as `Grassmannian.tautologicalBundleNaive`; the two present the same bundle (they
differ by the gauge `orientMat`, a fibrewise linear automorphism over the base).
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology
open CategoryTheory

noncomputable section

variable {k m : ℕ}

/-! ## The determinant of `matLin` -/

/-- The determinant of the matrix model `matLin M` of an endomorphism of `Amb k` is the determinant
of `M`. -/
theorem det_matLin (M : Matrix (Fin k) (Fin k) ℝ) :
    LinearMap.det (matLin M).toLinearMap = M.det := by
  let e : Amb k ≃ₗ[ℝ] (Fin k → ℝ) := WithLp.linearEquiv 2 ℝ (Fin k → ℝ)
  have hfun : (matLin M).toLinearMap
      = ((e.symm : (Fin k → ℝ) ≃ₗ[ℝ] Amb k) : (Fin k → ℝ) →ₗ[ℝ] Amb k) ∘ₗ
        (Matrix.toLin' M) ∘ₗ ((e : Amb k →ₗ[ℝ] (Fin k → ℝ))) := by
    apply LinearMap.ext
    intro v
    show matLin M v = _
    rw [LinearMap.comp_apply, LinearMap.comp_apply, matLin_apply, Matrix.toLin'_apply]
    rfl
  rw [hfun]
  exact (LinearMap.det_conj (Matrix.toLin' M) (e.symm : (Fin k → ℝ) ≃ₗ[ℝ] Amb k)).trans
    (LinearMap.det_toLin' M)

/-- `M ↦ M.det` is continuous. -/
theorem continuous_matrix_det : Continuous (fun M : Matrix (Fin k) (Fin k) ℝ => M.det) := by
  fun_prop

/-! ## The sign of the determinant of the frame matrix -/

/-- The sign `det A / |det A| ∈ {±1}` of the `S`-minor of a frame `f`. -/
def frameSignFun (S : ChartIdx k m) (f : Stiefel k m) : ℝ :=
  (frameMatrix S f.1).det / |(frameMatrix S f.1).det|

theorem frameSignFun_invariant (S : ChartIdx k m) (A : SOk k) (f : Stiefel k m) :
    frameSignFun S (A.act f) = frameSignFun S f := by
  show (frameMatrix S (soActFun A.1 f.1)).det / |(frameMatrix S (soActFun A.1 f.1)).det|
      = (frameMatrix S f.1).det / |(frameMatrix S f.1).det|
  rw [det_frameMatrix_soActFun, A.2.2, mul_one]

/-- **The sign attached to a point of the Grassmannian**: the sign of the determinant of the
`S`-minor of any frame representing it (well defined because the action of `SO(k)` does not change
the determinant). -/
def frameSign (S : ChartIdx k m) : OG k m → ℝ :=
  Quotient.lift (frameSignFun S) fun f g hfg => by
    obtain ⟨A, rfl⟩ := hfg
    exact (frameSignFun_invariant S A f).symm

@[simp] theorem frameSign_mk (S : ChartIdx k m) (f : Stiefel k m) :
    frameSign S (Quotient.mk'' f) = frameSignFun S f := rfl

theorem continuousOn_frameSignFun (S : ChartIdx k m) :
    ContinuousOn (frameSignFun S) (chartSet S) := by
  have hdet : ContinuousOn (fun f : Stiefel k m => (frameMatrix S f.1).det) (chartSet S) :=
    (continuous_matrix_det (k := k)).comp_continuousOn (continuous_frameMatrix S).continuousOn
  exact hdet.div hdet.abs (fun f hf => abs_ne_zero.mpr hf)

/-- The sign function is continuous on the chart `S` (it is locally constant there). -/
theorem continuousOn_frameSign (S : ChartIdx k m) : ContinuousOn (frameSign S) (baseSet S) := by
  have hpre : (Quotient.mk'' ⁻¹' baseSet S) = chartSet S := by
    ext f
    rw [Set.mem_preimage, mem_baseSet_iff]
  have hq : Topology.IsQuotientMap
      ((baseSet S).restrictPreimage (Quotient.mk'' : Stiefel k m → OG k m)) :=
    Topology.IsQuotientMap.restrictPreimage_isOpen isQuotientMap_quotient_mk' (isOpen_baseSet S)
  have hcomp : ((baseSet S).domRestrict (frameSign S)) ∘
        ((baseSet S).restrictPreimage (Quotient.mk'' : Stiefel k m → OG k m))
      = fun y : ↥(Quotient.mk'' ⁻¹' (baseSet S)) => frameSignFun S y.1 := by
    funext y
    rfl
  rw [continuousOn_iff_continuous_domRestrict, hq.isCoinducing.eq_coinduced, continuous_coinduced_dom]
  rw [hcomp, hpre]
  exact continuousOn_iff_continuous_domRestrict.mp (continuousOn_frameSignFun S)

/-- The sign is `±1` on the chart: it is a unit. -/
theorem frameSign_mul_self (S : ChartIdx k m) (x : OG k m) (hx : x ∈ baseSet S) :
    frameSign S x * frameSign S x = 1 := by
  obtain ⟨f, hf⟩ := Quotient.exists_rep x
  have hx' : Quotient.mk'' f ∈ baseSet S := Set.mem_of_eq_of_mem hf hx
  have h : (frameMatrix S f.1).det ≠ 0 := (mem_baseSet_iff S f).mp hx'
  rw [← hf, frameSign_mk, frameSignFun, div_mul_div_comm, ← sq, ← sq, sq_abs,
    div_self (pow_ne_zero 2 h)]

/-- The determinant of the frame matrix multiplied by the sign is its absolute value. -/
theorem frameSignFun_eq_one_of_k_eq_zero {S : ChartIdx k m} (h : k = 0) (f : Stiefel k m) :
    frameSignFun S f = 1 := by
  subst h
  have : frameMatrix S f.1 = 1 := Subsingleton.elim _ _
  simp [frameSignFun, this]

theorem frameSign_eq_one_of_k_eq_zero {S : ChartIdx k m} (h : k = 0) (x : OG k m) :
    frameSign S x = 1 := by
  obtain ⟨f, hf⟩ := Quotient.exists_rep x
  rw [← hf, frameSign_mk, frameSignFun_eq_one_of_k_eq_zero h f]

theorem frameMatrix_det_eq_sign (S : ChartIdx k m) (f : Stiefel k m) (hx : f ∈ chartSet S) :
    (frameMatrix S f.1).det = frameSign S (Quotient.mk'' f) * |(frameMatrix S f.1).det| := by
  rw [frameSign_mk, frameSignFun, div_mul_cancel₀ _ (abs_ne_zero.mpr hx)]

/-! ## The sign gauge and the corrected transition functions -/

/-- **The sign gauge on the chart `S`**: the diagonal matrix `diag(ε, 1, …, 1)` with
`ε = frameSign S x ∈ {±1}`.  (For `k = 0` there is no coordinate to change and the matrix is `1`.) -/
def orientMat (S : ChartIdx k m) (x : OG k m) : Matrix (Fin k) (Fin k) ℝ :=
  if h : k = 0 then 1 else
    Matrix.diagonal fun i : Fin k =>
      if i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k) then frameSign S x else 1

theorem orientMat_of_ne_zero {S : ChartIdx k m} {x : OG k m} (h : k ≠ 0) :
    orientMat S x = Matrix.diagonal (fun i : Fin k =>
      if i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k) then frameSign S x else 1) :=
  dif_neg h

/-- The gauge has determinant the sign `ε`. -/
theorem orientMat_det {S : ChartIdx k m} (x : OG k m) :
    (orientMat S x).det = frameSign S x := by
  by_cases h : k = 0
  · rw [orientMat, dif_pos h, Matrix.det_one, frameSign_eq_one_of_k_eq_zero h x]
  · rw [orientMat_of_ne_zero h, Matrix.det_diagonal,
      Finset.prod_eq_single (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k)
        (fun b _ hb => by rw [if_neg hb])
        (fun hmem => absurd (Finset.mem_univ _) hmem)]
    rw [if_pos rfl]

/-- The gauge is an involution. -/
theorem orientMat_mul_self {S : ChartIdx k m} (x : OG k m) (hx : x ∈ baseSet S) :
    orientMat S x * orientMat S x = 1 := by
  by_cases h : k = 0
  · rw [orientMat, dif_pos h]; exact mul_one 1
  · rw [orientMat_of_ne_zero h, Matrix.diagonal_mul_diagonal]
    have hfun : (fun i : Fin k =>
        (if i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k) then frameSign S x else 1)
          * (if i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k) then frameSign S x else 1))
        = fun _ : Fin k => (1 : ℝ) := by
      funext i
      by_cases hi : i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k)
      · rw [if_pos hi, frameSign_mul_self S x hx]
      · rw [if_neg hi]; simp
    rw [hfun, Matrix.diagonal_one]

/-- `d ↦ Matrix.diagonal d` is continuous. -/
theorem continuous_diagonal : Continuous (fun d : Fin k → ℝ => Matrix.diagonal d) := by
  fun_prop

/-- The sign gauge depends continuously on the point of the chart. -/
theorem continuousOn_orientMat (S : ChartIdx k m) :
    ContinuousOn (orientMat S) (baseSet S) := by
  by_cases h : k = 0
  · rw [show orientMat S = fun _ : OG k m => (1 : Matrix (Fin k) (Fin k) ℝ) from
      funext fun x => by rw [orientMat, dif_pos h]]
    exact continuousOn_const
  · have hsign : ContinuousOn (fun x : OG k m => frameSign S x) (baseSet S) :=
      continuousOn_frameSign S
    rw [show orientMat S = fun x : OG k m => Matrix.diagonal (fun i : Fin k =>
        if i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k) then frameSign S x else 1) from
      funext fun x => orientMat_of_ne_zero h]
    refine continuous_diagonal.comp_continuousOn (continuousOn_pi.mpr fun i => ?_)
    by_cases hi : i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k)
    · rw [show (fun y : OG k m =>
          if i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k) then frameSign S y else 1)
          = fun y => frameSign S y from funext fun y => by rw [if_pos hi]]
      exact hsign
    · rw [show (fun y : OG k m =>
          if i = (⟨0, Nat.pos_of_ne_zero h⟩ : Fin k) then frameSign S y else 1)
          = fun _ => (1 : ℝ) from funext fun y => by rw [if_neg hi]]
      exact continuousOn_const

/-- **The corrected transition function** `D_T ∘ coordChange S T ∘ D_S`: the transition
functions of the tautological bundle, gauged by the sign gauge.  (Outside the overlap the gauge is
the junk value `frameSign = 0`, which the vector-bundle axioms never see.) -/
def coordChangeO (S T : ChartIdx k m) (x : OG k m) : Amb k →L[ℝ] Amb k :=
  ((matLin (orientMat T x)).comp (coordChange S T x)).comp (matLin (orientMat S x))

theorem coordChangeO_apply (S T : ChartIdx k m) (x : OG k m) (v : Amb k) :
    coordChangeO S T x v = matLin (orientMat T x) (coordChange S T x (matLin (orientMat S x) v)) :=
  rfl

theorem coordChangeO_self (S : ChartIdx k m) (x : OG k m) (hx : x ∈ baseSet S) (v : Amb k) :
    coordChangeO S S x v = v := by
  rw [coordChangeO_apply, coordChange_self S x hx]
  have h2 : (matLin (orientMat S x)).comp (matLin (orientMat S x)) = 1 := by
    rw [← matLin_mul, orientMat_mul_self x hx, matLin_one]
  rw [← ContinuousLinearMap.comp_apply, h2, ContinuousLinearMap.one_apply]

theorem coordChangeO_comp (i j l : ChartIdx k m) (x : OG k m)
    (hx : x ∈ baseSet i ∩ baseSet j ∩ baseSet l) (v : Amb k) :
    coordChangeO j l x (coordChangeO i j x v) = coordChangeO i l x v := by
  obtain ⟨hij, hl⟩ := hx
  obtain ⟨hi, hj⟩ := hij
  have hDj : ∀ w : Amb k, matLin (orientMat j x) (matLin (orientMat j x) w) = w := by
    intro w
    have h2 : (matLin (orientMat j x)).comp (matLin (orientMat j x)) = 1 := by
      rw [← matLin_mul, orientMat_mul_self x hj, matLin_one]
    rw [← ContinuousLinearMap.comp_apply, h2, ContinuousLinearMap.one_apply]
  rw [coordChangeO_apply, coordChangeO_apply, coordChangeO_apply, hDj,
    coordChange_comp i j l x ⟨⟨hi, hj⟩, hl⟩]

theorem continuousOn_coordChangeO (S T : ChartIdx k m) :
    ContinuousOn (coordChangeO S T) (baseSet S ∩ baseSet T) := by
  have hc : ContinuousOn (coordChange S T) (baseSet S ∩ baseSet T) := continuousOn_coordChange S T
  have hS : ContinuousOn (fun x : OG k m => matLin (orientMat S x)) (baseSet S ∩ baseSet T) :=
    continuous_matLin.comp_continuousOn ((continuousOn_orientMat S).mono Set.inter_subset_left)
  have hT : ContinuousOn (fun x : OG k m => matLin (orientMat T x)) (baseSet S ∩ baseSet T) :=
    continuous_matLin.comp_continuousOn ((continuousOn_orientMat T).mono Set.inter_subset_right)
  exact (hT.clm_comp hc).clm_comp hS

/-- **The corrected transition functions have positive determinant.**  This is the whole point of
the sign gauge: on the overlap, writing `cc = A_T A_S⁻¹` for a common frame and `ε_S = frameSign S x`
(so that `det A_S = ε_S |det A_S|`), one has

`det (D_T cc D_S) = ε_T · (ε_T ε_S P) · ε_S = P > 0`

with `P = |det A_T| / |det A_S| > 0`. -/
theorem det_coordChangeO_pos (S T : ChartIdx k m) (x : OG k m) (hx : x ∈ baseSet S ∩ baseSet T) :
    0 < LinearMap.det (coordChangeO S T x).toLinearMap := by
  obtain ⟨f, hf⟩ := Quotient.exists_rep x
  have hSmem : Quotient.mk'' f ∈ baseSet S := Set.mem_of_eq_of_mem hf hx.1
  have hTmem : Quotient.mk'' f ∈ baseSet T := Set.mem_of_eq_of_mem hf hx.2
  have hS : f ∈ chartSet S := (mem_baseSet_iff S f).mp hSmem
  have hT : f ∈ chartSet T := (mem_baseSet_iff T f).mp hTmem
  -- unfold the corrected transition at the representative
  have hcc : coordChange S T x = matLin (frameMatrix T f.1 * (frameMatrix S f.1)⁻¹) := by
    rw [← hf, coordChange_mk, coordChangeAux, dif_pos (show (frameMatrix S f.1).det ≠ 0 from hS)]
  have hD : coordChangeO S T x
      = matLin (orientMat T x * (frameMatrix T f.1 * (frameMatrix S f.1)⁻¹)
          * orientMat S x) := by
    rw [coordChangeO, hcc, ← matLin_mul, ← matLin_mul]
  -- determinant of the matrix product
  have hdet : LinearMap.det (coordChangeO S T x).toLinearMap
      = (orientMat T x).det * (frameMatrix T f.1 * (frameMatrix S f.1)⁻¹).det
        * (orientMat S x).det := by
    rw [hD, det_matLin, Matrix.det_mul, Matrix.det_mul]
  -- the signs
  have hεS : frameSign S x * frameSign S x = 1 := by
    rw [← hf]; exact frameSign_mul_self S (Quotient.mk'' f) hSmem
  have hεT : frameSign T x * frameSign T x = 1 := by
    rw [← hf]; exact frameSign_mul_self T (Quotient.mk'' f) hTmem
  have hdS : (frameMatrix S f.1).det
      = frameSign S x * |(frameMatrix S f.1).det| := by
    rw [← hf]; exact frameMatrix_det_eq_sign S f hS
  have hdT : (frameMatrix T f.1).det
      = frameSign T x * |(frameMatrix T f.1).det| := by
    rw [← hf]; exact frameMatrix_det_eq_sign T f hT
  have hdetS1 : (frameMatrix S f.1)⁻¹.det * (frameMatrix S f.1).det = 1 :=
    Matrix.det_nonsing_inv_mul_det (frameMatrix S f.1) (isUnit_iff_ne_zero.mpr hS)
  have hdetS2 : (frameMatrix S f.1).det * (frameMatrix S f.1)⁻¹.det = 1 := by
    rw [mul_comm]; exact hdetS1
  have hinv : ((frameMatrix S f.1)⁻¹).det = ((frameMatrix S f.1).det)⁻¹ :=
    (inv_eq_of_mul_eq_one_right hdetS2).symm
  -- the middle determinant
  have hMd : (frameMatrix T f.1 * (frameMatrix S f.1)⁻¹).det
      = frameSign T x * frameSign S x
        * (|(frameMatrix T f.1).det| * |(frameMatrix S f.1).det|⁻¹) := by
    rw [Matrix.det_mul, hinv]
    have hεS' : (frameSign S x)⁻¹ = frameSign S x := inv_eq_of_mul_eq_one_right hεS
    conv_lhs => rw [hdT, hdS, mul_inv, hεS']
    ring_nf
  have hP : 0 < |(frameMatrix T f.1).det| * |(frameMatrix S f.1).det|⁻¹ :=
    mul_pos (abs_pos.mpr hT) (inv_pos.mpr (abs_pos.mpr hS))
  rw [hdet, orientMat_det, orientMat_det, hMd]
  have hmain : frameSign T x * (frameSign T x * frameSign S x
      * (|(frameMatrix T f.1).det| * |(frameMatrix S f.1).det|⁻¹)) * frameSign S x
      = |(frameMatrix T f.1).det| * |(frameMatrix S f.1).det|⁻¹ := by
    calc frameSign T x * (frameSign T x * frameSign S x
          * (|(frameMatrix T f.1).det| * |(frameMatrix S f.1).det|⁻¹)) * frameSign S x
        = (frameSign T x * frameSign T x) * (frameSign S x * frameSign S x)
          * (|(frameMatrix T f.1).det| * |(frameMatrix S f.1).det|⁻¹) := by ring
      _ = |(frameMatrix T f.1).det| * |(frameMatrix S f.1).det|⁻¹ := by rw [hεT, hεS]; ring
  rw [hmain]
  exact hP

/-! ## The corrected tautological bundle, and its Thom class -/

/-- **The tautological oriented rank-`k` bundle over `G̃r_k(ℝ^{k+m})`**, with orientation-consistent
trivialisations: the gluing data of `Grassmannian.tautologicalBundleNaive` corrected by the sign
gauge `orientMat`.  This is the bundle whose fibre over an oriented plane is the plane itself; the
only difference from the naive presentation is that the trivialisation over `baseSet S` is composed
with the reflection of the first coordinate when the frame is negatively oriented in the coordinates
`S`, which makes every transition function have positive determinant. -/
noncomputable def tautologicalBundleO (k m : ℕ) :
    Work.TangentClasses.RealBundle (OG k m) (Amb k) (ChartIdx k m) where
  baseSet := baseSet
  isOpen_baseSet := isOpen_baseSet
  indexAt := chartCover
  mem_baseSet_at := mem_baseSet_chartCover
  coordChange := coordChangeO
  coordChange_self := fun S x hx v => coordChangeO_self S x hx v
  continuousOn_coordChange := fun S T => continuousOn_coordChangeO S T
  coordChange_comp := fun i j l x hx v => coordChangeO_comp i j l x hx v

/-- **The tautological oriented rank-`k` bundle over `G̃r_k(ℝ^{k+m})`** — the model's `γ`: the
orientation-consistent presentation `tautologicalBundleO` of the naive gluing data
`Grassmannian.tautologicalBundleNaive` (they differ by the sign gauge `orientMat`, a fibrewise linear
automorphism over the base, so they present the same bundle and have the same total space up to a
homeomorphism over the Grassmannian). -/
abbrev tautologicalBundle (k m : ℕ) :
    Work.TangentClasses.RealBundle (OG k m) (Amb k) (ChartIdx k m) :=
  tautologicalBundleO k m

/-- **The Thom isomorphism theorem for the tautological oriented bundle.**  The tautological bundle
over the oriented Grassmannian is oriented, and every oriented rank-`k` real bundle over a finite
cover carries an integral Thom class (`Work.Thom.thomClass_of_oriented_fintype`); the only input is
the positivity of the transition determinants (`det_coordChangeO_pos`). -/
theorem nonempty_thomClass_tautologicalBundleO (hk : 1 ≤ k) :
    Nonempty (Work.Thom.ThomClass (tautologicalBundleO k m) k) :=
  Work.Thom.thomClass_of_oriented_fintype hk (tautologicalBundleO k m)
    fun i j x => det_coordChangeO_pos i j x.1 x.2

/-! ## The rank-zero case: the Thom class of a bundle with subsingleton fibre -/

/-- **The complement of the zero section of a bundle with a subsingleton fibre is empty.** -/
theorem zeroComplement_of_subsingleton {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Subsingleton F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) : Work.Thom.zeroComplement Z = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr (fun p hp => ?_)
  rw [Work.Thom.mem_zeroComplement] at hp
  exact hp (Subsingleton.elim _ _)

/-- **The forgetful map `H^n(E,∅) → H^n(E)` is bijective.** -/
theorem bijective_relToAbs_empty {E : Type} [TopologicalSpace E] (n : ℕ) :
    Function.Bijective ((Work.Thom.relToAbs ℤ (∅ : Set E) n).hom) := by
  haveI := Work.Cohomology.relComplex_empty_homology_iso (TopCat.of E) n
  exact ConcreteCategory.bijective_of_isIso _

/-- **The Thom class of a bundle with a subsingleton fibre exists.**  In particular every rank-`0`
real bundle has an integral Thom class.  (This is
`Work.Thom.nonempty_thomClass_zero_of_subsingleton`, re-proved here for an arbitrary model fibre
because the module that holds it is in an import island incompatible with the present one.) -/
theorem nonempty_thomClass_zero_of_subsingleton {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Subsingleton F] {ι : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) : Nonempty (Work.Thom.ThomClass Z 0) := by
  have hA : Work.Thom.zeroComplement Z = ∅ := zeroComplement_of_subsingleton Z
  have hrel : ∀ n,
      Function.Bijective ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) n).hom) := by
    intro n
    rw [hA]
    exact bijective_relToAbs_empty n
  let u : Work.Thom.Coh ℤ 0 Z.TotalSpace :=
    Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace))
  obtain ⟨τ, hτ⟩ := (hrel 0).2 u
  refine ⟨⟨τ, fun k => ?_⟩⟩
  have key : ∀ x : Work.Thom.Coh ℤ k B,
      (Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) (k + 0)).hom
          (Work.Thom.thomMap Z 0 τ k x)
        = (Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x := by
    intro x
    rw [Work.Thom.thomMap_apply Z 0 τ k x,
      Work.Thom.mixedCup_relToAbs (Work.Thom.zeroComplement Z) k 0
        ((Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x) τ, hτ]
    exact Work.Cohomology.cupH'_one_right ℤ (TopCat.toSSet.obj (TopCat.of Z.TotalSpace)) k _
  have keyk : ∀ x : Work.Thom.Coh ℤ k B,
      (Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) k).hom
          (Work.Thom.thomMap Z 0 τ k x)
        = (Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x := fun x => key x
  constructor
  · intro x y hxy
    have h3 : (Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom x
        = (Work.Thom.CohMap (Work.Thom.bundleProj Z) ℤ k).hom y := by
      rw [← keyk x, ← keyk y, hxy]
    exact (Work.Thom.bijective_CohMap_bundleProj Z k).1 h3
  · intro z
    obtain ⟨x, hx⟩ := (Work.Thom.bijective_CohMap_bundleProj Z k).2
      ((Work.Thom.relToAbs ℤ (Work.Thom.zeroComplement Z) k).hom z)
    refine ⟨x, ?_⟩
    apply (hrel k).1
    rw [keyk x, hx]

end

end Work.ThomBordism.Grassmann
