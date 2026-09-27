import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.D2.Basic
import Submission.Work.KT.D2.mZero
import Submission.Work.KT.D2.windLoop_mul
import Submission.Work.KT.D2.windLoop_compl
import Submission.Work.KT.D2.stab_loop_nullhomotopic
import Submission.Work.KT.D2.loop_cone_extend
import Submission.Work.KT.D2.kpairMat_of_boundary_const
import Submission.Work.KT.D2.toCM_injective
import Submission.Work.KT.D2.isUnit_of_forall_isUnit_toCM
import Submission.Work.KT.homInv_cls_eq_of_conj
import Submission.Work.KT.D2.idem_conj_of_rank_eq

/-!
# `Work.KT.D2.Core` — the injectivity of the (rank, winding) invariants

The heart of the dimension-two computation: two idempotent matrices over `Kpair ℝ²` with the same
boundary value and the same winding invariant `Work.KT.D2.mZero` have the same class in `K₀`.

Given trivialising families `U, V` (for `P`) and `W, Z` (for `Q`) at the common boundary value
`e`, the boundary loop of `W * V` is null-homotopic inside the stabiliser of `e` (its block
determinants have winding zero), and extending that null-homotopy over the disc gives a disc
gauge `λ` commuting with `e` with `λ * e * λ⁻¹ = e`.  The unit `G = Z * λ * U` is then equal to
`1` on the boundary circle, so it is an invertible matrix over `Kpair ℝ²` satisfying
`G * P = Q * G`; conjugating the idempotents gives `cls P = cls Q`.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.KT.D2

open Matrix
open Classical

noncomputable section

/-! ## Auxiliary lemmas -/

/-- The reversal of the unit interval. -/
def unitRev (t : unitInterval) : unitInterval := ⟨1 - (t : ℝ), by
  refine ⟨?_, ?_⟩
  · linarith [t.2.2]
  · linarith [t.2.1]⟩

@[simp] lemma unitRev_coe (t : unitInterval) : (unitRev t : ℝ) = 1 - (t : ℝ) := rfl

lemma continuous_unitRev : Continuous unitRev := by
  apply Continuous.subtype_mk
  exact continuous_const.sub continuous_subtype_val

@[simp] lemma unitRev_zero : unitRev 0 = 1 := by
  apply Subtype.ext
  rw [unitRev_coe]
  simp

@[simp] lemma unitRev_one : unitRev 1 = 0 := by
  apply Subtype.ext
  rw [unitRev_coe]
  simp

/-- Equality of winding numbers of loops with the same function but different non-vanishing
proofs. -/
lemma degNZ_congr {f g : C(Sph (Euc 2), ℂ)} (h : f = g) (hf : ∀ x, f x ≠ 0)
    (hg : ∀ x, g x ≠ 0) : degNZ f hf = degNZ g hg := by
  obtain rfl := h
  exact degNZ_proof_irrel f hf hg

/-- Equality of winding numbers of loops of matrices, changing both the idempotent and the loop. -/
lemma windLoop_congr {n : ℕ} {e e' : Matrix (Fin n) (Fin n) ℂ}
    {γ γ' : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)} (he : e = e') (hγ : γ = γ')
    (h : ∀ x, Matrix.det (e * γ x * e + (1 - e)) ≠ 0)
    (h' : ∀ x, Matrix.det (e' * γ' x * e' + (1 - e')) ≠ 0) :
    windLoop n e γ h = windLoop n e' γ' h' := by
  obtain rfl := he
  obtain rfl := hγ
  exact windLoop_proof_irrel e γ h h'

/-- A nowhere-zero loop of matrices whose determinant extends over the disc has winding zero. -/
lemma degNZ_detCM_inBall {n : ℕ} (γ : C(Ball (Euc 2), Matrix (Fin n) (Fin n) ℂ))
    (hγ : ∀ x, Matrix.det (γ x) ≠ 0) :
    degNZ (detCM (γ.comp inBallCM)) (fun x => hγ (inBall x)) = 0 := by
  have h : detCM (γ.comp inBallCM) = (detCMBall γ).comp inBallCM :=
    ContinuousMap.ext (fun x => rfl)
  have hg : ∀ y, (detCMBall γ) y ≠ 0 := fun y => hγ y
  exact (degNZ_congr h (fun x => hγ (inBall x)) (fun x => hg (inBall x))).trans
    (degNZ_comp_inBall (detCMBall γ) hg)

/-- The determinant of a product of two disc families of units has boundary loop of winding
zero. -/
lemma degNZ_detCM_prod {n : ℕ} (γ γ' : C(Ball (Euc 2), Matrix (Fin n) (Fin n) ℂ))
    (hγ : ∀ x, Matrix.det (γ x) ≠ 0) (hγ' : ∀ x, Matrix.det (γ' x) ≠ 0)
    (h : ∀ x, Matrix.det (((γ.comp inBallCM) * (γ'.comp inBallCM)) x) ≠ 0) :
    degNZ (detCM ((γ.comp inBallCM) * (γ'.comp inBallCM))) h = 0 := by
  have hmul : detCM ((γ.comp inBallCM) * (γ'.comp inBallCM))
      = detCM (γ.comp inBallCM) * detCM (γ'.comp inBallCM) := by
    apply ContinuousMap.ext
    intro x
    show Matrix.det (γ (inBall x) * γ' (inBall x))
      = Matrix.det (γ (inBall x)) * Matrix.det (γ' (inBall x))
    rw [Matrix.det_mul]
  have h1 : ∀ x, (detCM (γ.comp inBallCM) * detCM (γ'.comp inBallCM)) x ≠ 0 := by
    intro x
    rw [ContinuousMap.mul_apply]
    exact mul_ne_zero (hγ (inBall x)) (hγ' (inBall x))
  have hA : degNZ (detCM (γ.comp inBallCM)) (fun x => hγ (inBall x)) = 0 :=
    degNZ_detCM_inBall γ hγ
  have hB : degNZ (detCM (γ'.comp inBallCM)) (fun x => hγ' (inBall x)) = 0 :=
    degNZ_detCM_inBall γ' hγ'
  have hAB : degNZ (detCM (γ.comp inBallCM) * detCM (γ'.comp inBallCM)) h1 = 0 := by
    have := degNZ_mul (detCM (γ.comp inBallCM)) (detCM (γ'.comp inBallCM))
      (fun x => hγ (inBall x)) (fun x => hγ' (inBall x)) h1
    rw [hA, hB] at this
    rw [this]
    ring
  exact (degNZ_congr hmul h h1).trans hAB

/-- The winding number of a loop that is constantly `1` vanishes. -/
lemma windLoop_one {n : ℕ} (e : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e)
    (h : ∀ x, Matrix.det (e * (1 : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)) x * e
      + (1 - e)) ≠ 0) :
    windLoop n e (1 : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)) h = 0 := by
  rw [windLoop]
  set F : C(Sph (Euc 2), ℂ) := ⟨fun x => Matrix.det
    (e * (1 : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)) x * e + (1 - e)), by
      have hcont : Continuous fun x : Sph (Euc 2) =>
        e * (1 : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)) x * e + (1 - e) := by fun_prop
      exact hcont.matrix_det⟩ with hF
  have hconst : F = ContinuousMap.const (Sph (Euc 2)) 1 := by
    apply ContinuousMap.ext
    intro x
    show Matrix.det (e * 1 * e + (1 - e)) = 1
    rw [Matrix.mul_one, he]
    have : e + (1 - e) = (1 : Matrix (Fin n) (Fin n) ℂ) := by abel
    rw [this, Matrix.det_one]
  have hne : ∀ x : Sph (Euc 2), (ContinuousMap.const (Sph (Euc 2)) (1 : ℂ)) x ≠ 0 :=
    fun x => one_ne_zero
  exact (degNZ_congr hconst h hne).trans (degNZ_const 1 one_ne_zero)

/-- The winding number of a loop of matrices that is constantly `1` vanishes. -/
lemma windLoop_of_eq_one {n : ℕ} (e : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e)
    {γ : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)} (hγ : γ = 1)
    (h : ∀ x, Matrix.det (e * γ x * e + (1 - e)) ≠ 0) : windLoop n e γ h = 0 := by
  have hconst : ∀ x, Matrix.det (e * (1 : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)) x * e
      + (1 - e)) ≠ 0 := by
    intro x
    rw [← hγ]
    exact h x
  exact (windLoop_congr (rfl : e = e) hγ h hconst).trans (windLoop_one e he hconst)

/-- A matrix over `ℂ` with a right inverse is invertible. -/
lemma isUnitMat_of_mul_eq_one {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ} (h : A * B = 1) :
    IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  intro h0
  rw [h0, zero_mul] at hdet
  exact one_ne_zero hdet.symm


/-! ## The core injectivity statement -/

/-- **Core step.** Idempotent matrices over `Kpair ℝ²` of the same size with the same boundary
value and the same winding invariant are equal in `K₀`. -/
theorem cls_eq_of_boundary_eq {y0 : Ball (Euc 2)} (hy0 : y0 ∈ bdry (Euc 2)) {N : ℕ}
    (P Q : Matrix (Fin N) (Fin N) (Kpair (Euc 2)))
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hb : P.map (augPair (Euc 2) y0).toRingHom = Q.map (augPair (Euc 2) y0).toRingHom)
    (hm : mZero y0 hy0 (⟨N, P⟩ : Mat (Kpair (Euc 2)))
      = mZero y0 hy0 (⟨N, Q⟩ : Mat (Kpair (Euc 2)))) :
    cls (⟨N, P⟩ : Mat (Kpair (Euc 2))) = cls (⟨N, Q⟩ : Mat (Kpair (Euc 2))) := by
  have hbval : bval N y0 P = bval N y0 Q := hb
  have heQ : bval N y0 Q * bval N y0 Q = bval N y0 Q := bval_idem N y0 Q hQ
  -- trivialising families of `P` and of `Q` at the common boundary value
  set U : C(Ball (Euc 2), Matrix (Fin N) (Fin N) ℂ) :=
    trivU y0 (⟨N, P⟩ : Mat (Kpair (Euc 2))) hP with hUdef
  set V : C(Ball (Euc 2), Matrix (Fin N) (Fin N) ℂ) :=
    trivV y0 (⟨N, P⟩ : Mat (Kpair (Euc 2))) hP with hVdef
  set W : C(Ball (Euc 2), Matrix (Fin N) (Fin N) ℂ) :=
    trivU y0 (⟨N, Q⟩ : Mat (Kpair (Euc 2))) hQ with hWdef
  set Z : C(Ball (Euc 2), Matrix (Fin N) (Fin N) ℂ) :=
    trivV y0 (⟨N, Q⟩ : Mat (Kpair (Euc 2))) hQ with hZdef
  have hUV : ∀ x, U x * V x = 1 :=
    (trivU_spec y0 (⟨N, P⟩ : Mat (Kpair (Euc 2))) hP).1
  have hVU : ∀ x, V x * U x = 1 :=
    (trivU_spec y0 (⟨N, P⟩ : Mat (Kpair (Euc 2))) hP).2.1
  have hUP : ∀ x, U x * toCM N P x = bval N y0 P * U x :=
    (trivU_spec y0 (⟨N, P⟩ : Mat (Kpair (Euc 2))) hP).2.2
  have hWZ : ∀ x, W x * Z x = 1 :=
    (trivU_spec y0 (⟨N, Q⟩ : Mat (Kpair (Euc 2))) hQ).1
  have hZW : ∀ x, Z x * W x = 1 :=
    (trivU_spec y0 (⟨N, Q⟩ : Mat (Kpair (Euc 2))) hQ).2.1
  have hWQ : ∀ x, W x * toCM N Q x = bval N y0 Q * W x :=
    (trivU_spec y0 (⟨N, Q⟩ : Mat (Kpair (Euc 2))) hQ).2.2
  -- the inverses commute with the boundary value, at the level of the disc
  have hVP : ∀ x, V x * bval N y0 P = toCM N P x * V x := by
    intro x
    have he : bval N y0 P = U x * toCM N P x * V x := by
      rw [hUP x, Matrix.mul_assoc, hUV x, Matrix.mul_one]
    calc V x * bval N y0 P
        = V x * (U x * toCM N P x * V x) := by rw [he]
      _ = (V x * U x) * toCM N P x * V x := by noncomm_ring
      _ = toCM N P x * V x := by rw [hVU x, Matrix.one_mul]
  have hZQ : ∀ x, toCM N Q x * Z x = Z x * bval N y0 Q := by
    intro x
    calc toCM N Q x * Z x = (Z x * W x) * (toCM N Q x * Z x) := by
          rw [hZW x, Matrix.one_mul]
      _ = Z x * (W x * toCM N Q x) * Z x := by noncomm_ring
      _ = Z x * (bval N y0 Q * W x) * Z x := by rw [hWQ x]
      _ = Z x * bval N y0 Q * (W x * Z x) := by noncomm_ring
      _ = Z x * bval N y0 Q := by rw [hWZ x, Matrix.mul_one]
  -- the boundary loops commute with the common boundary value
  have hUPb : ∀ x : Sph (Euc 2), U (inBall x) * bval N y0 Q = bval N y0 Q * U (inBall x) := by
    intro x
    have h := hUP (inBall x)
    rw [toCM_inBall N P y0 hy0 x, hbval] at h
    exact h
  have hVPb : ∀ x : Sph (Euc 2), V (inBall x) * bval N y0 Q = bval N y0 Q * V (inBall x) := by
    intro x
    have h := hVP (inBall x)
    rw [toCM_inBall N P y0 hy0 x, hbval] at h
    exact h
  have hWQb : ∀ x : Sph (Euc 2), W (inBall x) * bval N y0 Q = bval N y0 Q * W (inBall x) := by
    intro x
    have h := hWQ (inBall x)
    rw [toCM_inBall N Q y0 hy0 x] at h
    exact h
  -- the defect loop `W * V` on the boundary circle
  set f : C(Sph (Euc 2), Matrix (Fin N) (Fin N) ℂ) := (W.comp inBallCM) * (V.comp inBallCM)
    with hfdef
  have hfcomm : ∀ x : Sph (Euc 2), f x * bval N y0 Q = bval N y0 Q * f x := by
    intro x
    show W (inBall x) * V (inBall x) * bval N y0 Q = bval N y0 Q * (W (inBall x) * V (inBall x))
    calc W (inBall x) * V (inBall x) * bval N y0 Q
        = W (inBall x) * (V (inBall x) * bval N y0 Q) := by noncomm_ring
      _ = W (inBall x) * (bval N y0 Q * V (inBall x)) := by rw [hVPb x]
      _ = (W (inBall x) * bval N y0 Q) * V (inBall x) := by noncomm_ring
      _ = (bval N y0 Q * W (inBall x)) * V (inBall x) := by rw [hWQb x]
      _ = bval N y0 Q * (W (inBall x) * V (inBall x)) := by noncomm_ring
  have hfunit : ∀ x, IsUnit (f x) := by
    intro x
    show IsUnit (W (inBall x) * V (inBall x))
    exact (isUnitMat_of_mul_eq_one (hWZ (inBall x))).mul
      (isUnitMat_of_mul_eq_one (hVU (inBall x)))
  -- the various block determinants are nonzero
  have hfdetW : ∀ x : Sph (Euc 2), Matrix.det (bval N y0 Q * W (inBall x) * bval N y0 Q
      + (1 - bval N y0 Q)) ≠ 0 := fun x =>
    blk_det_ne_zero (bval N y0 Q) (W (inBall x)) (Z (inBall x)) heQ (hWQb x)
      (hWZ (inBall x)) (hZW (inBall x))
  have hfdetV : ∀ x : Sph (Euc 2), Matrix.det (bval N y0 Q * V (inBall x) * bval N y0 Q
      + (1 - bval N y0 Q)) ≠ 0 := fun x =>
    blk_det_ne_zero (bval N y0 Q) (V (inBall x)) (U (inBall x)) heQ (hVPb x)
      (hVU (inBall x)) (hUV (inBall x))
  have heQ' : (1 - bval N y0 Q) * (1 - bval N y0 Q) = 1 - bval N y0 Q := by
    rw [sub_mul, one_mul, mul_sub, mul_one, heQ]
    abel
  let finv : Sph (Euc 2) → Matrix (Fin N) (Fin N) ℂ := fun x => ↑((hfunit x).unit)⁻¹
  have hfinv1 : ∀ x, f x * finv x = 1 := fun x => IsUnit.mul_val_inv (hfunit x)
  have hfinv2 : ∀ x, finv x * f x = 1 := fun x => IsUnit.val_inv_mul (hfunit x)
  have hfun1 : ∀ x : Sph (Euc 2), f x * (1 - bval N y0 Q) = (1 - bval N y0 Q) * f x := by
    intro x
    rw [mul_sub, mul_one, hfcomm x, sub_mul, one_mul]
  have hfdet : ∀ x, Matrix.det (bval N y0 Q * f x * bval N y0 Q + (1 - bval N y0 Q)) ≠ 0 :=
    fun x => blk_det_ne_zero (bval N y0 Q) (f x) (finv x) heQ (hfcomm x) (hfinv1 x) (hfinv2 x)
  have hfdet' : ∀ x, Matrix.det ((1 - bval N y0 Q) * f x * (1 - bval N y0 Q)
      + (1 - (1 - bval N y0 Q))) ≠ 0 :=
    fun x => blk_det_ne_zero (1 - bval N y0 Q) (f x) (finv x) heQ' (hfun1 x) (hfinv1 x) (hfinv2 x)
  have hWdetBall : ∀ x : Ball (Euc 2), Matrix.det (W x) ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det (W x)).mp (isUnitMat_of_mul_eq_one (hWZ x))).ne_zero
  have hVdetBall : ∀ x : Ball (Euc 2), Matrix.det (V x) ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det (V x)).mp (isUnitMat_of_mul_eq_one (hVU x))).ne_zero
  have hd : ∀ x : Sph (Euc 2), Matrix.det (f x) ≠ 0 := fun x =>
    ((Matrix.isUnit_iff_isUnit_det (f x)).mp (hfunit x)).ne_zero
  -- the winding of the `Q`- and `P`-loops
  have hWloop : windLoop N (bval N y0 Q) (W.comp inBallCM) hfdetW
      = mZero y0 hy0 (⟨N, Q⟩ : Mat (Kpair (Euc 2))) := by
    rw [mZero_of_idem y0 hy0 (⟨N, Q⟩ : Mat (Kpair (Euc 2))) hQ]
  have hfdetU : ∀ x : Sph (Euc 2), Matrix.det (bval N y0 Q * U (inBall x) * bval N y0 Q
      + (1 - bval N y0 Q)) ≠ 0 := by
    intro x
    have h := trivU_blk_det y0 hy0 (⟨N, P⟩ : Mat (Kpair (Euc 2))) hP x
    rwa [hbval] at h
  have hUloop : windLoop N (bval N y0 Q) (U.comp inBallCM) hfdetU
      = mZero y0 hy0 (⟨N, P⟩ : Mat (Kpair (Euc 2))) := by
    rw [mZero_of_idem y0 hy0 (⟨N, P⟩ : Mat (Kpair (Euc 2))) hP]
    exact windLoop_congr hbval.symm (rfl : U.comp inBallCM = U.comp inBallCM) hfdetU _
  have hcomp : (U.comp inBallCM) * (V.comp inBallCM)
      = (1 : C(Sph (Euc 2), Matrix (Fin N) (Fin N) ℂ)) := by
    apply ContinuousMap.ext
    intro x
    exact hUV (inBall x)
  have hunitAB : ∀ x, Matrix.det (bval N y0 Q * ((U.comp inBallCM) * (V.comp inBallCM)) x
      * bval N y0 Q + (1 - bval N y0 Q)) ≠ 0 := by
    intro x
    have hx : ((U.comp inBallCM) * (V.comp inBallCM)) x = 1 := hUV (inBall x)
    rw [hx, Matrix.mul_one, heQ]
    have : bval N y0 Q + (1 - bval N y0 Q) = (1 : Matrix (Fin N) (Fin N) ℂ) := by abel
    rw [this, Matrix.det_one]
    exact one_ne_zero
  have hVloop : windLoop N (bval N y0 Q) (V.comp inBallCM) hfdetV
      = - mZero y0 hy0 (⟨N, P⟩ : Mat (Kpair (Euc 2))) := by
    have hmul := windLoop_mul N (bval N y0 Q) heQ (U.comp inBallCM) (V.comp inBallCM)
      hUPb hVPb hfdetU hfdetV hunitAB
    have hzero := windLoop_of_eq_one (bval N y0 Q) heQ hcomp hunitAB
    linarith [hmul, hzero, hUloop]
  have hδloop : windLoop N (bval N y0 Q) f hfdet = 0 := by
    have hmul := windLoop_mul N (bval N y0 Q) heQ (W.comp inBallCM) (V.comp inBallCM)
      hWQb hVPb hfdetW hfdetV hfdet
    linarith [hmul, hWloop, hVloop, hm]
  have hδloop' : windLoop N (1 - bval N y0 Q) f hfdet' = 0 := by
    have hcompl := windLoop_compl N (bval N y0 Q) heQ f hfcomm hfdet hfdet' hd
    have hdeg : degNZ (detCM f) hd = 0 := degNZ_detCM_prod W V hWdetBall hVdetBall hd
    linarith [hcompl, hδloop, hdeg]
  -- continuous logarithms of the two block determinants
  have hlog1 : ∃ F : C(Sph (Euc 2), ℂ), ∀ x, Complex.exp (F x)
      = Matrix.det (bval N y0 Q * f x * bval N y0 Q + (1 - bval N y0 Q)) := by
    have h := hδloop
    rw [windLoop] at h
    exact (degNZ_zero_iff _ hfdet).mp h
  have hlog2 : ∃ F : C(Sph (Euc 2), ℂ), ∀ x, Complex.exp (F x)
      = Matrix.det ((1 - bval N y0 Q) * f x * (1 - bval N y0 Q) + bval N y0 Q) := by
    have h := hδloop'
    rw [windLoop] at h
    obtain ⟨F, hF⟩ := (degNZ_zero_iff _ hfdet').mp h
    refine ⟨F, fun x => ?_⟩
    have hx : Complex.exp (F x) = Matrix.det ((1 - bval N y0 Q) * f x * (1 - bval N y0 Q)
        + (1 - (1 - bval N y0 Q))) := hF x
    have hsub : (1 - bval N y0 Q) * f x * (1 - bval N y0 Q) + (1 - (1 - bval N y0 Q))
        = (1 - bval N y0 Q) * f x * (1 - bval N y0 Q) + bval N y0 Q := by
      rw [show (1 : Matrix (Fin N) (Fin N) ℂ) - (1 - bval N y0 Q) = bval N y0 Q from by abel]
    rw [hsub] at hx
    exact hx
  obtain ⟨H, hHunit, hHcomm, hH0, hH1⟩ :=
    stab_loop_nullhomotopic N (bval N y0 Q) heQ f hfunit hfcomm hlog1 hlog2
  -- reverse the homotopy and extend it over the disc
  set F : C(Sph (Euc 2) × unitInterval, Matrix (Fin N) (Fin N) ℂ) :=
    ⟨fun p => H (p.1, unitRev p.2),
      H.continuous.comp (continuous_fst.prodMk (continuous_unitRev.comp continuous_snd))⟩ with hFdef
  have hFunit : ∀ p, IsUnit (F p) := fun p => hHunit _
  have hFzero : ∀ x, F (x, 0) = 1 := by
    intro x
    show H (x, unitRev 0) = 1
    rw [unitRev_zero]
    exact hH1 x
  have hFone : ∀ x, F (x, 1) = f x := by
    intro x
    show H (x, unitRev 1) = f x
    rw [unitRev_one]
    exact hH0 x
  have hFstab : ∀ p, F p * bval N y0 Q = bval N y0 Q * F p := fun p => hHcomm _
  obtain ⟨Λ, hΛunit, hΛ0, hΛcomm, hΛbdry⟩ :=
    loop_cone_extend N (bval N y0 Q) F hFunit hFzero hFstab
  -- the conjugating family
  set G' : C(Ball (Euc 2), Matrix (Fin N) (Fin N) ℂ) := Z * Λ * U with hG'def
  have hG'unit : ∀ y, IsUnit (G' y) := by
    intro y
    show IsUnit (Z y * Λ y * U y)
    exact (isUnitMat_of_mul_eq_one (hZW y)).mul (hΛunit y) |>.mul
      (isUnitMat_of_mul_eq_one (hUV y))
  have hG'const : ∀ y ∈ bdry (Euc 2), G' y = 1 := by
    intro y hy
    set x : Sph (Euc 2) := ⟨y, by rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hy⟩
      with hxdef
    have hinBall : inBall x = y := Subtype.ext rfl
    show Z y * Λ y * U y = 1
    rw [← hinBall, hΛbdry x, hFone x]
    show Z (inBall x) * (W (inBall x) * V (inBall x)) * U (inBall x) = 1
    calc Z (inBall x) * (W (inBall x) * V (inBall x)) * U (inBall x)
        = (Z (inBall x) * W (inBall x)) * (V (inBall x) * U (inBall x)) := by noncomm_ring
      _ = 1 := by rw [hZW (inBall x), hVU (inBall x), Matrix.one_mul]
  obtain ⟨M, hM⟩ := kpairMat_of_boundary_const N G' hG'const
  have hMunit : IsUnit M := isUnit_of_forall_isUnit_toCM N M (fun x => by rw [hM x]; exact hG'unit x)
  have huMspec : ((hMunit.unit : (Matrix (Fin N) (Fin N) (Kpair (Euc 2)))ˣ) :
      Matrix (Fin N) (Fin N) (Kpair (Euc 2))) = M := IsUnit.unit_spec hMunit
  have hpoint : ∀ x : Ball (Euc 2),
      toCM N M x * toCM N P x = toCM N Q x * toCM N M x := by
    intro x
    rw [hM x]
    show Z x * Λ x * U x * toCM N P x = toCM N Q x * (Z x * Λ x * U x)
    calc Z x * Λ x * U x * toCM N P x
        = Z x * Λ x * (U x * toCM N P x) := by noncomm_ring
      _ = Z x * Λ x * (bval N y0 Q * U x) := by rw [hUP x, hbval]
      _ = Z x * (Λ x * bval N y0 Q) * U x := by noncomm_ring
      _ = Z x * (bval N y0 Q * Λ x) * U x := by rw [hΛcomm x]
      _ = Z x * bval N y0 Q * Λ x * U x := by noncomm_ring
      _ = (toCM N Q x * Z x) * Λ x * U x := by rw [hZQ x]
      _ = toCM N Q x * (Z x * Λ x * U x) := by noncomm_ring
  have hmat : ((hMunit.unit : (Matrix (Fin N) (Fin N) (Kpair (Euc 2)))ˣ) :
      Matrix (Fin N) (Fin N) (Kpair (Euc 2))) * P
      = Q * ((hMunit.unit : (Matrix (Fin N) (Fin N) (Kpair (Euc 2)))ˣ) :
        Matrix (Fin N) (Fin N) (Kpair (Euc 2))) := by
    apply toCM_injective N
    intro x
    rw [huMspec, toCM_mul_apply, toCM_mul_apply]
    exact hpoint x
  exact (homInv_cls_eq_of_conj Q P hQ hP hMunit.unit hmat).symm

end

end Work.KT.D2
