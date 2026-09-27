import Mathlib
import Submission.Work.KT.D2.mZeroH_defs

namespace Work.KT.D2

open Matrix

noncomputable section

/-!
# `Work.KT.D2.mZeroH_wind_sum_zero` — the two Bott trivialisations have opposite windings

`mZeroH_U y0` and `mZeroH_V y0` are mutually inverse families of units on the disc trivialising the
disc-model Hopf idempotent `PA` to its boundary value `e0M`.  Their boundary loops are therefore
pointwise inverse to one another, and the winding of a loop of units at `e0M` is additive under the
pointwise product (`Work.KT.D2.windLoop_mul`).  Since the product of the two boundary loops is the
constant loop `1`, whose winding vanishes, the two windings sum to `0`.
-/

/-! ## Auxiliary winding facts -/

/-- Equality of winding numbers of complex loops which are equal as continuous maps. -/
lemma degNZ_congr' {f g : C(Sph (Euc 2), ℂ)} (h : f = g) (hf : ∀ x, f x ≠ 0)
    (hg : ∀ x, g x ≠ 0) : degNZ f hf = degNZ g hg := by
  subst h
  exact degNZ_proof_irrel f hf hg

/-- Equality of winding numbers of matrix loops which are equal as continuous maps. -/
lemma windLoop_congr' {n : ℕ} {e : Matrix (Fin n) (Fin n) ℂ}
    {γ γ' : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)} (hγ : γ = γ')
    (h : ∀ x, Matrix.det (e * γ x * e + (1 - e)) ≠ 0)
    (h' : ∀ x, Matrix.det (e * γ' x * e + (1 - e)) ≠ 0) :
    windLoop n e γ h = windLoop n e γ' h' := by
  subst hγ
  exact windLoop_proof_irrel e γ h h'

/-- The constant loop of units `1` has zero winding at any idempotent. -/
lemma windLoop_const_one {n : ℕ} (e : Matrix (Fin n) (Fin n) ℂ) (he : e * e = e)
    (h : ∀ x, Matrix.det (e * (1 : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)) x * e
      + (1 - e)) ≠ 0) :
    windLoop n e (1 : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)) h = 0 := by
  rw [windLoop_eq_degNZ]
  have hconst : wlmDet n e (1 : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ))
      = ContinuousMap.const (Sph (Euc 2)) (1 : ℂ) := by
    apply ContinuousMap.ext
    intro x
    show Matrix.det (e * (1 : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)) x * e
      + (1 - e)) = 1
    rw [show (1 : C(Sph (Euc 2), Matrix (Fin n) (Fin n) ℂ)) x = 1 from rfl,
      Matrix.mul_one, he]
    rw [show e + (1 - e) = (1 : Matrix (Fin n) (Fin n) ℂ) from by abel, Matrix.det_one]
  exact (degNZ_congr' hconst h (fun _ => one_ne_zero)).trans (degNZ_const 1 one_ne_zero)

/-! ## The two trivialising families of the Bott class -/

/-- The companion inverse family `mZeroH_V` commutes with `e0M` on the boundary circle (because
`mZeroH_U` does and `mZeroH_V` is its two-sided inverse). -/
lemma mZeroH_V_comm (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) (x : Sph (Euc 2)) :
    mZeroH_V y0 (inBall x) * e0M = e0M * mZeroH_V y0 (inBall x) := by
  calc mZeroH_V y0 (inBall x) * e0M
      = mZeroH_V y0 (inBall x) * e0M
          * (mZeroH_U y0 (inBall x) * mZeroH_V y0 (inBall x)) := by
          rw [mZeroH_U_mul_V y0 (inBall x), Matrix.mul_one]
    _ = mZeroH_V y0 (inBall x) * (e0M * mZeroH_U y0 (inBall x)) * mZeroH_V y0 (inBall x) := by
          noncomm_ring
    _ = mZeroH_V y0 (inBall x) * (mZeroH_U y0 (inBall x) * e0M) * mZeroH_V y0 (inBall x) := by
          rw [mZeroH_U_comm y0 hy0 x]
    _ = (mZeroH_V y0 (inBall x) * mZeroH_U y0 (inBall x)) * e0M * mZeroH_V y0 (inBall x) := by
          noncomm_ring
    _ = e0M * mZeroH_V y0 (inBall x) := by
          rw [mZeroH_V_mul_U y0 (inBall x), Matrix.one_mul]

/-- The pointwise product of the two boundary loops of the Bott trivialisations is the constant
loop `1`. -/
lemma mZeroH_UV_eq_one (y0 : Ball (Euc 2)) :
    (mZeroH_U y0).comp inBallCM * (mZeroH_V y0).comp inBallCM
      = (1 : C(Sph (Euc 2), Matrix (Fin 2) (Fin 2) ℂ)) := by
  apply ContinuousMap.ext
  intro x
  show mZeroH_U y0 (inBall x) * mZeroH_V y0 (inBall x) = 1
  exact mZeroH_U_mul_V y0 (inBall x)

/-! ## The main statement -/

theorem mZeroH_wind_sum_zero (y0 : Work.KT.Ball (EuclideanSpace ℝ (Fin 2)))
    (hy0 : y0 ∈ Work.KT.bdry (EuclideanSpace ℝ (Fin 2)))
    (hu : ∀ x, Matrix.det (Work.KT.D2.e0M * ((Work.KT.D2.mZeroH_U y0).comp Work.KT.D2.inBallCM) x
        * Work.KT.D2.e0M + (1 - Work.KT.D2.e0M)) ≠ 0)
    (hv : ∀ x, Matrix.det (Work.KT.D2.e0M * ((Work.KT.D2.mZeroH_V y0).comp Work.KT.D2.inBallCM) x
        * Work.KT.D2.e0M + (1 - Work.KT.D2.e0M)) ≠ 0) :
    Work.KT.D2.windLoop 2 Work.KT.D2.e0M ((Work.KT.D2.mZeroH_U y0).comp Work.KT.D2.inBallCM) hu
      + Work.KT.D2.windLoop 2 Work.KT.D2.e0M ((Work.KT.D2.mZeroH_V y0).comp Work.KT.D2.inBallCM) hv
      = 0 := by
  have he : e0M * e0M = e0M := e0M_idem
  have hγU : ∀ x, ((mZeroH_U y0).comp inBallCM) x * e0M = e0M * ((mZeroH_U y0).comp inBallCM) x :=
    fun x => mZeroH_U_comm y0 hy0 x
  have hγV : ∀ x, ((mZeroH_V y0).comp inBallCM) x * e0M = e0M * ((mZeroH_V y0).comp inBallCM) x :=
    fun x => mZeroH_V_comm y0 hy0 x
  have hprod : (mZeroH_U y0).comp inBallCM * (mZeroH_V y0).comp inBallCM
      = (1 : C(Sph (Euc 2), Matrix (Fin 2) (Fin 2) ℂ)) := mZeroH_UV_eq_one y0
  -- The product loop has nowhere-vanishing block determinant.
  have h2 : ∀ x, Matrix.det (e0M * (((mZeroH_U y0).comp inBallCM)
      * ((mZeroH_V y0).comp inBallCM)) x * e0M + (1 - e0M)) ≠ 0 := by
    intro x
    have hx : (((mZeroH_U y0).comp inBallCM) * ((mZeroH_V y0).comp inBallCM)) x = 1 := by
      rw [hprod]; rfl
    rw [hx, Matrix.mul_one, e0M_idem]
    rw [show e0M + (1 - e0M) = (1 : Matrix (Fin 2) (Fin 2) ℂ) from by abel, Matrix.det_one]
    exact one_ne_zero
  -- Non-vanishing for the constant loop `1`.
  have h1 : ∀ x, Matrix.det (e0M * (1 : C(Sph (Euc 2), Matrix (Fin 2) (Fin 2) ℂ)) x * e0M
      + (1 - e0M)) ≠ 0 := by
    intro x
    rw [show (1 : C(Sph (Euc 2), Matrix (Fin 2) (Fin 2) ℂ)) x = 1 from rfl,
      Matrix.mul_one, e0M_idem]
    rw [show e0M + (1 - e0M) = (1 : Matrix (Fin 2) (Fin 2) ℂ) from by abel, Matrix.det_one]
    exact one_ne_zero
  -- Additivity of the winding under the pointwise product.
  have hmul := windLoop_mul 2 e0M he ((mZeroH_U y0).comp inBallCM) ((mZeroH_V y0).comp inBallCM)
    hγU hγV hu hv h2
  -- The product loop is the constant loop `1`, so its winding vanishes.
  have hzero : windLoop 2 e0M (((mZeroH_U y0).comp inBallCM)
      * ((mZeroH_V y0).comp inBallCM)) h2 = 0 :=
    (windLoop_congr' hprod h2 h1).trans (windLoop_const_one e0M he h1)
  rw [← hmul, hzero]

end

end Work.KT.D2
