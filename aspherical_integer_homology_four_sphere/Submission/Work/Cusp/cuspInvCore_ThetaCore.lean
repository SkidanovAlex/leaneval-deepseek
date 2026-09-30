import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.invY_wOf
import Submission.Work.Cusp.bndOfU_uPerim
import Submission.Work.Cusp.bndOfU_add_int
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.nrm_nonneg
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.radial_bounds
import Submission.Work.Cusp.collarHeight_inv
import Submission.Work.Cusp.radial_collar
import Submission.Work.Cusp.beta_add_int

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-! ### Helper lemmas -/

/-- The vector `![w 0, w 1]` is `w`. -/
private lemma cons_wOf (v : Fin 5) (y : E2) :
    (!₂[wOf v y 0, wOf v y 1] : E2) = wOf v y := by
  ext i; fin_cases i <;> rfl

/-- `√((r cos θ)² + (r sin θ)²) = r` for `r ≥ 0`. -/
private lemma sqrt_cos_sin_sq {r θ : ℝ} (hr : 0 ≤ r) :
    Real.sqrt ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) = r := by
  have h : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ
    nlinarith [this]
  rw [h, Real.sqrt_sq_eq_abs, abs_of_nonneg hr]

/-- The argument of the complex number `r(cos θ + i sin θ)`. -/
private lemma argOf_cos_sin {r θ : ℝ} (hr : 0 < r) :
    argOf (r * Real.sin θ) (r * Real.cos θ) = θ + 2 * π * ⌊(π - θ) / (2 * π)⌋ := by
  have hz : (⟨r * Real.cos θ, r * Real.sin θ⟩ : ℂ) =
      (r : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
        Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  have h := Complex.arg_mul_cos_add_sin_mul_I_sub hr θ
  rw [argOf, hz]
  linarith [h]

/-- For nonzero `p`, `bndOfU` inverts the perimeter parameter `u p`. -/
private lemma bndOfU_u_of_ne {p : E2} (hp : p ≠ 0) : bndOfU (u p) = bnd p :=
  bndOfU_uPerim (nrm_bnd hp)

/-- `β` is invariant under translation by an integer multiple of the slope `σ_v`. -/
private lemma beta_add_smul_slope_local (v : Fin 5) (x : E3) (m : ℤ) :
    beta (x + (m : ℝ) • slope v) = beta x := by
  have hslope : slope v = ofInt3
      (fun i => kappa v 0 i + slopeB v * kappa v 1 i + slopeC v * kappa v 2 i) := by
    ext i; fin_cases i <;> simp [slope, kv, ofInt3]
  have hsmul : (m : ℝ) • slope v = ofInt3
      (fun i => m * (kappa v 0 i + slopeB v * kappa v 1 i + slopeC v * kappa v 2 i)) := by
    rw [hslope]
    ext i; fin_cases i <;> simp [ofInt3]
  rw [hsmul, beta_add_int]

/-- If the radial coordinate vanishes then `p = 0`. -/
private lemma radial_eq_zero {v : Fin 5} {p y : E2} (h : radial v p y = 0) : p = 0 := by
  have hrJ : (0 : ℝ) < rJ := by norm_num [rJ]
  by_cases hle : nrm p ≤ 1 / 2
  · rw [radial_eq_inner v p y hle] at h
    have hnp : nrm p = 0 := by nlinarith
    by_contra hp
    exact absurd hnp (ne_of_gt (nrm_pos hp))
  · have hgt : 1 / 2 < nrm p := not_le.mp hle
    have hg := (radial_bounds v p y).2.2 hgt
    rw [h] at hg
    linarith

/-- The inside of `cuspInvInner`'s perimeter coordinate: `u` recovered from `(θ, y)`. -/
private def uuOf (v : Fin 5) (θ : ℝ) (y : E2) : ℝ :=
  (θ - 2 * π * (⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2)) / (2 * π)

/-- The perimeter parameter `uuOf` at the angle of the polar chart, shifted by `2πm`. -/
private lemma uuOf_thetaAng_add (v : Fin 5) (p y : E2) (m : ℤ) :
    uuOf v (thetaAng v p y + 2 * π * (m : ℝ)) y = u p + (m : ℝ) := by
  rw [uuOf, thetaAng]
  field_simp
  ring

/-- The ceiling reached by the recovered perimeter parameter is the original one. -/
private lemma beta_cuspX_thetaAng_add (v : Fin 5) (p y : E2) (m : ℤ) :
    beta (cuspX v (uuOf v (thetaAng v p y + 2 * π * (m : ℝ)) y) y)
      = beta (cuspX v (u p) y) := by
  rw [uuOf_thetaAng_add]
  have hcx : cuspX v (u p + (m : ℝ)) y = cuspX v (u p) y + (m : ℝ) • slope v := by
    simp only [cuspX, add_smul]
    abel
  rw [hcx, beta_add_smul_slope_local]

/-- The layer parameter recovered in `cuspInvInner` equals `‖p‖∞`. -/
private lemma ifval (v : Fin 5) (p y : E2) :
    (if radial v p y ≤ rJ then radial v p y / (2 * rJ)
      else 1 + (R0 - radial v p y - Real.log (beta (cuspX v (u p) y))) /
              (2 * (Real.log (beta (cuspX v (u p) y)) - Real.log sJ))) = nrm p := by
  by_cases hb : radial v p y ≤ rJ
  · rw [ite_eq_left hb]
    have hle : nrm p ≤ 1 / 2 := by
      by_contra hcon
      have hgt : 1 / 2 < nrm p := not_le.mp hcon
      have := radial_gt_rJ v p y hgt
      linarith
    rw [radial_eq_inner v p y hle]
    have hrJ : rJ ≠ 0 := by norm_num [rJ]
    field_simp
  · rw [ite_eq_right hb]
    have hgt : 1 / 2 < nrm p := by
      by_contra hcon
      have hle : nrm p ≤ 1 / 2 := not_lt.mp hcon
      have h1 := radial_eq_inner v p y hle
      have h2 := (radial_bounds v p y).2.1 hle
      linarith
    have hb0 : 0 < beta (cuspX v (u p) y) := beta_pos _
    have hbs : beta (cuspX v (u p) y) ≠ sJ :=
      ne_of_lt (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ)
    have hrc : radial v p y = R0 - Real.log (collarS v p y) :=
      radial_collar v p y (le_of_lt hgt)
    have hinv := collarHeight_inv (nrm p) (beta (cuspX v (u p) y)) (collarS v p y) hb0 hbs rfl
    have hexp : R0 - radial v p y = Real.log (collarS v p y) := by rw [hrc]; ring
    rw [hexp, hinv]

/-- `cuspInvCore` on a Cartesian core point `(r cos θ, r sin θ, w)` is `cuspInvInner` on the
polar coordinates `(r, θ + 2π⌊(π−θ)/2π⌋, w)`. -/
private lemma cuspInvCore_cons (v : Fin 5) (y : E2) {r θ : ℝ} (hr : 0 < r) :
    cuspInvCore v (!₂[r * Real.cos θ, r * Real.sin θ, wOf v y 0, wOf v y 1] : E4)
      = cuspInvInner v (!₂[r, θ + 2 * π * ⌊(π - θ) / (2 * π)⌋, wOf v y 0, wOf v y 1] : E4) := by
  simp only [cuspInvCore, Matrix.cons_val_zero]
  congr 1
  ext i
  fin_cases i <;> simp [sqrt_cos_sin_sq (le_of_lt hr), argOf_cos_sin hr]

/-- The unfolding of `cuspInvInner` on the inner chart of `(p, y)`. -/
private lemma cuspInvInner_cons (v : Fin 5) (y : E2) (r θ : ℝ) :
    cuspInvInner v (!₂[r, θ, wOf v y 0, wOf v y 1] : E4) =
      ((if r ≤ rJ then r / (2 * rJ)
        else 1 + (R0 - r - Real.log (beta (cuspX v (uuOf v θ y) y))) /
                (2 * (Real.log (beta (cuspX v (uuOf v θ y) y)) - Real.log sJ))) •
        bndOfU (uuOf v θ y), y) := by
  simp [cuspInvInner, uuOf, cons_wOf, invY_wOf]

theorem cuspInvCore_ThetaCore (v : Fin 5) (p y : E2) :
    cuspInvCore v (ThetaCore v p y) = (p, y) := by
  by_cases hp : p = 0
  · subst hp
    have hT : ThetaCore v 0 y = (!₂[0, 0, wOf v y 0, wOf v y 1] : E4) := by
      simp [ThetaCore, radial, nrm]
    have hC : cuspInvCore v (!₂[0, 0, wOf v y 0, wOf v y 1] : E4) =
        cuspInvInner v (!₂[0, 0, wOf v y 0, wOf v y 1] : E4) := by
      simp only [cuspInvCore, Matrix.cons_val_zero]
      congr 1
      ext i
      fin_cases i <;> first
        | exact Complex.arg_zero
        | simp [argOf, Matrix.cons_val_zero]
    rw [hT, hC, cuspInvInner_cons v y 0 0]
    simp [rJ]
  · have hrpos : 0 < radial v p y := by
      have hne : radial v p y ≠ 0 := fun h => hp (radial_eq_zero h)
      exact lt_of_le_of_ne (radial_bounds v p y).1 (Ne.symm hne)
    have hTheta : ThetaCore v p y =
        (!₂[radial v p y * Real.cos (thetaAng v p y), radial v p y * Real.sin (thetaAng v p y),
           wOf v y 0, wOf v y 1] : E4) := by simp [ThetaCore]
    rw [hTheta, cuspInvCore_cons v y hrpos, cuspInvInner_cons]
    rw [beta_cuspX_thetaAng_add v p y ⌊(π - thetaAng v p y) / (2 * π)⌋]
    rw [ifval v p y]
    rw [uuOf_thetaAng_add v p y ⌊(π - thetaAng v p y) / (2 * π)⌋]
    rw [bndOfU_add_int, bndOfU_u_of_ne hp]
    exact Prod.ext (smul_bnd p) rfl

end Work.Cusp
