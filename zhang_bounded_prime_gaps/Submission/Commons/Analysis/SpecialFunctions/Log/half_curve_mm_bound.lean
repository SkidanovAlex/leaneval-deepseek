import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Commons.Analysis.SpecialFunctions.Log.convex_combo_log_le

/-!
# Half-curve "mm" bound (Heath-Brown's Linnik exponent 5.5 development)

Auxiliary real-analysis lemma proving, for `0 ≤ t`:

`(1 + 4t²) log (2 + 2t) ≥ 4t(1+t) log (√(t² + 1/4)) + 2(1+t) arctan(2t)`.

The proof goes through the one-variable function
`F(t) = LHS − RHS` (after rewriting `log √x = (1/2) log x`).  We show `F` is convex
on `[0, ∞)` (its second derivative is nonnegative by a rational certificate together
with the harmonic-type lower bound `log y ≥ 2(y−1)/(y+1)`), evaluate the first
derivative at `0` and at `2`, and then use the tangent lower bound together with
monotonicity of the derivative.
-/

noncomputable section
open Real

namespace half_curve_mm_bound

def F (t : ℝ) : ℝ :=
  (1 + 4 * t ^ 2) * Real.log (2 + 2 * t) - 2 * t * (1 + t) * Real.log (t ^ 2 + 1 / 4) -
    2 * (1 + t) * Real.arctan (2 * t)

def Fd1 (t : ℝ) : ℝ :=
  8 * t * Real.log (2 + 2 * t) - 2 * (1 + 2 * t) * Real.log (t ^ 2 + 1 / 4) -
    2 * Real.arctan (2 * t) + (1 + 4 * t ^ 2) / (1 + t) - 4 * (1 + t)

def Fd2 (t : ℝ) : ℝ :=
  8 * Real.log (2 + 2 * t) - 4 * Real.log (t ^ 2 + 1 / 4) - 4 / (1 + 4 * t ^ 2) +
    8 * t / (1 + t) - 4 * t * (1 + 2 * t) / (t ^ 2 + 1 / 4) +
    (4 * t ^ 2 + 8 * t - 1) / (1 + t) ^ 2 - 4

def Xr (t : ℝ) : ℝ := 16 * (1 + t) ^ 2 / (1 + 4 * t ^ 2)

def Qr (t : ℝ) : ℝ :=
  -4 / (1 + 4 * t ^ 2) + 8 * t / (1 + t) - 4 * t * (1 + 2 * t) / (t ^ 2 + 1 / 4) +
    (4 * t ^ 2 + 8 * t - 1) / (1 + t) ^ 2 - 4

def Dp (t : ℝ) : ℝ := (1 + t) ^ 2 * (1 + 4 * t ^ 2) * (8 * t ^ 2 + 8 * t + 5)

def Np (t : ℝ) : ℝ := 128 * t ^ 5 + 416 * t ^ 4 + 496 * t ^ 3 + 352 * t ^ 2 + 40 * t + 21

lemma HasDerivAt.funext' {f g : ℝ → ℝ} {a : ℝ} {x : ℝ} (h : HasDerivAt f a x)
    (hfg : f = g) : HasDerivAt g a x := by
  simpa [hfg] using h

lemma log_affine_deriv (t : ℝ) (ht : 1 + t ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.log (2 + 2 * u)) (1 / (1 + t)) t := by
  have h2 : (2 + 2 * t) ≠ 0 := by
    have : 2 + 2 * t = 2 * (1 + t) := by ring
    rw [this]
    exact mul_ne_zero (by norm_num) ht
  have hg : HasDerivAt (fun u : ℝ => 2 + 2 * u) 2 t := by
    have hh := ((hasDerivAt_id t).const_mul 2).add_const 2
    have hfun : (fun u : ℝ => 2 * id u + 2) = (fun u : ℝ => 2 + 2 * u) := by
      funext u; dsimp; ring
    exact HasDerivAt.funext' (hh.congr_deriv (by norm_num)) hfun
  have hcomp : HasDerivAt (Real.log ∘ fun u : ℝ => 2 + 2 * u) ((2 + 2 * t)⁻¹ * 2) t :=
    (Real.hasDerivAt_log h2).comp t hg
  change HasDerivAt (fun u : ℝ => Real.log (2 + 2 * u)) (1 / (1 + t)) t
  exact hcomp.congr_deriv (by field_simp [h2, ht])

lemma log_sq_quarter_deriv (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.log (u ^ 2 + 1 / 4)) (2 * t / (t ^ 2 + 1 / 4)) t := by
  have hq : t ^ 2 + 1 / 4 ≠ 0 := by positivity
  have hg : HasDerivAt (fun u : ℝ => u ^ 2 + 1 / 4) (2 * t) t := by
    have hh := (hasDerivAt_pow 2 t).add_const (1 / 4)
    have hfun : (fun u : ℝ => u ^ 2 + 1 / 4) = (fun u : ℝ => u ^ 2 + 1 / 4) := rfl
    simpa using hh
  have hcomp : HasDerivAt (Real.log ∘ fun u : ℝ => u ^ 2 + 1 / 4) ((t ^ 2 + 1 / 4)⁻¹ * (2 * t)) t :=
    (Real.hasDerivAt_log hq).comp t hg
  change HasDerivAt (fun u : ℝ => Real.log (u ^ 2 + 1 / 4)) (2 * t / (t ^ 2 + 1 / 4)) t
  exact hcomp.congr_deriv (by ring)

lemma arctan_affine_deriv (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.arctan (2 * u)) (2 / (1 + 4 * t ^ 2)) t := by
  have hg : HasDerivAt (fun u : ℝ => 2 * u) 2 t := by
    have hh := (hasDerivAt_id t).const_mul 2
    have hfun : (fun u : ℝ => 2 * u) = (fun u : ℝ => 2 * u) := rfl
    simpa using hh
  have hcomp : HasDerivAt (Real.arctan ∘ fun u : ℝ => 2 * u) ((1 / (1 + (2 * t) ^ 2)) * 2) t :=
    (Real.hasDerivAt_arctan (2 * t)).comp t hg
  change HasDerivAt (fun u : ℝ => Real.arctan (2 * u)) (2 / (1 + 4 * t ^ 2)) t
  exact hcomp.congr_deriv (by ring)

lemma quad_deriv (t : ℝ) : HasDerivAt (fun u : ℝ => 1 + 4 * u ^ 2) (8 * t) t := by
  have h := (hasDerivAt_pow 2 t).const_mul 4
  have h' : HasDerivAt (fun u : ℝ => 4 * u ^ 2) (8 * t) t := by
    exact h.congr_deriv (by ring)
  have hh := h'.add_const 1
  have hfun : (fun u : ℝ => 4 * u ^ 2 + 1) = (fun u : ℝ => 1 + 4 * u ^ 2) := by
    funext u; ring
  exact HasDerivAt.funext' hh hfun

lemma one_add_deriv (t : ℝ) : HasDerivAt (fun u : ℝ => 1 + u) 1 t := by
  have hh := (hasDerivAt_id t).const_add 1
  have hfun : (fun u : ℝ => 1 + u) = (fun u : ℝ => 1 + u) := rfl
  simpa using hh

lemma two_mul_one_add_deriv (t : ℝ) :
    HasDerivAt (fun u : ℝ => 2 * u * (1 + u)) (2 * (1 + t) + 2 * t * 1) t := by
  have hu : HasDerivAt (fun u : ℝ => 2 * u) 2 t := by
    have hh := (hasDerivAt_id t).const_mul 2
    have hfun : (fun u : ℝ => 2 * u) = (fun u : ℝ => 2 * u) := rfl
    simpa using hh
  have hv : HasDerivAt (fun u : ℝ => 1 + u) 1 t := one_add_deriv t
  have hh := hu.mul hv
  have hfun : (fun u : ℝ => 2 * u) * (fun u : ℝ => 1 + u) = (fun u : ℝ => 2 * u * (1 + u)) := by
    funext u; rfl
  exact HasDerivAt.funext' hh hfun

lemma eight_u_deriv (t : ℝ) : HasDerivAt (fun u : ℝ => 8 * u) 8 t := by
  have hh := (hasDerivAt_id t).const_mul 8
  have hfun : (fun u : ℝ => 8 * u) = (fun u : ℝ => 8 * u) := rfl
  simpa using hh

lemma one_add_two_u_deriv (t : ℝ) : HasDerivAt (fun u : ℝ => 1 + 2 * u) 2 t := by
  have hh := ((hasDerivAt_id t).const_mul 2).add_const 1
  have hfun : (fun u : ℝ => 2 * id u + 1) = (fun u : ℝ => 1 + 2 * u) := by
    funext u; dsimp; ring
  exact HasDerivAt.funext' (hh.congr_deriv (by norm_num)) hfun

lemma two_mul_one_add_two_u_deriv (t : ℝ) :
    HasDerivAt (fun u : ℝ => 2 * (1 + 2 * u)) 4 t := by
  have hh := (one_add_two_u_deriv t).const_mul 2
  have hfun : (fun u : ℝ => 2 * (1 + 2 * u)) = (fun u : ℝ => 2 * (1 + 2 * u)) := rfl
  exact HasDerivAt.funext' (hh.congr_deriv (by norm_num)) hfun

lemma neg_two_arctan_u_deriv (t : ℝ) :
    HasDerivAt (fun u : ℝ => -2 * Real.arctan (2 * u)) (-(2 * (2 / (1 + 4 * t ^ 2)))) t := by
  have hh := (arctan_affine_deriv t).const_mul (-2)
  have hfun : (fun u : ℝ => -2 * Real.arctan (2 * u)) = (fun u : ℝ => -2 * Real.arctan (2 * u)) := rfl
  simpa using hh

lemma quad_over_one_add_deriv (t : ℝ) (ht : 1 + t ≠ 0) :
    HasDerivAt (fun u : ℝ => (1 + 4 * u ^ 2) / (1 + u))
      ((8 * t * (1 + t) - (1 + 4 * t ^ 2) * 1) / (1 + t) ^ 2) t := by
  have hh := (quad_deriv t).div (one_add_deriv t) ht
  have hfun : (fun u : ℝ => 1 + 4 * u ^ 2) / (fun u : ℝ => 1 + u) =
      (fun u : ℝ => (1 + 4 * u ^ 2) / (1 + u)) := by
    funext u; rfl
  exact HasDerivAt.funext' hh hfun

lemma neg_four_one_add_deriv (t : ℝ) : HasDerivAt (fun u : ℝ => -4 * (1 + u)) (-4) t := by
  have hh := (one_add_deriv t).const_mul (-4)
  have hfun : (fun u : ℝ => -4 * (1 + u)) = (fun u : ℝ => -4 * (1 + u)) := rfl
  simpa using hh

lemma hasDerivAt_F (t : ℝ) (ht : 1 + t ≠ 0) : HasDerivAt F (Fd1 t) t := by
  have hA0 := (quad_deriv t).mul (log_affine_deriv t ht)
  have hfunA : (fun u : ℝ => 1 + 4 * u ^ 2) * (fun u : ℝ => Real.log (2 + 2 * u)) =
      (fun u : ℝ => (1 + 4 * u ^ 2) * Real.log (2 + 2 * u)) := by
    funext u; rfl
  have hA : HasDerivAt (fun u : ℝ => (1 + 4 * u ^ 2) * Real.log (2 + 2 * u))
      (8 * t * Real.log (2 + 2 * t) + (1 + 4 * t ^ 2) * (1 / (1 + t))) t :=
    HasDerivAt.funext' hA0 hfunA
  have hB0 := (two_mul_one_add_deriv t).mul (log_sq_quarter_deriv t)
  have hfunB : (fun u : ℝ => 2 * u * (1 + u)) * (fun u : ℝ => Real.log (u ^ 2 + 1 / 4)) =
      (fun u : ℝ => 2 * u * (1 + u) * Real.log (u ^ 2 + 1 / 4)) := by
    funext u; rfl
  have hB : HasDerivAt (fun u : ℝ => 2 * u * (1 + u) * Real.log (u ^ 2 + 1 / 4))
      ((2 * (1 + t) + 2 * t * 1) * Real.log (t ^ 2 + 1 / 4) +
        2 * t * (1 + t) * (2 * t / (t ^ 2 + 1 / 4))) t :=
    HasDerivAt.funext' hB0 hfunB
  have htwo : HasDerivAt (fun u : ℝ => 2 * (1 + u)) 2 t := by
    have hh := (one_add_deriv t).const_mul 2
    have hfun : (fun u : ℝ => 2 * (1 + u)) = (fun u : ℝ => 2 * (1 + u)) := rfl
    simpa using hh
  have hC0 := htwo.mul (arctan_affine_deriv t)
  have hfunC : (fun u : ℝ => 2 * (1 + u)) * (fun u : ℝ => Real.arctan (2 * u)) =
      (fun u : ℝ => 2 * (1 + u) * Real.arctan (2 * u)) := by
    funext u; rfl
  have hC : HasDerivAt (fun u : ℝ => 2 * (1 + u) * Real.arctan (2 * u))
      (2 * Real.arctan (2 * t) + 2 * (1 + t) * (2 / (1 + 4 * t ^ 2))) t :=
    HasDerivAt.funext' hC0 hfunC
  have hAB0 := hA.sub hB
  have hfunAB : (fun u : ℝ => (1 + 4 * u ^ 2) * Real.log (2 + 2 * u)) -
        (fun u : ℝ => 2 * u * (1 + u) * Real.log (u ^ 2 + 1 / 4)) =
      (fun u : ℝ => (1 + 4 * u ^ 2) * Real.log (2 + 2 * u) -
        2 * u * (1 + u) * Real.log (u ^ 2 + 1 / 4)) := by
    funext u; rfl
  have hAB : HasDerivAt (fun u : ℝ => (1 + 4 * u ^ 2) * Real.log (2 + 2 * u) -
        2 * u * (1 + u) * Real.log (u ^ 2 + 1 / 4))
      ((8 * t * Real.log (2 + 2 * t) + (1 + 4 * t ^ 2) * (1 / (1 + t))) -
        ((2 * (1 + t) + 2 * t * 1) * Real.log (t ^ 2 + 1 / 4) +
          2 * t * (1 + t) * (2 * t / (t ^ 2 + 1 / 4)))) t :=
    HasDerivAt.funext' hAB0 hfunAB
  have hABC0 := hAB.sub hC
  have hfunABC : (fun u : ℝ => (1 + 4 * u ^ 2) * Real.log (2 + 2 * u) -
          2 * u * (1 + u) * Real.log (u ^ 2 + 1 / 4)) -
        (fun u : ℝ => 2 * (1 + u) * Real.arctan (2 * u)) =
      (fun u : ℝ => (1 + 4 * u ^ 2) * Real.log (2 + 2 * u) -
        2 * u * (1 + u) * Real.log (u ^ 2 + 1 / 4) - 2 * (1 + u) * Real.arctan (2 * u)) := by
    funext u; rfl
  have hBody : HasDerivAt (fun u : ℝ => (1 + 4 * u ^ 2) * Real.log (2 + 2 * u) -
        2 * u * (1 + u) * Real.log (u ^ 2 + 1 / 4) - 2 * (1 + u) * Real.arctan (2 * u))
      ((8 * t * Real.log (2 + 2 * t) + (1 + 4 * t ^ 2) * (1 / (1 + t))) -
        ((2 * (1 + t) + 2 * t * 1) * Real.log (t ^ 2 + 1 / 4) +
          2 * t * (1 + t) * (2 * t / (t ^ 2 + 1 / 4))) -
        (2 * Real.arctan (2 * t) + 2 * (1 + t) * (2 / (1 + 4 * t ^ 2)))) t :=
    HasDerivAt.funext' hABC0 hfunABC
  have hBody' : HasDerivAt F
      ((8 * t * Real.log (2 + 2 * t) + (1 + 4 * t ^ 2) * (1 / (1 + t))) -
        ((2 * (1 + t) + 2 * t * 1) * Real.log (t ^ 2 + 1 / 4) +
          2 * t * (1 + t) * (2 * t / (t ^ 2 + 1 / 4))) -
        (2 * Real.arctan (2 * t) + 2 * (1 + t) * (2 / (1 + 4 * t ^ 2)))) t := by
    exact HasDerivAt.funext' hBody (by unfold F; funext u; rfl)
  exact hBody'.congr_deriv (by
    unfold Fd1
    field_simp [ht]
    ring)

lemma hasDerivAt_Fd1 (t : ℝ) (ht : 1 + t ≠ 0) : HasDerivAt Fd1 (Fd2 t) t := by
  have h1 := (eight_u_deriv t).mul (log_affine_deriv t ht)
  have hfun1 : (fun u : ℝ => 8 * u) * (fun u : ℝ => Real.log (2 + 2 * u)) =
      (fun u : ℝ => 8 * u * Real.log (2 + 2 * u)) := by
    funext u; rfl
  have hp1 : HasDerivAt (fun u : ℝ => 8 * u * Real.log (2 + 2 * u))
      (8 * Real.log (2 + 2 * t) + 8 * t * (1 / (1 + t))) t :=
    HasDerivAt.funext' h1 hfun1
  have h2 := ((two_mul_one_add_two_u_deriv t).mul (log_sq_quarter_deriv t)).neg
  have hfun2 : -(fun u : ℝ => 2 * (1 + 2 * u) * Real.log (u ^ 2 + 1 / 4)) =
      (fun u : ℝ => -(2 * (1 + 2 * u) * Real.log (u ^ 2 + 1 / 4))) := by
    funext u; rfl
  have hp2 : HasDerivAt (fun u : ℝ => -(2 * (1 + 2 * u) * Real.log (u ^ 2 + 1 / 4)))
      (-(4 * Real.log (t ^ 2 + 1 / 4) + 2 * (1 + 2 * t) * (2 * t / (t ^ 2 + 1 / 4)))) t := by
    refine HasDerivAt.funext' ?_ hfun2
    exact h2.congr_deriv (by ring)
  have hp3 : HasDerivAt (fun u : ℝ => -2 * Real.arctan (2 * u))
      (-(2 * (2 / (1 + 4 * t ^ 2)))) t := neg_two_arctan_u_deriv t
  have hp4 := quad_over_one_add_deriv t ht
  have hp5 := neg_four_one_add_deriv t
  have hSum := (((hp1.add hp2).add hp3).add hp4).add hp5
  have hBody : HasDerivAt Fd1
      ((8 * Real.log (2 + 2 * t) + 8 * t * (1 / (1 + t))) +
        (-(4 * Real.log (t ^ 2 + 1 / 4) + 2 * (1 + 2 * t) * (2 * t / (t ^ 2 + 1 / 4)))) +
        (-(2 * (2 / (1 + 4 * t ^ 2)))) +
        ((8 * t * (1 + t) - (1 + 4 * t ^ 2) * 1) / (1 + t) ^ 2) + (-4)) t := by
    refine HasDerivAt.funext' hSum ?_
    funext u
    dsimp
    unfold Fd1
    ring_nf
  exact hBody.congr_deriv (by
    unfold Fd2
    field_simp [ht]
    ring)

/-- harmonic-type lower bound: for `y ≥ 1`, `log y ≥ 2(y-1)/(y+1)` -/
lemma log_ge_two_div (y : ℝ) (hy : 1 ≤ y) : 2 * (y - 1) / (y + 1) ≤ Real.log y := by
  have hu : 0 ≤ y - 1 := sub_nonneg.mpr hy
  have h := Real.le_log_one_add_of_nonneg hu
  have hden : (y - 1) + 2 = y + 1 := by ring
  have harg : 1 + (y - 1) = y := by ring
  rw [hden, harg] at h
  exact h

lemma log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- for `y ≥ 4` : `4 log y ≥ 8 log 2 + 8 (y-4)/(y+4)` -/
lemma four_log_ge (y : ℝ) (hy : 4 ≤ y) :
    4 * Real.log y ≥ 8 * Real.log 2 + 8 * (y - 4) / (y + 4) := by
  have hyp : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hdiv : 1 ≤ y / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    nlinarith
  have hl := log_ge_two_div (y / 4) hdiv
  have hlogdiv : Real.log y - Real.log 4 = Real.log (y / 4) :=
    (Real.log_div hyp.ne' (by norm_num : (4 : ℝ) ≠ 0)).symm
  calc
    4 * Real.log y = 4 * (Real.log 4 + Real.log (y / 4)) := by rw [← hlogdiv]; ring
    _ = 8 * Real.log 2 + 4 * Real.log (y / 4) := by rw [log_four]; ring
    _ ≥ 8 * Real.log 2 + 4 * (2 * (y / 4 - 1) / (y / 4 + 1)) := by
      have hh := add_le_add_left (mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 4))
        (8 * Real.log 2)
      simpa [add_comm, add_left_comm, add_assoc] using hh
    _ = 8 * Real.log 2 + 8 * (y - 4) / (y + 4) := by
      have h1 : y / 4 - 1 = (y - 4) / 4 := by ring
      have h2 : y / 4 + 1 = (y + 4) / 4 := by ring
      have hny : y ≠ 0 := hyp.ne'
      have hden : y + 4 ≠ 0 := by nlinarith
      have h4 : (4 : ℝ) ≠ 0 := by norm_num
      rw [h1, h2]
      field_simp [hny, hden, h4]
      ring

lemma Xr_ge_four (t : ℝ) (ht : 0 ≤ t) : 4 ≤ Xr t := by
  unfold Xr
  have hd : 0 < 1 + 4 * t ^ 2 := by positivity
  rw [le_div_iff₀ hd]
  nlinarith

lemma R_eq (t : ℝ) : 8 * (Xr t - 4) / (Xr t + 4) = 8 * (3 + 8 * t) / (8 * t ^ 2 + 8 * t + 5) := by
  have hd : (1 + 4 * t ^ 2 : ℝ) ≠ 0 := by positivity
  have hd2 : (8 * t ^ 2 + 8 * t + 5 : ℝ) ≠ 0 := by
    have hpos : 0 < 8 * t ^ 2 + 8 * t + 5 := by
      nlinarith [sq_nonneg (t + 1 / 2)]
    exact ne_of_gt hpos
  have hx4 : Xr t + 4 ≠ 0 := by
    have hXnn : 0 ≤ Xr t := by
      unfold Xr
      apply div_nonneg
      · positivity
      · positivity
    nlinarith
  have hcr : (Xr t - 4) * (8 * t ^ 2 + 8 * t + 5) = (Xr t + 4) * (3 + 8 * t) := by
    unfold Xr
    field_simp [hd]
    ring
  have hdiv : (Xr t - 4) / (Xr t + 4) = (3 + 8 * t) / (8 * t ^ 2 + 8 * t + 5) :=
    (div_eq_div_iff hx4 hd2).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hcr)
  have hmul := congr_arg (fun y : ℝ => 8 * y) hdiv
  simpa [mul_div_assoc] using hmul

lemma rational_id (t : ℝ) (ht : 0 ≤ t) :
    8 * (3 + 8 * t) / (8 * t ^ 2 + 8 * t + 5) + Qr t = -(Np t / Dp t) := by
  have h1 : (1 + t : ℝ) ≠ 0 := by nlinarith
  have h2 : (1 + 4 * t ^ 2 : ℝ) ≠ 0 := by positivity
  have h3 : (t ^ 2 + 1 / 4 : ℝ) ≠ 0 := by positivity
  have h4 : (8 * t ^ 2 + 8 * t + 5 : ℝ) ≠ 0 := by
    have hpos : 0 < 8 * t ^ 2 + 8 * t + 5 := by
      nlinarith [sq_nonneg (t + 1 / 2)]
    exact ne_of_gt hpos
  unfold Qr Np Dp
  field_simp [h1, h2, h3, h4]
  ring

lemma log_comb (t : ℝ) (ht : 0 < 1 + t) :
    8 * Real.log (2 + 2 * t) - 4 * Real.log (t ^ 2 + 1 / 4) =
      4 * Real.log (16 * (1 + t) ^ 2 / (1 + 4 * t ^ 2)) := by
  have hA : (2 + 2 * t) ≠ 0 := by nlinarith
  have hB : t ^ 2 + 1 / 4 ≠ 0 := by positivity
  have hA2 : (2 + 2 * t) ^ 2 ≠ 0 := pow_ne_zero 2 hA
  have harg : (2 + 2 * t) ^ 2 / (t ^ 2 + 1 / 4) = 16 * (1 + t) ^ 2 / (1 + 4 * t ^ 2) := by
    have hd1 : (1 + 4 * t ^ 2 : ℝ) ≠ 0 := by positivity
    field_simp [hB, hd1]
    ring
  calc
    8 * Real.log (2 + 2 * t) - 4 * Real.log (t ^ 2 + 1 / 4)
        = 4 * (2 * Real.log (2 + 2 * t) - Real.log (t ^ 2 + 1 / 4)) := by ring
    _ = 4 * (Real.log ((2 + 2 * t) ^ 2) - Real.log (t ^ 2 + 1 / 4)) := by
      have hsq : (2 : ℝ) * Real.log (2 + 2 * t) = Real.log ((2 + 2 * t) ^ 2) := by
        rw [Real.log_pow]
        norm_num
      rw [← hsq]
    _ = 4 * Real.log ((2 + 2 * t) ^ 2 / (t ^ 2 + 1 / 4)) := by
      rw [Real.log_div hA2 hB]
    _ = 4 * Real.log (16 * (1 + t) ^ 2 / (1 + 4 * t ^ 2)) := by rw [harg]

lemma Fd2_eq (t : ℝ) (ht : 0 ≤ t) : Fd2 t = 4 * Real.log (Xr t) + Qr t := by
  have hc := log_comb t (by nlinarith)
  unfold Fd2 Xr Qr
  rw [hc]
  ring

lemma log_two_lower : (69 / 100 : ℝ) ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

lemma log_two_upper : Real.log 2 ≤ 7 / 10 := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  linarith

lemma log_three_lower : (13 / 12 : ℝ) ≤ Real.log 3 := by
  have hs : HasSum (fun k : ℕ => 2 * (1 / (2 * (k : ℝ) + 1)) * (2 / (2 + 2)) ^ (2 * k + 1))
      (Real.log (1 + 2)) := by
    simpa using (Real.hasSum_log_one_add (a := (2 : ℝ)) (by norm_num))
  have hnonneg : ∀ k : ℕ, 0 ≤ 2 * (1 / (2 * (k : ℝ) + 1)) * (2 / (2 + 2)) ^ (2 * k + 1) := by
    intro k
    positivity
  have hsum := sum_le_hasSum (Finset.range 2) (fun i hi => hnonneg i) hs
  have hval : (∑ k ∈ Finset.range 2, 2 * (1 / (2 * (k : ℝ) + 1)) * (2 / (2 + 2)) ^ (2 * k + 1)) = 13/12 := by
    norm_num [Finset.sum_range_succ]
  rw [hval] at hsum
  rw [show (1 + 2 : ℝ) = 3 by norm_num] at hsum
  exact hsum

lemma log17_16_upper : Real.log (17 / 16) ≤ 1 / 16 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 17 / 16 by norm_num)
  linarith

lemma Q6pos (t : ℝ) (ht : 0 ≤ t) : 0 ≤ (138 / 25) * Dp t - Np t := by
  have hE : (25 : ℝ) * ((138 / 25) * Dp t - Np t) =
      4416 * t ^ 6 + 10048 * t ^ 5 + 6712 * t ^ 4 + 848 * t ^ 3 - 2038 * t ^ 2 +
        1484 * t + 165 := by
    unfold Dp Np
    ring_nf
  have hcase : 0 ≤ (25 : ℝ) * ((138 / 25) * Dp t - Np t) := by
    rw [hE]
    by_cases h1 : 1 ≤ t
    · have ht2 : t ^ 2 ≤ t ^ 3 := by nlinarith [sq_nonneg t, h1]
      have ht3 : t ^ 3 ≤ t ^ 4 := by nlinarith [sq_nonneg t, h1]
      nlinarith
    · have hle1 : t ≤ 1 := le_of_not_ge h1
      by_cases h35 : 3 / 5 ≤ t
      · have hsub : 0 ≤ t - 3 / 5 := sub_nonneg.mpr h35
        have hsum : 0 ≤ t + 3 / 5 := by nlinarith
        have hprod : 0 ≤ (t - 3 / 5) * (t + 3 / 5) := mul_nonneg hsub hsum
        have ht2 : (9 / 25) ≤ t ^ 2 := by nlinarith [hprod]
        have hcoef : (0 : ℝ) ≤ (6712 : ℝ) * (9 / 25) - 2038 := by norm_num
        have hC : 0 ≤ 6712 * t ^ 4 - 2038 * t ^ 2 := by
          have h1' : 0 ≤ (6712 * (9 / 25) - 2038) * t ^ 2 := mul_nonneg hcoef (sq_nonneg t)
          have hprod2 : 0 ≤ (t ^ 2 - 9 / 25) * t ^ 2 := by
            exact mul_nonneg (sub_nonneg.mpr ht2) (sq_nonneg t)
          have h2' : 0 ≤ 6712 * (t ^ 2 - 9 / 25) * t ^ 2 := by
            nlinarith [hprod2]
          nlinarith
        have hR : 0 ≤ 165 + 1484 * t + 848 * t ^ 3 + 4416 * t ^ 6 + 10048 * t ^ 5 := by positivity
        nlinarith
      · have hle : t ≤ 3 / 5 := le_of_not_ge h35
        have hB : 0 ≤ 4416 * t ^ 6 + 10048 * t ^ 5 + 6712 * t ^ 4 + 848 * t ^ 3 := by positivity
        have hC : 0 ≤ 2038 * (3 / 5) * t - 2038 * t ^ 2 := by
          have hm : 0 ≤ (2038 : ℝ) * t * (3 / 5 - t) := by
            exact mul_nonneg (mul_nonneg (by norm_num) ht) (sub_nonneg.mpr hle)
          nlinarith
        have hA : 0 ≤ 165 + (1484 - 2038 * (3 / 5)) * t := by
          have hcoef : (0 : ℝ) ≤ (1484 : ℝ) - (2038 : ℝ) * (3 / 5) := by norm_num
          nlinarith [mul_nonneg hcoef ht]
        nlinarith
  nlinarith [hcase]

lemma Dp_pos (t : ℝ) (ht : 0 < 1 + t) : 0 < Dp t := by
  unfold Dp
  have h1 : 0 < (1 + t) ^ 2 := sq_pos_of_pos ht
  have h2 : 0 < 1 + 4 * t ^ 2 := by positivity
  have h3 : 0 < 8 * t ^ 2 + 8 * t + 5 := by
    nlinarith [sq_nonneg (t + 1 / 2)]
  positivity

lemma Fd2_nonneg (t : ℝ) (ht : 0 < t) : 0 ≤ Fd2 t := by
  have h0 : 0 ≤ t := le_of_lt ht
  rw [Fd2_eq t h0]
  have hx4 : 4 ≤ Xr t := Xr_ge_four t h0
  have hf := four_log_ge (Xr t) hx4
  have hB : (8 * Real.log 2 + 8 * (Xr t - 4) / (Xr t + 4) + Qr t) =
      (8 * Real.log 2 * Dp t - Np t) / Dp t := by
    have hD : Dp t ≠ 0 := (Dp_pos t (by nlinarith)).ne'
    calc
      (8 * Real.log 2 + 8 * (Xr t - 4) / (Xr t + 4) + Qr t)
          = 8 * Real.log 2 + (8 * (Xr t - 4) / (Xr t + 4) + Qr t) := by ring
      _ = 8 * Real.log 2 + (8 * (3 + 8 * t) / (8 * t ^ 2 + 8 * t + 5) + Qr t) := by
        rw [R_eq t]
      _ = 8 * Real.log 2 - Np t / Dp t := by
        rw [rational_id t h0]
        ring
      _ = (8 * Real.log 2 * Dp t - Np t) / Dp t := by
        have hfs : (8 * Real.log 2 * Dp t - Np t) / Dp t = 8 * Real.log 2 - Np t / Dp t := by
          field_simp [hD]
        exact hfs.symm
  have hnum : 0 ≤ 8 * Real.log 2 * Dp t - Np t := by
    have hDnn : 0 ≤ Dp t := (Dp_pos t (by nlinarith)).le
    have hq6 : 0 ≤ (138 / 25) * Dp t - Np t := Q6pos t h0
    have h2a : (8 * (69 / 100 : ℝ)) * Dp t ≤ (8 * Real.log 2) * Dp t := by
      exact mul_le_mul_of_nonneg_right (by nlinarith [log_two_lower]) hDnn
    nlinarith
  have hQ : 0 ≤ (8 * Real.log 2 + 8 * (Xr t - 4) / (Xr t + 4) + Qr t) := by
    rw [hB]
    exact div_nonneg hnum (Dp_pos t (by nlinarith)).le
  have hle : 8 * Real.log 2 + 8 * (Xr t - 4) / (Xr t + 4) + Qr t ≤
      4 * Real.log (Xr t) + Qr t := by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hf (Qr t)
  nlinarith

lemma one_add_pos_of_mem_Ici {x : ℝ} (hx : x ∈ Set.Ici (0 : ℝ)) : 0 < 1 + x := by
  have hx0 : (0 : ℝ) ≤ x := (Set.mem_Ici).1 hx
  nlinarith

lemma convexOn_F : ConvexOn ℝ (Set.Ici (0 : ℝ)) F := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (f := F) (f' := Fd1) (f'' := Fd2) ?_ ?_ ?_ ?_ ?_
  · exact convex_Ici (𝕜 := ℝ) (β := ℝ) (r := (0 : ℝ))
  · intro x hx
    have hc : ContinuousAt F x :=
      (hasDerivAt_F x (ne_of_gt (one_add_pos_of_mem_Ici hx))).continuousAt
    exact hc.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : (0 : ℝ) < x := (Set.mem_Ioi).1 hx
    exact (hasDerivAt_F x (by nlinarith : 1 + x ≠ 0)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : (0 : ℝ) < x := (Set.mem_Ioi).1 hx
    exact (hasDerivAt_Fd1 x (by nlinarith : 1 + x ≠ 0)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact Fd2_nonneg x ((Set.mem_Ioi).1 hx)

lemma F_zero : F 0 = Real.log 2 := by
  unfold F
  simp [Real.arctan_zero]

lemma deriv_F (t : ℝ) (ht : 1 + t ≠ 0) : deriv F t = Fd1 t :=
  (hasDerivAt_F t ht).deriv

lemma Fd1_zero : Fd1 0 = 4 * Real.log 2 - 3 := by
  unfold Fd1
  norm_num
  have hlog : Real.log (1 / 4) = -2 * Real.log 2 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
    rw [Real.log_inv]
    rw [log_four]
    ring
  rw [hlog]
  ring

lemma arctan_four_le_two : Real.arctan 4 ≤ 2 := by
  nlinarith [Real.arctan_lt_pi_div_two (4 : ℝ), Real.pi_lt_four]

lemma Fd1_two_nonneg : 0 ≤ Fd1 2 := by
  have hmain : Fd1 2 = -4 * Real.log 2 + 16 * Real.log 3 - 10 * Real.log (17 / 16) -
      2 * Real.arctan 4 - 19 / 3 := by
    have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
      have hm := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)
      rw [show (6 : ℝ) = 2 * 3 by norm_num]
      exact hm
    have h17 : Real.log (17 / 4) = Real.log (17 / 16) + 2 * Real.log 2 := by
      have hm := Real.log_mul (by norm_num : (17 / 16 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)
      rw [log_four] at hm
      rwa [show (17 / 16 : ℝ) * 4 = 17 / 4 by ring] at hm
    have hmid : Fd1 2 = 16 * Real.log 6 - 10 * Real.log (17 / 4) - 2 * Real.arctan 4 + 17 / 3 - 12 := by
      unfold Fd1
      ring_nf
    rw [hmid, h6, h17]
    ring
  rw [hmain]
  have hlog2hi : Real.log 2 ≤ 7 / 10 := log_two_upper
  have hlog3lo : (13 / 12 : ℝ) ≤ Real.log 3 := log_three_lower
  have hlog17 : Real.log (17 / 16) ≤ 1 / 16 := log17_16_upper
  have hat4 : Real.arctan 4 ≤ 2 := arctan_four_le_two
  nlinarith

/-- F ≥ tangent at 0 : `log 2 + t*(4 log 2 − 3) ≤ F t` for `t ≥ 0`. -/
lemma tangent_bound (t : ℝ) (ht : 0 ≤ t) : Real.log 2 + t * (4 * Real.log 2 - 3) ≤ F t := by
  by_cases hz : t = 0
  · subst t
    simp [F_zero]
  · have h0t : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hld := convexOn_F.le_slope_of_hasDerivAt (hx := by simp) (hy := by simpa using ht)
      (hxy := h0t) (hasDerivAt_F 0 (by norm_num))
    rw [slope_def_field, Fd1_zero, F_zero] at hld
    have ht0 : t - 0 = t := by ring
    rw [ht0] at hld
    have hmul : (4 * Real.log 2 - 3) * t ≤ F t - Real.log 2 := by
      calc
        (4 * Real.log 2 - 3) * t ≤ ((F t - Real.log 2) / t) * t :=
          mul_le_mul_of_nonneg_right hld (le_of_lt h0t)
        _ = F t - Real.log 2 := by field_simp [h0t.ne']
    nlinarith

lemma F_ge_nine_log2_sub_six (t : ℝ) (ht : 0 ≤ t) : 9 * Real.log 2 - 6 ≤ F t := by
  have hder0 : 4 * Real.log 2 - 3 ≤ 0 := by
    nlinarith [log_two_upper]
  have htan := tangent_bound t ht
  by_cases hle : t ≤ 2
  · have hline : Real.log 2 + 2 * (4 * Real.log 2 - 3) ≤ Real.log 2 + t * (4 * Real.log 2 - 3) := by
      have hdiff : 0 ≤ 2 - t := sub_nonneg.mpr hle
      have hprod : (2 - t) * (4 * Real.log 2 - 3) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hdiff hder0
      nlinarith
    have hfin : 9 * Real.log 2 - 6 = Real.log 2 + 2 * (4 * Real.log 2 - 3) := by ring
    nlinarith
  · have hgt : 2 < t := lt_of_not_ge hle
    have hd2ge0 : 0 ≤ deriv F 2 := by
      rw [deriv_F 2 (by norm_num)]
      exact Fd1_two_nonneg
    have hld := convexOn_F.deriv_le_slope (hx := by simp) (hy := by simpa using ht)
      (hxy := hgt) ((hasDerivAt_F 2 (by norm_num)).differentiableAt)
    rw [slope_def_field] at hld
    have hslope0 : 0 ≤ (F t - F 2) / (t - 2) := by
      nlinarith
    have hF : F 2 ≤ F t := by
      have hpos2 : 0 < t - 2 := by nlinarith
      have hq : 0 ≤ ((F t - F 2) / (t - 2)) * (t - 2) :=
        mul_nonneg hslope0 (le_of_lt hpos2)
      have hnn : 0 ≤ F t - F 2 := by
        calc 0 ≤ ((F t - F 2) / (t - 2)) * (t - 2) := hq
             _ = F t - F 2 := by field_simp [ne_of_gt hpos2]
      nlinarith
    have htan2 := tangent_bound 2 (by norm_num)
    have hfin : 9 * Real.log 2 - 6 = Real.log 2 + 2 * (4 * Real.log 2 - 3) := by ring
    nlinarith

/-- `F t ≥ 0` for `0 ≤ t` (the body of the inequality). -/
lemma F_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ F t := by
  have hM : 0 < 9 * Real.log 2 - 6 := by
    have : (9 * (69 / 100) - 6 : ℝ) = 21 / 100 := by norm_num
    nlinarith [log_two_lower]
  nlinarith [F_ge_nine_log2_sub_six t ht]

lemma F_eq_lhs_sub_rhs (t : ℝ) (_ht : 0 ≤ t) :
    F t = (1 + 4 * t ^ 2) * Real.log (2 + 2 * t) -
      4 * t * (1 + t) * Real.log (Real.sqrt (t ^ 2 + 1 / 4)) -
      2 * (1 + t) * Real.arctan (2 * t) := by
  have hlog : Real.log (Real.sqrt (t ^ 2 + 1 / 4)) = (1 / 2) * Real.log (t ^ 2 + 1 / 4) := by
    rw [Real.log_sqrt]
    · ring
    · positivity
  unfold F
  rw [hlog]
  ring

end half_curve_mm_bound

namespace Commons.Analysis.SpecialFunctions.Log

open half_curve_mm_bound

theorem half_curve_mm_bound (t : ℝ) (ht : 0 ≤ t) :
    (1 + 4 * t ^ 2) * Real.log (2 + 2 * t) ≥
      4 * t * (1 + t) * Real.log (Real.sqrt (t ^ 2 + 1 / 4)) + 2 * (1 + t) * Real.arctan (2 * t) := by
  have hF : 0 ≤ F t := F_nonneg t ht
  have hEq := F_eq_lhs_sub_rhs t ht
  nlinarith

end Commons.Analysis.SpecialFunctions.Log