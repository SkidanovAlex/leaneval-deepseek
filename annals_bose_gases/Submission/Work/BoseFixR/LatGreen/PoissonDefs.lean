import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.LatGreen.Theta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.PoissonDefs` — the one-dimensional heat kernel, the coordinate
splitting `(Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ`, and the Fourier terms of the torus heat kernel.

This is the vocabulary layer for `Work.BoseFixR.LatGreen.PoissonTheta`, the Poisson/Jacobi
summation identity

`Σ_{n ∈ ℤ³} p_t(u − n) = Σ_{k ∈ ℤ³} exp(−4π²t‖k‖²) cos(2π k·u)`

on the unit torus `ℝ³/ℤ³`.

The three-dimensional heat kernel `heatK3` factorises into the product of three copies of the
one-dimensional kernel `heatK1`, so the `ℤ³`-sum of `PoissonTheta` is a triple sum of products of
one-dimensional sums; the coordinate splitting `piFinThreeEquiv` turns the `ℤ³`-indexed sum into
that triple sum.  The *terms* of the Fourier series are `thetaTerm1` (one dimension) and
`thetaTerm` (three dimensions).
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory Set

namespace Work.BoseFixR.LatGreen

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The heat kernel of `∂_t = ∂_x²` on `ℝ`, normalised so that `∫_ℝ heatK1 t = 1`. -/
noncomputable def heatK1 (t : ℝ) (x : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-(x ^ 2) / (4 * t))

lemma heatK1_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ heatK1 t x := by
  unfold heatK1
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_nonneg _)

lemma heatK1_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatK1 t x := by
  unfold heatK1
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

/-- The three-dimensional heat kernel is the product of the three one-dimensional ones. -/
lemma heatK3_eq_prod_heatK1 {t : ℝ} (ht : 0 < t) (x : ℝ³) :
    heatK3 t x = heatK1 t (x 0) * heatK1 t (x 1) * heatK1 t (x 2) := by
  have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hsq : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_three]
  unfold heatK3 heatK1
  rw [hsq]
  have e1 : -(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / (4 * t) =
      -(x 0 ^ 2) / (4 * t) + (-(x 1 ^ 2) / (4 * t) + -(x 2 ^ 2) / (4 * t)) := by ring
  rw [e1, Real.exp_add, Real.exp_add]
  have e2 : (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) =
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
        ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * (4 * Real.pi * t) ^ (-(1 / 2 : ℝ))) := by
    rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]
    norm_num
  rw [e2]; ring

/-- The coordinate-splitting equivalence `(Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ`, sending `k ↦ (k 0, k 1, k 2)`. -/
def piFinThreeEquiv : (Fin 3 → ℤ) ≃ ℤ × ℤ × ℤ where
  toFun k := (k 0, k 1, k 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv p := by obtain ⟨a, b, c⟩ := p; rfl

@[simp] lemma piFinThreeEquiv_apply (k : Fin 3 → ℤ) :
    piFinThreeEquiv k = (k 0, k 1, k 2) := rfl

@[simp] lemma piFinThreeEquiv_symm_zero (p : ℤ × ℤ × ℤ) :
    piFinThreeEquiv.symm p 0 = p.1 := rfl

@[simp] lemma piFinThreeEquiv_symm_one (p : ℤ × ℤ × ℤ) :
    piFinThreeEquiv.symm p 1 = p.2.1 := rfl

@[simp] lemma piFinThreeEquiv_symm_two (p : ℤ × ℤ × ℤ) :
    piFinThreeEquiv.symm p 2 = p.2.2 := rfl

/-- The squared norm of `latVec k` is the sum of the squares of the coordinates. -/
lemma latVec_norm_sq (k : Fin 3 → ℤ) :
    ‖latVec k‖ ^ 2 = (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three, latVec]

@[simp] lemma sub_latVec_apply (u : ℝ³) (n : Fin 3 → ℤ) (i : Fin 3) :
    (u - latVec n) i = u i - (n i : ℝ) := by
  simp [latVec]

/-- Gaussian sums over `ℤ` converge. -/
lemma summable_exp_neg_mul_sq_int {c : ℝ} (hc : 0 < c) :
    Summable fun k : ℤ => Real.exp (-c * (k : ℝ) ^ 2) := by
  have hle : ∀ n : ℕ, n ≤ n ^ 2 := by
    intro n
    calc n ≤ n * n := Nat.le_mul_self n
      _ = n ^ 2 := by ring
  have h : Summable fun n : ℕ => Real.exp (-c * (n : ℝ) ^ 2) := by
    have h2 := Real.summable_exp_nat_mul_of_ge (c := -c) (by linarith) (f := fun n : ℕ => n ^ 2)
      (fun n => by exact_mod_cast hle n)
    simpa [Nat.cast_pow] using h2
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨h, by simpa [Int.cast_neg, neg_sq] using h⟩

/-- The `m`-th term of the Fourier series of the heat kernel on the unit circle `ℝ/ℤ`, evaluated
at `x`: `exp(−4π²t m²) e^{−2πi m x}`. -/
noncomputable def thetaTerm1 (t : ℝ) (x : ℝ) (m : ℤ) : ℂ :=
  (Real.exp (-(4 * Real.pi ^ 2 * t) * (m : ℝ) ^ 2) : ℂ)
    * Complex.exp (-(2 * Real.pi * Complex.I * ((m : ℝ) * x)))

/-- The `k`-th term of the Fourier series of the heat kernel on the unit torus `ℝ³/ℤ³`, evaluated
at `u`: `exp(−4π²t‖k‖²) e^{−2πi k·u}`. -/
noncomputable def thetaTerm (t : ℝ) (u : ℝ³) (k : Fin 3 → ℤ) : ℂ :=
  (Real.exp (-(4 * Real.pi ^ 2 * t) * ‖latVec k‖ ^ 2) : ℂ)
    * Complex.exp (-(2 * Real.pi * Complex.I * (((∑ i, (k i : ℝ) * u i) : ℝ) : ℂ)))

end Work.BoseFixR.LatGreen
