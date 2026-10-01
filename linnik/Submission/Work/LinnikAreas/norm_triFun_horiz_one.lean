import Mathlib
import Submission.Work.LinnikAreas.LoneLowerDefs

namespace Work.LinnikAreas

open DirichletCharacter Complex

theorem norm_triFun_horiz_one (CZ : ℝ) (hCZ : 0 < CZ)
    (hZ : ∀ σ t : ℝ, 5 / 8 ≤ σ → σ ≤ 2 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16))
    (hLlog : ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), ψ ≠ 1 → ∀ z : ℂ, 1 ≤ z.re →
      ‖DirichletCharacter.LFunction ψ z‖
        ≤ Real.log (2 * N) + Real.log (2 + |z.im|) + 6)
    {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    {β x t u : ℝ} (hβ : 3 / 4 ≤ β) (hβ1 : β < 1) (hx : 0 < x) (ht : 1 ≤ |t|)
    (hu : 1 - β ≤ u) (hu' : u ≤ 1) :
    ‖Work.LinnikAreas.triFun ψ β x ((u : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16) * (Real.log (2 * N) + Real.log (2 + |t|) + 6) * x ^ u / t ^ 2 := by
  set s : ℂ := (u : ℂ) + (t : ℂ) * Complex.I with hs
  have hre : s.re = u := by rw [hs]; simp
  have him : s.im = t := by rw [hs]; simp
  have him1 : (s + 1).im = t := by rw [hs]; simp
  have hsp : s + (β : ℂ) = ((u + β : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    rw [hs]; push_cast; ring
  -- exponent range for hZ
  have huβ58 : 5 / 8 ≤ u + β := by linarith
  have huβ2 : u + β ≤ 2 := by linarith
  have huβ1 : 1 ≤ u + β := by linarith
  -- positivity of t^2
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have ht2pos : 0 < t ^ 2 := by positivity
  -- bounds
  have hCZnn : 0 ≤ CZ := le_of_lt hCZ
  have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog2N : 0 ≤ Real.log (2 * N) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
    push_cast
    linarith
  have hlog2t : 0 ≤ Real.log (2 + |t|) := by
    apply Real.log_nonneg
    have := abs_nonneg t; linarith
  have hLnn : 0 ≤ Real.log (2 * N) + Real.log (2 + |t|) + 6 := by linarith
  have hbD : 0 ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16) :=
    mul_nonneg hCZnn (Real.rpow_nonneg (by have := abs_nonneg t; linarith) _)
  have hDnn : 0 ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16) * (Real.log (2 * N) + Real.log (2 + |t|) + 6) :=
    mul_nonneg hbD hLnn
  -- zeta bound
  have hZb : ‖riemannZeta (s + (β : ℂ))‖ ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16) := by
    rw [hsp]
    exact hZ (u + β) t huβ58 huβ2 ht
  -- L-function bound
  have hLb : ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
      ≤ Real.log (2 * N) + Real.log (2 + |t|) + 6 := by
    rw [hsp]
    have h := hLlog ψ hψ (((u + β : ℝ) : ℂ) + (t : ℂ) * Complex.I) (by simp; linarith)
    simpa using h
  -- combined zlFun bound
  have hzl : ‖zlFun ψ (s + (β : ℂ))‖
      ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16) * (Real.log (2 * N) + Real.log (2 + |t|) + 6) := by
    rw [zlFun, norm_mul]
    exact mul_le_mul hZb hLb (norm_nonneg _) hbD
  -- norm of the power
  have hxs : ‖(x : ℂ) ^ s‖ = x ^ u := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
  -- denominator lower bound
  have hden : t ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul]
    have h1 : |t| ≤ ‖s‖ := by rw [← him]; exact Complex.abs_im_le_norm s
    have h2 : |t| ≤ ‖s + 1‖ := by rw [← him1]; exact Complex.abs_im_le_norm (s + 1)
    have h3 : |t| * |t| ≤ ‖s‖ * ‖s + 1‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    have : |t| * |t| = t ^ 2 := by rw [← sq_abs]; ring
    linarith
  have hnum_le : ‖zlFun ψ (s + (β : ℂ))‖ * x ^ u
      ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16) * (Real.log (2 * N) + Real.log (2 + |t|) + 6) * x ^ u :=
    mul_le_mul_of_nonneg_right hzl (Real.rpow_nonneg (le_of_lt hx) u)
  rw [triFun]
  have hnum : ‖zlFun ψ (s + (β : ℂ)) * (x : ℂ) ^ s‖
      = ‖zlFun ψ (s + (β : ℂ))‖ * ‖(x : ℂ) ^ s‖ := norm_mul _ _
  rw [norm_div, hnum]
  calc ‖zlFun ψ (s + (β : ℂ))‖ * ‖(x : ℂ) ^ s‖ / ‖s * (s + 1)‖
      = ‖zlFun ψ (s + (β : ℂ))‖ * x ^ u / ‖s * (s + 1)‖ := by rw [hxs]
    _ ≤ (CZ * (1 + |t|) ^ ((7 : ℝ) / 16) * (Real.log (2 * N) + Real.log (2 + |t|) + 6) * x ^ u)
          / ‖s * (s + 1)‖ := div_le_div_of_nonneg_right hnum_le (norm_nonneg _)
    _ ≤ (CZ * (1 + |t|) ^ ((7 : ℝ) / 16) * (Real.log (2 * N) + Real.log (2 + |t|) + 6) * x ^ u)
          / t ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg hDnn (Real.rpow_nonneg (le_of_lt hx) u)) ht2pos hden

end Work.LinnikAreas
