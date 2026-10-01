import Mathlib
import Submission.Work.LinnikAreas.LoneLowerDefs

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped BigOperators

noncomputable section

/-- Pointwise bound for `triFun ψ β x` along the horizontal contour segment
`Re s = u ∈ [5/8 - β, 1 - β]`, `Im s = t`, `|t| ≥ 1`.

With `s = u + it` one has `Re (s + β) = u + β ∈ [5/8, 1]`, so the strip bounds for `ζ`
(exponent `7/16`) and for the primitive `L`-function (exponent `1/4`) apply; the triangle
kernel gives `‖s(s+1)‖ ≥ t²` and `‖x^s‖ = x^u`. -/
theorem norm_triFun_horiz_quarter (CZ CL : ℝ) (hCZ : 0 < CZ) (hCL : 0 < CL)
    (hZ : ∀ σ t : ℝ, 5 / 8 ≤ σ → σ ≤ 2 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ CZ * (1 + |t|) ^ ((7 : ℝ) / 16))
    (hL : ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), ψ ≠ 1 → ψ.IsPrimitive →
      ∀ σ T : ℝ, 5 / 8 ≤ σ → σ ≤ 1 →
      ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (T : ℂ) * Complex.I)‖
        ≤ CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |T|) ^ ((1 : ℝ) / 4))
    {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) (hprim : ψ.IsPrimitive)
    {β x t u : ℝ} (hβ : 3 / 4 ≤ β) (hβ1 : β < 1) (hx : 0 < x) (ht : 1 ≤ |t|)
    (hu : 5 / 8 - β ≤ u) (hu' : u ≤ 1 - β) :
    ‖Work.LinnikAreas.triFun ψ β x ((u : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ CZ * CL * (1 + |t|) ^ ((11 : ℝ) / 16) * (N : ℝ) ^ ((1 : ℝ) / 4) * x ^ u / t ^ 2 := by
  set s : ℂ := (u : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = u := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hsplus : s + (β : ℂ) = ((u + β : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
    rw [hs]; push_cast; ring
  have hσlo : 5 / 8 ≤ u + β := by linarith
  have hσhi : u + β ≤ 1 := by linarith
  have htpos : (0 : ℝ) < t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t, ht]
  have hxrpow : ‖(x : ℂ) ^ s‖ = x ^ u := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx s, hsre]
  have h11 : (1 + |t|) ^ ((7 : ℝ) / 16) * (1 + |t|) ^ ((1 : ℝ) / 4)
      = (1 + |t|) ^ ((11 : ℝ) / 16) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + |t|)]
    norm_num
  have hnum : ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
      ≤ CZ * CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((11 : ℝ) / 16) := by
    rw [hsplus]
    calc ‖riemannZeta (((u + β : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          * ‖DirichletCharacter.LFunction ψ (((u + β : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (CZ * (1 + |t|) ^ ((7 : ℝ) / 16))
            * (CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul (hZ (u + β) t hσlo (by linarith) ht)
            (hL ψ hψ hprim (u + β) t hσlo hσhi) (norm_nonneg _)
            (mul_nonneg (le_of_lt hCZ) (Real.rpow_nonneg (by positivity) _))
      _ = CZ * CL * (N : ℝ) ^ ((1 : ℝ) / 4)
            * ((1 + |t|) ^ ((7 : ℝ) / 16) * (1 + |t|) ^ ((1 : ℝ) / 4)) := by ring
      _ = CZ * CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((11 : ℝ) / 16) := by rw [h11]
  have hmain : ‖triFun ψ β x s‖
      = ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
          * ‖(x : ℂ) ^ s‖ / ‖s * (s + 1)‖ := by
    simp only [triFun, zlFun, norm_div, norm_mul]
  have hden : t ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul]
    have hA : |t| ≤ ‖s‖ := by
      have h := abs_im_le_norm s
      rwa [hsim] at h
    have hB : |t| ≤ ‖s + 1‖ := by
      have h := abs_im_le_norm (s + 1)
      have h1 : (s + 1).im = t := by simp [Complex.add_im, hsim]
      rwa [h1] at h
    have hmul := mul_le_mul hA hB (abs_nonneg t) (norm_nonneg s)
    calc t ^ 2 = |t| * |t| := by rw [← sq_abs]; ring
      _ ≤ ‖s‖ * ‖s + 1‖ := hmul
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hxe : (0 : ℝ) ≤ x ^ u := Real.rpow_nonneg (le_of_lt hx) _
  have hnum2 : ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
        * x ^ u
      ≤ CZ * CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((11 : ℝ) / 16) * x ^ u :=
    mul_le_mul_of_nonneg_right hnum hxe
  have hnum2nn : (0 : ℝ) ≤ CZ * CL * (N : ℝ) ^ ((1 : ℝ) / 4)
      * (1 + |t|) ^ ((11 : ℝ) / 16) * x ^ u :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCZ) (le_of_lt hCL)) hN0)
      (Real.rpow_nonneg (by positivity) _)) hxe
  have hstep : ‖riemannZeta (s + (β : ℂ))‖ * ‖DirichletCharacter.LFunction ψ (s + (β : ℂ))‖
        * x ^ u / ‖s * (s + 1)‖
      ≤ (CZ * CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((11 : ℝ) / 16) * x ^ u) / t ^ 2 := by
    refine le_trans (div_le_div_of_nonneg_right hnum2 (norm_nonneg _)) ?_
    exact div_le_div_of_nonneg_left hnum2nn htpos hden
  have heq : CZ * CL * (N : ℝ) ^ ((1 : ℝ) / 4) * (1 + |t|) ^ ((11 : ℝ) / 16) * x ^ u
      = CZ * CL * (1 + |t|) ^ ((11 : ℝ) / 16) * (N : ℝ) ^ ((1 : ℝ) / 4) * x ^ u := by ring
  rw [heq] at hstep
  rw [hmain, hxrpow]
  exact hstep

end

end Work.LinnikAreas
