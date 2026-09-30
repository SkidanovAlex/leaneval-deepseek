import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_Gamma_le_norm_Gamma_re

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex
open scoped Real
set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

lemma cosh_le_exp_of_nonneg (x : ℝ) (hx : 0 ≤ x) : Real.cosh x ≤ rexp x := by
  rw [Real.cosh_eq]
  have h' : rexp (-x) ≤ rexp x := by
    exact Real.exp_le_exp.mpr (by linarith)
  nlinarith

/-- `‖sin z‖ ≤ exp |z.im|` for all complex `z`. -/
lemma norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ rexp |z.im| := by
  have h1 : ‖Complex.sin z‖ ≤ Real.cosh z.im := by
    have hzI_re : (z * Complex.I).re = -z.im := by
      rw [Complex.mul_re]; simp
    have hnzI_re : ((-z) * Complex.I).re = z.im := by
      rw [Complex.mul_re]; simp
    have h2norm : ‖(2 : ℂ)‖ = (2 : ℝ) := by
      exact Complex.norm_of_nonneg (by norm_num)
    calc
      ‖Complex.sin z‖ = ‖(cexp (-z * Complex.I) - cexp (z * Complex.I)) * Complex.I / (2 : ℂ)‖ := by
        simp [Complex.sin]
      _ = ‖cexp (-z * Complex.I) - cexp (z * Complex.I)‖ / (2 : ℝ) := by
        rw [norm_div, norm_mul, norm_I, h2norm, mul_one]
      _ ≤ (‖cexp (-z * Complex.I)‖ + ‖cexp (z * Complex.I)‖) / (2 : ℝ) := by
        exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num : (0 : ℝ) ≤ 2)
      _ = Real.cosh z.im := by
        rw [Complex.norm_exp, Complex.norm_exp, hnzI_re, hzI_re]
        rw [Real.cosh_eq]
  have h2 : Real.cosh z.im ≤ rexp |z.im| := by
    rw [← Real.cosh_abs z.im]
    exact cosh_le_exp_of_nonneg |z.im| (abs_nonneg z.im)
  exact le_trans h1 h2

/-- The complex sine does not vanish at arguments with nonzero imaginary part. -/
lemma sin_ne_zero_of_im_ne_zero {θ : ℂ} (h : θ.im ≠ 0) : Complex.sin θ ≠ 0 := by
  intro hs
  rw [Complex.sin_eq_zero_iff] at hs
  rcases hs with ⟨k, hk⟩
  apply h
  rw [hk]
  simp

/-- Norm version of Euler's reflection formula: `‖Γ(z)Γ(1-z)‖ = π / ‖sin(πz)‖`. -/
lemma Gamma_mul_Gamma_one_sub_norm (z : ℂ) :
    ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
  have h := congrArg norm (Complex.Gamma_mul_Gamma_one_sub z)
  rw [norm_mul] at h
  rw [norm_div] at h
  rw [Complex.norm_of_nonneg (le_of_lt Real.pi_pos)] at h
  simpa using h

/-- `Γ` is decreasing on `[1/2, 1]`, so `Γ x ≤ Γ(1/2)` there. -/
lemma Gamma_le_Gamma_half_of_mem {x : ℝ} (hxhalf : (1 / 2 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    Real.Gamma x ≤ Real.Gamma (1 / 2) := by
  have hm1 : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hmx : x ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor <;> linarith
  simpa using (Real.Gamma_strictAntiOn_Ioc.antitoneOn hm1 hmx hxhalf)

/-- On `[1, 3/2]` the Gamma function is bounded by `3/4 Γ(1/2)`. -/
lemma Gamma_le_three_quarters_Gamma_half {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 3 / 2) :
    Real.Gamma x ≤ (3 / 4) * Real.Gamma (1 / 2) := by
  have hxpos : 0 < x := by positivity
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have h2le : (2 : ℝ) ≤ x + 1 := by linarith
  have hx1le : x + 1 ≤ 5 / 2 := by linarith
  have hx1mem : x + 1 ∈ Set.Ici (2 : ℝ) := by simpa [Set.mem_Ici] using h2le
  have h52mem : (5 / 2 : ℝ) ∈ Set.Ici (2 : ℝ) := by norm_num [Set.mem_Ici]
  have hmono : Real.Gamma (x + 1) ≤ Real.Gamma (5 / 2) := by
    simpa using (Real.Gamma_strictMonoOn_Ici.monotoneOn hx1mem h52mem hx1le)
  have h32 : Real.Gamma (3 / 2) = (1 / 2) * Real.Gamma (1 / 2) := by
    have hne : (1 / 2 : ℝ) ≠ 0 := by norm_num
    have hg := Real.Gamma_add_one hne
    convert hg using 1 <;> norm_num
  have h52 : Real.Gamma (5 / 2) = (3 / 4) * Real.Gamma (1 / 2) := by
    have hne2 : (3 / 2 : ℝ) ≠ 0 := by norm_num
    have hg2 := Real.Gamma_add_one hne2
    calc
      Real.Gamma (5 / 2) = (3 / 2) * Real.Gamma (3 / 2) := by
        convert hg2 using 1 <;> norm_num
      _ = (3 / 2) * ((1 / 2) * Real.Gamma (1 / 2)) := by rw [h32]
      _ = (3 / 4) * Real.Gamma (1 / 2) := by ring
  have hdiv : Real.Gamma x = Real.Gamma (x + 1) / x := by
    have hg := Real.Gamma_add_one hxne
    rw [hg]
    field_simp [hxne]
  have h1x : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx1
  have hGpos : 0 ≤ Real.Gamma (5 / 2) := by positivity
  calc
    Real.Gamma x = Real.Gamma (x + 1) / x := hdiv
    _ ≤ Real.Gamma (5 / 2) / x := by
      exact div_le_div_of_nonneg_right hmono (le_of_lt hxpos)
    _ ≤ Real.Gamma (5 / 2) := by
      calc
        Real.Gamma (5 / 2) / x = Real.Gamma (5 / 2) * x⁻¹ := by ring
        _ ≤ Real.Gamma (5 / 2) * 1 := by
          exact mul_le_mul_of_nonneg_left h1x hGpos
        _ = Real.Gamma (5 / 2) := by ring
    _ = (3 / 4) * Real.Gamma (1 / 2) := h52

/-- For `z = a + it` with `0 ≤ a ≤ 1` and `1 ≤ |t|` we have the uniform bound
`‖Γ(1 - z)‖ ≤ Γ(1/2)`. -/
lemma norm_Gamma_one_sub_le_Gamma_half {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (1 - ((a : ℂ) + Complex.I * (t : ℂ)))‖ ≤ Real.Gamma (1 / 2) := by
  let z : ℂ := (a : ℂ) + Complex.I * (t : ℂ)
  have hz_re : z.re = a := by simp [z]
  have hz_im : z.im = t := by simp [z]
  have ht_ne : t ≠ 0 := by
    intro ht0
    rw [ht0] at ht
    norm_num at ht
  by_cases hle : a ≤ 1 / 2
  · -- case a ≤ 1/2: 1-a ∈ [1/2,1]
    let w : ℂ := 1 - z
    have hw_re : w.re = 1 - a := by simp [w, z]
    have hw_pos : 0 < w.re := by
      rw [hw_re]
      linarith
    have hmain := norm_Gamma_le_norm_Gamma_re w hw_pos
    have hG1 : ‖Complex.Gamma w‖ ≤ Real.Gamma (1 - a) := by
      calc
        ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma ((w.re : ℝ) : ℂ)‖ := hmain
        _ = ‖Complex.Gamma (((1 - a : ℝ) : ℂ))‖ := by rw [hw_re]
        _ = Real.Gamma (1 - a) := by
          rw [Complex.Gamma_ofReal, Complex.norm_of_nonneg]
          exact le_of_lt (Real.Gamma_pos_of_pos (by linarith : 0 < 1 - a))
    have hG2 : Real.Gamma (1 - a) ≤ Real.Gamma (1 / 2) := by
      exact Gamma_le_Gamma_half_of_mem (by linarith) (by linarith)
    calc
      ‖Complex.Gamma (1 - z)‖ = ‖Complex.Gamma w‖ := by simp [w]
      _ ≤ Real.Gamma (1 / 2) := le_trans hG1 hG2
  · -- case a > 1/2
    let w : ℂ := 1 - z
    have hw_re : w.re = 1 - a := by simp [w, z]
    have hw_im : w.im = -t := by simp [w, z]
    have hw_ne : w ≠ 0 := by
      intro hw0
      apply ht_ne
      have h0 : w.im = 0 := by rw [hw0]; simp
      rw [hw_im] at h0
      linarith
    have hw1 : w + 1 = 2 - z := by simp [w]; ring
    have hx2lo : 1 ≤ 2 - a := by linarith
    have hx2hi : 2 - a ≤ 3 / 2 := by linarith
    have hpos2 : 0 < 2 - a := by linarith
    have hGnorm : ‖Complex.Gamma (2 - z)‖ ≤ Real.Gamma (2 - a) := by
      have harg_re : (2 - z).re = 2 - a := by simp [z]
      have hle2 := norm_Gamma_le_norm_Gamma_re (2 - z) (by rw [harg_re]; linarith)
      calc
        ‖Complex.Gamma (2 - z)‖ ≤ ‖Complex.Gamma (((2 - a : ℝ) : ℂ))‖ := by simpa [harg_re] using hle2
        _ = Real.Gamma (2 - a) := by
          rw [Complex.Gamma_ofReal, Complex.norm_of_nonneg]
          exact le_of_lt (Real.Gamma_pos_of_pos hpos2)
    have hw_ge1 : 1 ≤ ‖w‖ := by
      calc
        1 ≤ |t| := ht
        _ = |w.im| := by rw [hw_im]; simp
        _ ≤ ‖w‖ := Complex.abs_im_le_norm w
    have hrecur_norm : ‖Complex.Gamma w‖ = ‖Complex.Gamma (w + 1)‖ / ‖w‖ := by
      have hg := Complex.Gamma_add_one w hw_ne
      have hn : ‖Complex.Gamma (w + 1)‖ = ‖w‖ * ‖Complex.Gamma w‖ := by
        rw [hg, norm_mul]
      rw [hn]
      field_simp [norm_ne_zero_iff.mpr hw_ne]
    have hG2 : ‖Complex.Gamma w‖ ≤ Real.Gamma (2 - a) := by
      calc
        ‖Complex.Gamma w‖ = ‖Complex.Gamma (w + 1)‖ / ‖w‖ := hrecur_norm
        _ = ‖Complex.Gamma (2 - z)‖ / ‖w‖ := by rw [hw1]
        _ ≤ Real.Gamma (2 - a) / ‖w‖ := by
          exact div_le_div_of_nonneg_right hGnorm (norm_nonneg w)
        _ ≤ Real.Gamma (2 - a) := by
          have h1w : ‖w‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hw_ge1
          have hposG : 0 ≤ Real.Gamma (2 - a) := le_of_lt (Real.Gamma_pos_of_pos hpos2)
          calc
            Real.Gamma (2 - a) / ‖w‖ = Real.Gamma (2 - a) * ‖w‖⁻¹ := by ring
            _ ≤ Real.Gamma (2 - a) * 1 := by
              exact mul_le_mul_of_nonneg_left h1w hposG
            _ = Real.Gamma (2 - a) := by ring
    have hG34 : Real.Gamma (2 - a) ≤ (3 / 4) * Real.Gamma (1 / 2) :=
      Gamma_le_three_quarters_Gamma_half hx2lo hx2hi
    have hGfin : (3 / 4) * Real.Gamma (1 / 2) ≤ Real.Gamma (1 / 2) := by
      have hposG : 0 < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
      nlinarith
    calc
      ‖Complex.Gamma (1 - z)‖ = ‖Complex.Gamma w‖ := by simp [w]
      _ ≤ Real.Gamma (1 / 2) := le_trans (le_trans hG2 hG34) hGfin

local macro_rules | `($x ^ $y) => `(HPow.hPow $x ($y : ℝ))

/-- Uniform lower bound for `|Γ(a + i·t)|` on the strip `0 ≤ a ≤ 1`, for large `|t|`:
there is `c > 0` such that `c · (1+|t|)^(-1) · exp(-π|t|) ≤ ‖Γ(a + i·t)‖` whenever
`0 ≤ a ≤ 1` and `1 ≤ |t|`.  (Proof: Euler reflection `Γ(z)·Γ(1-z) = π/sin(πz)`
plus `|Γ(w)| ≤ Γ(Re w)` on `Re w > 0` and `|sin(x + iy)| ≤ exp|y|`, splitting the
range of `a` near `0` and near `1` by the recurrence `Γ(z+1) = z·Γ(z)`.) -/
theorem norm_Gamma_lower_strip :
    ∃ c : ℝ, 0 < c ∧ ∀ (a t : ℝ), 0 ≤ a → a ≤ 1 → 1 ≤ |t| →
      c * (1 + |t|) ^ (-1) * Real.exp (-Real.pi * |t|) ≤ ‖Complex.Gamma ((a : ℂ) + I * (t : ℂ))‖ := by

  let C : ℝ := Real.Gamma (1 / 2)
  let c : ℝ := Real.pi / C
  have hCpos : 0 < C := by
    dsimp [C]
    exact Real.Gamma_pos_of_pos (by norm_num)
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos Real.pi_pos hCpos
  refine ⟨c, hcpos, ?_⟩
  intro a t ha0 ha1 ht
  let z : ℂ := (a : ℂ) + I * (t : ℂ)
  have hz_im : z.im = t := by simp [z]
  have ht_ne : t ≠ 0 := by
    intro ht0
    rw [ht0] at ht
    norm_num at ht
  have hBleC : ‖Complex.Gamma (1 - z)‖ ≤ C := by
    dsimp [C]
    simpa [z] using norm_Gamma_one_sub_le_Gamma_half ha0 ha1 ht
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    exact sin_ne_zero_of_im_ne_zero (by
      rw [Complex.im_ofReal_mul, hz_im]
      exact mul_ne_zero (ne_of_gt Real.pi_pos) ht_ne)
  have hsin_le : ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ rexp (Real.pi * |t|) := by
    have h1 := norm_sin_le_exp_abs_im ((Real.pi : ℂ) * z)
    have him : ((Real.pi : ℂ) * z).im = Real.pi * t := by
      rw [Complex.im_ofReal_mul, hz_im]
    calc
      ‖Complex.sin ((Real.pi : ℂ) * z)‖ ≤ rexp |(((Real.pi : ℂ) * z).im)| := h1
      _ = rexp (Real.pi * |t|) := by
        rw [him]
        congr 1
        rw [abs_mul, abs_of_pos Real.pi_pos]
  have hAB : Real.pi * rexp (-Real.pi * |t|) ≤
      ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ := by
    have hn := Gamma_mul_Gamma_one_sub_norm z
    rw [hn]
    have hsinpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * z)‖ := norm_pos_iff.mpr hsin_ne
    have hInv : rexp (-Real.pi * |t|) ≤ (‖Complex.sin ((Real.pi : ℂ) * z)‖)⁻¹ := by
      have hstep : (rexp (Real.pi * |t|))⁻¹ ≤ (‖Complex.sin ((Real.pi : ℂ) * z)‖)⁻¹ := by
        simpa using (one_div_le_one_div_of_le hsinpos hsin_le)
      simpa [Real.exp_neg] using hstep
    calc
      Real.pi * rexp (-Real.pi * |t|) ≤ Real.pi * (‖Complex.sin ((Real.pi : ℂ) * z)‖)⁻¹ := by
        exact mul_le_mul_of_nonneg_left hInv (le_of_lt Real.pi_pos)
      _ = Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by ring
  have hAge0 : 0 ≤ ‖Complex.Gamma z‖ := norm_nonneg _
  have hXC : Real.pi * rexp (-Real.pi * |t|) ≤ ‖Complex.Gamma z‖ * C := by
    calc
      Real.pi * rexp (-Real.pi * |t|) ≤ ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ := hAB
      _ ≤ ‖Complex.Gamma z‖ * C := by
        exact mul_le_mul_of_nonneg_left hBleC hAge0
  have hXdiv : (Real.pi * rexp (-Real.pi * |t|)) / C ≤ ‖Complex.Gamma z‖ := by
    exact (div_le_iff₀ hCpos).mpr hXC
  have hpow : (1 + |t|) ^ (-1 : ℝ) ≤ 1 := by
    rw [Real.rpow_neg_one]
    exact inv_le_one_of_one_le₀ (by linarith [abs_nonneg t])
  have h2 : c * (1 + |t|) ^ (-1 : ℝ) * rexp (-Real.pi * |t|) ≤ c * rexp (-Real.pi * |t|) := by
    have hc0 : 0 ≤ c := le_of_lt hcpos
    have he0 : 0 ≤ rexp (-Real.pi * |t|) := Real.exp_nonneg _
    calc
      c * (1 + |t|) ^ (-1 : ℝ) * rexp (-Real.pi * |t|) = c * rexp (-Real.pi * |t|) * ((1 + |t|) ^ (-1 : ℝ)) := by
        ring
      _ ≤ c * rexp (-Real.pi * |t|) * 1 := by
        exact mul_le_mul_of_nonneg_left hpow (mul_nonneg hc0 he0)
      _ = c * rexp (-Real.pi * |t|) := by ring
  have hmain : c * rexp (-Real.pi * |t|) ≤ ‖Complex.Gamma z‖ := by
    calc
      c * rexp (-Real.pi * |t|) = (Real.pi / C) * rexp (-Real.pi * |t|) := by
        dsimp [c]
      _ = (Real.pi * rexp (-Real.pi * |t|)) / C := by ring
      _ ≤ ‖Complex.Gamma z‖ := hXdiv
  calc
    c * (1 + |t|) ^ (-1 : ℝ) * rexp (-Real.pi * |t|) ≤ c * rexp (-Real.pi * |t|) := h2
    _ ≤ ‖Complex.Gamma ((a : ℂ) + I * (t : ℂ))‖ := by
      simpa [z] using hmain

end Commons.Analysis.SpecialFunctions.Gamma