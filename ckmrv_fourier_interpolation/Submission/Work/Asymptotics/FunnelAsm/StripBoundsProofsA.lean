/-
# The four quantitative strip estimates

This module proves the four inputs collected in `Work.Asymptotics.StripBounds`:

* `PGF24StripBound`, `PGA24StripBound` : the second-order `q`-expansions of `F24` and `A24`
  (used to compute the integer `n` from the vanishing of `G_{1,1}`),
* `PGGcusp10StripBound`, `PGGcusp10DeltaBound` : the size of `G_{1,0}` and of its `T`-difference
  on the fundamental strip.

All estimates are consequences of the Eisenstein `q`-expansions (`EisensteinQExp`), the theta
expansions (`ThetaQExp`), the explicit `𝓛`-expansion (`LfunQExp`) and `cuspL ℓ = 4 log 2`
(`CuspL_eq`), together with `‖nomeQ w‖ ≤ e^{-4π} ≤ 1/280000` and
`‖w‖ ‖nomeQ w‖ ≤ 3 e^{-4π}` on the strip.
-/
import Mathlib
import Submission.Work.Asymptotics.PGFar.Defs
import Submission.Work.Asymptotics.PGFar.Reduction
import Submission.Work.Asymptotics.FunnelAsm.EisensteinQExpA
import Submission.Work.Asymptotics.ThetaQExp
import Submission.Work.Asymptotics.LfunQExp
import Submission.Work.Asymptotics.CuspL_eq

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup

noncomputable section

/-- Elementary product estimate: `x y - x' y' = (x-x')y + x'(y-y')`. -/
lemma norm_mul_sub_mul_le (x x' y y' : ℂ) :
    ‖x * y - x' * y'‖ ≤ ‖x - x'‖ * ‖y‖ + ‖x'‖ * ‖y - y'‖ := by
  have h : x * y - x' * y' = (x - x') * y + x' * (y - y') := by ring
  rw [h]
  calc ‖(x - x') * y + x' * (y - y')‖ ≤ ‖(x - x') * y‖ + ‖x' * (y - y')‖ := norm_add_le _ _
    _ = ‖x - x'‖ * ‖y‖ + ‖x'‖ * ‖y - y'‖ := by rw [norm_mul, norm_mul]

lemma norm_sub_add_le (a b c : ℂ) : ‖a - b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 : ‖a - b + c‖ ≤ ‖a - b‖ + ‖c‖ := norm_add_le _ _
  have h2 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  linarith [h1, h2]

lemma norm_add_add_le (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 := norm_add_le (a + b) c
  have h2 := norm_add_le a b
  linarith [h1, h2]

/-- `‖a + b q + c q²‖ ≤ ‖a‖ + ‖b‖‖q‖ + ‖c‖‖q‖²`. -/
lemma norm_quadratic_le (q a b c : ℂ) :
    ‖a + b * q + c * q ^ 2‖ ≤ ‖a‖ + ‖b‖ * ‖q‖ + ‖c‖ * ‖q‖ ^ 2 := by
  have h1 : ‖a + b * q + c * q ^ 2‖ ≤ ‖a + b * q‖ + ‖c * q ^ 2‖ := norm_add_le _ _
  have h2 : ‖a + b * q‖ ≤ ‖a‖ + ‖b * q‖ := norm_add_le _ _
  simp only [norm_mul, norm_pow] at h1 h2
  linarith

/-- On the strip the three Eisenstein truncations and `E₂,E₄,E₆` have norm at most `2`. -/
lemma strip_trunc_bounds (w : UpperHalfPlane) (h : Strip w) :
    ‖(1 : ℂ) - 24 * nomeQ w - 72 * (nomeQ w) ^ 2‖ ≤ 2
      ∧ ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ≤ 2
      ∧ ‖(1 : ℂ) - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2‖ ≤ 2
      ∧ ‖Work.Kernels.E2Fun w‖ ≤ 2 ∧ ‖Work.Kernels.E4Fun w‖ ≤ 2
      ∧ ‖Work.Kernels.E6Fun w‖ ≤ 2 := by
  have hQ1 : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
  have hQ1' : ‖nomeQ w‖ ≤ 1 := by linarith
  have hq2 : ‖(nomeQ w) ^ 2‖ ≤ 1 / 280000 := by
    rw [norm_pow]
    have := norm_nonneg (nomeQ w)
    nlinarith [hQ1, hQ1']
  obtain ⟨he2, he4, he6⟩ := EisensteinQExp
  have h2 := he2 w h.2
  have h4 := he4 w h.2
  have h6 := he6 w h.2
  have hb2 : ‖(1 : ℂ) - 24 * nomeQ w - 72 * (nomeQ w) ^ 2‖
      ≤ 1 + 24 * ‖nomeQ w‖ + 72 * ‖(nomeQ w) ^ 2‖ := by
    have h1 := norm_quadratic_le (nomeQ w) 1 (-24) (-72)
    have heq : (1 : ℂ) + (-24) * nomeQ w + (-72) * (nomeQ w) ^ 2
        = 1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2 := by ring
    rw [heq] at h1
    rw [norm_one, norm_neg, norm_neg, Complex.norm_ofNat, Complex.norm_ofNat] at h1
    rw [norm_pow]
    exact h1
  have hb4 : ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖
      ≤ 1 + 240 * ‖nomeQ w‖ + 2160 * ‖(nomeQ w) ^ 2‖ := by
    have h1 := norm_quadratic_le (nomeQ w) 1 240 2160
    rw [norm_one, Complex.norm_ofNat, Complex.norm_ofNat] at h1
    rw [norm_pow]
    exact h1
  have hb6 : ‖(1 : ℂ) - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2‖
      ≤ 1 + 504 * ‖nomeQ w‖ + 16632 * ‖(nomeQ w) ^ 2‖ := by
    have h1 := norm_quadratic_le (nomeQ w) 1 (-504) (-16632)
    have heq : (1 : ℂ) + (-504) * nomeQ w + (-16632) * (nomeQ w) ^ 2
        = 1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2 := by ring
    rw [heq] at h1
    rw [norm_one, norm_neg, norm_neg, Complex.norm_ofNat, Complex.norm_ofNat] at h1
    rw [norm_pow]
    exact h1
  have hq3 : ‖nomeQ w‖ ^ 3 ≤ 1 / 280000 := by
    have h : ‖nomeQ w‖ ^ 3 ≤ ‖nomeQ w‖ := by
      have h' : ‖nomeQ w‖ ^ 3 ≤ ‖nomeQ w‖ ^ 1 :=
        pow_le_pow_of_le_one (norm_nonneg _) hQ1' (by norm_num : 1 ≤ 3)
      simpa using h'
    linarith [h, hQ1]
  have hmul3 : ∀ m : ℝ, 0 ≤ m → m * ‖nomeQ w‖ ^ 3 ≤ m * ((1 / 280000 : ℝ) ^ 3) := by
    intro m hm
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hQ1 3) hm
  refine ⟨by nlinarith [hb2, hQ1', hq2], by nlinarith [hb4, hQ1', hq2],
    by nlinarith [hb6, hQ1', hq2], ?_, ?_, ?_⟩
  · have hsub := norm_add_le (Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2))
      (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
    rw [sub_add_cancel] at hsub
    have := hmul3 1000 (by norm_num)
    nlinarith [hsub, h2, hb2, this, hQ1, hq2]
  · have hsub := norm_add_le (Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2))
      (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
    rw [sub_add_cancel] at hsub
    have := hmul3 50000 (by norm_num)
    nlinarith [hsub, h4, hb4, this, hQ1, hq2]
  · have hsub := norm_add_le (Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
      (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
    rw [sub_add_cancel] at hsub
    have := hmul3 1000000 (by norm_num)
    nlinarith [hsub, h6, hb6, this, hQ1, hq2]

lemma norm_sq_sub_sq_le (x x' : ℂ) : ‖x ^ 2 - x' ^ 2‖ ≤ ‖x - x'‖ * (‖x‖ + ‖x'‖) := by
  have h : x ^ 2 - x' ^ 2 = (x - x') * (x + x') := by ring
  rw [h, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)

lemma norm_cube_sub_cube_le (x x' : ℂ) :
    ‖x ^ 3 - x' ^ 3‖ ≤ ‖x - x'‖ * (‖x‖ ^ 2 + ‖x‖ * ‖x'‖ + ‖x'‖ ^ 2) := by
  have h : x ^ 3 - x' ^ 3 = (x - x') * (x ^ 2 + x * x' + x' ^ 2) := by ring
  rw [h, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖x ^ 2 + x * x' + x' ^ 2‖ ≤ ‖x ^ 2 + x * x'‖ + ‖x' ^ 2‖ := norm_add_le _ _
    _ ≤ (‖x ^ 2‖ + ‖x * x'‖) + ‖x' ^ 2‖ := by
        have := norm_add_le (x ^ 2) (x * x'); linarith
    _ = ‖x‖ ^ 2 + ‖x‖ * ‖x'‖ + ‖x'‖ ^ 2 := by rw [norm_pow, norm_mul, norm_pow]

lemma norm_add_sub_le (a b c : ℂ) : ‖a + b - c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h : a + b - c = (a + b) + (-c) := by ring
  rw [h]
  calc ‖(a + b) + -c‖ ≤ ‖a + b‖ + ‖-c‖ := norm_add_le _ _
    _ = ‖a + b‖ + ‖c‖ := by rw [norm_neg]
    _ ≤ (‖a‖ + ‖b‖) + ‖c‖ := by linarith [norm_add_le a b]

/-- Second-order `q`-expansion of `E₂E₄ - E₆`. -/
lemma E2E4_sub_E6_expansion (w : UpperHalfPlane) (h : Strip w) :
    ‖Work.Kernels.E2Fun w * Work.Kernels.E4Fun w - Work.Kernels.E6Fun w
        - (720 * nomeQ w + 12960 * (nomeQ w) ^ 2)‖ ≤ 1200000 * ‖nomeQ w‖ ^ 3 := by
  obtain ⟨hb2, hb4, hb6, hE2, hE4, hE6⟩ := strip_trunc_bounds w h
  obtain ⟨he2, he4, he6⟩ := EisensteinQExp
  have h2 := he2 w h.2
  have h4 := he4 w h.2
  have h6 := he6 w h.2
  have hQ1 : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
  have hq4 : ‖nomeQ w‖ ^ 4 ≤ (1 / 280000) * ‖nomeQ w‖ ^ 3 := by
    have hh : ‖nomeQ w‖ ^ 4 = ‖nomeQ w‖ * ‖nomeQ w‖ ^ 3 := by ring
    rw [hh]
    exact mul_le_mul_of_nonneg_right hQ1 (by positivity)
  have key : Work.Kernels.E2Fun w * Work.Kernels.E4Fun w - Work.Kernels.E6Fun w
      - (720 * nomeQ w + 12960 * (nomeQ w) ^ 2)
      = (Work.Kernels.E2Fun w * Work.Kernels.E4Fun w
          - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2))
        + ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
            - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) - (720 * nomeQ w + 12960 * (nomeQ w) ^ 2))
        - (Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)) := by ring
  rw [key]
  have hAB : ‖Work.Kernels.E2Fun w * Work.Kernels.E4Fun w
      - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)‖
      ≤ 110000 * ‖nomeQ w‖ ^ 3 := by
    have h := norm_mul_sub_mul_le (Work.Kernels.E2Fun w) (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
      (Work.Kernels.E4Fun w) (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
    have h1 : ‖Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)‖
        * ‖Work.Kernels.E4Fun w‖ ≤ 1000 * ‖nomeQ w‖ ^ 3 * 2 :=
      mul_le_mul h2 hE4 (norm_nonneg _) (by positivity)
    have h2' : ‖(1 : ℂ) - 24 * nomeQ w - 72 * (nomeQ w) ^ 2‖
        * ‖Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)‖
        ≤ 2 * (50000 * ‖nomeQ w‖ ^ 3) :=
      mul_le_mul hb2 h4 (by positivity) (by norm_num)
    have hsum : 1000 * ‖nomeQ w‖ ^ 3 * 2 + 2 * (50000 * ‖nomeQ w‖ ^ 3) ≤ 110000 * ‖nomeQ w‖ ^ 3 := by
      have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
      nlinarith [hq]
    linarith [h, h1, h2', hsum]
  have hT : ‖(1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
      - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) - (720 * nomeQ w + 12960 * (nomeQ w) ^ 2)‖
      ≤ 70000 * ‖nomeQ w‖ ^ 3 := by
    have hpoly : (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
        - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) - (720 * nomeQ w + 12960 * (nomeQ w) ^ 2)
        = -69120 * (nomeQ w) ^ 3 - 155520 * (nomeQ w) ^ 4 := by ring
    rw [hpoly]
    calc ‖-(69120 : ℂ) * (nomeQ w) ^ 3 - 155520 * (nomeQ w) ^ 4‖
        ≤ ‖-(69120 : ℂ) * (nomeQ w) ^ 3‖ + ‖(155520 : ℂ) * (nomeQ w) ^ 4‖ := norm_sub_le _ _
      _ = 69120 * ‖nomeQ w‖ ^ 3 + 155520 * ‖nomeQ w‖ ^ 4 := by
          rw [norm_mul, norm_mul, norm_neg, norm_pow, norm_pow, Complex.norm_ofNat,
            Complex.norm_ofNat]
      _ ≤ 70000 * ‖nomeQ w‖ ^ 3 := by
          have h2 : 155520 * ‖nomeQ w‖ ^ 4 ≤ 155520 * ((1 / 280000) * ‖nomeQ w‖ ^ 3) :=
            mul_le_mul_of_nonneg_left hq4 (by norm_num)
          have hnum : 69120 * ‖nomeQ w‖ ^ 3 + 155520 * ((1 / 280000) * ‖nomeQ w‖ ^ 3)
              ≤ 70000 * ‖nomeQ w‖ ^ 3 := by
            have hq : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
            nlinarith [hq]
          linarith [h2, hnum]
  have hfin := norm_add_sub_le (Work.Kernels.E2Fun w * Work.Kernels.E4Fun w
        - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2))
      ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
        - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) - (720 * nomeQ w + 12960 * (nomeQ w) ^ 2))
      (Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
  have hsum : 110000 * ‖nomeQ w‖ ^ 3 + 70000 * ‖nomeQ w‖ ^ 3 + 1000000 * ‖nomeQ w‖ ^ 3
      ≤ 1200000 * ‖nomeQ w‖ ^ 3 := by
    have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
    nlinarith [hq]
  linarith [hfin, hAB, hT, h6, hsum]

/-- Second-order `q`-expansion of `E₂E₆ - E₄²`. -/
lemma E2E6_sub_E4sq_expansion (w : UpperHalfPlane) (h : Strip w) :
    ‖Work.Kernels.E2Fun w * Work.Kernels.E6Fun w - (Work.Kernels.E4Fun w) ^ 2
        + (1008 * nomeQ w + 66528 * (nomeQ w) ^ 2)‖ ≤ 4000000 * ‖nomeQ w‖ ^ 3 := by
  obtain ⟨hb2, hb4, hb6, hE2, hE4, hE6⟩ := strip_trunc_bounds w h
  obtain ⟨he2, he4, he6⟩ := EisensteinQExp
  have h2 := he2 w h.2
  have h4 := he4 w h.2
  have h6 := he6 w h.2
  have hQ1 : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
  have hQ1' : ‖nomeQ w‖ ≤ 1 := by linarith
  have hq4 : ‖nomeQ w‖ ^ 4 ≤ (1 / 280000) * ‖nomeQ w‖ ^ 3 := by
    have hh : ‖nomeQ w‖ ^ 4 = ‖nomeQ w‖ * ‖nomeQ w‖ ^ 3 := by ring
    rw [hh]
    exact mul_le_mul_of_nonneg_right hQ1 (by positivity)
  have hq5 : ‖nomeQ w‖ ^ 5 ≤ (1 / 280000) * ‖nomeQ w‖ ^ 3 := by
    have hh : ‖nomeQ w‖ ^ 5 = ‖nomeQ w‖ ^ 2 * ‖nomeQ w‖ ^ 3 := by ring
    rw [hh]
    have h2 : ‖nomeQ w‖ ^ 2 ≤ 1 / 280000 := by
      have h : ‖nomeQ w‖ ^ 2 ≤ ‖nomeQ w‖ := by
        have h' : ‖nomeQ w‖ ^ 2 ≤ ‖nomeQ w‖ ^ 1 :=
          pow_le_pow_of_le_one (norm_nonneg _) hQ1' (by norm_num : 1 ≤ 2)
        simpa using h'
      linarith [h, hQ1]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have key : Work.Kernels.E2Fun w * Work.Kernels.E6Fun w - (Work.Kernels.E4Fun w) ^ 2
      + (1008 * nomeQ w + 66528 * (nomeQ w) ^ 2)
      = (Work.Kernels.E2Fun w * Work.Kernels.E6Fun w
          - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
        + ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
            - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2 + (1008 * nomeQ w + 66528 * (nomeQ w) ^ 2))
        - ((Work.Kernels.E4Fun w) ^ 2 - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2) := by ring
  rw [key]
  have hAB : ‖Work.Kernels.E2Fun w * Work.Kernels.E6Fun w
      - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)‖
      ≤ 2500000 * ‖nomeQ w‖ ^ 3 := by
    have h := norm_mul_sub_mul_le (Work.Kernels.E2Fun w) (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
      (Work.Kernels.E6Fun w) (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
    have h1 : ‖Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)‖
        * ‖Work.Kernels.E6Fun w‖ ≤ 1000 * ‖nomeQ w‖ ^ 3 * 2 :=
      mul_le_mul h2 hE6 (norm_nonneg _) (by positivity)
    have h2' : ‖(1 : ℂ) - 24 * nomeQ w - 72 * (nomeQ w) ^ 2‖
        * ‖Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)‖
        ≤ 2 * (1000000 * ‖nomeQ w‖ ^ 3) :=
      mul_le_mul hb2 h6 (by positivity) (by norm_num)
    have hsum : 1000 * ‖nomeQ w‖ ^ 3 * 2 + 2 * (1000000 * ‖nomeQ w‖ ^ 3) ≤ 2500000 * ‖nomeQ w‖ ^ 3 := by
      have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
      nlinarith [hq]
    linarith [h, h1, h2', hsum]
  have hT : ‖(1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
      - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
      + (1008 * nomeQ w + 66528 * (nomeQ w) ^ 2)‖ ≤ 700000 * ‖nomeQ w‖ ^ 3 := by
    have hpoly : (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2
        + (1008 * nomeQ w + 66528 * (nomeQ w) ^ 2)
        = -601344 * (nomeQ w) ^ 3 - 3468096 * (nomeQ w) ^ 4 := by ring
    rw [hpoly]
    calc ‖-(601344 : ℂ) * (nomeQ w) ^ 3 - 3468096 * (nomeQ w) ^ 4‖
        ≤ ‖-(601344 : ℂ) * (nomeQ w) ^ 3‖ + ‖(3468096 : ℂ) * (nomeQ w) ^ 4‖ := norm_sub_le _ _
      _ = 601344 * ‖nomeQ w‖ ^ 3 + 3468096 * ‖nomeQ w‖ ^ 4 := by
          rw [norm_mul, norm_mul, norm_neg, norm_pow, norm_pow, Complex.norm_ofNat,
            Complex.norm_ofNat]
      _ ≤ 700000 * ‖nomeQ w‖ ^ 3 := by
          have h2 : 3468096 * ‖nomeQ w‖ ^ 4 ≤ 3468096 * ((1 / 280000) * ‖nomeQ w‖ ^ 3) :=
            mul_le_mul_of_nonneg_left hq4 (by norm_num)
          have hnum : 601344 * ‖nomeQ w‖ ^ 3 + 3468096 * ((1 / 280000) * ‖nomeQ w‖ ^ 3)
              ≤ 700000 * ‖nomeQ w‖ ^ 3 := by
            have hq : (0 : ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
            nlinarith [hq]
          linarith [h2, hnum]
  have hsq : ‖(Work.Kernels.E4Fun w) ^ 2 - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2‖
      ≤ 250000 * ‖nomeQ w‖ ^ 3 := by
    have h := norm_sq_sub_sq_le (Work.Kernels.E4Fun w) (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
    have h1 : ‖Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)‖
        * (‖Work.Kernels.E4Fun w‖ + ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖)
        ≤ (50000 * ‖nomeQ w‖ ^ 3) * 4 := by
      have h2' : ‖Work.Kernels.E4Fun w‖ + ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ≤ 4 := by
        linarith [hE4, hb4]
      exact mul_le_mul h4 h2' (by positivity) (by positivity)
    have hsum : (50000 * ‖nomeQ w‖ ^ 3) * 4 ≤ 250000 * ‖nomeQ w‖ ^ 3 := by
      have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
      nlinarith [hq]
    linarith [h, h1, hsum]
  have hfin := norm_add_sub_le (Work.Kernels.E2Fun w * Work.Kernels.E6Fun w
        - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
      ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
        - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2 + (1008 * nomeQ w + 66528 * (nomeQ w) ^ 2))
      ((Work.Kernels.E4Fun w) ^ 2 - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 2)
  have hsum : 2500000 * ‖nomeQ w‖ ^ 3 + 700000 * ‖nomeQ w‖ ^ 3 + 250000 * ‖nomeQ w‖ ^ 3
      ≤ 4000000 * ‖nomeQ w‖ ^ 3 := by
    have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
    nlinarith [hq]
  linarith [hfin, hAB, hT, hsq, hsum]

/-- Norm bound for a quintic polynomial in `q` on the strip. -/
lemma norm_poly5_le {q : ℂ} {a : ℝ} (ha : ‖q‖ ≤ a) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (c0 c1 c2 c3 c4 c5 : ℂ) :
    ‖c0 + c1 * q + c2 * q ^ 2 + c3 * q ^ 3 + c4 * q ^ 4 + c5 * q ^ 5‖
      ≤ ‖c0‖ + ‖c1‖ * a + ‖c2‖ * a ^ 2 + ‖c3‖ * a ^ 3 + ‖c4‖ * a ^ 4 + ‖c5‖ * a ^ 5 := by
  have hp : ∀ k : ℕ, ‖q‖ ^ k ≤ a ^ k := fun k => pow_le_pow_left₀ (norm_nonneg _) ha k
  have h₁ : ‖c0 + c1 * q + c2 * q ^ 2 + c3 * q ^ 3 + c4 * q ^ 4 + c5 * q ^ 5‖
      ≤ ‖c0 + c1 * q + c2 * q ^ 2 + c3 * q ^ 3 + c4 * q ^ 4‖ + ‖c5 * q ^ 5‖ := norm_add_le _ _
  have h₂ : ‖c0 + c1 * q + c2 * q ^ 2 + c3 * q ^ 3 + c4 * q ^ 4‖
      ≤ ‖c0 + c1 * q + c2 * q ^ 2 + c3 * q ^ 3‖ + ‖c4 * q ^ 4‖ := norm_add_le _ _
  have h₃ : ‖c0 + c1 * q + c2 * q ^ 2 + c3 * q ^ 3‖
      ≤ ‖c0 + c1 * q + c2 * q ^ 2‖ + ‖c3 * q ^ 3‖ := norm_add_le _ _
  have h₄ : ‖c0 + c1 * q + c2 * q ^ 2‖ ≤ ‖c0 + c1 * q‖ + ‖c2 * q ^ 2‖ := norm_add_le _ _
  have h₅ : ‖c0 + c1 * q‖ ≤ ‖c0‖ + ‖c1 * q‖ := norm_add_le _ _
  simp only [norm_mul, norm_pow] at h₁ h₂ h₃ h₄ h₅
  have k1 : ‖c1‖ * ‖q‖ ≤ ‖c1‖ * a := mul_le_mul_of_nonneg_left ha (norm_nonneg _)
  have k2 : ‖c2‖ * ‖q‖ ^ 2 ≤ ‖c2‖ * a ^ 2 := mul_le_mul_of_nonneg_left (hp 2) (norm_nonneg _)
  have k3 : ‖c3‖ * ‖q‖ ^ 3 ≤ ‖c3‖ * a ^ 3 := mul_le_mul_of_nonneg_left (hp 3) (norm_nonneg _)
  have k4 : ‖c4‖ * ‖q‖ ^ 4 ≤ ‖c4‖ * a ^ 4 := mul_le_mul_of_nonneg_left (hp 4) (norm_nonneg _)
  have k5 : ‖c5‖ * ‖q‖ ^ 5 ≤ ‖c5‖ * a ^ 5 := mul_le_mul_of_nonneg_left (hp 5) (norm_nonneg _)
  linarith [h₁, h₂, h₃, h₄, h₅, k1, k2, k3, k4, k5]

/-- **Second-order `q`-expansion of `A24`**, sharp form. -/
lemma PGA24StripBound_sharp (w : UpperHalfPlane) (h : Strip w) :
    ‖A24 w + 725760 * (nomeQ w) ^ 2‖ ≤ 100000000 * ‖nomeQ w‖ ^ 3 := by
  have hQ1 : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
  have hQ0 : (0:ℝ) ≤ ‖nomeQ w‖ := norm_nonneg _
  have hQ1' : ‖nomeQ w‖ ≤ 1 := by linarith
  have hq4 : ‖nomeQ w‖ ^ 4 ≤ (1 / 280000) * ‖nomeQ w‖ ^ 3 := by
    have hh : ‖nomeQ w‖ ^ 4 = ‖nomeQ w‖ * ‖nomeQ w‖ ^ 3 := by ring
    rw [hh]
    exact mul_le_mul_of_nonneg_right hQ1 (by positivity)
  have hq6 : ‖nomeQ w‖ ^ 6 ≤ ((1 / 280000 : ℝ) ^ 3) * ‖nomeQ w‖ ^ 3 := by
    have hh : ‖nomeQ w‖ ^ 6 = (‖nomeQ w‖ ^ 3) * ‖nomeQ w‖ ^ 3 := by ring
    rw [hh]
    have h3 : ‖nomeQ w‖ ^ 3 ≤ (1 / 280000 : ℝ) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hQ1 3
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  have hq2' : ‖nomeQ w‖ ^ 2 ≤ (1 / 280000) * ‖nomeQ w‖ := by
    have hh : ‖nomeQ w‖ ^ 2 = ‖nomeQ w‖ * ‖nomeQ w‖ := by ring
    rw [hh]
    exact mul_le_mul_of_nonneg_right hQ1 hQ0
  set ρX := Work.Kernels.E2Fun w * Work.Kernels.E4Fun w - Work.Kernels.E6Fun w
    - (720 * nomeQ w + 12960 * (nomeQ w) ^ 2) with hρX
  set ρY := Work.Kernels.E2Fun w * Work.Kernels.E6Fun w - (Work.Kernels.E4Fun w) ^ 2
    + (1008 * nomeQ w + 66528 * (nomeQ w) ^ 2) with hρY
  have hX : ‖ρX‖ ≤ 1200000 * ‖nomeQ w‖ ^ 3 := E2E4_sub_E6_expansion w h
  have hY : ‖ρY‖ ≤ 4000000 * ‖nomeQ w‖ ^ 3 := E2E6_sub_E4sq_expansion w h
  have key : A24 w + 725760 * (nomeQ w) ^ 2
      = ρX * ρY + (720 * nomeQ w + 12960 * (nomeQ w) ^ 2) * ρY
        + ρX * (-1008 * nomeQ w - 66528 * (nomeQ w) ^ 2)
        + ((720 * nomeQ w + 12960 * (nomeQ w) ^ 2) * (-1008 * nomeQ w - 66528 * (nomeQ w) ^ 2)
            + 725760 * (nomeQ w) ^ 2) := by
    rw [hρX, hρY]
    unfold A24
    ring
  rw [key]
  have h1 : ‖ρX * ρY‖ ≤ 1 * ‖nomeQ w‖ ^ 3 := by
    rw [norm_mul]
    have hb := mul_le_mul hX hY (norm_nonneg _) (by positivity)
    have h3 : 1200000 * ‖nomeQ w‖ ^ 3 * (4000000 * ‖nomeQ w‖ ^ 3) ≤ 1 * ‖nomeQ w‖ ^ 3 := by
      nlinarith [hq6, hQ0]
    nlinarith [hb, h3]
  have h2 : ‖(720 * nomeQ w + 12960 * (nomeQ w) ^ 2) * ρY‖ ≤ 11000 * ‖nomeQ w‖ ^ 3 := by
    rw [norm_mul]
    have hXb : ‖720 * nomeQ w + 12960 * (nomeQ w) ^ 2‖ ≤ 720.1 * ‖nomeQ w‖ := by
      have hh := norm_quadratic_le (nomeQ w) 0 720 12960
      simp only [norm_zero, zero_add, Complex.norm_ofNat, norm_pow] at hh
      nlinarith [hh, hQ1, hQ0, hq2']
    have hb := mul_le_mul hXb hY (norm_nonneg _) (by positivity)
    have h3 : 720.1 * ‖nomeQ w‖ * (4000000 * ‖nomeQ w‖ ^ 3) ≤ 11000 * ‖nomeQ w‖ ^ 3 := by
      nlinarith [hq4, hQ0]
    nlinarith [hb, h3]
  have h3 : ‖ρX * (-1008 * nomeQ w - 66528 * (nomeQ w) ^ 2)‖ ≤ 5000 * ‖nomeQ w‖ ^ 3 := by
    rw [norm_mul]
    have hYb : ‖-1008 * nomeQ w - 66528 * (nomeQ w) ^ 2‖ ≤ 1008.3 * ‖nomeQ w‖ := by
      have hgoal : ‖-1008 * nomeQ w - 66528 * (nomeQ w) ^ 2‖
          = ‖(-1008 : ℂ) * nomeQ w + (-66528 : ℂ) * (nomeQ w) ^ 2‖ := by
        congr 1
        ring
      rw [hgoal]
      calc ‖(-1008 : ℂ) * nomeQ w + (-66528 : ℂ) * (nomeQ w) ^ 2‖
          ≤ ‖(-1008 : ℂ) * nomeQ w‖ + ‖(-66528 : ℂ) * (nomeQ w) ^ 2‖ := norm_add_le _ _
        _ = 1008 * ‖nomeQ w‖ + 66528 * ‖(nomeQ w) ^ 2‖ := by
            rw [norm_mul, norm_mul, norm_neg, norm_neg, Complex.norm_ofNat, Complex.norm_ofNat]
        _ ≤ 1008.3 * ‖nomeQ w‖ := by
            rw [norm_pow]
            nlinarith [hq2', hQ0]
    have hb := mul_le_mul hX hYb (norm_nonneg _) (by positivity)
    have h3 : 1200000 * ‖nomeQ w‖ ^ 3 * (1008.3 * ‖nomeQ w‖) ≤ 5000 * ‖nomeQ w‖ ^ 3 := by
      nlinarith [hq4, hQ0]
    nlinarith [hb, h3]
  have h4 : ‖(720 * nomeQ w + 12960 * (nomeQ w) ^ 2) * (-1008 * nomeQ w - 66528 * (nomeQ w) ^ 2)
      + 725760 * (nomeQ w) ^ 2‖ ≤ 61000000 * ‖nomeQ w‖ ^ 3 := by
    have hpoly : (720 * nomeQ w + 12960 * (nomeQ w) ^ 2) * (-1008 * nomeQ w - 66528 * (nomeQ w) ^ 2)
        + 725760 * (nomeQ w) ^ 2
        = (nomeQ w) ^ 3 * ((-60963840 : ℂ) + (-862202880) * nomeQ w) := by ring
    rw [hpoly, norm_mul, norm_pow]
    have hW : ‖(-60963840 : ℂ) + (-862202880) * nomeQ w‖ ≤ 61000000 := by
      have hh := norm_quadratic_le (nomeQ w) (-60963840) (-862202880) 0
      simp only [Complex.norm_ofNat, norm_zero, zero_mul, add_zero, norm_neg] at hh
      nlinarith [hh, hQ1, hQ0]
    calc ‖nomeQ w‖ ^ 3 * ‖(-60963840 : ℂ) + (-862202880) * nomeQ w‖
        ≤ ‖nomeQ w‖ ^ 3 * 61000000 := mul_le_mul_of_nonneg_left hW (by positivity)
      _ = 61000000 * ‖nomeQ w‖ ^ 3 := by ring
  have hAB : ‖ρX * ρY + (720 * nomeQ w + 12960 * (nomeQ w) ^ 2) * ρY‖
      ≤ ‖ρX * ρY‖ + ‖(720 * nomeQ w + 12960 * (nomeQ w) ^ 2) * ρY‖ := norm_add_le _ _
  have hfin := norm_add_add_le (ρX * ρY + (720 * nomeQ w + 12960 * (nomeQ w) ^ 2) * ρY)
    (ρX * (-1008 * nomeQ w - 66528 * (nomeQ w) ^ 2))
    ((720 * nomeQ w + 12960 * (nomeQ w) ^ 2) * (-1008 * nomeQ w - 66528 * (nomeQ w) ^ 2)
      + 725760 * (nomeQ w) ^ 2)
  have hsum : 1 * ‖nomeQ w‖ ^ 3 + 11000 * ‖nomeQ w‖ ^ 3 + 5000 * ‖nomeQ w‖ ^ 3
      + 61000000 * ‖nomeQ w‖ ^ 3 ≤ 100000000 * ‖nomeQ w‖ ^ 3 := by
    have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
    nlinarith [hq]
  nlinarith [hfin, hAB, h1, h2, h3, h4, hsum]

/-- **Second-order `q`-expansion of `A24`.** -/
theorem PGA24StripBound (w : UpperHalfPlane) (h : Strip w) :
    ‖A24 w + 725760 * (nomeQ w) ^ 2‖ ≤ 1000000000 * ‖nomeQ w‖ ^ 3 := by
  have h := PGA24StripBound_sharp w h
  have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
  linarith [h, hq]

set_option maxHeartbeats 2000000 in
/-- Second-order `q`-expansion of `7E₄³+5E₆²-12E₂E₄E₆` (the `𝔹` of the dimension-24 kernel). -/
lemma B_expansion (w : UpperHalfPlane) (h : Strip w) :
    ‖7 * (Work.Kernels.E4Fun w) ^ 3 + 5 * (Work.Kernels.E6Fun w) ^ 2
        - 12 * (Work.Kernels.E2Fun w * Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
        - (3456 * nomeQ w + 3908736 * (nomeQ w) ^ 2)‖ ≤ 500000000 * ‖nomeQ w‖ ^ 3 := by
  obtain ⟨hb2, hb4, hb6, hE2, hE4, hE6⟩ := strip_trunc_bounds w h
  obtain ⟨he2, he4, he6⟩ := EisensteinQExp
  have h2 := he2 w h.2
  have h4 := he4 w h.2
  have h6 := he6 w h.2
  have hQ1 : ‖nomeQ w‖ ≤ 1 / 280000 := (strip_facts w h).1
  have hQ0 : (0:ℝ) ≤ ‖nomeQ w‖ := norm_nonneg _
  have hQ1' : ‖nomeQ w‖ ≤ 1 := by linarith
  set ρ4 := (Work.Kernels.E4Fun w) ^ 3
    - ((1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3 with hρ4
  set ρ6 := (Work.Kernels.E6Fun w) ^ 2
    - ((1 : ℂ) - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2 with hρ6
  set ρ246 := Work.Kernels.E2Fun w * Work.Kernels.E4Fun w * Work.Kernels.E6Fun w
    - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
      * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
    with hρ246
  set P := 7 * ((1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) ^ 3
    + 5 * ((1 : ℂ) - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2) ^ 2
    - 12 * ((1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
      * ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)))
    - (3456 * nomeQ w + 3908736 * (nomeQ w) ^ 2) with hP
  have hc4 : ‖ρ4‖ ≤ 600000 * ‖nomeQ w‖ ^ 3 := by
    have hh := norm_cube_sub_cube_le (Work.Kernels.E4Fun w)
      (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
    have i1 : ‖Work.Kernels.E4Fun w‖ ^ 2 ≤ 4 := by
      nlinarith [hE4, norm_nonneg (Work.Kernels.E4Fun w)]
    have i2 : ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ^ 2 ≤ 4 := by
      nlinarith [hb4, norm_nonneg ((1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)]
    have i3 : ‖Work.Kernels.E4Fun w‖ * ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ≤ 4 := by
      have := mul_le_mul hE4 hb4 (norm_nonneg _) (by norm_num)
      linarith [this]
    rw [hρ4]
    have hb : ‖Work.Kernels.E4Fun w‖ ^ 2 + ‖Work.Kernels.E4Fun w‖
          * ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖
          + ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ^ 2 ≤ 12 := by linarith [i1, i2, i3]
    have h1 : ‖Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)‖
        * (‖Work.Kernels.E4Fun w‖ ^ 2 + ‖Work.Kernels.E4Fun w‖
            * ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖
          + ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖ ^ 2)
        ≤ (50000 * ‖nomeQ w‖ ^ 3) * 12 := mul_le_mul h4 hb (by positivity) (by norm_num)
    linarith [hh, h1]
  have hs6 : ‖ρ6‖ ≤ 4000000 * ‖nomeQ w‖ ^ 3 := by
    have hh := norm_sq_sub_sq_le (Work.Kernels.E6Fun w)
      (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
    have hb : ‖Work.Kernels.E6Fun w‖ + ‖(1 : ℂ) - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2‖ ≤ 4 := by
      linarith [hE6, hb6]
    have h1 : ‖Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)‖
        * (‖Work.Kernels.E6Fun w‖ + ‖(1 : ℂ) - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2‖)
        ≤ (1000000 * ‖nomeQ w‖ ^ 3) * 4 := mul_le_mul h6 hb (by positivity) (by norm_num)
    rw [hρ6]
    linarith [hh, h1]
  have h46 : ‖Work.Kernels.E4Fun w * Work.Kernels.E6Fun w
      - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)‖
      ≤ 2500000 * ‖nomeQ w‖ ^ 3 := by
    have hh := norm_mul_sub_mul_le (Work.Kernels.E4Fun w)
      (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
      (Work.Kernels.E6Fun w) (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)
    have h1 : ‖Work.Kernels.E4Fun w - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)‖
        * ‖Work.Kernels.E6Fun w‖ ≤ (50000 * ‖nomeQ w‖ ^ 3) * 2 :=
      mul_le_mul h4 hE6 (norm_nonneg _) (by positivity)
    have h2' : ‖(1 : ℂ) + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2‖
        * ‖Work.Kernels.E6Fun w - (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)‖
        ≤ 2 * (1000000 * ‖nomeQ w‖ ^ 3) :=
      mul_le_mul hb4 h6 (by positivity) (by norm_num)
    have hsum : 50000 * ‖nomeQ w‖ ^ 3 * 2 + 2 * (1000000 * ‖nomeQ w‖ ^ 3)
        ≤ 2500000 * ‖nomeQ w‖ ^ 3 := by
      have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
      nlinarith [hq]
    linarith [hh, h1, h2', hsum]
  have hprod : ‖ρ246‖ ≤ 6000000 * ‖nomeQ w‖ ^ 3 := by
    rw [hρ246,
      show Work.Kernels.E2Fun w * Work.Kernels.E4Fun w * Work.Kernels.E6Fun w
        = Work.Kernels.E2Fun w * (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w) from by ring]
    have hh := norm_mul_sub_mul_le (Work.Kernels.E2Fun w) (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)
      (Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
      ((1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2) * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2))
    have hE46 : ‖Work.Kernels.E4Fun w * Work.Kernels.E6Fun w‖ ≤ 4 := by
      rw [norm_mul]
      have := mul_le_mul hE4 hE6 (norm_nonneg _) (by norm_num)
      linarith [this]
    have h1 : ‖Work.Kernels.E2Fun w - (1 - 24 * nomeQ w - 72 * (nomeQ w) ^ 2)‖
        * ‖Work.Kernels.E4Fun w * Work.Kernels.E6Fun w‖ ≤ (1000 * ‖nomeQ w‖ ^ 3) * 4 :=
      mul_le_mul h2 hE46 (norm_nonneg _) (by positivity)
    have h2' : ‖(1 : ℂ) - 24 * nomeQ w - 72 * (nomeQ w) ^ 2‖
        * ‖Work.Kernels.E4Fun w * Work.Kernels.E6Fun w
            - (1 + 240 * nomeQ w + 2160 * (nomeQ w) ^ 2)
              * (1 - 504 * nomeQ w - 16632 * (nomeQ w) ^ 2)‖
        ≤ 2 * (2500000 * ‖nomeQ w‖ ^ 3) :=
      mul_le_mul hb2 h46 (by positivity) (by norm_num)
    have hsum : 1000 * ‖nomeQ w‖ ^ 3 * 4 + 2 * (2500000 * ‖nomeQ w‖ ^ 3)
        ≤ 6000000 * ‖nomeQ w‖ ^ 3 := by
      have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
      nlinarith [hq]
    linarith [hh, h1, h2', hsum]
  have hp : P = (nomeQ w) ^ 3 * (224097408 + 2944786752 * nomeQ w
      + 8778792960 * (nomeQ w) ^ 2 + 39504568320 * (nomeQ w) ^ 3) := by
    rw [hP]; ring
  have hPb : ‖P‖ ≤ 230000000 * ‖nomeQ w‖ ^ 3 := by
    rw [hp, norm_mul, norm_pow]
    have hW : ‖(224097408 : ℂ) + 2944786752 * nomeQ w + 8778792960 * (nomeQ w) ^ 2
        + 39504568320 * (nomeQ w) ^ 3‖ ≤ 230000000 := by
      have hh := norm_poly5_le hQ1 (by norm_num) (by norm_num)
        224097408 2944786752 8778792960 39504568320 0 0
      simp only [Complex.norm_ofNat, norm_zero, zero_mul, mul_zero, add_zero, norm_pow] at hh
      nlinarith [hh, hQ1, hQ0]
    calc ‖nomeQ w‖ ^ 3 * ‖(224097408 : ℂ) + 2944786752 * nomeQ w
          + 8778792960 * (nomeQ w) ^ 2 + 39504568320 * (nomeQ w) ^ 3‖
        ≤ ‖nomeQ w‖ ^ 3 * 230000000 := mul_le_mul_of_nonneg_left hW (by positivity)
      _ = 230000000 * ‖nomeQ w‖ ^ 3 := by ring
  have hkey : 7 * (Work.Kernels.E4Fun w) ^ 3 + 5 * (Work.Kernels.E6Fun w) ^ 2
        - 12 * (Work.Kernels.E2Fun w * Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
        - (3456 * nomeQ w + 3908736 * (nomeQ w) ^ 2)
      = 7 * ρ4 + 5 * ρ6 - 12 * ρ246 + P := by
    rw [hρ4, hρ6, hρ246, hP]
    ring
  rw [hkey]
  calc ‖7 * ρ4 + 5 * ρ6 - 12 * ρ246 + P‖
      ≤ ‖7 * ρ4 + 5 * ρ6 - 12 * ρ246‖ + ‖P‖ := norm_add_le _ _
    _ ≤ (‖7 * ρ4 + 5 * ρ6‖ + ‖12 * ρ246‖) + ‖P‖ := by
        have := norm_sub_le (7 * ρ4 + 5 * ρ6) (12 * ρ246); linarith [this]
    _ ≤ ((‖7 * ρ4‖ + ‖5 * ρ6‖) + ‖12 * ρ246‖) + ‖P‖ := by
        have := norm_add_le (7 * ρ4) (5 * ρ6); linarith [this]
    _ ≤ ((4200000 * ‖nomeQ w‖ ^ 3 + 20000000 * ‖nomeQ w‖ ^ 3) + 80000000 * ‖nomeQ w‖ ^ 3)
          + 230000000 * ‖nomeQ w‖ ^ 3 := by
        have h7 : ‖(7:ℂ)‖ = 7 := by norm_num
        have h5 : ‖(5:ℂ)‖ = 5 := by norm_num
        have h12 : ‖(12:ℂ)‖ = 12 := by norm_num
        have i1 : ‖7 * ρ4‖ ≤ 4200000 * ‖nomeQ w‖ ^ 3 := by
          rw [norm_mul, h7]; linarith [hc4]
        have i2 : ‖5 * ρ6‖ ≤ 20000000 * ‖nomeQ w‖ ^ 3 := by
          rw [norm_mul, h5]; linarith [hs6]
        have i3 : ‖12 * ρ246‖ ≤ 80000000 * ‖nomeQ w‖ ^ 3 := by
          rw [norm_mul, h12]
          have h := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ) ≤ 12)
          have h2 : 12 * (6000000 * ‖nomeQ w‖ ^ 3) ≤ 80000000 * ‖nomeQ w‖ ^ 3 := by
            have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
            nlinarith [hq]
          linarith [h, h2]
        nlinarith [i1, i2, i3, hPb]
    _ ≤ 500000000 * ‖nomeQ w‖ ^ 3 := by
        have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
        nlinarith [hq]

/-- **Second-order `q`-expansion of `F24`.** -/
theorem PGF24StripBound (w : UpperHalfPlane) (h : Strip w) :
    ‖F24 w - (3456 * nomeQ w
        + (3908736 + 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760) * (nomeQ w) ^ 2)‖
      ≤ 1000000000 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖ ^ 3 := by
  have hB := B_expansion w h
  have hA := PGA24StripBound_sharp w h
  have key : F24 w - (3456 * nomeQ w
        + (3908736 + 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * 725760) * (nomeQ w) ^ 2)
      = (7 * (Work.Kernels.E4Fun w) ^ 3 + 5 * (Work.Kernels.E6Fun w) ^ 2
          - 12 * (Work.Kernels.E2Fun w * Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
          - (3456 * nomeQ w + 3908736 * (nomeQ w) ^ 2))
        - 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * (A24 w + 725760 * (nomeQ w) ^ 2) := by
    unfold F24
    ring
  rw [key]
  have h2 : ‖2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * (A24 w + 725760 * (nomeQ w) ^ 2)‖
      ≤ 2 * Real.pi * ‖(w : ℂ)‖ * (100000000 * ‖nomeQ w‖ ^ 3) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left hA (by positivity)
  have hsum : 500000000 * ‖nomeQ w‖ ^ 3
      + 2 * Real.pi * ‖(w : ℂ)‖ * (100000000 * ‖nomeQ w‖ ^ 3)
      ≤ 1000000000 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖ ^ 3 := by
    have hq : (0:ℝ) ≤ ‖nomeQ w‖ ^ 3 := by positivity
    have hw : (0:ℝ) ≤ ‖(w : ℂ)‖ := norm_nonneg _
    have hgoal : 1000000000 * (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖ ^ 3
        = 1000000000 * ‖nomeQ w‖ ^ 3 + 1000000000 * ‖(w : ℂ)‖ * ‖nomeQ w‖ ^ 3 := by ring
    rw [hgoal]
    have h1 : 2 * Real.pi * ‖(w : ℂ)‖ * (100000000 * ‖nomeQ w‖ ^ 3)
        ≤ 1000000000 * ‖(w : ℂ)‖ * ‖nomeQ w‖ ^ 3 := by
      have hpi : 2 * Real.pi * 100000000 ≤ 1000000000 := by linarith [Real.pi_lt_four]
      have h0 : (0:ℝ) ≤ ‖(w : ℂ)‖ * ‖nomeQ w‖ ^ 3 := by positivity
      nlinarith [hpi, h0]
    linarith [h1, hq]
  have hfin := norm_sub_le (7 * (Work.Kernels.E4Fun w) ^ 3 + 5 * (Work.Kernels.E6Fun w) ^ 2
      - 12 * (Work.Kernels.E2Fun w * Work.Kernels.E4Fun w * Work.Kernels.E6Fun w)
      - (3456 * nomeQ w + 3908736 * (nomeQ w) ^ 2))
    (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) * (A24 w + 725760 * (nomeQ w) ^ 2))
  nlinarith [hfin, hB, h2, hsum]

end

end Work.Asymptotics
