/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the angular weighted integrals on `[0, π/2]`

For a `C¹` function `f : ℝ → ℝ` on `[0, π/2]` vanishing at both endpoints
(`f 0 = f (π/2) = 0`) and `0 ≤ η < 1`, the five weighted integrals

* `f(θ)² sin(2θ)^{-(2+η)}`,  `f(θ)² sin(2θ)^{-η}`,  `f'(θ)² sin(2θ)^{-η}`,
* `f(θ)² (2θ)^{-(2+η)}`,  `f'(θ)² (2θ)^{-η}`

are interval integrable on `[0, π/2]`.

The mechanism is that `f` vanishes at both endpoints at least linearly
(`contDiffOn_one_bounds`), so writing `m = min θ (π/2-θ)`,

`f(θ)² ≤ C² m²`,

while Jordan's inequality bounds the singular weights by the endpoint majorant
`θ^{-η} + (π/2-θ)^{-η}` (integrable since `η < 1`).  The pointwise estimates are
`sin_weight_pointwise_majorants`; the a.e.-measurability/dominated-convergence
step is `integrableOn_of_rpow_majorant`; the continuity of the integrands on the
open interval is `continuousOn_sin_weight_integrals`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.contDiffOn_one_bounds
import Submission.Work.Elliptic.integrableOn_of_rpow_majorant
import Submission.Work.Spaces.sin_rpow_le_majorant_pi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory
open Set

namespace Work.Elliptic

/-- `sin(2θ)^{-p}` is dominated by the endpoint majorant for every `0 ≤ p`
(the case `p = 0` is trivial, the rest is Jordan's inequality). -/
private lemma sin_rpow_le_majorant0 {p θ : ℝ} (hp : 0 ≤ p) (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    (Real.sin (2 * θ)) ^ (-p) ≤
      (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)) := by
  rcases eq_or_lt_of_le hp with h | h
  · subst h
    simp only [neg_zero, Real.rpow_zero]
    norm_num
  · exact Work.Spaces.sin_rpow_le_majorant_pi p θ h hθ

/-- `min θ (π/2-θ)² · θ^{-(2+η)} ≤ θ^{-η}`. -/
private lemma min_sq_mul_rpow_le_left {η θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + η)) ≤ θ ^ (-η) := by
  have hφ0 : 0 < Real.pi / 2 - θ := by linarith
  have hm0 : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ0.le hφ0.le
  have hle : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hm0 (min_le_left _ _) 2
  have hw : 0 ≤ θ ^ (-(2 + η)) := Real.rpow_nonneg hθ0.le _
  calc (min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + η))
      ≤ θ ^ 2 * θ ^ (-(2 + η)) := mul_le_mul_of_nonneg_right hle hw
    _ = θ ^ (-η) := by
        rw [show θ ^ 2 = θ ^ (2 : ℝ) by norm_num [Real.rpow_two],
          ← Real.rpow_add hθ0 (2 : ℝ) (-(2 + η))]
        ring_nf

/-- `min θ (π/2-θ)² · (π/2-θ)^{-(2+η)} ≤ (π/2-θ)^{-η}`. -/
private lemma min_sq_mul_rpow_le_right {η θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (min θ (Real.pi / 2 - θ)) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η)) ≤
      (Real.pi / 2 - θ) ^ (-η) := by
  have hφ0 : 0 < Real.pi / 2 - θ := by linarith
  have hm0 : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ0.le hφ0.le
  have hle : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 :=
    pow_le_pow_left₀ hm0 (min_le_right _ _) 2
  have hw : 0 ≤ (Real.pi / 2 - θ) ^ (-(2 + η)) := Real.rpow_nonneg hφ0.le _
  calc (min θ (Real.pi / 2 - θ)) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η))
      ≤ (Real.pi / 2 - θ) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η)) := mul_le_mul_of_nonneg_right hle hw
    _ = (Real.pi / 2 - θ) ^ (-η) := by
        rw [show (Real.pi / 2 - θ) ^ 2 = (Real.pi / 2 - θ) ^ (2 : ℝ) by
              norm_num [Real.rpow_two],
          ← Real.rpow_add hφ0 (2 : ℝ) (-(2 + η))]
        ring_nf

/-- The five pointwise majorant estimates. -/
theorem sin_weight_pointwise_majorants {η C C' : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hC : 0 ≤ C) (hC' : 0 ≤ C') {f : ℝ → ℝ}
    (hf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C * min θ (Real.pi / 2 - θ))
    (hf' : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ C') :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))|
          ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)|
          ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)|
          ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |f θ ^ 2 * (2 * θ) ^ (-(2 + η))|
          ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        |(deriv f θ) ^ 2 * (2 * θ) ^ (-η)|
          ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) := by
  have hpi4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hK1 : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (2 + η) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg hpi4 _)
  have hK2 : 0 ≤ C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η :=
    mul_nonneg (mul_nonneg (sq_nonneg C) (sq_nonneg _)) (Real.rpow_nonneg hpi4 _)
  have hK3 : 0 ≤ C' ^ 2 * (Real.pi / 4) ^ η :=
    mul_nonneg (sq_nonneg C') (Real.rpow_nonneg hpi4 _)
  have hK4 : 0 ≤ C ^ 2 * (2 : ℝ) ^ (-(2 + η)) :=
    mul_nonneg (sq_nonneg C) (Real.rpow_nonneg h2 _)
  have hK5 : 0 ≤ C' ^ 2 * (2 : ℝ) ^ (-η) :=
    mul_nonneg (sq_nonneg C') (Real.rpow_nonneg h2 _)
  set K : ℝ := C ^ 2 * (Real.pi / 4) ^ (2 + η) + C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η
    + C' ^ 2 * (Real.pi / 4) ^ η + C ^ 2 * (2 : ℝ) ^ (-(2 + η)) + C' ^ 2 * (2 : ℝ) ^ (-η)
    with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; linarith
  refine ⟨K, hKnn, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hφ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hIcc : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨hθ0.le, hθ.2.le⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
    have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-(2 + η)) := Real.rpow_nonneg hsin0 _
    have hG : 0 ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) :=
      add_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hφ0.le _)
    have hf2 : f θ ^ 2 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by
      rw [← sq_abs]
      calc |f θ| ^ 2 ≤ (C * min θ (Real.pi / 2 - θ)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hf θ hθ) 2
        _ = C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by ring
    have hsinb : (Real.sin (2 * θ)) ^ (-(2 + η)) ≤
        (Real.pi / 4) ^ (2 + η) * (θ ^ (-(2 + η)) + (Real.pi / 2 - θ) ^ (-(2 + η))) :=
      sin_rpow_le_majorant0 (p := 2 + η) (by linarith) hIcc
    have hmn : 0 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by positivity
    calc |f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))|
        ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 *
            ((Real.pi / 4) ^ (2 + η) *
              (θ ^ (-(2 + η)) + (Real.pi / 2 - θ) ^ (-(2 + η)))) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hw]
          exact mul_le_mul hf2 hsinb hw hmn
      _ = (C ^ 2 * (Real.pi / 4) ^ (2 + η)) *
            ((min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + η)) +
              (min θ (Real.pi / 2 - θ)) ^ 2 * (Real.pi / 2 - θ) ^ (-(2 + η))) := by ring
      _ ≤ (C ^ 2 * (Real.pi / 4) ^ (2 + η)) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (min_sq_mul_rpow_le_left hθ0 hθ.2) (min_sq_mul_rpow_le_right hθ0 hθ.2))
            hK1
      _ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith [hK2, hK3, hK4, hK5]) hG
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hφ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hIcc : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨hθ0.le, hθ.2.le⟩
    have hm0 : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ0.le hφ0.le
    have hmle : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 := le_trans (min_le_left _ _) hθ.2.le
    have hm2 : (min θ (Real.pi / 2 - θ)) ^ 2 ≤ (Real.pi / 2) ^ 2 :=
      pow_le_pow_left₀ hm0 hmle 2
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
    have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hsin0 _
    have hG : 0 ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) :=
      add_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hφ0.le _)
    have hf2 : f θ ^ 2 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by
      rw [← sq_abs]
      calc |f θ| ^ 2 ≤ (C * min θ (Real.pi / 2 - θ)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hf θ hθ) 2
        _ = C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by ring
    have hsinb : (Real.sin (2 * θ)) ^ (-η) ≤
        (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
      sin_rpow_le_majorant0 (p := η) hη0 hIcc
    have hcoef : 0 ≤ (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
      mul_nonneg (Real.rpow_nonneg hpi4 _) hG
    calc |f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)|
        ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 *
            ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hw]
          exact mul_le_mul hf2 hsinb hw (by positivity)
      _ ≤ (C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η) *
            (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by
          have h1 : C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 ≤ C ^ 2 * (Real.pi / 2) ^ 2 :=
            mul_le_mul_of_nonneg_left hm2 (sq_nonneg C)
          have h2 := mul_le_mul_of_nonneg_right h1 hcoef
          calc C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 *
                ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)))
              = (C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2) *
                ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) := by ring
            _ ≤ (C ^ 2 * (Real.pi / 2) ^ 2) *
                ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) := h2
            _ = (C ^ 2 * (Real.pi / 2) ^ 2 * (Real.pi / 4) ^ η) *
                (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by ring
      _ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith [hK1, hK3, hK4, hK5]) hG
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hφ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hIcc : θ ∈ Set.Icc 0 (Real.pi / 2) := ⟨hθ0.le, hθ.2.le⟩
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).le
    have hw : 0 ≤ (Real.sin (2 * θ)) ^ (-η) := Real.rpow_nonneg hsin0 _
    have hG : 0 ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) :=
      add_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hφ0.le _)
    have hd2 : (deriv f θ) ^ 2 ≤ C' ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hf' θ hθ) 2
    have hsinb : (Real.sin (2 * θ)) ^ (-η) ≤
        (Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
      sin_rpow_le_majorant0 (p := η) hη0 hIcc
    calc |(deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)|
        ≤ C' ^ 2 * ((Real.pi / 4) ^ η * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ)), abs_of_nonneg hw]
          exact mul_le_mul hd2 hsinb hw (by positivity)
      _ = (C' ^ 2 * (Real.pi / 4) ^ η) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) := by ring
      _ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith [hK1, hK2, hK4, hK5]) hG
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hφ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hG : 0 ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) :=
      add_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hφ0.le _)
    have hf2 : f θ ^ 2 ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by
      rw [← sq_abs]
      calc |f θ| ^ 2 ≤ (C * min θ (Real.pi / 2 - θ)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hf θ hθ) 2
        _ = C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 := by ring
    have hmm : (min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + η)) ≤ θ ^ (-η) :=
      min_sq_mul_rpow_le_left hθ0 hθ.2
    have hmul : (2 * θ) ^ (-(2 + η)) = (2 : ℝ) ^ (-(2 + η)) * θ ^ (-(2 + η)) :=
      Real.mul_rpow h2 hθ0.le
    have hw : 0 ≤ (2 * θ) ^ (-(2 + η)) :=
      Real.rpow_nonneg (mul_nonneg (by norm_num) hθ0.le) _
    calc |f θ ^ 2 * (2 * θ) ^ (-(2 + η))|
        ≤ C ^ 2 * (min θ (Real.pi / 2 - θ)) ^ 2 *
            ((2 : ℝ) ^ (-(2 + η)) * θ ^ (-(2 + η))) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hw]
          exact mul_le_mul hf2 (le_of_eq hmul) hw (by positivity)
      _ = (C ^ 2 * (2 : ℝ) ^ (-(2 + η))) *
            ((min θ (Real.pi / 2 - θ)) ^ 2 * θ ^ (-(2 + η))) := by ring
      _ ≤ (C ^ 2 * (2 : ℝ) ^ (-(2 + η))) * θ ^ (-η) :=
          mul_le_mul_of_nonneg_left hmm hK4
      _ ≤ (C ^ 2 * (2 : ℝ) ^ (-(2 + η))) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg hφ0.le _)) hK4
      _ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith [hK1, hK2, hK3, hK5]) hG
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hφ0 : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hd2 : (deriv f θ) ^ 2 ≤ C' ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hf' θ hθ) 2
    have hmul : (2 * θ) ^ (-η) = (2 : ℝ) ^ (-η) * θ ^ (-η) := Real.mul_rpow h2 hθ0.le
    have hw : 0 ≤ (2 * θ) ^ (-η) :=
      Real.rpow_nonneg (mul_nonneg (by norm_num) hθ0.le) _
    have hG : 0 ≤ θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η) :=
      add_nonneg (Real.rpow_nonneg hθ0.le _) (Real.rpow_nonneg hφ0.le _)
    calc |(deriv f θ) ^ 2 * (2 * θ) ^ (-η)|
        ≤ C' ^ 2 * ((2 : ℝ) ^ (-η) * θ ^ (-η)) := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (deriv f θ)), abs_of_nonneg hw]
          exact mul_le_mul hd2 (le_of_eq hmul) hw (by positivity)
      _ = (C' ^ 2 * (2 : ℝ) ^ (-η)) * θ ^ (-η) := by ring
      _ ≤ (C' ^ 2 * (2 : ℝ) ^ (-η)) * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg hφ0.le _)) hK5
      _ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η)) :=
          mul_le_mul_of_nonneg_right (by rw [hKdef]; linarith [hK1, hK2, hK3, hK4]) hG

/-- Continuity on the open interval of the five integrands. -/
theorem continuousOn_sin_weight_integrals {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) {η : ℝ} (hη0 : 0 ≤ η) :
    ContinuousOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 2)) ∧
    ContinuousOn (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) ∧
    ContinuousOn (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) ∧
    ContinuousOn (fun θ => f θ ^ 2 * (2 * θ) ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 2)) ∧
    ContinuousOn (fun θ => (deriv f θ) ^ 2 * (2 * θ) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) := by
  have h2 : (0 : ℝ) < Real.pi / 2 := Real.pi_div_two_pos
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Icc 0 (Real.pi / 2) :=
    Set.Ioo_subset_Icc_self
  have hfd : ContinuousOn (deriv f) (Set.Ioo 0 (Real.pi / 2)) := by
    have hd : ContinuousOn (derivWithin f (Set.Icc 0 (Real.pi / 2)))
        (Set.Icc 0 (Real.pi / 2)) :=
      hf.continuousOn_derivWithin (uniqueDiffOn_Icc h2) le_rfl
    refine (hd.mono hIoo).congr ?_
    intro θ hθ
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds hθ.1 hθ.2)).symm
  have hf2 : ContinuousOn (fun θ => f θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    (hf.continuousOn.mono hIoo).pow 2
  have hd2 : ContinuousOn (fun θ => (deriv f θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := hfd.pow 2
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have htwo : ContinuousOn (fun θ : ℝ => 2 * θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (continuous_const.mul continuous_id).continuousOn
  have hsinne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have htwone : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 2 * θ ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (by linarith [hθ.1])
  have hs1 : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (-(2 + η)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const fun θ hθ => Or.inl (hsinne θ hθ)
  have hs2 : ContinuousOn (fun θ => (Real.sin (2 * θ)) ^ (-η))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const fun θ hθ => Or.inl (hsinne θ hθ)
  have ht1 : ContinuousOn (fun θ => (2 * θ) ^ (-(2 + η))) (Set.Ioo 0 (Real.pi / 2)) :=
    htwo.rpow_const fun θ hθ => Or.inl (htwone θ hθ)
  have ht2 : ContinuousOn (fun θ => (2 * θ) ^ (-η)) (Set.Ioo 0 (Real.pi / 2)) :=
    htwo.rpow_const fun θ hθ => Or.inl (htwone θ hθ)
  exact ⟨hf2.mul hs1, hf2.mul hs2, hd2.mul hs2, hf2.mul ht1, hd2.mul ht2⟩

/-- **Target lemma.** All five weighted integrals are interval integrable on `[0, π/2]`. -/
theorem sin_weight_integrable {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2))) (h0 : f 0 = 0) (hpi : f (Real.pi / 2) = 0) :
    IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => f θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η)) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => f θ ^ 2 * (2 * θ) ^ (-(2 + η))) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * (2 * θ) ^ (-η)) volume 0 (Real.pi / 2) := by
  obtain ⟨C, hC, hfC, hdC⟩ := contDiffOn_one_bounds hf h0 hpi
  have hfIoo : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ C * min θ (Real.pi / 2 - θ) :=
    fun θ hθ => hfC θ (Set.Ioo_subset_Icc_self hθ)
  have hdIoo : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ C := by
    intro θ hθ
    rw [← Real.norm_eq_abs]
    exact hdC θ hθ
  obtain ⟨K, hK, hm1, hm2, hm3, hm4, hm5⟩ :=
    sin_weight_pointwise_majorants hη0 hη1 hC hC hfIoo hdIoo
  obtain ⟨c1, c2, c3, c4, c5⟩ := continuousOn_sin_weight_integrals hf hη0
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := Real.pi_div_two_pos.le
  have key : ∀ g : ℝ → ℝ, ContinuousOn g (Set.Ioo 0 (Real.pi / 2)) →
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖g θ‖ ≤ K * (θ ^ (-η) + (Real.pi / 2 - θ) ^ (-η))) →
      IntervalIntegrable g volume 0 (Real.pi / 2) := by
    intro g hgc hb
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hpi2).mpr
      (integrableOn_of_rpow_majorant hη0 hη1 hK hgc hb)
  have e1 := key _ c1 (fun θ hθ => by rw [Real.norm_eq_abs]; exact hm1 θ hθ)
  have e2 := key _ c2 (fun θ hθ => by rw [Real.norm_eq_abs]; exact hm2 θ hθ)
  have e3 := key _ c3 (fun θ hθ => by rw [Real.norm_eq_abs]; exact hm3 θ hθ)
  have e4 := key _ c4 (fun θ hθ => by rw [Real.norm_eq_abs]; exact hm4 θ hθ)
  have e5 := key _ c5 (fun θ hθ => by rw [Real.norm_eq_abs]; exact hm5 θ hθ)
  exact ⟨e1, e2, e3, e4, e5⟩

end Work.Elliptic
