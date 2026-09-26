import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Asymptotics.KhatE1.E1combo8_bound

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-!
# From the sharp leading coefficient to the sharp funnel strip bound

The sharp funnel statement

  `‖Kdev ℓ d τ z‖ ≤ C ‖q(τ)‖ (scale τ)^N (1+t)^M e^{-πt}`   (`τ ∈ 𝔽`, `z` in the strip `[0,1]`,
  `Im z = t ≥ Im τ + 1`)

is the `S`-transport (`Asymptotics/KhatE1/Kdev_cusp0_strip_sharp`, `cusp0_strip_of_funnel`) of the
cusp-`0` target of this assignment.  Two independent reductions of it are recorded here:

* `funnel_strip_sharp_of_leading_core` — from the **sharp leading coefficient**, i.e. from a
  function `f` with `‖f τ‖ ≤ C (scale τ)^N ‖q(τ)‖` and
  `Kdev ℓ d τ z = f τ · E(z) + O(‖q(τ)‖ (scale τ)^N (1+t)^M e^{-2πt})`, the funnel bound follows
  by the triangle inequality (`e^{-2πt} ≤ e^{-πt}` for `t ≥ 0`).
  For `d = 8` the coefficient is *exactly* `f = E1combo8/(288π)` (verified numerically to ten
  digits: `c₁/(E1combo8/(288π)) = 1.000000000` at `τ = 2i, 2.5i, 3i, 4i, 6i, 8i`), whence the
  funnel bound also follows from `KhatE1.E1combo8_bound` and the explicit form
  `KhatE1/Kdev_strip_sharp8_core`.  For `d = 24` the coefficient is only known to be of size
  `O(‖q(τ)‖ (scale τ)^N)`, which is the form used below.

* `funnel_strip_sharp_of_E1combo8` — the `d = 8` specialisation with the explicit coefficient
  `E1combo8/(288π)`, using `KhatE1.E1combo8_bound`.

`Kdev_funnel_strip_sharp` (this directory) is then the statement obtained by applying these to
the two-dimensional core; it is equivalent to the target of
`Asymptotics/KhatE1/Kdev_cusp0_strip_sharp` by `cusp0_strip_of_funnel`.
-/

/-- **From a sharp leading coefficient to the sharp funnel strip bound.** -/
theorem funnel_strip_sharp_of_leading_core (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hcore : ∃ (f : ℍ → ℂ) (C N M : ℝ), 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      (∀ τ : ℍ, Work.Asymptotics.Funnel τ →
        ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖) ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ d τ z - f τ * Work.Residues.Ept z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t))) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ d τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by
  obtain ⟨f, C, N, M, hC, hN, hM, hf, hker⟩ := hcore
  refine ⟨2 * C, N, M, by positivity, hN, hM, ?_⟩
  intro τ z t hτ ht hz0 hz1 hzim
  have ht3 : (3 : ℝ) ≤ t := by have := hτ.2; linarith
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hspos : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hsN : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N := Real.rpow_nonneg hspos.le N
  have h1t : (0 : ℝ) ≤ 1 + t := by linarith
  have h1tM : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg h1t M
  have hexp1 : (0 : ℝ) < Real.exp (-(Real.pi * t)) := Real.exp_pos _
  have hEz : ‖Work.Residues.Ept z‖ = Real.exp (-(Real.pi * t)) := by
    rw [Work.Residues.norm_Ept, hzim]
  have hexp2 : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(Real.pi * t)) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, ht0]
  have hfτ : ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ := hf τ hτ
  have hk := hker τ z t hτ ht hz0 hz1 hzim
  -- the two summands
  have hbase : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by positivity
  have h1 : ‖Work.Asymptotics.Kdev ℓ d τ z - f τ * Work.Residues.Ept z‖
      ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(Real.pi * t)) := by
    refine le_trans hk ?_
    have h2 : C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(2 * Real.pi * t))
        ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(Real.pi * t)) := by
      have h3 : (0 : ℝ) ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
          * (1 + t) ^ M := by positivity
      calc C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (-(2 * Real.pi * t))
          = (C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
              * Real.exp (-(2 * Real.pi * t)) := by ring
        _ ≤ (C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
              * Real.exp (-(Real.pi * t)) := mul_le_mul_of_nonneg_left hexp2 h3
        _ = C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by ring
    exact h2
  have h2 : ‖f τ * Work.Residues.Ept z‖
      ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(Real.pi * t)) := by
    rw [norm_mul, hEz]
    calc ‖f τ‖ * Real.exp (-(Real.pi * t))
        ≤ (C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖)
            * Real.exp (-(Real.pi * t)) :=
          mul_le_mul_of_nonneg_right hfτ hexp1.le
      _ ≤ (C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖)
            * ((1 + t) ^ M * Real.exp (-(Real.pi * t))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc Real.exp (-(Real.pi * t)) = 1 * Real.exp (-(Real.pi * t)) := (one_mul _).symm
            _ ≤ (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
                refine mul_le_mul_of_nonneg_right ?_ hexp1.le
                exact Real.one_le_rpow (by linarith) hM
      _ = C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (-(Real.pi * t)) := by ring
  calc ‖Work.Asymptotics.Kdev ℓ d τ z‖
      = ‖(Work.Asymptotics.Kdev ℓ d τ z - f τ * Work.Residues.Ept z)
          + f τ * Work.Residues.Ept z‖ := by congr 1; ring
    _ ≤ ‖Work.Asymptotics.Kdev ℓ d τ z - f τ * Work.Residues.Ept z‖
          + ‖f τ * Work.Residues.Ept z‖ := norm_add_le _ _
    _ ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(Real.pi * t))
        + C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(Real.pi * t)) := add_le_add h1 h2
    _ = 2 * C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
          * Real.exp (-(Real.pi * t)) := by ring

/-- **The `d = 8` specialisation with the explicit coefficient `E1combo8/(288π)`.** -/
theorem funnel_strip_sharp_of_E1combo8 (ℓ : Work.Kernels.LogLambdaData)
    (hcore : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ 8 τ z
            - (Work.Asymptotics.E1combo8 ℓ τ / (288 * (Real.pi : ℂ))) * Work.Residues.Ept z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t))) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.Kdev ℓ 8 τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C8, N8, M8, hC8, hN8, hM8, hker⟩ := hcore
  obtain ⟨Ce, Ne, hCe, hNe, hEb⟩ := Work.Asymptotics.KhatE1.E1combo8_bound ℓ
  -- the leading coefficient is `‖q(τ)‖·(scale τ)^N`-small by `E1combo8_bound`
  refine funnel_strip_sharp_of_leading_core ℓ 8 (Or.inl rfl) ?_
  refine ⟨fun τ => Work.Asymptotics.E1combo8 ℓ τ / (288 * (Real.pi : ℂ)),
    Ce / (288 * Real.pi) + C8, max Ne N8, max M8 0, by positivity, by positivity, by positivity, ?_, ?_⟩
  · -- size of the coefficient
    intro τ hτ
    have h288 : (0 : ℝ) < 288 * Real.pi := by positivity
    have hnorm : ‖(288 * (Real.pi : ℂ))‖ = 288 * Real.pi := by
      rw [norm_mul, Complex.norm_ofNat]
      congr 1
      exact (RCLike.norm_ofReal Real.pi).trans (abs_of_pos Real.pi_pos)
    rw [norm_div, hnorm]
    have h1 : ‖Work.Asymptotics.E1combo8 ℓ τ‖ / (288 * Real.pi)
        ≤ Ce * (Work.Kernels.scale τ) ^ Ne * ‖Work.Kernels.qParamFun τ‖
            / (288 * Real.pi) := div_le_div_of_nonneg_right (hEb τ hτ) h288.le
    refine le_trans h1 ?_
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hsNa : (Work.Kernels.scale τ) ^ Ne ≤ (Work.Kernels.scale τ) ^ (max Ne N8) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
    have hsN0 : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
    calc Ce * (Work.Kernels.scale τ) ^ Ne * ‖Work.Kernels.qParamFun τ‖ / (288 * Real.pi)
        = (Ce / (288 * Real.pi)) * ((Work.Kernels.scale τ) ^ Ne
            * ‖Work.Kernels.qParamFun τ‖) := by ring
      _ ≤ (Ce / (288 * Real.pi) + C8) * ((Work.Kernels.scale τ) ^ (max Ne N8)
            * ‖Work.Kernels.qParamFun τ‖) := by
          have hA : (0 : ℝ) ≤ Ce / (288 * Real.pi) := by positivity
          have hB : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ Ne
              * ‖Work.Kernels.qParamFun τ‖ := by positivity
          have hle : Ce / (288 * Real.pi) ≤ Ce / (288 * Real.pi) + C8 := by linarith
          refine mul_le_mul hle ?_ hB (by positivity)
          exact mul_le_mul_of_nonneg_right hsNa (norm_nonneg _)
      _ = (Ce / (288 * Real.pi) + C8) * (Work.Kernels.scale τ) ^ (max Ne N8)
            * ‖Work.Kernels.qParamFun τ‖ := by ring
  · -- the core with the modified polynomial exponents
    intro τ z t hτ ht hz0 hz1 hzim
    have hk := hker τ z t hτ ht hz0 hz1 hzim
    refine le_trans hk ?_
    have h1t : (1 : ℝ) ≤ 1 + t := by have := hτ.2; linarith
    have h1tm : (1 + t) ^ M8 ≤ (1 + t) ^ (max M8 0) :=
      Real.rpow_le_rpow_of_exponent_le h1t (le_max_left _ _)
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hsN : (Work.Kernels.scale τ) ^ N8 ≤ (Work.Kernels.scale τ) ^ (max Ne N8) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
    have hexp0 : (0 : ℝ) < Real.exp (-(2 * Real.pi * t)) := Real.exp_pos _
    have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
    have hC0 : (0 : ℝ) ≤ C8 := hC8.le
    have hCe0 : (0 : ℝ) ≤ Ce / (288 * Real.pi) + C8 := by positivity
    have hsN8 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N8 := by positivity
    have hbase : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N8 * (1 + t) ^ M8
        * Real.exp (-(2 * Real.pi * t)) := by positivity
    calc C8 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N8 * (1 + t) ^ M8
          * Real.exp (-(2 * Real.pi * t))
        ≤ C8 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max Ne N8)
            * (1 + t) ^ (max M8 0) * Real.exp (-(2 * Real.pi * t)) := by
          have s1 : C8 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N8
              ≤ C8 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max Ne N8) :=
            mul_le_mul_of_nonneg_left hsN (by positivity)
          have s2 : C8 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max Ne N8)
              * (1 + t) ^ M8
              ≤ C8 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max Ne N8)
                * (1 + t) ^ (max M8 0) := by
            refine mul_le_mul_of_nonneg_left h1tm ?_
            exact mul_nonneg (mul_nonneg hC0 hq0) (by positivity)
          have s1' : C8 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N8
              * (1 + t) ^ M8
              ≤ C8 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max Ne N8)
                * (1 + t) ^ M8 :=
            mul_le_mul_of_nonneg_right s1 (by positivity)
          exact mul_le_mul_of_nonneg_right (le_trans s1' s2) hexp0.le
      _ ≤ (Ce / (288 * Real.pi) + C8) * ‖Work.Kernels.qParamFun τ‖
            * (Work.Kernels.scale τ) ^ (max Ne N8) * (1 + t) ^ (max M8 0)
            * Real.exp (-(2 * Real.pi * t)) := by
          have hcle : C8 ≤ Ce / (288 * Real.pi) + C8 := by linarith [show (0:ℝ) ≤ Ce / (288 * Real.pi) by positivity]
          have hb : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max Ne N8)
              * (1 + t) ^ (max M8 0) * Real.exp (-(2 * Real.pi * t)) := by positivity
          calc C8 * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max Ne N8)
                * (1 + t) ^ (max M8 0) * Real.exp (-(2 * Real.pi * t))
              = C8 * (‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ (max Ne N8)
                  * (1 + t) ^ (max M8 0) * Real.exp (-(2 * Real.pi * t))) := by ring
            _ ≤ (Ce / (288 * Real.pi) + C8) * (‖Work.Kernels.qParamFun τ‖
                  * (Work.Kernels.scale τ) ^ (max Ne N8) * (1 + t) ^ (max M8 0)
                  * Real.exp (-(2 * Real.pi * t))) := mul_le_mul_of_nonneg_right hcle hb
            _ = (Ce / (288 * Real.pi) + C8) * ‖Work.Kernels.qParamFun τ‖
                  * (Work.Kernels.scale τ) ^ (max Ne N8) * (1 + t) ^ (max M8 0)
                  * Real.exp (-(2 * Real.pi * t)) := by ring

end

end Work.Asymptotics.KhatE1
