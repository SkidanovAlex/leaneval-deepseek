/-
# The shifted-integral decay lemma of the Weyl/Liouville step

`tendsto_integral_mul_shift`: if `f : ℝ³ → ℝ` is continuous and *vanishes at infinity*
(`Tendsto f (cocompact ℝ³) (nhds 0)`) and `g : ℝ³ → ℝ` is continuous with compact support, then
the shifted integral

  `t ↦ ∫ x, f x * g (x - t)`

tends to `0` along the cocompact filter: it is the convolution `f ∗ g~` (`g~(y) = g(-y)`) of a
`C₀`-function with an `L¹`-function, hence again `C₀`.

The proof is the elementary quantitative one.  Fix `ε > 0`.  Since `f → 0` at infinity there is
`R` with `R ≤ ‖x‖ → |f x| ≤ ε` outside the compact `K` where `K` is supplied by the cocompact
membership of `{|f| < ε}`; since `tsupport g` is bounded there is `M` with
`‖y‖ ≤ M` on `tsupport g`.  For `‖t‖ ≥ R + M` and any `x` with `g (x - t) ≠ 0` we have
`‖x - t‖ ≤ M`, hence `‖x‖ ≥ ‖t‖ - M ≥ R` and `|f x| ≤ ε`.  Therefore the integrand is
pointwise dominated by `ε * |g (· - t)|`, whence

  `‖∫ x, f x * g (x - t)‖ ≤ ∫ x, ε * |g (x - t)| = ε * ∫ x, |g|`,

and `∫ |g|` is finite by compact support.  Translating by `t` is measure preserving
(`integral_sub_right_eq_self`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.Auxiliary.tendsto_cocompact_bound_scalar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Weyl

open MeasureTheory Filter

theorem tendsto_integral_mul_shift
    (f g : Work.FTS.PressureOn.R3 → ℝ) (hf : Continuous f)
    (hf0 : Filter.Tendsto f (Filter.cocompact Work.FTS.PressureOn.R3) (nhds 0))
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Filter.Tendsto (fun t : Work.FTS.PressureOn.R3 => ∫ x, f x * g (x - t))
      (Filter.cocompact Work.FTS.PressureOn.R3) (nhds 0) := by
  have hgint : Integrable g := hg.integrable_of_hasCompactSupport hgc
  -- bound for the support of `g`
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ tsupport g, ‖x‖ ≤ M := hgc.isBounded.exists_norm_le
  -- the total mass of `|g|`
  set Cg : ℝ := ∫ x, |g x| with hCg
  have hCgnn : 0 ≤ Cg := by rw [hCg]; exact integral_nonneg fun x => abs_nonneg (g x)
  have hCg1 : 0 < Cg + 1 := by linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := ε / (Cg + 1) with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; exact div_pos hε hCg1
  -- threshold beyond which `|f| ≤ ε'`
  have hmem : {x : Work.FTS.PressureOn.R3 | f x ∈ Metric.ball (0 : ℝ) ε'}
      ∈ Filter.cocompact _ := hf0 (Metric.ball_mem_nhds 0 hε'pos)
  obtain ⟨K, hKc, hKsub⟩ := Filter.mem_cocompact.1 hmem
  obtain ⟨C, hC⟩ := hKc.isBounded.exists_norm_le
  set R : ℝ := C + 1 with hRdef
  have hRfd : ∀ x, R ≤ ‖x‖ → |f x| ≤ ε' := by
    intro x hx
    have hxK : x ∉ K := by
      intro hxK
      have h1 : ‖x‖ ≤ C := hC x hxK
      have h2 : C < R := by rw [hRdef]; linarith
      linarith
    have h : f x ∈ Metric.ball (0 : ℝ) ε' := hKsub (by simpa using hxK)
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at h
    exact le_of_lt h
  -- eventually `‖t‖ ≥ R + M`
  have hfinal : ∀ᶠ t in Filter.cocompact (Work.FTS.PressureOn.R3), R + M ≤ ‖t‖ :=
    tendsto_norm_cocompact_atTop.eventually (Filter.eventually_ge_atTop (R + M))
  refine hfinal.mono ?_
  intro t ht
  have hbound : ‖∫ x, f x * g (x - t)‖ ≤ ε' * Cg := by
    calc ‖∫ x, f x * g (x - t)‖
        ≤ ∫ x, ‖f x * g (x - t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ε' * |g (x - t)| := by
            apply integral_mono_of_nonneg
            · filter_upwards with x
              simp only [Pi.zero_apply]
              positivity
            · exact (hgint.abs.comp_sub_right t).const_mul ε'
            · filter_upwards with x
              rw [Real.norm_eq_abs, abs_mul]
              by_cases hg0 : g (x - t) = 0
              · rw [hg0, abs_zero, mul_zero, mul_zero]
              · have hsupp : x - t ∈ tsupport g :=
                  subset_tsupport g (by simpa [Function.mem_support] using hg0)
                have hxt : ‖x - t‖ ≤ M := hM _ hsupp
                have hx : R ≤ ‖x‖ := by
                  have htx : x - (x - t) = t := by abel
                  have h : ‖t‖ ≤ ‖x‖ + ‖x - t‖ := by
                    calc ‖t‖ = ‖x - (x - t)‖ := by rw [htx]
                      _ ≤ ‖x‖ + ‖x - t‖ := norm_sub_le x (x - t)
                  linarith
                exact mul_le_mul_of_nonneg_right (hRfd x hx) (abs_nonneg _)
      _ = ε' * Cg := by
            rw [integral_const_mul]
            congr 1
            rw [hCg]
            exact integral_sub_right_eq_self (fun x => |g x|) t
  rw [Real.dist_eq, sub_zero]
  have hlt : ε' * Cg < ε := by
    have h1 : ε' * Cg < ε' * (Cg + 1) := mul_lt_mul_of_pos_left (by linarith) hε'pos
    have h2 : ε' * (Cg + 1) = ε := by rw [hε'def]; field_simp
    linarith
  rw [Real.norm_eq_abs] at hbound
  linarith

end Work.FTS.PressureOn.Weyl
