import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.H2.DivQ.hardyA_le_W
import Submission.Work.FTS.H2.DivQ.divSinPrimitive
import Submission.Work.FTS.H2.DivQ.integrableOn_Ioc_of_trunc
import Submission.Work.FTS.EllipticEst.remov.HardyFin.Basic
import Submission.Work.FTS.EllipticEst.remov.HardyFin.TruncFin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter
open scoped Topology

/-- **Finite-order Hardy division (Elgindi's Lemma 2 / Hilbert-type inequality at finite
smoothness).**  For `j : ℕ`, `γ > -1`, `x₁ > 0` and `f` of class `C^{j+2}` on `(0,x₁]` with
`f → 0` at `0⁺` and `∫_0^{x₁} x^{2j-γ}(f^{(j+1)})² < ∞`:

`∫_0^{x₁} x^{2j-γ}((f/x)^{(j)})² ≤ C(1+γ)^{-2} ∫_0^{x₁} x^{2j-γ}(f^{(j+1)})²`

and the left-hand integrand is `IntegrableOn (Ioc 0 x₁)`.

The `C^∞`-smoothness ancestor of this statement is `Work.FTS.H2.DivQ.hardyA_le_W`
(`ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁)`); here `⊤` is replaced by the finite order `j + 2`,
which is what the proof needs (continuity of `f/x` and its iterated derivatives up to order
`j+1`).  Suggested route: verbatim adaptation of the proof of `hardyA_le_W` (primitive identity
`x^{j+1}(f/x)^{(j)} = ∫_0^x s^j f^{(j+1)}`, pointwise quantitative bound
`x^{2j+1-γ}((f/x)^{(j)})² ≤ (1+γ)^{-1}∫_0^x s^{2j-γ}(f^{(j+1)})²`, sharp integration by parts with
constant `4/(1+γ)²`, and the truncation argument of
`Work.FTS.H2.DivQ.integrableOn_Ioc_of_trunc`). -/
theorem hardyDiv_fin (j : ℕ) (γ : ℝ) (hγ : -1 < γ) (x₁ : ℝ) (hx₁ : 0 < x₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ,
      ContDiffOn ℝ (j + 2) f (Set.Ioc 0 x₁) →
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (j : ℝ) - γ) * (iteratedDeriv (j + 1) f x) ^ 2)
        (Set.Ioc 0 x₁) →
      MeasureTheory.IntegrableOn
        (fun x : ℝ => x ^ (2 * (j : ℝ) - γ)
          * (iteratedDeriv j (fun y : ℝ => f y / y) x) ^ 2) (Set.Ioc 0 x₁)
      ∧ (∫ x in (0 : ℝ)..x₁, x ^ (2 * (j : ℝ) - γ)
            * (iteratedDeriv j (fun y : ℝ => f y / y) x) ^ 2)
          ≤ C / (1 + γ) ^ 2 * (∫ x in (0 : ℝ)..x₁,
              x ^ (2 * (j : ℝ) - γ) * (iteratedDeriv (j + 1) f x) ^ 2) := by
  refine ⟨6, by norm_num, ?_⟩
  intro f hf hf0 hB
  -- the hypothesis `ContDiffOn ℝ (j + 2) f` (order `↑j + 2 : WithTop ℕ∞`) in the form
  -- `ContDiffOn ℝ ((j+2 : ℕ) : WithTop ℕ∞) f`
  have hf' : ContDiffOn ℝ (((j + 2 : ℕ)) : WithTop ℕ∞) f (Set.Ioc 0 x₁) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hf
  set v : ℝ → ℝ := fun x => iteratedDeriv j (fun y : ℝ => f y / y) x with hv
  set u : ℝ → ℝ := fun x => x ^ (2 * (j : ℝ) - γ) * v x ^ 2 with hu
  set ua : ℝ → ℝ := fun x => |u x| with hua
  set w : ℝ → ℝ := fun x => x ^ (2 * (j : ℝ) - γ) * (iteratedDeriv (j + 1) f x) ^ 2 with hw
  set Btot : ℝ := ∫ x in (0 : ℝ)..x₁, w x with hBtot
  have hgm : ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) (fun z : ℝ => f z / z) (Set.Ioo 0 x₁) := by
    have h1 : ContDiffOn ℝ (((j + 2 : ℕ)) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
      hf'.mono Set.Ioo_subset_Ioc_self
    have h2 : ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) f (Set.Ioo 0 x₁) :=
      h1.of_le (by exact_mod_cast (show j ≤ j + 2 by omega))
    have hid : ContDiffOn ℝ ((j : ℕ) : WithTop ℕ∞) (fun y : ℝ => y) (Set.Ioo 0 x₁) :=
      contDiffOn_id
    have hdiv := h2.div hid
      (fun x hx => by simp only [Set.mem_Ioo] at hx; exact ne_of_gt hx.1)
    have hfun : (f / fun y : ℝ => y) = fun y : ℝ => f y / y := by
      funext y; rw [Pi.div_apply]
    rwa [hfun] at hdiv
  have hvcont : ContinuousOn v (Set.Ioo 0 x₁) := by
    rw [hv]
    exact Work.FTS.EllipticEst.remov.HardyFin.continuousOn_iteratedDeriv_Ioo_fin' hgm le_rfl
  have hucont : ContinuousOn u (Set.Ioo 0 x₁) := by
    rw [hu]
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1))).mul (hvcont.pow 2)
  have huacont : ContinuousOn ua (Set.Ioo 0 x₁) := by
    rw [hua]
    exact hucont.abs
  have htrunc0 :=
    Work.FTS.EllipticEst.remov.HardyFin.hardyA_trunc_bound_fin j γ x₁ hx₁ hγ (j + 2) le_rfl
      f hf' hf0 hB
  have htrunc : ∀ y x : ℝ, 0 < y → y < x → x < x₁ →
      (∫ t in y..x, ua t) ≤ 6 * Btot / (1 + γ) ^ 2 := by
    intro y x hy hyx hxx₁
    have heq : (∫ t in y..x, ua t) = ∫ t in y..x, u t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hyx.le] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hy ht.1
      simp only [hua]
      exact abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (sq_nonneg _))
    rw [heq]
    exact htrunc0 y x hy hyx hxx₁
  obtain ⟨hua_int, hua_bound⟩ :=
    Work.FTS.H2.DivQ.integrableOn_Ioc_of_trunc hx₁ (fun t => abs_nonneg (u t)) huacont htrunc
  have hu_int : MeasureTheory.IntegrableOn u (Set.Ioc 0 x₁) := by
    refine hua_int.congr_fun (fun t ht => ?_) measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    exact abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht0 _).le (sq_nonneg _))
  refine ⟨?_, ?_⟩
  · exact hu_int
  · have heq_final : (∫ t in (0 : ℝ)..x₁, u t) = ∫ t in (0 : ℝ)..x₁, ua t := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with t
      intro ht
      rw [Set.uIoc_of_le hx₁.le] at ht
      simp only [hua]
      exact (abs_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos ht.1 _).le (sq_nonneg _))).symm
    calc (∫ t in (0 : ℝ)..x₁, u t) = ∫ t in (0 : ℝ)..x₁, ua t := heq_final
      _ ≤ 6 * Btot / (1 + γ) ^ 2 := hua_bound
      _ = 6 / (1 + γ) ^ 2 * Btot := by ring

end Work.FTS.EllipticEst.remov
