import Submission.Work.FunctionalEquations.TauDifferenceExpansionF
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.TauDiffSetup

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (im_ofReal_add_mul_I)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (norm_exp_neg_two_pi_I_nat)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (dirichletNormSum)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tauDiffM)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (div_two_rpow_neg)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (mul_exp_neg_pi_le_one)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tendsto_rpow_neg_mul_exp)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (tendsto_const_mul_rpow_neg_mul_exp)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (DirichletExpansion)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (norm_le_dirichletNormSum)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (phiBound)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (hasSum_ici_of_hasSum_nat)
end Work.FunctionalEquations

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## The coefficient bound -/

/-- **Coefficient bound.**  The Dirichlet coefficients of `diffF`, given by their integral
formula, satisfy `‖c k‖ ≤ 2 α (y/2)^{-β} e^{π(k+1)y}` for every `y > 0`. -/
lemma coeffBound (S : FunctionalEquationSolution n) (x : E n) (c : ℕ → ℂ)
    (hc : ∀ (k : ℕ) (y : ℝ), 0 < y → c k = ∫ t in (0 : ℝ)..1,
      diffF S x ((t : ℂ) + (y : ℂ) * Complex.I) * Complex.exp
        (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * ((t : ℂ) + (y : ℂ) * Complex.I))))
    {α β : ℝ}
    (hstrip : ∀ (τ : ℂ) (z : E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.F τ z‖ ≤ α * τ.im ^ (-β))
    (k : ℕ) (y : ℝ) (hy : 0 < y) :
    ‖c k‖ ≤ 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y) := by
  have hy2 : 0 < y / 2 := by linarith
  have hnorm : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖diffF S x ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I) * Complex.exp
        (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) *
          ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I)))‖
      ≤ 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y) := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : (0 : ℝ) < t := ht.1
    have ht2 : t ≤ 1 := ht.2
    have hpt : ‖diffF S x ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        2 * α * (y / 2) ^ (-β) := by
      have hpt0 := norm_diffF_le S x hstrip ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I)
        (by rw [im_ofReal_add_mul_I]; exact hy2)
      rwa [im_ofReal_add_mul_I] at hpt0
    rw [norm_mul, norm_exp_neg_two_pi_I_nat k t (y / 2)]
    have hexp : 2 * Real.pi * ((k : ℝ) + 1) * (y / 2) = Real.pi * ((k : ℝ) + 1) * y := by ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_right hpt (Real.exp_pos _).le
  rw [hc k (y / 2) hy2]
  calc ‖∫ t in (0 : ℝ)..1, diffF S x ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I) * Complex.exp
        (-(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) *
          ((t : ℂ) + ((y / 2 : ℝ) : ℂ) * Complex.I)))‖
      ≤ (2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y)) * |1 - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hnorm
    _ = 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y) := by norm_num

/-! ## The comparison bound for `tauDiffF` -/

/-- **The comparison bound.**  The function `tauDiffM α β c` dominates `‖tauDiffF S x τ‖`
on the upper half plane, is bounded by `A y^{-β'}`, and satisfies the decay hypothesis of
`DirichletExpansion`. -/
lemma mBound (S : FunctionalEquationSolution n) (x : E n) (c : ℕ → ℂ)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (hstrip : ∀ (τ : ℂ) (z : E n), 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖S.F τ z‖ ≤ α * τ.im ^ (-β))
    (hc : ∀ τ : ℂ, 0 < τ.im → HasSum (fun k : ℕ =>
      c k * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ)) (diffF S x τ))
    (hPhi : ∀ y : ℝ, 0 < y → dirichletNormSum c y ≤ 2 * α * (y / 2) ^ (-β) *
      (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))))) :
    (∀ τ : ℂ, 0 < τ.im → ‖tauDiffF S x τ‖ ≤ tauDiffM α β c τ.im) ∧
      (∃ A β' : ℝ, 0 ≤ A ∧ 0 ≤ β' ∧ ∀ y : ℝ, 0 < y →
        tauDiffM α β c y ≤ A * y ^ (-β')) ∧
      (∀ m : ℕ, Filter.Tendsto (fun y : ℝ =>
        tauDiffM α β c y * Real.exp (-(2 * Real.pi) * y) ^ m) Filter.atTop (nhds 0)) := by
  have hPhi' : ∀ y : ℝ, 1 ≤ y →
      dirichletNormSum c y ≤ 4 * α * (2 : ℝ) ^ β * y ^ (-β) * Real.exp (-(Real.pi * y)) := by
    intro y hy1
    have hy : 0 < y := lt_of_lt_of_le one_pos hy1
    have h := hPhi y hy
    have hexp1 : Real.exp (-(Real.pi * y)) ≤ 1 / 2 := by
      have h4 : Real.exp (-(Real.pi * y)) ≤ Real.exp (-Real.pi) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos, hy1]
      have h5 : Real.exp (-Real.pi) ≤ 1 / 2 := by
        have htwo : (2 : ℝ) ≤ Real.exp Real.pi := by
          have h3 := Real.add_one_le_exp Real.pi
          linarith [Real.pi_gt_three]
        calc Real.exp (-Real.pi) = (Real.exp Real.pi)⁻¹ := Real.exp_neg _
          _ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr htwo
          _ = 1 / 2 := by norm_num
      linarith
    have hden : 0 < 1 - Real.exp (-(Real.pi * y)) := by linarith
    have h1den : Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y))) ≤
        2 * Real.exp (-(Real.pi * y)) := by
      rw [div_le_iff₀ hden]
      nlinarith [hexp1, Real.exp_pos (-(Real.pi * y))]
    have hdiv : (y / 2) ^ (-β) = (2 : ℝ) ^ β * y ^ (-β) := div_two_rpow_neg y β hy.le
    have hnonneg : 0 ≤ 2 * α * (y / 2) ^ (-β) :=
      mul_nonneg (mul_nonneg (by norm_num) hα)
        (le_of_lt (Real.rpow_pos_of_pos (by linarith) _))
    calc dirichletNormSum c y
        ≤ 2 * α * (y / 2) ^ (-β) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))) := h
      _ ≤ 2 * α * (y / 2) ^ (-β) * (2 * Real.exp (-(Real.pi * y))) :=
          mul_le_mul_of_nonneg_left h1den hnonneg
      _ = 4 * α * (2 : ℝ) ^ β * y ^ (-β) * Real.exp (-(Real.pi * y)) := by
          rw [hdiv]; ring
  have htauM : ∀ y : ℝ, 1 < y → tauDiffM α β c y ≤ (α + 8 * α * (2 : ℝ) ^ β) * y ^ (-β) := by
    intro y hy1
    have hy : 0 < y := by linarith
    have hyy : 0 ≤ y := hy.le
    have hny : ¬ (y ≤ 1) := by linarith
    have hPhiY := hPhi' y hy1.le
    have hpos : 0 < y ^ (-β) := Real.rpow_pos_of_pos hy _
    have h2b : 0 < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
    have hC : 0 ≤ 4 * α * (2 : ℝ) ^ β * y ^ (-β) := by
      have h1 : (0 : ℝ) ≤ α * (2 : ℝ) ^ β := mul_nonneg hα h2b.le
      have h2 : (0 : ℝ) ≤ 4 * (α * (2 : ℝ) ^ β) * y ^ (-β) :=
        mul_nonneg (mul_nonneg (by norm_num) h1) hpos.le
      nlinarith [h2]
    have hye : (1 + y) * Real.exp (-(Real.pi * y)) ≤ 2 := by
      have h1 : y * Real.exp (-(Real.pi * y)) ≤ 1 := mul_exp_neg_pi_le_one hyy
      have h2 : Real.exp (-(Real.pi * y)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [Real.pi_pos, hy]
      nlinarith [h1, h2, Real.exp_pos (-(Real.pi * y))]
    rw [show tauDiffM α β c y = α * y ^ (-β) + (1 + y) * dirichletNormSum c y by
      simp [tauDiffM, hny]]
    have hstep : (1 + y) * dirichletNormSum c y ≤
        (1 + y) * (4 * α * (2 : ℝ) ^ β * y ^ (-β) * Real.exp (-(Real.pi * y))) :=
      mul_le_mul_of_nonneg_left hPhiY (by linarith)
    have hstep2 : (1 + y) * (4 * α * (2 : ℝ) ^ β * y ^ (-β) * Real.exp (-(Real.pi * y))) ≤
        8 * α * (2 : ℝ) ^ β * y ^ (-β) := by
      calc (1 + y) * (4 * α * (2 : ℝ) ^ β * y ^ (-β) * Real.exp (-(Real.pi * y)))
          = (4 * α * (2 : ℝ) ^ β * y ^ (-β)) * ((1 + y) * Real.exp (-(Real.pi * y))) := by ring
        _ ≤ (4 * α * (2 : ℝ) ^ β * y ^ (-β)) * 2 := mul_le_mul_of_nonneg_left hye hC
        _ = 8 * α * (2 : ℝ) ^ β * y ^ (-β) := by ring
    calc α * y ^ (-β) + (1 + y) * dirichletNormSum c y
        ≤ α * y ^ (-β) + 8 * α * (2 : ℝ) ^ β * y ^ (-β) :=
          add_le_add (le_refl _) (le_trans hstep hstep2)
      _ = (α + 8 * α * (2 : ℝ) ^ β) * y ^ (-β) := by ring
  refine ⟨?_, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨τ', him, hre1, hre2, heq⟩ := exists_periodic_reduce (tauDiffF_periodic S x) τ hτ
    have hτ' : 0 < τ'.im := by rw [him]; exact hτ
    have hmain := norm_tauDiffF_le S x hstrip hτ' hre1 hre2
    rw [← heq, ← him]
    by_cases hy1 : τ'.im ≤ 1
    · have hg := norm_diffF_le_of_strip S x hstrip hτ' hre1 hre2
      have hpos : 0 < τ'.im ^ (-β) := Real.rpow_pos_of_pos hτ' _
      have h5 : α * τ'.im ^ (-β) + (1 + τ'.im) * ‖diffF S x τ'‖ ≤ 5 * α * τ'.im ^ (-β) := by
        have h1y : 1 + τ'.im ≤ 2 := by linarith
        have h2 : (1 + τ'.im) * (2 * α * τ'.im ^ (-β)) ≤ 4 * α * τ'.im ^ (-β) := by
          calc (1 + τ'.im) * (2 * α * τ'.im ^ (-β))
              ≤ 2 * (2 * α * τ'.im ^ (-β)) := by
                refine mul_le_mul_of_nonneg_right h1y ?_
                exact mul_nonneg (mul_nonneg (by norm_num) hα) hpos.le
            _ = 4 * α * τ'.im ^ (-β) := by ring
        have h3 : (1 + τ'.im) * ‖diffF S x τ'‖ ≤ (1 + τ'.im) * (2 * α * τ'.im ^ (-β)) :=
          mul_le_mul_of_nonneg_left hg (by linarith)
        linarith
      calc ‖tauDiffF S x τ'‖ ≤ 5 * α * τ'.im ^ (-β) := le_trans hmain h5
        _ = tauDiffM α β c τ'.im := by simp [tauDiffM, hy1]
    · have hg : ‖diffF S x τ'‖ ≤ dirichletNormSum c τ'.im :=
        norm_le_dirichletNormSum (c := c) (g := diffF S x) hc hτ'
      have hsum : α * τ'.im ^ (-β) + (1 + τ'.im) * ‖diffF S x τ'‖ ≤
          α * τ'.im ^ (-β) + (1 + τ'.im) * dirichletNormSum c τ'.im :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hg (by linarith))
      calc ‖tauDiffF S x τ'‖ ≤ α * τ'.im ^ (-β) + (1 + τ'.im) * ‖diffF S x τ'‖ := hmain
        _ ≤ α * τ'.im ^ (-β) + (1 + τ'.im) * dirichletNormSum c τ'.im := hsum
        _ = tauDiffM α β c τ'.im := by simp [tauDiffM, hy1]
  · refine ⟨5 * α + 8 * α * (2 : ℝ) ^ β, β, ?_, hβ.le, ?_⟩
    · positivity
    · intro y hy
      by_cases hy1 : y ≤ 1
      · have hyy : tauDiffM α β c y = 5 * α * y ^ (-β) := by simp [tauDiffM, hy1]
        rw [hyy]
        have hpos : 0 ≤ y ^ (-β) := le_of_lt (Real.rpow_pos_of_pos hy _)
        have hle : 5 * α ≤ 5 * α + 8 * α * (2 : ℝ) ^ β := by
          have h2b : 0 ≤ (2 : ℝ) ^ β := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
          have : 0 ≤ 8 * α * (2 : ℝ) ^ β := mul_nonneg (by positivity) h2b
          linarith
        exact mul_le_mul_of_nonneg_right hle hpos
      · have h1 : tauDiffM α β c y ≤ (α + 8 * α * (2 : ℝ) ^ β) * y ^ (-β) :=
          htauM y (by linarith)
        have h2 : (α + 8 * α * (2 : ℝ) ^ β) ≤ 5 * α + 8 * α * (2 : ℝ) ^ β := by linarith
        exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.rpow_pos_of_pos hy _)))
  · intro m
    have hev : (fun y : ℝ => tauDiffM α β c y * Real.exp (-(2 * Real.pi) * y) ^ m)
        =ᶠ[Filter.atTop] fun y : ℝ =>
          (α * y ^ (-β) + (1 + y) * dirichletNormSum c y) * Real.exp (-(2 * Real.pi) * y) ^ m := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
      rw [show tauDiffM α β c y = α * y ^ (-β) + (1 + y) * dirichletNormSum c y by
        simp [tauDiffM, (by linarith : ¬ (y ≤ 1))]]
    refine Filter.Tendsto.congr' hev.symm ?_
    have hlim : Filter.Tendsto (fun y : ℝ =>
        (α + 8 * α * (2 : ℝ) ^ β) * (y ^ (-β) * Real.exp (-(2 * Real.pi) * y) ^ m))
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_rpow_neg_mul_exp hβ m).const_mul (α + 8 * α * (2 : ℝ) ^ β)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy1
    have hy : 0 < y := by linarith
    have hM : α * y ^ (-β) + (1 + y) * dirichletNormSum c y ≤ (α + 8 * α * (2 : ℝ) ^ β) * y ^ (-β) := by
      rw [← show tauDiffM α β c y = α * y ^ (-β) + (1 + y) * dirichletNormSum c y by
        simp [tauDiffM, (by linarith : ¬ (y ≤ 1))]]
      exact htauM y hy1
    have hnonneg : 0 ≤ α * y ^ (-β) + (1 + y) * dirichletNormSum c y := by
      have h1 : 0 ≤ α * y ^ (-β) := mul_nonneg hα (le_of_lt (Real.rpow_pos_of_pos hy _))
      have h2 : 0 ≤ dirichletNormSum c y := tsum_nonneg fun k => by positivity
      nlinarith [h1, h2, hy]
    have hexp : 0 ≤ Real.exp (-(2 * Real.pi) * y) ^ m := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnonneg hexp)]
    calc (α * y ^ (-β) + (1 + y) * dirichletNormSum c y) * Real.exp (-(2 * Real.pi) * y) ^ m
        ≤ ((α + 8 * α * (2 : ℝ) ^ β) * y ^ (-β)) * Real.exp (-(2 * Real.pi) * y) ^ m :=
          mul_le_mul_of_nonneg_right hM hexp
      _ = (α + 8 * α * (2 : ℝ) ^ β) * (y ^ (-β) * Real.exp (-(2 * Real.pi) * y) ^ m) := by ring

/-! ## The Dirichlet expansion of `F(τ,x) - τ (F(τ+1,x) - F(τ,x))` -/

theorem TauDifferenceExpansionF {n : ℕ} [NeZero n]
    (S : Work.FE.FunctionalEquationSolution n) (x : Work.FE.E n) :
    ∃ a : Set.Ici (1 : ℕ) → ℂ,
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun m : Set.Ici (1 : ℕ) =>
          a m * Work.FE.dirichletTerm m.1 τ)
        (S.F τ x - τ * (S.F (τ + 1) x - S.F τ x))) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (y : ℝ), 0 < y →
        a m = ∫ t in (0 : ℝ)..1,
          (S.F ((t : ℂ) + (y : ℂ) * Complex.I) x
            - ((t : ℂ) + (y : ℂ) * Complex.I) * (S.F ((t : ℂ) + (y : ℂ) * Complex.I + 1) x
              - S.F ((t : ℂ) + (y : ℂ) * Complex.I) x)) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
              * ((t : ℂ) + (y : ℂ) * Complex.I)))) := by
  obtain ⟨α, β, hα, hβ, hstrip⟩ := S.uniform_F
  have hM1 : ∀ τ : ℂ, 0 < τ.im → ‖diffF S x τ‖ ≤ (fun y : ℝ => 2 * α * y ^ (-β)) τ.im :=
    fun τ hτ => norm_diffF_le S x hstrip τ hτ
  have hM2 : ∃ A β' : ℝ, 0 ≤ A ∧ 0 ≤ β' ∧ ∀ y : ℝ, 0 < y →
      (fun y : ℝ => 2 * α * y ^ (-β)) y ≤ A * y ^ (-β') :=
    ⟨2 * α, β, by linarith, hβ.le, fun y _ => le_refl _⟩
  have hM3 : ∀ m : ℕ, Tendsto (fun y : ℝ =>
      (fun y : ℝ => 2 * α * y ^ (-β)) y * Real.exp (-(2 * Real.pi) * y) ^ m) atTop (𝓝 0) :=
    fun m => tendsto_const_mul_rpow_neg_mul_exp α β hβ m
  obtain ⟨c, hc_exp, hc_int⟩ := DirichletExpansion (diffF S x) (diffF_periodic S x)
    (diffF_differentiableOn S x) (fun y : ℝ => 2 * α * y ^ (-β)) hM1 hM2 hM3
  have hcoeff : ∀ (k : ℕ) (y : ℝ), 0 < y →
      ‖c k‖ ≤ 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y) :=
    fun k y hy => coeffBound S x c hc_int hstrip k y hy
  have hPhi : ∀ y : ℝ, 0 < y → dirichletNormSum c y ≤ 2 * α * (y / 2) ^ (-β) *
      (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))) :=
    fun y hy => phiBound c hcoeff hy
  obtain ⟨hMle, hMbd, hMdec⟩ := mBound S x c hα hβ hstrip hc_exp hPhi
  obtain ⟨d, hd_exp, hd_int⟩ := DirichletExpansion (tauDiffF S x) (tauDiffF_periodic S x)
    (tauDiffF_differentiableOn S x) (tauDiffM α β c) hMle hMbd hMdec
  refine ⟨fun m => d (m.1 - 1), ?_, ?_⟩
  · intro τ hτ
    exact hasSum_ici_of_hasSum_nat (hd_exp τ hτ)
  · intro m y hy
    have h := hd_int (m.1 - 1) y hy
    simp only []
    rw [h]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    simp only [tauDiffF_apply]
    refine congrArg (fun z : ℂ => (S.F ((t : ℂ) + (y : ℂ) * Complex.I) x
        - ((t : ℂ) + (y : ℂ) * Complex.I) * (S.F ((t : ℂ) + (y : ℂ) * Complex.I + 1) x
          - S.F ((t : ℂ) + (y : ℂ) * Complex.I) x)) * Complex.exp z) ?_
    rw [Nat.cast_sub m.2]
    ring

end

end Work.FunctionalEquations


end Work.CKFinal.Shadow
