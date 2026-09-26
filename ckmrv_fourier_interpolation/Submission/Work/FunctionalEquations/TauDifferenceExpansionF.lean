import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.DirichletExpansion
import Submission.Work.FunctionalEquations.TauDiffSetup

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## Reindexing a Dirichlet series from `ℕ` to `{m : ℕ // 1 ≤ m}` -/

/-- The bijection `{m : ℕ | 1 ≤ m} ≃ ℕ`, `m ↦ m - 1`. -/
def iciShiftEquiv : Set.Ici (1 : ℕ) ≃ ℕ where
  toFun m := m.1 - 1
  invFun k := ⟨k + 1, Nat.le_add_left 1 k⟩
  left_inv m := by
    apply Subtype.ext
    exact Nat.sub_add_cancel m.2
  right_inv k := by
    show k + 1 - 1 = k
    simp

@[simp] lemma iciShiftEquiv_apply (m : Set.Ici (1 : ℕ)) : iciShiftEquiv m = m.1 - 1 := rfl

/-- Reindexing a Dirichlet series `∑_k c_k e^{2πi(k+1)τ}` as a series over
`{m : ℕ | 1 ≤ m}` with frequencies `m`. -/
lemma hasSum_ici_of_hasSum_nat {c : ℕ → ℂ} {g : ℂ} {τ : ℂ}
    (h : HasSum (fun k : ℕ => c k * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + 1) * τ)) g) :
    HasSum (fun m : Set.Ici (1 : ℕ) => c (m.1 - 1) * dirichletTerm m.1 τ) g := by
  have h1 : HasSum (fun m : Set.Ici (1 : ℕ) => c (m.1 - 1) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m.1 - 1 : ℕ) : ℂ) + 1) * τ)) g := by
    have h2 := (Equiv.hasSum_iff iciShiftEquiv).mpr h
    refine h2.congr_fun fun m => ?_
    simp only [Function.comp_apply, iciShiftEquiv_apply]
  refine h1.congr_fun fun m => ?_
  show c (m.1 - 1) * dirichletTerm m.1 τ =
    c (m.1 - 1) * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((m.1 - 1 : ℕ) : ℂ) + 1) * τ)
  rw [dirichletTerm]
  refine congrArg (fun z : ℂ => c (m.1 - 1) * Complex.exp z) ?_
  rw [Nat.cast_sub m.2]
  ring

/-! ## Elementary properties of the points `t + i y` -/

lemma re_ofReal_add_mul_I (t y : ℝ) : ((t : ℂ) + (y : ℂ) * Complex.I).re = t := by
  simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]

lemma im_ofReal_add_mul_I (t y : ℝ) : ((t : ℂ) + (y : ℂ) * Complex.I).im = y := by
  simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]

/-- `(y/2)^{-β} = 2^β y^{-β}` for `y ≥ 0`. -/
lemma div_two_rpow_neg (y β : ℝ) (hy : 0 ≤ y) : (y / 2) ^ (-β) = (2 : ℝ) ^ β * y ^ (-β) := by
  have hhalf : (0 : ℝ) ≤ (2 : ℝ)⁻¹ := by norm_num
  have h2 : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  have hinv : ((2 : ℝ)⁻¹) ^ (-β) = (2 : ℝ) ^ β := by
    rw [Real.rpow_neg hhalf β]
    exact inv_eq_of_mul_eq_one_right (by rw [← Real.mul_rpow hhalf h2]; norm_num)
  rw [show y / 2 = y * (2 : ℝ)⁻¹ by ring, Real.mul_rpow hy hhalf, hinv]
  ring

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

/-! ## The geometric bound for the norm sum -/

/-- **Norm-sum bound.**  If `‖c k‖ ≤ 2 α (y/2)^{-β} e^{π(k+1)y}` for all `y > 0`, then the
norm sum of the Dirichlet series is bounded by a geometric series. -/
lemma phiBound (c : ℕ → ℂ) {α β : ℝ}
    (hbound : ∀ (k : ℕ) (y : ℝ), 0 < y →
      ‖c k‖ ≤ 2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y))
    {y : ℝ} (hy : 0 < y) :
    dirichletNormSum c y ≤ 2 * α * (y / 2) ^ (-β) *
      (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))) := by
  set r : ℝ := Real.exp (-(Real.pi * y)) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos, hy]
  have hrnorm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0.le]
  have hsummable : Summable fun k : ℕ => r ^ (k + 1) := by
    have h := (summable_geometric_of_norm_lt_one hrnorm).mul_left r
    simpa [pow_succ, mul_comm] using h
  have htsum : ∑' k : ℕ, r ^ (k + 1) = r / (1 - r) := by
    rw [div_eq_mul_inv]
    rw [show (fun k : ℕ => r ^ (k + 1)) = (fun k : ℕ => r * r ^ k) by
      funext k; rw [pow_succ]; ring]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hrnorm]
  have hterm : ∀ k : ℕ, ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y)) ≤
      (2 * α * (y / 2) ^ (-β)) * r ^ (k + 1) := by
    intro k
    have hk := hbound k y hy
    have e1 : r ^ (k + 1) = Real.exp (-(Real.pi * ((k : ℝ) + 1) * y)) := by
      rw [hr, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have e2 : Real.exp (Real.pi * ((k : ℝ) + 1) * y) *
        Real.exp (-(Real.pi * ((k : ℝ) + 1) * y)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y))
        = ‖c k‖ * Real.exp (-(Real.pi * ((k : ℝ) + 1) * y)) *
            Real.exp (-(Real.pi * ((k : ℝ) + 1) * y)) := by
          rw [show -(2 * Real.pi * ((k : ℝ) + 1) * y)
              = -(Real.pi * ((k : ℝ) + 1) * y) + -(Real.pi * ((k : ℝ) + 1) * y) by ring,
            Real.exp_add]
          ring
      _ ≤ (2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y)) *
            Real.exp (-(Real.pi * ((k : ℝ) + 1) * y)) *
            Real.exp (-(Real.pi * ((k : ℝ) + 1) * y)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le)
            (Real.exp_pos _).le
      _ = (2 * α * (y / 2) ^ (-β)) * r ^ (k + 1) := by
          rw [e1]
          calc (2 * α * (y / 2) ^ (-β) * Real.exp (Real.pi * ((k : ℝ) + 1) * y)) *
                Real.exp (-(Real.pi * ((k : ℝ) + 1) * y)) *
                Real.exp (-(Real.pi * ((k : ℝ) + 1) * y))
              = (2 * α * (y / 2) ^ (-β)) * (Real.exp (Real.pi * ((k : ℝ) + 1) * y) *
                  Real.exp (-(Real.pi * ((k : ℝ) + 1) * y))) *
                  Real.exp (-(Real.pi * ((k : ℝ) + 1) * y)) := by ring
            _ = (2 * α * (y / 2) ^ (-β)) * 1 *
                  Real.exp (-(Real.pi * ((k : ℝ) + 1) * y)) := by rw [e2]
            _ = (2 * α * (y / 2) ^ (-β)) * Real.exp (-(Real.pi * ((k : ℝ) + 1) * y)) := by ring
  have hdomsum : Summable fun k : ℕ => ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hterm (hsummable.mul_left _)
  rw [dirichletNormSum]
  calc ∑' k : ℕ, ‖c k‖ * Real.exp (-(2 * Real.pi * ((k : ℝ) + 1) * y))
      ≤ ∑' k : ℕ, (2 * α * (y / 2) ^ (-β)) * r ^ (k + 1) :=
        hdomsum.tsum_le_tsum hterm (hsummable.mul_left _)
    _ = (2 * α * (y / 2) ^ (-β)) * ∑' k : ℕ, r ^ (k + 1) := tsum_mul_left
    _ = 2 * α * (y / 2) ^ (-β) * (Real.exp (-(Real.pi * y)) / (1 - Real.exp (-(Real.pi * y)))) := by
        rw [htsum, hr]

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
