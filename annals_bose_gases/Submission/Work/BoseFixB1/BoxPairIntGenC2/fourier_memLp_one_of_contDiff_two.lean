import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Submission.Work.BoseFixB1.BoxPairIntGenC2.FourierLpAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `𝓕 f ∈ L¹` for `f` of class `C²` with compact support on `ℝ³`

The Fourier transform of a `C²` function with compact support on `ℝ³` decays like `‖ξ‖⁻²`,
which by itself is *not* integrable in dimension three.  The saving is Plancherel: the weight
`‖ξ‖⁴ ‖𝓕 f ξ‖²` is integrable, because `‖ξ‖² 𝓕 f` is (up to constants) the Fourier transform
of the trace of the Hessian of `f`, a continuous compactly supported function.  Writing

  `‖𝓕 f ξ‖ = A ξ * G ξ`,  `A ξ = (1 + ‖ξ‖²)⁻¹`,  `G ξ = (1 + ‖ξ‖²) ‖𝓕 f ξ‖`,

both factors are square integrable (`∫ A² = ∫ (1+‖ξ‖²)⁻² < ∞` in dimension `3`, and
`∫ G² < ∞` by Plancherel for `f` and for the Hessian trace), and `2 ‖𝓕 f ξ‖ ≤ A ξ² + G ξ²`.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace Real

namespace Work.BoseFixB1.BoxPairIntGenC2

namespace Prep

/-- Short name for the ambient Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The space of real-bilinear continuous maps `ℝ³ × ℝ³ → ℂ`, i.e. the values of
`iteratedFDeriv ℝ 2 f`. -/
abbrev Hess : Type := ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E3) ℂ

/-- Evaluation of a continuous bilinear map at a fixed pair of vectors is continuous. -/
lemma continuous_hess_eval (m : Fin 2 → E3) : Continuous (fun φ : Hess => φ m) :=
  AddMonoidHomClass.continuous_of_bound (ContinuousMultilinearMap.applyAddHom m) (∏ i, ‖m i‖)
    (fun φ => by
      have h := ContinuousMultilinearMap.le_opNorm φ m
      rw [show ‖φ‖ * ∏ i, ‖m i‖ = (∏ i, ‖m i‖) * ‖φ‖ from mul_comm _ _] at h
      exact h)

/-- **Weighted `L²` bound for the Fourier transform.**  For `f : ℝ³ → ℂ` of class `C²` with
compact support, the function `ξ ↦ ‖ξ‖⁴ ‖𝓕 f ξ‖²` is integrable.  This is Plancherel's theorem
applied to the trace of the Hessian of `f`. -/
theorem integrable_pow_four_mul_fourier_sq (f : E3 → ℂ) (hf : ContDiff ℝ 2 f)
    (hs : HasCompactSupport f) :
    Integrable (fun ξ : E3 => ‖ξ‖ ^ 4 * ‖𝓕 f ξ‖ ^ 2) (volume : Measure E3) := by
  classical
  set b : OrthonormalBasis (Fin 3) ℝ E3 := EuclideanSpace.basisFun (Fin 3) ℝ with hb
  have hint : ∀ n : ℕ, (n : ℕ∞) ≤ (2 : ℕ∞) →
      Integrable (iteratedFDeriv ℝ n f) (volume : Measure E3) := by
    intro n hn
    exact (hf.continuous_iteratedFDeriv (m := n) (by simpa using hn)).integrable_of_hasCompactSupport
      (hs.iteratedFDeriv n)
  set L : E3 → ℂ := fun x => ∑ j : Fin 3, iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j) with hLdef
  have hLcont : Continuous L := by
    rw [hLdef]
    exact continuous_finsetSum _ (fun j _ =>
      (continuous_hess_eval (m := fun _ : Fin 2 => b j)).comp
        (hf.continuous_iteratedFDeriv (m := 2) le_rfl))
  have hLsupp : HasCompactSupport L := by
    rw [hLdef]
    exact (hs.iteratedFDeriv 2).comp_left
      (g := fun φ : Hess => ∑ j : Fin 3, φ (fun _ : Fin 2 => b j)) (by simp)
  have hL1 : MemLp L 1 (volume : Measure E3) := hLcont.memLp_of_hasCompactSupport hLsupp
  have hL2 : MemLp L 2 (volume : Measure E3) := hLcont.memLp_of_hasCompactSupport hLsupp
  have hPlanch : Integrable (fun ξ : E3 => ‖𝓕 L ξ‖ ^ 2) (volume : Measure E3) :=
    integrable_norm_fourier_sq' hL1 hL2
  have hdf : ∀ j : Fin 3,
      Integrable (fun x : E3 => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j))
        (volume : Measure E3) := by
    intro j
    have hc : Continuous (fun x : E3 => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j)) :=
      (continuous_hess_eval (m := fun _ : Fin 2 => b j)).comp
        (hf.continuous_iteratedFDeriv (m := 2) le_rfl)
    have hsupp : HasCompactSupport
        (fun x : E3 => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j)) :=
      (hs.iteratedFDeriv 2).comp_left (g := fun φ : Hess => φ (fun _ : Fin 2 => b j)) (by simp)
    exact hc.integrable_of_hasCompactSupport hsupp
  have hscal : (-(2 * (Real.pi : ℂ) * Complex.I)) ^ 2 = ((-(4 * Real.pi ^ 2) : ℝ) : ℂ) := by
    rw [show (-(2 * (Real.pi : ℂ) * Complex.I)) = -(((2 * Real.pi : ℝ)) : ℂ) * Complex.I by
      push_cast; ring]
    rw [mul_pow, Complex.I_sq]
    push_cast
    ring
  have hterm : ∀ (ξ : E3) (j : Fin 3),
      𝓕 (fun x => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j)) ξ
        = ((-(4 * π ^ 2 * ⟪ξ, b j⟫ ^ 2)) : ℝ) • 𝓕 f ξ := by
    intro ξ j
    rw [← Real.fourier_continuousMultilinearMap_apply (f := iteratedFDeriv ℝ 2 f)
      (m := fun _ : Fin 2 => b j) (v := ξ) (hint 2 le_rfl)]
    rw [Real.fourier_iteratedFDeriv (N := (2 : ℕ∞)) hf (fun n hn => hint n hn) (n := 2) le_rfl]
    rw [VectorFourier.fourierPowSMulRight_apply]
    have hprod : (∏ i : Fin 2, (-innerSL ℝ) ξ (b j)) = ⟪ξ, b j⟫ ^ 2 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      simp only [neg_apply, innerSL_apply_apply, neg_sq]
    rw [hprod, hscal, smul_eq_mul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hId : ∀ ξ : E3, 𝓕 L ξ = ((-(4 * π ^ 2 * ‖ξ‖ ^ 2)) : ℝ) • 𝓕 f ξ := by
    intro ξ
    have h1 : 𝓕 L ξ
        = ∑ j : Fin 3, 𝓕 (fun x => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j)) ξ := by
      rw [hLdef]
      exact Commons.Analysis.Fourier.fourier_finsetSum Finset.univ
        (fun j => fun x : E3 => iteratedFDeriv ℝ 2 f x (fun _ : Fin 2 => b j))
        (fun j _ => hdf j) ξ
    rw [h1, Finset.sum_congr rfl (fun j _ => hterm ξ j), ← Finset.sum_smul]
    congr 1
    calc ∑ j : Fin 3, (-(4 * π ^ 2 * ⟪ξ, b j⟫ ^ 2))
        = (-(4 * π ^ 2)) * ∑ j : Fin 3, ⟪ξ, b j⟫ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = (-(4 * π ^ 2)) * ‖ξ‖ ^ 2 := by rw [OrthonormalBasis.sum_sq_inner_left b ξ]
      _ = -(4 * π ^ 2 * ‖ξ‖ ^ 2) := by ring
  have hNorm : ∀ ξ : E3, ‖ξ‖ ^ 4 * ‖𝓕 f ξ‖ ^ 2 = ((4 * π ^ 2) ^ 2)⁻¹ * ‖𝓕 L ξ‖ ^ 2 := by
    intro ξ
    rw [hId ξ, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2)]
    have hπ : (4 * π ^ 2 : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  refine (hPlanch.const_mul ((4 * π ^ 2) ^ 2)⁻¹).congr ?_
  filter_upwards with ξ
  exact (hNorm ξ).symm

/-- **`L¹` from `L²` plus weighted-square integrability.**  If `F ∈ L²(ℝ³)` and
`ξ ↦ ‖ξ‖⁴ ‖F ξ‖²` is integrable, then `F ∈ L¹(ℝ³)`.  Indeed, writing
`F ξ = A ξ * G ξ` with `A ξ = (1+‖ξ‖²)⁻¹` and `G ξ = (1+‖ξ‖²)‖F ξ‖`, both `A` and `G` are in
`L²` and `2‖F ξ‖ ≤ A ξ² + G ξ²`. -/
theorem memLp_one_of_memLp_two_and_pow_four {F : E3 → ℂ}
    (h2 : MemLp F 2 (volume : Measure E3))
    (h4 : Integrable (fun ξ : E3 => ‖ξ‖ ^ 4 * ‖F ξ‖ ^ 2) (volume : Measure E3)) :
    MemLp F 1 (volume : Measure E3) := by
  set A : E3 → ℝ := fun ξ => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ with hA
  set G : E3 → ℝ := fun ξ => (1 + ‖ξ‖ ^ 2) * ‖F ξ‖ with hG
  have hnorm2 : Integrable (fun ξ : E3 => ‖F ξ‖ ^ 2) (volume : Measure E3) :=
    (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
  have hA2 : Integrable (fun ξ : E3 => A ξ ^ 2) (volume : Measure E3) := by
    have hbase : Integrable (fun ξ : E3 => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)))
        (volume : Measure E3) := by
      have h := integrable_rpow_neg_one_add_norm_sq (E := E3) (μ := (volume : Measure E3)) (r := 4)
        (by rw [finrank_euclideanSpace_fin]; norm_num)
      convert h using 2 with ξ
      norm_num
    refine hbase.congr ?_
    filter_upwards with ξ
    rw [hA]
    rw [show ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 : ℝ)) = (((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) ^ 2 by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]]
  have hG2 : Integrable (fun ξ : E3 => G ξ ^ 2) (volume : Measure E3) := by
    have hdom : Integrable (fun ξ : E3 => 2 * ‖F ξ‖ ^ 2 + 2 * (‖ξ‖ ^ 4 * ‖F ξ‖ ^ 2))
        (volume : Measure E3) := (hnorm2.const_mul 2).add (h4.const_mul 2)
    refine hdom.mono' ?_ ?_
    · have hc : AEStronglyMeasurable (fun ξ : E3 => (1 : ℝ) + ‖ξ‖ ^ 2) (volume : Measure E3) :=
        (continuous_const.add (continuous_norm.pow 2)).aestronglyMeasurable
      exact (hc.mul h2.aestronglyMeasurable.norm).pow 2
    · filter_upwards with ξ
      rw [hG]
      have hb : (1 + ‖ξ‖ ^ 2) ^ 2 ≤ 2 * (1 + (‖ξ‖ ^ 2) ^ 2) := by
        nlinarith [sq_nonneg (‖ξ‖ ^ 2 - 1)]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((1 + ‖ξ‖ ^ 2) * ‖F ξ‖) ^ 2), mul_pow]
      calc (1 + ‖ξ‖ ^ 2) ^ 2 * ‖F ξ‖ ^ 2
          ≤ (2 * (1 + (‖ξ‖ ^ 2) ^ 2)) * ‖F ξ‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = 2 * ‖F ξ‖ ^ 2 + 2 * (‖ξ‖ ^ 4 * ‖F ξ‖ ^ 2) := by ring
  have hAG : Integrable (fun ξ : E3 => (A ξ ^ 2 + G ξ ^ 2) / 2) (volume : Measure E3) :=
    (hA2.add hG2).div_const 2
  refine MemLp.of_le (memLp_one_iff_integrable.2 hAG) h2.aestronglyMeasurable ?_
  filter_upwards with ξ
  have key : ‖F ξ‖ ≤ A ξ ^ 2 / 2 + G ξ ^ 2 / 2 := by
    have hsplit : ‖F ξ‖ = A ξ * G ξ := by
      simp only [hA, hG]
      field_simp
    rw [hsplit]
    nlinarith [sq_nonneg (A ξ - G ξ)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
    show (A ξ ^ 2 + G ξ ^ 2) / 2 = A ξ ^ 2 / 2 + G ξ ^ 2 / 2 from by ring]
  exact key

end Prep

theorem fourier_memLp_one_of_contDiff_two
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    MeasureTheory.MemLp (FourierTransform.fourier f) 1
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  have h1 : MemLp f 1 (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    memLp_one_iff_integrable.2 (hf.continuous.integrable_of_hasCompactSupport hs)
  have h2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    hf.continuous.memLp_of_hasCompactSupport hs
  exact Prep.memLp_one_of_memLp_two_and_pow_four (memLp_two_fourier h1 h2)
    (Prep.integrable_pow_four_mul_fourier_sq f hf hs)

end Work.BoseFixB1.BoxPairIntGenC2
