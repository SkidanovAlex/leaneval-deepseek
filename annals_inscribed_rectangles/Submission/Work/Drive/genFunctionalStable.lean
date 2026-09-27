import Mathlib
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.exists_generic_functional_family

/-!
# Stably generic functionals along a curve, and the smallness of the class perturbation

The reference factor `(F1)` of `hn2` (`Work.Drive.odd_coreSideCountPt_reference_mixed`) needs, at the
*perturbed* chart `chartPert τ ∘ Q'` and with the reference plane perturbed by `σ`, that the
transported functional

> `ℓ_τσ := linFun (φ.trans (classEquiv σ))` restricted to the lift `classEquiv τ ∘ V`

have a nonzero value at `t = 0` and only simple (hence finitely many) zeros on `[0,1]`.  This file
supplies the two analytical inputs of the *circularity-free* resolution of that obligation (see
`F1_GENERICITY_RESOLUTION.md`):

* **`Work.Drive.GenAlong`** — the predicate "the functional `ℓ` is generic along the curve `V`",
  which is literally the hypothesis list `hV0`/`hfin`/`hreg` of
  `Work.Drive.odd_coreSideCountPt_reference` (the `hder` clause is automatic when `V` is smooth);
* **`Work.Drive.exists_genAlong_family`** — the finite-family existence theorem
  `Work.Drive.exists_generic_functional_family` restated in that form;
* **`Work.Drive.norm_classEquiv_sub_one_le`** and its inverse counterpart — the class perturbation
  `classEquiv t = 1 + classGen t` is `O(‖t‖)`-close to the identity, *with an explicit constant*, and
  its inverse is close to the identity for small `t`.

The resolution of the `(F1)` obligation rests on the observation that the *unperturbed* functional
`ℓ = linFun φ` may be chosen **before** the perturbation parameters: the family form
`exists_genAlong_family` produces a single `ℓ` generic along the two class lifts `V 0`, `V 1` of the
rotated configuration charts, the reference plane is then `linPlaneChart φ lam hlampos`, the
reference-triple genericity `Work.Drive.exists_meet3Hyp_and_goodAt_refTriple` supplies the parameters
`τ` of arbitrarily small norm, and the estimates below carry the genericity of `ℓ` over to the
transported functional `linFun (φ ∘ (classEquiv σ)⁻¹ ∘ classEquiv τ)` — because the transport
differs from `ℓ` by at most `‖ℓ‖ · ‖(classEquiv σ)⁻¹ ∘ classEquiv τ - 1‖`, which is
`O(‖τ‖ + ‖σ‖)`, and `GenAlong` is *open* (`Work.Drive.genAlong_open`, delegated and living in
`Submission/Work/Drive/genAlong_open.lean`).

The corresponding identity in `linFun` is `Work.Drive.linFun_trans_classEquiv`
(`Drive/chartPertTransfer.lean`):

> `linFun (φ.trans (classEquiv σ)) (classEquiv τ w) = linFun φ ((classEquiv σ)⁻¹ (classEquiv τ w))`.
-/

namespace Work.Drive

open Set
open scoped ContDiff Topology

noncomputable section

/-! ## 1. The predicate and the existence theorem in `GenAlong` form -/

/-- **A functional is *generic along a curve*** if it does not vanish at the initial parameter and its
zero set on the unit interval is finite, with every zero simple.

This is exactly the hypothesis triple `hV0`/`hfin`/`hreg` of
`Work.Drive.odd_coreSideCountPt_reference` (and of
`Work.Drive.odd_coreSideCountPt_reference_mixed`), with `hVne`/`hVcls`/`hder`/`hκ`/`hesse` kept
separate because they are properties of the lift rather than of the functional. -/
def GenAlong (ℓ : Eucl 3 →L[ℝ] ℝ) (V : ℝ → Eucl 3) : Prop :=
  ℓ (V 0) ≠ 0 ∧ ({t : ℝ | t ∈ Icc 0 1 ∧ ℓ (V t) = 0}).Finite ∧
    (∀ t ∈ Icc 0 1, ℓ (V t) = 0 → deriv (fun s : ℝ => ℓ (V s)) t ≠ 0)

/-- **The finite-family generic functional, in `GenAlong` form.** -/
theorem exists_genAlong_family {ι : Type*} [Fintype ι] (V : ι → ℝ → Eucl 3)
    (hVs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i))
    (hVne : ∀ i t, t ∈ Icc 0 1 → V i t ≠ 0) :
    ∃ ℓ : Eucl 3 →L[ℝ] ℝ, ℓ ≠ 0 ∧ ∀ i, GenAlong ℓ (V i) := by
  obtain ⟨ℓ, hℓ, hgood⟩ := exists_generic_functional_family ι V hVs hVne
  exact ⟨ℓ, hℓ, fun i => ⟨(hgood i).1, (hgood i).2.1, (hgood i).2.2⟩⟩

/-! ## 2. The class perturbation is close to the identity near the identity parameter -/

/-- The explicit constant of the estimates: `‖classGen t‖ ≤ C ‖t‖`. -/
def classGenC : ℝ := ‖genI‖ + ‖genJ‖ + ‖genK‖

lemma classGenC_nonneg : 0 ≤ classGenC :=
  add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)

/-- **The class generator is `O(‖t‖)`.** -/
lemma classGen_norm_le (t : Eucl 3) : ‖classGen t‖ ≤ classGenC * ‖t‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg classGenC_nonneg (norm_nonneg t))
    fun v => ?_
  have h1 : |t 1| ≤ ‖t‖ := PiLp.norm_apply_le t 1
  have h2 : |t 2| ≤ ‖t‖ := PiLp.norm_apply_le t 2
  have h3 : |t 3| ≤ ‖t‖ := PiLp.norm_apply_le t 3
  have b1 : ‖genI v‖ ≤ ‖genI‖ * ‖v‖ := genI.le_opNorm v
  have b2 : ‖genJ v‖ ≤ ‖genJ‖ * ‖v‖ := genJ.le_opNorm v
  have b3 : ‖genK v‖ ≤ ‖genK‖ * ‖v‖ := genK.le_opNorm v
  have n1 : ‖(t 1) • genI v‖ ≤ ‖t‖ * (‖genI‖ * ‖v‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul h1 b1 (norm_nonneg _) (norm_nonneg _)
  have n2 : ‖(t 2) • genJ v‖ ≤ ‖t‖ * (‖genJ‖ * ‖v‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul h2 b2 (norm_nonneg _) (norm_nonneg _)
  have n3 : ‖(t 3) • genK v‖ ≤ ‖t‖ * (‖genK‖ * ‖v‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul h3 b3 (norm_nonneg _) (norm_nonneg _)
  rw [classGen_apply]
  calc ‖(t 1) • genI v + (t 2) • genJ v + (t 3) • genK v‖
      ≤ ‖(t 1) • genI v + (t 2) • genJ v‖ + ‖(t 3) • genK v‖ := norm_add_le _ _
    _ ≤ (‖(t 1) • genI v‖ + ‖(t 2) • genJ v‖) + ‖(t 3) • genK v‖ := by
        linarith [norm_add_le ((t 1) • genI v) ((t 2) • genJ v)]
    _ ≤ (‖t‖ * (‖genI‖ * ‖v‖) + ‖t‖ * (‖genJ‖ * ‖v‖)) + ‖t‖ * (‖genK‖ * ‖v‖) := by
        linarith
    _ = classGenC * ‖t‖ * ‖v‖ := by rw [classGenC]; ring

/-- **The class equivalence as `1 + classGen`.** -/
lemma classEquiv_coe_sub_one (t : Eucl 3) :
    (classEquiv t : Eucl 3 →L[ℝ] Eucl 3) - 1 = classGen t := by
  ext v
  simp [classEquiv_apply]

/-- **`classEquiv t` is `O(‖t‖)`-close to the identity.** -/
lemma norm_classEquiv_sub_one_le (t : Eucl 3) :
    ‖(classEquiv t : Eucl 3 →L[ℝ] Eucl 3) - 1‖ ≤ classGenC * ‖t‖ := by
  rw [classEquiv_coe_sub_one]
  exact classGen_norm_le t

/-- **The class generator is additive.** -/
lemma classGen_sub (t s : Eucl 3) : classGen t - classGen s = classGen (t - s) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [classGen_apply, ContinuousLinearMap.sub_apply, PiLp.sub_apply, sub_smul]
  abel

/-- **The difference of two class equivalences is the generator of the difference.** -/
lemma classEquiv_sub_classEquiv (t s : Eucl 3) :
    (classEquiv t : Eucl 3 →L[ℝ] Eucl 3) - classEquiv s = classGen (t - s) := by
  rw [show (classEquiv t : Eucl 3 →L[ℝ] Eucl 3) = 1 + classGen t from by
        rw [← classEquiv_coe_sub_one t]; abel,
      show (classEquiv s : Eucl 3 →L[ℝ] Eucl 3) = 1 + classGen s from by
        rw [← classEquiv_coe_sub_one s]; abel,
      ← classGen_sub t s]
  abel

/-- **The explicit inverse of the class equivalence**, applied to a vector. -/
lemma classEquiv_symm_apply (t w : Eucl 3) :
    (classEquiv t).symm w = (1 + classNormSq t)⁻¹ • ((1 - classGen t) w) := by
  have hpos : (0 : ℝ) < 1 + classNormSq t := by
    have := classNormSq_nonneg t; linarith
  have hcoe : ⇑(classEquiv t : Eucl 3 →L[ℝ] Eucl 3)
      = ⇑(1 + classGen t : Eucl 3 →L[ℝ] Eucl 3) := by
    rw [show ⇑(classEquiv t : Eucl 3 →L[ℝ] Eucl 3)
        = ⇑((1 + classGen t : Eucl 3 →L[ℝ] Eucl 3)) from by
          rw [← classEquiv_coe_sub_one t]; abel]
  apply (classEquiv t).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  show w = (classEquiv t : Eucl 3 →L[ℝ] Eucl 3)
    ((1 + classNormSq t)⁻¹ • ((1 - classGen t : Eucl 3 →L[ℝ] Eucl 3) w))
  rw [hcoe, map_smul, classGen_mul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hpos), one_smul,
    eq_comm]

/-- **The inverse of the class equivalence as a continuous linear map.** -/
lemma classEquiv_symm_coe (t : Eucl 3) :
    ((classEquiv t).symm : Eucl 3 →L[ℝ] Eucl 3)
      = (1 + classNormSq t)⁻¹ • (1 - classGen t) := by
  refine ContinuousLinearMap.ext fun w => ?_
  show (classEquiv t).symm w = ((1 + classNormSq t)⁻¹ • (1 - classGen t) : Eucl 3 →L[ℝ] Eucl 3) w
  rw [classEquiv_symm_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]

/-- **The inverse of the class equivalence is close to the identity for small parameters**. -/
theorem exists_norm_classEquiv_symm_sub_one_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Eucl 3, ‖t‖ < δ →
      ‖((classEquiv t).symm : Eucl 3 →L[ℝ] Eucl 3) - 1‖ < ε := by
  refine ⟨min (min 1 (ε / 2)) (ε / (2 * (classGenC + 1))),
    lt_min (lt_min one_pos (by linarith)) (div_pos hε (by linarith [classGenC_nonneg])),
    fun t ht => ?_⟩
  have ht1 : ‖t‖ < 1 := lt_of_lt_of_le ht (le_trans (min_le_left _ _) (min_le_left _ _))
  have hthalf : ‖t‖ < ε / 2 :=
    lt_of_lt_of_le ht (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht2 : ‖t‖ < ε / (2 * (classGenC + 1)) := lt_of_lt_of_le ht (min_le_right _ _)
  rw [lt_div_iff₀ (by linarith [classGenC_nonneg] : (0 : ℝ) < 2 * (classGenC + 1))] at ht2
  have hC := classGenC_nonneg
  have htnn : (0 : ℝ) ≤ ‖t‖ := norm_nonneg t
  have hcs0 : 0 ≤ classNormSq t := classNormSq_nonneg t
  have hpos : (0 : ℝ) < 1 + classNormSq t := by linarith
  have hcs : classNormSq t ≤ ‖t‖ ^ 2 := by
    have hnorm := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 4 => ℝ) (t : Eucl 3)
    rw [Fin.sum_univ_four] at hnorm
    simp only [Real.norm_eq_abs, sq_abs] at hnorm
    have h0 : (0 : ℝ) ≤ (t 0) ^ 2 := sq_nonneg _
    rw [hnorm]
    simp only [classNormSq]
    linarith
  have hinv_le : (1 + classNormSq t)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hpos]; linarith
  have hinv_pos : (0 : ℝ) < (1 + classNormSq t)⁻¹ := inv_pos.mpr hpos
  have hfirst : |(1 + classNormSq t)⁻¹ - 1| ≤ ‖t‖ ^ 2 := by
    rw [abs_of_nonpos (by linarith), neg_sub]
    have h3 : 1 - (1 + classNormSq t)⁻¹ = classNormSq t / (1 + classNormSq t) := by
      rw [inv_eq_one_div]
      field_simp
      ring
    rw [h3, div_le_iff₀ hpos]
    nlinarith [hcs, hcs0, hpos]
  have hsecond : (1 + classNormSq t)⁻¹ * ‖classGen t‖ ≤ classGenC * ‖t‖ := by
    calc (1 + classNormSq t)⁻¹ * ‖classGen t‖
        ≤ 1 * ‖classGen t‖ := mul_le_mul_of_nonneg_right hinv_le (norm_nonneg _)
      _ ≤ classGenC * ‖t‖ := by rw [one_mul]; exact classGen_norm_le t
  rw [classEquiv_symm_coe]
  have hdecomp : (1 + classNormSq t)⁻¹ • (1 - classGen t) - 1
      = ((1 + classNormSq t)⁻¹ - 1) • (1 : Eucl 3 →L[ℝ] Eucl 3)
        - (1 + classNormSq t)⁻¹ • classGen t := by
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    module
  rw [hdecomp]
  have hmain : ‖((1 + classNormSq t)⁻¹ - 1) • (1 : Eucl 3 →L[ℝ] Eucl 3)
        - (1 + classNormSq t)⁻¹ • classGen t‖
      ≤ ‖t‖ ^ 2 + classGenC * ‖t‖ := by
    calc ‖((1 + classNormSq t)⁻¹ - 1) • (1 : Eucl 3 →L[ℝ] Eucl 3)
          - (1 + classNormSq t)⁻¹ • classGen t‖
        ≤ ‖((1 + classNormSq t)⁻¹ - 1) • (1 : Eucl 3 →L[ℝ] Eucl 3)‖
          + ‖(1 + classNormSq t)⁻¹ • classGen t‖ := norm_sub_le _ _
      _ = |(1 + classNormSq t)⁻¹ - 1| * 1 + (1 + classNormSq t)⁻¹ * ‖classGen t‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (le_of_lt hinv_pos), norm_one]
      _ ≤ ‖t‖ ^ 2 + classGenC * ‖t‖ := by linarith [hfirst, hsecond]
  have hsq : ‖t‖ ^ 2 ≤ ‖t‖ := by nlinarith [ht1, htnn]
  have hcb : classGenC * ‖t‖ ≤ ε / 2 := by nlinarith [hC, ht2, htnn]
  linarith [hmain, hsq, hcb, hthalf]

/-- **`classEquiv t` is close to the identity for small parameters.** -/
theorem exists_norm_classEquiv_sub_one_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : Eucl 3, ‖t‖ < δ →
      ‖(classEquiv t : Eucl 3 →L[ℝ] Eucl 3) - 1‖ < ε := by
  refine ⟨min 1 (ε / (classGenC + 1)),
    lt_min one_pos (div_pos hε (by linarith [classGenC_nonneg])), fun t ht => ?_⟩
  have ht2 : ‖t‖ < ε / (classGenC + 1) := lt_of_lt_of_le ht (min_le_right _ _)
  rw [lt_div_iff₀ (by linarith [classGenC_nonneg] : (0 : ℝ) < classGenC + 1)] at ht2
  have h := norm_classEquiv_sub_one_le t
  have hC := classGenC_nonneg
  nlinarith [norm_nonneg t]

end

end Work.Drive
