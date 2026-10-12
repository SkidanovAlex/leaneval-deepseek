import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pinQ_kernel_expansion
import Submission.Work.BoseBoxFock.potPairRows_kernelForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.kernelExpandedAux` — the toolbox of the *expanded* kernel form

The `Q₂` pair row is known in two equivalent shapes:

* the **kernel form** (`Work.BoseBoxFock.potPairRows_kernelForm`), where the mode sum is *inside*
  the position integrals as the kernel `Σ_k c k·Fp_k(x_{p.2})·conj(Fp_k y)` in the first two
  blocks, and *outside* them in the third block;
* the **expanded kernel form** (the target `Work.BoseBoxFock.potPairRows_kernelExpanded`), where
  the honest kernel `Σ_k c k·pinQ_k(w)·conj(pinQ_k(y))` is replaced everywhere by its four-term
  lattice expansion `K1exp` (`Work.BoseBoxFock.pinQ_kernel_expansion`), which is the shape the
  Poisson/periodisation analysis of the chapter consumes.

This module collects the generic facts that the passage between the two shapes needs:

* `pinQ_neg_apply`, `star_pinQ_neg_apply` — the reality of `pinQ` at the opposite label
  (`pinQ(-k) = conj ∘ pinQ k`, from `qVec(-p) = conj ∘ qVec p`), which is what makes the
  Bogoliubov rows of the kernel form match the `K1exp` spelling;
* `sum_W1_add_W1omega_kernel`, `sum_W1_conj_neg`, `sum_W1_pinQ_neg`, `pinQ_kernel_one` — the four
  pointwise kernel expansions in exactly the shape in which the row's integrals carry them;
* `integral_triple_const_mul`, `integral_double_const_mul` — pulling a constant out of the
  *nested* integrals (three/two applications of `integral_const_mul`; unconditional);
* `sum_mul_iterated_double_eq` — the two-slot analogue of
  `Work.BoseBoxFock.sum_mul_iterated_triple_eq`: a finite sum exchanges with the *double*
  iterated integral over `Xn n × Ω` (via `integral_prod` + `integral_finsetSum` at the product
  level);
* `sum_smul_pullout_triple`, `sum_smul_pullout_double` — the third block's exchange:
  `Σ_k α • (Σ_p ∫ A_kp) = α • Σ_p ∫ Σ_k A_kp` (the constant `α` is factored out and the finite
  sum moved inside);
* `sum_mul_mul_factor` — the reassociation `Σ_k ((L·f_k)·g_k)·D = (L·Σ_k f_k·g_k)·D` that turns
  `Σ_k A_k` into the product of the common factors with the kernel sum.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The reality of the pinned mode at the opposite label -/

/-- `1_Λ` is real, so it is conjugation-invariant. -/
theorem conj_thetaFun_apply (ℓ : ℝ) (x : Ω) :
    (starRingEnd ℂ) (Work.BoseK15.corpusBox.thetaFun ℓ x)
      = Work.BoseK15.corpusBox.thetaFun ℓ x := by
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  split <;> simp

/-- `conj (e^{i⟪k,x⟫}) = e^{−i⟪k,x⟫}` in the order in which the pinned modes carry it. -/
theorem conj_exp_inner (k x : Ω) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * ((inner ℝ k x : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * ((inner ℝ k x : ℝ) : ℂ))) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  congr 1
  ring

/-- `qVec (−p) = conj ∘ qVec p`: the localised plane wave with the opposite momentum, with the
condensate component removed (`χ_Λ` and `χ̂` are real). -/
theorem qVec_neg_apply (ℓ : ℝ) (k x : Ω) :
    Work.BoseK15.corpusBox.qVec ℓ (-k) x
      = (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x) := by
  simp only [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply]
  rw [map_sub, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, conj_thetaFun_apply,
    conj_exp_inner, inner_neg_left, smul_neg, Work.BoseB4.BoxData.hatChi_neg]
  have h : Complex.I * (↑(-(inner ℝ k x)) : ℂ) = -(Complex.I * ↑(inner ℝ k x)) := by
    push_cast
    ring
  rw [h]

/-- **The reality of `pinQ` at the opposite label**: `pinQ(−k) = conj ∘ pinQ k` (the normalising
scalar `(√ℓ³)⁻¹` is real). -/
theorem pinQ_neg_apply (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) (z : Ω) :
    pinQ v μ N (-k) z = (starRingEnd ℂ) (pinQ v μ N k z) := by
  have hq := qVec_neg_apply (ellH v μ) (kmomLab (ellH v μ) N k) z
  simp only [pinQ]
  rw [kmomLab_neg, hq, map_mul, Complex.conj_ofReal]

/-- The `star`-form of `pinQ_neg_apply`: `conj (pinQ(−k) z) = pinQ k z`. -/
theorem star_pinQ_neg_apply (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) (z : Ω) :
    (starRingEnd ℂ) (pinQ v μ N (-k) z) = pinQ v μ N k z := by
  rw [pinQ_neg_apply]
  simp

/-! ## 1bis. Measurability and bounds of the pinned modes -/

/-- The norm of the image of a real number in `ℂ` is its absolute value. -/
theorem norm_ofReal_c (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- `χ_Λ` has compact support (it is `χ` composed with the dilation by `ℓ⁻¹`). -/
theorem chiLam_hasCompactSupport (ℓ : ℝ) (hℓ : ℓ ≠ 0) :
    HasCompactSupport (Work.BoseK15.corpusBox.chiLam ℓ) := by
  have h : Work.BoseK15.corpusBox.chiLam ℓ
      = fun x : Ω => Work.BoseK15.corpusBox.chi (ℓ⁻¹ • x) := rfl
  rw [h]
  exact (Work.BoseB4.BoxData.hasCompactSupport_chi (B := Work.BoseK15.corpusBox)).comp_smul
    (inv_ne_zero hℓ)

/-- `χ_Λ` is bounded, uniformly in the position. -/
theorem chiLam_bdd (ℓ : ℝ) (hℓ : ℓ ≠ 0) :
    ∃ C : ℝ, ∀ x : Ω, |Work.BoseK15.corpusBox.chiLam ℓ x| ≤ C := by
  obtain ⟨C, hC⟩ :=
    (Work.BoseB4.BoxData.chiLam_cont (B := Work.BoseK15.corpusBox) ℓ).bounded_above_of_compact_support
      (chiLam_hasCompactSupport ℓ hℓ)
  exact ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x⟩

/-- `θ = 1_Λ` is measurable (it is the indicator of the box). -/
theorem thetaFun_measurable_aux (ℓ : ℝ) : Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := by
  classical
  have h : Work.BoseK15.corpusBox.thetaFun ℓ
      = (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ : Ω => (1 : ℂ)) := by
    funext z
    simp only [Work.BoseB4.BoxData.thetaFun_apply, Set.indicator_apply]
  simpa only [h] using
    measurable_const.indicator (Work.BoseB4.BoxData.boxL_measurableSet (Work.BoseK15.corpusBox) ℓ)

/-- The localised plane wave is measurable. -/
theorem modeVec_measurable_aux (ℓ : ℝ) (p : Ω) :
    Measurable (Work.BoseK15.corpusBox.modeVec ℓ p) := by
  have h : Work.BoseK15.corpusBox.modeVec ℓ p
      = fun z : Ω => Complex.exp (Complex.I * ((inner ℝ p z : ℝ) : ℂ))
          * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) :=
    funext fun z => Work.BoseB4.BoxData.modeVec_apply _ _ _ _
  rw [h]
  refine (Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_id)))).measurable.mul ?_
  exact Complex.continuous_ofReal.measurable.comp
    (Work.BoseB4.BoxData.chiLam_cont (B := Work.BoseK15.corpusBox) ℓ).measurable

/-- `pinQ` is measurable. -/
theorem pinQ_measurable (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) :
    Measurable (pinQ v μ N k) := by
  have h : pinQ v μ N k = fun z : Ω =>
      (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) *
        (Work.BoseK15.corpusBox.modeVec (ellH v μ) (kmomLab (ellH v μ) N k) z
          - ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (ellH v μ) z) :=
    funext fun z => by rw [pinQ, Work.BoseB4.BoxData.qVec_apply]
  rw [h]
  refine Measurable.const_mul ?_ _
  exact (modeVec_measurable_aux (ellH v μ) (kmomLab (ellH v μ) N k)).sub
    (measurable_const.mul (thetaFun_measurable_aux (ellH v μ)))

/-- `pinQ` is bounded, uniformly in the position. -/
theorem pinQ_bdd (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Ω, ‖pinQ v μ N k z‖ ≤ C := by
  obtain ⟨Cχ, hCχ⟩ := chiLam_bdd (ellH v μ) (ne_of_gt (ellH_pos v μ))
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hs : 0 < (Real.sqrt ((ellH v μ) ^ 3))⁻¹ :=
    inv_pos.mpr (Real.sqrt_pos_of_pos (pow_pos hℓ 3))
  have hθ : ∀ z : Ω, ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) z‖ ≤ 1 := by
    intro z
    classical
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    split <;> simp
  have hq : ∀ z : Ω,
      ‖Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) N k) z‖
        ≤ max Cχ 0 + 1 := by
    intro z
    rw [Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply]
    refine le_trans (norm_sub_le _ _) ?_
    have h1 : ‖Complex.exp (Complex.I * ((inner ℝ (kmomLab (ellH v μ) N k) z : ℝ) : ℂ)) *
        ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)‖ ≤ max Cχ 0 := by
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, norm_ofReal_c]
      exact le_trans (hCχ z) (le_max_left _ _)
    have h2 : ‖((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N k) : ℝ) : ℂ) *
        Work.BoseK15.corpusBox.thetaFun (ellH v μ) z‖ ≤ 1 := by
      rw [norm_mul, norm_ofReal_c]
      have hh := Work.BoseK15.hatChi_le_one.1 ((ellH v μ) • kmomLab (ellH v μ) N k)
      exact le_trans (mul_le_mul hh (hθ z) (norm_nonneg _) (by norm_num))
        (by norm_num)
    linarith
  refine ⟨(Real.sqrt ((ellH v μ) ^ 3))⁻¹ * (max Cχ 0 + 1), by positivity, fun z => ?_⟩
  rw [pinQ, norm_mul, norm_ofReal_c, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_left (hq z) hs.le

/-- `pinCond` is measurable. -/
theorem pinCond_measurable (v : Ω → ℝ) (μ : ℝ) (c : ℂ) : Measurable (pinCond v μ c) :=
  measurable_const.mul (thetaFun_measurable_aux (ellH v μ))

/-- `pinCond` is bounded, uniformly in the position. -/
theorem pinCond_bdd (v : Ω → ℝ) (μ : ℝ) (c : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Ω, ‖pinCond v μ c z‖ ≤ C := by
  refine ⟨‖c‖, norm_nonneg _, fun z => ?_⟩
  have hθ : ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) z‖ ≤ 1 := by
    classical
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    split <;> simp
  rw [pinCond, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg c) hθ

/-! ## 2. The four pointwise kernel expansions -/

/-- The kernel expansion at the weight `W₁ + W₁ω`, in the shape of the first block. -/
theorem sum_W1_add_W1omega_kernel (N : ℕ) (v : Ω → ℝ) (μ : ℝ)
    (E : Work.BoseB7.Q3Env (Lab N)) (w y : Ω) :
    (∑ k : Lab N,
        (↑(E.W1 k) + ↑(E.W1omega k)) * (pinQ v μ N k w * (starRingEnd ℂ) (pinQ v μ N k y)))
      = K1exp v μ N (fun k => E.W1 k + E.W1omega k) w y := by
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans
    (pinQ_kernel_expansion (fun k : Lab N => E.W1 k + E.W1omega k) w y)
  rw [Complex.ofReal_add]

/-- The kernel expansion with weight `1`, in the shape of the third block. -/
theorem pinQ_kernel_one (N : ℕ) (v : Ω → ℝ) (μ : ℝ) (w y : Ω) :
    (∑ k : Lab N, pinQ v μ N k w * (starRingEnd ℂ) (pinQ v μ N k y))
      = K1exp v μ N (fun _ : Lab N => (1 : ℝ)) w y := by
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans
    (pinQ_kernel_expansion (fun _ : Lab N => (1 : ℝ)) w y)
  rw [Complex.ofReal_one, one_mul]

/-- The kernel expansion at the weight `W₁`, in the shape of the first Bogoliubov row
(`conj (pinQ k y)·conj (pinQ (−k) u)`). -/
theorem sum_W1_conj_neg (N : ℕ) (v : Ω → ℝ) (μ : ℝ) (E : Work.BoseB7.Q3Env (Lab N)) (u y : Ω) :
    (∑ k : Lab N,
        ↑(E.W1 k) * ((starRingEnd ℂ) (pinQ v μ N k y) * (starRingEnd ℂ) (pinQ v μ N (-k) u)))
      = K1exp v μ N E.W1 u y := by
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans (pinQ_kernel_expansion E.W1 u y)
  rw [star_pinQ_neg_apply]
  ring

/-- The kernel expansion at the weight `W₁`, in the shape of the second Bogoliubov row
(`pinQ k (x p.1)·pinQ (−k) (x p.2)`). -/
theorem sum_W1_pinQ_neg (N : ℕ) (v : Ω → ℝ) (μ : ℝ) (E : Work.BoseB7.Q3Env (Lab N))
    (w₁ w₂ : Ω) :
    (∑ k : Lab N, ↑(E.W1 k) * (pinQ v μ N k w₁ * pinQ v μ N (-k) w₂))
      = K1exp v μ N E.W1 w₁ w₂ := by
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans (pinQ_kernel_expansion E.W1 w₁ w₂)
  rw [pinQ_neg_apply]

/-! ## 3. Pulling constants out of the nested integrals -/

/-- `∫ₓ∫_y∫_u c·f = c·∫ₓ∫_y∫_u f` (unconditional: three applications of
`MeasureTheory.integral_const_mul`). -/
theorem integral_triple_const_mul {n : ℕ} (c : ℂ) (f : Xn n → Ω → Ω → ℂ) :
    (∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, c * f x y u) = c * ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, f x y u := by
  simp_rw [MeasureTheory.integral_const_mul]

/-- `∫ₓ∫_y c·f = c·∫ₓ∫_y f`. -/
theorem integral_double_const_mul {n : ℕ} (c : ℂ) (f : Xn n → Ω → ℂ) :
    (∫ x : Xn n, ∫ y : Ω, c * f x y) = c * ∫ x : Xn n, ∫ y : Ω, f x y := by
  simp_rw [MeasureTheory.integral_const_mul]

/-! ## 4. The finite sum / double integral exchange -/

/-- **The finite sum exchanges with the double iterated integral** (the two-slot twin of
`Work.BoseBoxFock.sum_mul_iterated_triple_eq`): if each summand is integrable for
`vXn n ⊗ volume`, then
`Σ_k c_k·(Σ_{j∈s} ∫ₓ∫_y B_kj) = Σ_{j∈s} ∫ₓ∫_y Σ_k c_k·B_kj`. -/
theorem sum_mul_iterated_double_eq {ι : Type*} {Mode : Type*} [Fintype Mode] {n : ℕ}
    (s : Finset ι) (c : Mode → ℂ) (B : Mode → ι → Xn n → Ω → ℂ)
    (hB : ∀ k j, j ∈ s →
      Integrable (fun q : Xn n × Ω => B k j q.1 q.2) ((vXn n).prod (volume : Measure Ω))) :
    (∑ k : Mode, c k * (∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, B k j x y))
      = ∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, ∑ k : Mode, c k * B k j x y := by
  classical
  have key : ∀ j ∈ s, (∑ k : Mode, c k * (∫ x : Xn n, ∫ y : Ω, B k j x y))
      = ∫ x : Xn n, ∫ y : Ω, ∑ k : Mode, c k * B k j x y := by
    intro j hj
    have h1 : ∀ k, (∫ q : Xn n × Ω, B k j q.1 q.2 ∂(vXn n).prod (volume : Measure Ω))
        = ∫ x : Xn n, ∫ y : Ω, B k j x y := fun k =>
      MeasureTheory.integral_prod (fun q : Xn n × Ω => B k j q.1 q.2) (hB k j hj)
    have hs : Integrable (fun q : Xn n × Ω => ∑ k : Mode, c k * B k j q.1 q.2)
        ((vXn n).prod (volume : Measure Ω)) :=
      MeasureTheory.integrable_finsetSum Finset.univ (fun k _ => (hB k j hj).const_mul (c k))
    have h1s : (∫ q : Xn n × Ω, (∑ k : Mode, c k * B k j q.1 q.2)
          ∂(vXn n).prod (volume : Measure Ω))
        = ∫ x : Xn n, ∫ y : Ω, ∑ k : Mode, c k * B k j x y :=
      MeasureTheory.integral_prod
        (fun q : Xn n × Ω => ∑ k : Mode, c k * B k j q.1 q.2) hs
    calc (∑ k : Mode, c k * (∫ x : Xn n, ∫ y : Ω, B k j x y))
        = ∑ k : Mode, c k * (∫ q : Xn n × Ω, B k j q.1 q.2
            ∂(vXn n).prod (volume : Measure Ω)) := by
          exact Finset.sum_congr rfl (fun k _ => by rw [h1 k])
      _ = ∑ k : Mode, ∫ q : Xn n × Ω, c k * B k j q.1 q.2
            ∂(vXn n).prod (volume : Measure Ω) := by
          exact Finset.sum_congr rfl (fun k _ => (MeasureTheory.integral_const_mul (c k) _).symm)
      _ = ∫ q : Xn n × Ω, ∑ k : Mode, c k * B k j q.1 q.2
            ∂(vXn n).prod (volume : Measure Ω) :=
          (MeasureTheory.integral_finsetSum Finset.univ
            (fun k _ => (hB k j hj).const_mul (c k))).symm
      _ = _ := h1s
  calc (∑ k : Mode, c k * (∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, B k j x y))
      = ∑ k : Mode, ∑ j ∈ s, c k * (∫ x : Xn n, ∫ y : Ω, B k j x y) := by
        exact Finset.sum_congr rfl (fun k _ => Finset.mul_sum s _ (c k))
    _ = ∑ j ∈ s, ∑ k : Mode, c k * (∫ x : Xn n, ∫ y : Ω, B k j x y) := Finset.sum_comm
    _ = ∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, ∑ k : Mode, c k * B k j x y :=
        Finset.sum_congr rfl (fun j hj => key j hj)

/-! ## 5. The exchange of the third block -/

/-- **The third block's exchange (triple-integral row)**: a constant `α` factors out of the finite
sum `Σ_k`, and the finite sum moves inside the `pairSet`-sum and the triple integral. -/
theorem sum_smul_pullout_triple {ι : Type*} {Mode : Type*} [Fintype Mode] {n : ℕ}
    (s : Finset ι) (α : ℝ) (A : Mode → ι → Xn n → Ω → Ω → ℂ)
    (hA : ∀ k p, p ∈ s →
      Integrable (fun z : (Xn n × Ω) × Ω => A k p z.1.1 z.1.2 z.2) (v3 n)) :
    (∑ k : Mode, α • (∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, A k p x y u))
      = α • (∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, ∑ k : Mode, A k p x y u) := by
  classical
  calc (∑ k : Mode, α • (∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, A k p x y u))
      = ∑ k : Mode, (↑α : ℂ) * (∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, A k p x y u) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Complex.real_smul]
    _ = ∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, ∑ k : Mode, (↑α : ℂ) * A k p x y u :=
        sum_mul_iterated_triple_eq s (fun _ : Mode => (↑α : ℂ)) A hA
    _ = ∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
          (↑α : ℂ) * (∑ k : Mode, A k p x y u) := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        refine integral_triple_congr_of_forall (fun x y u => ?_)
        rw [Finset.mul_sum]
    _ = ∑ p ∈ s, (↑α : ℂ) * (∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, ∑ k : Mode, A k p x y u) := by
        refine Finset.sum_congr rfl (fun p hp => integral_triple_const_mul _ _)
    _ = (↑α : ℂ) * (∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, ∑ k : Mode, A k p x y u) := by
        rw [Finset.mul_sum]
    _ = α • (∑ p ∈ s, ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω, ∑ k : Mode, A k p x y u) := by
        rw [Complex.real_smul]

/-- **The third block's exchange (double-integral row)**: the same for the single-slot
`Σ_j ∫ₓ∫_y` row. -/
theorem sum_smul_pullout_double {ι : Type*} {Mode : Type*} [Fintype Mode] {n : ℕ}
    (s : Finset ι) (α : ℝ) (B : Mode → ι → Xn n → Ω → ℂ)
    (hB : ∀ k j, j ∈ s →
      Integrable (fun q : Xn n × Ω => B k j q.1 q.2) ((vXn n).prod (volume : Measure Ω))) :
    (∑ k : Mode, α • (∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, B k j x y))
      = α • (∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, ∑ k : Mode, B k j x y) := by
  classical
  calc (∑ k : Mode, α • (∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, B k j x y))
      = ∑ k : Mode, (↑α : ℂ) * (∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, B k j x y) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Complex.real_smul]
    _ = ∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, ∑ k : Mode, (↑α : ℂ) * B k j x y :=
        sum_mul_iterated_double_eq s (fun _ : Mode => (↑α : ℂ)) B hB
    _ = ∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, (↑α : ℂ) * (∑ k : Mode, B k j x y) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        refine integral_double_congr_of_forall (fun x y => ?_)
        rw [Finset.mul_sum]
    _ = ∑ j ∈ s, (↑α : ℂ) * (∫ x : Xn n, ∫ y : Ω, ∑ k : Mode, B k j x y) := by
        refine Finset.sum_congr rfl (fun j hj => integral_double_const_mul _ _)
    _ = (↑α : ℂ) * (∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, ∑ k : Mode, B k j x y) := by
        rw [Finset.mul_sum]
    _ = α • (∑ j ∈ s, ∫ x : Xn n, ∫ y : Ω, ∑ k : Mode, B k j x y) := by
        rw [Complex.real_smul]

/-! ## 6. Reassociating the kernel sum under the common factors -/

/-- `Σₖ ((L·fₖ)·gₖ)·D = (L·Σₖ fₖ·gₖ)·D`: the common factors `L`, `D` factor out of the finite
sum, which is exactly the shape in which the third block's integrands carry the kernel. -/
theorem sum_mul_mul_factor {Mode : Type*} [Fintype Mode] (f g : Mode → ℂ) (Ks L D : ℂ)
    (h : (∑ k : Mode, f k * g k) = Ks) :
    (∑ k : Mode, ((L * f k) * g k) * D) = (L * Ks) * D := by
  rw [← Finset.sum_mul]
  rw [show (∑ k : Mode, (L * f k) * g k) = ∑ k : Mode, L * (f k * g k) from
        Finset.sum_congr rfl (fun k _ => by ring)]
  rw [← Finset.mul_sum, h]

end Work.BoseBoxFock
