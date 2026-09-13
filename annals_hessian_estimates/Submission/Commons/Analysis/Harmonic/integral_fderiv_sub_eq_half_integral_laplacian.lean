import Mathlib
import Submission.Commons.Analysis.MeasureTheory.integral_divergence_eq_zero_euclidean
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_apply_directional
import Submission.Commons.Analysis.Calculus.iteratedDeriv_smoothTransition_scale_bound
import Submission.Commons.Analysis.Calculus.fderiv_smoothTransition_const_mul
import Submission.Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian

namespace Commons.Analysis.Harmonic

open _root_.MeasureTheory Metric Set Filter Function
open scoped BigOperators Topology RealInnerProductSpace InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- The weight `ρ² - ‖y - c‖²`. -/
private def Phi (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ρ ^ 2 - ‖y - c‖ ^ 2

/-- The cutoff `smoothTransition ((k+1) * (ρ² - ‖y-c‖²))`. -/
private def cut (k : ℕ) (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.smoothTransition ((k + 1 : ℝ) * Phi c ρ y)

/-- The coordinate divergence `∑ i, ∂_i V_i`. -/
private def divE (V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, (fderiv ℝ V z (EuclideanSpace.single i 1)) i

/-- The vector field `(cut · Phi) • ∇v`. -/
private def Wfield (k : ℕ) (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (cut k c ρ y * Phi c ρ y) • gradient v y

private lemma contDiff_Phi (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) :
    ContDiff ℝ 2 (Phi c ρ) := by
  unfold Phi
  have h1 : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => y - c) :=
    contDiff_id.sub contDiff_const
  exact (contDiff_const (c := ρ ^ 2)).sub (h1.norm_sq ℝ)

private lemma contDiff_cut (k : ℕ) (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) :
    ContDiff ℝ 2 (cut k c ρ) := by
  have h1 : ContDiff ℝ 2 (fun _ : EuclideanSpace ℝ (Fin n) => ((k : ℝ) + 1)) := contDiff_const
  have h2 : ContDiff ℝ 2 (Phi c ρ) := contDiff_Phi c ρ
  unfold cut
  exact (Real.smoothTransition.contDiff (n := (2 : ℕ∞))).comp (h1.mul h2)

private lemma cut_nonneg (k : ℕ) (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ cut k c ρ y := Real.smoothTransition.nonneg _

private lemma cut_le_one (k : ℕ) (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : cut k c ρ y ≤ 1 := Real.smoothTransition.le_one _

private lemma cut_eq_zero_of_nonpos (k : ℕ) (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (h : Phi c ρ y ≤ 0) : cut k c ρ y = 0 := by
  unfold cut
  refine Real.smoothTransition.zero_of_nonpos ?_
  have : (0:ℝ) ≤ (k + 1 : ℝ) := by positivity
  nlinarith

private lemma pos_of_cut_ne_zero (k : ℕ) (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    {y : EuclideanSpace ℝ (Fin n)} (h : cut k c ρ y ≠ 0) : 0 < Phi c ρ y := by
  by_contra hle
  exact h (cut_eq_zero_of_nonpos k c ρ (not_lt.mp hle))

private lemma parseval {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    (∑ i : Fin n, ⟪a, EuclideanSpace.single i 1⟫ * ⟪b, EuclideanSpace.single i 1⟫) = ⟪a, b⟫ := by
  have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner a b
  simp only [EuclideanSpace.basisFun_apply] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (EuclideanSpace.single i 1) b]

private lemma coord_single {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    a i = ⟪a, EuclideanSpace.single i 1⟫ := by
  rw [PiLp.inner_apply]; simp

private lemma inner_gradient_left' {n : ℕ} (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (z w : EuclideanSpace ℝ (Fin n)) : ⟪gradient v z, w⟫ = (fderiv ℝ v z) w :=
  inner_gradient_left

private lemma divE_smul {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (X : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin n)) (hf : DifferentiableAt ℝ f z) (hX : DifferentiableAt ℝ X z) :
    divE (fun y => f y • X y) z = f z * divE X z + ⟪gradient f z, X z⟫ := by
  unfold divE
  have hderiv : fderiv ℝ (fun y => f y • X y) z
      = f z • fderiv ℝ X z + (fderiv ℝ f z).smulRight (X z) :=
    fderiv_smul hf hX
  have hterm : ∀ i : Fin n, (fderiv ℝ (fun y => f y • X y) z (EuclideanSpace.single i 1)) i
      = f z * (fderiv ℝ X z (EuclideanSpace.single i 1)) i
        + (fderiv ℝ f z (EuclideanSpace.single i 1)) * (X z) i := by
    intro i
    rw [hderiv]
    simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
      PiLp.add_apply, PiLp.smul_apply]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsecond : (∑ i : Fin n, (fderiv ℝ f z (EuclideanSpace.single i 1)) * (X z) i)
      = ⟪gradient f z, X z⟫ := by
    rw [show (∑ i : Fin n, (fderiv ℝ f z (EuclideanSpace.single i 1)) * (X z) i)
        = ∑ i : Fin n, ⟪gradient f z, EuclideanSpace.single i 1⟫
            * ⟪X z, EuclideanSpace.single i 1⟫ from by
      apply Finset.sum_congr rfl
      intro i _
      rw [← inner_gradient_left, coord_single]]
    exact parseval _ _
  rw [hsecond]

private lemma divE_gradient_eq_laplacian [Nonempty (Fin n)]
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (hv : ContDiff ℝ 2 v)
    (z : EuclideanSpace ℝ (Fin n)) :
    divE (gradient v) z = Laplacian.laplacian v z := by
  unfold divE
  have hgraddiff : DifferentiableAt ℝ (gradient v) z := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ v) z :=
      ((hv.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero).differentiableAt
    have h2 := (LinearIsometryEquiv.differentiableAt
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm).comp z h1
    rw [show gradient v = (fun x => (InnerProductSpace.toDual ℝ
      (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ v x)) from rfl]
    exact h2
  have hcoord : ∀ i : Fin n,
      (fderiv ℝ (gradient v) z (EuclideanSpace.single i 1)) i
        = (fderiv ℝ (fun w => (fderiv ℝ v w) (EuclideanSpace.single i 1)) z)
            (EuclideanSpace.single i 1) := by
    intro i
    have hfun : (fun w => (gradient v w) i)
        = (fun w => (fderiv ℝ v w) (EuclideanSpace.single i 1)) := by
      funext w
      rw [show (gradient v w) i = ⟪gradient v w, EuclideanSpace.single i 1⟫ from by
        rw [PiLp.inner_apply]; simp]
      rw [inner_gradient_left]
    rw [show (fderiv ℝ (gradient v) z (EuclideanSpace.single i 1)) i
          = (fderiv ℝ (fun w => (gradient v w) i) z) (EuclideanSpace.single i 1) from by
        have h : (fun w => (gradient v w) i)
            = (EuclideanSpace.proj (𝕜 := ℝ) i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
              ∘ gradient v := by
          funext w; rw [EuclideanSpace.coe_proj]; rfl
        rw [h, fderiv_comp z]
        · rw [ContinuousLinearMap.fderiv]; rfl
        · exact (ContinuousLinearMap.hasFDerivAt _).differentiableAt
        · exact hgraddiff]
    rw [hfun]
  rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
  have h2 : ∀ i : Fin n,
      (fderiv ℝ (fun w => (fderiv ℝ v w) (EuclideanSpace.single i 1)) z)
        (EuclideanSpace.single i 1)
        = (iteratedFDeriv ℝ 2 v z) ![(EuclideanSpace.single i 1),
            (EuclideanSpace.single i 1)] := by
    intro i
    exact Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_apply_directional
      isOpen_univ (mem_univ z) hv.contDiffOn
  rw [Finset.sum_congr rfl (fun i _ => h2 i)]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis v
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply]

private lemma fderiv_Phi (c z : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    (w : EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ (Phi c ρ) z) w = -2 * ⟪z - c, w⟫ := by
  have hsub : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => y - c)
      (ContinuousLinearMap.id ℝ _) z := by
    simpa using (hasFDerivAt_id z).sub_const c
  have h1hf : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y - c‖^2)
      (2 • innerSL ℝ (z - c)) z := by
    simpa using hsub.norm_sq
  have hmain : fderiv ℝ (Phi c ρ) z = - (2 • innerSL ℝ (z - c)) := by
    rw [show Phi c ρ = (fun y : EuclideanSpace ℝ (Fin n) => ρ^2 - ‖y - c‖^2) from rfl]
    rw [fderiv_const_sub (𝕜 := ℝ) (c := ρ^2)
      (f := fun y : EuclideanSpace ℝ (Fin n) => ‖y - c‖^2) (x := z), h1hf.fderiv]
  rw [hmain]
  simp only [neg_apply, smul_apply, innerSL_apply_apply]
  rw [inner_sub_left]
  ring


private lemma contDiff_gradient' (v : EuclideanSpace ℝ (Fin n) → ℝ) (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 1 (gradient v) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (m := 1) (by norm_num)
  have h2 : gradient v = (fun w => (InnerProductSpace.toDual ℝ
      (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ v w)) := rfl
  rw [h2]
  exact (LinearIsometryEquiv.contDiff
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm).comp h1

private lemma contDiff_Wfield (k : ℕ) (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hv : ContDiff ℝ 2 v) (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) :
    ContDiff ℝ 1 (Wfield k v c ρ) := by
  unfold Wfield
  have h1 : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) => cut k c ρ y * Phi c ρ y) :=
    ((contDiff_cut k c ρ).of_le (by norm_num)).mul ((contDiff_Phi c ρ).of_le (by norm_num))
  exact h1.smul (contDiff_gradient' v hv)

private lemma hasCompactSupport_Wfield (k : ℕ) (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 < ρ) :
    HasCompactSupport (Wfield k v c ρ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := closedBall c ρ) (isCompact_closedBall c ρ) ?_
  intro y hy
  simp only [Function.mem_support] at hy
  have hcut : cut k c ρ y ≠ 0 := by
    intro h
    exact hy (by unfold Wfield; rw [h, zero_mul, zero_smul])
  have hpos : 0 < Phi c ρ y := pos_of_cut_ne_zero k c ρ hcut
  have hsq : ‖y - c‖ ^ 2 < ρ ^ 2 := by unfold Phi at hpos; linarith
  rw [Metric.mem_closedBall, dist_eq_norm]
  have habs : |‖y - c‖| < |ρ| := (sq_lt_sq.mp hsq)
  rw [abs_of_nonneg (norm_nonneg _), abs_of_pos hρ] at habs
  exact habs.le

private lemma divE_Wfield (k : ℕ) (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (hv : ContDiff ℝ 2 v) [Nonempty (Fin n)] (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    divE (Wfield k v c ρ) z
      = cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z
        - 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))
        + Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)) := by
  have hcd : DifferentiableAt ℝ (fun y => cut k c ρ y * Phi c ρ y) z :=
    ((contDiff_cut k c ρ).differentiable (by norm_num)).differentiableAt.mul
      (((contDiff_Phi c ρ).differentiable (by norm_num)).differentiableAt)
  have hgd : DifferentiableAt ℝ (gradient v) z :=
    ((contDiff_gradient' v hv).differentiable (by norm_num)).differentiableAt
  have hsmul := divE_smul (fun y => cut k c ρ y * Phi c ρ y) (gradient v) z hcd hgd
  have hlap := divE_gradient_eq_laplacian v hv z
  -- rewrite the inner product with the gradient
  have hinner : ⟪gradient (fun y => cut k c ρ y * Phi c ρ y) z, gradient v z⟫
      = (fderiv ℝ (fun y => cut k c ρ y * Phi c ρ y) z) (gradient v z) :=
    inner_gradient_left
  have hmul : fderiv ℝ (fun y => cut k c ρ y * Phi c ρ y) z
      = cut k c ρ z • fderiv ℝ (Phi c ρ) z + Phi c ρ z • fderiv ℝ (cut k c ρ) z :=
    fderiv_mul ((contDiff_cut k c ρ).differentiable (by norm_num)).differentiableAt
      (((contDiff_Phi c ρ).differentiable (by norm_num)).differentiableAt)
  have happly : (fderiv ℝ (fun y => cut k c ρ y * Phi c ρ y) z) (gradient v z)
      = cut k c ρ z * ((fderiv ℝ (Phi c ρ) z) (gradient v z))
        + Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)) := by
    rw [hmul]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hPhi : (fderiv ℝ (Phi c ρ) z) (gradient v z)
      = -2 * ((fderiv ℝ v z) (z - c)) := by
    rw [fderiv_Phi]
    rw [real_inner_comm]
    rw [inner_gradient_left]
  unfold Wfield
  rw [hsmul, hlap, hinner, happly, hPhi]
  ring


private lemma deriv_smoothTransition_eq_zero_of_neg {t : ℝ} (h : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have := Commons.Analysis.Calculus.iteratedDeriv_succ_smoothTransition_eq_zero_of_neg 0 h
  simpa [iteratedDeriv_one] using this

private lemma deriv_smoothTransition_eq_zero_of_one_lt {t : ℝ} (h : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have := Commons.Analysis.Calculus.iteratedDeriv_succ_smoothTransition_eq_zero_of_one_lt 0 h
  simpa [iteratedDeriv_one] using this

private lemma deriv_smoothTransition_mul_self_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t * deriv Real.smoothTransition t| ≤ C := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Commons.Analysis.Calculus.exists_pos_abs_iteratedDeriv_succ_smoothTransition_bound 0
  refine ⟨2 * C0 + 1, by linarith, fun t => ?_⟩
  have hderiv : |deriv Real.smoothTransition t| ≤ C0 := by
    have := hC0 t
    simpa [iteratedDeriv_one] using this
  by_cases h : t < -1
  · rw [deriv_smoothTransition_eq_zero_of_neg (by linarith : t < 0), mul_zero, abs_zero]
    linarith
  · by_cases h2 : 2 < t
    · rw [deriv_smoothTransition_eq_zero_of_one_lt (by linarith : 1 < t), mul_zero, abs_zero]
      linarith
    · have ht : |t| ≤ 2 := by rw [abs_le]; constructor <;> linarith
      calc |t * deriv Real.smoothTransition t| = |t| * |deriv Real.smoothTransition t| :=
            abs_mul _ _
        _ ≤ 2 * C0 := by gcongr
        _ ≤ 2 * C0 + 1 := by linarith

private lemma fderiv_cut (k : ℕ) (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (cut k c ρ) z
      = (deriv Real.smoothTransition (((k : ℝ) + 1) * Phi c ρ z) * ((k : ℝ) + 1))
          • fderiv ℝ (Phi c ρ) z := by
  have hd : DifferentiableAt ℝ (Phi c ρ) z :=
    ((contDiff_Phi c ρ).differentiable (by norm_num)).differentiableAt
  have hcut : cut k c ρ = (fun y => Real.smoothTransition (((k : ℝ) + 1) * Phi c ρ y)) := by
    funext y; rfl
  rw [hcut]
  exact Commons.Analysis.Calculus.fderiv_smoothTransition_const_mul hd ((k : ℝ) + 1)


private lemma Phi_mul_fderiv_cut_apply_bound (k : ℕ) (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ)
    {C : ℝ} (hC : ∀ t : ℝ, |t * deriv Real.smoothTransition t| ≤ C)
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    |Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z))|
      ≤ C * ‖fderiv ℝ (Phi c ρ) z‖ * ‖gradient v z‖ := by
  rw [fderiv_cut]
  have happ : ((deriv Real.smoothTransition (((k : ℝ) + 1) * Phi c ρ z) * ((k : ℝ) + 1))
        • fderiv ℝ (Phi c ρ) z) (gradient v z)
      = deriv Real.smoothTransition (((k : ℝ) + 1) * Phi c ρ z) * ((k : ℝ) + 1)
        * ((fderiv ℝ (Phi c ρ) z) (gradient v z)) := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [happ]
  have hrewrite : Phi c ρ z * (deriv Real.smoothTransition (((k : ℝ) + 1) * Phi c ρ z)
        * ((k : ℝ) + 1) * ((fderiv ℝ (Phi c ρ) z) (gradient v z)))
      = ((((k : ℝ) + 1) * Phi c ρ z) * deriv Real.smoothTransition (((k : ℝ) + 1) * Phi c ρ z))
        * ((fderiv ℝ (Phi c ρ) z) (gradient v z)) := by ring
  rw [hrewrite, abs_mul]
  calc |(((k : ℝ) + 1) * Phi c ρ z) * deriv Real.smoothTransition (((k : ℝ) + 1) * Phi c ρ z)|
        * |(fderiv ℝ (Phi c ρ) z) (gradient v z)|
      ≤ C * ‖(fderiv ℝ (Phi c ρ) z) (gradient v z)‖ := by
        rw [Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg _)
    _ ≤ C * (‖fderiv ℝ (Phi c ρ) z‖ * ‖gradient v z‖) := by
        have hCnn : 0 ≤ C := by have := hC 0; simpa using this
        exact mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.le_opNorm (fderiv ℝ (Phi c ρ) z) (gradient v z)) hCnn
    _ = C * ‖fderiv ℝ (Phi c ρ) z‖ * ‖gradient v z‖ := by ring


private lemma eventually_one_le_mul {a : ℝ} (ha : 0 < a) :
    ∀ᶠ k : ℕ in atTop, 1 ≤ ((k : ℝ) + 1) * a := by
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (1 / a))] with k hk
  have h1 : (1 : ℝ) / a ≤ (Nat.ceil (1 / a) : ℝ) := Nat.le_ceil _
  have h1' : 1 ≤ (Nat.ceil (1 / a) : ℝ) * a := (div_le_iff₀ ha).mp h1
  have h2 : ((Nat.ceil (1 / a) : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h3 : 1 ≤ (k : ℝ) * a := le_trans h1' (mul_le_mul_of_nonneg_right h2 ha.le)
  nlinarith [h3, ha]

private lemma eventually_one_lt_mul {a : ℝ} (ha : 0 < a) :
    ∀ᶠ k : ℕ in atTop, 1 < ((k : ℝ) + 1) * a := by
  filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (2 / a))] with k hk
  have h1 : (2 : ℝ) / a ≤ (Nat.ceil (2 / a) : ℝ) := Nat.le_ceil _
  have h1' : 2 ≤ (Nat.ceil (2 / a) : ℝ) * a := (div_le_iff₀ ha).mp h1
  have h2 : ((Nat.ceil (2 / a) : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h3 : 2 ≤ (k : ℝ) * a := le_trans h1' (mul_le_mul_of_nonneg_right h2 ha.le)
  nlinarith [h3, ha]

private lemma tendsto_integral_G [Nonempty (Fin n)]
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (hv : ContDiff ℝ 2 v)
    (c : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun k : ℕ => ∫ z, (cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z
        - 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))
        + Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)))) atTop
      (𝓝 (∫ z in ball c ρ,
        (Phi c ρ z * Laplacian.laplacian v z - 2 * ((fderiv ℝ v z) (z - c))))) := by
  obtain ⟨C, hCpos, hC⟩ := deriv_smoothTransition_mul_self_bound
  have hPhi_c : Continuous (Phi c ρ) := (contDiff_Phi c ρ).continuous
  have hlap_c : Continuous (fun z : EuclideanSpace ℝ (Fin n) => Laplacian.laplacian v z) :=
    continuousOn_univ.mp (Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian
      isOpen_univ hv.contDiffOn)
  have hfderiv_c : Continuous (fun z : EuclideanSpace ℝ (Fin n) => fderiv ℝ v z) :=
    ((hv.fderiv_right (m := 1) (by norm_num)) : ContDiff ℝ 1 (fderiv ℝ v)).continuous
  have hfd_sub : Continuous (fun z : EuclideanSpace ℝ (Fin n) => (fderiv ℝ v z) (z - c)) :=
    hfderiv_c.clm_apply (continuous_id.sub continuous_const)
  have hgrad_c : Continuous (gradient v) := (contDiff_gradient' v hv).continuous
  have hfderivPhi_c : Continuous (fun z : EuclideanSpace ℝ (Fin n) => fderiv ℝ (Phi c ρ) z) :=
    ((contDiff_Phi c ρ).fderiv_right (m := 1) (by norm_num)).continuous
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun z => |Phi c ρ z| * |Laplacian.laplacian v z|
      + 2 * |(fderiv ℝ v z) (z - c)| + (C * ‖fderiv ℝ (Phi c ρ) z‖) * ‖gradient v z‖ with hg
  have hg_cont : ContinuousOn g (closedBall c ρ) := by
    rw [hg]
    exact ((((hPhi_c.abs).mul (hlap_c.abs)).add ((hfd_sub.abs).const_mul 2)).add
      (((hfderivPhi_c.norm).const_mul C).mul hgrad_c.norm)).continuousOn
  set bound : EuclideanSpace ℝ (Fin n) → ℝ := (closedBall c ρ).indicator g with hbound
  have hbound_int : Integrable bound := by
    rw [hbound]
    exact (hg_cont.integrableOn_compact (isCompact_closedBall c ρ)).integrable_indicator
      measurableSet_closedBall
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin n) =>
      (cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z
        - 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))
        + Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)))) volume := by
    intro k
    have hc1 : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
        cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z) :=
      ((contDiff_cut k c ρ).continuous.mul hPhi_c).mul hlap_c
    have hc2 : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
        2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))) :=
      ((contDiff_cut k c ρ).continuous.mul hfd_sub).const_mul 2
    have hc3 : Continuous (fun z : EuclideanSpace ℝ (Fin n) =>
        Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z))) :=
      hPhi_c.mul ((((contDiff_cut k c ρ).fderiv_right (m := 1) (by norm_num)).continuous).clm_apply
        hgrad_c)
    exact ((hc1.sub hc2).add hc3).aestronglyMeasurable
  have h_bound : ∀ k : ℕ, ∀ᵐ z ∂volume, ‖(cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z
        - 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))
        + Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)))‖ ≤ bound z := by
    intro k
    filter_upwards with z
    rw [hbound]
    by_cases hz : z ∈ closedBall c ρ
    · rw [Set.indicator_of_mem hz]
      rw [hg]
      have hb1 : ‖cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z‖
          ≤ |Phi c ρ z| * |Laplacian.laplacian v z| := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 : 0 ≤ cut k c ρ z := cut_nonneg k c ρ z
        have h2 : cut k c ρ z ≤ 1 := cut_le_one k c ρ z
        calc |cut k c ρ z| * |Phi c ρ z| * |Laplacian.laplacian v z|
            ≤ 1 * |Phi c ρ z| * |Laplacian.laplacian v z| := by
              apply mul_le_mul_of_nonneg_right
              · apply mul_le_mul_of_nonneg_right
                · rwa [abs_of_nonneg h1]
                · exact abs_nonneg _
              · exact abs_nonneg _
          _ = |Phi c ρ z| * |Laplacian.laplacian v z| := by rw [one_mul]
      have hb2 : ‖2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))‖
          ≤ 2 * |(fderiv ℝ v z) (z - c)| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul]
        have h1 := cut_nonneg k c ρ z
        have h2 := cut_le_one k c ρ z
        have h3 : |cut k c ρ z| ≤ 1 := by rw [abs_of_nonneg h1]; exact h2
        calc 2 * (|cut k c ρ z| * |(fderiv ℝ v z) (z - c)|)
            ≤ 2 * (1 * |(fderiv ℝ v z) (z - c)|) := by gcongr
          _ = 2 * |(fderiv ℝ v z) (z - c)| := by rw [one_mul]
      have hb3 : ‖Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z))‖
          ≤ (C * ‖fderiv ℝ (Phi c ρ) z‖) * ‖gradient v z‖ := by
        rw [Real.norm_eq_abs]
        exact Phi_mul_fderiv_cut_apply_bound k c ρ hC v z
      calc ‖(cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z
              - 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))
              + Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)))‖
          ≤ ‖cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z
              - 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))‖
            + ‖Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z))‖ := norm_add_le _ _
        _ ≤ (‖cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z‖
              + ‖2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))‖)
            + ‖Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z))‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ |Phi c ρ z| * |Laplacian.laplacian v z| + 2 * |(fderiv ℝ v z) (z - c)|
            + (C * ‖fderiv ℝ (Phi c ρ) z‖) * ‖gradient v z‖ := by linarith
    · rw [Set.indicator_of_notMem hz]
      have hneg : Phi c ρ z < 0 := by
        rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hz
        unfold Phi
        nlinarith [norm_nonneg (z - c)]
      have hcut0 : cut k c ρ z = 0 := cut_eq_zero_of_nonpos k c ρ hneg.le
      have ht : (((k : ℝ) + 1) * Phi c ρ z) < 0 :=
        mul_neg_of_pos_of_neg (by positivity) hneg
      have hder0 : deriv Real.smoothTransition (((k : ℝ) + 1) * Phi c ρ z) = 0 :=
        deriv_smoothTransition_eq_zero_of_neg ht
      have hfder0 : fderiv ℝ (cut k c ρ) z = 0 := by
        rw [fderiv_cut, hder0]; simp
      rw [hcut0, hfder0]
      simp
  have h_lim : ∀ᵐ z ∂volume, Tendsto (fun k : ℕ =>
      (cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z
        - 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))
        + Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)))) atTop
      (𝓝 (((ball c ρ).indicator (fun z =>
        (Phi c ρ z * Laplacian.laplacian v z - 2 * ((fderiv ℝ v z) (z - c))))) z)) := by
    filter_upwards with z
    by_cases hz : z ∈ ball c ρ
    · rw [Set.indicator_of_mem hz]
      have hΦ : 0 < Phi c ρ z := by
        rw [Metric.mem_ball, dist_eq_norm] at hz
        unfold Phi
        nlinarith [norm_nonneg (z - c)]
      have hcut_t : (fun k : ℕ => cut k c ρ z) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
        filter_upwards [eventually_one_le_mul hΦ] with k hk
        unfold cut
        rw [Real.smoothTransition.one_of_one_le hk]
      have hcut_lim : Tendsto (fun k : ℕ => cut k c ρ z) atTop (𝓝 1) :=
        Tendsto.congr' hcut_t.symm tendsto_const_nhds
      have hA : Tendsto (fun k : ℕ => cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z) atTop
          (𝓝 (Phi c ρ z * Laplacian.laplacian v z)) := by
        have := (hcut_lim.mul_const (Phi c ρ z)).mul_const (Laplacian.laplacian v z)
        simpa using this
      have hB : Tendsto (fun k : ℕ => 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))) atTop
          (𝓝 (2 * ((fderiv ℝ v z) (z - c)))) := by
        have := (hcut_lim.mul_const ((fderiv ℝ v z) (z - c))).const_mul 2
        simpa using this
      have hC3 : Tendsto (fun k : ℕ => Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)))
          atTop (𝓝 0) := by
        have hev : (fun k : ℕ => Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)))
            =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
          filter_upwards [eventually_one_lt_mul hΦ] with k hk
          have hder0 : deriv Real.smoothTransition (((k : ℝ) + 1) * Phi c ρ z) = 0 :=
            deriv_smoothTransition_eq_zero_of_one_lt hk
          rw [fderiv_cut, hder0]
          simp
        exact Tendsto.congr' hev.symm tendsto_const_nhds
      have hmain := (hA.sub hB).add hC3
      simpa using hmain
    · rw [Set.indicator_of_notMem hz]
      have hle : Phi c ρ z ≤ 0 := by
        rw [Metric.mem_ball, dist_eq_norm, not_lt] at hz
        unfold Phi
        nlinarith [norm_nonneg (z - c)]
      have hev : (fun k : ℕ =>
          (cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z
            - 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))
            + Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z))))
          =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
        filter_upwards with k
        have hcut0 : cut k c ρ z = 0 := cut_eq_zero_of_nonpos k c ρ hle
        have hC0 : Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)) = 0 := by
          rcases lt_or_eq_of_le hle with h | h
          · have ht : (((k : ℝ) + 1) * Phi c ρ z) < 0 :=
              mul_neg_of_pos_of_neg (by positivity) h
            rw [fderiv_cut, deriv_smoothTransition_eq_zero_of_neg ht]
            simp
          · rw [h]; ring
        rw [hcut0, hC0]; ring
      exact Tendsto.congr' hev.symm tendsto_const_nhds
  have := tendsto_integral_of_dominated_convergence bound hmeas hbound_int h_bound h_lim
  simpa only [integral_indicator measurableSet_ball] using this


open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace in
theorem integral_fderiv_sub_eq_half_integral_laplacian {n : ℕ} [Nonempty (Fin n)]
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (hv : ContDiff ℝ 2 v)
    (c : EuclideanSpace ℝ (Fin n)) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ y in Metric.ball c ρ, (fderiv ℝ v y) (y - c))
      = (1/2 : ℝ) * ∫ y in Metric.ball c ρ, (ρ ^ 2 - ‖y - c‖ ^ 2) * Laplacian.laplacian v y := by
  have hlim := tendsto_integral_G v hv c ρ hρ
  have hzero_seq : ∀ k : ℕ, ∫ z, (cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z
        - 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))
        + Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z))) = 0 := by
    intro k
    have hdiv : ∫ z, divE (Wfield k v c ρ) z = 0 := by
      unfold divE
      exact Commons.Analysis.MeasureTheory.integral_divergence_eq_zero_euclidean
        (Wfield k v c ρ) (contDiff_Wfield k v hv c ρ) (hasCompactSupport_Wfield k v c ρ hρ)
    rw [← hdiv]
    apply integral_congr_ae
    filter_upwards with z
    exact (divE_Wfield k v hv c ρ z).symm
  have hconst : Tendsto (fun k : ℕ => ∫ z, (cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z
        - 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))
        + Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)))) atTop (𝓝 0) := by
    have hfun : (fun k : ℕ => ∫ z, (cut k c ρ z * Phi c ρ z * Laplacian.laplacian v z
        - 2 * (cut k c ρ z * ((fderiv ℝ v z) (z - c)))
        + Phi c ρ z * ((fderiv ℝ (cut k c ρ) z) (gradient v z)))) = fun _ => (0:ℝ) :=
      funext fun k => hzero_seq k
    rw [hfun]
    exact tendsto_const_nhds
  have huniq : (∫ z in ball c ρ,
      (Phi c ρ z * Laplacian.laplacian v z - 2 * ((fderiv ℝ v z) (z - c)))) = 0 :=
    tendsto_nhds_unique hlim hconst
  have hPhi_c : Continuous (Phi c ρ) := (contDiff_Phi c ρ).continuous
  have hlap_c : Continuous (fun z : EuclideanSpace ℝ (Fin n) => Laplacian.laplacian v z) :=
    continuousOn_univ.mp (Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian
      isOpen_univ hv.contDiffOn)
  have hfd_sub_c : Continuous (fun z : EuclideanSpace ℝ (Fin n) => (fderiv ℝ v z) (z - c)) :=
    (((hv.fderiv_right (m := 1) (by norm_num)) : ContDiff ℝ 1 (fderiv ℝ v)).continuous).clm_apply
      (continuous_id.sub continuous_const)
  have h1 : IntegrableOn (fun z : EuclideanSpace ℝ (Fin n) =>
      Phi c ρ z * Laplacian.laplacian v z) (ball c ρ) volume :=
    (((hPhi_c.mul hlap_c).continuousOn).integrableOn_compact
      (isCompact_closedBall c ρ)).mono_set ball_subset_closedBall
  have h2 : IntegrableOn (fun z : EuclideanSpace ℝ (Fin n) =>
      2 * ((fderiv ℝ v z) (z - c))) (ball c ρ) volume :=
    (((hfd_sub_c.const_mul 2).continuousOn).integrableOn_compact
      (isCompact_closedBall c ρ)).mono_set ball_subset_closedBall
  have hsplit : (∫ z in ball c ρ,
        (Phi c ρ z * Laplacian.laplacian v z - 2 * ((fderiv ℝ v z) (z - c))))
      = (∫ z in ball c ρ, Phi c ρ z * Laplacian.laplacian v z)
        - 2 * (∫ z in ball c ρ, (fderiv ℝ v z) (z - c)) := by
    rw [integral_sub h1 h2, integral_const_mul]
  have hfin : (∫ z in ball c ρ, (fderiv ℝ v z) (z - c))
      = (1/2 : ℝ) * (∫ z in ball c ρ, Phi c ρ z * Laplacian.laplacian v z) := by
    linarith [huniq, hsplit]
  simpa [Phi] using hfin


end

end Commons.Analysis.Harmonic
