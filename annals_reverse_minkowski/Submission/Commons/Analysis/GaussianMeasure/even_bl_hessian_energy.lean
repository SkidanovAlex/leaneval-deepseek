import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.bl_gradient_odd

open MeasureTheory Filter
open scoped RealInnerProductSpace BigOperators

namespace Commons.Analysis.GaussianMeasure

/-- The square of the operator norm of a real linear functional, expanded in an orthonormal
basis. -/
lemma continuousLinearMap_norm_sq_eq_sum_apply_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (φ : E →L[ℝ] ℝ) :
    ‖φ‖ ^ 2 = ∑ i : ι, (φ (b i)) ^ 2 := by
  have hv : ∀ i : ι, φ (b i) = ⟪(InnerProductSpace.toDual ℝ E).symm φ, b i⟫ := by
    intro i; rw [InnerProductSpace.toDual_symm_apply]
  have hnorm : ‖φ‖ = ‖(InnerProductSpace.toDual ℝ E).symm φ‖ := by
    rw [← (InnerProductSpace.toDual ℝ E).symm.norm_map φ]
  simp only [hv]
  rw [hnorm]
  exact (OrthonormalBasis.sum_sq_inner_left b _).symm

/-- For an even differentiable function, the derivative is odd. -/
private lemma fderiv_even_eq_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} (hu : Differentiable ℝ u) (hueven : ∀ x, u (-x) = u x) (x : E) :
    fderiv ℝ u (-x) = - fderiv ℝ u x := by
  have hdiff_neg : DifferentiableAt ℝ (fun y : E => -y) x := by fun_prop
  have hcomp := fderiv_comp x (hu.differentiableAt) hdiff_neg
  have heq : (fun y : E => u (-y)) = u := funext hueven
  rw [Function.comp_def] at hcomp
  rw [heq] at hcomp
  have hneg : fderiv ℝ (fun y : E => -y) x = - ContinuousLinearMap.id ℝ E := by
    have h1 : (fun y : E => -y) = - id := by funext y; simp
    rw [h1, fderiv_neg, fderiv_id]
  rw [hneg] at hcomp
  apply ContinuousLinearMap.ext
  intro v
  have h2 : ((fderiv ℝ u (-x)).comp (- ContinuousLinearMap.id ℝ E)) v
      = - (fderiv ℝ u (-x)) v := by simp
  have hcongr := congrArg (fun (L : E →L[ℝ] ℝ) => L v) hcomp
  simp only [h2] at hcongr
  simp only [neg_apply]
  linarith [hcongr]

theorem even_bl_hessian_energy {n : ℕ} (f u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (hfe : ∀ x, f (-x) = f x)
    (hH : ∀ x v : EuclideanSpace ℝ (Fin n), 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2))
    (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n),
      |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2)
    (hu : ContDiff ℝ 2 u) (hueven : ∀ x, u (-x) = u x)
    (hgu : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v w : EuclideanSpace ℝ (Fin n),
      |u x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ u) x v w| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ * ‖w‖) :
    2 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
      ≤ ∫ x, (∑ i : Fin n, ∑ j : Fin n,
            ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
              (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)) := by
  classical
  obtain ⟨C, hC0, N, hguB⟩ := hgu
  let h : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun j x => fderiv ℝ u x (EuclideanSpace.single j 1)
  -- smoothness of the partials
  have hsm : ∀ j : Fin n, ContDiff ℝ 1 (h j) := by
    intro j
    have h1 : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) => fderiv ℝ u x) :=
      hu.fderiv_right (m := 1) (by norm_num)
    exact h1.clm_apply contDiff_const
  -- oddness of the partials
  have hodd : ∀ j : Fin n, ∀ x : EuclideanSpace ℝ (Fin n), h j (-x) = - h j x := by
    intro j x
    have hd : Differentiable ℝ u := hu.differentiable (by norm_num)
    show fderiv ℝ u (-x) (EuclideanSpace.single j 1) = - (fderiv ℝ u x (EuclideanSpace.single j 1))
    rw [fderiv_even_eq_neg hd hueven x]
    simp
  -- polynomial bound for the partials
  have hbound_h : ∀ (j : Fin n) (x : EuclideanSpace ℝ (Fin n)),
      |h j x| ≤ C * (1 + ‖x‖) ^ N := by
    intro j x
    have hb := (hguB x (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)).2.1
    have hn : ‖(EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin n))‖ = 1 := by simp
    rw [hn, mul_one] at hb
    simpa only [h] using hb
  -- rewriting the derivative of a partial
  have hfderiv_partial_apply : ∀ (j : Fin n) (x v : EuclideanSpace ℝ (Fin n)),
      fderiv ℝ (h j) x v
        = (fderiv ℝ (fderiv ℝ u) x v) (EuclideanSpace.single j 1) := by
    intro j x v
    show fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => fderiv ℝ u y (EuclideanSpace.single j 1)) x v
        = (fderiv ℝ (fderiv ℝ u) x v) (EuclideanSpace.single j 1)
    have h1 : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) => fderiv ℝ u x) :=
      hu.fderiv_right (m := 1) (by norm_num)
    have hc : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => fderiv ℝ u y) x :=
      (h1.differentiable (by norm_num)).differentiableAt
    have hu' : DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) => (EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin n))) x :=
      differentiableAt_const _
    have hclm := fderiv_clm_apply
      (c := fun y : EuclideanSpace ℝ (Fin n) => fderiv ℝ u y)
      (u := fun _ : EuclideanSpace ℝ (Fin n) => (EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin n))) hc hu'
    rw [hclm]
    have hzero : fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) =>
        (EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin n))) x = 0 := fderiv_const_apply _
    rw [hzero, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  -- growth bound for the derivative of a partial (for `bl_gradient_odd`)
  have hgh : ∀ j : Fin n, ∃ C' : ℝ, 0 ≤ C' ∧ ∃ N' : ℕ,
      ∀ x v : EuclideanSpace ℝ (Fin n),
        |h j x| ≤ C' * (1 + ‖x‖) ^ N' ∧ |fderiv ℝ (h j) x v| ≤ C' * (1 + ‖x‖) ^ N' * ‖v‖ := by
    intro j
    refine ⟨C, hC0, N, fun x v => ⟨hbound_h j x, ?_⟩⟩
    rw [hfderiv_partial_apply j x v]
    have hb := (hguB x v (EuclideanSpace.single j 1)).2.2
    have hn : ‖(EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin n))‖ = 1 := by simp
    rw [hn, mul_one] at hb
    exact hb
  -- Brascamp–Lieb for each partial
  have hBL : ∀ j : Fin n,
      2 * Real.pi * (∫ x, (h j x) ^ 2 * Real.exp (-(f x)))
        ≤ ∫ x, ‖fderiv ℝ (h j) x‖ ^ 2 * Real.exp (-(f x)) := by
    intro j
    exact bl_gradient_odd f (h j) hf hfe hH hconv hgf (hsm j) (hodd j) (hgh j)
  -- norm expansion (first level)
  have hnorm_u : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖fderiv ℝ u x‖ ^ 2 = ∑ j : Fin n, (h j x) ^ 2 := by
    intro x
    rw [continuousLinearMap_norm_sq_eq_sum_apply_sq (EuclideanSpace.basisFun (Fin n) ℝ) (fderiv ℝ u x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [EuclideanSpace.basisFun_apply]
  -- norm expansion (second level)
  have hnorm_partial : ∀ (j : Fin n) (x : EuclideanSpace ℝ (Fin n)),
      ‖fderiv ℝ (h j) x‖ ^ 2
        = ∑ i : Fin n, ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
              (EuclideanSpace.single j 1)) ^ 2 := by
    intro j x
    rw [continuousLinearMap_norm_sq_eq_sum_apply_sq (EuclideanSpace.basisFun (Fin n) ℝ) (fderiv ℝ (h j) x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, hfderiv_partial_apply j x]
  -- continuity of the second derivative
  have hcont2 : Continuous (fun x : EuclideanSpace ℝ (Fin n) => fderiv ℝ (fderiv ℝ u) x) := by
    have hF : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) => fderiv ℝ u x) :=
      hu.fderiv_right (m := 1) (by norm_num)
    exact (hF.fderiv_right (m := 0) (by norm_num)).continuous
  -- integrability of the partial-energy terms
  have hInt_h : ∀ j : Fin n,
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => (h j x) ^ 2 * Real.exp (-(f x))) := by
    intro j
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (h j x) ^ 2) :=
      (hsm j).continuous.pow 2
    have hb : ∀ x : EuclideanSpace ℝ (Fin n),
        |(h j x) ^ 2| ≤ C ^ 2 * (1 + ‖x‖) ^ (2 * N) := by
      intro x
      have hb0 := hbound_h j x
      rw [abs_of_nonneg (sq_nonneg _)]
      calc (h j x) ^ 2 = |h j x| ^ 2 := by rw [sq_abs]
        _ ≤ (C * (1 + ‖x‖) ^ N) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb0 2
        _ = C ^ 2 * (1 + ‖x‖) ^ (2 * N) := by rw [mul_pow, ← pow_mul, Nat.mul_comm N 2]
    exact integrable_mul_exp_neg_stronglyConvex f (fun x : EuclideanSpace ℝ (Fin n) => (h j x) ^ 2)
      hf hconv hcont (C ^ 2) (sq_nonneg C) (2 * N) hb
  -- integrability of the Hessian-energy terms
  have hInt_A : ∀ i j : Fin n,
      Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
        (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
            (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x))) := by
    intro i j
    have hcontA : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
        (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) :=
      (hcont2.clm_apply continuous_const).clm_apply continuous_const
    have hcontAsq : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
        ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2) :=
      hcontA.pow 2
    have hb : ∀ x : EuclideanSpace ℝ (Fin n),
        |((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
            (EuclideanSpace.single j 1)) ^ 2| ≤ C ^ 2 * (1 + ‖x‖) ^ (2 * N) := by
      intro x
      have hb0 := (hguB x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)).2.2
      have hni : ‖(EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin n))‖ = 1 := by simp
      have hnj : ‖(EuclideanSpace.single j 1 : EuclideanSpace ℝ (Fin n))‖ = 1 := by simp
      rw [hni, hnj, mul_one, mul_one] at hb0
      rw [abs_of_nonneg (sq_nonneg _)]
      calc ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
              (EuclideanSpace.single j 1)) ^ 2
          = |(fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
              (EuclideanSpace.single j 1)| ^ 2 := by rw [sq_abs]
        _ ≤ (C * (1 + ‖x‖) ^ N) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb0 2
        _ = C ^ 2 * (1 + ‖x‖) ^ (2 * N) := by rw [mul_pow, ← pow_mul, Nat.mul_comm N 2]
    exact integrable_mul_exp_neg_stronglyConvex f
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)) (EuclideanSpace.single j 1)) ^ 2)
      hf hconv hcontAsq (C ^ 2) (sq_nonneg C) (2 * N) hb
  -- first level of integration of the sums
  have hL : (∫ x : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
      = ∑ j : Fin n, ∫ x : EuclideanSpace ℝ (Fin n), (h j x) ^ 2 * Real.exp (-(f x)) := by
    have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
        ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))
          = ∑ j : Fin n, ((h j x) ^ 2 * Real.exp (-(f x))) := by
      intro x
      rw [hnorm_u x, Finset.sum_mul]
    calc (∫ x : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
        = ∫ x : EuclideanSpace ℝ (Fin n),
            ∑ j : Fin n, ((h j x) ^ 2 * Real.exp (-(f x))) :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = ∑ j : Fin n, ∫ x : EuclideanSpace ℝ (Fin n), (h j x) ^ 2 * Real.exp (-(f x)) := by
          simpa using integral_finsetSum (Finset.univ : Finset (Fin n))
            (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hInt_h j)
  -- second level of integration (per partial)
  have hRj : ∀ j : Fin n,
      (∫ x : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ (h j) x‖ ^ 2 * Real.exp (-(f x)))
        = ∑ i : Fin n, ∫ x : EuclideanSpace ℝ (Fin n),
            (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
              (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)) := by
    intro j
    have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
        ‖fderiv ℝ (h j) x‖ ^ 2 * Real.exp (-(f x))
          = ∑ i : Fin n, ((((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
                (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x))) := by
      intro x
      rw [hnorm_partial j x, Finset.sum_mul]
    calc (∫ x : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ (h j) x‖ ^ 2 * Real.exp (-(f x)))
        = ∫ x : EuclideanSpace ℝ (Fin n),
            ∑ i : Fin n, ((((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
                (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x))) :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = ∑ i : Fin n, ∫ x : EuclideanSpace ℝ (Fin n),
            (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
              (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)) := by
          simpa using integral_finsetSum (Finset.univ : Finset (Fin n))
            (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hInt_A i j)
  -- the full right-hand side
  have hR : (∫ x : EuclideanSpace ℝ (Fin n),
        (∑ i : Fin n, ∑ j : Fin n,
          ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
            (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)))
      = ∑ i : Fin n, ∑ j : Fin n, ∫ x : EuclideanSpace ℝ (Fin n),
          (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
            (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)) := by
    have hpt : ∀ x : EuclideanSpace ℝ (Fin n),
        (∑ i : Fin n, ∑ j : Fin n,
          ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
            (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x))
          = ∑ p : Fin n × Fin n,
              (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single p.1 1))
                (EuclideanSpace.single p.2 1)) ^ 2) * Real.exp (-(f x)) := by
      intro x
      rw [Finset.sum_mul]
      simp only [Finset.sum_mul]
      exact (Fintype.sum_prod_type (fun p : Fin n × Fin n =>
        (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single p.1 1))
          (EuclideanSpace.single p.2 1)) ^ 2) * Real.exp (-(f x)))).symm
    calc (∫ x : EuclideanSpace ℝ (Fin n),
            (∑ i : Fin n, ∑ j : Fin n,
              ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
                (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)))
        = ∫ x : EuclideanSpace ℝ (Fin n), ∑ p : Fin n × Fin n,
            (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single p.1 1))
              (EuclideanSpace.single p.2 1)) ^ 2) * Real.exp (-(f x)) :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = ∑ p : Fin n × Fin n, ∫ x : EuclideanSpace ℝ (Fin n),
            (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single p.1 1))
              (EuclideanSpace.single p.2 1)) ^ 2) * Real.exp (-(f x)) := by
          simpa using integral_finsetSum (Finset.univ : Finset (Fin n × Fin n))
            (fun p (_ : p ∈ (Finset.univ : Finset (Fin n × Fin n))) => hInt_A p.1 p.2)
      _ = ∑ i : Fin n, ∑ j : Fin n, ∫ x : EuclideanSpace ℝ (Fin n),
            (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
              (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)) := by
          exact Fintype.sum_prod_type (fun p : Fin n × Fin n => ∫ x : EuclideanSpace ℝ (Fin n),
            (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single p.1 1))
              (EuclideanSpace.single p.2 1)) ^ 2) * Real.exp (-(f x)))
  calc 2 * Real.pi * (∫ x : EuclideanSpace ℝ (Fin n), ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
      = 2 * Real.pi * (∑ j : Fin n, ∫ x : EuclideanSpace ℝ (Fin n),
            (h j x) ^ 2 * Real.exp (-(f x))) := by rw [hL]
    _ = ∑ j : Fin n, 2 * Real.pi * (∫ x : EuclideanSpace ℝ (Fin n),
            (h j x) ^ 2 * Real.exp (-(f x))) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin n, (∫ x : EuclideanSpace ℝ (Fin n),
            ‖fderiv ℝ (h j) x‖ ^ 2 * Real.exp (-(f x))) :=
          Finset.sum_le_sum (fun j _ => hBL j)
    _ = ∑ j : Fin n, ∑ i : Fin n, ∫ x : EuclideanSpace ℝ (Fin n),
            (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
              (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)) := by
          refine Finset.sum_congr rfl (fun j _ => hRj j)
    _ = ∑ i : Fin n, ∑ j : Fin n, ∫ x : EuclideanSpace ℝ (Fin n),
            (((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
              (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)) :=
          Finset.sum_comm
    _ = ∫ x : EuclideanSpace ℝ (Fin n),
          (∑ i : Fin n, ∑ j : Fin n,
            ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1))
              (EuclideanSpace.single j 1)) ^ 2) * Real.exp (-(f x)) := hR.symm


end Commons.Analysis.GaussianMeasure
