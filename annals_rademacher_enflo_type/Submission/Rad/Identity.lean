import Submission.Rad.Pisier
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal BigOperators Interval
noncomputable section
namespace RadType
open RademacherEnfloType

lemma biasW_mul_delta (θ : ℝ) {n : ℕ} (ξ : Ω n) (j : Fin n) (hsin : Real.sin θ ≠ 0) :
    biasW θ ξ * delta θ ξ j =
      (((ξ j : C) : ℝ) * Real.sin θ) *
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ))) / (2 : ℝ) ^ n := by
  unfold biasW delta
  have hB : (∏ k : Fin n, (1 + Real.cos θ * ((ξ k : C) : ℝ)) / 2) =
      (∏ k : Fin n, (1 + Real.cos θ * ((ξ k : C) : ℝ))) / (2 : ℝ) ^ n := by
    rw [Finset.prod_div_distrib]
    simp
  rw [hB]
  have hP : (∏ k : Fin n, (1 + Real.cos θ * ((ξ k : C) : ℝ))) =
      (1 + Real.cos θ * ((ξ j : C) : ℝ)) *
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ))) := by
    exact (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
      (f := fun k : Fin n => (1 + Real.cos θ * ((ξ k : C) : ℝ))) (a := j) (by simp)).symm
  rw [hP]
  rcases coe_real_eq (ξ j) with hz | hz
  · rw [hz]
    field_simp [hsin]
    ring_nf
    have hs2 : (Real.sin θ) ^ 2 = 1 - (Real.cos θ) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [hs2]
    ring
  · rw [hz]
    field_simp [hsin]
    ring_nf
    have hs2 : (Real.sin θ) ^ 2 = 1 - (Real.cos θ) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [hs2]
    ring

/-- `∑_j biasW·δ_j = -biasWderiv`. -/
lemma sum_biasW_mul_delta_eq_neg_biasWderiv (θ : ℝ) {n : ℕ} (ξ : Ω n) :
    (∑ j : Fin n, biasW θ ξ * delta θ ξ j) = - biasWderiv θ ξ := by
  by_cases hsin : Real.sin θ = 0
  · have hd : ∀ j : Fin n, delta θ ξ j = 0 := by
      intro j
      unfold delta
      simp [hsin]
    have hb : biasWderiv θ ξ = 0 := by
      unfold biasWderiv
      simp [hsin]
    simp [hd, hb]
  · have hA : ∀ j : Fin n, biasW θ ξ * delta θ ξ j =
        (((ξ j : C) : ℝ) * Real.sin θ) *
          (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ))) / (2 : ℝ) ^ n := by
        intro j
        exact biasW_mul_delta θ ξ j hsin
    have hL : (∑ j : Fin n, biasW θ ξ * delta θ ξ j) =
        (∑ j : Fin n, (((ξ j : C) : ℝ) * Real.sin θ) *
          (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ))) / (2 : ℝ) ^ n) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hA j
    have hR : - biasWderiv θ ξ =
        (∑ j : Fin n, (((ξ j : C) : ℝ) * Real.sin θ) *
          (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (1 + Real.cos θ * ((ξ k : C) : ℝ))) / (2 : ℝ) ^ n) := by
      unfold biasWderiv
      rw [← neg_div, ← Finset.sum_neg_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    exact hL.trans hR.symm

/-- The `j`-th term of the pointwise identity integrand, summed over `ξ`. -/
noncomputable def δSum1 (θ : ℝ) {n : ℕ} (j : Fin n) {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (f : Ω n → X) (x : Ω n) : X :=
  ∑ ξ : Ω n, (biasW θ ξ * delta θ ξ j) • f (mulΩ x ξ)

/-- The derivative-form heat integrand (finite sum). -/
noncomputable def dSum (θ : ℝ) {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : Ω n → X) (x : Ω n) : X :=
  ∑ ξ : Ω n, (biasWderiv θ ξ) • f (mulΩ x ξ)

/-- Flip is a bijection. -/
def flipEquiv {n : ℕ} (j : Fin n) : Ω n ≃ Ω n where
  toFun := flip j
  invFun := flip j
  left_inv := fun ξ => flip_flip j ξ
  right_inv := fun ξ => flip_flip j ξ

/-- `f - D_j f` is even under the flip of coordinate `j`. -/
lemma even_f_sub_D {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (j : Fin n) (f : Ω n → X) (y : Ω n) :
    (f - D j f) (flip j y) = (f - D j f) y := by
  unfold D
  have hupd : update (flip j y) j (-(flip j y) j) = y := by
    ext i
    by_cases h : i = j
    · subst i; simp [flip]
    · simp [flip, h]
  simp only [Pi.sub_apply]
  rw [hupd]
  rw [flip]
  module

/-- Sum of an odd weight times an even function is zero. -/
lemma sum_odd_smul_even_zero {n : ℕ} (j : Fin n) {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {w : Ω n → ℝ} (hw : ∀ ξ : Ω n, w (flip j ξ) = - w ξ)
    {H : Ω n → X} (hH : ∀ ξ : Ω n, H (flip j ξ) = H ξ) :
    (∑ ξ : Ω n, w ξ • H ξ) = 0 := by
  have hswap : (∑ ξ : Ω n, w ξ • H ξ) = ∑ η : Ω n, w (flip j η) • H (flip j η) := by
    exact (Equiv.sum_comp (flipEquiv j) (fun ξ : Ω n => w ξ • H ξ)).symm
  have hs : (∑ ξ : Ω n, w ξ • H ξ) = - (∑ ξ : Ω n, w ξ • H ξ) := by
    calc
      (∑ ξ : Ω n, w ξ • H ξ) = ∑ η : Ω n, w (flip j η) • H (flip j η) := hswap
      _ = ∑ η : Ω n, (- w η) • H η := by
            apply Finset.sum_congr rfl
            intro η hη
            rw [hw η, hH η]
      _ = - (∑ η : Ω n, w η • H η) := by
            simp [neg_smul]
  have hss : (∑ ξ : Ω n, w ξ • H ξ) + (∑ ξ : Ω n, w ξ • H ξ) = 0 := by
    exact neg_eq_iff_add_eq_zero.mp hs.symm
  calc
    (∑ ξ : Ω n, w ξ • H ξ)
        = (1 / 2 : ℝ) • ((∑ ξ : Ω n, w ξ • H ξ) + (∑ ξ : Ω n, w ξ • H ξ)) := by
          rw [smul_add, ← add_smul]
          norm_num
    _ = 0 := by
          rw [hss]
          simp

/-- Oddness of the weight `biasW·δ_j` under flipping coordinate `j`. -/
lemma weight_odd (θ : ℝ) {n : ℕ} (j : Fin n) (ξ : Ω n) :
    (biasW θ (flip j ξ) * delta θ (flip j ξ) j) = - (biasW θ ξ * delta θ ξ j) := by
  by_cases hsin : Real.sin θ = 0
  · have hd : ∀ η : Ω n, delta θ η j = 0 := by
      intro η
      unfold delta
      simp [hsin]
    simp [hd]
  · have hfl : (flip j ξ) j = - ξ j := by simp
    rw [biasW_mul_delta θ (flip j ξ) j hsin, biasW_mul_delta θ ξ j hsin]
    have hprod : (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j,
        (1 + Real.cos θ * (((flip j ξ) k : C) : ℝ))) =
        (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j,
        (1 + Real.cos θ * ((ξ k : C) : ℝ))) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      rw [flip_apply_of_ne (j := j) (i := k) hkj]
    rw [hfl, hprod]
    rw [neg_coe_real]
    ring

/-- Parity: the `δSum1`-form does not see `D_j` (only the symmetric part). -/
lemma δSum1_eq_δSum1_D (θ : ℝ) {n : ℕ} {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (j : Fin n) (f : Ω n → X) (x : Ω n) :
    δSum1 θ j f x = δSum1 θ j (D j f) x := by
  have hdiff : δSum1 θ j f x - δSum1 θ j (D j f) x =
      (∑ ξ : Ω n, (biasW θ ξ * delta θ ξ j) • ((f - D j f) (mulΩ x ξ))) := by
    unfold δSum1
    simp_rw [Pi.sub_apply, smul_sub]
    rw [Finset.sum_sub_distrib]
  have hzero : (∑ ξ : Ω n, (biasW θ ξ * delta θ ξ j) • ((f - D j f) (mulΩ x ξ))) = 0 := by
    apply sum_odd_smul_even_zero (j := j)
    · intro η
      exact weight_odd θ j η
    · intro η
      calc
        (f - D j f) (mulΩ x (flip j η)) = (f - D j f) (flip j (mulΩ x η)) := by
          rw [flip_mulΩ]
        _ = (f - D j f) (mulΩ x η) := even_f_sub_D j f (mulΩ x η)
  have hd : δSum1 θ j f x - δSum1 θ j (D j f) x = 0 := by
    rw [hdiff, hzero]
  exact sub_eq_zero.mp hd

/-- `dSum = -∑_j δSum1_j (D_j f)` (the X-valued integrand identity). -/
lemma dSum_eq_neg_sum_δSum1_D (θ : ℝ) {n : ℕ} {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (f : Ω n → X) (x : Ω n) :
    dSum θ f x = - (∑ j : Fin n, δSum1 θ j (D j f) x) := by
  have hfirst : dSum θ f x = - (∑ j : Fin n, δSum1 θ j f x) := by
    unfold dSum δSum1
    calc
      (∑ ξ : Ω n, (biasWderiv θ ξ) • f (mulΩ x ξ))
          = ∑ ξ : Ω n, - (∑ j : Fin n, (biasW θ ξ * delta θ ξ j) • f (mulΩ x ξ)) := by
            apply Finset.sum_congr rfl
            intro ξ hξ
            have h1 : (biasWderiv θ ξ) • f (mulΩ x ξ) =
                (- (∑ j : Fin n, biasW θ ξ * delta θ ξ j)) • f (mulΩ x ξ) := by
              congr 1
              have h1s := sum_biasW_mul_delta_eq_neg_biasWderiv θ ξ
              have h1' : biasWderiv θ ξ = - (∑ j : Fin n, biasW θ ξ * delta θ ξ j) := by
                simpa using (congrArg Neg.neg h1s).symm
              exact h1'
            rw [h1, neg_smul, Finset.sum_smul]
      _ = - (∑ ξ : Ω n, ∑ j : Fin n, (biasW θ ξ * delta θ ξ j) • f (mulΩ x ξ)) := by
            rw [Finset.sum_neg_distrib]
      _ = - (∑ j : Fin n, ∑ ξ : Ω n, (biasW θ ξ * delta θ ξ j) • f (mulΩ x ξ)) := by
            congr 1
            exact Finset.sum_comm
      _ = - (∑ j : Fin n, δSum1 θ j f x) := by
            rfl
  have hpar : (∑ j : Fin n, δSum1 θ j f x) = ∑ j : Fin n, δSum1 θ j (D j f) x := by
    apply Finset.sum_congr rfl
    intro j hj
    exact δSum1_eq_δSum1_D θ j f x
  rw [hfirst, hpar]



lemma continuous_biasW (θ : ℝ) {n : ℕ} (ξ : Ω n) : Continuous (fun t : ℝ => biasW t ξ) := by
  unfold biasW
  continuity

lemma continuous_biasWderiv (θ : ℝ) {n : ℕ} (ξ : Ω n) : Continuous (fun t : ℝ => biasWderiv t ξ) := by
  unfold biasWderiv
  continuity

lemma continuousOn_biasW {n : ℕ} (ξ : Ω n) : ContinuousOn (fun t : ℝ => biasW t ξ) (Set.Icc (0:ℝ) (Real.pi/2)) := by
  exact (continuous_biasW (0:ℝ) ξ).continuousOn

lemma continuousOn_biasWderiv {n : ℕ} (ξ : Ω n) : ContinuousOn (fun t : ℝ => biasWderiv t ξ) (Set.uIcc (0:ℝ) (Real.pi/2)) := by
  exact (continuous_biasWderiv (0:ℝ) ξ).continuousOn

/-- Scalar FTC for `biasW`: `∫_0^{π/2} biasWderiv = biasW(π/2) - biasW(0)`. -/
lemma biasW_integral_deriv {n : ℕ} (ξ : Ω n) :
    (∫ t in (0)..(Real.pi / 2), biasWderiv t ξ) = biasW (Real.pi / 2) ξ - biasW 0 ξ := by
  have hab : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (E := ℝ) hab (f := fun t : ℝ => biasW t ξ) (f' := fun t : ℝ => biasWderiv t ξ)
    (continuousOn_biasW ξ) (by intro x hx; simpa using biasW_hasDerivAt x ξ)
    ((continuousOn_biasWderiv ξ).intervalIntegrable)

/-- X-valued FTC for the heat semigroup: `∫_0^{π/2} dSum-form = meanX f - f x`. -/
lemma heat_integral_deriv {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (f : Ω n → X) (x : Ω n) :
    (∫ θ in (0)..(Real.pi / 2), dSum θ f x)
      = meanX f - f x := by
  unfold dSum
  have hstep1 : (∫ θ in (0)..(Real.pi / 2), (∑ ξ : Ω n, (biasWderiv θ ξ) • f (mulΩ x ξ))) =
      (∑ ξ : Ω n, ∫ θ in (0)..(Real.pi / 2), (biasWderiv θ ξ) • f (mulΩ x ξ)) := by
    rw [intervalIntegral.integral_finsetSum]
    intro ξ hξ
    refine ContinuousOn.intervalIntegrable ?_
    have hc : Continuous (fun θ : ℝ => biasWderiv θ ξ) := continuous_biasWderiv 0 ξ
    have hcv : Continuous (fun θ : ℝ => (biasWderiv θ ξ) • f (mulΩ x ξ)) := hc.smul continuous_const
    exact hcv.continuousOn
  have hstep2 : (∑ ξ : Ω n, ∫ θ in (0)..(Real.pi / 2), (biasWderiv θ ξ) • f (mulΩ x ξ)) =
      (∑ ξ : Ω n, (∫ θ in (0)..(Real.pi / 2), biasWderiv θ ξ) • f (mulΩ x ξ)) := by
    apply Finset.sum_congr rfl
    intro ξ hξ
    exact intervalIntegral.integral_smul_const (μ := MeasureTheory.volume)
      (f := fun θ : ℝ => biasWderiv θ ξ) (c := f (mulΩ x ξ))
  have hstep3 : (∑ ξ : Ω n, (∫ θ in (0)..(Real.pi / 2), biasWderiv θ ξ) • f (mulΩ x ξ)) =
      (∑ ξ : Ω n, (biasW (Real.pi / 2) ξ - biasW 0 ξ) • f (mulΩ x ξ)) := by
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [biasW_integral_deriv ξ]
  have hstep4 : (∑ ξ : Ω n, (biasW (Real.pi / 2) ξ - biasW 0 ξ) • f (mulΩ x ξ)) =
      (∑ ξ : Ω n, (biasW (Real.pi / 2) ξ) • f (mulΩ x ξ)) -
        (∑ ξ : Ω n, (biasW 0 ξ) • f (mulΩ x ξ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [sub_smul]
  rw [hstep1, hstep2, hstep3, hstep4]
  change heat (Real.pi / 2) f x - heat 0 f x = meanX f - f x
  rw [heat_pi_half f x, heat_zero f x]

/-- Pointwise (all `θ`) integrand identity (from the parity computation). -/
lemma pointwise_integrand_eq_neg_dSum {n : ℕ} {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (θ : ℝ) (f : Ω n → X) (x : Ω n) :
    (∑ j : Fin n, δSum1 θ j (D j f) x) = - dSum θ f x := by
  have h := dSum_eq_neg_sum_δSum1_D θ f x
  have hneg := congrArg Neg.neg h
  simpa using hneg.symm

/-- The pointwise identity (interval form): `∫_0^{π/2} Σ_j δSum1_j(D_jf) = f x - meanX f`. -/
lemma interval_identity {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (f : Ω n → X) (x : Ω n) :
    (∫ θ in (0)..(Real.pi / 2), (∑ j : Fin n, δSum1 θ j (D j f) x)) = f x - meanX f := by
  calc
    (∫ θ in (0)..(Real.pi / 2), (∑ j : Fin n, δSum1 θ j (D j f) x))
        = ∫ θ in (0)..(Real.pi / 2), - dSum θ f x := by
            apply intervalIntegral.integral_congr
            intro θ hθ
            exact pointwise_integrand_eq_neg_dSum θ f x
    _ = - (∫ θ in (0)..(Real.pi / 2), dSum θ f x) := by
            rw [intervalIntegral.integral_neg]
    _ = f x - meanX f := by
            rw [heat_integral_deriv f x]
            abel



/-- The biased-expectation form of the pointwise integrand. -/
noncomputable def Jint (θ : ℝ) {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (f : Ω n → X) (x : Ω n) : X :=
  ∫ ξ : Ω n, (∑ j : Fin n, (delta θ ξ j) • (D j f) (mulΩ x ξ))
    ∂(biasedMeasure (n := n) θ)

/-- The finite-sum form of the integrand equals its biased-expectation form. -/
lemma Jsum_eq_Jint {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (θ : ℝ) (f : Ω n → X) (x : Ω n) :
    (∑ j : Fin n, δSum1 θ j (D j f) x) = Jint θ f x := by
  unfold δSum1 Jint
  -- swap: ∫_ξ (Σ_j h_j) = Σ_j ∫_ξ h_j
  have hswap : (∫ ξ : Ω n, (∑ j : Fin n, (delta θ ξ j) • (D j f) (mulΩ x ξ))
      ∂(biasedMeasure (n := n) θ))
      = (∑ j : Fin n, ∫ ξ : Ω n, (delta θ ξ j) • (D j f) (mulΩ x ξ)
          ∂(biasedMeasure (n := n) θ)) := by
    rw [MeasureTheory.integral_finsetSum]
    intro j hj
    exact integrable_biased θ (fun ξ : Ω n => (delta θ ξ j) • (D j f) (mulΩ x ξ))
  rw [hswap]
  apply Finset.sum_congr rfl
  intro j hj
  -- per j: δSum1-side Σ_ξ (biasW·δ_j)•(D_jf)(xξ) equals ∫_ξ (δ_j)•(D_jf)(xξ) dρθ
  have h1 : (∫ ξ : Ω n, (delta θ ξ j) • (D j f) (mulΩ x ξ) ∂(biasedMeasure (n := n) θ))
      = ∑ ξ : Ω n, (biasW θ ξ) • ((delta θ ξ j) • (D j f) (mulΩ x ξ)) := by
    exact integral_biased_eq θ (fun ξ : Ω n => (delta θ ξ j) • (D j f) (mulΩ x ξ))
  calc
    (∑ ξ : Ω n, (biasW θ ξ * delta θ ξ j) • (D j f) (mulΩ x ξ))
        = ∑ ξ : Ω n, (biasW θ ξ) • ((delta θ ξ j) • (D j f) (mulΩ x ξ)) := by
            apply Finset.sum_congr rfl
            intro ξ hξ
            rw [← smul_smul]
    _ = ∫ ξ : Ω n, (delta θ ξ j) • (D j f) (mulΩ x ξ) ∂(biasedMeasure (n := n) θ) := h1.symm

/-- The pointwise identity in the `ν`-probability form:
`f x - meanX f = (π/2) · ∫ Jint dν`. -/
lemma identity_nu {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (f : Ω n → X) (x : Ω n) :
    f x - meanX f = (Real.pi / 2) • (∫ θ : ℝ, Jint θ f x ∂thetaMeasure) := by
  have hconv : (∫ θ : ℝ, Jint θ f x ∂thetaMeasure)
      = (2 / Real.pi) • (∫ θ in (0)..(Real.pi / 2), Jint θ f x) := by
    unfold thetaMeasure thetaSet
    rw [MeasureTheory.integral_smul_measure]
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 : ℝ) / Real.pi)]
    congr 1
    rw [intervalIntegral.integral_of_le]
    positivity
  -- Jint interval integral = f x - meanX f via Jsum_eq_Jint + interval_identity
  have hinter : (∫ θ in (0)..(Real.pi / 2), Jint θ f x) = f x - meanX f := by
    calc
      (∫ θ in (0)..(Real.pi / 2), Jint θ f x)
          = ∫ θ in (0)..(Real.pi / 2), (∑ j : Fin n, δSum1 θ j (D j f) x) := by
            apply intervalIntegral.integral_congr
            intro θ hθ
            exact (Jsum_eq_Jint θ f x).symm
      _ = f x - meanX f := interval_identity f x
  calc
    f x - meanX f = (Real.pi / 2) • ((2 / Real.pi) • (f x - meanX f)) := by
          have hc : (Real.pi / 2) * (2 / Real.pi) = 1 := by field_simp [Real.pi_ne_zero]
          rw [smul_smul, hc]
          simp
    _ = (Real.pi / 2) • (∫ θ : ℝ, Jint θ f x ∂thetaMeasure) := by
          rw [hconv, hinter]

end RadType
end
