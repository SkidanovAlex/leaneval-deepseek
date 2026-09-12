import Submission.Rad.BiasedType
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal BigOperators Interval
noncomputable section
namespace RadType
open RademacherEnfloType

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

lemma deltaJ {n : ℕ} (θ : ℝ) (hsin : Real.sin θ ≠ 0) (u : Fin n → X) (ξ : Ω n) {p : ℝ} (hp1 : 1 ≤ p) :
    ‖∑ j : Fin n, (delta θ ξ j) • u j‖ ^ p ≤
      (∑ y : Ω n, biasW θ y * ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ p) := by
  have hp0 : 0 ≤ p := by linarith
  -- V := fun y => Σ_j ((ξj−yj)/s) • u_j : Ωn → X
  let V : Ω n → X := fun y => ∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j
  -- Σ_j δ_j u_j = ∫_y V dρθ
  have hlin : (∑ j : Fin n, (delta θ ξ j) • u j) = ∫ y : Ω n, V y ∂(biasedMeasure (n := n) θ) := by
    calc
      (∑ j : Fin n, (delta θ ξ j) • u j)
          = ∑ j : Fin n, (∫ y : Ω n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ)
              ∂(biasedMeasure (n := n) θ)) • u j := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [delta_as_integral θ j ξ hsin]
      _ = ∫ y : Ω n, (∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)
              ∂(biasedMeasure (n := n) θ) := by
              -- Σ_j (∫ s_j) • u_j = ∫ Σ_j s_j • u_j
              have hswap : (∫ y : Ω n, (∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)
                  ∂(biasedMeasure (n := n) θ))
                  = ∑ j : Fin n, ∫ y : Ω n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j
                      ∂(biasedMeasure (n := n) θ) := by
                rw [MeasureTheory.integral_finsetSum]
                intro j hj
                exact integrable_biased θ (fun y : Ω n => ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)
              rw [hswap]
              apply Finset.sum_congr rfl
              intro j hj
              rw [integral_smul_const]
      _ = ∫ y : Ω n, V y ∂(biasedMeasure (n := n) θ) := rfl
  -- Jensen 1: ‖∫V‖ ≤ ∫‖V‖
  have hj1 : ‖∫ y : Ω n, V y ∂(biasedMeasure (n := n) θ)‖ ≤
      ∫ y : Ω n, ‖V y‖ ∂(biasedMeasure (n := n) θ) := by
    exact norm_integral_le_integral_norm _
  -- Jensen 2 power: (∫‖V‖)^p ≤ ∫‖V‖^p
  have hj2 : (∫ y : Ω n, ‖V y‖ ∂(biasedMeasure (n := n) θ)) ^ p ≤
      (∫ y : Ω n, ‖V y‖ ^ p ∂(biasedMeasure (n := n) θ)) := by
    exact Commons.Analysis.Integral.jensen_rpow_prob (μ := biasedMeasure (n := n) θ) hp1
      (by apply ae_of_all; intro y; exact norm_nonneg (V y))
      (integrable_biased θ (fun y : Ω n => ‖V y‖))
      (integrable_biased θ (fun y : Ω n => ‖V y‖ ^ p))
  have hconv : (∫ y : Ω n, ‖V y‖ ^ p ∂(biasedMeasure (n := n) θ)) =
      ∑ y : Ω n, biasW θ y * ‖V y‖ ^ p := by
    rw [integral_biased_eq θ (fun y : Ω n => ‖V y‖ ^ p)]
    simp
  calc
    ‖∑ j : Fin n, (delta θ ξ j) • u j‖ ^ p
        = ‖∫ y : Ω n, V y ∂(biasedMeasure (n := n) θ)‖ ^ p := by rw [← hlin]
    _ ≤ (∫ y : Ω n, ‖V y‖ ∂(biasedMeasure (n := n) θ)) ^ p := by
          exact Real.rpow_le_rpow (norm_nonneg _) hj1 hp0
    _ ≤ (∫ y : Ω n, ‖V y‖ ^ p ∂(biasedMeasure (n := n) θ)) := hj2
    _ = ∑ y : Ω n, biasW θ y * ‖V y‖ ^ p := hconv
    _ = ∑ y : Ω n, biasW θ y * ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ p := by
          rfl



/-- splitting: a double product-weight sum factors. -/
lemma double_sum_factor {n : ℕ} (θ : ℝ) (f g : Ω n → ℝ) :
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * f ξ * g y)
      = (∑ ξ : Ω n, biasW θ ξ * f ξ) * (∑ y : Ω n, biasW θ y * g y) := by
  calc
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * f ξ * g y)
        = ∑ ξ : Ω n, (biasW θ ξ * f ξ) * (∑ y : Ω n, biasW θ y * g y) := by
            apply Finset.sum_congr rfl
            intro ξ hξ
            calc
              (∑ y : Ω n, biasW θ ξ * biasW θ y * f ξ * g y)
                  = ∑ y : Ω n, (biasW θ ξ * f ξ) * (biasW θ y * g y) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      ring
              _ = (biasW θ ξ * f ξ) * (∑ y : Ω n, biasW θ y * g y) := by
                      rw [Finset.mul_sum]
    _ = (∑ ξ : Ω n, biasW θ ξ * f ξ) * (∑ y : Ω n, biasW θ y * g y) := by
          rw [← Finset.sum_mul]

/-- `P(ξ_j ≠ y_j)` for two independent biased copies is `sin²θ/2`. -/
lemma prob_diff_coord {n : ℕ} (θ : ℝ) (j : Fin n) :
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * (if (ξ j) ≠ (y j) then (1 : ℝ) else 0))
      = (1 - (Real.cos θ)^2) / 2 := by
  -- split indicator: ξj≠yj on two points = [ξj=cOne][yj=cNegOne] + [ξj=cNegOne][yj=cOne]
  have hsplit : ∀ ξ y : Ω n,
      (if (ξ j) ≠ (y j) then (1 : ℝ) else 0) =
        (if (ξ j) = cOne then (1 : ℝ) else 0) * (if (y j) = cNegOne then (1 : ℝ) else 0) +
        (if (ξ j) = cNegOne then (1 : ℝ) else 0) * (if (y j) = cOne then (1 : ℝ) else 0) := by
    intro ξ y
    rcases mem_two (ξ j) with hx | hx
    · rcases mem_two (y j) with hy | hy
      · rw [hx, hy]
        simp [cOne_ne_cNegOne]
      · rw [hx, hy]
        simp [cOne_ne_cNegOne]
    · rcases mem_two (y j) with hy | hy
      · rw [hx, hy]
        simp [cNegOne_ne_cOne]
      · rw [hx, hy]
        simp [cNegOne_ne_cOne]
  calc
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * (if (ξ j) ≠ (y j) then (1 : ℝ) else 0))
        = (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
            ((if (ξ j) = cOne then (1 : ℝ) else 0) * (if (y j) = cNegOne then (1 : ℝ) else 0) +
             (if (ξ j) = cNegOne then (1 : ℝ) else 0) * (if (y j) = cOne then (1 : ℝ) else 0))) := by
            apply Finset.sum_congr rfl
            intro ξ hξ
            apply Finset.sum_congr rfl
            intro y hy
            rw [hsplit ξ y]
    _ = (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
          (if (ξ j) = cOne then (1 : ℝ) else 0) * (if (y j) = cNegOne then (1 : ℝ) else 0)) +
        (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
          (if (ξ j) = cNegOne then (1 : ℝ) else 0) * (if (y j) = cOne then (1 : ℝ) else 0)) := by
          simp_rw [mul_add]
          simp_rw [Finset.sum_add_distrib]
          congr 1
          · apply Finset.sum_congr rfl
            intro ξ hξ
            apply Finset.sum_congr rfl
            intro y hy
            ring
          · apply Finset.sum_congr rfl
            intro ξ hξ
            apply Finset.sum_congr rfl
            intro y hy
            ring
    _ = ((∑ ξ : Ω n, biasW θ ξ * (if (ξ j) = cOne then (1 : ℝ) else 0)) *
          (∑ y : Ω n, biasW θ y * (if (y j) = cNegOne then (1 : ℝ) else 0))) +
        ((∑ ξ : Ω n, biasW θ ξ * (if (ξ j) = cNegOne then (1 : ℝ) else 0)) *
          (∑ y : Ω n, biasW θ y * (if (y j) = cOne then (1 : ℝ) else 0))) := by
          congr 1
          · exact double_sum_factor θ (fun ξ : Ω n => (if (ξ j) = cOne then (1 : ℝ) else 0))
              (fun y : Ω n => (if (y j) = cNegOne then (1 : ℝ) else 0))
          · exact double_sum_factor θ (fun ξ : Ω n => (if (ξ j) = cNegOne then (1 : ℝ) else 0))
              (fun y : Ω n => (if (y j) = cOne then (1 : ℝ) else 0))
    _ = (1 - (Real.cos θ)^2) / 2 := by
          rw [biasW_sum_indicator θ j cOne]
          rw [biasW_sum_indicator θ j cNegOne]
          simp [cOne, cNegOne]
          ring


/-- coordinatewise swap of the pair `(ξ,y)` according to signs `ε` -/
def swapPair {n : ℕ} (ε : Ω n) : (Ω n × Ω n) ≃ (Ω n × Ω n) where
  toFun p := (fun j => if (ε j) = cNegOne then (p.2 j) else (p.1 j),
              fun j => if (ε j) = cNegOne then (p.1 j) else (p.2 j))
  invFun p := (fun j => if (ε j) = cNegOne then (p.2 j) else (p.1 j),
              fun j => if (ε j) = cNegOne then (p.1 j) else (p.2 j))
  left_inv := by
    intro p
    ext j <;> by_cases h : (ε j) = cNegOne <;> simp [h]
  right_inv := by
    intro p
    ext j <;> by_cases h : (ε j) = cNegOne <;> simp [h]

lemma sign_diff_eq_diff_swap {n : ℕ} (ε ξ y : Ω n) (j : Fin n) :
    (((ε j : C) : ℝ) * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) =
      (((swapPair ε (ξ, y)).1 j : C) : ℝ) - (((swapPair ε (ξ, y)).2 j : C) : ℝ) := by
  by_cases h : (ε j) = cNegOne
  · have hε : ((ε j : C) : ℝ) = -1 := by
      rw [h]; simp [cNegOne]
    simp [swapPair, h, hε]
  · have hε : ((ε j : C) : ℝ) = 1 := by
      rcases mem_two (ε j) with hε1 | hε1
      · simp [hε1, cOne]
      · exact False.elim (h hε1)
    simp [swapPair, h]
    rw [hε]
    ring


/-- The biased weight of a pair is invariant under the coordinatewise swap. -/
lemma biasW_pair_swap {n : ℕ} (θ : ℝ) (ε ξ y : Ω n) :
    biasW θ ((swapPair ε (ξ, y)).1) * biasW θ ((swapPair ε (ξ, y)).2) = biasW θ ξ * biasW θ y := by
  let f : C → ℝ := fun z => (1 + Real.cos θ * ((z : C) : ℝ)) / 2
  unfold biasW
  calc
    (∏ j : Fin n, f ((swapPair ε (ξ, y)).1 j)) * (∏ j : Fin n, f ((swapPair ε (ξ, y)).2 j))
        = ∏ j : Fin n, f ((swapPair ε (ξ, y)).1 j) * f ((swapPair ε (ξ, y)).2 j) := by
            rw [← Finset.prod_mul_distrib]
    _ = ∏ j : Fin n, f (ξ j) * f (y j) := by
            apply Finset.prod_congr rfl
            intro j hj
            by_cases h : (ε j) = cNegOne
            · have h1 : ((swapPair ε (ξ, y)).1 j) = y j := by simp [swapPair, h]
              have h2 : ((swapPair ε (ξ, y)).2 j) = ξ j := by simp [swapPair, h]
              rw [h1, h2]
              ring
            · have h1 : ((swapPair ε (ξ, y)).1 j) = ξ j := by simp [swapPair, h]
              have h2 : ((swapPair ε (ξ, y)).2 j) = y j := by simp [swapPair, h]
              rw [h1, h2]
    _ = (∏ j : Fin n, f (ξ j)) * (∏ j : Fin n, f (y j)) := by
            rw [Finset.prod_mul_distrib]


/-- A double sum with a fixed sign pattern inserted equals the plain double sum. -/
lemma signed_double_eq_double {n : ℕ} (θ : ℝ) (ε : Ω n) (v : Fin n → X) {pow : ℝ} :
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
        ‖∑ j : Fin n, (((ε j : C) : ℝ) * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) • v j‖ ^ pow)
      = (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
        ‖∑ j : Fin n, (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) • v j‖ ^ pow) := by
  let φ : Ω n × Ω n → ℝ := fun p => biasW θ (p.1) * biasW θ (p.2) *
      ‖∑ j : Fin n, (((ε j : C) : ℝ) * (((p.1 j : C) : ℝ) - ((p.2 j : C) : ℝ))) • v j‖ ^ pow
  let ψ : Ω n × Ω n → ℝ := fun p => biasW θ (p.1) * biasW θ (p.2) *
      ‖∑ j : Fin n, (((p.1 j : C) : ℝ) - ((p.2 j : C) : ℝ)) • v j‖ ^ pow
  have hpoint : ∀ p : Ω n × Ω n, φ (swapPair ε p) = ψ p := by
    intro p
    rcases p with ⟨ξ, y⟩
    have hw : biasW θ ((swapPair ε (ξ, y)).1) * biasW θ ((swapPair ε (ξ, y)).2) = biasW θ ξ * biasW θ y :=
      biasW_pair_swap θ ε ξ y
    have hv : (∑ j : Fin n, (((ε j : C) : ℝ) * ((((swapPair ε (ξ, y)).1 j : C) : ℝ) - (((swapPair ε (ξ, y)).2 j : C) : ℝ))) • v j)
        = ∑ j : Fin n, (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) • v j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hscalar : (((ε j : C) : ℝ) * ((((swapPair ε (ξ, y)).1 j : C) : ℝ) - (((swapPair ε (ξ, y)).2 j : C) : ℝ)))
          = (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) := by
        have hsc := sign_diff_eq_diff_swap ε ξ y j
        have hsq : ((ε j : C) : ℝ) * ((ε j : C) : ℝ) = 1 := by
          rcases mem_two (ε j) with h | h <;> simp [h, cOne, cNegOne]
        calc
          ((ε j : C) : ℝ) * ((((swapPair ε (ξ, y)).1 j : C) : ℝ) - (((swapPair ε (ξ, y)).2 j : C) : ℝ))
              = ((ε j : C) : ℝ) * (((ε j : C) : ℝ) * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) := by
                  rw [← hsc]
              _ = (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) := by
                  rw [← mul_assoc, hsq, one_mul]
      rw [hscalar]
    unfold φ ψ
    rw [hw]
    congr 1
    rw [hv]
  calc
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
        ‖∑ j : Fin n, (((ε j : C) : ℝ) * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) • v j‖ ^ pow)
        = ∑ p : Ω n × Ω n, φ p := by
            rw [← Fintype.sum_prod_type (f := fun p : Ω n × Ω n => φ p)]
    _ = ∑ p : Ω n × Ω n, φ (swapPair ε p) := by
            exact (Equiv.sum_comp (swapPair ε) φ).symm
    _ = ∑ p : Ω n × Ω n, ψ p := by
            apply Finset.sum_congr rfl
            intro p hp
            exact hpoint p
    _ = (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
        ‖∑ j : Fin n, (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) • v j‖ ^ pow) := by
            rw [Fintype.sum_prod_type (f := fun p : Ω n × Ω n => ψ p)]




/-- `a` factors out of a double weighted sum. -/
lemma double_sum_const_mul {n : ℕ} (θ : ℝ) (a : ℝ) (h : Ω n → Ω n → ℝ) :
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * (a * h ξ y))
      = a * (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * h ξ y) := by
  calc
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * (a * h ξ y))
        = ∑ ξ : Ω n, (biasW θ ξ * a) * (∑ y : Ω n, biasW θ y * h ξ y) := by
            apply Finset.sum_congr rfl
            intro ξ hξ
            calc
              (∑ y : Ω n, biasW θ ξ * biasW θ y * (a * h ξ y))
                  = ∑ y : Ω n, (biasW θ ξ * a) * (biasW θ y * h ξ y) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      ring
              _ = (biasW θ ξ * a) * (∑ y : Ω n, biasW θ y * h ξ y) := by
                      exact (Finset.mul_sum (s := Finset.univ)
                        (f := fun y : Ω n => biasW θ y * h ξ y) (a := biasW θ ξ * a)).symm
    _ = a * (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * h ξ y) := by
          calc
            (∑ ξ : Ω n, (biasW θ ξ * a) * (∑ y : Ω n, biasW θ y * h ξ y))
                = ∑ ξ : Ω n, a * (biasW θ ξ * (∑ y : Ω n, biasW θ y * h ξ y)) := by
                    apply Finset.sum_congr rfl
                    intro ξ hξ
                    ring
            _ = a * (∑ ξ : Ω n, biasW θ ξ * (∑ y : Ω n, biasW θ y * h ξ y)) := by
                    exact (Finset.mul_sum (s := Finset.univ)
                      (f := fun ξ : Ω n => biasW θ ξ * (∑ y : Ω n, biasW θ y * h ξ y)) (a := a)).symm
            _ = a * (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * h ξ y) := by
                    congr 1
                    apply Finset.sum_congr rfl
                    intro ξ hξ
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro y hy
                    ring


/-- `E |ξ_j − y_j|^pow ≤ 2^(pow/2) · sin^pow θ` for independent biased copies. -/
lemma moment_coord_le {n : ℕ} (θ : ℝ) (j : Fin n) {pow : ℝ} (hp1 : 1 ≤ pow) (hp2 : pow ≤ 2)
    (hs0 : 0 < Real.sin θ) (hs1 : Real.sin θ ≤ 1) :
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
        |(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow)
      ≤ (2 : ℝ) ^ (pow / 2) * (Real.sin θ) ^ pow := by
  have hp0 : 0 < pow := by linarith
  have hpt : ∀ ξ y : Ω n,
      |(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow
        = (2 : ℝ) ^ pow * (if (ξ j) ≠ (y j) then (1 : ℝ) else 0) := by
    intro ξ y
    by_cases h : (ξ j) = (y j)
    · have hd : (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) = 0 := by rw [h]; ring
      rw [hd]
      rw [if_neg (by intro hne; exact hne h)]
      simp
      rw [Real.zero_rpow (ne_of_gt hp0)]
    · rw [if_pos h]
      rcases mem_two (ξ j) with hx | hx
      · rcases mem_two (y j) with hy | hy
        · exfalso
          exact h (by rw [hx, hy])
        · have hd : (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) = 2 := by
            rw [hx, hy]
            norm_num [cOne, cNegOne]
          rw [hd]
          simp
      · rcases mem_two (y j) with hy | hy
        · have hd : (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) = -2 := by
            rw [hx, hy]
            norm_num [cOne, cNegOne]
          rw [hd]
          simp
        · exfalso
          exact h (by rw [hx, hy])
  have hsin2 : (1 : ℝ) - (Real.cos θ)^2 = (Real.sin θ)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsqpow : (Real.sin θ) ^ 2 ≤ (Real.sin θ) ^ pow := by
    have hA : (Real.sin θ) ^ (2 : ℝ) ≤ (Real.sin θ) ^ pow := by
      have h2p : 0 ≤ 2 - pow := by linarith
      have hsmall : (Real.sin θ) ^ (2 - pow) ≤ 1 := Real.rpow_le_one (le_of_lt hs0) hs1 h2p
      have hpos : 0 < (Real.sin θ) ^ pow := Real.rpow_pos_of_pos hs0 pow
      calc
        (Real.sin θ) ^ (2 : ℝ) = (Real.sin θ) ^ (pow + (2 - pow)) := by
              exact congrArg (fun e : ℝ => (Real.sin θ) ^ e) (by ring : (2 : ℝ) = pow + (2 - pow))
        _ = (Real.sin θ) ^ pow * (Real.sin θ) ^ (2 - pow) := Real.rpow_add hs0 pow (2 - pow)
        _ ≤ (Real.sin θ) ^ pow * 1 := mul_le_mul_of_nonneg_left hsmall (le_of_lt hpos)
        _ = (Real.sin θ) ^ pow := by ring
    rw [← Real.rpow_natCast (Real.sin θ) 2]
    exact hA
  have hpowdiv : (2 : ℝ) ^ pow / 2 ≤ (2 : ℝ) ^ (pow / 2) := by
    have hle : pow ≤ 1 + pow / 2 := by nlinarith
    calc
      (2 : ℝ) ^ pow / 2 ≤ (2 : ℝ) ^ (1 + pow / 2) / 2 := by
            exact div_le_div_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) hle)
              (by norm_num : (0 : ℝ) ≤ 2)
      _ = (2 : ℝ) ^ (pow / 2) := by
            rw [Real.rpow_add (by norm_num : 0 < (2 : ℝ)) 1 (pow / 2)]
            simp
  calc
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
        |(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow)
        = ∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
            ((2 : ℝ) ^ pow * (if (ξ j) ≠ (y j) then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro ξ hξ
            apply Finset.sum_congr rfl
            intro y hy
            rw [hpt ξ y]
    _ = (2 : ℝ) ^ pow * (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
            (if (ξ j) ≠ (y j) then (1 : ℝ) else 0)) := by
            exact double_sum_const_mul θ ((2 : ℝ) ^ pow)
              (fun ξ y : Ω n => if (ξ j) ≠ (y j) then (1 : ℝ) else 0)
    _ = (2 : ℝ) ^ pow * ((1 - (Real.cos θ)^2) / 2) := by
            rw [prob_diff_coord θ j]
    _ = (2 : ℝ) ^ pow * ((Real.sin θ)^2 / 2) := by
            rw [hsin2]
    _ ≤ (2 : ℝ) ^ (pow / 2) * (Real.sin θ) ^ pow := by
          calc
            (2 : ℝ) ^ pow * ((Real.sin θ)^2 / 2)
                ≤ (2 : ℝ) ^ pow * ((Real.sin θ)^pow / 2) := by
                    exact mul_le_mul_of_nonneg_left
                      (div_le_div_of_nonneg_right hsqpow (by norm_num : (0 : ℝ) ≤ 2))
                      (by positivity : 0 ≤ (2 : ℝ) ^ pow)
            _ = (2 : ℝ) ^ pow / 2 * (Real.sin θ) ^ pow := by ring
            _ ≤ (2 : ℝ) ^ (pow / 2) * (Real.sin θ) ^ pow := by
                    exact mul_le_mul_of_nonneg_right hpowdiv (Real.rpow_nonneg (le_of_lt hs0) pow)

/-- `|a/s|^pow = |a|^pow / s^pow` for `s > 0`. -/
lemma abs_div_rpow {a s : ℝ} (hs : 0 < s) {pow : ℝ} :
    |a / s| ^ pow = |a| ^ pow / s ^ pow := by
  calc
    |a / s| ^ pow = (|a| / s) ^ pow := by
          congr 1
          rw [abs_div]
          rw [abs_of_pos hs]
    _ = |a| ^ pow / s ^ pow := Real.div_rpow (abs_nonneg a) (le_of_lt hs) pow



/-- scaled moment: `E|(ξ_j − y_j)/sinθ|^pow ≤ 2^(pow/2)`. -/
lemma moment_scaled_le {n : ℕ} (θ : ℝ) (j : Fin n) {pow : ℝ} (hp1 : 1 ≤ pow) (hp2 : pow ≤ 2)
    (hs0 : 0 < Real.sin θ) (hs1 : Real.sin θ ≤ 1) :
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
        |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow) ≤ (2 : ℝ) ^ (pow / 2) := by
  have hm := moment_coord_le θ j hp1 hp2 hs0 hs1
  have hsum : (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
        |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow)
      = (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
          |(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow) / (Real.sin θ) ^ pow := by
    calc
      (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
          |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow)
          = ∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
              (|(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow / (Real.sin θ) ^ pow) := by
              apply Finset.sum_congr rfl
              intro ξ hξ
              apply Finset.sum_congr rfl
              intro y hy
              rw [abs_div_rpow hs0]
      _ = ∑ ξ : Ω n, (∑ y : Ω n, biasW θ ξ * biasW θ y *
              |(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow) / (Real.sin θ) ^ pow := by
              apply Finset.sum_congr rfl
              intro ξ hξ
              calc
                (∑ y : Ω n, biasW θ ξ * biasW θ y *
                    (|(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow / (Real.sin θ) ^ pow))
                    = ∑ y : Ω n, (biasW θ ξ * biasW θ y *
                        |(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow) / (Real.sin θ) ^ pow := by
                        apply Finset.sum_congr rfl
                        intro y hy
                        ring
                _ = (∑ y : Ω n, biasW θ ξ * biasW θ y *
                        |(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow) / (Real.sin θ) ^ pow := by
                        exact (Finset.sum_div (s := Finset.univ)
                          (f := fun y : Ω n => biasW θ ξ * biasW θ y *
                            |(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow)
                          (a := (Real.sin θ) ^ pow)).symm
      _ = (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
              |(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow) / (Real.sin θ) ^ pow := by
              exact (Finset.sum_div (s := Finset.univ)
                (f := fun ξ : Ω n => ∑ y : Ω n, biasW θ ξ * biasW θ y *
                  |(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow)
                (a := (Real.sin θ) ^ pow)).symm
  have hspos : 0 < (Real.sin θ) ^ pow := Real.rpow_pos_of_pos hs0 pow
  rw [hsum]
  calc
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
        |(((ξ j : C) : ℝ) - ((y j : C) : ℝ))| ^ pow) / (Real.sin θ) ^ pow
        ≤ ((2 : ℝ) ^ (pow / 2) * (Real.sin θ) ^ pow) / (Real.sin θ) ^ pow := by
            exact div_le_div_of_nonneg_right hm (Real.rpow_nonneg (le_of_lt hs0) pow)
    _ = (2 : ℝ) ^ (pow / 2) := by
            field_simp [ne_of_gt hspos]

/-- `Σ_j (a_j/s)•u_j = Σ_j a_j•((1/s)•u_j)`. -/
lemma sum_smul_div {n : ℕ} (s : ℝ) (a : Fin n → ℝ) (u : Fin n → X) :
    (∑ j : Fin n, (a j / s) • u j) = ∑ j : Fin n, (a j) • ((1 / s) • u j) := by
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (a j / s) • u j = ((a j) * (1 / s)) • u j := by congr 1; ring
    _ = (a j) • ((1 / s) • u j) := by rw [← smul_smul]

/-- `Σ_ε (1/2)^n = 1` (uniform weights on the cube). -/
lemma sum_uniw_eq_one {n : ℕ} : (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n)) = 1 := by
  have hcard : Fintype.card (Ω n) = 2 ^ n := by
    unfold Ω
    rw [Fintype.card_fun]
    have hC : Fintype.card C = 2 := by
      rw [← Finset.card_univ]
      rw [univ_C_eq]
      simp [cOne_ne_cNegOne]
    simp [hC]
  calc
    (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n)) = (Fintype.card (Ω n)) • ((1 / 2 : ℝ) ^ n) := by
          rw [Finset.sum_const, Finset.card_univ]
    _ = ((2 : ℝ) ^ n) * ((1 / 2 : ℝ) ^ n) := by
          rw [nsmul_eq_mul, hcard]
          simp [Nat.cast_pow]
    _ = 1 := by
          rw [← mul_pow]
          norm_num


/-- Pull a real constant out of a double weighted sum on the right. -/
lemma double_sum_mul_right {n : ℕ} (θ : ℝ) (a : ℝ) (b : Ω n → Ω n → ℝ) :
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * (b ξ y * a))
      = a * (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * b ξ y) := by
  calc
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * (b ξ y * a))
        = ∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * (a * b ξ y) := by
            apply Finset.sum_congr rfl; intro ξ hξ
            apply Finset.sum_congr rfl; intro y hy; ring
    _ = a * (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * b ξ y) := by
            exact double_sum_const_mul θ a b

/-- Swap the `j`-sum with the double `(ξ,y)`-sum. -/
lemma sum_j_double_swap {n : ℕ} (θ : ℝ) (f : Fin n → Ω n → Ω n → ℝ) :
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * (∑ j : Fin n, f j ξ y))
      = ∑ j : Fin n, (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * f j ξ y) := by
  calc
    (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * (∑ j : Fin n, f j ξ y))
        = ∑ ξ : Ω n, ∑ y : Ω n, ∑ j : Fin n, biasW θ ξ * biasW θ y * f j ξ y := by
            apply Finset.sum_congr rfl; intro ξ hξ
            apply Finset.sum_congr rfl; intro y hy
            exact Finset.mul_sum (s := Finset.univ)
              (f := fun j : Fin n => f j ξ y) (a := (biasW θ ξ * biasW θ y))
    _ = ∑ ξ : Ω n, ∑ j : Fin n, ∑ y : Ω n, biasW θ ξ * biasW θ y * f j ξ y := by
            apply Finset.sum_congr rfl; intro ξ hξ
            exact Finset.sum_comm
    _ = ∑ j : Fin n, ∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * f j ξ y := by
            exact Finset.sum_comm


lemma biased_type_le {n : ℕ} (hn : 1 ≤ n) (θ : ℝ) (hs0 : 0 < Real.sin θ) (hs1 : Real.sin θ ≤ 1)
    (u : Fin n → X) {pow : ℝ} (hp1 : 1 ≤ pow) (hp2 : pow ≤ 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hRad : ∀ (m : ℕ), 1 ≤ m → ∀ x : Fin m → X,
      (∑ ε : Ω m, ((1 / 2 : ℝ) ^ m) * ‖∑ j : Fin m, (((ε j : C) : ℝ) • x j)‖ ^ pow)
        ≤ c ^ pow * (∑ j : Fin m, ‖x j‖ ^ pow)) :
    (∑ ξ : Ω n, biasW θ ξ * ‖∑ j : Fin n, (delta θ ξ j) • u j‖ ^ pow)
      ≤ (2 : ℝ) ^ (pow / 2) * c ^ pow * (∑ j : Fin n, ‖u j‖ ^ pow) := by
  have hsin : Real.sin θ ≠ 0 := ne_of_gt hs0
  have hA : (∑ ξ : Ω n, biasW θ ξ * ‖∑ j : Fin n, (delta θ ξ j) • u j‖ ^ pow)
      ≤ ∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
          ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow := by
    apply Finset.sum_le_sum
    intro ξ hξ
    have h1 := deltaJ θ hsin u ξ (p := pow) hp1
    calc
      biasW θ ξ * ‖∑ j : Fin n, (delta θ ξ j) • u j‖ ^ pow
          ≤ biasW θ ξ * (∑ y : Ω n, biasW θ y * ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow) := by
              exact mul_le_mul_of_nonneg_left h1 (biasW_nonneg θ ξ)
      _ = ∑ y : Ω n, biasW θ ξ * (biasW θ y * ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow) := by
              exact Finset.mul_sum (s := Finset.univ)
                (f := fun y : Ω n => biasW θ y * ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)
                (a := biasW θ ξ)
      _ = ∑ y : Ω n, (biasW θ ξ * biasW θ y) * ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
  -- hSigned
  have hSigned : ∀ ε : Ω n,
      (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow)
        = ∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow := by
    intro ε
    let v : Fin n → X := fun j => (1 / Real.sin θ) • u j
    have hSD := signed_double_eq_double θ ε v (pow := pow)
    have hs : ∀ ξ y : Ω n,
        (∑ j : Fin n, (((ε j : C) : ℝ) * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) • v j) = ∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j := by
      intro ξ y
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (((ε j : C) : ℝ) * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) • v j = (((ε j : C) : ℝ) * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) • ((1 / Real.sin θ) • u j) := by rfl
        _ = ((((ε j : C) : ℝ) * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) * (1 / Real.sin θ)) • u j := by
              rw [smul_smul]
        _ = ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j := by
              congr 1
              ring
    have hp : ∀ ξ y : Ω n,
        (∑ j : Fin n, (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) • v j) = ∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j := by
      intro ξ y
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) • v j = (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) • ((1 / Real.sin θ) • u j) := by rfl
        _ = ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) * (1 / Real.sin θ)) • u j := by
              rw [smul_smul]
        _ = ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j := by
              congr 1
              ring
    calc
      (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow)
          = ∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * ‖∑ j : Fin n, (((ε j : C) : ℝ) * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) • v j‖ ^ pow := by
              apply Finset.sum_congr rfl
              intro ξ hξ
              apply Finset.sum_congr rfl
              intro y hy
              rw [← hs ξ y]
      _ = ∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * ‖∑ j : Fin n, (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) • v j‖ ^ pow := hSD
      _ = ∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y * ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow := by
              apply Finset.sum_congr rfl
              intro ξ hξ
              apply Finset.sum_congr rfl
              intro y hy
              rw [hp ξ y]
  have htype : ∀ ξ y : Ω n,
      (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) *
          ‖∑ j : Fin n, (((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j))‖ ^ pow)
        ≤ c ^ pow * (∑ j : Fin n, ‖((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow) := by
    intro ξ y
    exact hRad n hn (fun j : Fin n => ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)
  have hMom : ∀ j : Fin n,
      (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
          |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow) ≤ (2 : ℝ) ^ (pow / 2) := by
    intro j
    exact moment_scaled_le θ j hp1 hp2 hs0 hs1
  -- norm identity
  have hnorm : ∀ (ξ y : Ω n) (j : Fin n),
      ‖((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow
        = |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow * ‖u j‖ ^ pow := by
    intro ξ y j
    calc
      ‖((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow
          = (|(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| * ‖u j‖) ^ pow := by
              congr 1
              rw [norm_smul, Real.norm_eq_abs]
      _ = |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow * ‖u j‖ ^ pow := by
              exact Real.mul_rpow (abs_nonneg _) (norm_nonneg _)
  -- Let D = the plain double sum (RHS of hA and of hSigned)
  -- hAv: D = averaged signed sums
  have hAv : (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
          ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)
      = ∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) *
          (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
            ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow) := by
    calc
      (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
          ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)
          = ∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) *
              (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
                ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow) := by
              -- D = (Σ_ε 2^{-n})·D = Σ_ε 2^{-n}·D
              calc
                (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
                    ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)
                    = (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n)) *
                        (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
                          ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow) := by
                        rw [sum_uniw_eq_one]
                        ring
                _ = ∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) *
                        (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
                          ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow) := by
                        -- distribute: (Σ_ε w)·D = Σ_ε w·D via Finset.sum_mul backward
                        rw [Finset.sum_mul]
      _ = ∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) *
              (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
                ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow) := by
              apply Finset.sum_congr rfl
              intro ε hε
              congr 1
              exact (hSigned ε).symm

  -- identity: signed-in-(κ/s) form equals ((εj):ℝ)•x form with x_j = (κ/s)•u_j
  have hsx : ∀ ε ξ y : Ω n,
      (∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j)
        = ∑ j : Fin n, ((((ε j : C) : ℝ) • ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)) := by
    intro ε ξ y
    apply Finset.sum_congr rfl
    intro j hj
    rw [← smul_smul]
  -- swap the ε-sum outside with the (ξ,y)-double sum, apply the type bound pointwise, collect moments
  have hBD : (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) *
          (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
            ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow))
      ≤ c ^ pow * (∑ j : Fin n, (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
            |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow) * ‖u j‖ ^ pow) := by
    calc
      (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) *
          (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
            ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow))
          = ∑ ε : Ω n, ∑ ξ : Ω n, ∑ y : Ω n, ((1 / 2 : ℝ) ^ n) *
              (biasW θ ξ * biasW θ y *
                ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow) := by
              apply Finset.sum_congr rfl
              intro ε hε
              calc
                ((1 / 2 : ℝ) ^ n) * (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
                    ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow)
                    = ∑ ξ : Ω n, ((1 / 2 : ℝ) ^ n) * (∑ y : Ω n, biasW θ ξ * biasW θ y *
                        ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow) := by
                        exact (Finset.mul_sum (s := Finset.univ)
                          (f := fun ξ : Ω n => ∑ y : Ω n, biasW θ ξ * biasW θ y *
                            ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow)
                          (a := ((1 / 2 : ℝ) ^ n)))
                _ = ∑ ξ : Ω n, ∑ y : Ω n, ((1 / 2 : ℝ) ^ n) * (biasW θ ξ * biasW θ y *
                        ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow) := by
                        apply Finset.sum_congr rfl
                        intro ξ hξ
                        exact (Finset.mul_sum (s := Finset.univ)
                          (f := fun y : Ω n => biasW θ ξ * biasW θ y *
                            ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow)
                          (a := ((1 / 2 : ℝ) ^ n)))
    _ ≤ c ^ pow * (∑ j : Fin n, (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
            |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow) * ‖u j‖ ^ pow) := by
          have hSW : (∑ ε : Ω n, ∑ ξ : Ω n, ∑ y : Ω n, ((1 / 2 : ℝ) ^ n) *
                (biasW θ ξ * biasW θ y * ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow))
              = ∑ ξ : Ω n, ∑ y : Ω n, (biasW θ ξ * biasW θ y) *
                  (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) * ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow) := by
              calc
                (∑ ε : Ω n, ∑ ξ : Ω n, ∑ y : Ω n, ((1 / 2 : ℝ) ^ n) *
                    (biasW θ ξ * biasW θ y * ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow))
                    = ∑ ε : Ω n, ∑ p : Ω n × Ω n, ((1 / 2 : ℝ) ^ n) *
                        (biasW θ (p.1) * biasW θ (p.2) * ‖∑ j : Fin n,
                          ((ε j : C) : ℝ) • (((((p.1 j : C) : ℝ) - ((p.2 j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow) := by
                        apply Finset.sum_congr rfl
                        intro ε hε
                        rw [← Fintype.sum_prod_type (f := fun p : Ω n × Ω n =>
                          ((1 / 2 : ℝ) ^ n) * (biasW θ (p.1) * biasW θ (p.2) *
                            ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((p.1 j : C) : ℝ) - ((p.2 j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow))]
                    _ = ∑ p : Ω n × Ω n, ∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) *
                        (biasW θ (p.1) * biasW θ (p.2) * ‖∑ j : Fin n,
                          ((ε j : C) : ℝ) • (((((p.1 j : C) : ℝ) - ((p.2 j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow) := by
                        exact Finset.sum_comm
                    _ = ∑ ξ : Ω n, ∑ y : Ω n, (biasW θ ξ * biasW θ y) *
                        (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) * ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow) := by
                        rw [Fintype.sum_prod_type]
                        apply Finset.sum_congr rfl
                        intro ξ hξ
                        apply Finset.sum_congr rfl
                        intro y hy
                        calc
                          (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) *
                              (biasW θ ξ * biasW θ y * ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow))
                              = ∑ ε : Ω n, (biasW θ ξ * biasW θ y) *
                                  (((1 / 2 : ℝ) ^ n) * ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow) := by
                                  apply Finset.sum_congr rfl
                                  intro ε hε
                                  ring
                          _ = (biasW θ ξ * biasW θ y) *
                              (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) * ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow) := by
                              exact (Finset.mul_sum (s := Finset.univ)
                                (f := fun ε : Ω n => ((1 / 2 : ℝ) ^ n) * ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow)
                                (a := (biasW θ ξ * biasW θ y))).symm
          calc
            (∑ ε : Ω n, ∑ ξ : Ω n, ∑ y : Ω n, ((1 / 2 : ℝ) ^ n) *
                (biasW θ ξ * biasW θ y * ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow))
                = ∑ ε : Ω n, ∑ ξ : Ω n, ∑ y : Ω n, ((1 / 2 : ℝ) ^ n) *
                    (biasW θ ξ * biasW θ y * ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow) := by
                    apply Finset.sum_congr rfl
                    intro ε hε
                    apply Finset.sum_congr rfl
                    intro ξ hξ
                    apply Finset.sum_congr rfl
                    intro y hy
                    congr 1
                    rw [hsx ε ξ y]
            _ ≤ ∑ ξ : Ω n, ∑ y : Ω n, (biasW θ ξ * biasW θ y) *
                    (c ^ pow * (∑ j : Fin n, ‖((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)) := by
                    calc
                      (∑ ε : Ω n, ∑ ξ : Ω n, ∑ y : Ω n, ((1 / 2 : ℝ) ^ n) *
                          (biasW θ ξ * biasW θ y * ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow))
                          = ∑ ξ : Ω n, ∑ y : Ω n, (biasW θ ξ * biasW θ y) *
                              (∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) * ‖∑ j : Fin n, ((ε j : C) : ℝ) • (((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j)‖ ^ pow) := hSW
                      _ ≤ ∑ ξ : Ω n, ∑ y : Ω n, (biasW θ ξ * biasW θ y) *
                              (c ^ pow * (∑ j : Fin n, ‖((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)) := by
                              apply Finset.sum_le_sum
                              intro ξ hξ
                              apply Finset.sum_le_sum
                              intro y hy
                              exact mul_le_mul_of_nonneg_left (htype ξ y)
                                (mul_nonneg (biasW_nonneg θ ξ) (biasW_nonneg θ y))
            _ = c ^ pow * (∑ j : Fin n, (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
                    |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow) * ‖u j‖ ^ pow) := by
                    calc
                      (∑ ξ : Ω n, ∑ y : Ω n, (biasW θ ξ * biasW θ y) *
                          (c ^ pow * (∑ j : Fin n, ‖((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)))
                          = c ^ pow * (∑ ξ : Ω n, ∑ y : Ω n, (biasW θ ξ * biasW θ y) *
                              (∑ j : Fin n, ‖((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)) := by
                              exact double_sum_const_mul θ (c ^ pow)
                                (fun ξ y : Ω n => ∑ j : Fin n, ‖((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)
                      _ = c ^ pow * (∑ j : Fin n, (∑ ξ : Ω n, ∑ y : Ω n, (biasW θ ξ * biasW θ y) *
                              ‖((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)) := by
                              congr 1
                              exact sum_j_double_swap θ
                                (fun (j : Fin n) (ξ y : Ω n) => ‖((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)
                      _ = c ^ pow * (∑ j : Fin n, (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
                              |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow) * ‖u j‖ ^ pow) := by
                              congr 1
                              apply Finset.sum_congr rfl
                              intro j hj
                              calc
                                (∑ ξ : Ω n, ∑ y : Ω n, (biasW θ ξ * biasW θ y) * ‖((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow)
                                    = ∑ ξ : Ω n, ∑ y : Ω n, (biasW θ ξ * biasW θ y) *
                                        (|(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow * ‖u j‖ ^ pow) := by
                                        apply Finset.sum_congr rfl
                                        intro ξ hξ
                                        apply Finset.sum_congr rfl
                                        intro y hy
                                        rw [hnorm ξ y j]
                                _ = (∑ ξ : Ω n, ∑ y : Ω n, (biasW θ ξ * biasW θ y) * |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow) * ‖u j‖ ^ pow := by
                                        rw [mul_comm]
                                        exact double_sum_mul_right θ (‖u j‖ ^ pow)
                                          (fun ξ y : Ω n => |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow)
  -- final
  -- final
  calc
    (∑ ξ : Ω n, biasW θ ξ * ‖∑ j : Fin n, (delta θ ξ j) • u j‖ ^ pow)
        ≤ ∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
          ‖∑ j : Fin n, ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ) • u j‖ ^ pow := hA
    _ = ∑ ε : Ω n, ((1 / 2 : ℝ) ^ n) *
          (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
            ‖∑ j : Fin n, ((((ε j : C) : ℝ) * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ))) • u j‖ ^ pow) := hAv
    _ ≤ c ^ pow * (∑ j : Fin n, (∑ ξ : Ω n, ∑ y : Ω n, biasW θ ξ * biasW θ y *
            |(((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ| ^ pow) * ‖u j‖ ^ pow) := hBD
    _ ≤ c ^ pow * (∑ j : Fin n, (2 : ℝ) ^ (pow / 2) * ‖u j‖ ^ pow) := by
          -- use hMom and 0 ≤ ‖u j‖^pow and c^pow ≥ 0
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_right (hMom j) (Real.rpow_nonneg (norm_nonneg (u j)) pow)
          · exact Real.rpow_nonneg hc0 pow
    _ = (2 : ℝ) ^ (pow / 2) * c ^ pow * (∑ j : Fin n, ‖u j‖ ^ pow) := by
          have hfac : (∑ j : Fin n, (2 : ℝ) ^ (pow / 2) * ‖u j‖ ^ pow)
              = (2 : ℝ) ^ (pow / 2) * (∑ j : Fin n, ‖u j‖ ^ pow) := by
            exact (Finset.mul_sum (s := Finset.univ)
              (f := fun j : Fin n => ‖u j‖ ^ pow) (a := (2 : ℝ) ^ (pow / 2))).symm
          rw [hfac]
          ring

end RadType
end
