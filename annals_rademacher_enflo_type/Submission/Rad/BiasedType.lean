import Submission.Rad.Main
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal BigOperators Interval
noncomputable section
namespace RadType
open RademacherEnfloType

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

lemma biased_mass_coord {n : ℕ} (θ : ℝ) (j : Fin n) (z : C) :
    (biasedMeasure (n := n) θ) {ξ : Ω n | ξ j = z} = (biasedCoord θ) {z} := by
  classical
  rw [biasedMeasure]
  rw [MeasureTheory.Measure.infinitePi_eq_pi (μ := fun _ : Fin n => biasedCoord θ)]
  have hset : {ξ : Ω n | ξ j = z} = Set.univ.pi (fun k : Fin n => if k = j then ({z} : Set C) else Set.univ) := by
    ext ξ
    simp [Set.pi]
  rw [hset]
  rw [MeasureTheory.Measure.pi_pi (μ := fun _ : Fin n => biasedCoord θ)
    (s := fun k : Fin n => if k = j then ({z} : Set C) else Set.univ)]
  have h0 : ∀ b : Fin n, b ∈ Finset.univ → b ≠ j →
      (if b = j then (biasedCoord θ) ({z} : Set C) else (biasedCoord θ) Set.univ) = 1 := by
    intro b hb hbj
    simp [hbj]
  have h1 : j ∉ (Finset.univ : Finset (Fin n)) →
      (if j = j then (biasedCoord θ) ({z} : Set C) else (biasedCoord θ) Set.univ) = 1 := by
    intro hj
    exact False.elim (hj (Finset.mem_univ j))
  calc
    (∏ i : Fin n, (biasedCoord θ) (if i = j then ({z} : Set C) else Set.univ))
        = ∏ i : Fin n, (if i = j then (biasedCoord θ) ({z} : Set C) else (biasedCoord θ) Set.univ) := by
            apply Finset.prod_congr rfl
            intro i hi
            by_cases hij : i = j <;> simp [hij]
    _ = (biasedCoord θ) ({z} : Set C) := by
            rw [Finset.prod_eq_single (s := Finset.univ)
              (f := fun i : Fin n => if i = j then (biasedCoord θ) ({z} : Set C) else (biasedCoord θ) Set.univ)
              j h0 h1]
            simp

lemma measurable_coord_set {n : ℕ} (j : Fin n) (z : C) : MeasurableSet {ξ : Ω n | ξ j = z} := by
  change MeasurableSet ((fun ξ : Ω n => ξ j) ⁻¹' ({z} : Set C))
  exact measurableSet_singleton z |>.preimage (measurable_pi_apply j)

lemma biasW_sum_indicator {n : ℕ} (θ : ℝ) (j : Fin n) (z : C) :
    (∑ ξ : Ω n, biasW θ ξ * (if ξ j = z then (1 : ℝ) else 0)) = (1 + Real.cos θ * ((z : C) : ℝ)) / 2 := by
  have hs : MeasurableSet {ξ : Ω n | ξ j = z} := measurable_coord_set j z
  have hstep2 : (∫ ξ : Ω n, (if ξ j = z then (1 : ℝ) else 0) ∂(biasedMeasure (n := n) θ))
      = (biasedMeasure (n := n) θ).real {ξ : Ω n | ξ j = z} := by
    have h : (fun ξ : Ω n => (if ξ j = z then (1 : ℝ) else 0)) =
        ({ξ : Ω n | ξ j = z}).indicator (fun _ : Ω n => (1 : ℝ)) := by
      funext ξ
      by_cases hz : ξ j = z
      · simp [hz]
      · have hmem : ξ ∉ {ξ : Ω n | ξ j = z} := by
          intro hm
          exact hz hm
        simp [hz, hmem]
    rw [h]
    rw [integral_indicator hs]
    rw [setIntegral_const]
    simp
  calc
    (∑ ξ : Ω n, biasW θ ξ * (if ξ j = z then (1 : ℝ) else 0))
        = (∫ ξ : Ω n, (if ξ j = z then (1 : ℝ) else 0) ∂(biasedMeasure (n := n) θ)) := by
            simpa using (integral_biased_eq θ (fun ξ : Ω n => (if ξ j = z then (1 : ℝ) else 0))).symm
    _ = (biasedMeasure (n := n) θ).real {ξ : Ω n | ξ j = z} := hstep2
    _ = (biasedCoord θ).real {z} := by
          rw [measureReal_def (biasedMeasure (n := n) θ) {ξ : Ω n | ξ j = z}]
          rw [biased_mass_coord θ j z]
          rw [← measureReal_def (biasedCoord θ) {z}]
    _ = (1 + Real.cos θ * ((z : C) : ℝ)) / 2 := biasedCoord_real_mass θ z



lemma sum_biasW_eq_one {n : ℕ} (θ : ℝ) : (∑ ξ : Ω n, biasW θ ξ) = 1 := by
  calc
    (∑ ξ : Ω n, biasW θ ξ) = ∑ ξ : Ω n, (biasW θ ξ) • (1 : ℝ) := by simp
    _ = ∫ ξ : Ω n, (1 : ℝ) ∂(biasedMeasure (n := n) θ) := by
          simpa using (integral_biased_eq θ (fun _ : Ω n => (1 : ℝ))).symm
    _ = 1 := by
          rw [integral_const]
          simp

/-- `Σ_ξ biasW·(ξ_j : ℝ) = cosθ` (single-coordinate mean under the biased law). -/
lemma marginal_mean {n : ℕ} (θ : ℝ) (j : Fin n) :
    (∑ ξ : Ω n, biasW θ ξ * ((ξ j : C) : ℝ)) = Real.cos θ := by
  have hc1 : (∑ ξ : Ω n, biasW θ ξ * (if (ξ j) = cOne then (1 : ℝ) else 0)) = (1 + Real.cos θ) / 2 := by
    simpa [cOne] using biasW_sum_indicator θ j cOne
  have hc2 : (∑ ξ : Ω n, biasW θ ξ * (if (ξ j) = cNegOne then (1 : ℝ) else 0)) = (1 + -Real.cos θ) / 2 := by
    simpa [cNegOne] using biasW_sum_indicator θ j cNegOne
  calc
    (∑ ξ : Ω n, biasW θ ξ * ((ξ j : C) : ℝ))
        = ∑ ξ : Ω n, biasW θ ξ * ((if (ξ j) = cOne then (1 : ℝ) else 0) - (if (ξ j) = cNegOne then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro ξ hξ
            congr 1
            rcases mem_two (ξ j) with hz1 | hz1
            · rw [hz1]
              simp [cOne, cNegOne, cOne_ne_cNegOne]
            · rw [hz1]
              simp [cOne, cNegOne, cNegOne_ne_cOne]
    _ = (∑ ξ : Ω n, biasW θ ξ * (if (ξ j) = cOne then (1 : ℝ) else 0)) -
        (∑ ξ : Ω n, biasW θ ξ * (if (ξ j) = cNegOne then (1 : ℝ) else 0)) := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
    _ = (1 + Real.cos θ) / 2 - (1 + -Real.cos θ) / 2 := by
            rw [hc1, hc2]
    _ = Real.cos θ := by ring

/-- `a` factors out of a biased-weight sum. -/
lemma sum_const_mul {n : ℕ} (θ : ℝ) (a : ℝ) :
    (∑ x : Ω n, a * biasW θ x) = a * (∑ x : Ω n, biasW θ x) := by
  exact (Finset.mul_sum (s := Finset.univ) (f := fun x : Ω n => biasW θ x) (a := a)).symm


/-- `Σ_x biasW·(a − (x_j : ℝ)) = a − cosθ` for a fixed scalar `a`. -/
lemma sum_biasW_sub_mean {n : ℕ} (θ : ℝ) (j : Fin n) (a : ℝ) :
    (∑ x : Ω n, biasW θ x * (a - ((x j : C) : ℝ))) = a - Real.cos θ := by
  calc
    (∑ x : Ω n, biasW θ x * (a - ((x j : C) : ℝ)))
        = (∑ x : Ω n, biasW θ x * a) - (∑ x : Ω n, biasW θ x * ((x j : C) : ℝ)) := by
            calc
              (∑ x : Ω n, biasW θ x * (a - ((x j : C) : ℝ)))
                  = ∑ x : Ω n, (biasW θ x * a - biasW θ x * ((x j : C) : ℝ)) := by
                      simp_rw [mul_sub]
              _ = (∑ x : Ω n, biasW θ x * a) - (∑ x : Ω n, biasW θ x * ((x j : C) : ℝ)) := by
                      rw [Finset.sum_sub_distrib]
    _ = a - Real.cos θ := by
          calc
            (∑ x : Ω n, biasW θ x * a) - (∑ x : Ω n, biasW θ x * ((x j : C) : ℝ))
                = a * (∑ x : Ω n, biasW θ x) - (∑ x : Ω n, biasW θ x * ((x j : C) : ℝ)) := by
                    congr 1
                    calc
                      (∑ x : Ω n, biasW θ x * a) = ∑ x : Ω n, a * biasW θ x := by
                            apply Finset.sum_congr rfl; intro x hx; ring
                      _ = a * (∑ x : Ω n, biasW θ x) := by
                            exact (Finset.mul_sum (s := Finset.univ) (f := fun x : Ω n => biasW θ x) (a := a)).symm
            _ = a - Real.cos θ := by
                    rw [marginal_mean θ j, sum_biasW_eq_one θ]
                    ring

/-- Expansion of `δ_j(θ)(ξ)` as a biased expectation over an independent copy. -/
lemma delta_as_integral {n : ℕ} (θ : ℝ) (j : Fin n) (ξ : Ω n) (hsin : Real.sin θ ≠ 0) :
    delta θ ξ j = ∫ y : Ω n, (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ
      ∂(biasedMeasure (n := n) θ) := by
  unfold delta
  have hI : (∫ y : Ω n, (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ
      ∂(biasedMeasure (n := n) θ)) = (((ξ j : C) : ℝ) - Real.cos θ) / Real.sin θ := by
    calc
      (∫ y : Ω n, (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ
          ∂(biasedMeasure (n := n) θ))
          = (∑ y : Ω n, biasW θ y * ((((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ)) := by
              simpa [smul_eq_mul] using integral_biased_eq θ (fun y : Ω n =>
                (((ξ j : C) : ℝ) - ((y j : C) : ℝ)) / Real.sin θ)
      _ = (∑ y : Ω n, (biasW θ y * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) / Real.sin θ) := by
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (∑ y : Ω n, biasW θ y * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) / Real.sin θ := by
              exact (Finset.sum_div (s := Finset.univ)
                (f := fun y : Ω n => biasW θ y * (((ξ j : C) : ℝ) - ((y j : C) : ℝ))) (a := Real.sin θ)).symm
      _ = (((ξ j : C) : ℝ) - Real.cos θ) / Real.sin θ := by
              rw [sum_biasW_sub_mean θ j ((ξ j : C) : ℝ)]
  rw [hI]

end RadType
end
