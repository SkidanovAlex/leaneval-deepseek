import Submission.Rad.Mul
import Submission.Rad.Prob
set_option autoImplicit false
open Function MeasureTheory ProbabilityTheory Measure
open scoped ENNReal

noncomputable section

namespace RadType
open RademacherEnfloType

/-- The weight of a cube point `ξ` under the biased measure with parameter `θ`:
`∏_j (1 + cos θ · ξ_j) / 2`.  (With `cos θ = e^{-t}` this is the mass of `ξ` under a product of
independent biased Bernoulli coordinates `P(ξ_j = ±1) = (1 ± cos θ)/2`.) -/
def biasW (θ : ℝ) {n : ℕ} (ξ : Ω n) : ℝ :=
  ∏ j : Fin n, ((1 + Real.cos θ * ((ξ j : C) : ℝ)) / 2)

lemma biasW_nonneg (θ : ℝ) {n : ℕ} (ξ : Ω n) : 0 ≤ biasW θ ξ := by
  unfold biasW
  apply Finset.prod_nonneg
  intro j hj
  have h1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have h2 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hz : -1 ≤ (ξ j : ℝ) := by
    rcases coe_real_eq (ξ j) with hz | hz <;> simp [hz]
  have hz1 : (ξ j : ℝ) ≤ 1 := by
    rcases coe_real_eq (ξ j) with hz | hz <;> simp [hz]
  have hc : 0 ≤ 1 + Real.cos θ * ((ξ j : C) : ℝ) := by
    nlinarith
  positivity

lemma pOne_mem (θ : ℝ) : (1 + Real.cos θ) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have h2 : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  constructor <;> nlinarith

/-- Biased coordinate measure on `{-1,1}` with `P(+1) = (1 + cos θ)/2`. -/
noncomputable def biasedCoord (θ : ℝ) : Measure C :=
  bernoulliMeasure cOne cNegOne ⟨(1 + Real.cos θ) / 2, pOne_mem θ⟩

/-- Biased measure on the cube (product of independent biased coordinates). -/
noncomputable def biasedMeasure {n : ℕ} (θ : ℝ) : Measure (Ω n) :=
  Measure.infinitePi (fun _ : Fin n => biasedCoord θ)

set_option synthInstance.maxHeartbeats 0 in
instance prob_biasedCoord (θ : ℝ) : IsProbabilityMeasure (biasedCoord θ) := by
  unfold biasedCoord
  infer_instance

set_option synthInstance.maxHeartbeats 0 in
instance prob_biased {n : ℕ} (θ : ℝ) : IsProbabilityMeasure (biasedMeasure (n := n) θ) := by
  unfold biasedMeasure biasedCoord
  infer_instance

/-- Real mass of the point `+1` under the biased coordinate. -/
lemma biasedCoord_real_mass_one (θ : ℝ) :
    (biasedCoord θ).real ({cOne} : Set C) = (1 + Real.cos θ) / 2 := by
  unfold biasedCoord
  rw [bernoulliMeasure_real_apply_of_mem_of_notMem (⟨(1 + Real.cos θ)/2, pOne_mem θ⟩ : unitInterval)
    (MeasurableSet.singleton cOne) ?hx ?hy]
  · rfl
  · exact fun h => cOne_ne_cNegOne h.symm

/-- Real mass of the point `-1` under the biased coordinate. -/
lemma biasedCoord_real_mass_negone (θ : ℝ) :
    (biasedCoord θ).real ({cNegOne} : Set C) = (1 - Real.cos θ) / 2 := by
  unfold biasedCoord
  rw [bernoulliMeasure_real_apply_of_notMem_of_mem (⟨(1 + Real.cos θ)/2, pOne_mem θ⟩ : unitInterval)
    (MeasurableSet.singleton cNegOne) ?hx ?hy]
  · ring
  · intro h; exact cOne_ne_cNegOne h
  · simp

/-- Real mass of an arbitrary point `z` under the biased coordinate measure. -/
lemma biasedCoord_real_mass (θ : ℝ) (z : C) :
    (biasedCoord θ).real ({z} : Set C) = (1 + Real.cos θ * ((z : C) : ℝ)) / 2 := by
  rcases val_eq z with hz | hz
  · have hzC : z = cOne := by
      apply Subtype.ext
      simpa [cOne] using hz
    rw [hzC, biasedCoord_real_mass_one θ]
    congr 1
    simp [cOne]
  · have hzC : z = cNegOne := by
      apply Subtype.ext
      simpa [cNegOne] using hz
    rw [hzC, biasedCoord_real_mass_negone θ]
    congr 1
    simp [cNegOne]
    ring

/-- Real mass of a cube point `ξ` under the biased measure. -/
lemma biased_real_mass (θ : ℝ) {n : ℕ} (ξ : Ω n) :
    (biasedMeasure (n := n) θ).real ({ξ} : Set (Ω n)) = biasW θ ξ := by
  classical
  unfold biasedMeasure biasW
  change (((Measure.infinitePi (fun _ : Fin n => biasedCoord θ)) {ξ}).toReal)
      = ∏ j : Fin n, ((1 + Real.cos θ * ((ξ j : C) : ℝ)) / 2)
  rw [Measure.infinitePi_eq_pi]
  rw [Measure.pi_singleton]
  have hmain : (∏ j : Fin n, ((biasedCoord θ) {ξ j}).toReal)
        = ∏ j : Fin n, ((1 + Real.cos θ * ((ξ j : C) : ℝ)) / 2) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    exact (measureReal_def (biasedCoord θ) {ξ j}).symm.trans (biasedCoord_real_mass θ (ξ j))
  rw [ENNReal.toReal_prod]
  exact hmain

/-- Any function on the finite cube is Bochner integrable w.r.t. the biased measure. -/
lemma integrable_biased {n : ℕ} {E : Type*} [NormedAddCommGroup E] (θ : ℝ)
    (f : Ω n → E) : Integrable f (biasedMeasure (n := n) θ) := by
  refine Integrable.of_bound ?hf (∑ ε : Ω n, ‖f ε‖) ?bound
  · exact (StronglyMeasurable.of_discrete (f := f)).aestronglyMeasurable
  · apply ae_of_all
    intro ε
    exact Finset.single_le_sum (by intro a ha; exact norm_nonneg (f a)) (Finset.mem_univ ε)

end RadType
end
