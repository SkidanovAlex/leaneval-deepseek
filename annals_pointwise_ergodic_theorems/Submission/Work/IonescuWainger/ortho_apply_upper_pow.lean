import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OrthoApplyUpper

namespace Work.IonescuWainger

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger (opArc arcShift sigmaStrataFinset strataCompFinset
  memℓp_finsupp ortho_apply_upper)

/-- A `tsum` of a finset of sums over `ℝ≥0∞` may be exchanged with the outer sum. -/
lemma tsum_finset_sum_ennreal {ι κ : Type*} (s : Finset ι) (g : ι → κ → ENNReal) :
    (∑' n : κ, ∑ i ∈ s, g i n) = ∑ i ∈ s, ∑' n : κ, g i n :=
  Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

/-- From `L ^ (1 / T) ≤ Z` with `T > 0` conclude `L ≤ Z ^ T`. -/
lemma le_of_rpow_le {L Z : ENNReal} {T : ℝ} (hT0 : 0 < T) (h : L ^ (1 / T) ≤ Z) :
    L ≤ Z ^ T := by
  have h1T : (1 / T) * T = 1 := by field_simp
  calc L = (L ^ (1 / T)) ^ T := by rw [← ENNReal.rpow_mul, h1T, ENNReal.rpow_one]
    _ ≤ Z ^ T := ENNReal.rpow_le_rpow h hT0.le

/-- `(ofReal P · Y ^ (1 / T)) ^ T = ofReal (P ^ T) · Y` for `P ≥ 0` and `T > 0`. -/
lemma ofReal_mul_rpow_one_div {P : ℝ} (hP0 : 0 ≤ P) {T : ℝ} (hT0 : 0 < T) (Y : ENNReal) :
    (ENNReal.ofReal P * Y ^ (1 / T)) ^ T = ENNReal.ofReal (P ^ T) * Y := by
  have h1T : (1 / T) * T = 1 := by field_simp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hT0.le, ENNReal.ofReal_rpow_of_nonneg hP0 hT0.le,
    ← ENNReal.rpow_mul, h1T, ENNReal.rpow_one]

/-- `ofReal (x ^ (2 * r))` with a real exponent `2 * r` agrees with the natural power. -/
lemma ofReal_rpow_two_mul_eq_pow (x : ℝ) (r : ℕ) :
    ENNReal.ofReal (x ^ (2 * r : ℝ)) = ENNReal.ofReal (x ^ (2 * r)) := by
  rw [show (2 * r : ℝ) = ((2 * r : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]

theorem ortho_apply_upper_pow {S : Finset ℕ} (h2S : ∀ q ∈ S, 2 ≤ q)
    (hScop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {k : ℕ} {qmax : ℕ} (hmax : ∀ q ∈ S, q ≤ qmax) (hqmax : 1 ≤ qmax)
    {ε : ℝ} (hε0 : 0 < ε) (hsmall : 2 * ε < 1 / (qmax : ℝ) ^ (2 * k))
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {M : ℝ} (hM : 0 ≤ M)
    (hφbd : ∀ ξ, ‖φ ξ‖ ≤ M) (hφsupp : ∀ ξ, ε < ‖ξ‖ → φ ξ = 0)
    {K : ℤ → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hK : ∀ m : ℤ, ∫ ξ, φ ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = K m)
    (hdecay : ∀ m : ℤ, ‖K m‖ ≤ C * ε / (1 + (ε * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2))
    {r : ℕ} (hr : 1 ≤ r) (f : ℤ →₀ ℂ) :
    ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑' n : ℤ, (∑ α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀,
            ENNReal.ofReal (‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
              (Work.BourgainPlan.IonescuWainger.arcShift
                (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀) α)
              (⇑f) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ)
      ≤ ENNReal.ofReal (((M ^ 2 * (2 ^ k : ℝ)) ^ (1 / (2 * r : ℝ)) *
            (8 * C * (2 ^ k : ℝ)) ^ (1 - 2 / (2 * r : ℝ))) ^ (2 * r : ℝ)) *
          ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)) := by
  classical
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hp : (2 : ℝ) ≤ (2 * r : ℝ) := by linarith
  have hTpos : (0 : ℝ) < (2 * r : ℝ) := by linarith
  have hP0 : (0 : ℝ) ≤ (M ^ 2 * (2 ^ k : ℝ)) ^ (1 / (2 * r : ℝ)) *
      (8 * C * (2 ^ k : ℝ)) ^ (1 - 2 / (2 * r : ℝ)) := by
    apply mul_nonneg <;> apply Real.rpow_nonneg <;> positivity
  have hmain := ortho_apply_upper h2S hScop hmax hqmax hε0 hsmall φ hφ hM hφbd hφsupp
      hC0 hK hdecay (p := (2 * r : ℝ)) hp f
  have hexp : (2 * r : ℝ) / 2 = (r : ℝ) := by ring
  rw [hexp] at hmain
  have hswap := tsum_finset_sum_ennreal (S.powerset.filter (fun A => A.card ≤ k))
      (fun A₀ n => (∑ α ∈ strataCompFinset S k A₀, ENNReal.ofReal
          (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f) (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ))
  have hYe : (∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r : ℝ)))
      = ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)) :=
    tsum_congr (fun n => ofReal_rpow_two_mul_eq_pow _ r)
  calc ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k), ∑' n : ℤ,
        (∑ α ∈ strataCompFinset S k A₀, ENNReal.ofReal
          (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f) (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ)
      = ∑' n : ℤ, ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        (∑ α ∈ strataCompFinset S k A₀, ENNReal.ofReal
          (‖opArc φ hφ (arcShift (sigmaStrataFinset A₀) α) (⇑f) (memℓp_finsupp f) n‖ ^ 2)) ^ (r : ℝ) :=
        hswap.symm
    _ ≤ (ENNReal.ofReal ((M ^ 2 * (2 ^ k : ℝ)) ^ (1 / (2 * r : ℝ)) *
          (8 * C * (2 ^ k : ℝ)) ^ (1 - 2 / (2 * r : ℝ))) *
          (∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r : ℝ))) ^ (1 / (2 * r : ℝ))) ^ (2 * r : ℝ) :=
        le_of_rpow_le hTpos hmain
    _ = ENNReal.ofReal (((M ^ 2 * (2 ^ k : ℝ)) ^ (1 / (2 * r : ℝ)) *
          (8 * C * (2 ^ k : ℝ)) ^ (1 - 2 / (2 * r : ℝ))) ^ (2 * r : ℝ)) *
        ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r : ℝ)) :=
        ofReal_mul_rpow_one_div hP0 hTpos _
    _ = ENNReal.ofReal (((M ^ 2 * (2 ^ k : ℝ)) ^ (1 / (2 * r : ℝ)) *
          (8 * C * (2 ^ k : ℝ)) ^ (1 - 2 / (2 * r : ℝ))) ^ (2 * r : ℝ)) *
        ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)) := by
        rw [hYe]

end Work.IonescuWainger
