import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

open Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **The minor-arc `ℓᵖ` endpoint of MST §4.1**, step (a): the operator `A_{2^n} − A_{2^n} Π_n` (the density average minus its level-`n` major-arc projection, KMSZ's `m_{2^n}(1 − Ξ_n)`) is `ℓᵖ`-bounded with a constant *uniform in* `n`, for every `1 < p < 2`. The route is `mstMinorOp_eq` (the operator is `discAvgZC P (2^n) g − discAvgZC P (2^n) (opArc η_n (mstU l n) g)`) together with `discAvgZC_contraction` applied twice and the `ℓᵖ` bound for the projected average supplied by the Ionescu–Wainger input `IWSupersetBoundLift` at the level `N = n^l`, `ρ = mstRho l` (of which the Mikhlin and support hypotheses are `hcd/hbdd/hder/hder2/hsupp`). This is only the endpoint: the `(n+1)^{−2}` gain of MST (61) comes from interpolating this bound with the `ℓ²` gain of the companion module. -/
theorem mst_minor_lp_per_n (hIW : Work.BourgainPlan.Maximal.IWSupersetBoundLift)
    (P : Polynomial ℤ) {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (l : ℕ) (hl : 1 ≤ l) (χ : ℝ) (η : ℝ → ℂ)
    (hη : ∀ n : ℕ, MeasureTheory.MemLp
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n) ⊤ (AddCircle.haarAddCircle (T := 1)))
    (A : ℝ) (hA : 0 < A)
    (hcd : ∀ n : ℕ, ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)))
    (hbdd : ∀ (n : ℕ) (x : ℝ), ‖Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n) x‖ ≤ A)
    (hder : ∀ (n : ℕ) (x : ℝ), |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)) x‖ ≤ A)
    (hder2 : ∀ (n : ℕ) (x : ℝ), |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift
      (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n)) x‖ ≤ A)
    (hsupp : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
      Work.BourgainPlan.Maximal.iwEps (Work.BourgainPlan.Maximal.mstRho l) (n ^ l) < ‖ξ‖ →
        Work.BourgainPlan.Maximal.mstEta P.natDegree χ η n ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ (g : ℤ → ℂ) (hg : Memℓp g 2),
      ∫⁻ m : ℤ, ‖Work.BourgainPlan.Maximal.mstMinorOp P l P.natDegree χ η n (hη n) g hg m‖ₑ ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂MeasureTheory.Measure.count := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have hρ : 0 < mstRho l := by unfold mstRho; positivity
  obtain ⟨C₁, hC₁pos, N₁, hN₁⟩ := hIW (mstRho l) hρ p hp
  obtain ⟨N₀, hN₀⟩ := hsupp
  refine ⟨4 * (1 + C₁ * A), by positivity, max N₁ N₀, ?_⟩
  intro n hn g hg
  have hnN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnN₀ : N₀ ≤ n := le_trans (le_max_right _ _) hn
  have hNle : N₁ ≤ n ^ l := le_trans hnN₁ (Nat.le_self_pow (by omega) n)
  -- the Ionescu–Wainger bound for the projected average
  have hIWn : ∫⁻ m : ℤ, ‖opArc (mstEta P.natDegree χ η n) (hη n) (mstU l n) g hg m‖ₑ ^ p
        ∂Measure.count
      ≤ ENNReal.ofReal ((C₁ * A) ^ p) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count := by
    have h := hN₁ (n ^ l) hNle (ε := iwEps (mstRho l) (n ^ l)) (Real.exp_pos _) le_rfl
      (mstEta P.natDegree χ η n) (hη n) (hcd n) hA.le (hbdd n) (hder n) (hder2 n)
      (hN₀ n hnN₀) g hg
    simpa only [mstU] using h
  set X : ℝ≥0∞ := ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count with hXdef
  set a : ℤ → ℝ≥0∞ := fun m => ‖discAvgZC P (2 ^ n) g m‖ₑ with hadef
  set b : ℤ → ℝ≥0∞ := fun m => ‖discAvgZC P (2 ^ n)
      (opArc (mstEta P.natDegree χ η n) (hη n) (mstU l n) g hg) m‖ₑ with hbdef
  -- the two `ℓᵖ` contractions
  have hcontr1 : ∫⁻ m : ℤ, a m ^ p ∂Measure.count ≤ X :=
    discAvgZC_contraction P (2 ^ n) hp.le g
  have hcontr2 : ∫⁻ m : ℤ, b m ^ p ∂Measure.count ≤ ENNReal.ofReal ((C₁ * A) ^ p) * X :=
    le_trans (discAvgZC_contraction P (2 ^ n) hp.le _) hIWn
  have hfun : (fun m : ℤ => ‖mstMinorOp P l P.natDegree χ η n (hη n) g hg m‖ₑ ^ p)
      = fun m : ℤ => ‖discAvgZC P (2 ^ n) g m - discAvgZC P (2 ^ n)
          (opArc (mstEta P.natDegree χ η n) (hη n) (mstU l n) g hg) m‖ₑ ^ p := by
    funext m
    rw [mstMinorOp_eq]
    simp only [Pi.sub_apply]
  -- the triangle inequality plus the two contractions
  have hkey : ∫⁻ m : ℤ, ‖mstMinorOp P l P.natDegree χ η n (hη n) g hg m‖ₑ ^ p ∂Measure.count
      ≤ (2 : ℝ≥0∞) ^ p * (X + ENNReal.ofReal ((C₁ * A) ^ p) * X) := by
    rw [hfun]
    calc ∫⁻ m : ℤ, ‖discAvgZC P (2 ^ n) g m - discAvgZC P (2 ^ n)
            (opArc (mstEta P.natDegree χ η n) (hη n) (mstU l n) g hg) m‖ₑ ^ p
            ∂Measure.count
        ≤ ∫⁻ m : ℤ, (a m + b m) ^ p ∂Measure.count :=
          lintegral_mono fun m => ENNReal.rpow_le_rpow enorm_sub_le hp0.le
      _ ≤ ∫⁻ m : ℤ, (2 : ℝ≥0∞) ^ p * (a m ^ p + b m ^ p) ∂Measure.count :=
          lintegral_mono fun m =>
            ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp0.le
      _ = (2 : ℝ≥0∞) ^ p *
            (∫⁻ m : ℤ, a m ^ p ∂Measure.count + ∫⁻ m : ℤ, b m ^ p ∂Measure.count) := by
          rw [lintegral_const_mul _ (by measurability), lintegral_add_left (by measurability)]
      _ ≤ (2 : ℝ≥0∞) ^ p * (X + ENNReal.ofReal ((C₁ * A) ^ p) * X) := by
          gcongr
  -- the coefficient: `2^p · (1 + (C₁A)^p) ≤ (4(1 + C₁A))^p`
  have hx : 0 ≤ C₁ * A := by positivity
  have hcoeff : (2 : ℝ≥0∞) ^ p * (1 + ENNReal.ofReal ((C₁ * A) ^ p))
      ≤ ENNReal.ofReal ((4 * (1 + C₁ * A)) ^ p) := by
    have h2p : (2 : ℝ≥0∞) ^ p = ENNReal.ofReal ((2 : ℝ) ^ p) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp0.le]
      norm_num
    have hreal : (2 : ℝ) ^ p * (1 + (C₁ * A) ^ p) ≤ (4 * (1 + C₁ * A)) ^ p := by
      have h1x : (1 : ℝ) ≤ 1 + C₁ * A := by linarith
      have hpow1 : (1 : ℝ) ≤ (1 + C₁ * A) ^ p := Real.one_le_rpow h1x hp0.le
      have hxpow : (C₁ * A) ^ p ≤ (1 + C₁ * A) ^ p :=
        Real.rpow_le_rpow hx (by linarith) hp0.le
      have hsum : 1 + (C₁ * A) ^ p ≤ 2 * (1 + C₁ * A) ^ p := by linarith
      have h2le : (2 : ℝ) ≤ 2 ^ p := by
        have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (y := 1) (z := p)
          (by norm_num) hp.le
        simpa using h
      have h2pos : (0 : ℝ) < 2 ^ p := Real.rpow_pos_of_pos (by norm_num) p
      have h4 : (4 * (1 + C₁ * A)) ^ p = 2 ^ p * (2 ^ p * (1 + C₁ * A) ^ p) := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2 * 2) (by linarith : (0 : ℝ) ≤ 1 + C₁ * A),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      rw [h4]
      calc 2 ^ p * (1 + (C₁ * A) ^ p) ≤ 2 ^ p * (2 * (1 + C₁ * A) ^ p) :=
            mul_le_mul_of_nonneg_left hsum h2pos.le
        _ ≤ 2 ^ p * (2 ^ p * (1 + C₁ * A) ^ p) := by
            apply mul_le_mul_of_nonneg_left _ h2pos.le
            exact mul_le_mul_of_nonneg_right h2le
              (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + C₁ * A) p)
    calc (2 : ℝ≥0∞) ^ p * (1 + ENNReal.ofReal ((C₁ * A) ^ p))
        = ENNReal.ofReal ((2 : ℝ) ^ p) * (1 + ENNReal.ofReal ((C₁ * A) ^ p)) := by
          rw [h2p]
      _ = ENNReal.ofReal ((2 : ℝ) ^ p) * ENNReal.ofReal (1 + (C₁ * A) ^ p) := by
          rw [ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg hx p), ENNReal.ofReal_one]
      _ = ENNReal.ofReal ((2 : ℝ) ^ p * (1 + (C₁ * A) ^ p)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)]
      _ ≤ ENNReal.ofReal ((4 * (1 + C₁ * A)) ^ p) := ENNReal.ofReal_le_ofReal hreal
  calc ∫⁻ m : ℤ, ‖mstMinorOp P l P.natDegree χ η n (hη n) g hg m‖ₑ ^ p ∂Measure.count
      ≤ (2 : ℝ≥0∞) ^ p * (X + ENNReal.ofReal ((C₁ * A) ^ p) * X) := hkey
    _ = ((2 : ℝ≥0∞) ^ p * (1 + ENNReal.ofReal ((C₁ * A) ^ p))) * X := by ring
    _ ≤ ENNReal.ofReal ((4 * (1 + C₁ * A)) ^ p) * X := mul_le_mul_left hcoeff X

end

end Work.BourgainPlan.Maximal
